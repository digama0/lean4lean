import Lean4Lean.Level
import Lean4Lean.Quot
import Lean4Lean.Inductive.Reduce
import Lean4Lean.Instantiate
import Lean4Lean.ForEachExprV
import Lean4Lean.EquivManager

namespace Lean

abbrev InferCache := ExprMap Expr

structure TypeChecker.State where
  ngen : NameGenerator := { namePrefix := `_kernel_fresh }
  inferTypeI : InferCache := {}
  inferTypeC : InferCache := {}
  whnfCoreCache : ExprMap Expr := {}
  whnfCache : ExprMap Expr := {}
  eqvManager : EquivManager := {}
  failure : HashSet (Expr × Expr) := {}

structure TypeChecker.Context where
  env : Environment
  lctx : LocalContext := {}
  safety : DefinitionSafety := .safe
  -- When `lparams != none`, the `check` method makes sure all level parameters
  -- are in `lparams`.
  lparams : Option (List Name) := none

namespace TypeChecker

abbrev M := ReaderT Context <| StateT State <| Except KernelException

def M.run (env : Environment) (safety : DefinitionSafety := .safe) (lctx : LocalContext := {})
    (x : M α) : Except KernelException α :=
  x { env, safety, lctx } |>.run' {}

instance : MonadEnv M where
  getEnv := return (← read).env
  modifyEnv _ := pure ()

instance : MonadLCtx M where
  getLCtx := return (← read).lctx

instance [Monad m] : MonadNameGenerator (StateT State m) where
  getNGen := return (← get).ngen
  setNGen ngen := modify fun s => { s with ngen }

instance (priority := low) : MonadWithReaderOf LocalContext M where
  withReader f := withReader fun s => { s with lctx := f s.lctx }

structure Methods where
  isDefEqCore : Expr → Expr → M Bool
  whnfCore (e : Expr) (cheapRec := false) (cheapProj := false) : M Expr
  whnf (e : Expr) : M Expr
  inferType (e : Expr) (inferOnly : Bool) : M Expr

abbrev RecM := ReaderT Methods M

inductive ReductionStatus where
  | continue (tn sn : Expr)
  | unknown (tn sn : Expr)
  | bool (b : Bool)

namespace Inner

def whnf (e : Expr) : RecM Expr := fun m => m.whnf e

@[inline] def withLCtx [MonadWithReaderOf LocalContext m] (lctx : LocalContext) (x : m α) : m α :=
  withReader (fun _ => lctx) x

def ensureSortCore (e s : Expr) : RecM Expr := do
  if e.isSort then return e
  let e ← whnf e
  if e.isSort then return e
  throw <| .typeExpected (← getEnv) (← getLCtx) s

def ensureForallCore (e s : Expr) : RecM Expr := do
  if e.isForall then return e
  let e ← whnf e
  if e.isForall then return e
  throw <| .funExpected (← getEnv) (← getLCtx) s

def checkLevel (tc : Context) (l : Level) : Except KernelException Unit := do
  if let some lps := tc.lparams then
    if let some n2 := l.getUndefParam lps then
      throw <| .other
        s!"invalid reference to undefined universe level parameter '{n2}'"

def inferFVar (tc : Context) (name : FVarId) : Except KernelException Expr := do
  if let some decl := tc.lctx.find? name then
    return decl.type
  throw <| .other "unknown free variable"

def inferConstant (tc : Context) (name : Name) (ls : List Level) (inferOnly : Bool) :
    Except KernelException Expr := do
  let e := Expr.const name ls
  let info ← tc.env.get name
  let ps := info.levelParams
  if ps.length != ls.length then
    throw <| .other s!"incorrect number of universe levels parameters for '{e
      }', #{ps.length} expected, #{ls.length} provided"
  if !inferOnly then
    if info.isUnsafe && tc.safety != .unsafe then
      throw <| .other s!"invalid declaration, it uses unsafe declaration '{e}'"
    if let .defnInfo v := info then
      if v.safety == .partial && tc.safety == .safe then
        throw <| .other
          s!"invalid declaration, safe declaration must not contain partial declaration '{e}'"
    for l in ls do
      checkLevel tc l
  return info.instantiateTypeLevelParams ls

def inferType (e : Expr) (inferOnly := true) : RecM Expr := fun m => m.inferType e inferOnly

def inferLambda (e : Expr) (inferOnly : Bool) : RecM Expr := loop #[] e where
  loop fvars : Expr → RecM Expr
  | .lam name dom body bi => do
    let d := dom.instantiateRev fvars
    let id := ⟨← mkFreshId⟩
    withLCtx ((← getLCtx).mkLocalDecl id name d bi) do
      let fvars := fvars.push (.fvar id)
      if !inferOnly then
        _ ← ensureSortCore (← inferType d inferOnly) d
      loop fvars body
  | e => do
    let r ← inferType (e.instantiateRev fvars) inferOnly
    let r := r.cheapBetaReduce
    return (← getLCtx).mkForall fvars r

def inferForall (e : Expr) (inferOnly : Bool) : RecM Expr := loop #[] #[] e where
  loop fvars us : Expr → RecM Expr
  | .forallE name dom body bi => do
    let d := dom.instantiateRev fvars
    let t1 ← ensureSortCore (← inferType d inferOnly) d
    let us := us.push t1.sortLevel!
    let id := ⟨← mkFreshId⟩
    withLCtx ((← getLCtx).mkLocalDecl id name d bi) do
      let fvars := fvars.push (.fvar id)
      loop fvars us body
  | e => do
    let r ← inferType (e.instantiateRev fvars) inferOnly
    let s ← ensureSortCore r e
    return .sort <| us.foldr mkLevelIMax' s.sortLevel!

def isDefEqCore (t s : Expr) : RecM Bool := fun m => m.isDefEqCore t s

def isDefEq (t s : Expr) : RecM Bool := do
  let r ← isDefEqCore t s
  if r then
    modify fun st => { st with eqvManager := st.eqvManager.addEquiv t s }
  pure r

def inferApp (e : Expr) : RecM Expr := do
  e.withApp fun f args => do
  let mut fType ← inferType f
  let mut j := 0
  for i in [:args.size] do
    match fType with
    | .forallE _ _ body _ =>
      fType := body
    | _ =>
      fType := fType.instantiateRevRange j i args
      fType := (← ensureForallCore fType e).bindingBody!
      j := i
  return fType.instantiateRevRange j args.size args

def markUsed (n : Nat) (fvars : Array Expr) (b : Expr) (used : Array Bool) : Array Bool := Id.run do
  if !b.hasFVar then return used
  (·.2) <$> StateT.run (s := used) do
    b.forEachV' fun x => do
      if !x.hasFVar then return false
      if let .fvar name := x then
        for i in [:n] do
          if fvars[i]!.fvarId! == name then
            modify (·.set! i true)
            return false
      return true

def inferLet (e : Expr) (inferOnly : Bool) : RecM Expr := loop #[] #[] e where
  loop fvars vals : Expr → RecM Expr
  | .letE name type val body _ => do
    let type := type.instantiateRev fvars
    let val := val.instantiateRev fvars
    let id := ⟨← mkFreshId⟩
    withLCtx ((← getLCtx).mkLetDecl id name type val) do
      let fvars := fvars.push (.fvar id)
      let vals := vals.push val
      if !inferOnly then
        _ ← ensureSortCore (← inferType type inferOnly) type
        let valType ← inferType val inferOnly
        if !(← isDefEq valType type) then
          throw <| .letTypeMismatch (← getEnv) (← getLCtx) name valType type
      loop fvars vals body
  | e => do
    let r ← inferType (e.instantiateRev fvars) inferOnly
    let r := r.cheapBetaReduce
    let rec loopUsed i (used : Array Bool) :=
      match i with
      | 0 => used
      | i+1 =>
        let used := if used[i]! then markUsed i fvars vals[i]! used else used
        loopUsed i used
    let used := mkArray fvars.size false
    let used := markUsed fvars.size fvars r used
    let used := loopUsed fvars.size used
    let mut usedFVars := #[]
    for fvar in fvars, b in used do
      if b then
        usedFVars := usedFVars.push fvar
    return (← getLCtx).mkForall fvars r

def isProp (e : Expr) : RecM Bool :=
  return (← whnf (← inferType e)) == .prop

def inferProj (typeName : Name) (idx : Nat) (struct structType : Expr) : RecM Expr := do
  let e := Expr.proj typeName idx struct
  let type ← whnf structType
  type.withApp fun I args => do
  let env ← getEnv
  let fail {_} := do throw <| .invalidProj env (← getLCtx) e
  let .const I_name I_levels := I | fail
  if typeName != I_name then fail
  let .inductInfo I_val ← env.get I_name | fail
  let [c] := I_val.ctors | fail
  if args.size != I_val.numParams + I_val.numIndices then fail
  let c_info ← env.get c
  let mut r := c_info.instantiateTypeLevelParams I_levels
  for i in [:I_val.numParams] do
    let .forallE _ _ b _ ← whnf r | fail
    r := b.instantiate1 args[i]!
  let isPropType ← isProp type
  for i in [:idx] do
    let .forallE _ dom b _ ← whnf r | fail
    if b.hasLooseBVars then
      if isPropType then if !(← isProp dom) then fail
      r := b.instantiate1 (.proj I_name i struct)
    else
      r := b
  let .forallE _ dom _ _ ← whnf r | fail
  if isPropType then if !(← isProp dom) then fail
  return dom

def inferType' (e : Expr) (inferOnly : Bool) : RecM Expr := do
  if e.isBVar then
    throw <| .other
      s!"type checker does not support loose bound variables, {""
        }replace them with free variables before invoking it"
  assert! !e.hasLooseBVars
  let state ← get
  if let some r := (cond inferOnly state.inferTypeI state.inferTypeC).find? e then
    return r
  let r ← match e with
    | .lit l => pure l.type
    | .mdata _ e => inferType' e inferOnly
    | .proj s idx e => inferProj s idx e (← inferType' e inferOnly)
    | .fvar n => inferFVar (← readThe Context) n
    | .mvar _ => throw <| .other "kernel type checker does not support meta variables"
    | .bvar _ => unreachable!
    | .sort l =>
      if !inferOnly then
        checkLevel (← readThe Context) l
      pure <| .sort (.succ l)
    | .const c ls => inferConstant (← readThe Context) c ls inferOnly
    | .lam .. => inferLambda e inferOnly
    | .forallE .. => inferForall e inferOnly
    | .app f a =>
      if inferOnly then
        inferApp e
      else
        let fType ← ensureForallCore (← inferType' f inferOnly) e
        let aType ← inferType' a inferOnly
        let dType := fType.bindingDomain!
        if !(← isDefEq dType aType) then
          throw <| .appTypeMismatch (← getEnv) (← getLCtx) e fType aType
        return fType.bindingBody!.instantiate1 a
    | .letE .. => inferLet e inferOnly
  modify fun s => cond inferOnly
    { s with inferTypeI := s.inferTypeI.insert e r }
    { s with inferTypeC := s.inferTypeC.insert e r }
  return r

def whnfCore (e : Expr) (cheapRec := false) (cheapProj := false) : RecM Expr :=
  fun m => m.whnfCore e cheapRec cheapProj

def reduceRecursor (e : Expr) (cheapRec cheapProj : Bool) : RecM (Option Expr) := do
  let env ← getEnv
  if env.header.quotInit then
    if let some r ← quotReduceRec e whnf then
      return r
  let whnf' e := if cheapRec then whnfCore e cheapRec cheapProj else whnf e
  if let some r ← inductiveReduceRec env e whnf' inferType isDefEq then
    return r
  return none

def whnfFVar (e : Expr) (cheapRec cheapProj : Bool) : RecM Expr := do
  if let some (.ldecl (value := v) ..) := (← getLCtx).find? e.fvarId! then
    return ← whnfCore v cheapRec cheapProj
  return e

def reduceProj (idx : Nat) (struct : Expr) (cheapRec cheapProj : Bool) : RecM (Option Expr) := do
  let mut c ← (if cheapProj then whnfCore struct cheapRec cheapProj else whnf struct)
  if let .lit (.strVal s) := c then
    c := .strLitToConstructor s
  c.withApp fun mk args => do
  let .const mkC _ := mk | return none
  let env ← getEnv
  let .ctorInfo mkInfo ← env.get mkC | return none
  return args[mkInfo.numParams + idx]?

def isLetFVar (lctx : LocalContext) (fvar : FVarId) : Bool :=
  lctx.find? fvar matches some (.ldecl ..)

def whnfCore' (e : Expr) (cheapRec := false) (cheapProj := false) : RecM Expr := do
  match e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .const .. | .lam .. | .lit .. => return e
  | .mdata _ e => return ← whnfCore' e cheapRec cheapProj
  | .fvar id => if !isLetFVar (← getLCtx) id then return e
  | .app .. | .letE .. | .proj .. => pure ()
  if let some r := (← get).whnfCoreCache.find? e then
    return r
  let save r := do
    if !cheapRec && !cheapProj then
      modify fun s => { s with whnfCoreCache := s.whnfCoreCache.insert e r }
    return r
  match e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .const .. | .lam .. | .lit ..
  | .mdata .. => unreachable!
  | .fvar _ => return ← whnfFVar e cheapRec cheapProj
  | .app .. =>
    e.withAppRev fun f0 rargs => do
    let f ← whnfCore f0 cheapRec cheapProj
    if let .lam _ _ body _ := f then
      let rec loop m (f : Expr) : RecM Expr :=
        let cont2 := do
          let r := f.instantiateRange (rargs.size - m) rargs.size rargs
          let r := r.mkAppRevRange 0 (rargs.size - m) rargs
          save <|← whnfCore r cheapRec cheapProj
        if let .lam _ _ body _ := f then
          if m < rargs.size then loop (m + 1) body
          else cont2
        else cont2
      loop 1 body
    else if f == f0 then
      if let some r ← reduceRecursor e cheapRec cheapProj then
        whnfCore r cheapRec cheapProj
      else
        pure e
    else
      let r := f.mkAppRevRange 0 rargs.size rargs
      save <|← whnfCore r cheapRec cheapProj
  | .letE _ _ val body _ =>
    save <|← whnfCore (body.instantiate1 val) cheapRec cheapProj
  | .proj _ idx s =>
    if let some m ← reduceProj idx s cheapRec cheapProj then
      save <|← whnfCore m cheapRec cheapProj
    else
      save e

def isDelta (env : Environment) (e : Expr) : Option ConstantInfo := do
  if let .const c _ := e.getAppFn then
    if let some ci := env.find? c then
      if ci.hasValue then
        return ci
  none

def unfoldDefinitionCore (env : Environment) (e : Expr) : Option Expr := do
  if let .const _ ls := e then
    if let some d := isDelta env e then
      if ls.length == d.numLevelParams then
        return d.instantiateValueLevelParams! ls
  none

def unfoldDefinition (env : Environment) (e : Expr) : Option Expr := do
  if e.isApp then
    let f0 := e.getAppFn
    if let some f := unfoldDefinitionCore env f0 then
      let rargs := e.getAppRevArgs
      return f.mkAppRevRange 0 rargs.size rargs
    none
  else
    unfoldDefinitionCore env e

def reduceNative (_env : Environment) (e : Expr) : Except KernelException (Option Expr) := do
  let .app f (.const c _) := e | return none
  if f == .const ``reduceBool [] then
    throw <| .other s!"lean4lean does not support 'reduceBool {c}' reduction"
  else if f == .const ``reduceNat [] then
    throw <| .other s!"lean4lean does not support 'reduceNat {c}' reduction"
  return none

def natLitExt? (e : Expr) : Option Nat := if e == .natZero then some 0 else e.natLit?

def reduceBinNatOp (f : Nat → Nat → Nat) (a b : Expr) : RecM (Option Expr) := do
  let some v1 := natLitExt? (← whnf a) | return none
  let some v2 := natLitExt? (← whnf b) | return none
  return some <| .lit <| .natVal <| f v1 v2

def reduceBinNatPred (f : Nat → Nat → Bool) (a b : Expr) : RecM (Option Expr) := do
  let some v1 := natLitExt? (← whnf a) | return none
  let some v2 := natLitExt? (← whnf b) | return none
  return toExpr <| f v1 v2

def reduceNat (e : Expr) : RecM (Option Expr) := do
  if e.hasFVar then return none
  let nargs := e.getAppNumArgs
  if nargs == 1 then
    let f := e.appFn!
    if f == .const ``Nat.succ [] then
      let some v := natLitExt? (← whnf e.appArg!) | return none
      return some <| .lit <| .natVal <| v + 1
  else if nargs == 2 then
    let .app (.app (.const f _) a) b := e | return none
    if f == ``Nat.add then return ← reduceBinNatOp Nat.add a b
    if f == ``Nat.sub then return ← reduceBinNatOp Nat.sub a b
    if f == ``Nat.mul then return ← reduceBinNatOp Nat.mul a b
    if f == ``Nat.pow then return ← reduceBinNatOp Nat.pow a b
    if f == ``Nat.mod then return ← reduceBinNatOp Nat.mod a b
    if f == ``Nat.div then return ← reduceBinNatOp Nat.div a b
    if f == ``Nat.beq then return ← reduceBinNatPred Nat.beq a b
    if f == ``Nat.ble then return ← reduceBinNatPred Nat.ble a b
  return none


def whnf' (e : Expr) : RecM Expr := do
  -- Do not cache easy cases
  match e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .lit .. => return e
  | .mdata _ e => return ← whnf' e
  | .fvar id =>
    if !isLetFVar (← getLCtx) id then
      return e
  | .lam .. | .app .. | .const .. | .letE .. | .proj .. => pure ()
  -- check cache
  if let some r := (← get).whnfCache.find? e then
    return r
  let rec loop t
  | 0 => throw .deterministicTimeout
  | fuel+1 => do
    let env ← getEnv
    let t ← whnfCore' t
    if let some t ← reduceNative env t then return t
    if let some t ← reduceNat t then return t
    let some t := unfoldDefinition env t | return t
    loop t fuel
  let r ← loop e 1000
  modify fun s => { s with whnfCache := s.whnfCache.insert e r }
  return r

def isDefEqLambda (t s : Expr) (subst : Array Expr := #[]) : RecM Bool :=
  match t, s with
  | .lam _ tDom tBody _, .lam name sDom sBody bi => do
    let sType ← if tDom != sDom then
      let sType := sDom.instantiateRev subst
      let tType := tDom.instantiateRev subst
      if !(← isDefEq tType sType) then return false
      pure (some sType)
    else pure none
    if tBody.hasLooseBVars || sBody.hasLooseBVars then
      let sType := sType.getD (sDom.instantiateRev subst)
      let id := ⟨← mkFreshId⟩
      withLCtx ((← getLCtx).mkLocalDecl id name sType bi) do
        isDefEqLambda tBody sBody (subst.push (.fvar id))
    else
      isDefEqLambda tBody sBody (subst.push default)
  | t, s => isDefEq (t.instantiateRev subst) (s.instantiateRev subst)

def isDefEqForall (t s : Expr) (subst : Array Expr := #[]) : RecM Bool :=
  match t, s with
  | .forallE _ tDom tBody _, .forallE name sDom sBody bi => do
    let sType ← if tDom != sDom then
      let sType := sDom.instantiateRev subst
      let tType := tDom.instantiateRev subst
      if !(← isDefEq tType sType) then return false
      pure (some sType)
    else pure none
    if tBody.hasLooseBVars || sBody.hasLooseBVars then
      let sType := sType.getD (sDom.instantiateRev subst)
      let id := ⟨← mkFreshId⟩
      withLCtx ((← getLCtx).mkLocalDecl id name sType bi) do
        isDefEqForall tBody sBody (subst.push (.fvar id))
    else
      isDefEqForall tBody sBody (subst.push default)
  | t, s => isDefEq (t.instantiateRev subst) (s.instantiateRev subst)

def quickIsDefEq (t s : Expr) (useHash := false) : RecM LBool := do
  if ← modifyGet fun st =>
    let (b, m) := st.eqvManager.isEquiv useHash t s
    (b, { st with eqvManager := m })
  then return .true
  match t, s with
  | .lam .., .lam .. => toLBoolM <| isDefEqLambda t s
  | .forallE .., .forallE .. => toLBoolM <| isDefEqForall t s
  | .sort a1, .sort a2 => pure (a1.isEquiv a2).toLBool
  | .mdata _ a1, .mdata _ a2 => toLBoolM <| isDefEq a1 a2
  | .mvar .., .mvar .. => unreachable!
  | .lit a1, .lit a2 => pure (a1 == a2).toLBool
  | _, _ => return .undef

def isDefEqArgs (t s : Expr) : RecM Bool := do
  match t, s with
  | .app tf ta, .app sf sa =>
    if !(← isDefEq ta sa) then return false
    isDefEqArgs tf sf
  | .app .., _ | _, .app .. => return false
  | _, _ => return true

def tryEtaExpansionCore (t s : Expr) : RecM Bool := do
  if t.isLambda && !s.isLambda then
    let .forallE name ty _ bi ← whnf (← inferType s) | return false
    isDefEq t (.lam name ty (.app s (.bvar 0)) bi)
  else return false

def tryEtaExpansion (t s : Expr) : RecM Bool :=
  tryEtaExpansionCore t s <||> tryEtaExpansionCore s t

def tryEtaStructCore (t s : Expr) : RecM Bool := do
  let .const f _ := s.getAppFn | return false
  let env ← getEnv
  let .ctorInfo fInfo ← env.get f | return false
  unless s.getAppNumArgs == fInfo.numParams + fInfo.numFields do return false
  unless isStructureLike env fInfo.induct do return false
  unless ← isDefEq (← inferType t) (← inferType s) do return false
  let args := s.getAppArgs
  for h : i in [fInfo.numParams:args.size] do
    unless ← isDefEq (.proj fInfo.induct (i - fInfo.numParams) t) (args[i]'h.2) do return false
  return true

def tryEtaStruct (t s : Expr) : RecM Bool :=
  tryEtaStructCore t s <||> tryEtaStructCore s t

def isDefEqApp (t s : Expr) : RecM Bool := do
  unless t.isApp && s.isApp do return false
  t.withApp fun tf tArgs =>
  s.withApp fun sf sArgs => do
  unless tArgs.size == sArgs.size do return false
  unless ← isDefEq tf sf do return false
  for ta in tArgs, sa in sArgs do
    unless ← isDefEq ta sa do return false
  return true

def isDefEqProofIrrel (t s : Expr) : RecM LBool := do
  let tType ← inferType t
  if !(← isProp tType) then return .undef
  toLBoolM <| isDefEq tType (← inferType s)

def failedBefore (failure : HashSet (Expr × Expr)) (t s : Expr) : Bool :=
  if t.hash < s.hash then
    failure.contains (t, s)
  else if t.hash > s.hash then
    failure.contains (s, t)
  else
    failure.contains (t, s) || failure.contains (s, t)

def cacheFailure (t s : Expr) : M Unit := do
  let k := if t.hash ≤ s.hash then (t, s) else (s, t)
  modify fun st => { st with failure := st.failure.insert k }

def tryUnfoldProjApp (e : Expr) : RecM (Option Expr) := do
  let f := e.getAppFn
  if !f.isProj then return none
  let e' ← whnfCore e
  return if e' != e then e' else none

def lazyDeltaReductionStep (tn sn : Expr) : RecM ReductionStatus := do
  let env ← getEnv
  let delta e := whnfCore (unfoldDefinition env e).get! (cheapProj := true)
  let cont tn sn :=
    return match ← quickIsDefEq tn sn with
    | .undef => .continue tn sn
    | .true => .bool true
    | .false => .bool false
  match isDelta env tn, isDelta env sn with
  | none, none => return .unknown tn sn
  | some _, none =>
    if let some sn' ← tryUnfoldProjApp sn then
      cont tn sn'
    else
      cont (← delta tn) sn
  | none, some _ =>
    if let some tn' ← tryUnfoldProjApp tn then
      cont tn' sn
    else
      cont tn (← delta sn)
  | some dt, some ds =>
    let ht := dt.hints
    let hs := ds.hints
    if ht.lt hs then
      cont (← delta tn) sn
    else if hs.lt ht then
      cont tn (← delta sn)
    else
      if tn.isApp && sn.isApp && (unsafe ptrEq dt ds) && dt.hints.isRegular
        && !failedBefore (← get).failure tn sn
      then
        if Level.isEquivList tn.getAppFn.constLevels! sn.getAppFn.constLevels! then
          if ← isDefEqArgs tn sn then
            return .bool true
        cacheFailure tn sn
      cont (← delta tn) (← delta sn)

@[inline] def isNatZero (t : Expr) : Bool :=
  t == .natZero || t matches .lit (.natVal 0)

def isNatSuccOf? : Expr → Option Expr
  | .lit (.natVal (n+1)) => return .lit (.natVal n)
  | .app (.const ``Nat.succ _) e => return e
  | _ => none

def isDefEqOffset (t s : Expr) : RecM LBool := do
  if isNatZero t && isNatZero s then
    return .true
  match isNatSuccOf? t, isNatSuccOf? s with
  | some t', some s' => toLBoolM <| isDefEqCore t' s'
  | _, _ => return .undef

def lazyDeltaReduction (tn sn : Expr) : RecM ReductionStatus := loop tn sn 1000 where
  loop tn sn
  | 0 => throw .deterministicTimeout
  | fuel+1 => do
    let r ← isDefEqOffset tn sn
    if r != .undef then return .bool (r == .true)
    if !tn.hasFVar && !sn.hasFVar then
      if let some tn' ← reduceNat tn then
        return .bool (← isDefEqCore tn' sn)
      else if let some sn' ← reduceNat sn then
        return .bool (← isDefEqCore tn sn')
    let env ← getEnv
    if let some tn' ← reduceNative env tn then
      return .bool (← isDefEqCore tn' sn)
    else if let some sn' ← reduceNative env sn then
      return .bool (← isDefEqCore tn sn')
    match ← lazyDeltaReductionStep tn sn with
    | .continue tn sn => loop tn sn fuel
    | r => return r

def tryStringLitExpansionCore (t s : Expr) : RecM LBool := do
  let .lit (.strVal st) := t | return .undef
  let .app sf _ := s | return .undef
  unless sf == .const ``String.mk [] do return .undef
  toLBoolM <| isDefEqCore (.strLitToConstructor st) s

def tryStringLitExpansion (t s : Expr) : RecM LBool := do
  match ← tryStringLitExpansionCore t s with
  | .undef => tryStringLitExpansionCore s t
  | r => return r

def isDefEqUnitLike (t s : Expr) : RecM Bool := do
  let tType ← whnf (← inferType t)
  let .const I _ := tType.getAppFn | return false
  let env ← getEnv
  let .inductInfo { isRec := false, ctors := [c], numIndices := 0, .. } ← env.get I
    | return false
  let .ctorInfo { numFields := 0, .. } ← env.get c | return false
  isDefEqCore tType (← inferType s)

def isDefEqCore' (t s : Expr) : RecM Bool := do
  let r ← quickIsDefEq t s (useHash := true)
  if r != .undef then return r == .true

  if !t.hasFVar && s.isConstOf ``true then
    if (← whnf t).isConstOf ``true then return true

  let tn ← whnfCore t (cheapProj := true)
  let sn ← whnfCore s (cheapProj := true)

  if !(unsafe ptrEq tn t && ptrEq sn s) then
    let r ← quickIsDefEq tn sn (useHash := true)
    if r != .undef then return r == .true

  let r ← isDefEqProofIrrel tn sn
  if r != .undef then return r == .true

  match ← lazyDeltaReduction tn sn with
  | .continue .. => unreachable!
  | .bool b => return b
  | .unknown tn sn =>

  match tn, sn with
  | .const tf tl, .const sf sl =>
    if tf == sf && Level.isEquivList tl sl then return true
  | .fvar tv, .fvar sv => if tv == sv then return true
  | .proj _ ti te, .proj _ si se =>
    if ti == si then if ← isDefEq te se then return true
  | _, _ => pure ()

  let tnn ← whnfCore tn
  let snn ← whnfCore sn
  if !(unsafe ptrEq tnn tn && ptrEq snn sn) then
    return ← isDefEqCore tnn snn

  if ← isDefEqApp tn sn then return true
  if ← tryEtaExpansion tn sn then return true
  if ← tryEtaStruct tn sn then return true
  let r ← tryStringLitExpansion tn sn
  if r != .undef then return r == .true
  if ← isDefEqUnitLike tn sn then return true
  return false

end Inner

open Inner

def Methods.withFuel : Nat → Methods
  | 0 =>
    { isDefEqCore := fun _ _ => throw .deepRecursion
      whnfCore := fun _ _ _ => throw .deepRecursion
      whnf := fun _ => throw .deepRecursion
      inferType := fun _ _ => throw .deepRecursion }
  | n + 1 =>
    { isDefEqCore := fun t s => isDefEqCore' t s (withFuel n)
      whnfCore := fun e r p => whnfCore' e r p (withFuel n)
      whnf := fun e => whnf' e (withFuel n)
      inferType := fun e i => inferType' e i (withFuel n) }

def RecM.run (x : RecM α) : M α := x (Methods.withFuel 1000)

def check (e : Expr) (lps : List Name) : M Expr :=
  withReader ({ · with lparams := lps }) (inferType e (inferOnly := false)).run

def checkIgnoreUndefinedUniverses (e : Expr) : M Expr :=
  withReader ({ · with lparams := none }) (inferType e (inferOnly := false)).run

def whnf (e : Expr) : M Expr := (Inner.whnf e).run

def inferType (e : Expr) : M Expr := (Inner.inferType e).run

def isDefEq (t s : Expr) : M Bool := (Inner.isDefEq t s).run

def ensureSort (t : Expr) (s := t) : M Expr := (ensureSortCore t s).run

def ensureForall (t : Expr) (s := t) : M Expr := (ensureForallCore t s).run

def ensureType (e : Expr) : M Expr := do ensureSort (← inferType e) e

def etaExpand (e : Expr) : M Expr :=
  let rec loop fvars
  | .lam name dom body bi => do
    let d := dom.instantiateRev fvars
    let id := ⟨← mkFreshId⟩
    withLCtx ((← getLCtx).mkLocalDecl id name d bi) do
      let fvars := fvars.push (.fvar id)
      loop fvars body
  | it => do
    let itType ← whnf <| ← inferType <| it.instantiateRev fvars
    if !itType.isForall then return e
    let rec loop2 fvars args
    | 0, _ => throw .deepRecursion
    | fuel + 1, .forallE name dom body bi => do
      let d := dom.instantiateRev fvars
      let id := ⟨← mkFreshId⟩
      withLCtx ((← getLCtx).mkLocalDecl id name d bi) do
        let arg := .fvar id
        let fvars := fvars.push arg
        let args := args.push arg
        loop2 fvars args fuel <| ← whnf <| body.instantiate1 arg
    | _, it => return (← getLCtx).mkLambda fvars (mkAppN it args)
    loop2 fvars #[] 1000 itType
  loop #[] e
