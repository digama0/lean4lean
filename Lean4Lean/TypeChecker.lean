import Lean4Lean.WHNFCacheKey
import Lean4Lean.Declaration
import Lean4Lean.Level
import Lean4Lean.Quot
import Lean4Lean.Inductive.Reduce
import Lean4Lean.Instantiate
import Lean4Lean.ForEachExprV
import Lean4Lean.EquivManager
import Lean4Lean.FuelConfig

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

abbrev InferCache := ExprMap Expr

structure TypeChecker.State where
  ngen : NameGenerator := { namePrefix := `_kernel_fresh, idx := 0 }
  inferTypeI : InferCache := {}
  inferTypeC : InferCache := {}
  whnfCoreCache : ExprMap Expr := {}
  whnfCache : ExprMap Expr := {}
  eqvManager : EquivManager := {}
  failure : Std.HashSet (Expr × Expr) := {}
  unfold : ExprMap Expr := {}

structure TypeChecker.Context where
  env : Environment
  lctx : LocalContext := {}
  safety : DefinitionSafety := .safe
  eagerReduce := false
  lparams : List Name := []
  fuel : FuelConfig := {}

namespace TypeChecker

abbrev M := ReaderT Context <| StateT State <| Except Exception

def M.run (env : Environment) (safety : DefinitionSafety := .safe)
    (lctx : LocalContext := {}) (lparams : List Name := []) (fuel : FuelConfig := {})
    (x : M α) : Except Exception α :=
  x { env, safety, lctx, lparams, fuel } |>.run' {}

def M.runTermElab (m : M α) (safety := DefinitionSafety.safe) : Elab.Term.TermElabM α := do
  ofExceptKernelException <| m.run (env := (← getEnv).toKernelEnv)
    (lctx := ← getLCtx) (safety := safety) (lparams := (← get).levelNames)

instance : MonadLift M Elab.Term.TermElabM := ⟨M.runTermElab⟩

def getEnv : M Environment := return (← read).env

instance : MonadLCtx M where
  getLCtx := return (← read).lctx

instance [Monad m] : MonadNameGenerator (StateT State m) where
  getNGen := return (← get).ngen
  setNGen ngen := modify fun s => { s with ngen }

/-- The state on leaving a binder scope entered from `saved`. The name generator stays advanced, so
that names are never reused, and the `unfold` cache is kept because it depends only on the
environment. Everything that records a judgement relative to the local context -- the inference and
reduction caches, the equivalence manager and the failure cache -- is put back to what it was
before the binder was opened. This is scoped so that no conversion fact outlives its binder: a fact
found under a binder can hold there without holding in the smaller context, even when it does not
mention the bound variable. -/
def State.leaveScope (saved s : State) : State :=
  { saved with ngen := s.ngen, unfold := s.unfold }

/-- The state on leaving a binder scope entered from `saved`, in cache mode `mode`: in the scoped
mode `State.leaveScope`, in the global mode the state of the body unchanged. -/
def State.exitScope : CacheMode → State → State → State
  | .scoped, saved, s => saved.leaveScope s
  | .global _, _, s => s

/-- Runs `x` with a fresh free variable. In the scoped cache mode (the default) the scope is
closed with `State.leaveScope`, so that no conversion fact outlives its binder. In the global cache
mode nothing is restored, as in the C++ kernel, whose caches belong to the whole run. Every binder
of the checker (`withLocalDecl`, `withLetDecl`) opens its scope through this. -/
instance : MonadLocalNameGenerator M where
  withFreshId x := do
    match (← read).fuel.cacheMode with
    | .scoped =>
      let saved ← get
      let r ← x (← mkFreshId)
      modify saved.leaveScope
      pure r
    | .global _ => x (← mkFreshId)

instance (priority := low) : MonadWithReaderOf LocalContext M where
  withReader f := withReader fun s => { s with lctx := f s.lctx }

structure Methods where
  protected isDefEqCore : Expr → Expr → M Bool
  protected whnfCore (e : Expr) (cheapProj := false) : M Expr
  protected whnf (e : Expr) : M Expr
  protected inferType (e : Expr) (inferOnly : Bool) : M Expr

abbrev RecM := ReaderT Methods M

inductive ReductionStatus where
  | continue (tn sn : Expr)
  | unknown (tn sn : Expr)
  | true
  | false (tn sn : Expr)

def ReductionStatus.bool (tn sn : Expr) : Bool → ReductionStatus
  | .true => .true
  | .false => .false tn sn

namespace Inner

/-- Reduces `e` to its weak-head normal form. -/
def whnf (e : Expr) : RecM Expr := fun m => m.whnf e

@[inline] def withLCtx [MonadWithReaderOf LocalContext m] (lctx : LocalContext) (x : m α) : m α :=
  withReader (fun _ => lctx) x

/-- Ensures that `e` is defeq to some `e' := .sort ..`, returning `e'`. If not, throws an error with
`s` (the expression required to be a sort). -/
def ensureSortCore (e s : Expr) : RecM Expr := do
  if e.isSort then return e
  let e ← whnf e
  if e.isSort then return e
  throw <| .typeExpected (← getEnv) (← getLCtx) s

/-- Ensures that `e` is defeq to some `e' := .forallE ..`, returning `e'`. If not, throws an error
with `s := f a` (the application requiring `f` to be of function type). -/
def ensureForallCore (e s : Expr) : RecM Expr := do
  if e.isForall then return e
  let e ← whnf e
  if e.isForall then return e
  throw <| .funExpected (← getEnv) (← getLCtx) s

/-- Checks that `l` does not contain any level parameters not found in the context `tc`. -/
def checkLevel (tc : Context) (l : Level) : Except Exception Unit := do
  if let some n2 := l.getUndefParam tc.lparams then
    throw <| .other s!"invalid reference to undefined universe level parameter '{n2}'"

def inferFVar (tc : Context) (name : FVarId) : Except Exception Expr := do
  if let some decl := tc.lctx.find? name then
    return decl.type
  throw <| .other "unknown free variable"

/-- Infers the type of `.const name ls`. -/
def inferConstant (tc : Context) (name : Name) (ls : List Level) (inferOnly : Bool) :
    Except Exception Expr := do
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

/-- Infers the type of expression `e`. If `inferOnly := false`, this function throws an error
whenever `e` is not typeable according to Lean's algorithmic typing judgment (barring resource
exhaustion: it may also throw `.deterministicTimeout` or `.deepRecursion` on a typeable term).
Setting `inferOnly := true` optimizes to avoid unnecessary checks in the case that `e` is already
known to be well-typed. -/
def inferType (e : Expr) (inferOnly := true) : RecM Expr := fun m => m.inferType e inferOnly

/-- Infers the type of lambda expression `e`. -/
def inferLambda (e : Expr) (inferOnly : Bool) : RecM Expr := loop #[] e where
  loop fvars : Expr → RecM Expr
  | .lam name dom body bi => do
    let d := dom.instantiateRev fvars
    if !inferOnly then
      _ ← ensureSortCore (← inferType d inferOnly) d
    withLocalDecl name bi d fun fv => do
      let fvars := fvars.push fv
      loop fvars body
  | e => do
    let r ← inferType (e.instantiateRev fvars) inferOnly
    let r := r.cheapBetaReduce
    return (← getLCtx).mkForall fvars r

/-- Infers the type of for-all expression `e`. -/
def inferForall (e : Expr) (inferOnly : Bool) : RecM Expr := loop #[] #[] e where
  loop fvars us : Expr → RecM Expr
  | .forallE name dom body bi => do
    let d := dom.instantiateRev fvars
    let t1 ← ensureSortCore (← inferType d inferOnly) d
    let us := us.push t1.sortLevel!
    withLocalDecl name bi d fun fv =>
      loop (fvars.push fv) us body
  | e => do
    let r ← inferType (e.instantiateRev fvars) inferOnly
    let s ← ensureSortCore r e
    return .sort <| us.foldr mkLevelIMax' s.sortLevel!

/-- Returns whether `t` and `s` are definitionally equal according to Lean's algorithmic
definitional equality judgment.

NOTE: This function does not do any typechecking of its own on `t` and `s`. So, when this is used as
part of a typechecking routine, it is expected that they are already well-typed (that is, that
`checkType t` and `checkType s` did not/would not throw an error). This is what justifies the
internal uses of `inferType` at its default `inferOnly := true`: on a well-typed subterm the fast
path returns the same type the checking path would have. -/
def isDefEqCore (t s : Expr) : RecM Bool := fun m => m.isDefEqCore t s

@[inherit_doc isDefEqCore]
def isDefEq (t s : Expr) : RecM Bool := do
  let r ← isDefEqCore t s
  if r then
    modify fun st => { st with eqvManager := st.eqvManager.addEquiv t s }
  pure r

/-- Infers the type of application `e`, assuming that `e` is already well-typed. -/
def inferApp (e : Expr) : RecM Expr := do
  e.withApp fun f args =>
  let rec loop fType j i : RecM Expr :=
    if i < args.size then
      match fType with
      | .forallE _ _ body _ => loop body j (i+1)
      | _ => do
        let fType := fType.instantiateRevRange j i args
        let fType := (← ensureForallCore fType e).bindingBody!
        loop fType i (i+1)
    else
      return fType.instantiateRevRange j args.size args
  do loop (← inferType f) 0 0

/-- Infers the type of let-expression `e`. -/
def inferLet (e : Expr) (inferOnly : Bool) : RecM Expr := loop #[] e where
  loop fvars : Expr → RecM Expr
  | .letE name type val body _ => do
    let type := type.instantiateRev fvars
    let val := val.instantiateRev fvars
    if !inferOnly then
      _ ← ensureSortCore (← inferType type inferOnly) type
      let valType ← inferType val inferOnly
      if !(← isDefEq valType type) then
        throw <| .letTypeMismatch (← getEnv) (← getLCtx) name valType type
    withLetDecl name type val fun fv =>
      loop (fvars.push fv) body
  | e => do
    let r ← inferType (e.instantiateRev fvars) inferOnly
    let r := r.cheapBetaReduce
    return (← getLCtx).mkForall fvars r

/-- Gets the universe level of the sort that `e`'s type is defeq to, failing if `e` is not
a type. -/
def getSortLevel (e : Expr) : RecM Level := do
  let .sort u ← ensureSortCore (← inferType e) e | unreachable!
  return u

/-- Checks if `e` is a proposition, that is, if its type is a sort whose level normalizes to
zero. -/
def isProp (e : Expr) : RecM Bool := return (← getSortLevel e).isAlwaysZero

/-- Instantiate the common-parameter prefix of a constructor telescope. -/
def instantiateProjectionParameters (type : Expr) (args : Array Expr) :
    Nat → Nat → RecM (Option Expr)
  | _, 0 => pure (some type)
  | position, remaining + 1 => do
    let .forallE _ _ body _ ← whnf type | return none
    let some argument := args[position]? | return none
    instantiateProjectionParameters (body.instantiate1 argument) args
      (position + 1) remaining

/-- Instantiate the fields preceding a selected projection field. -/
def instantiateProjectionFields (typeName : Name) (struct : Expr)
    (maybePropType : Bool) : Expr → Nat → Nat → RecM (Option Expr)
  | type, _, 0 => pure (some type)
  | type, position, remaining + 1 => do
    let .forallE _ domain body _ ← whnf type | return none
    if body.hasLooseBVars then
      if maybePropType then
        unless ← isProp domain do return none
      instantiateProjectionFields typeName struct maybePropType
        (body.instantiate1 (.proj typeName position struct))
        (position + 1) remaining
    else
      instantiateProjectionFields typeName struct maybePropType body
        (position + 1) remaining

/-- Infers the type of a structure projection. -/
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
  let some afterParameters ← instantiateProjectionParameters
      (c_info.instantiateTypeLevelParams I_levels) args 0 I_val.numParams
    | fail
  let maybePropType := !(← getSortLevel type).isNeverZero
  let some selected ← instantiateProjectionFields typeName struct maybePropType
      afterParameters 0 idx
    | fail
  let .forallE _ domain _ _ ← whnf selected | fail
  if maybePropType then if !(← isProp domain) then fail
  return domain

@[inherit_doc inferType]
def inferType' (e : Expr) (inferOnly : Bool) : RecM Expr := do
  if e.hasLooseBVars then
    throw <| .other
      s!"type checker does not support loose bound variables, \
         replace them with free variables before invoking it"
  let state ← get
  if let some r := (cond inferOnly state.inferTypeI state.inferTypeC)[e]? then
    return r
  let r ← match e with
    | .lit l =>
      if !inferOnly then
        match l with
        | .natVal _ => _ ← (← getEnv).get ``Nat
        | .strVal _ => _ ← (← getEnv).get ``Char.ofNat; _ ← (← getEnv).get ``String.ofList
      pure (mkConst l.typeName)
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
        -- it can be shown that if `e` is typeable as `T`, then `T` is typeable as `Sort l`
        -- for some universe level `l`, so this use of `isDefEq` is valid
        let ok ← if a.isAppOfArity ``eagerReduce 2 then
          withTheReader Context (fun s => {s with eagerReduce := true}) <|
            isDefEq dType aType
        else
          isDefEq dType aType
        if !ok then throw <| .appTypeMismatch (← getEnv) (← getLCtx) e fType aType
        pure <| fType.bindingBody!.instantiate1 a
    | .letE .. => inferLet e inferOnly
  modify fun s => cond inferOnly
    { s with inferTypeI := s.inferTypeI.insert e r }
    { s with inferTypeC := s.inferTypeC.insert e r }
  return r

/-- Reduces `e` to its weak-head normal form, without unfolding definitions. This is a conservative
version of `whnf` (which does unfold definitions), to be used for efficiency purposes.

Setting `cheapProj` to `true` will cause the struct argument to be reduced "lazily" (using
`whnfCore` rather than `whnf`) when reducing struct projections, and suppresses caching of the
result. This can be a useful optimization if we're checking the definitional equality of two struct
projections of the same projection, where we might save some work by directly checking if the struct
arguments are defeq (rather than eagerly applying a projection).

Recursor reduction does not use an analogous flag. -/
def whnfCore (e : Expr) (cheapProj := false) : RecM Expr :=
  fun m => m.whnfCore e cheapProj

def reduceRecursor (e : Expr) : RecM (Option Expr) := do
  let env ← getEnv
  if env.quotInit then
    if let some r ← quotReduceRec e whnf then
      return r
  if let some r ← inductiveReduceRec env e whnf inferType isDefEq then
    return r
  return none

/-- Reduces the free variable `e`: to the `whnfCore` of its definition if `e` is a let variable,
and to itself if it is a lambda variable. -/
def whnfFVar (e : Expr) (cheapProj : Bool) : RecM Expr := do
  if let some (.ldecl (value := v) ..) := (← getLCtx).find? e.fvarId! then
    return ← whnfCore v cheapProj
  return e

/-- Reduce a projection whose structure argument has already been reduced to a constructor
application.

As in `type_checker::reduce_proj_core`, the head must be a constructor of `structName`, and the
selected argument need only be present. -/
def reduceProjCoreCont (structName : Name) (idx : Nat) (c : Expr) : RecM (Option Expr) :=
  c.withApp fun mk args => do
  let .const mkC _ := mk | return none
  let env ← getEnv
  let .ctorInfo mkInfo ← env.get mkC | return none
  unless mkInfo.induct == structName do return none
  return args[mkInfo.numParams + idx]?

@[inherit_doc reduceProjCoreCont]
def reduceProjCore (structName : Name) (idx : Nat) (struct : Expr) : RecM (Option Expr) := do
  let c ← if let .lit (.strVal s) := struct then whnf (.strLitToConstructor s) else pure struct
  reduceProjCoreCont structName idx c

/-- Reduces a projection of `struct` at index `idx` (when `struct` is reducible to a constructor
application). -/
def reduceProj (structName : Name) (idx : Nat) (struct : Expr) (cheapProj : Bool) :
    RecM (Option Expr) :=
  (if cheapProj then whnfCore struct cheapProj else whnf struct) >>= reduceProjCore structName idx

def isLetFVar (lctx : LocalContext) (fvar : FVarId) : Bool :=
  lctx.find? fvar matches some (.ldecl ..)

@[inherit_doc whnfCore]
def whnfCore' (e : Expr) (cheapProj := false) : RecM Expr := do
  match e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .const .. | .lam .. | .lit .. => return e
  | .mdata _ e => return ← whnfCore' e cheapProj
  | .fvar id => if !isLetFVar (← getLCtx) id then return e
  | .app .. | .letE .. | .proj .. => pure ()
  if let some r := (← get).whnfCoreCache[e]? then
    return r
  let rec save r := do
    if !cheapProj && whnfCacheKey e then
      modify fun s => { s with whnfCoreCache := s.whnfCoreCache.insert e r }
    return r
  match e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .const .. | .lam .. | .lit ..
  | .mdata .. => unreachable!
  | .fvar _ => return ← whnfFVar e cheapProj
  | .app .. =>
    -- beta-reduce at the head as much as possible, apply any remaining `rargs`
    -- to the resulting expression, and re-run `whnfCore`
    e.withAppRev fun f0 rargs => do
    -- the head may still be a let variable/binding, projection, or mdata-wrapped expression
    let f ← whnfCore f0 cheapProj
    if let .lam _ _ body _ := f then
      let rec loop m (f : Expr) : RecM Expr :=
        let rec cont := do
          let r := f.instantiateRange (rargs.size - m) rargs.size rargs
          let r := r.mkAppRevRange 0 (rargs.size - m) rargs
          save <|← whnfCore r cheapProj
        if let .lam _ _ body _ := f then
          if m < rargs.size then loop (m + 1) body
          else cont
        else cont
      loop 1 body
    else if f == f0 then
      if let some r ← reduceRecursor e then
        whnfCore r cheapProj
      else
        pure e
    else
      let r := f.mkAppRevRange 0 rargs.size rargs
      -- Re-enter reduction after rebuilding the complete application spine.
      save <|← whnfCore r cheapProj
  | .letE _ _ val body _ =>
    save <|← whnfCore (body.instantiate1 val) cheapProj
  | .proj structName idx s =>
    if let some m ← reduceProj structName idx s cheapProj then
      save <|← whnfCore m cheapProj
    else
      save e

/-- Checks if the head of `e` is a constant that can be delta-reduced, applied to the right number
of universe levels, returning its `ConstantInfo` if so. See `ConstantInfo.deltaValue?` for which
constants qualify. -/
def isDelta (env : Environment) (e : Expr) : Option ConstantInfo := do
  if let .const c ls := e.getAppFn then
    if let some ci := env.find? c then
      if ci.deltaValue?.isSome && ls.length == ci.numLevelParams then
        return ci
  none

def instantiateDeltaValue (ci : ConstantInfo) (ls : List Level) : Expr :=
  ci.deltaValue?.get!.instantiateLevelParams ci.levelParams ls

/-- If `e` is itself a constant that can be delta-reduced, returns its value with the constant's
level parameters instantiated. Unlike `unfoldDefinition`, this does not look through applications:
`e` must be a `.const`. -/
def unfoldDefinitionCore (e : Expr) : RecM (Option Expr) := do
  let .const _ ls := e | return none
  let env ← getEnv
  let some d := isDelta env e | return none
  unless 0 < ls.length do return some (instantiateDeltaValue d ls)
  if let some r := (← get).unfold[e]? then return some r
  let r := instantiateDeltaValue d ls
  modify fun s => { s with unfold := s.unfold.insert e r }
  return some r

/-- Unfolds the definition at the head of the application `e` (or `e` itself if it is not an
application). -/
def unfoldDefinition (e : Expr) : RecM (Option Expr) := do
  if e.isApp then
    let f0 := e.getAppFn
    let some f ← unfoldDefinitionCore f0 | return none
    let rargs := e.getAppRevArgs
    return f.mkAppRevRange 0 rargs.size rargs
  else
    unfoldDefinitionCore e

def reduceNative (_env : Environment) (e : Expr) : Except Exception (Option Expr) := do
  let .app f (.const c _) := e | return none
  if f == .const ``reduceBool [] then
    throw <| .other s!"lean4lean does not support 'reduceBool {c}' reduction"
  else if f == .const ``reduceNat [] then
    throw <| .other s!"lean4lean does not support 'reduceNat {c}' reduction"
  return none

def rawNatLitExt? (e : Expr) : Option Nat := if e == .natZero then some 0 else e.rawNatLit?

/-- Reduces the application `f a b` to a Nat literal if `a` and `b` can be reduced to Nat literals.

Note: `f` should have an (efficient) external implementation. -/
def reduceBinNatOp (f : Nat → Nat → Nat) (a b : Expr) : RecM (Option Expr) := do
  let some v1 := rawNatLitExt? (← whnf a) | return none
  let some v2 := rawNatLitExt? (← whnf b) | return none
  return some <| .lit <| .natVal <| f v1 v2

def reducePowMaxExp : Nat := 1 <<< 24

def reducePow (a b : Expr) : RecM (Option Expr) := do
  let some v1 := rawNatLitExt? (← whnf a) | return none
  let some v2 := rawNatLitExt? (← whnf b) | return none
  if v2 > reducePowMaxExp then return none
  return some <| .lit <| .natVal <| Nat.pow v1 v2

/-- Reduces the application `f a b` to a boolean expression if `a` and `b` can be reduced to Nat
literals.

Note: `f` should have an (efficient) external implementation. -/
def reduceBinNatPred (f : Nat → Nat → Bool) (a b : Expr) : RecM (Option Expr) := do
  let some v1 := rawNatLitExt? (← whnf a) | return none
  let some v2 := rawNatLitExt? (← whnf b) | return none
  return toExpr <| f v1 v2

/-- Reduces `e` to a literal if possible, where the unary operation `Nat.succ` and the binary
operations and predicates with an external implementation may be applied: `Nat.add`, `Nat.sub`,
`Nat.mul`, `Nat.pow`, `Nat.gcd`, `Nat.mod`, `Nat.div`, `Nat.land`, `Nat.lor`, `Nat.xor`,
`Nat.shiftLeft`, `Nat.shiftRight` produce a `Nat` literal, while the predicates `Nat.beq` and
`Nat.ble` produce a `Bool` literal. -/
def reduceNat (e : Expr) : RecM (Option Expr) := do
  let nargs := e.getAppNumArgs
  if nargs == 1 then
    let f := e.appFn!
    if f == .const ``Nat.succ [] then
      let some v := rawNatLitExt? (← whnf e.appArg!) | return none
      return some <| .lit <| .natVal <| v + 1
  else if nargs == 2 then
    let .app (.app (.const f _) a) b := e | return none
    if f == ``Nat.add then return ← reduceBinNatOp Nat.add a b
    if f == ``Nat.sub then return ← reduceBinNatOp Nat.sub a b
    if f == ``Nat.mul then return ← reduceBinNatOp Nat.mul a b
    if f == ``Nat.pow then return ← reducePow a b
    if f == ``Nat.gcd then return ← reduceBinNatOp Nat.gcd a b
    if f == ``Nat.mod then return ← reduceBinNatOp Nat.mod a b
    if f == ``Nat.div then return ← reduceBinNatOp Nat.div a b
    if f == ``Nat.beq then return ← reduceBinNatPred Nat.beq a b
    if f == ``Nat.ble then return ← reduceBinNatPred Nat.ble a b
    if f == ``Nat.land then return ← reduceBinNatOp Nat.land a b
    if f == ``Nat.lor then return ← reduceBinNatOp Nat.lor a b
    if f == ``Nat.xor then return ← reduceBinNatOp Nat.xor a b
    if f == ``Nat.shiftLeft then return ← reduceBinNatOp Nat.shiftLeft a b
    if f == ``Nat.shiftRight then return ← reduceBinNatOp Nat.shiftRight a b
  return none

@[inherit_doc whnf]
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
  if let some r := (← get).whnfCache[e]? then
    return r
  let rec loop t
  | 0 => throw .deterministicTimeout
  | fuel+1 => do
    let env ← getEnv
    let t ← whnfCore' t
    if let some t ← reduceNative env t then return t
    if let some t ← reduceNat t then return t
    let some t ← unfoldDefinition t | return t
    loop t fuel
  let ctx ← readThe Context
  let r ← loop e <| if ctx.eagerReduce then ctx.fuel.whnfEager else ctx.fuel.whnf
  if whnfCacheKey e then
    modify fun s => { s with whnfCache := s.whnfCache.insert e r }
  return r

/-- If `t` and `s` are lambda expressions, checks that their domains are defeq and recurses on the
bodies, substituting in a new free variable for that binder (this substitution is delayed for
efficiency purposes using the `subst` parameter). Otherwise, does a normal defeq check. -/
def isDefEqLambda (t s : Expr) (subst : Array Expr := #[]) : RecM Bool :=
  match t, s with
  | .lam _ tDom tBody _, .lam name sDom sBody bi => do
    let sType ← if tDom == sDom then pure none else
      let sType := sDom.instantiateRev subst
      let tType := tDom.instantiateRev subst
      if !(← isDefEq tType sType) then return false
      pure (some sType)
    -- In the scoped cache mode the bodies are always compared under a binder, even when
    -- neither mentions it, so that the comparison happens in the context where it is meaningful.
    -- In the global cache mode a binder is opened only when a body mentions it, as in the C++
    -- kernel's `is_def_eq_binding`.
    if (← readThe Context).fuel.cacheMode.isGlobal && !tBody.hasLooseBVars && !sBody.hasLooseBVars then
      isDefEqLambda tBody sBody (subst.push default)
    else
      let sType := sType.getD (sDom.instantiateRev subst)
      withLocalDecl name bi sType fun fv =>
        isDefEqLambda tBody sBody (subst.push fv)
  | t, s => isDefEq (t.instantiateRev subst) (s.instantiateRev subst)

/-- If `t` and `s` are for-all expressions, checks that their domains are defeq and recurses on the
bodies, substituting in a new free variable for that binder (this substitution is delayed for
efficiency purposes using the `subst` parameter). Otherwise, does a normal defeq check. -/
def isDefEqForall (t s : Expr) (subst : Array Expr := #[]) : RecM Bool :=
  match t, s with
  | .forallE _ tDom tBody _, .forallE name sDom sBody bi => do
    let sType ← if tDom == sDom then pure none else
      let sType := sDom.instantiateRev subst
      let tType := tDom.instantiateRev subst
      if !(← isDefEq tType sType) then return false
      pure (some sType)
    -- In the scoped cache mode the bodies are always compared under a binder, even when
    -- neither mentions it, so that the comparison happens in the context where it is meaningful.
    -- In the global cache mode a binder is opened only when a body mentions it, as in the C++
    -- kernel's `is_def_eq_binding`.
    if (← readThe Context).fuel.cacheMode.isGlobal && !tBody.hasLooseBVars && !sBody.hasLooseBVars then
      isDefEqForall tBody sBody (subst.push default)
    else
      let sType := sType.getD (sDom.instantiateRev subst)
      withLocalDecl name bi sType fun fv =>
        isDefEqForall tBody sBody (subst.push fv)
  | t, s => isDefEq (t.instantiateRev subst) (s.instantiateRev subst)

/-- Decides definitional equality of `t` and `s` in the cases that can be settled without
reduction, returning `.undef` to defer to the calling function otherwise.

It returns `.true` if they are α-equivalent or have previously been checked for definitional
equality, and otherwise decides two sorts by level equivalence and two literals by equality,
returning `.false` where these disagree. Two lambdas or two for-alls are handed to
`isDefEqLambda`/`isDefEqForall`, which may return either. All remaining cases — including two
constants, two free variables, two applications and two projections — are deferred. -/
def quickIsDefEq (t s : Expr) (useHash := false) : RecM LBool := do
  -- optimization for terms that are already α-equivalent or were previously checked
  if ← modifyGet fun (.mk a1 a2 a3 a4 a5 a6 a7 (eqvManager := m)) =>
    let (b, m) := m.isEquiv useHash t s
    (b, .mk a1 a2 a3 a4 a5 a6 a7 (eqvManager := m))
  then return .true
  match t, s with
  | .lam .., .lam .. => toLBoolM <| isDefEqLambda t s
  | .forallE .., .forallE .. => toLBoolM <| isDefEqForall t s
  | .sort a1, .sort a2 => pure (a1.isEquiv a2).toLBool
  | .mdata _ a1, .mdata _ a2 => toLBoolM <| isDefEq a1 a2
  | .mvar .., .mvar .. => unreachable!
  | .lit a1, .lit a2 => pure (a1 == a2).toLBool
  | _, _ => return .undef

/-- Assuming that `t` and `s` have the same function heads, returns true if they are applications
with definitionally equal arguments (in which case they are defeq), and false otherwise (deferring
further defeq checking to caller). -/
def isDefEqArgs (t s : Expr) : RecM Bool := do
  match t, s with
  | .app tf ta, .app sf sa =>
    if !(← isDefEq ta sa) then return false
    isDefEqArgs tf sf
  | .app .., _ | _, .app .. => return false
  | _, _ => return true

/-- Assuming `t` and `s` are WHNF, checks if they are defeq on account of `t` being an η-expansion
of `s`.

Assuming that `s` has a function type `(x : A) → B x`, it η-expands to `fun (x : A) => s x`
(which it is definitionally equal to by the η rule). -/
def tryEtaExpansionCore (t s : Expr) : RecM Bool := do
  if t.isLambda && !s.isLambda then
    let .forallE name ty _ bi ← whnf (← inferType s) | return false
    isDefEq t (.lam name ty (.app s (.bvar 0)) bi)
  else return false

@[inherit_doc tryEtaExpansionCore]
def tryEtaExpansion (t s : Expr) : RecM Bool :=
  tryEtaExpansionCore t s <||> tryEtaExpansionCore s t

/-- Assuming `t` and `s` in WHNF, checks if they are defeq on account of `s` being defeq to the
struct-η-expansion of `t`.

Assuming that `t` has a non-recursive structure type `S` with constructor `S.mk` and projections
`pᵢ`, it struct-η-expands to `S.mk (p₁ t) ... (pₙ t)` (which it is definitionally equal to by the
struct-η rule). -/
def tryEtaStructCore (t s : Expr) : RecM Bool := do
  let .const f _ := s.getAppFn | return false
  let env ← getEnv
  let .ctorInfo fInfo ← env.get f | return false
  unless s.getAppNumArgs == fInfo.numParams + fInfo.numFields do return false
  unless env.isNonRecStructure fInfo.induct do return false
  let tType ← inferType t
  unless ← isDefEq tType (← inferType s) do return false
  -- The projections below are only well typed when the structure is never a proposition
  -- (see `divergences.md`); propositions are handled by proof irrelevance instead.
  let .sort u ← whnf (← inferType tType) | return false
  unless u.isNeverZero do return false
  let args := s.getAppArgs
  -- since `t` is in WHNF, and assuming it is not a constructor application, these projections
  -- cannot reduce (so we are directly checking if `s` is defeq to the struct-η-expansion of `t`)
  let rec loop i := do
    if _h : i < args.size then
      unless ← isDefEq (.proj fInfo.induct (i - fInfo.numParams) t) args[i] do return false
      loop (i + 1)
    else return true
  loop fInfo.numParams

@[inherit_doc tryEtaStructCore]
def tryEtaStruct (t s : Expr) : RecM Bool :=
  tryEtaStructCore t s <||> tryEtaStructCore s t

/-- Checks if applications `t` and `s` (should be WHNF) are defeq on account of their function heads
and arguments being defeq. -/
def isDefEqApp (t s : Expr) : RecM Bool := do
  unless t.isApp && s.isApp do return false
  t.withApp fun tf tArgs =>
  s.withApp fun sf sArgs => do
  if _h : tArgs.size = sArgs.size then
    unless ← isDefEq tf sf do return false
    let rec loop i := do
      if _h : i < tArgs.size then
        unless ← isDefEq tArgs[i] sArgs[i] do return false
        loop (i+1)
      else return true
    loop 0
  else return false

/-- Checks if `t` and `s` are definitionally equivalent according to proof irrelevance (that is,
they are proofs of the same proposition). -/
def isDefEqProofIrrel (t s : Expr) : RecM LBool := do
  let tType ← inferType t
  if !(← isProp tType) then return .undef
  toLBoolM <| isDefEq tType (← inferType s)

def failedBefore (failure : Std.HashSet (Expr × Expr)) (t s : Expr) : Bool :=
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

/-- Performs a single step of δ-reduction on `tn`, `sn`, or both (according to optimizations)
followed by weak-head normalization (without further δ-reduction). Returns `.bool` if the resulting
terms are settled by `quickIsDefEq`, or if they are applications of the same defined constant with
defeq args. Otherwise returns `.continue`, indicating to the calling `lazyDeltaReduction` that
δ-reduction is to be continued.

If neither side has a δ-reducible head, returns `.unknown` with the terms unchanged, leaving further
defeq-checking to `isDefEqCore'`. Note that these are weak-head normal forms with respect to
`cheapProj := true`, so a projection at the head may still be reducible. -/
def lazyDeltaReductionStep (tn sn : Expr) : RecM ReductionStatus := do
  let env ← getEnv
  let delta e := do whnfCore (← unfoldDefinition e).get! (cheapProj := true)
  let cont tn sn :=
    return match ← quickIsDefEq tn sn with
    | .undef => .continue tn sn
    | .true => .true
    | .false => .false tn sn
  match isDelta env tn, isDelta env sn with
  | none, none => return .unknown tn sn
  | some _, none =>
    -- `sn` was normalized with `cheapProj := true`, so a projection at its head may not have been
    -- reduced; `tryUnfoldProjApp` retries it with the struct argument fully normalized
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
    if ht.lt' hs then
      cont tn (← delta sn)
    else if hs.lt' ht then
      cont (← delta tn) sn
    else
      if tn.isApp && sn.isApp && ptrEqConstantInfo dt ds && dt.hints.isRegular
        && !failedBefore (← get).failure tn sn
      then
        if Level.isEquivList tn.getAppFn.constLevels! sn.getAppFn.constLevels! then
          if ← isDefEqArgs tn sn then
            return .true
        cacheFailure tn sn
      cont (← delta tn) (← delta sn)

@[inline] def isNatZero (t : Expr) : Bool :=
  t == .natZero || t matches .lit (.natVal 0)

def isNatSuccOf? : Expr → Option Expr
  | .lit (.natVal (n+1)) => return .lit (.natVal n)
  | .app (.const ``Nat.succ _) e => return e
  | _ => none

/-- Returns `.true` if `t` and `s` are both zero, either as a literal or as `Nat.zero`. If they are
both successors of natural numbers `t'` and `s'`, either as literals or `Nat.succ` applications,
checks that `t'` and `s'` are definitionally equal. Otherwise, defers to the calling function. -/
def isDefEqOffset (t s : Expr) : RecM LBool := do
  if isNatZero t && isNatZero s then
    return .true
  match isNatSuccOf? t, isNatSuccOf? s with
  | some t', some s' => toLBoolM <| isDefEqCore t' s'
  | _, _ => return .undef

/-- Repeatedly δ-reduces the `cheapProj := true` weak-head normal forms `tn` and `sn` until the
question is settled. Returns `.bool` if:
- they are both zero or both natural number successors (as literals or `Nat.succ` applications)
- one of them can be converted to a natural number/boolean literal
- a `lazyDeltaReductionStep` settles them

Otherwise returns `.unknown` with the reduced terms, deferring to the calling function. Throws
`.deterministicTimeout` after `FuelConfig.lazyDelta` steps. -/
def lazyDeltaReduction (tn sn : Expr) : RecM ReductionStatus := do
  loop tn sn (← readThe Context).fuel.lazyDelta
where
  loop tn sn
  | 0 => throw .deterministicTimeout
  | fuel+1 => do
    let r ← isDefEqOffset tn sn
    if r != .undef then return .bool tn sn (r == .true)
    if !tn.hasFVar && !sn.hasFVar || (← readThe Context).eagerReduce then
      if let some tn' ← reduceNat tn then
        return .bool tn' sn (← isDefEqCore tn' sn)
      else if let some sn' ← reduceNat sn then
        return .bool tn sn' (← isDefEqCore tn sn')
    let env ← getEnv
    if let some tn' ← reduceNative env tn then
      return .bool tn' sn (← isDefEqCore tn' sn)
    else if let some sn' ← reduceNative env sn then
      return .bool tn sn' (← isDefEqCore tn sn')
    match ← lazyDeltaReductionStep tn sn with
    | .continue tn sn => loop tn sn fuel
    | r => return r

/-- Lazily delta-unfold two structures and, once that stalls, compare their
projected fields. -/
def lazyDeltaProjReduction (structName : Name) (t s : Expr) (idx : Nat) : RecM Bool := do
  loop t s (← readThe Context).fuel.lazyDelta
where
  finish tn sn := do
    if let some tf ← reduceProjCore structName idx tn then
      if let some sf ← reduceProjCore structName idx sn then
        return ← isDefEqCore tf sf
    isDefEqCore tn sn
  loop tn sn
  | 0 => throw .deterministicTimeout
  | fuel+1 => do
    match ← lazyDeltaReductionStep tn sn with
    | .continue tn sn => loop tn sn fuel
    | .true => return true
    | .unknown tn sn | .false tn sn => finish tn sn

/-- If `t` is a string literal and `s` is a `String.ofList` application, checks that they are defeq
after expanding `t` into a `String.ofList` application of an explicit character list. Otherwise,
defers to the calling function. -/
def tryStringLitExpansionCore (t s : Expr) : RecM LBool := do
  let .lit (.strVal st) := t | return .undef
  let .app sf _ := s | return .undef
  unless sf == .const ``String.ofList [] do return .undef
  toLBoolM <| isDefEqCore (.strLitToConstructor st) s

@[inherit_doc tryStringLitExpansionCore]
def tryStringLitExpansion (t s : Expr) : RecM LBool := do
  match ← tryStringLitExpansionCore t s with
  | .undef => tryStringLitExpansionCore s t
  | r => return r

/-- Checks if `t` and `s` are defeq on account of both being of a unit type (a type with one
constructor without any fields or indices). -/
def isDefEqUnitLike (t s : Expr) : RecM Bool := do
  let tType ← whnf (← inferType t)
  let .const I _ := tType.getAppFn | return false
  let env ← getEnv
  let .inductInfo { isRec := false, ctors := [c], numIndices := 0, .. } ← env.get I | return false
  let .ctorInfo { numFields := 0, .. } ← env.get c | return false
  isDefEqCore tType (← inferType s)

@[inherit_doc isDefEqCore]
def isDefEqCore' (t s : Expr) : RecM Bool := do
  let r ← quickIsDefEq t s (useHash := true)
  if r != .undef then return r == .true

  if (!t.hasFVar || (← readThe Context).eagerReduce) && s.isConstOf ``true then
    if (← whnf t).isConstOf ``true then return true

  let tn ← whnfCore t (cheapProj := true)
  let sn ← whnfCore s (cheapProj := true)

  if !(ptrEqExpr tn t && ptrEqExpr sn s) then
    let r ← quickIsDefEq tn sn
    if r != .undef then return r == .true

  let r ← isDefEqProofIrrel tn sn
  if r != .undef then return r == .true

  match ← lazyDeltaReduction tn sn with
  | .continue .. => unreachable!
  | .true => return true
  | .false .. => return false
  | .unknown tn sn =>

  match tn, sn with
  | .const tf tl, .const sf sl =>
    if tf == sf && Level.isEquivList tl sl then return true
  | .fvar tv, .fvar sv => if tv == sv then return true
  | .proj tn ti te, .proj sn si se =>
    -- optimized by the previous reduction functions using `cheapProj := true`
    if tn == sn && ti == si then
      if ← lazyDeltaProjReduction tn te se ti then return true
  | _, _ => pure ()

  -- the previous reduction functions used `cheapProj := true`, so we may not have a complete WHNF
  let tnn ← whnfCore tn
  let snn ← whnfCore sn
  if !(ptrEqExpr tnn tn && ptrEqExpr snn sn) then
    -- if projection reduced, need to re-run (as we may not have a WHNF)
    return ← isDefEqCore tnn snn

  -- tn and sn are both in WHNF
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
      whnfCore := fun _ _ => throw .deepRecursion
      whnf := fun _ => throw .deepRecursion
      inferType := fun _ _ => throw .deepRecursion }
  | n + 1 =>
    { isDefEqCore := fun t s => isDefEqCore' t s (withFuel n)
      whnfCore := fun e p => whnfCore' e p (withFuel n)
      whnf := fun e => whnf' e (withFuel n)
      inferType := fun e i => inferType' e i (withFuel n) }

/-- Runs `x` with a limit on the recursion depth, taken from `FuelConfig.recDepth`. -/
def RecM.run (x : RecM α) : M α := do x (Methods.withFuel (← readThe Context).fuel.recDepth)

def RecM.runTermElab (x : RecM α) (safety := DefinitionSafety.safe) : Elab.Term.TermElabM α :=
  x.run.runTermElab safety

instance : MonadLift RecM Elab.Term.TermElabM := ⟨RecM.runTermElab⟩

@[inherit_doc whnf']
def whnf (e : Expr) : M Expr := (Inner.whnf e).run

def whnfCore (e : Expr) : M Expr := (Inner.whnfCore e).run

def unfoldDefinition (e : Expr) : M Expr := return (← (Inner.unfoldDefinition e).run).getD e

/-- Infers the type of expression `e`. If `inferOnly := false`, this function throws an error
whenever `e` is not typeable according to Lean's algorithmic typing judgment (barring resource
exhaustion: it may also throw `.deterministicTimeout` or `.deepRecursion` on a typeable term).
Setting `inferOnly := true` optimizes to avoid unnecessary checks in the case that `e` is already
known to be well-typed. -/
def inferType (e : Expr) (inferOnly := true) : M Expr := (Inner.inferType e inferOnly).run

/-- Infers the type of expression `e` and checks that `e` is well-typed according to Lean's typing
judgment. Use `inferType` to infer the type alone. -/
abbrev checkType (e : Expr) : M Expr := inferType e (inferOnly := false)

@[inherit_doc isDefEqCore]
def isDefEq (t s : Expr) : M Bool := (Inner.isDefEq t s).run

@[inherit_doc Inner.isProp]
def isProp (t : Expr) : M Bool := (Inner.isProp t).run

@[inherit_doc ensureSortCore]
def ensureSort (t : Expr) (s := t) : M Expr := (ensureSortCore t s).run

@[inherit_doc ensureForallCore]
def ensureForall (t : Expr) (s := t) : M Expr := (ensureForallCore t s).run

/-- Ensures that `e` is a type/proposition. If it is not, throws an error. -/
def ensureType (e : Expr) (inferOnly := true) : M Expr := do ensureSort (← inferType e inferOnly) e

def etaExpand (e : Expr) : M Expr :=
  let rec loop fvars
  | .lam name dom body bi => do
    let d := dom.instantiateRev fvars
    withLocalDecl name bi d fun fv => do
      let fvars := fvars.push fv
      loop fvars body
  | it => do
    let itType ← whnf <| ← inferType <| it.instantiateRev fvars
    if !itType.isForall then return e
    let rec loop2 fvars args
    | 0, _ => throw .deepRecursion
    | fuel + 1, .forallE name dom body bi => do
      let d := dom.instantiateRev fvars
      withLocalDecl name bi d fun arg => do
        let fvars := fvars.push arg
        let args := args.push arg
        loop2 fvars args fuel <| ← whnf <| body.instantiate1 arg
    | _, it => return (← getLCtx).mkLambda fvars (mkAppN it args)
    loop2 fvars #[] (← readThe Context).fuel.etaExpand itType
  loop #[] e
