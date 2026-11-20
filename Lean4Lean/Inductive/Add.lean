import Batteries.Data.List.Basic
import Lean4Lean.Environment.Basic
import Lean4Lean.TypeChecker

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace AddInductive
open TypeChecker

structure RecInfo where
  motive : Expr
  minors : Array Expr
  indices : Array Expr
  major : Expr
  deriving Inhabited

/-- What `checkConstructors` records about one constructor, for the recursor construction to
read back. -/
structure CtorData where
  /-- The constructor's type with the block's parameters instantiated, so that its binders are
  exactly the fields, and with `consumeFieldAnnotations` applied, so that each binder's domain
  is already the type the field is declared at. Prepared once by `checkConstructors`, which is
  also where the parameters are checked against the type former's; every later walk reads this
  and so never has to skip a parameter or consume an annotation. -/
  type : Expr
  /-- For each non-parameter field, the `deepWhnfField` normal form of that field's type.

  These are open terms, which is rare in this checker. Each one is abstracted over the fields
  before it, innermost as `#0`, so it carries loose bound variables. A reader closes it against
  its own field binders, as `mkRecInfos.loopCtorArgs` does with
  `fields[bu.size]!.instantiateRev bu`. That is what lets a field's normal form outlive the
  local declarations it was reduced under and be read again under the recursor construction's,
  which is the point of recording it at all.

  The parameters are not abstracted: `stats.params` are the block's own free variables, in
  scope for everything inside `checkInductiveTypes`, so they are the same variables at both
  ends and abstracting them would only be an identity round trip.

  Computed once by `checkConstructors`; `checkPositivity`, the recursive-argument
  classification in `mkRecInfos.loopCtorArgs` and the inductive hypotheses in
  `mkRecInfos.loopUArgs` all read it rather than reducing the field's type again. -/
  fields : Array Expr
  deriving Inhabited

structure InductiveStats where
  lctx : LocalContext := {}
  levels : List Level
  resultLevel : Level
  nindices : Array Nat := #[]
  indConsts : Array Expr
  params : Array Expr
  isNotZero : Bool
  /-- For each type former, for each of its constructors, what `checkConstructors` recorded. -/
  ctors : Array (Array CtorData) := #[]
  deriving Inhabited

structure Context where
  env : Environment
  lctx : LocalContext := {}
  lparams : List Name
  ngen : NameGenerator := { namePrefix := `_ind_fresh }
  safety : DefinitionSafety
  allowPrimitive : Bool
  fuel : FuelConfig := {}

abbrev M := ReaderT Context <| Except Exception

instance : MonadLocalNameGenerator M where
  withFreshId f c := f c.ngen.curr { c with ngen := c.ngen.next }

instance (priority := low) : MonadLift TypeChecker.M M where
  monadLift x c := x.run c.env c.safety c.lctx c.lparams (fuel := c.fuel)

instance (priority := low+1) : MonadWithReaderOf LocalContext M where
  withReader f x := withReader (fun c => { c with lctx := f c.lctx }) x

instance : MonadLCtx M where
  getLCtx := return (← read).lctx

@[inline] def withEnv (env : Environment) (x : M α) : M α :=
  withReader (fun c => { c with env }) x

def getType (fvar : Expr) : M Expr :=
  return ((← getLCtx).get! fvar.fvarId!).type

def checkInductiveTypes
    (nparams : Nat) (indTypes : Array InductiveType)
    (k : InductiveStats → M α) : M α := do
  let rec loopInd dIdx stats : M α := do
    if _h : dIdx < indTypes.size then
      let indType := indTypes[dIdx]
      let env := (← read).env
      let type := indType.type
      env.checkNoMVarNoFVar indType.name type
      _ ← checkType type
      let rec loop stats type i nindices fuel k : M α := match fuel with
      | 0 => throw .deepRecursion
      | fuel+1 => do
        if let .forallE name dom body bi := type then
          if i < nparams then
            if stats.indConsts.isEmpty then
              withLocalDecl name bi dom.consumeTypeAnnotations fun param => do
                let stats := { stats with params := stats.params.push param }
                let type := body.instantiate1 param
                loop stats (← whnf type) (i + 1) nindices fuel k
            else
              let param := stats.params[i]!
              unless ← isDefEq dom (← getType param) do
                throw <| .other "parameters of all inductive datatypes must match"
              let type := body.instantiate1 param
              loop stats (← whnf type) (i + 1) nindices fuel k
          else
            withLocalDecl name bi dom.consumeTypeAnnotations fun arg => do
              let type := body.instantiate1 arg
              loop stats (← whnf type) i (nindices + 1) fuel k
        else
          if i != nparams then
            throw <| .other "number of parameters mismatch in inductive datatype declaration"
          k type stats nindices
      let fuel := (← readThe Context).fuel.inductiveFuel
      loop stats (← whnf type) 0 0 fuel fun type stats nindices => show M α from do
      let type ← ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indType.name stats.levels) }
      loopInd (dIdx + 1) stats
    else
      k <|
        assert! stats.levels.length == (← read).lparams.length
        assert! stats.nindices.size == indTypes.size
        assert! stats.indConsts.size == indTypes.size
        assert! stats.params.size == nparams
        stats
  loopInd 0 { (default : InductiveStats) with levels := (← read).lparams.map .param }

def hasIndOcc (indConsts : Array Expr) (t : Expr) : Bool :=
  (t.find? fun
    | .const e _ => indConsts.any fun I => I.constName! == e
    | _ => false).isSome

/-- Return true if declaration is recursive -/
def isRec (indTypes : Array InductiveType) (indConsts : Array Expr) : Bool :=
  let rec loop
    | .forallE _ dom body _ => hasIndOcc indConsts dom || loop body
    | _ => false
  indTypes.any fun indType => indType.ctors.any fun ctor => loop ctor.type

/-- Return true if the given declaration is reflexive.

Remark: We say an inductive type `T` is reflexive if it
contains at least one constructor that takes as an argument a
function returning `T'` where `T'` is another inductive datatype (possibly equal to `T`)
in the same mutual declaration. -/
def isReflexive (indTypes : Array InductiveType) (indConsts : Array Expr) : Bool :=
  let rec loop
    | .forallE _ dom body _ => dom.isForall && hasIndOcc indConsts dom || loop body
    | _ => false
  indTypes.any fun indType => indType.ctors.any fun ctor => loop ctor.type

def declareInductiveTypes (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool) : M Environment :=
  fun c =>
  let all := indTypes.map (·.name) |>.toList
  let infos := indTypes.zipWith (bs := stats.nindices) fun indType numIndices =>
    { indType with
      numParams, numIndices, all, numNested, isUnsafe
      levelParams := c.lparams
      ctors := indType.ctors.map (·.name)
      isRec := isRec indTypes stats.indConsts
      isReflexive := isReflexive indTypes stats.indConsts }
  infos.foldlM (init := c.env) fun env info => do
    env.checkName info.name c.allowPrimitive
    return env.add (.inductInfo info)

def isValidIndAppIdx (stats : InductiveStats) (i : Nat) (I : Expr) (args : Array Expr) :
    Bool := Id.run do
  unless I == stats.indConsts[i]! && args.size == stats.params.size + stats.nindices[i]! do
    return false
  for i in [:stats.params.size] do
    if stats.params[i]! != args[i]! then return false
  for i in [stats.params.size:args.size] do
    if hasIndOcc stats.indConsts args[i]! then return false
  true

def isValidIndApp? (stats : InductiveStats) (t : Expr) : Option Nat := t.withApp fun I args => do
  for i in [:stats.indConsts.size] do
    if isValidIndAppIdx stats i I args then
      return i
  none

/-- Deep weak-head normalization of a constructor field's type: reduce the spine, and if
the result is a `∀`, take the domain as it stands and normalize the codomain under it.

These are exactly the `whnf` calls that the field's positivity check and its
recursive-argument classification each used to make for themselves. `whnf` is only
specified to return *some* definitionally equal expression (`whnf'.WF`), so two calls on
the same input are two unrelated results; a field must be normalized once and the result
shared, or the recursor's type and its computation rule can be built from different
readings of the same field. -/
def deepWhnfField (t : Expr) : M Expr := do
  loop #[] t (← readThe Context).fuel.inductiveFuel
where
  loop fvars t
  | 0 => throw .deepRecursion
  | fuel+1 => do
    let t ← whnf t
    let .forallE name dom body bi := t | return (← getLCtx).mkForall fvars t
    withLocalDecl name bi dom.consumeTypeAnnotations fun fv =>
    loop (fvars.push fv) (body.instantiate1 fv) fuel

/-- The recursive-argument classification of a field, read off its `deepWhnfField` normal
form: `some i` when the field's conclusion is an application of the `i`-th type former of
the block. A pure function of the normal form, so every reader gets the same answer. -/
def recArgIdx? (stats : InductiveStats) : Expr → Option Nat
  | .forallE _ _ body _ => recArgIdx? stats body
  | t => isValidIndApp? stats t

/-- Strict positivity of one constructor field, read off its `deepWhnfField` normal form:
no type former of the block occurs in a binder domain, and the conclusion either does not
mention the block at all or is a valid application of one of its type formers. -/
def checkPositivity (stats : InductiveStats) (ctor : Name) (idx : Nat) :
    Expr → Except Exception Unit
  | .forallE _ dom body _ =>
    if hasIndOcc stats.indConsts dom then
      throw <| .other s!"arg #{idx + 1} of '{ctor}' \
        has a non positive occurrence of the datatypes being declared"
    else checkPositivity stats ctor idx body
  | t =>
    if hasIndOcc stats.indConsts t && (isValidIndApp? stats t).isNone then
      throw <| .other s!"arg #{idx + 1} of '{ctor}' \
        has a non valid occurrence of the datatypes being declared"
    else pure ()

/-- `t` with the head type annotations consumed on every domain of its forall spine, which
for a constructor type stripped of its parameters means on every field's type.

That is the type each field binder is declared at -- in `checkConstructors` here, in
`isLargeEliminator` and in `mkRecInfos.loopCtorArgs` -- and the type `deepWhnfField`
reduces, so it is computed once and recorded in `CtorData.type` instead of again by every
walk. Consuming commutes with the instantiation those walks perform on the way down:
substituting for the loose variables of a domain cannot change the annotations at its head.
-/
def consumeFieldAnnotations : Expr → Expr
  | .forallE name dom body bi =>
    .forallE name dom.consumeTypeAnnotations (consumeFieldAnnotations body) bi
  | t => t

/-- Check the constructors, and record each one's `CtorData` in `InductiveStats.ctors`: its
type with the block's parameters instantiated, and the `deepWhnfField` normal form of every
field's type. This is the only place a constructor field is reduced; the positivity check
here and the recursor construction later both read the recorded normal form. -/
def checkConstructors (indTypes : Array InductiveType)
    (stats : InductiveStats) (isUnsafe : Bool) : M InductiveStats := do
  let env ← getEnv
  let mut allCtors := #[]
  for h : idx in [:indTypes.size] do
    let indType := indTypes[idx]
    let mut foundCtors : NameSet := {}
    let mut ctors := #[]
    for ctor in indType.ctors do
      let n := ctor.name
      if foundCtors.contains n then
        throw <| .other s!"duplicate constructor name '{n}'"
      foundCtors := foundCtors.insert n
      let t := ctor.type
      env.checkNoMVarNoFVar n t
      _ ← checkType t
      -- The parameters are checked and instantiated here, once, so that the binders of
      -- `ctype` are exactly the fields. A constructor type with fewer binders than the block
      -- has parameters cannot have a valid return type -- the identity check in
      -- `isValidIndAppIdx` would fail, since an uninstantiated parameter cannot appear in it --
      -- so it is rejected with that error rather than a separate one.
      let mut ctype := t
      for j in [:stats.params.size] do
        let .forallE _ dom body _ := ctype
          | throw <| .other s!"invalid return type for '{n}'"
        let param := stats.params[j]!
        unless ← isDefEq (dom.instantiateRevRange 0 j stats.params) (← getType param) do
          throw <| .other
            s!"arg #{j + 1} of '{n}' does not match inductive datatype parameters"
        ctype := body
      ctype := consumeFieldAnnotations (ctype.instantiateRev stats.params)
      -- `bvs` are the field binders introduced so far and `fields` the normalized field types
      -- abstracted over them. `ctype` is descended into without substituting, so each domain
      -- and the result type are instantiated from `bvs` as they are reached, rather than the
      -- remaining type once per binder. `i` counts binders of `ctor.type`, parameters
      -- included, because it names the argument in the errors.
      let rec loop t i bvs fields
      | 0 => throw .deepRecursion
      | fuel+1 => do
        if let .forallE name dom body bi := t then
          let dom := dom.instantiateRev bvs
          let s ← ensureType dom
          unless stats.resultLevel.isAlwaysZero || stats.resultLevel.geq' s.sortLevel! do
            throw <| .other s!"universe level of type_of(arg #{i + 1}) of '{n}' \
              is too big for the corresponding inductive datatype"
          let ndom ← deepWhnfField dom
          if !isUnsafe then
            checkPositivity stats n i ndom
          withLocalDecl name bi dom fun arg => do
            loop body (i + 1) (bvs.push arg) (fields.push (ndom.abstract bvs)) fuel
        else if (t.instantiateRev bvs).withApp (isValidIndAppIdx stats idx) then pure fields
        else throw <| .other s!"invalid return type for '{n}'"
      ctors := ctors.push {
        type := ctype
        fields := ← loop ctype stats.params.size #[] #[] (← readThe Context).fuel.inductiveFuel }
    allCtors := allCtors.push ctors
  return { stats with ctors := allCtors }

def declareConstructors (stats : InductiveStats)
    (indTypes : Array InductiveType) (isUnsafe : Bool) : M Environment :=
  fun c => indTypes.foldlM (init := c.env) fun env indType => do
    let (_, env) ← indType.ctors.foldlM (init := (0, env)) fun (cidx, env) ctor => do
      let type := ctor.type
      let rec arity i
        | .forallE _ _ body _ => arity (i+1) body
        | _ => i
      let arity := arity 0 type
      env.checkName ctor.name c.allowPrimitive
      pure (cidx + 1, env.add <| .ctorInfo {
        type, cidx, isUnsafe
        levelParams := c.lparams
        name := ctor.name
        induct := indType.name
        numParams := stats.params.size
        numFields := assert! arity ≥ stats.params.size; arity - stats.params.size
      })
    pure env

/-- Return true if recursor can map into any universe -/
def isLargeEliminator (stats : InductiveStats) (indTypes : Array InductiveType) : M Bool := do
  if stats.isNotZero then return true
  let #[indType] := indTypes | return false
  match indType.ctors with
  | [] => return true
  | [_] =>
    -- the parameters are instantiated in `CtorData.type`, so every binder reached here is a field
    let rec loop type fvs toCheck
    | 0 => throw .deepRecursion
    | fuel+1 => do
      if let .forallE name dom body bi := type then
        let dom := dom.instantiateRev fvs
        withLocalDecl name bi dom fun arg => do
          let mut toCheck := toCheck
          if !(← ensureType dom).sortLevel!.isAlwaysZero then
            toCheck := toCheck.push arg
          loop body (fvs.push arg) toCheck fuel
      else
        return toCheck.all (type.instantiateRev fvs).getAppArgs.contains
    loop stats.ctors[0]![0]!.type #[] #[] (← readThe Context).fuel.inductiveFuel
  | _ => return false

def getElimLevel (stats : InductiveStats) (indTypes : Array InductiveType) :
    M Level := do
  unless ← isLargeEliminator stats indTypes do return .zero
  let {lparams, ..} ← read
  -- `u` together with `u_1 … u_n`, for `n` the number of parameters the declaration has, are
  -- `n + 1` distinct names, so the search below always finds one that is free.
  unless lparams.contains `u do return .param `u
  for i in [1:lparams.length + 1] do
    let u := (`u).appendIndexAfter i
    unless lparams.contains u do return .param u
  unreachable!

def isKTarget (stats : InductiveStats) (indTypes : Array InductiveType) : M Bool := do
  let #[indType] := indTypes | return false
  unless stats.resultLevel.isAlwaysZero do return false
  let [ctor] := indType.ctors | return false
  let rec loop i
    | .forallE _ _ body _ => i < stats.params.size && loop (i + 1) body
    | _ => true
  return loop 0 ctor.type

@[inline] def getIIndices (stats : InductiveStats) (t : Expr) : Nat × Array Expr :=
  ((isValidIndApp? stats t).get!, t.getAppArgs[stats.params.size:])

-- FIXME: The function below has been exploded into nested loops as standalone functions
-- because I couldn't get them all to compile together as `let rec`s.
namespace mkRecInfos

def loopArgs1 (stats : InductiveStats) (type : Expr) (i : Nat) (indices : Array Expr)
    (fuel : Nat) (k : Array Expr → M α) : M α := match fuel with
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := type then
      if i < stats.params.size then
        loopArgs1 stats (← whnf <| body.instantiate1 stats.params[i]!) (i + 1) indices fuel k
      else
        withLocalDecl name bi dom.consumeTypeAnnotations fun arg => do
        loopArgs1 stats (← whnf <| body.instantiate1 arg) i (indices.push arg) fuel k
    else
      k indices

variable (stats : InductiveStats) (indTypes : Array InductiveType) (elimLevel : Level) in
def loopInd1 (dIdx : Nat) (recInfos : Array RecInfo) (k : Array RecInfo → M α) : M α := do
  if _h : dIdx < indTypes.size then
    let ctx ← readThe Context
    loopArgs1 stats (← whnf indTypes[dIdx].type) 0 #[] ctx.fuel.inductiveFuel fun indices =>
    let tTy := mkAppN (mkAppN stats.indConsts[dIdx]! stats.params) indices
    withLocalDecl `t .default tTy.consumeTypeAnnotations fun major => do
    let lctx ← getLCtx
    let motiveTy := lctx.mkForall indices <| lctx.mkForall #[major] <| .sort elimLevel
    let name := if indTypes.size > 1 then (`motive).appendIndexAfter (dIdx+1) else `motive
    withLocalDecl name .default motiveTy.consumeTypeAnnotations fun motive => do
    loopInd1 (dIdx + 1) (recInfos.push { motive, minors := #[], indices, major }) k
  else
    k recInfos

variable (stats : InductiveStats) (fields : Array Expr) in
/-- Walk a constructor's telescope, collecting its fields `bu` and, among them, the
recursive ones `u`, each paired with its `deepWhnfField` normal form. The classification
and the normal form both come from `fields`, recorded once by `checkConstructors`, so this
performs no reduction of its own and the minor premises and the recursor rules see the
same reading of every field. -/
def loopCtorArgs (t : Expr) (k : Expr → Array Expr → Array (Expr × Expr) → M α) : M α := do
  loop t #[] #[] (← readThe Context).fuel.inductiveFuel
where
  loop t bu u
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := t then
      withLocalDecl name bi (dom.instantiateRev bu) fun arg => do
      let ndom := fields[bu.size]!.instantiateRev bu
      let u := if (recArgIdx? stats ndom).isSome then u.push (arg, ndom) else u
      loop body (bu.push arg) u fuel
    else k (t.instantiateRev bu) bu u

/-- Rebuild a recursive field's recorded normal form with its conclusion replaced: the
higher-order binders of `∀ xs, I params indices` are kept exactly as recorded, and the
conclusion becomes `mkHead indices (ui xs)`, under `mkBinder` -- `Expr.forallE` for the minor
premise's inductive hypothesis, `Expr.lam` for the rule's recursive call.

The binders stay in place, so this instantiates nothing, introduces no local declaration and
reduces nothing; the caller used to open the telescope with fresh variables only to abstract
them again. `k` counts the binders passed so far, which is how `ui` is applied to them. -/
def mapIHConclusion (stats : InductiveStats) (ui : Expr)
    (mkBinder : Name → Expr → Expr → BinderInfo → Expr) (mkHead : Nat → Array Expr → Expr) :
    Expr → Nat → Expr
  | .forallE name dom body bi, k =>
    mkBinder name dom (mapIHConclusion stats ui mkBinder mkHead body (k + 1)) bi
  | t, k =>
    let (itIdx, itIndices) := getIIndices stats t
    (mkHead itIdx itIndices).app (mkAppN ui (Array.ofFn fun i : Fin k => Expr.bvar (k - 1 - i.1)))

variable (stats : InductiveStats) (u : Array (Expr × Expr)) (recInfos : Array RecInfo) in
def loopU (i : Nat) (v : Array Expr) (k : Array Expr → M α) : M α := do
  if _h : i < u.size then
    let (ui, uiTy) := u[i]
    let viTy := mapIHConclusion stats ui Expr.forallE (mkAppN recInfos[·]!.motive) uiTy 0
    let vName := ((← getLCtx).get! ui.fvarId!).userName.appendAfter "_ih"
    -- `viTy` is a `∀` or an application of a motive, so it carries no annotation to consume
    withLocalDecl vName .default viTy fun vi => do
    loopU (i + 1) (v.push vi) k
  else
    k v

variable (stats : InductiveStats) (indTypeName : Name) (dIdx : Nat) in
def loopCtors (recInfos : Array RecInfo) (cIdx : Nat)
    (ctors : List Constructor) (k : Array RecInfo → M α) : M α := match ctors with
  | ctor::ctors =>
    let cd := stats.ctors[dIdx]![cIdx]!
    loopCtorArgs stats cd.fields cd.type fun t bu u => do
    let (itIdx, itIndices) := getIIndices stats t
    let introApp := mkAppN (mkAppN (.const ctor.name stats.levels) stats.params) bu
    let motiveApp := Expr.app (mkAppN recInfos[itIdx]!.motive itIndices) introApp
    loopU stats u recInfos 0 #[] fun v => do
    let lctx ← getLCtx
    let minorTy := lctx.mkForall bu <| lctx.mkForall v motiveApp
    let minorName := ctor.name.replacePrefix indTypeName .anonymous
    withLocalDecl minorName .default minorTy.consumeTypeAnnotations fun minor => do
    let recInfos := recInfos.modify dIdx fun s => { s with minors := s.minors.push minor }
    loopCtors recInfos (cIdx + 1) ctors k
  | [] => k recInfos

variable (stats : InductiveStats) (indTypes : Array InductiveType) in
def loopInd2 (dIdx : Nat) (recInfos : Array RecInfo) (k : Array RecInfo → M α) : M α := do
  if _h : dIdx < indTypes.size then
    let indType := indTypes[dIdx]
    let indTypeName := indType.name
    loopCtors stats indTypeName dIdx recInfos 0 indType.ctors fun recInfos =>
    loopInd2 (dIdx + 1) recInfos k
  else
    k recInfos

end mkRecInfos

def mkRecInfos (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (k : Array RecInfo → M α) : M α :=
  mkRecInfos.loopInd1 stats indTypes elimLevel 0 #[] fun recInfos =>
  mkRecInfos.loopInd2 stats indTypes 0 recInfos k

def getRecLevels (elimLevel : Level) (levels : List Level) : List Level :=
  if elimLevel.isParam then elimLevel :: levels else levels

def getRecLevelParams (elimLevel : Level) (lparams : List Name) : List Name :=
  if let .param u := elimLevel then u :: lparams else lparams

def mkRecRules (indTypes : Array InductiveType) (elimLevel : Level) (stats : InductiveStats)
    (dIdx : Nat) (motives : Array Expr) (minors : Array Expr) :
    StateT Nat M (List RecursorRule) := do
  let d := indTypes[dIdx]!
  let lvls := getRecLevels elimLevel stats.levels
  -- `I.rec params motives minors`, for each type former `I` of the block: the prefix every
  -- recursive call in every rule of the block shares, so it is built once here
  let recApps := indTypes.map fun indType =>
    mkAppN (mkAppN (mkAppN (.const (mkRecName indType.name) lvls) stats.params) motives) minors
  let mut rules := #[]
  let ctors := d.ctors.toArray
  for h : cIdx in [:ctors.size] do
    let ctor := ctors[cIdx]
    let cd := stats.ctors[dIdx]![cIdx]!
    let rule ← fun minorIdx =>
      mkRecInfos.loopCtorArgs stats cd.fields cd.type fun _ bu u =>
      let rec loopU i (v : Array Expr) k := do
        if _h : i < u.size then
          let (ui, uiTy) := u[i]
          let val := mkRecInfos.mapIHConclusion stats ui Expr.lam
            (mkAppN recApps[·]!) uiTy 0
          loopU (i + 1) (v.push val) k
        else
          k v
      loopU 0 #[] fun v => do
      let lctx ← getLCtx
      let rule := {
        ctor := ctor.name
        nfields := bu.size
        rhs := lctx.mkLambda stats.params <| lctx.mkLambda motives <|
          lctx.mkLambda minors <| lctx.mkLambda bu <|
          mkAppN (mkAppN minors[minorIdx]! bu) v
      }
      return (rule, minorIdx + 1)
    rules := rules.push rule
  return rules.toList

def run (nparams : Nat) (types : List InductiveType) (numNested : Nat) : M Environment := do
  let isUnsafe := (← read).safety != .safe
  let indTypes := types.toArray
  let {lparams, ..} ← read
  Environment.checkDuplicatedUnivParams lparams
  checkInductiveTypes nparams indTypes fun stats => do
  withEnv (← declareInductiveTypes stats nparams indTypes numNested isUnsafe) do
  let stats ← checkConstructors indTypes stats isUnsafe
  withEnv (← declareConstructors stats indTypes isUnsafe) do
  let elimLevel ← getElimLevel stats indTypes
  let k ← isKTarget stats indTypes
  mkRecInfos stats indTypes elimLevel fun recInfos => do
  let motives := recInfos.map (·.motive)
  let minors := recInfos.flatMap (·.minors)
  let numMinors := minors.size
  let numMotives := motives.size
  let all := indTypes.map (·.name) |>.toList
  let lctx ← getLCtx
  let isUnsafe := (← read).safety != .safe
  StateT.run' (s := 0) do
  let mut env ← getEnv
  let {allowPrimitive, ..} ← read
  for h : dIdx in [:indTypes.size] do
    let indType := indTypes[dIdx]
    let info := recInfos[dIdx]!
    let ty :=
      lctx.mkForall stats.params <|
      lctx.mkForall motives <|
      lctx.mkForall minors <|
      lctx.mkForall info.indices <|
      lctx.mkForall #[info.major] <|
      .app (mkAppN info.motive info.indices) info.major
    let rules ← mkRecRules indTypes elimLevel stats dIdx motives minors
    let name := mkRecName indType.name
    env.checkName name allowPrimitive
    env := env.add <| .recInfo {
      levelParams := getRecLevelParams elimLevel lparams
      type := ty.inferImplicit 1000 false -- note: flag has reversed polarity from C++
      numParams := stats.params.size
      numIndices := stats.nindices[dIdx]!
      name, all, numMotives, numMinors, rules, k, isUnsafe
    }
  pure env

end AddInductive

namespace ElimNestedInductive

structure Result where
  ngen : NameGenerator
  nparams : Nat
  lctx : LocalContext
  params : Array Expr -- the fvars declared in `lctx`
  aux2nested : NameMap Expr -- exprs are open over `params`, like the C++ `m_aux2nested`
  types : List InductiveType

instance [MonadStateOf NameGenerator m] : MonadNameGenerator m where
  getNGen := get
  setNGen := set

namespace Result

def getNestedIfAuxCtor (r : Result) (env' : Environment) (c : Name) : Option (Expr × Name) := do
  let .ctorInfo { induct, .. } ← env'.find? c | none
  return (← r.aux2nested.find? induct, induct)

def restoreCtorName (r : Result) (env' : Environment) (c : Name) : Name := Id.run do
  let (e, name) := (r.getNestedIfAuxCtor env' c).get!
  let .const I _ := e.getAppFn | unreachable!
  c.replacePrefix name I

def restoreNested (r : Result) (env' : Environment) (e : Expr)
    (auxRec : NameMap Name := {}) : Expr :=
  Id.run <| StateT.run' (s := { namePrefix := `_nested_fresh : NameGenerator }) do
  let pi := e.isForall
  let mut e := e
  let mut As := #[]
  let mut lctx : LocalContext := {}
  for _ in [:r.nparams] do
    match e with
    | .forallE name dom body bi | .lam name dom body bi =>
      let id := ⟨← mkFreshId⟩
      lctx := lctx.mkLocalDecl id name dom bi
      let arg := .fvar id
      e := body.instantiate1 arg
      As := As.push arg
    | _ => unreachable!
  e := e.replace fun t => do
    if let .const c ls := t then
      if let some recName := auxRec.find? c then
        return .const recName ls
    let .const c _ := t.getAppFn | none
    if let some nested := r.aux2nested.find? c then
      let args := t.getAppArgs
      assert! args.size ≥ r.nparams
      return mkAppRange ((nested.abstract r.params).instantiateRev As) r.nparams args.size args
    let (nested, auxI_name) ← r.getNestedIfAuxCtor env' c
    let args := t.getAppArgs
    assert! args.size ≥ r.nparams
    let nested' := (nested.abstract r.params).instantiateRev As
    nested'.withApp fun I I_args => do
    let .const I_c I_ls := I | unreachable!
    let c' := .const (c.replacePrefix auxI_name I_c) I_ls
    return mkAppRange (mkAppN c' I_args) r.nparams args.size args
  return if pi then lctx.mkForall As e else lctx.mkLambda As e

end Result

structure State where
  ngen : NameGenerator := { namePrefix := `_nested_fresh }
  nestedAux : Array (Expr × Name) := {}
  lvls : List Level
  newTypes : Array InductiveType
  nextIdx : Nat := 1
  deriving Inhabited

abbrev M := ReaderT Environment <| StateT State <| Except Exception

instance : MonadNameGenerator M where
  getNGen := return (← get).ngen
  setNGen ngen := modify fun s => { s with ngen }

-- TODO: remove partial
partial def mkUniqueName (n : Name) : M Name := fun env s =>
  let rec loop i :=
    let r := n.appendIndexAfter i
    if env.contains r then
      loop (i + 1)
    else
      pure (r, { s with nextIdx := i + 1 })
  loop s.nextIdx

def illFormed : Exception :=
  .other "invalid nested inductive datatype, ill-formed declaration"

def replaceParams (params : Array Expr) (e : Expr) (As : Array Expr) : M Expr := do
  assert! As.size == params.size
  return (e.abstract As).instantiateRev params

/-- IF `e` is of the form `I Ds is` where
  1) `I` is a nested inductive datatype (i.e., a previously declared inductive datatype),
  2) the parametric arguments `Ds` do not contain loose bound variables, and do contain inductive datatypes in `m_new_types`
THEN return the `inductive_val` in the `constant_info` associated with `I`.
Otherwise, return none. -/
def isNestedInductiveApp? (e : Expr) : M (Option InductiveVal) := do
  if !e.isApp then return none
  let .const fn _ := e.getAppFn | return none
  let env ← read
  let some (.inductInfo ci) := env.find? fn | return none
  let args := e.getAppArgs
  if ci.numParams > args.size then return none
  let mut isNested := false
  let mut looseBVars := false
  for i in [0:ci.numParams] do
    if args[i]!.hasLooseBVars then
      looseBVars := true
    let newTypes := (← get).newTypes
    if let some _ := args[i]!.find? fun
      | .const t _ => newTypes.any fun ty => t == ty.name
      | _ => false
    then
      isNested := true
  if !isNested then return none
  if looseBVars then
    throw <| .other s!"invalid nested inductive datatype '{fn}', \
      nested inductive datatypes parameters cannot contain local variables."
  return some ci

def instantiateForallParams (e : Expr) (hi : Nat) (params : Array Expr) :
    Except Exception Expr := do
  let mut e := e
  for _ in [:hi] do
    let .forallE _ _ body _ := e | throw illFormed
    e := body
  return e.instantiateRevRange 0 hi params

/-- If `e` is a nested occurrence `I Ds is`, return `Iaux As is` -/
def replaceIfNested (lctx : LocalContext) (params : Array Expr) (As : Array Expr) (e : Expr) :
    M (Option Expr) := do
  let some I_val ← isNestedInductiveApp? e | return none
  e.withApp fun fn args => do
  let .const I_name I_lvls := fn | unreachable!
  let I_nparams := I_val.numParams
  assert! I_nparams ≤ args.size
  let IAs := mkAppRange fn 0 I_nparams args -- `I As`
  let Iparams ← replaceParams params IAs As
  let st ← get
  if let some auxI_name := st.nestedAux.findSome? fun (e, n) =>
    if e == Iparams then some n else none
  then
    return mkAppRange (mkAppN (.const auxI_name st.lvls) As) I_nparams args.size args
  let mut result := none
  let env ← read
  for J_name in I_val.all do
    let .inductInfo J_info ← env.get J_name | unreachable!
    let J := .const J_name I_lvls
    let JAs := mkAppRange J 0 I_nparams args
    let auxJ_name ← mkUniqueName (`_nested ++ J_name)
    let auxJ_type := J_info.type.instantiateLevelParams J_info.levelParams I_lvls
    let auxJ_type := lctx.mkForall As <| ← instantiateForallParams auxJ_type I_nparams args
    let JAs' ← replaceParams params JAs As
    modify fun st => { st with nestedAux := st.nestedAux.push (JAs', auxJ_name) }
    if J_name == I_name then
      result := some <|
        mkAppRange (mkAppN (.const auxJ_name (← get).lvls) As) I_nparams args.size args
    let auxJ_ctors ← J_info.ctors.mapM fun J_ctor_name => do
      let J_ctor_info ← env.get J_ctor_name
      -- auxJ_cnstr_type still has references to `J`, this will be fixed later when we process it.
      let auxJ_ctor_name := J_ctor_name.replacePrefix J_name auxJ_name
      let auxJ_ctor_type := J_ctor_info.type.instantiateLevelParams J_ctor_info.levelParams I_lvls
      let auxJ_ctor_type ← instantiateForallParams auxJ_ctor_type I_nparams args
      return { name := auxJ_ctor_name, type := lctx.mkForall As auxJ_ctor_type }
    let newType := { name := auxJ_name, type := auxJ_type, ctors := auxJ_ctors }
    modify fun st => { st with newTypes := st.newTypes.push newType }
  assert! result.isSome
  return result

def replaceAllNested (lctx : LocalContext) (params : Array Expr) (As : Array Expr) (e : Expr) :
    M Expr := e.replaceM (replaceIfNested lctx params As)

def withParams (type : Expr) (nparams : Nat)
    (k : LocalContext → Expr → Array Expr → M α) : M α := loop {} type #[] nparams where
  loop lctx type params
  | 0 => k lctx type params
  | i+1 => do
    let .forallE name dom body bi := type
      | throw <| .other "invalid inductive datatype declaration, incorrect number of parameters"
    let id := ⟨← mkFreshId⟩
    let lctx := lctx.mkLocalDecl id name dom bi
    let arg := .fvar id
    loop lctx (body.instantiate1 arg) (params.push arg) i

def run (fuel nparams : Nat) (types : List InductiveType) : M Result := do
  let I :: _ := types
    | throw <| .other s!"invalid empty (mutual) inductive datatype declaration, \
        it must contain at least one inductive type."
  withParams I.type nparams fun lctx _ params => do
  let rec loop i
  | 0 => throw <| .other "deep recursion: ElimNestedInductive.run.loop"
  | fuel+1 => do
    let s ← get
    if _h : i < s.newTypes.size then
      let indType := s.newTypes[i]
      let ctors ← indType.ctors.mapM fun ctor => do
        withParams ctor.type nparams fun lctx ctorType As => do
        assert! As.size == nparams
        return { ctor with type := lctx.mkForall As (← replaceAllNested lctx params As ctorType) }
      modify fun s => { s with newTypes := s.newTypes.set! i { indType with ctors } }
      loop (i+1) fuel
    else
      let aux2nested := s.nestedAux.foldl (fun m (e, n) => m.insert n e) {}
      return { s with nparams := params.size, lctx, params, aux2nested, types := s.newTypes.toList }
  loop 0 fuel
end ElimNestedInductive

def mkAuxRecNameMap (env' : Environment) (types : List InductiveType) :
    List Name × NameMap Name := Id.run do
  let mainType :: _ := types | unreachable!
  let ntypes := types.length
  let mainName := mainType.name
  let some (.inductInfo mainInfo) := env'.find? mainName | unreachable!
  let allNames := mainInfo.all
  assert! allNames.length > ntypes
  let mut oldRecNames := #[]
  let mut recMap : NameMap Name := {}
  let mut nextIdx := 1
  for indName in allNames.drop ntypes do
    let oldRecName := mkRecName indName
    let newRecName := (mkRecName mainName).appendIndexAfter nextIdx
    nextIdx := nextIdx + 1
    recMap := recMap.insert oldRecName newRecName
    oldRecNames := oldRecNames.push oldRecName
  return (oldRecNames.toList, recMap)

def checkNoNestedAux (n : Name) (e : Expr) : Except Exception Unit := do
  if (e.find? fun
      | .const c _ => (`_nested).isPrefixOf c
      | .proj s _ _ => (`_nested).isPrefixOf s
      | _ => false).isSome then
    throw <| .other s!"invalid declaration '{n}', it uses the reserved prefix '_nested'"

def Environment.addInductive (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig := {}) :
    Except Exception Environment := do
  for indType in types do
    env.checkNoMVarNoFVar indType.name indType.type
    for ctor in indType.ctors do
      env.checkNoMVarNoFVar ctor.name ctor.type
      checkNoNestedAux ctor.name ctor.type
  let res ← ElimNestedInductive.run fuel.inductiveFuel nparams types env
    |>.run' { lvls := lparams.map .param, newTypes := types.toArray }
  let numNested := res.aux2nested.size
  let safety := if isUnsafe then .unsafe else .safe
  let env' ← AddInductive.run nparams res.types numNested
    { env, allowPrimitive, lparams, fuel, safety }
  if numNested = 0 then return env'
  let allIndNames := types.map (·.name)
  let (recNames', recNameMap') := mkAuxRecNameMap env' types
  (·.2) <$> StateT.run (s := env) do
  let processRec recName := do
    let newRecName := recNameMap'.getD recName recName
    let some (.recInfo recInfo) := env'.find? recName | unreachable!
    let newRecType := res.restoreNested env' recInfo.type recNameMap'
    let newRules ← recInfo.rules.mapM fun rule => do
      let newRhs := res.restoreNested env' rule.rhs recNameMap'
      let newCtorName := if newRecName == recName then rule.ctor else
        res.restoreCtorName env' rule.ctor
      return { rule with ctor := newCtorName, rhs := newRhs }
    (← MonadState.get).checkName newRecName allowPrimitive
    modify (·.add <| .recInfo { recInfo with
      name := newRecName, type := newRecType, all := allIndNames, rules := newRules })
  for indType in types do
    let some (.inductInfo ind) := env'.find? indType.name | unreachable!
    (← get).checkName ind.name allowPrimitive
    modify (·.add <| .inductInfo { ind with all := allIndNames })
    for ctorName in ind.ctors do
      let some (.ctorInfo ctor) := env'.find? ctorName | unreachable!
      let newType := res.restoreNested env' ctor.type
      (← get).checkName ctor.name allowPrimitive
      modify (·.add <| .ctorInfo { ctor with type := newType })
    processRec (mkRecName indType.name)
  recNames'.forM processRec
  TypeChecker.M.run (← get) (safety := safety) (lctx := res.lctx)
      (lparams := lparams) (fuel := fuel) do
    res.aux2nested.forM fun _ e => do _ ← TypeChecker.checkType e
