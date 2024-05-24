import Lean4Lean.TypeChecker
import Lean4Lean.Stream

namespace Lean

open private add from Lean.Environment

namespace AddInductive
open TypeChecker

/--
Record of free variables to be used in generating recursor types/rules.
-/
structure RecInfo where
  motive : Expr
  minors : Array Expr
  indices : Array Expr
  major : Expr
  deriving Inhabited

structure InductiveStats where
  -- FIXME lctx is unused
  lctx : LocalContext := {}
  levels : List Level
  resultLevel : Level
  nindices : Array Nat := #[]
  indConsts : Array Expr
  params : Array Expr
  isNotZero : Bool
  deriving Inhabited

structure Context where
  env : Environment
  lctx : LocalContext := {}
  ngen : NameGenerator := { namePrefix := `_ind_fresh }
  safety : DefinitionSafety
  allowPrimitive : Bool

abbrev M := ReaderT Context <| Except KernelException

instance : MonadLocalNameGenerator M where
  withFreshId f c := f c.ngen.curr { c with ngen := c.ngen.next }

instance (priority := low) : MonadLift TypeChecker.M M where
  monadLift x c := x.run c.env c.safety c.lctx

instance (priority := low+1) : MonadWithReaderOf LocalContext M where
  withReader f x := withReader (fun c => { c with lctx := f c.lctx }) x

instance : MonadLCtx M where
  getLCtx := return (← read).lctx

@[inline] def withEnv (f : Environment → Environment) (x : M α) : M α :=
  withReader (fun c => { c with env := f c.env }) x

def getType (fvar : Expr) : M Expr :=
  return ((← getLCtx).get! fvar.fvarId!).type

def checkName (name : Name) : M Unit := fun c => c.env.checkName name c.allowPrimitive

/--
Checks that the types of the mutually defined `indTypes` are valid, namely that
they have the same parameters and inhabit the same universes. Collects
information about these types in an `InductiveStats` that is passed to the
callback `k`.
-/
def checkInductiveTypes
    (lparams : List Name) (nparams : Nat) (indTypes : Array InductiveType)
    (k : InductiveStats → M α) : M α := do
  let rec loopInd dIdx stats : M α := do
    if _h : dIdx < indTypes.size then
      let indType := indTypes[dIdx]
      let env := (← read).env
      let type := indType.type
      checkName indType.name
      checkName (mkRecName indType.name)
      env.checkNoMVarNoFVar indType.name type
      _ ← check type lparams
      -- checks that the parameters are valid, counts the number of indices,
      -- and gets the sort that this inductive inhabits
      let rec loop stats type i nindices fuel k : M α := match fuel with
      | 0 => throw .deepRecursion
      | fuel+1 => do
        if let .forallE name dom body bi := type then
          if i < nparams then
            if stats.indConsts.isEmpty then
              withLocalDecl name dom.consumeTypeAnnotations bi fun param => do
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
            withLocalDecl name dom.consumeTypeAnnotations bi fun arg => do
              let type := body.instantiate1 arg
              loop stats (← whnf type) i (nindices + 1) fuel k
        else
          if i != nparams then
            throw <| .other "number of parameters mismatch in inductive datatype declaration"
          k type stats nindices
      loop stats (← whnf type) 0 0 1000 fun type stats nindices => do
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
        assert! stats.levels.length == lparams.length
        assert! stats.nindices.size == indTypes.size
        assert! stats.indConsts.size == indTypes.size
        assert! stats.params.size == nparams
        stats
  termination_by indTypes.size - dIdx
  loopInd 0 { (default : InductiveStats) with levels := lparams.map .param }

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
    -- `hasIndOcc indConsts dom` is sufficient since constructor positivity is
    -- checked elsewhere
    | .forallE _ dom body _ => dom.isForall && hasIndOcc indConsts dom || loop body
    | _ => false
  indTypes.any fun indType => indType.ctors.any fun ctor => loop ctor.type

/--
Adds a `ConstantInfo.inductInfo` for each of `indTypes` to `env`.
-/
def declareInductiveTypes
    (stats : InductiveStats)
    (levelParams : List Name) (numParams : Nat) (indTypes : Array InductiveType)
    (isUnsafe isNested : Bool) (env : Environment) : Environment :=
  let all := indTypes.map (·.name) |>.toList
  let infos := indTypes.zipWith stats.nindices fun indType numIndices =>
    .inductInfo { indType with
      levelParams, numParams, numIndices, all, isUnsafe, isNested
      ctors := indType.ctors.map (·.name)
      isRec := isRec indTypes stats.indConsts
      isReflexive := isReflexive indTypes stats.indConsts }
  infos.foldl add env

def isValidIndAppIdx (stats : InductiveStats) (t : Expr) (i : Nat) : Bool :=
  t.withApp fun I args => Id.run do
  unless I == stats.indConsts[i]! && args.size == stats.params.size + stats.nindices[i]! do
    return false
  for i in [:stats.params.size] do
    if stats.params[i]! != args[i]! then return false
  for i in [stats.params.size:args.size] do
    if hasIndOcc stats.indConsts args[i]! then return false
  true

def isValidIndApp? (stats : InductiveStats) (t : Expr) : Option Nat := do
  for i in [:stats.indConsts.size] do
    if isValidIndAppIdx stats t i then
      return i
  none

def isRecArg (stats : InductiveStats) (t : Expr) : M (Option Nat) := loop t 1000 where
  loop t
  | 0 => throw .deepRecursion
  | fuel+1 => do
    let t ← whnf t
    let .forallE name dom body bi := t | return isValidIndApp? stats t
    withLocalDecl name dom.consumeTypeAnnotations bi fun arg => do
    loop (body.instantiate1 arg) fuel

def checkPositivity (stats : InductiveStats) (t : Expr) (ctor : Name) (idx : Nat) :
    M Unit := loop t 1000 where
  loop t
  | 0 => throw .deepRecursion
  | fuel+1 => do
    let t ← whnf t
    if !hasIndOcc stats.indConsts t then return
    if let .forallE name dom body bi := t then
      if hasIndOcc stats.indConsts dom then
        throw <| .other s!"arg #{idx + 1} of '{ctor
          }' has a non positive occurrence of the datatypes being declared"
      withLocalDecl name dom.consumeTypeAnnotations bi fun arg => do
      loop (body.instantiate1 arg) fuel
    else if let none := isValidIndApp? stats t then
      throw <| .other s!"arg #{idx + 1} of '{ctor
        }' has a non valid occurrence of the datatypes being declared"

/--
Checks whether the constructors `mkAppN indTypes[i].ctors[j] stats.params` are
admissible for their inductive types `mkAppN stats.indConsts[i] stats.params`,
requiring that they are well-typed and respect positivity and output type
constraints.
-/
def checkConstructors (indTypes : Array InductiveType) (lparams : List Name)
    (stats : InductiveStats) (isUnsafe : Bool) : M Unit := do
  let env ← getEnv
  for h : idx in [:indTypes.size] do
    let indType := indTypes[idx]'h.2
    let mut foundCtors : NameSet := {}
    for ctor in indType.ctors do
      let n := ctor.name
      if foundCtors.contains n then
        throw <| .other s!"duplicate constructor name '{n}'"
      foundCtors := foundCtors.insert n
      let t := ctor.type
      checkName n
      env.checkNoMVarNoFVar n t
      _ ← check t lparams
      let rec loop t i
      | 0 => throw .deepRecursion
      | fuel+1 => do
        if let .forallE name dom body bi := t then
          if let some param := stats.params[i]? then
            unless ← isDefEq dom (← getType param) do
              throw <| .other
                s!"arg #{i + 1} of '{n}' does not match inductive datatype parameters"
            -- instantiate params with those from the inductive type signature
            loop (body.instantiate1 param) (i + 1) fuel
          else
            let s ← ensureType dom
            unless stats.resultLevel.isZero || stats.resultLevel.geq' s.sortLevel! do
              throw <| .other s!"universe level of type_of(arg #{i + 1
                }) of '{n}' is too big for the corresponding inductive datatype"
            if !isUnsafe then
              checkPositivity stats dom n i
            withLocalDecl name dom.consumeTypeAnnotations bi fun arg => do
              loop (body.instantiate1 arg) (i + 1) fuel
        else if !isValidIndAppIdx stats t idx then
          throw <| .other s!"invalid return type for '{n}'"
      loop t 0 1000

/--
Adds a `ConstantInfo.ctorInfo` for each of the constructors of `indTypes` to `env`.
-/
def declareConstructors (stats : InductiveStats) (levelParams : List Name)
    (indTypes : Array InductiveType) (isUnsafe : Bool)
    (env : Environment) : Environment :=
  indTypes.foldl (init := env) fun env indType =>
    indType.ctors.foldlIdx (init := env) fun cidx env ctor =>
      let type := ctor.type
      let rec arity i
        | .forallE _ _ body _ => arity (i+1) body
        | _ => i
      let arity := arity 0 type
      add env <| .ctorInfo {
        levelParams, type, cidx, isUnsafe
        name := ctor.name
        induct := indType.name
        numParams := stats.params.size
        numFields := assert! arity ≥ stats.params.size; arity - stats.params.size
      }

/--
Returns true if the recursors of `indTypes` can map into any universe
(i.e, they are large-eliminating).

Inductives that live in some `Type u` are always large-eliminating.
Mutual inductives that live in `Prop` are never large-eliminating.
Single inductives in `Prop` are large-eliminating iff they have no
constructors, or a single constructor whose non-proof fields are all output
type parameters/indices.
-/
def isLargeEliminator (stats : InductiveStats) (indTypes : Array InductiveType) : M Bool := do
  if stats.isNotZero then return true
  let #[indType] := indTypes | return false
  match indType.ctors with
  | [] => return true
  | [ctor] =>
    let rec loop type i toCheck
    | 0 => throw .deepRecursion
    | fuel+1 => do
      if let .forallE name dom body bi := type then
        withLocalDecl name dom.consumeTypeAnnotations bi fun arg => do
          let mut toCheck := toCheck
          if i ≥ stats.params.size then
            if !(← ensureType dom).sortLevel!.isZero then
              toCheck := toCheck.push arg
          loop (body.instantiate1 arg) (i + 1) toCheck fuel
      else
        return toCheck.all type.getAppArgs.contains
    loop ctor.type 0 #[] 1000
  | _ => return false

/--
Returns the universe level to use for the sort of the output type of the
recursors of `indTypes`.

This is a fresh universe level parameter if the recursors of `indTypes` are
large-eliminating, and level zero (output type `Prop`) otherwise.
-/
partial -- TODO: remove
def getElimLevel (stats : InductiveStats) (lparams : List Name) (indTypes : Array InductiveType) :
    M Level := do
  unless ← isLargeEliminator stats indTypes do return .zero
  let rec loop u i := do
    unless lparams.contains u do return .param u
    loop ((`u).appendIndexAfter i) (i + 1)
  loop `u 1

def isKTarget (stats : InductiveStats) (indTypes : Array InductiveType) : M Bool := do
  let #[indType] := indTypes | return false
  unless stats.resultLevel.isZero do return false
  let [ctor] := indType.ctors | return false
  let rec loop i
    | .forallE _ _ body _ => i < stats.params.size && loop (i + 1) body
    | _ => true
  return loop 0 ctor.type

/--
Assuming that `t := I p₁ ⋯ pₙ i₁ ⋯ iₘ` is a valid application of inductive type `I`,
returns the index of `I` within its mutual block and the list of indices `#[i₁, ⋯, iₘ]`.
-/
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
        withLocalDecl name dom.consumeTypeAnnotations bi fun arg => do
        loopArgs1 stats (← whnf <| body.instantiate1 arg) i (indices.push arg) fuel k
    else
      k indices

variable (stats : InductiveStats) (indTypes : Array InductiveType) (elimLevel : Level) in
def loopInd1 (dIdx : Nat) (recInfos : Array RecInfo) (k : Array RecInfo → M α) : M α := do
  if _h : dIdx < indTypes.size then
    loopArgs1 stats (← whnf indTypes[dIdx].type) 0 #[] 1000 fun indices =>
    let tTy := mkAppN (mkAppN stats.indConsts[dIdx]! stats.params) indices
    withLocalDecl `t tTy.consumeTypeAnnotations .default fun major => do
    let lctx ← getLCtx
    let motiveTy := lctx.mkForall indices <| lctx.mkForall #[major] <| .sort elimLevel
    let name := if indTypes.size > 1 then (`motive).appendIndexAfter (dIdx+1) else `motive
    withLocalDecl name motiveTy.consumeTypeAnnotations .default fun motive => do
    loopInd1 (dIdx + 1) (recInfos.push { motive, minors := #[], indices, major }) k
  else
    k recInfos
termination_by indTypes.size - dIdx

variable (stats : InductiveStats) in
/--
Assuming that `t` is a constructor type, returns `k t' bu u`, where `t'` is the
output type, `bu` is a list of fvars for each of the argument types, and `u` is
the fvars of `bu` corresponding to the recursive constructor fields.
-/
def loopCtorArgs (t : Expr) (k : Expr → Array Expr → Array Expr → M α) : M α :=
  loop t 0 #[] #[] 1000
where
  loop t i bu u
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := t then
      if let some param := stats.params[i]? then
        loop (body.instantiate1 param) (i + 1) bu u fuel
      else
        withLocalDecl name dom.consumeTypeAnnotations bi fun arg => do
        let bu := bu.push arg
        let u := if (← isRecArg stats dom).isSome then u.push arg else u
        loop (body.instantiate1 arg) (i + 1) bu u fuel
    else k t bu u

def loopUArgs (ui : Expr) (k : Expr → Array Expr → M α) : M α := do
  loop (← whnf (← inferType ui)) #[] 1000
where
  loop uiTy xs
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := uiTy then
      withLocalDecl name dom.consumeTypeAnnotations bi fun arg => do
      loop (← whnf <| body.instantiate1 arg) (xs.push arg) fuel
    else
      k uiTy xs

variable (stats : InductiveStats) (u : Array Expr) (recInfos : Array RecInfo) in
/--
Given a list `u` of recursive constructor field types, returns `k v`,
where `v` is a list of fresh fvars for each inductive hypothesis.
-/
def loopU (i : Nat) (v : Array Expr) (k : Array Expr → M α) : M α := do
  if _h : i < u.size then
    let ui := u[i]
    let viTy ← loopUArgs ui fun uiTy xs => do
      let (itIdx, itIndices) := getIIndices stats uiTy
      return (← getLCtx).mkForall xs <|
        .app (mkAppN recInfos[itIdx]!.motive itIndices) (mkAppN ui xs)
    let vName := ((← getLCtx).get! ui.fvarId!).userName.appendAfter "_ih"
    withLocalDecl vName viTy.consumeTypeAnnotations .default fun vi => do
    loopU (i + 1) (v.push vi) k
  else
    k v
termination_by u.size - i

variable (stats : InductiveStats) (indTypeName : Name) (dIdx : Nat) in
/--
Given `recInfos`, returns `k recInfos'`, where each of the `RecInfo`s in
`recInfos'` has been completed by populating it with fvars for their recursor's
minor premises.
-/
def loopCtors (recInfos : Array RecInfo)
    (ctors : List Constructor) (k : Array RecInfo → M α) : M α := match ctors with
  | ctor::ctors =>
    loopCtorArgs stats ctor.type fun t bu u => do
    let (itIdx, itIndices) := getIIndices stats t
    let introApp := mkAppN (mkAppN (.const ctor.name stats.levels) stats.params) bu
    let motiveApp := Expr.app (mkAppN recInfos[itIdx]!.motive itIndices) introApp
    loopU stats u recInfos 0 #[] fun v => do
    let lctx ← getLCtx
    let minorTy := lctx.mkForall bu <| lctx.mkForall v motiveApp
    let minorName := ctor.name.replacePrefix indTypeName .anonymous
    withLocalDecl minorName minorTy.consumeTypeAnnotations .default fun minor => do
    let recInfos := recInfos.modify dIdx fun s => { s with minors := s.minors.push minor }
    loopCtors recInfos ctors k
  | [] => k recInfos

variable (stats : InductiveStats) (indTypes : Array InductiveType) in
@[inherit_doc loopCtors]
def loopInd2 (dIdx : Nat) (recInfos : Array RecInfo) (k : Array RecInfo → M α) : M α := do
  if _h : dIdx < indTypes.size then
    let indType := indTypes[dIdx]
    let indTypeName := indType.name
    loopCtors stats indTypeName dIdx recInfos indType.ctors fun recInfos =>
    loopInd2 (dIdx + 1) recInfos k
  else
    k recInfos
termination_by indTypes.size - dIdx

end mkRecInfos

/--
Given the list of inductive types `indTypes`, returns `k recInfos`, where
`recInfos` contains all of the fvars needed to construct the recursor types/rules.
-/
def mkRecInfos (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (k : Array RecInfo → M α) : M α :=
  mkRecInfos.loopInd1 stats indTypes elimLevel 0 #[] fun recInfos =>
  mkRecInfos.loopInd2 stats indTypes 0 recInfos k

def getRecLevels (elimLevel : Level) (levels : List Level) : List Level :=
  if elimLevel.isParam then elimLevel :: levels else levels

def getRecLevelParams (elimLevel : Level) (lparams : List Name) : List Name :=
  if let .param u := elimLevel then u :: lparams else lparams

/--
Constructs the recursor rules corresponding to each constructor in `indTypes`.
-/
def mkRecRules (indTypes : Array InductiveType) (elimLevel : Level) (stats : InductiveStats)
    (dIdx : Nat) (motives : Array Expr) (minors : Array Expr) :
    StateT Nat M (List RecursorRule) := do
  let d := indTypes[dIdx]!
  let lvls := getRecLevels elimLevel stats.levels
  let mut rules := #[]
  for ctor in d.ctors do
    let rule ← fun minorIdx => mkRecInfos.loopCtorArgs stats ctor.type fun _ bu u =>
      let rec loopU i (v : Array Expr) k := do
        if _h : i < u.size then
          let ui := u[i]
          let val ← mkRecInfos.loopUArgs ui fun uiTy xs => do
            let (itIdx, itIndices) := getIIndices stats uiTy
            let val := .const (mkRecName indTypes[itIdx]!.name) lvls
            let val := mkAppN (mkAppN (mkAppN (mkAppN val stats.params) motives) minors) itIndices
            return (← getLCtx).mkLambda xs <| val.app (mkAppN ui xs)
          loopU (i + 1) (v.push val) k
        else
          k v
      termination_by u.size - i
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

/--
If the inductive types declared in `types` are admissible, adds their types,
constructors and recursors to the to the environment.
-/
def run (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isNested : Bool) : M Environment := do
  let isUnsafe := (← read).safety != .safe
  let indTypes := types.toArray
  Environment.checkDuplicatedUnivParams lparams
  checkInductiveTypes lparams nparams indTypes fun stats => do
  withEnv (declareInductiveTypes stats lparams nparams indTypes isUnsafe isNested) do
  checkConstructors indTypes lparams stats isUnsafe
  withEnv (declareConstructors stats lparams indTypes isUnsafe) do
  let elimLevel ← getElimLevel stats lparams indTypes
  mkRecInfos stats indTypes elimLevel fun recInfos => do
  let motives := recInfos.map (·.motive)
  let minors := recInfos.concatMap (·.minors)
  let numMinors := minors.size
  let numMotives := motives.size
  let all := indTypes.map (·.name) |>.toList
  let lctx ← getLCtx
  let k ← isKTarget stats indTypes
  let isUnsafe := (← read).safety != .safe
  StateT.run' (s := 0) do
  let mut env ← getEnv
  for h : dIdx in [:indTypes.size] do
    let indType := indTypes[dIdx]'h.2
    let info := recInfos[dIdx]!
    let ty :=
      -- all of the recursors in the block share the same parameters, motives, and minor premises
      lctx.mkForall stats.params <|
      lctx.mkForall motives <|
      lctx.mkForall minors <|
      lctx.mkForall info.indices <|
      lctx.mkForall #[info.major] <|
      .app (mkAppN info.motive info.indices) info.major
    let rules ← mkRecRules indTypes elimLevel stats dIdx motives minors
    env := add env <| .recInfo {
      name := mkRecName indType.name
      levelParams := getRecLevelParams elimLevel lparams
      type := ty.inferImplicit 1000 false -- note: flag has reversed polarity from C++
      numParams := stats.params.size
      numIndices := stats.nindices[dIdx]!
      all, numMotives, numMinors, rules, k, isUnsafe
    }
  pure env

end AddInductive

namespace ElimNestedInductive

structure Result where
  ngen : NameGenerator
  nparams : Nat
  /--
  Mapping from aux inductive type names to their original nested occurrences,
  where this block's `nparams` parameters have been replaced by loose bvars.
  -/
  aux2nested : NameMap Expr -- exprs contain `nparams` loose bvars
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

/--
Given a lambda or forall expression `e` binding `r.nparams` parameters `As`:
- Replaces all uses of aux inductive types with the nested occurrences
  found in the original inductive type declarations that generated them.
- Replaces all uses of aux inductive constructor applications with
  constructor applications of the nested occurrence's inductive type.
The loose bvars in the nested occurrences' parameters are instantiated by `As`.

This is meant to be used in the following cases:
  1) On recursor types/rules and constructor types of inductive types referencing
     aux inductive types.
  2) On the recursor types/rules of aux inductive types themselves,
     which are then added as additional elimination principles under the block's
     first-declared inductive type.
This aligns these rules/constructors with the original declaration of the
nested inductive, eliminating the need for the aux inductive while
maintaining the mutual recursion principle that was generated between them.
-/
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
      return mkAppRange (nested.instantiateRev As) r.nparams args.size args
    let (nested, auxI_name) ← r.getNestedIfAuxCtor env' c
    let args := t.getAppArgs
    assert! args.size ≥ r.nparams
    let nested' := nested.instantiateRev As
    nested'.withApp fun I I_args => do
    let .const I_c I_ls := I | unreachable!
    let c' := .const (c.replacePrefix auxI_name I_c) I_ls
    return mkAppRange (mkAppN c' I_args) r.nparams args.size args
  return if pi then lctx.mkForall As e else lctx.mkLambda As e

end Result

structure State where
  ngen : NameGenerator := { namePrefix := `_nested_fresh }
  /--
  List of nested type family occurrences paired with the name of its
  corresponding aux inductive type.
  -/
  nestedAux : Array (Expr × Name) := {}
  lvls : List Level
  /--
  List of inductive type declarations to be incrementally updated with
  declarations corresponding to the aux inductive types that are
  replacing nested occurrences.
  -/
  newTypes : Array InductiveType
  nextIdx : Nat := 1
  deriving Inhabited

abbrev M := ReaderT Environment <| StateT State <| Except KernelException

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

def illFormed : KernelException :=
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
    throw <| .other "invalid nested inductive datatype '{fn
      }', nested inductive datatypes parameters cannot contain local variables."
  return some ci

def instantiateForallParams (e : Expr) (hi : Nat) (params : Array Expr) :
    Except KernelException Expr := do
  let mut e := e
  for _ in [:hi] do
    let .forallE _ _ body _ := e | throw illFormed
    e := body
  return e.instantiateRevRange 0 hi params

/--
In the context `lctx` with parameters `As`, if `e` is a nested occurrence
`I Ds is`, constructs a new aux inductive type `Iaux` representing
the "specialization" of `I` to `Ds`, abstracted over the parameters
corresponding to `As`, with the inductive type family `Iaux As` isomorphic to
`I Ds`. This eliminates the non-positive instance(s) in `Ds` (any other
non-positive instances are not replaced, and will result in an error).
Auxiliary constructor types for `Iaux` are similarly constructed.

`Iaux`, together with similarly constructed aux inductive type decls for
each of the inductives in `I`'s mutual block, are added to this mutual block.

Returns `Iaux As is`.
-/
def replaceIfNested (lctx : LocalContext) (params : Array Expr) (As : Array Expr) (e : Expr) :
    M (Option Expr) := do
  let some I_val ← isNestedInductiveApp? e | return none
  e.withApp fun fn args => do
  let .const I_name I_lvls := fn | unreachable!
  let I_nparams := I_val.numParams
  assert! I_nparams ≤ args.size
  let IDs := mkAppRange fn 0 I_nparams args -- `I Ds`
  let IDsParams ← replaceParams params IDs As
  let st ← get
  if let some auxI_name := st.nestedAux.findSome? fun (e, n) =>
    if e == IDsParams then some n else none
  then
    return mkAppRange (mkAppN (.const auxI_name st.lvls) As) I_nparams args.size args
  let mut result := none
  let env ← read
  for J_name in I_val.all do
    let .inductInfo J_info ← env.get J_name | unreachable!
    let J := .const J_name I_lvls
    let JDs := mkAppRange J 0 I_nparams args
    let auxJ_name ← mkUniqueName (`_nested ++ J_name)
    -- (the aux inductives will use `(← get).lvls` for their `levelParams`)
    let auxJ_type := J_info.type.instantiateLevelParams J_info.levelParams I_lvls
    let auxJ_type := lctx.mkForall As <| ← instantiateForallParams auxJ_type I_nparams args
    -- must replace `As` with `params` before adding to cache because different constructors will have different `As`
    let JDsParams ← replaceParams params JDs As
    modify fun st => { st with nestedAux := st.nestedAux.push (JDsParams, auxJ_name) }
    if J_name == I_name then
      result := some <|
        mkAppRange (mkAppN (.const auxJ_name (← get).lvls) As) I_nparams args.size args
    let auxJ_ctors ← J_info.ctors.mapM fun J_ctor_name => do
      let J_ctor_info ← env.get J_ctor_name
      -- auxJ_cnstr_type still has references to `J`, this will be fixed in a subsequent iteration of `ElimNestedInductive.run`
      let auxJ_ctor_name := J_ctor_name.replacePrefix J_name auxJ_name
      let auxJ_ctor_type := J_ctor_info.type.instantiateLevelParams J_ctor_info.levelParams I_lvls
      let auxJ_ctor_type ← instantiateForallParams auxJ_ctor_type I_nparams args
      return { name := auxJ_ctor_name, type := lctx.mkForall As auxJ_ctor_type }
    let newType := { name := auxJ_name, type := auxJ_type, ctors := auxJ_ctors }
    modify fun st => { st with newTypes := st.newTypes.push newType }
  assert! result.isSome
  return result

/--
In the context `lctx` with parameters `As`, returns constructor type `e` where
all nested occurrences have been replaced by specialized auxiliary types so
that there are no non-positive occurrences in the parameters of any inductive
type found in `e`. `params` are the parameters of this mutual inductive block,
and are used to replace `As` when necessary for caching. Updates this mutual
inductive block to include these new auxiliary types.
-/
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

/--
Converts the mutual inductive block declaration `types` such that any nested
instances of inductive types found in their constructors have been replaced
with fresh auxiliary inductive types. The new block of inductive types
(including these auxiliary types) is returned in `Result.types`.
-/
def run (nparams : Nat) (types : List InductiveType) : M Result := do
  let I :: _ := types
    | throw <| .other s!"invalid empty (mutual) inductive datatype declaration, {""
        }it must contain at least one inductive type."
  withParams I.type nparams fun _ _ params => do
  let rec loop i
  | 0 => throw <| .other "deep recursion: ElimNestedInductive.run.loop"
  | fuel+1 => do
    let s ← get
    if _h : i < s.newTypes.size then
      let indType := s.newTypes[i]
      -- constructors with all instances of nested types replaced by auxiliary ones (that are specific to `indType`)
      let ctors ← indType.ctors.mapM fun ctor => do
        withParams ctor.type nparams fun lctx ctorType As => do
        assert! As.size == nparams
        return { ctor with type := lctx.mkForall As (← replaceAllNested lctx params As ctorType) }
      modify fun s => { s with newTypes := s.newTypes.set! i { indType with ctors } }
      loop (i+1) fuel
    else
      let aux2nested := s.nestedAux.foldl (fun m (e, n) => m.insert n (e.abstract params)) {}
      return { s with nparams := params.size, aux2nested, types := s.newTypes.toList }
  loop 0 1000
end ElimNestedInductive

/--
Creates a mapping from the recursor names of aux inductive types to the names
of new recursors namespaced under the first-declared inductive of this block.
Returns this mapping, along with a list of all of the aux recursor names.
-/
def mkAuxRecNameMap (env' : Environment) (types : List InductiveType) :
    List Name × NameMap Name := Id.run do
  let mainType :: _ := types | unreachable!
  let ntypes := types.length
  let mainName := mainType.name
  let some (.inductInfo mainInfo) := env'.find? mainName | unreachable!
  let allNames := mainInfo.all
  assert! allNames.length > ntypes
  let mut auxRecNames := #[]
  let mut recMap : NameMap Name := {}
  let mut nextIdx := 1
  for auxIndName in allNames.drop ntypes do
    let auxRecName := mkRecName auxIndName
    let newRecName := (mkRecName mainName).appendIndexAfter nextIdx
    nextIdx := nextIdx + 1
    recMap := recMap.insert auxRecName newRecName
    auxRecNames := auxRecNames.push auxRecName
  return (auxRecNames.toList, recMap)

/--
Adds the inductive types, constructors, and recursors corresponding to the
mutual block of inductive declarations `types` to `env`, where `lparams` is a
list of level parameters, and `nparams` is the number of inductive type
parameters (which must be the same for every inductive in the block).

This happens in three steps:
  1) `types` is preprocessed to eliminate occurrences of nested inductive types
     by substituting them for specialized auxiliary inductive types which are
     added to the mutual block.
  2) This block is then processed to check admissibility and generate the types,
     constructors, and recursors (+ recursor rules) for each of the declarations.
     If there were no nested occurrences, these constants are added to the `env`
     which is then returned.
  3) If there were nested occurrences, these terms are processed to replace any
     uses of the auxiliary inductive types/constructors with those of the
     original type from the nested occurrence. The auxiliary inductive types'
     recursors are namespaced under the first-declared inductive of this block,
     and finally only the original (non-auxiliary) inductive declarations'
     constants are added to the environment.

For example, consider the following nested inductive type:
```
inductive N (α : Type): Type where
| mk : Option (N α) → N α
```
After (1), its declaration would be converted to:
```
mutual
inductive N (α : Type) : Type where
| mk : _nested_Option α → N α

inductive _nested_Option (α : Type) where
| none : _nested_Option α
| some : N α → _nested_Option α
end
```
The recursors generated by (2) would be:
```
Lean.N.rec.{u} {α : Type}
  {m1 : N α → Sort u} {m2 : _nested_Option α → Sort u}
  (mk : (a : _nested_Option α) → m2 a → m1 (N.mk a))
  (none : m2 _nested_Option.none) (some : (a : N α) → m1 a → m2 (_nested_Option.some a))
  (t : N α) : m1 t
Lean._nested_Option.rec.{u} {α : Type}
  {m1 : N α → Sort u} {m2 : _nested_Option α → Sort u}
  (mk : (a : _nested_Option α) → m2 a → m1 (N.mk a))
  (none : m2 _nested_Option.none) (some : (a : N α) → m1 a → m2 (_nested_Option.some a))
  (t : _nested_Option α) : m2 t
```
Following the replacement of auxiliary inductive types/constructors in (3), these would become:
```
Lean.N.rec.{u} {α : Type}
  {m1 : N α → Sort u} {m2 : Option (N α) → Sort u}
  (mk : (a : Option (N α)) → m2 a → m1 (N.mk a))
  (none : m2 none) (some : (val : N α) → m1 val → m2 (some val))
  (t : N α) : m1 t
Lean.N.rec_1.{u} {α : Type}
  {m1 : N α → Sort u} {m2 : Option (N α) → Sort u}
  (mk : (a : Option (N α)) → m2 a → m1 (N.mk a))
  (none : m2 none) (some : (val : N α) → m1 val → m2 (some val))
  (t : Option (N α)) : m2 t
```
-/
def Environment.addInductive (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool) :
    Except KernelException Environment := do
  let res ← ElimNestedInductive.run nparams types env
    |>.run' { lvls := lparams.map .param, newTypes := types.toArray }
  let isNested := !res.aux2nested.isEmpty
  let env' ← AddInductive.run lparams nparams res.types isNested
    { env, allowPrimitive, safety := if isUnsafe then .unsafe else .safe }
  if !isNested then return env'
  let allIndNames := types.map (·.name)
  let (recNames', recNameMap') := mkAuxRecNameMap env' types
  (·.2) <$> StateT.run (s := env) do
  let processRec recName := do
    let newRecName := recNameMap'.findD recName recName
    let some (.recInfo recInfo) := env'.find? recName | unreachable!
    let newRecType := res.restoreNested env' recInfo.type recNameMap'
    let newRules ← recInfo.rules.mapM fun rule => do
      let newRhs := res.restoreNested env' rule.rhs recNameMap'
      let newCtorName := if newRecName == recName then rule.ctor else
        res.restoreCtorName env' rule.ctor
      return { rule with ctor := newCtorName, rhs := newRhs }
    (← MonadState.get).checkName newRecName
    modify (add · <| .recInfo { recInfo with
      name := newRecName, type := newRecType, all := allIndNames, rules := newRules })
  for indType in types do
    let some (.inductInfo ind) := env'.find? indType.name | unreachable!
    modify (add · <| .inductInfo { ind with all := allIndNames })
    for ctorName in ind.ctors do
      let some (.ctorInfo ctor) := env'.find? ctorName | unreachable!
      let newType := res.restoreNested env' ctor.type
      modify (add · <| .ctorInfo { ctor with type := newType })
    processRec (mkRecName indType.name)
  recNames'.forM processRec
