import Batteries.Data.List.Basic
import Lean4Lean.Environment.Basic
import Lean4Lean.TypeChecker
import Lean4Lean.ExprUniverses

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace AddInductive
open TypeChecker

structure RecCallTemplate where
  major : Expr
  args : Array Expr
  /-- The local context of the minor pass, containing the temporary higher-order binders in
  `args`.  These binders are out of scope when the recursor is installed, so
  rule construction must not consult the ambient context for them. -/
  lctx : LocalContext
  targetTypeIdx : Nat
  targetIndices : Array Expr
  /-- The complete call closed over its temporary higher-order binders, with
  one outer de Bruijn placeholder for the recursor application.  It is
  produced before those temporary identifiers leave scope, so later outer
  binders cannot be confused with them even if the reader-local name
  generator reuses an identifier. -/
  template : Expr
  deriving Inhabited

structure RecRuleTemplate where
  ctor : Name
  fields : Array Expr
  /-- The local context of the minor pass, containing the temporary constructor fields. -/
  lctx : LocalContext
  recursiveCalls : Array RecCallTemplate
  targetTypeIdx : Nat
  targetIndices : Array Expr
  minor : Expr
  deriving Inhabited

structure RecInfo where
  motive : Expr
  minors : Array Expr
  indices : Array Expr
  major : Expr
  ruleTemplates : Array RecRuleTemplate := #[]
  deriving Inhabited

structure InductiveStats where
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
  /-- The checking context: the local context seen by embedded typechecker runs.  It holds
  only the binders a run may need (parameters, indices and fields, never majors,
  motives, minors or induction hypotheses), so every checker fact is produced
  in the context in which its verification uses it.  The C++ kernel shows each
  call a larger context; the results agree because a checker run only
  consults free variables reachable from its inputs.  See section 3.2 of
  the design notes. -/
  checkLCtx : LocalContext := {}
  lparams : List Name
  /-- Universe parameters used by embedded typechecker calls.  Inductive
  declarations normally use `lparams`; generated large-elimination recursors
  temporarily prepend their fresh result-universe parameter. -/
  typeCheckerLParams : Option (List Name) := none
  ngen : NameGenerator := { namePrefix := `_ind_fresh }
  safety : DefinitionSafety
  allowPrimitive : Bool
  fuel : FuelConfig := {}

abbrev M := ReaderT Context <| Except Exception

instance : MonadLocalNameGenerator M where
  withFreshId f c := f c.ngen.curr { c with ngen := c.ngen.next }

instance (priority := low) : MonadLift TypeChecker.M M where
  monadLift x c := x.run c.env c.safety c.checkLCtx
    (c.typeCheckerLParams.getD c.lparams) (fuel := c.fuel)

instance (priority := low+1) : MonadWithReaderOf LocalContext M where
  withReader f x := withReader (fun c => { c with lctx := f c.lctx }) x

instance : MonadLCtx M where
  getLCtx := return (← read).lctx

@[inline] def withEnv (env : Environment) (x : M α) : M α :=
  withReader (fun c => { c with env }) x

/-- Run embedded typechecker calls under the universe parameters of a
generated recursor while preserving every other inductive-checker reader
field. -/
@[inline] def withTypeCheckerLParams (lparams : List Name) (x : M α) : M α :=
  withReader (fun c => { c with typeCheckerLParams := some lparams }) x

def getType (fvar : Expr) : M Expr :=
  return ((← getLCtx).get! fvar.fvarId!).type

/-- Run `x` with embedded typechecker calls seeing exactly `lctx`. -/
@[inline] def withCheckLCtx (lctx : LocalContext) (x : M α) : M α :=
  withReader (fun c => { c with checkLCtx := lctx }) x

/-- Open a binder in both the main context and the checker context. -/
@[inline] def withCheckedLocalDecl (name : Name) (bi : BinderInfo) (ty : Expr)
    (k : Expr → M α) : M α :=
  withFreshId fun id =>
    withReader (fun c => { c with
      lctx := c.lctx.mkLocalDecl ⟨id⟩ name ty bi
      checkLCtx := c.checkLCtx.mkLocalDecl ⟨id⟩ name ty bi }) <| k <| .fvar ⟨id⟩

/-- Open a binder in the main context and, in the checker context, on top of
`base` (which replaces the current checker context). -/
@[inline] def withCheckedLocalDeclOn (base : LocalContext) (name : Name)
    (bi : BinderInfo) (ty : Expr) (k : Expr → M α) : M α :=
  withFreshId fun id =>
    withReader (fun c => { c with
      lctx := c.lctx.mkLocalDecl ⟨id⟩ name ty bi
      checkLCtx := base.mkLocalDecl ⟨id⟩ name ty bi }) <| k <| .fvar ⟨id⟩

/-- `withCheckedLocalDecl` on the unannotated domain. A type-annotation
wrapper is stripped only if the current environment declares it as the prelude's
definition (`Kernel.Environment.isTypeAnnotationWrapper`); otherwise the domain is kept
literally. -/
@[inline] def withUnannotatedCheckedLocalDecl (name : Name) (bi : BinderInfo) (dom : Expr)
    (k : Expr → M α) : M α := fun c =>
  withCheckedLocalDecl name bi (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper)
    k c

/-- `withCheckedLocalDeclOn` on the unannotated domain. -/
@[inline] def withUnannotatedCheckedLocalDeclOn (base : LocalContext) (name : Name)
    (bi : BinderInfo) (dom : Expr) (k : Expr → M α) : M α := fun c =>
  withCheckedLocalDeclOn base name bi
    (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) k c

/-- `withLocalDecl` on the unannotated domain. -/
@[inline] def withUnannotatedLocalDecl (name : Name) (bi : BinderInfo) (dom : Expr)
    (k : Expr → M α) : M α := fun c =>
  withLocalDecl name bi (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) k c

/-- Rebuild a local context from the declarations of `lctx` for `fvars`, in
order.  Free variables without a declaration are skipped. -/
def _root_.Lean.LocalContext.restrictTo (lctx : LocalContext) (fvars : List FVarId) :
    LocalContext :=
  fvars.foldl (init := {}) fun acc fv =>
    match lctx.find? fv with
    | some (.cdecl _ fv name type bi kind) => acc.mkLocalDecl fv name type bi kind
    | some (.ldecl _ fv name type value nonDep kind) =>
      acc.mkLetDecl fv name type value nonDep kind
    | none => acc

/-- The checker context holding exactly the first `n` parameters. -/
def paramCheckLCtx (stats : InductiveStats) (n : Nat) : M LocalContext :=
  return (← getLCtx).restrictTo ((stats.params.toList.take n).map (·.fvarId!))

def checkClosedType (name : Name) (type : Expr) : M Expr := do
  let env := (← read).env
  env.checkNoMVarNoFVar name type
  -- runs in the checking context (section 3.2 of the design notes)
  withCheckLCtx {} (checkType type)

namespace checkInductiveTypes

def loopType (nparams : Nat) (stats : InductiveStats) (type : Expr)
    (i nindices fuel : Nat) (k : Expr → InductiveStats → Nat → M α) : M α :=
  match fuel with
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := type then
      if i < nparams then
        if stats.indConsts.isEmpty then
          -- runs in the checking context (section 3.2 of the design notes)
          withUnannotatedCheckedLocalDecl name bi dom fun param => do
            let stats := { stats with params := stats.params.push param }
            let type := body.instantiate1 param
            loopType nparams stats (← whnf type) (i + 1) nindices fuel k
        else
          let param := stats.params[i]!
          -- runs in the checking context (section 3.2 of the design notes)
          let paramTy ← getType param
          unless ← withCheckLCtx (← paramCheckLCtx stats i) (isDefEq dom paramTy) do
            throw <| .other "parameters of all inductive datatypes must match"
          let type := body.instantiate1 param
          let type ← withCheckLCtx (← paramCheckLCtx stats (i + 1)) (whnf type)
          loopType nparams stats type (i + 1) nindices fuel k
      else
        -- runs in the checking context (section 3.2 of the design notes)
        withUnannotatedCheckedLocalDecl name bi dom fun arg => do
          let type := body.instantiate1 arg
          loopType nparams stats (← whnf type) i (nindices + 1) fuel k
    else
      if i != nparams then
        throw <| .other "number of parameters mismatch in inductive datatype declaration"
      k type stats nindices

def loopInd (nparams : Nat) (indTypes : Array InductiveType)
    (dIdx : Nat) (stats : InductiveStats) (k : InductiveStats → M α) : M α := do
  if _h : dIdx < indTypes.size then
    let indType := indTypes[dIdx]
    let type := indType.type
    _ ← checkClosedType indType.name type
    let fuel := (← readThe Context).fuel.inductiveFuel
    -- runs in the checking context (section 3.2 of the design notes)
    -- The closed header is normalized in the empty context, and the telescope
    -- is opened on top of the parameters (none yet for the first family).
    let type ← withCheckLCtx {} (whnf type)
    withCheckLCtx (← paramCheckLCtx stats stats.params.size) do
    loopType nparams stats type 0 0 fuel fun type stats nindices => show M α from do
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
    loopInd nparams indTypes (dIdx + 1) stats k
  else
    k <|
      assert! stats.levels.length == (← read).lparams.length
      assert! stats.nindices.size == indTypes.size
      assert! stats.indConsts.size == indTypes.size
      assert! stats.params.size == nparams
      stats
termination_by indTypes.size - dIdx

end checkInductiveTypes

def checkInductiveTypes
    (nparams : Nat) (indTypes : Array InductiveType)
    (k : InductiveStats → M α) : M α := do
  checkInductiveTypes.loopInd nparams indTypes 0
    { (default : InductiveStats) with levels := (← read).lparams.map .param } k

def hasIndOcc (indConsts : Array Expr) (t : Expr) : Bool :=
  t.findAny fun
    | .const e _ => indConsts.any fun I => I.constName! == e
    | _ => false

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

/-- The `InductiveVal` entries installed for the families of the mutual block. A named
function, so that the verification can relate these kernel entries, with their metadata, to
the independently translated source headers. -/
def inductiveTypeInfos (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (lparams : List Name) : Array InductiveVal :=
  let all := indTypes.map (·.name) |>.toList
  indTypes.zipWith (bs := stats.nindices) fun indType numIndices =>
    { indType with
      numParams, numIndices, all, numNested, isUnsafe
      levelParams := lparams
      ctors := indType.ctors.map (·.name)
      isRec := isRec indTypes stats.indConsts
      isReflexive := isReflexive indTypes stats.indConsts }

/-- Public name for the private kernel environment insertion `Kernel.Environment.add` used
by the inductive checker, so that the verification can state and prove how it changes
lookups. -/
def addConstant (env : Environment) (info : ConstantInfo) : Environment :=
  env.add info

def declareInductiveTypeInfos (allowPrimitive : Bool) :
    List InductiveVal → Environment → Except Exception Environment
  | [], env => pure env
  | info :: infos, env => do
    env.checkName info.name allowPrimitive
    declareInductiveTypeInfos allowPrimitive infos
      (addConstant env (.inductInfo info))

def declareInductiveTypes (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool) : M Environment :=
  fun c =>
  let infos := inductiveTypeInfos stats numParams indTypes numNested
    isUnsafe c.lparams
  declareInductiveTypeInfos c.allowPrimitive infos.toList c.env

def isValidIndAppIdx (stats : InductiveStats) (t : Expr) (i : Nat) : Bool :=
  t.withApp fun I args => Id.run do
  unless I == stats.indConsts[i]! && args.size == stats.params.size + stats.nindices[i]! do
    return false
  unless stats.params == args.extract 0 stats.params.size do
    return false
  unless (args.extract stats.params.size args.size).all fun arg =>
      !hasIndOcc stats.indConsts arg do
    return false
  true

def isValidIndAppFrom? (stats : InductiveStats) (t : Expr) (start : Nat) :
    Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    if isValidIndAppIdx stats t start then some start
    else isValidIndAppFrom? stats t (start + 1) fuel

def isValidIndApp? (stats : InductiveStats) (t : Expr) : Option Nat :=
  isValidIndAppFrom? stats t 0 stats.indConsts.size

def isRecArg (stats : InductiveStats) (t : Expr) : M (Option Nat) := do
  loop t (← readThe Context).fuel.inductiveFuel
where
  loop t
  | 0 => throw .deepRecursion
  | fuel+1 => do
    let t ← whnf t
    let .forallE name dom body bi := t | return isValidIndApp? stats t
    -- runs in the checking context (section 3.2 of the design notes)
    withUnannotatedCheckedLocalDecl name bi dom fun arg => do
    loop (body.instantiate1 arg) fuel

/-- One step of the positivity check on a field type in weak head normal form. The result
records whether the field is recursive: `false` when the type does not mention the families
being declared, `true` when it is a telescope over family-free domains ending in a valid
application of one of them. -/
def checkPositivityStep (stats : InductiveStats) (t : Expr)
    (ctor : Name) (idx : Nat) (recur : Expr → M Bool) : M Bool := do
  if !hasIndOcc stats.indConsts t then return false
  if let .forallE name dom body bi := t then
    if hasIndOcc stats.indConsts dom then
      throw <| .other s!"arg #{idx + 1} of '{ctor}' \
        has a non positive occurrence of the datatypes being declared"
    -- runs in the checking context (section 3.2 of the design notes)
    withUnannotatedCheckedLocalDecl name bi dom fun arg => do
      recur (body.instantiate1 arg)
  else if let none := isValidIndApp? stats t then
    throw <| .other s!"arg #{idx + 1} of '{ctor}' \
      has a non valid occurrence of the datatypes being declared"
  else
    return true

/-- Check that a field type is strictly positive and report whether it is recursive (see
`checkPositivityStep`). -/
def checkPositivity (stats : InductiveStats) (t : Expr) (ctor : Name) (idx : Nat) :
    M Bool := do loop t (← readThe Context).fuel.inductiveFuel where
  loop t
  | 0 => throw .deepRecursion
  | fuel+1 => do
    let t ← whnf t
    checkPositivityStep stats t ctor idx fun body => loop body fuel

namespace checkConstructors

/-- Check one constructor telescope. The result lists, for each field in order, whether the
positivity check found it recursive (always `false` for an unsafe declaration, whose fields
are not checked for positivity). -/
def loopCtor (stats : InductiveStats) (isUnsafe : Bool) (ctor : Name)
    (targetIdx : Nat) (t : Expr) (i fuel : Nat) : M (List Bool) :=
  match fuel with
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := t then
      if let some param := stats.params[i]? then
        -- runs in the checking context (section 3.2 of the design notes)
        let paramTy ← getType param
        unless ← withCheckLCtx (← paramCheckLCtx stats i) (isDefEq dom paramTy) do
          throw <| .other
            s!"arg #{i + 1} of '{ctor}' does not match inductive datatype parameters"
        loopCtor stats isUnsafe ctor targetIdx
          (body.instantiate1 param) (i + 1) fuel
      else
        let s ← ensureType dom
        unless stats.resultLevel.isAlwaysZero || stats.resultLevel.geq' s.sortLevel! do
          throw <| .other s!"universe level of type_of(arg #{i + 1}) of '{ctor}' \
            is too big for the corresponding inductive datatype"
        let recursive ← if !isUnsafe then checkPositivity stats dom ctor i else pure false
        -- runs in the checking context (section 3.2 of the design notes)
        withUnannotatedCheckedLocalDecl name bi dom fun arg => do
          return recursive :: (← loopCtor stats isUnsafe ctor targetIdx
            (body.instantiate1 arg) (i + 1) fuel)
    else if !isValidIndAppIdx stats t targetIdx then
      throw <| .other s!"invalid return type for '{ctor}'"
    else
      return []

end checkConstructors

namespace checkConstructors

/-- Check the constructors of one family, from position `ctorIdx`, returning their field
classifications (`loopCtor`) in order. -/
def loopCtors (stats : InductiveStats) (isUnsafe : Bool)
    (targetIdx : Nat) (ctors : List Constructor) (ctorIdx : Nat)
    (foundCtors : NameSet) : M (List (List Bool)) := do
  if h : ctorIdx < ctors.length then
    let ctor := ctors[ctorIdx]
    let n := ctor.name
    if foundCtors.contains n then
      throw <| .other s!"duplicate constructor name '{n}'"
    let foundCtors := foundCtors.insert n
    let t := ctor.type
    _ ← checkClosedType n t
    let fields ← checkConstructors.loopCtor stats isUnsafe n targetIdx t 0
      (← readThe Context).fuel.inductiveFuel
    return fields :: (← loopCtors stats isUnsafe targetIdx ctors (ctorIdx + 1) foundCtors)
  else
    pure []
termination_by ctors.length - ctorIdx

/-- Check the constructors of the families from `targetIdx`, returning their field
classifications, family by family. -/
def loopTypes (indTypes : Array InductiveType)
    (stats : InductiveStats) (isUnsafe : Bool) (targetIdx : Nat) :
    M (List (List (List Bool))) := do
  if h : targetIdx < indTypes.size then
    let fields ← loopCtors stats isUnsafe targetIdx indTypes[targetIdx].ctors 0 {}
    return fields :: (← loopTypes indTypes stats isUnsafe (targetIdx + 1))
  else
    pure []
termination_by indTypes.size - targetIdx

end checkConstructors

/-- Check every constructor of the block. The result lists, family by family and
constructor by constructor, whether the positivity check found each field recursive; the
recursor construction is required to agree with it (`checkRecursiveFields`). -/
def checkConstructors (indTypes : Array InductiveType)
    (stats : InductiveStats) (isUnsafe : Bool) : M (List (List (List Bool))) := do
  let _ ← getEnv
  -- runs in the checking context (section 3.2 of the design notes)
  withCheckLCtx (← paramCheckLCtx stats stats.params.size) do
  checkConstructors.loopTypes indTypes stats isUnsafe 0

/-- Number of binders in a constructor's complete source telescope. A named function, so
that the verification of projections can read the installed `numFields` entry without
repeating the traversal. -/
def constructorArity : Expr → Nat
  | .forallE _ _ body _ => constructorArity body + 1
  | _ => 0

/-- The `ConstructorVal` entry installed for one constructor. A named function, so that the
verification can keep the exact entry, not only its translated type. -/
def constructorInfo (stats : InductiveStats) (lparams : List Name)
    (isUnsafe : Bool) (indType : InductiveType) (cidx : Nat)
    (ctor : Constructor) : ConstructorVal :=
  let type := ctor.type
  let arity := constructorArity type
  {
    type, cidx, isUnsafe
    levelParams := lparams
    name := ctor.name
    induct := indType.name
    numParams := stats.params.size
    numFields := assert! arity ≥ stats.params.size
      arity - stats.params.size
  }

@[simp] theorem constructorInfo_numFields
    (stats : InductiveStats) (lparams : List Name)
    (isUnsafe : Bool) (indType : InductiveType) (cidx : Nat)
    (ctor : Constructor) :
    (constructorInfo stats lparams isUnsafe indType cidx ctor).numFields =
      constructorArity ctor.type - stats.params.size := by
  simp [constructorInfo]
  omega

def declareConstructors (stats : InductiveStats)
    (indTypes : Array InductiveType) (isUnsafe : Bool) : M Environment :=
  fun c => indTypes.foldlM (init := c.env) fun env indType => do
    let (_, env) ← indType.ctors.foldlM (init := (0, env)) fun (cidx, env) ctor => do
      env.checkName ctor.name c.allowPrimitive
      pure (cidx + 1, addConstant env <| .ctorInfo
        (constructorInfo stats c.lparams isUnsafe indType cidx ctor))
    pure env

/-- Return true if recursor can map into any universe -/
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
        -- runs in the checking context (section 3.2 of the design notes)
        withUnannotatedCheckedLocalDecl name bi dom fun arg => do
          let mut toCheck := toCheck
          if i ≥ stats.params.size then
            if !(← ensureType dom).sortLevel!.isAlwaysZero then
              toCheck := toCheck.push arg
          loop (body.instantiate1 arg) (i + 1) toCheck fuel
      else
        return toCheck.all type.getAppArgs.contains
    -- runs in the checking context (section 3.2 of the design notes)
    withCheckLCtx {} (loop ctor.type 0 #[] (← readThe Context).fuel.inductiveFuel)
  | _ => return false

def getElimLevel (stats : InductiveStats) (indTypes : Array InductiveType) :
    M Level := do
  unless ← isLargeEliminator stats indTypes do return .zero
  let {lparams, ..} ← read
  let rec loop u i
    | 0 => throw <| .other "failed to select a fresh recursor universe parameter"
    | fuel + 1 => do
      unless lparams.contains u do return .param u
      loop ((`u).appendIndexAfter i) (i + 1) fuel
  loop `u 1 (lparams.length + 1)

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
        -- runs in the checking context (section 3.2 of the design notes)
        let type ← withCheckLCtx (← paramCheckLCtx stats (i + 1))
          (whnf <| body.instantiate1 stats.params[i]!)
        loopArgs1 stats type (i + 1) indices fuel k
      else
        -- runs in the checking context (section 3.2 of the design notes)
        withUnannotatedCheckedLocalDecl name bi dom fun arg => do
        loopArgs1 stats (← whnf <| body.instantiate1 arg) i (indices.push arg) fuel k
    else
      if i < stats.params.size then
        throw <| .other "recursor parameter arity does not match checked inductive header"
      else
        k indices

variable (stats : InductiveStats) (indTypes : Array InductiveType) (elimLevel : Level) in
def loopInd1 (dIdx : Nat) (recInfos : Array RecInfo) (k : Array RecInfo → M α) : M α := do
  if _h : dIdx < indTypes.size then
    let ctx ← readThe Context
    -- runs in the checking context (section 3.2 of the design notes)
    let type ← withCheckLCtx {} (whnf indTypes[dIdx].type)
    withCheckLCtx (← paramCheckLCtx stats stats.params.size) do
    loopArgs1 stats type 0 #[] ctx.fuel.inductiveFuel fun indices => do
    unless indices.size == stats.nindices[dIdx]! do
      throw <| .other "recursor index arity does not match checked inductive header"
    let tTy := mkAppN (mkAppN stats.indConsts[dIdx]! stats.params) indices
    withUnannotatedLocalDecl `t .default tTy fun major => do
    let lctx ← getLCtx
    let motiveTy := lctx.mkForall indices <| lctx.mkForall #[major] <| .sort elimLevel
    let name := if indTypes.size > 1 then (`motive).appendIndexAfter (dIdx+1) else `motive
    withUnannotatedLocalDecl name .default motiveTy fun motive => do
    loopInd1 (dIdx + 1) (recInfos.push {
      motive, minors := #[], indices, major, ruleTemplates := #[] }) k
  else
    k recInfos
termination_by indTypes.size - dIdx

variable (stats : InductiveStats) in
def loopCtorArgs (t : Expr) (k : Expr → Array Expr → Array Expr → M α) : M α := do
  loop t 0 #[] #[] (← readThe Context).fuel.inductiveFuel
where
  loop t i bu u
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := t then
      if let some param := stats.params[i]? then
        loop (body.instantiate1 param) (i + 1) bu u fuel
      else
        -- runs in the checking context (section 3.2 of the design notes)
        -- The field is checked on top of the parameters and earlier fields.
        let fieldCheck := (← getLCtx).restrictTo
          ((stats.params ++ bu).toList.map (·.fvarId!))
        withUnannotatedCheckedLocalDeclOn fieldCheck name bi dom
          fun arg => do
        let bu := bu.push arg
        let u := if (← withCheckLCtx fieldCheck (isRecArg stats dom)).isSome then
          u.push arg else u
        loop (body.instantiate1 arg) (i + 1) bu u fuel
    else k t bu u

/-- The parameters and the constructor fields before the field `ui`. -/
def fieldsBefore (stats : InductiveStats) (fields : Array Expr) (ui : Expr) :
    Array Expr :=
  stats.params ++ fields.takeWhile (·.fvarId! != ui.fvarId!)

def loopUArgs (prior : Array Expr) (ui : Expr) (k : Expr → Array Expr → M α) : M α := do
  -- runs in the checking context (section 3.2 of the design notes)
  -- The recursive field's type is read off its declaration and normalized in
  -- the checker context of `prior`: the parameters and the fields before it.
  let uiTy ← getType ui
  let fieldCheck := (← getLCtx).restrictTo (prior.toList.map (·.fvarId!))
  withCheckLCtx fieldCheck do
  loop (← whnf uiTy) #[] (← readThe Context).fuel.inductiveFuel
where
  loop uiTy xs
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := uiTy then
      -- runs in the checking context (section 3.2 of the design notes)
      withUnannotatedCheckedLocalDecl name bi dom fun arg => do
      loop (← whnf <| body.instantiate1 arg) (xs.push arg) fuel
    else
      k uiTy xs

variable (stats : InductiveStats) (bu u : Array Expr) (recInfos : Array RecInfo) in
def loopUTemplates (i : Nat) (v : Array Expr)
    (calls : Array RecCallTemplate)
    (k : Array Expr → Array RecCallTemplate → M α) : M α := do
  if _h : i < u.size then
    let ui := u[i]
    let (viTy, call) ← loopUArgs (fieldsBefore stats bu ui) ui fun uiTy xs => do
      let some itIdx := isValidIndApp? stats uiTy
        | throw (.other
          "recursive constructor field lost its inductive result type")
      let itIndices := uiTy.getAppArgs[stats.params.size:]
      let lctx ← getLCtx
      -- The recursor head of the call is a placeholder for the loose variable just
      -- outside the `xs` binders: `mkLambda` does not shift loose bound variables, so
      -- it must be `.bvar xs.size` inside the body. `RecCallTemplate.instantiate`
      -- then lifts the recursor application under those binders; its free variables
      -- may reuse identifiers of `xs`, so it cannot be placed in the body before
      -- the abstraction.
      let viTy := lctx.mkForall xs <|
        .app (mkAppN recInfos[itIdx]!.motive itIndices) (mkAppN ui xs)
      return (viTy, ({
        major := ui
        args := xs
        lctx := lctx
        targetTypeIdx := itIdx
        targetIndices := itIndices
        template := lctx.mkLambda xs <|
          (mkAppN (.bvar xs.size) itIndices).app (mkAppN ui xs) } :
            RecCallTemplate))
    let vName := ((← getLCtx).get! ui.fvarId!).userName.appendAfter "_ih"
    withUnannotatedLocalDecl vName .default viTy fun vi => do
    loopUTemplates (i + 1) (v.push vi)
      (calls.push call) k
  else
    k v calls
termination_by u.size - i

variable (stats : InductiveStats) (indTypeName : Name) (dIdx : Nat) in
def loopCtors (recInfos : Array RecInfo)
    (ctors : List Constructor) (k : Array RecInfo → M α) : M α := match ctors with
  | ctor::ctors =>
    loopCtorArgs stats ctor.type fun t bu u => do
    let (itIdx, itIndices) := getIIndices stats t
    let introApp := mkAppN (mkAppN (.const ctor.name stats.levels) stats.params) bu
    let motiveApp := Expr.app (mkAppN recInfos[itIdx]!.motive itIndices) introApp
    loopUTemplates stats bu u recInfos 0 #[] #[] fun v calls => do
    let lctx ← getLCtx
    let minorTy := lctx.mkForall bu <| lctx.mkForall v motiveApp
    let minorName := ctor.name.replacePrefix indTypeName .anonymous
    withUnannotatedLocalDecl minorName .default minorTy fun minor => do
    let blueprint : RecRuleTemplate := {
      ctor := ctor.name
      fields := bu
      lctx := lctx
      recursiveCalls := calls
      targetTypeIdx := itIdx
      targetIndices := itIndices
      minor := minor }
    let recInfos := recInfos.modify dIdx fun s => {
      s with
      minors := s.minors.push minor
      ruleTemplates := s.ruleTemplates.push blueprint }
    loopCtors recInfos ctors k
  | [] => k recInfos

variable (stats : InductiveStats) (indTypes : Array InductiveType) in
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

def mkRecInfos (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (k : Array RecInfo → M α) : M α :=
  mkRecInfos.loopInd1 stats indTypes elimLevel 0 #[] fun recInfos =>
  mkRecInfos.loopInd2 stats indTypes 0 recInfos k

/-- The fields of a rule template that receive an induction hypothesis, in field order. -/
def RecRuleTemplate.recursiveMask (blueprint : RecRuleTemplate) : List Bool :=
  blueprint.fields.toList.map fun field =>
    blueprint.recursiveCalls.any fun call => call.major == field

/-- The minor pass decides which fields are recursive by normalizing each field type in the
recursor's checking context (`isRecArg`); the constructor phase decided it with the positivity
check, in the environment with the family headers (`checkConstructors`). For a safe
declaration the two must agree, so that a field gets an induction hypothesis exactly when its
strictly positive normal form ends in one of the families being declared. -/
def checkRecursiveFields (isUnsafe : Bool) (positivity : List (List (List Bool)))
    (recInfos : Array RecInfo) : M Unit := do
  unless isUnsafe do
    unless (recInfos.toList.map fun info =>
        info.ruleTemplates.toList.map (·.recursiveMask)) == positivity do
      throw <| .other "recursive constructor fields disagree with the positivity check"

def getRecLevels (elimLevel : Level) (levels : List Level) : List Level :=
  if elimLevel.isParam then elimLevel :: levels else levels

def getRecLevelParams (elimLevel : Level) (lparams : List Name) : List Name :=
  if let .param u := elimLevel then u :: lparams else lparams

def RecCallTemplate.instantiate (blueprint : RecCallTemplate)
    (indTypes : Array InductiveType) (stats : InductiveStats)
    (motives minors : Array Expr) (lvls : List Level) : Expr :=
  let value := .const (mkRecName indTypes[blueprint.targetTypeIdx]!.name) lvls
  let value := mkAppN (mkAppN (mkAppN value stats.params) motives) minors
  -- The template binds the field arguments over a loose placeholder
  -- (`.bvar args.size` inside the body, see `loopUTemplates`); instantiating it
  -- afterwards lifts `value` under those binders.
  blueprint.template.instantiate1 value

def RecRuleTemplate.instantiate (blueprint : RecRuleTemplate)
    (indTypes : Array InductiveType) (stats : InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (outerLCtx : LocalContext) : RecursorRule :=
  let recursiveValues := blueprint.recursiveCalls.map fun call =>
    call.instantiate indTypes stats motives minors lvls
  {
    ctor := blueprint.ctor
    nfields := blueprint.fields.size
    rhs := outerLCtx.mkLambda stats.params <| outerLCtx.mkLambda motives <|
      outerLCtx.mkLambda minors <| blueprint.lctx.mkLambda blueprint.fields <|
      mkAppN (mkAppN blueprint.minor blueprint.fields) recursiveValues
  }

/-- Build recursor rules from the rule templates recorded by `mkRecInfos` (fields and
higher-order recursive calls). This performs no second constructor traversal,
classification, inference, or WHNF. -/
def mkRecRulesFromTemplates (indTypes : Array InductiveType)
    (elimLevel : Level) (stats : InductiveStats) (recInfos : Array RecInfo)
    (dIdx : Nat) (motives minors : Array Expr) : M (List RecursorRule) := do
  let lctx ← getLCtx
  let lvls := getRecLevels elimLevel stats.levels
  return recInfos[dIdx]!.ruleTemplates.toList.map fun blueprint =>
    blueprint.instantiate indTypes stats motives minors lvls lctx

namespace declareRecursors

def recursorType (stats : InductiveStats)
    (recInfos : Array RecInfo) (lctx : LocalContext) (dIdx : Nat) : Expr :=
  lctx.mkForall stats.params <|
  lctx.mkForall (recInfos.map (·.motive)) <|
  lctx.mkForall (recInfos.flatMap (·.minors)) <|
  lctx.mkForall recInfos[dIdx]!.indices <|
  lctx.mkForall #[recInfos[dIdx]!.major] <|
  .app (mkAppN recInfos[dIdx]!.motive recInfos[dIdx]!.indices)
    recInfos[dIdx]!.major

def recursorInfo (stats : InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (recInfos : Array RecInfo) (numMinors numMotives : Nat)
    (all : List Name) (lctx : LocalContext) (k isUnsafe : Bool)
    (lparams : List Name) (dIdx : Nat)
    (rules : List RecursorRule) : RecursorVal where
  levelParams := getRecLevelParams elimLevel lparams
  type := (recursorType stats recInfos lctx dIdx).inferImplicit 1000 false
  numParams := stats.params.size
  numIndices := stats.nindices[dIdx]!
  name := mkRecName indTypes[dIdx]!.name
  all := all
  numMotives := numMotives
  numMinors := numMinors
  rules := rules
  k := k
  isUnsafe := isUnsafe

/-- Independently validate the fully closed generated recursor type before
installing its kernel metadata. The recursor may carry one fresh eliminator
universe, so this deliberately uses `info.levelParams` and an empty local
context rather than the surrounding declaration context. -/
def checkRecursorType (info : RecursorVal) : M Expr := fun c => do
  c.env.checkNoMVarNoFVar info.name info.type
  TypeChecker.M.run c.env c.safety {} info.levelParams c.fuel do
    let type ← TypeChecker.checkType info.type
    _ ← TypeChecker.ensureSort type info.type
    return type

def checkRecursorTypes (stats : InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (recInfos : Array RecInfo) (numMinors numMotives : Nat)
    (all : List Name) (lctx : LocalContext) (k isUnsafe : Bool)
    (lparams : List Name) (dIdx : Nat) : M Unit := do
  if h : dIdx < indTypes.size then
    let info := recursorInfo stats indTypes elimLevel recInfos numMinors
      numMotives all lctx k isUnsafe lparams dIdx []
    _ ← checkRecursorType info
    checkRecursorTypes stats indTypes elimLevel recInfos numMinors numMotives
      all lctx k isUnsafe lparams (dIdx + 1)
termination_by indTypes.size - dIdx

def loop (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (recInfos : Array RecInfo)
    (motives minors : Array Expr) (numMinors numMotives : Nat)
    (all : List Name) (lctx : LocalContext) (k isUnsafe : Bool)
    (lparams : List Name) (allowPrimitive : Bool)
    (dIdx : Nat) (env : Environment) : StateT Nat M Environment := do
  if h : dIdx < indTypes.size then
    let rules ← mkRecRulesFromTemplates indTypes elimLevel stats recInfos
      dIdx motives minors
    modify (· + indTypes[dIdx]!.ctors.length)
    let info := recursorInfo stats indTypes elimLevel recInfos numMinors
      numMotives all lctx k isUnsafe lparams dIdx rules
    let name := info.name
    env.checkName name allowPrimitive
    let env := addConstant env (.recInfo info)
    loop stats indTypes elimLevel recInfos motives minors numMinors
      numMotives all lctx k isUnsafe lparams allowPrimitive (dIdx + 1) env
  else
    pure env
termination_by indTypes.size - dIdx

end declareRecursors

def declareRecursors (stats : InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (recInfos : Array RecInfo) (k : Bool)
    (declarationLParams : List Name) : M Environment := do
  let motives := recInfos.map (·.motive)
  let minors := recInfos.flatMap (·.minors)
  let numMinors := minors.size
  let numMotives := motives.size
  let all := indTypes.map (·.name) |>.toList
  let lctx ← getLCtx
  let {safety, ..} ← read
  let isUnsafe := safety != .safe
  AddInductive.declareRecursors.checkRecursorTypes stats indTypes elimLevel
    recInfos numMinors numMotives all lctx k isUnsafe declarationLParams 0
  StateT.run' (s := 0) do
  let env ← getEnv
  let {allowPrimitive, ..} ← read
  declareRecursors.loop stats indTypes elimLevel recInfos motives minors
    numMinors numMotives all lctx k isUnsafe declarationLParams
      allowPrimitive 0 env

/-- Declare the families, check the constructors in the environment with the family
headers, and declare the constructors. Returns the constructor environment and the field
classifications of the constructor check. -/
def constructorPhase (stats : InductiveStats) (nparams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool) :
    M (Environment × List (List (List Bool))) :=
  declareInductiveTypes stats nparams indTypes numNested isUnsafe >>= fun headerEnv =>
    withEnv headerEnv do
      let positivity ← checkConstructors indTypes stats isUnsafe
      return (← declareConstructors stats indTypes isUnsafe, positivity)

def runWithStats (stats : InductiveStats) (nparams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat)
    (isUnsafe : Bool) : M Environment := do
  let (ctorEnv, positivity) ← constructorPhase stats nparams indTypes numNested isUnsafe
  fun c =>
    (getElimLevel stats indTypes >>= fun elimLevel =>
      withTypeCheckerLParams (getRecLevelParams elimLevel c.lparams) do
        let k ← isKTarget stats indTypes
        mkRecInfos stats indTypes elimLevel fun recInfos => do
          checkRecursiveFields isUnsafe positivity recInfos
          declareRecursors stats indTypes elimLevel recInfos k c.lparams)
      { c with env := ctorEnv }

def run (nparams : Nat) (types : List InductiveType) (numNested : Nat) :
    M Environment := fun c => do
  let isUnsafe := c.safety != .safe
  let indTypes := types.toArray
  Environment.checkDuplicatedUnivParams c.lparams
  checkInductiveTypes nparams indTypes (fun stats =>
    runWithStats stats nparams indTypes numNested isUnsafe) c

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

def restoreNestedNode (r : Result) (env' : Environment) (As : Array Expr)
    (auxRec : NameMap Name) (t : Expr) : Option Expr := do
  if let .const c ls := t then
    if let some recName := auxRec.find? c then
      return .const recName ls
  let .const c _ := t.getAppFn | none
  if let some nested := r.aux2nested.find? c then
    let args := t.getAppArgs
    assert! args.size ≥ r.nparams
    return mkAppRange ((nested.abstract r.params).instantiateRev As)
      r.nparams args.size args
  let (nested, auxI_name) ← r.getNestedIfAuxCtor env' c
  let args := t.getAppArgs
  assert! args.size ≥ r.nparams
  let nested' := (nested.abstract r.params).instantiateRev As
  nested'.withApp fun I I_args => do
  let .const I_c I_ls := I | unreachable!
  let c' := .const (c.replacePrefix auxI_name I_c) I_ls
  return mkAppRange (mkAppN c' I_args) r.nparams args.size args

def openRestoreParams : Nat → LocalContext → Array Expr → Expr →
    StateM NameGenerator (LocalContext × Array Expr × Expr)
  | 0, lctx, As, e => pure (lctx, As, e)
  | n + 1, lctx, As, e => do
    let (name, dom, body, bi) := match e with
      | .forallE name dom body bi | .lam name dom body bi =>
        (name, dom, body, bi)
      | _ => unreachable!
    let id := ⟨← mkFreshId⟩
    let lctx := lctx.mkLocalDecl id name dom bi
    let arg := .fvar id
    openRestoreParams n lctx (As.push arg) (body.instantiate1 arg)

def restoreNested (r : Result) (env' : Environment) (e : Expr)
    (auxRec : NameMap Name := {}) : Expr :=
  let pi := e.isForall
  let ((lctx, As, e), _) := openRestoreParams r.nparams {} #[] e
    { namePrefix := `_nested_fresh }
  let e := e.replace (r.restoreNestedNode env' As auxRec)
  if pi then lctx.mkForall As e else lctx.mkLambda As e

def restoreRule (r : Result) (env' : Environment) (auxRec : NameMap Name)
    (oldRecName newRecName : Name) (rule : RecursorRule) : RecursorRule :=
  { rule with
    ctor := if newRecName == oldRecName then rule.ctor
      else r.restoreCtorName env' rule.ctor
    rhs := r.restoreNested env' rule.rhs auxRec }

def restoreRecursor (r : Result) (env' : Environment)
    (auxRec : NameMap Name) (allIndNames : List Name)
    (oldRecName newRecName : Name) (recInfo : RecursorVal) : RecursorVal :=
  { recInfo with
    name := newRecName
    type := r.restoreNested env' recInfo.type auxRec
    all := allIndNames
    rules := recInfo.rules.map
      (r.restoreRule env' auxRec oldRecName newRecName) }

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

def findUniqueName (env : Environment) (n : Name) (i : Nat) :
    Nat → Except Exception (Name × Nat)
  | 0 => throw <| .other "failed to select a fresh nested-inductive name"
  | fuel + 1 =>
    let r := Name.mkNum n i
    if env.contains r then
      findUniqueName env n (i + 1) fuel
    else
      pure (r, i + 1)

def mkUniqueName (n : Name) : M Name := fun env state => do
  let (name, nextIdx) ←
    findUniqueName env n state.nextIdx (env.constants.toList.length + 1)
  return (name, { state with nextIdx })

def illFormed : Exception :=
  .other "invalid nested inductive datatype, ill-formed declaration"

def replaceParamsCore (params : Array Expr) (e : Expr) (As : Array Expr) :
    Except Exception Expr := do
  assert! As.size == params.size
  return (e.abstract As).instantiateRev params

def replaceParams (params : Array Expr) (e : Expr) (As : Array Expr) : M Expr :=
  fun _ state => (fun result => (result, state)) <$> replaceParamsCore params e As

/-- IF `e` is of the form `I Ds is` where
  1) `I` is a nested inductive datatype (i.e., a previously declared inductive datatype),
  2) the parametric arguments `Ds` do not contain loose bound variables, and do contain inductive datatypes in `m_new_types`
THEN return the `inductive_val` in the `constant_info` associated with `I`.
Otherwise, return none. -/
def mentionsQueuedFamily (newTypes : Array InductiveType) (e : Expr) : Bool :=
  e.findAny fun
    | .const t _ => newTypes.any fun ty => t == ty.name
    | _ => false

def nestedParamFlags (newTypes : Array InductiveType) (args : Array Expr) :
    Nat → Bool × Bool
  | 0 => (false, false)
  | n + 1 =>
    let flags := nestedParamFlags newTypes args n
    (flags.1 || mentionsQueuedFamily newTypes args[n]!,
      flags.2 || args[n]!.hasLooseBVars)

def isNestedInductiveAppConst? (e : Expr) (fn : Name) : M (Option InductiveVal) :=
    fun env state => do
  let some (.inductInfo ci) := env.find? fn | return (none, state)
  let args := e.getAppArgs
  if ci.numParams > args.size then return (none, state)
  let flags := nestedParamFlags state.newTypes args ci.numParams
  if !flags.1 then return (none, state)
  if flags.2 then
    throw <| .other s!"invalid nested inductive datatype '{fn}', \
      nested inductive datatypes parameters cannot contain local variables."
  return (some ci, state)

def isNestedInductiveApp? (e : Expr) : M (Option InductiveVal) := do
  if !e.isApp then return none
  let .const fn _ := e.getAppFn | return none
  isNestedInductiveAppConst? e fn

def instantiateForallParams (e : Expr) (hi : Nat) (params : Array Expr) :
    Except Exception Expr := do
  let mut e := e
  for _ in [:hi] do
    let .forallE _ _ body _ := e | throw illFormed
    e := body
  return e.instantiateRevRange 0 hi params

def findCachedAux? (nestedAux : Array (Expr × Name)) (nested : Expr) :
    Option Name :=
  nestedAux.findSome? fun (e, n) =>
    if e == nested then some n else none

structure AuxiliaryData where
  nested : Expr
  type : InductiveType

def buildAuxiliary (env : Environment) (lctx : LocalContext)
    (params As : Array Expr) (I_lvls : List Level) (I_nparams : Nat)
    (args : Array Expr) (J_name auxJ_name : Name) : Except Exception AuxiliaryData := do
  let info ← env.get J_name
  let J_info := match info with
    | .inductInfo J_info => J_info
    | _ => unreachable!
  let J := .const J_name I_lvls
  let JAs := mkAppRange J 0 I_nparams args
  let auxJ_type := J_info.type.instantiateLevelParams J_info.levelParams I_lvls
  let auxJ_type := lctx.mkForall As <|
    ← instantiateForallParams auxJ_type I_nparams args
  let JAs' ← replaceParamsCore params JAs As
  let auxJ_ctors ← J_info.ctors.mapM fun J_ctor_name => do
    let J_ctor_info ← env.get J_ctor_name
    -- auxJ_cnstr_type still has references to `J`, this will be fixed later when we process it.
    let auxJ_ctor_name := J_ctor_name.replacePrefix J_name auxJ_name
    let auxJ_ctor_type := J_ctor_info.type.instantiateLevelParams
      J_ctor_info.levelParams I_lvls
    let auxJ_ctor_type ← instantiateForallParams auxJ_ctor_type I_nparams args
    return { name := auxJ_ctor_name, type := lctx.mkForall As auxJ_ctor_type }
  return {
    nested := JAs'
    type := { name := auxJ_name, type := auxJ_type, ctors := auxJ_ctors } }

def generateAuxiliary (lctx : LocalContext) (params As : Array Expr)
    (I_name : Name) (I_lvls : List Level) (I_nparams : Nat)
    (args : Array Expr) (J_name : Name) : M (Option Expr) := do
  let env ← read
  let auxJ_name ← mkUniqueName `_nested
  let data ← buildAuxiliary env lctx params As I_lvls I_nparams args J_name auxJ_name
  modify fun st => { st with nestedAux := st.nestedAux.push (data.nested, auxJ_name) }
  let result ← if J_name == I_name then
    pure <| some <| mkAppRange
      (mkAppN (.const auxJ_name (← get).lvls) As) I_nparams args.size args
  else
    pure none
  modify fun st => { st with newTypes := st.newTypes.push data.type }
  return result

def generateAuxiliaries (lctx : LocalContext) (params As : Array Expr)
    (I_name : Name) (I_lvls : List Level) (I_nparams : Nat)
    (args : Array Expr) (I_val : InductiveVal) : M (Option Expr) :=
  loop none I_val.all
where
  loop (result : Option Expr) : List Name → M (Option Expr)
    | [] => do
      assert! result.isSome
      return result
    | J_name :: names => do
      let found ← generateAuxiliary lctx params As I_name I_lvls I_nparams args J_name
      loop (found.or result) names

def replaceRecognizedNested (lctx : LocalContext) (params As : Array Expr)
    (fn : Expr) (args : Array Expr) (I_val : InductiveVal) : M (Option Expr) := do
  let .const I_name I_lvls := fn | unreachable!
  let I_nparams := I_val.numParams
  assert! I_nparams ≤ args.size
  let IAs := mkAppRange fn 0 I_nparams args -- `I As`
  let Iparams ← replaceParams params IAs As
  let st ← get
  if let some auxI_name := findCachedAux? st.nestedAux Iparams then
    return mkAppRange (mkAppN (.const auxI_name st.lvls) As) I_nparams args.size args
  generateAuxiliaries lctx params As I_name I_lvls I_nparams args I_val

/-- If `e` is a nested occurrence `I Ds is`, return `Iaux As is` -/
def replaceIfNested (lctx : LocalContext) (params : Array Expr) (As : Array Expr) (e : Expr) :
    M (Option Expr) := do
  let some I_val ← isNestedInductiveApp? e | return none
  e.withApp fun fn args =>
    replaceRecognizedNested lctx params As fn args I_val

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

def lowerConstructor (params : Array Expr) (nparams : Nat)
    (ctor : Constructor) : M Constructor := do
  withParams ctor.type nparams fun lctx ctorType As => do
  assert! As.size == nparams
  return { ctor with
    type := lctx.mkForall As (← replaceAllNested lctx params As ctorType) }

def lowerInductive (params : Array Expr) (nparams : Nat)
    (indType : InductiveType) : M InductiveType := do
  let ctors ← indType.ctors.mapM (lowerConstructor params nparams)
  return { indType with ctors }

def lowerNext (params : Array Expr) (nparams i : Nat) :
    M (Option InductiveType) := do
  let s ← get
  if _h : i < s.newTypes.size then
    let source := s.newTypes[i]
    let target ← lowerInductive params nparams source
    modify fun s => { s with newTypes := s.newTypes.set! i target }
    return some source
  else
    return none

def run (fuel nparams : Nat) (types : List InductiveType) : M Result := do
  let I :: _ := types
    | throw <| .other s!"invalid empty (mutual) inductive datatype declaration, \
        it must contain at least one inductive type."
  withParams I.type nparams fun lctx _ params => do
  let rec loop i
  | 0 => throw <| .other "deep recursion: ElimNestedInductive.run.loop"
  | fuel+1 => do
    match ← lowerNext params nparams i with
    | some _ => loop (i+1) fuel
    | none =>
      let s ← get
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
  if e.findAny fun
      | .const c _ => (`_nested).isPrefixOf c
      | .proj s _ _ => (`_nested).isPrefixOf s
      | _ => false then
    throw <| .other s!"invalid declaration '{n}', it uses the reserved prefix '_nested'"

def checkConstructorSources (env : Environment) :
    List Constructor → Except Exception Unit
  | [] => pure ()
  | ctor :: ctors => do
    env.checkNoMVarNoFVar ctor.name ctor.type
    checkNoNestedAux ctor.name ctor.type
    checkConstructorSources env ctors

def checkInductiveSources (env : Environment) :
    List InductiveType → Except Exception Unit
  | [] => pure ()
  | indType :: types => do
    env.checkNoMVarNoFVar indType.name indType.type
    checkConstructorSources env indType.ctors
    checkInductiveSources env types

/-- Restore and install one recursor emitted for the lowered nested block. -/
def restoreRecursorDecl (res : ElimNestedInductive.Result)
    (loweredEnv : Environment) (recNameMap : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool) (recName : Name) :
    StateT Environment (Except Exception) Unit := fun sourceEnv =>
  let newRecName := recNameMap.getD recName recName
  match loweredEnv.find? recName with
  | some (.recInfo recInfo) => do
    sourceEnv.checkName newRecName allowPrimitive
    return ((), sourceEnv.add <| .recInfo <|
      res.restoreRecursor loweredEnv recNameMap allIndNames recName newRecName
        recInfo)
  | _ => .error <| .other s!"missing lowered recursor '{recName}'"

/-- Restore and install one constructor emitted for the lowered nested block. -/
def restoreConstructorDecl (res : ElimNestedInductive.Result)
    (loweredEnv : Environment) (allowPrimitive : Bool) (ctorName : Name) :
    StateT Environment (Except Exception) Unit := fun sourceEnv =>
  match loweredEnv.find? ctorName with
  | some (.ctorInfo ctor) => do
    let newType := res.restoreNested loweredEnv ctor.type
    sourceEnv.checkName ctor.name allowPrimitive
    return ((), sourceEnv.add <| .ctorInfo { ctor with type := newType })
  | _ => .error <| .other s!"missing lowered constructor '{ctorName}'"

/-- Restore and install one source inductive header by replacing the lowered
mutual-family metadata with the source family names. -/
def restoreInductiveHeaderDecl (loweredEnv : Environment)
    (allIndNames : List Name) (allowPrimitive : Bool) (indName : Name) :
    StateT Environment (Except Exception) Unit := fun sourceEnv =>
  match loweredEnv.find? indName with
  | some (.inductInfo ind) => do
    sourceEnv.checkName ind.name allowPrimitive
    return ((), sourceEnv.add <| .inductInfo { ind with all := allIndNames })
  | _ => .error <| .other s!"missing lowered inductive '{indName}'"

/-- Restore and install one source inductive family member, its constructors,
and its source recursor. -/
def restoreInductiveDecl (res : ElimNestedInductive.Result)
    (loweredEnv : Environment) (recNameMap : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool)
    (indType : InductiveType) :
    StateT Environment (Except Exception) Unit := do
  let some (.inductInfo ind) := loweredEnv.find? indType.name | unreachable!
  restoreInductiveHeaderDecl loweredEnv allIndNames allowPrimitive indType.name
  ind.ctors.forM fun ctorName =>
    restoreConstructorDecl res loweredEnv allowPrimitive ctorName
  restoreRecursorDecl res loweredEnv recNameMap allIndNames allowPrimitive
    (mkRecName indType.name)

/-- Restore the constructors of one source family after every mutual header
has already been installed in the side validation environment. -/
def restoreInductiveConstructorsOnly (res : ElimNestedInductive.Result)
    (loweredEnv : Environment) (allowPrimitive : Bool)
    (indType : InductiveType) :
    StateT Environment (Except Exception) Unit := do
  let some (.inductInfo ind) := loweredEnv.find? indType.name | unreachable!
  ind.ctors.forM fun ctorName =>
    restoreConstructorDecl res loweredEnv allowPrimitive ctorName

/-- Restore only the source mutual-family headers.  Cached nested-family
applications are types in this environment: they may mention any sibling
family, but they cannot depend on constructors or recursors of the
declaration currently being checked. -/
def restoreNestedHeaders (loweredEnv : Environment)
    (allIndNames : List Name) (allowPrimitive : Bool)
    (types : List InductiveType) :
    StateT Environment (Except Exception) Unit := do
  types.forM fun indType =>
    restoreInductiveHeaderDecl loweredEnv allIndNames allowPrimitive
      indType.name

/-- Restore the source headers and constructors without any recursors. This side
environment is where restored recursor types are validated; the returned environment is
built by `restoreNestedDeclarations`. -/
def restoreNestedConstructors (res : ElimNestedInductive.Result)
    (loweredEnv : Environment) (allIndNames : List Name)
    (allowPrimitive : Bool) (types : List InductiveType) :
    StateT Environment (Except Exception) Unit := do
  -- Constructors of one mutual family may mention a later sibling, so the
  -- validation environment installs every header before any constructor.
  restoreNestedHeaders loweredEnv allIndNames allowPrimitive types
  types.forM fun indType =>
    restoreInductiveConstructorsOnly res loweredEnv allowPrimitive indType

/-- The declaration-restoration loop for a lowered nested block: every source family with its
constructors and source recursor, then the auxiliary recursors, each renamed through
`recNameMap`. -/
def restoreNestedDeclarations (res : ElimNestedInductive.Result)
    (loweredEnv : Environment) (recNameMap : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool)
    (types : List InductiveType) (auxRecNames : List Name) :
    StateT Environment (Except Exception) Unit := do
  types.forM fun indType =>
    restoreInductiveDecl res loweredEnv recNameMap allIndNames
      allowPrimitive indType
  auxRecNames.forM fun recName =>
    restoreRecursorDecl res loweredEnv recNameMap allIndNames
      allowPrimitive recName

namespace validateSourceConstructorTypes

/-- Recheck every source constructor type in the environment of the restored source
headers. -/
def run (env : Environment) (lparams : List Name) (safety : DefinitionSafety)
    (fuel : FuelConfig) (types : List InductiveType) : Except Exception Unit := do
  types.forM fun type =>
    type.ctors.forM fun ctor => do
      _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := lparams) (fuel := fuel)
        (do
          let type ← TypeChecker.checkType ctor.type
          TypeChecker.ensureSort type ctor.type)

end validateSourceConstructorTypes

namespace validateRestoredRecursorTypes

/-- Recheck the type of one restored recursor. The side environment contains the restored
source headers and constructors and no recursor; the recursor type is restored from the
lowered recursor through the restoration map. -/
def check (env loweredEnv : Environment)
    (safety : DefinitionSafety) (fuel : FuelConfig)
    (res : ElimNestedInductive.Result) (recNameMap : NameMap Name)
    (allIndNames : List Name) (recName : Name) : Except Exception Unit := do
  let some (.recInfo recInfo) := loweredEnv.find? recName
    | throw <| .other s!"missing lowered recursor '{recName}'"
  let newRecName := recNameMap.getD recName recName
  let restored := res.restoreRecursor loweredEnv recNameMap allIndNames
    recName newRecName recInfo
  env.checkNoMVarNoFVar restored.name restored.type
  _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
    (lparams := restored.levelParams) (fuel := fuel) do
      let type ← TypeChecker.checkType restored.type
      TypeChecker.ensureSort type restored.type

/-- Recheck every restored source and auxiliary recursor type in the environment of the
restored source headers and constructors. The rules are validated separately
(`validateRestoredRecursorRules`). -/
def run (env loweredEnv : Environment)
    (safety : DefinitionSafety) (fuel : FuelConfig)
    (res : ElimNestedInductive.Result) (recNameMap : NameMap Name)
    (allIndNames : List Name) (types : List InductiveType)
    (auxRecNames : List Name) : Except Exception Unit := do
  types.forM fun type =>
    check env loweredEnv safety fuel res recNameMap allIndNames
      (mkRecName type.name)
  auxRecNames.forM fun recName =>
    check env loweredEnv safety fuel res recNameMap allIndNames recName

end validateRestoredRecursorTypes

namespace validateRestoredRecursorRules

/-- Type-check the right-hand side of every rule stored in one restored
recursor, as the C++ kernel's revalidation of restored nested declarations
([leanprover/lean4#14621](https://github.com/leanprover/lean4/pull/14621))
does. -/
def check (env loweredEnv : Environment)
    (safety : DefinitionSafety) (fuel : FuelConfig)
    (res : ElimNestedInductive.Result) (recNameMap : NameMap Name)
    (allIndNames : List Name) (recName : Name) :
    Except Exception Unit := do
  let some (.recInfo recInfo) := loweredEnv.find? recName
    | throw <| .other s!"missing lowered recursor '{recName}'"
  let newRecName := recNameMap.getD recName recName
  let restored := res.restoreRecursor loweredEnv recNameMap allIndNames
    recName newRecName recInfo
  restored.rules.forM fun rule => do
    env.checkNoMVarNoFVar restored.name rule.rhs
    _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
      (lparams := restored.levelParams) (fuel := fuel) do
        TypeChecker.checkType rule.rhs

/-- Type-check the right-hand sides of the rules of every restored source and auxiliary
recursor. The caller passes the restored environment with the rules of these recursors
removed (`stripRecursorRules`). -/
def run (env loweredEnv : Environment)
    (safety : DefinitionSafety) (fuel : FuelConfig)
    (res : ElimNestedInductive.Result) (recNameMap : NameMap Name)
    (allIndNames : List Name) (types : List InductiveType)
    (auxRecNames : List Name) : Except Exception Unit := do
  types.forM fun type =>
    check env loweredEnv safety fuel res recNameMap allIndNames
      (mkRecName type.name)
  auxRecNames.forM fun recName =>
    check env loweredEnv safety fuel res recNameMap allIndNames recName

end validateRestoredRecursorRules

/-- Type-check the nested application `I Ds` of every auxiliary family (`aux2nested`) in
the lowering's local parameter context. -/
def validateNestedAuxiliaries (env : Environment) (lparams : List Name)
    (safety : DefinitionSafety) (fuel : FuelConfig)
    (res : ElimNestedInductive.Result) : Except Exception Unit :=
  TypeChecker.M.run env (safety := safety) (lctx := res.lctx)
      (lparams := lparams) (fuel := fuel) do
    res.aux2nested.forM fun _ e => do
      _ ← TypeChecker.checkType e

/-- The names of the recursors produced by nested restoration: the source recursors of the
source types and the auxiliary recursors, each renamed through `recNameMap`. -/
def restoredRecursorNames (recNameMap : NameMap Name) (types : List InductiveType)
    (auxRecNames : List Name) : List Name :=
  (types.map (mkRecName ·.name) ++ auxRecNames).map fun name => recNameMap.getD name name

/-- The environment `env` with the rule lists of the recursors named in `recNames` removed.
Restored recursor rules are validated in this environment, so that no restored rule can be used
by iota reduction while the rules themselves are being validated. -/
def stripRecursorRules (env : Environment) (recNames : List Name) : Environment :=
  recNames.foldl (init := env) fun env name =>
    match env.find? name with
    | some (.recInfo info) => env.add (.recInfo { info with rules := [] })
    | _ => env

/-- Restore a successfully installed lowered block. Before the restored environment is
returned, the source constructor types, the restored recursor types, the right-hand sides of
the restored rules and the nested applications `I Ds` are type-checked, each in its own side
environment (section 3.3 of the design notes). -/
def Environment.restoreNestedAfterInstall (env loweredEnv : Environment)
    (lparams : List Name) (types : List InductiveType)
    (safety : DefinitionSafety) (allowPrimitive : Bool) (fuel : FuelConfig)
    (res : ElimNestedInductive.Result) : Except Exception Environment := do
  let allIndNames := types.map (·.name)
  let (recNames', recNameMap') := mkAuxRecNameMap loweredEnv types
  let restoredEnv ← (·.2) <$> StateT.run (s := env)
    (restoreNestedDeclarations res loweredEnv recNameMap' allIndNames
      allowPrimitive types recNames')
  let validationEnv ← (·.2) <$> StateT.run (s := env)
    (restoreNestedConstructors res loweredEnv allIndNames allowPrimitive types)
  let auxiliaryHeaderEnv ← (·.2) <$> StateT.run (s := env)
    (restoreNestedHeaders loweredEnv allIndNames allowPrimitive types)
  validateSourceConstructorTypes.run auxiliaryHeaderEnv lparams safety
    fuel types
  validateRestoredRecursorTypes.run validationEnv loweredEnv safety
    fuel res recNameMap' allIndNames types recNames'
  validateRestoredRecursorRules.run
    (stripRecursorRules restoredEnv (restoredRecursorNames recNameMap' types recNames'))
    loweredEnv safety fuel res recNameMap' allIndNames types recNames'
  validateNestedAuxiliaries auxiliaryHeaderEnv lparams safety fuel res
  return restoredEnv

/-- The inductive checker after nested lowering: run the ordinary pipeline on the lowered
block, then return it directly if it has no auxiliary families, and otherwise restore and
validate the source declarations (`restoreNestedAfterInstall`). -/
def Environment.addInductiveAfterLowering (env : Environment)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig)
    (res : ElimNestedInductive.Result) : Except Exception Environment := do
  let numNested := res.aux2nested.size
  let safety := if isUnsafe then .unsafe else .safe
  let env' ← AddInductive.run nparams res.types numNested
    { env, allowPrimitive, lparams, fuel, safety }
  if numNested = 0 then return env'
  Environment.restoreNestedAfterInstall env env' lparams types safety
    allowPrimitive fuel res

def Environment.addInductive (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig := {}) :
    Except Exception Environment := do
  checkInductiveSources env types
  let res ← ElimNestedInductive.run fuel.inductiveFuel nparams types env
    |>.run' { lvls := lparams.map .param, newTypes := types.toArray }
  Environment.addInductiveAfterLowering env lparams nparams types isUnsafe
    allowPrimitive fuel res
