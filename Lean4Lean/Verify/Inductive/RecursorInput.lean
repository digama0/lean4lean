import Lean4Lean.Verify.Inductive.Constructor.Check
import Lean4Lean.Verify.Inductive.HeaderData

/-! # The input of the recursor phase

`RecursorInput` is what the recursor and rule phases read of the constructor phase. It is
`ConstructorCheck` with the header environment's checker context weakened to a
`LocalContextWF`, the part of `ContextWF` that does not assert the primitive invariant
(`HasPrimitives`): that invariant is false in the header-only environment of the primitive
`Bool`/`Nat` declarations (the family is present without its constructors). The ordinary
constructor phase produces it by `ConstructorCheck.toRecursorInput`, the primitive one directly
(`Primitive/`). Field names are those of `ConstructorCheck`, so `R.foo` reads the same field
under either index.

WAVE 2 install COMPAT: interface structure, introduced so that the recursor phase keeps one
input type for the ordinary and the primitive path. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The input of the recursor phase: `ConstructorCheck` (with its `CheckedFormation` fields
flattened, under the same names) with the header context a `LocalContextWF`. -/
structure RecursorInput (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (decl : VInductDecl) (nparams : Nat) (isUnsafe : Bool) (depth : Nat) (sourceEnv : VEnv)
    (indTypes : Array InductiveType) (ctorEnv : Environment) where
  headerEnv : Environment
  headers : HeaderData c stats decl nparams isUnsafe depth sourceEnv indTypes headerEnv
  ctorVEnv : VEnv
  core : TrInductDeclCore sourceEnv c.lparams nparams indTypes.toList isUnsafe decl
    headers.context.venv ctorVEnv
  formation : FormationCertificate sourceEnv decl
  params_eq : formation.headers.params = headers.headers.params
  checked : CheckedConstructorCertificate sourceEnv decl headers.context.venv
    formation.headers.params
  classes : List (List (List Bool))
  classes_length : classes.length = indTypes.size
  tails : ∀ i (hi : i < decl.types.length) j (hj : j < decl.types[i].ctors.length),
    CheckedCtorTail headers.context.venv decl formation.headers.params decl.types[i]
      decl.types[i].ctors[j] (classes[i]![j]!)
  ivals : List (InductiveVal × List ConstructorVal)
  ivals_infos : ivals.map (·.1) = headers.infos
  trTypes : List.Forall₂ (fun (iv : InductiveVal × List ConstructorVal) (t : VInductiveType) =>
    TrIndType c.safety sourceEnv headers.context.venv iv.1 iv.2 t) ivals decl.types
  map_eq : ctorEnv.constants =
    insertConsts headerEnv.constants (ivals.flatMap fun iv => iv.2.map .ctorInfo)
  quotInit_eq : ctorEnv.quotInit = headerEnv.quotInit
  fresh : ∀ iv ∈ ivals, ∀ cval ∈ iv.2, headerEnv.find? cval.name = none
  context : ContextWF { c with env := ctorEnv }
  contextVEnv : context.venv = ctorVEnv.addProjections decl.projectionEntries
  contextMLCtx : context.mlctx = headers.context.mlctx
  parameters : HeaderParameterContext context stats formation.headers.params depth
  closed : MutualInductivesClosed ctorEnv
  inductInfosFromDecl : InductInfosFromDecl c.env.constants ctorEnv.constants decl
  constructorParameterAlignment : ∀ {safety},
    ConstructorParameterAlignment safety c.env sourceEnv →
    ConstructorParameterAlignment safety ctorEnv ctorVEnv
  ivals_eq : ivals = (headers.infos.zip indTypes.toList).map fun p =>
    (p.1, familyCtorInfos stats c.lparams isUnsafe p.2)
  ctor_numParams : ∀ iv ∈ ivals, ∀ cval ∈ iv.2, cval.numParams = decl.nparams
  parameterPrefixes : ConstructorParameterPrefixes stats indTypes
  -- WAVE 2 ctor COMPAT: the tails are in the header statistics' parameter scope, as
  -- `ConstructorCheck.constructorTails` (and the source branch) states them.
  constructorTails : ConstructorTails headers.context.venv c.lparams
    headers.statsWF.parameterScope stats decl indTypes classes
  ownerNormalForms : ConstructorOwnerNormalForms stats indTypes
  /-- Positivity's literal side condition in the recursor phase's context. -/
  literalDisjoint : checkPositivityStep.AvailableLiteralDisjoint context.venv stats.indConsts

/-- The ordinary constructor phase's output as the recursor phase's input. -/
def ConstructorCheck.toRecursorInput {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl} {nparams : Nat} {isUnsafe : Bool}
    {depth : Nat} {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
    (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv where
  headerEnv := R.headerEnv
  headers := R.headers.toData
  ctorVEnv := R.ctorVEnv
  core := R.core
  formation := R.formation
  params_eq := R.params_eq
  checked := R.checked
  classes := R.classes
  classes_length := R.classes_length
  tails := R.tails
  ivals := R.ivals
  ivals_infos := R.ivals_infos
  trTypes := R.trTypes
  map_eq := R.map_eq
  quotInit_eq := R.quotInit_eq
  fresh := R.fresh
  context := R.context
  contextVEnv := R.contextVEnv
  contextMLCtx := R.contextMLCtx
  parameters := R.parameters
  closed := R.closed
  inductInfosFromDecl := R.inductInfosFromDecl
  constructorParameterAlignment := R.constructorParameterAlignment
  ivals_eq := R.ivals_eq
  ctor_numParams := R.ctor_numParams
  parameterPrefixes := R.parameterPrefixes
  constructorTails := R.constructorTails
  ownerNormalForms := R.ownerNormalForms
  literalDisjoint := R.literalDisjoint

/-- The recursor phase's input from a constructor installation over header data (the path of
the primitive declarations, whose header environment has no `ContextWF`). -/
noncomputable def CtorInstall.toRecursorInput {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl} {nparams : Nat} {isUnsafe : Bool}
    {depth : Nat} {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv : Environment} {classes : List (List (List Bool))}
    (I : CtorInstall c stats decl nparams isUnsafe depth sourceEnv indTypes headerEnv ctorEnv
      classes) (hclosed : MutualInductivesClosed c.env) :
    RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv where
  headerEnv := headerEnv
  headers := I.H
  ctorVEnv := I.ctorVEnv
  core := I.core
  formation := I.formation
  params_eq := rfl
  checked := ⟨I.K.shapes, I.K.types⟩
  classes := classes
  classes_length := I.K.classes_length
  tails := I.K.tails
  ivals := I.ivals
  ivals_infos := I.ivals_infos
  trTypes := I.trTypes
  map_eq := by rw [I.ivals_flat]; exact I.map_eq
  quotInit_eq := I.quotInit_eq
  fresh := fun iv hiv cval hcval => by
    have hmem : ConstantInfo.ctorInfo cval ∈
        I.ivals.flatMap (fun iv => iv.2.map ConstantInfo.ctorInfo) :=
      List.mem_flatMap.mpr ⟨iv, hiv, List.mem_map_of_mem hcval⟩
    rw [I.ivals_flat] at hmem
    obtain ⟨cv, hcv, he⟩ := List.mem_map.mp hmem
    cases he
    exact I.fresh _ hcv
  context := I.context
  contextVEnv := rfl
  contextMLCtx := I.context_mlctx
  parameters := I.parameters
  closed := I.closed hclosed
  inductInfosFromDecl := I.inductInfosFromDecl
  constructorParameterAlignment := fun h => I.constructorParameterAlignment h
  ivals_eq := rfl
  ctor_numParams := I.ctor_numParams
  parameterPrefixes := I.K.parameterPrefixes
  constructorTails := I.K.constructorTails
  ownerNormalForms := I.K.ownerNormalForms
  literalDisjoint := I.contextLiteralDisjoint

namespace RecursorInput

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {ctorEnv : Environment}

/-- The abstract header environment. -/
abbrev headerVEnv (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    VEnv := R.headers.context.venv

theorem headerVEnv_wf (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes
    ctorEnv) : R.headerVEnv.WF := R.headers.context.wf

/-- The projection-stage environment, in which the recursors are checked. -/
abbrev envP (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    VEnv := R.ctorVEnv.addProjections decl.projectionEntries

theorem envP_eq (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    R.context.venv = R.envP := R.contextVEnv

theorem envP_wf (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    R.envP.WF := by have := R.context.wf; rwa [R.contextVEnv] at this

theorem addTypesCtors (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes
    ctorEnv) : decl.addTypesCtors sourceEnv = some R.ctorVEnv := by
  rw [VInductDecl.addTypesCtors, VInductDecl.addTypes_eq_addConstVals, R.core.typesAdded]
  simp [VInductDecl.addCtors_eq_addConstVals, R.core.ctorsAdded]

theorem addTypesCtorsProjs (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv
    indTypes ctorEnv) : decl.addTypesCtorsProjs sourceEnv = some R.envP := by
  rw [VInductDecl.addTypesCtorsProjs, R.addTypesCtors]; rfl

theorem typesWF (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes
    ctorEnv) : ∀ ci ∈ decl.typeConstants, ci.toVConstant.WF sourceEnv := by
  intro ci hci
  simp only [VInductDecl.typeConstants, List.mem_map] at hci
  obtain ⟨t, ht, rfl⟩ := hci
  exact TrInductDeclCore.typeHeadersWF R.core t ht

theorem ctorsWF (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes
    ctorEnv) : ∀ ci ∈ decl.constructorConstants, ci.toVConstant.WF R.headerVEnv := by
  intro ci hci
  simp only [VInductDecl.constructorConstants, List.mem_flatMap] at hci
  obtain ⟨t, ht, hci⟩ := hci
  obtain ⟨_, _, Ht⟩ := List.Forall₂.forall_exists_r R.core.types t ht
  obtain ⟨_, _, Hc⟩ := List.Forall₂.forall_exists_r Ht.ctors ci hci
  exact Hc.wf

end RecursorInput

section
variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {ctorEnv : Environment}
  (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv)

@[simp] theorem ConstructorCheck.toRecursorInput_headerEnv :
    R.toRecursorInput.headerEnv = R.headerEnv := rfl
@[simp] theorem ConstructorCheck.toRecursorInput_ctorVEnv :
    R.toRecursorInput.ctorVEnv = R.ctorVEnv := rfl
@[simp] theorem ConstructorCheck.toRecursorInput_headerVEnv :
    R.toRecursorInput.headerVEnv = R.headerVEnv := rfl
@[simp] theorem ConstructorCheck.toRecursorInput_envP :
    R.toRecursorInput.envP = R.envP := rfl
@[simp] theorem ConstructorCheck.toRecursorInput_classes :
    R.toRecursorInput.classes = R.classes := rfl
@[simp] theorem ConstructorCheck.toRecursorInput_ivals :
    R.toRecursorInput.ivals = R.ivals := rfl
@[simp] theorem ConstructorCheck.toRecursorInput_infos :
    R.toRecursorInput.headers.infos = R.headers.infos := rfl
end

end VerifyInductive
end Lean4Lean
