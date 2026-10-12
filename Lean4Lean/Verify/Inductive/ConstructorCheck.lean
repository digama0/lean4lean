import Lean4Lean.Verify.Inductive.Constructor.Install
import Lean4Lean.Verify.Inductive.Constructor.CheckRun
import Lean4Lean.Verify.Inductive.HeaderData

/-! # The constructor check

`ConstructorCheck` is the output of the constructor phase and the input of the recursor and rule
phases: the header data, the translated declaration (`TrInductDeclCore`), the formation
certificate, the checked constructor tails with the executable's field classification, the
kernel constructors installed over the header environment (`ivals`, `map_eq`, `fresh`) and
translating to the abstract ones (`trTypes`, PR #43's `TrIndType`), and a valid checking context
over the constructor environment with the declaration's projection entries registered
(`context`, `contextVEnv`), in which the recursors are checked.

One structure serves the ordinary and the primitive path. Its header data (`HeaderData`) carries
the header environment's checker context as a `LocalContextWF`, the part of `ContextWF` without
the primitive invariant (`HasPrimitives`): that invariant is false in the header-only
environment of the primitive `Bool`/`Nat` declarations (the family is present without its
constructors). Both paths build it from a constructor installation (`CtorInstall.toConstructorCheck`:
`constructorPhase.WF` and `Primitive/`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The constructor check (see the module documentation). -/
structure ConstructorCheck (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
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
  -- The tails are in the header statistics' parameter scope.
  constructorTails : ConstructorTails headers.context.venv c.lparams
    headers.statsWF.parameterScope stats decl indTypes classes
  ownerNormalForms : ConstructorOwnerNormalForms stats indTypes
  /-- Positivity's literal side condition in the recursor phase's context. -/
  literalDisjoint : checkPositivityStep.AvailableLiteralDisjoint context.venv stats.indConsts
  /-- Without the primitive exception, the family and constructor names are not checker
  primitives (they passed `checkName`). Read by the nested restoration
  (`NestedRun.loweredNonprimitive`). -/
  nonprimitive : c.allowPrimitive = false → ∀ T ∈ decl.types,
    ¬ Kernel.Environment.primitives.contains T.name ∧
      ∀ ctor ∈ T.ctors, ¬ Kernel.Environment.primitives.contains ctor.name

/-- The constructor check of a constructor installation over header data. -/
noncomputable def CtorInstall.toConstructorCheck {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl} {nparams : Nat} {isUnsafe : Bool}
    {depth : Nat} {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv : Environment} {classes : List (List (List Bool))}
    (I : CtorInstall c stats decl nparams isUnsafe depth sourceEnv indTypes headerEnv ctorEnv
      classes) (hclosed : MutualInductivesClosed c.env)
    (hnprim : c.allowPrimitive = false → ∀ T ∈ decl.types,
      ¬ Kernel.Environment.primitives.contains T.name ∧
        ∀ ctor ∈ T.ctors, ¬ Kernel.Environment.primitives.contains ctor.name) :
    ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv where
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
  nonprimitive := hnprim

namespace ConstructorCheck

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {ctorEnv : Environment}

/-- The abstract header environment. -/
abbrev headerVEnv (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    VEnv := R.headers.context.venv

theorem headerVEnv_wf (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes
    ctorEnv) : R.headerVEnv.WF := R.headers.context.wf

/-- The projection-stage environment, in which the recursors are checked. -/
abbrev envP (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    VEnv := R.ctorVEnv.addProjections decl.projectionEntries

theorem envP_eq (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    R.context.venv = R.envP := R.contextVEnv

theorem envP_wf (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    R.envP.WF := by have := R.context.wf; rwa [R.contextVEnv] at this

theorem addTypesCtors (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes
    ctorEnv) : decl.addTypesCtors sourceEnv = some R.ctorVEnv := by
  rw [VInductDecl.addTypesCtors, VInductDecl.addTypes_eq_addConstVals, R.core.typesAdded]
  simp [VInductDecl.addCtors_eq_addConstVals, R.core.ctorsAdded]

theorem addTypesCtorsProjs (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv
    indTypes ctorEnv) : decl.addTypesCtorsProjs sourceEnv = some R.envP := by
  rw [VInductDecl.addTypesCtorsProjs, R.addTypesCtors]; rfl

theorem typesWF (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes
    ctorEnv) : ∀ ci ∈ decl.typeConstants, ci.toVConstant.WF sourceEnv := by
  intro ci hci
  simp only [VInductDecl.typeConstants, List.mem_map] at hci
  obtain ⟨t, ht, rfl⟩ := hci
  exact TrInductDeclCore.typeHeadersWF R.core t ht

theorem ctorsWF (R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes
    ctorEnv) : ∀ ci ∈ decl.constructorConstants, ci.toVConstant.WF R.headerVEnv := by
  intro ci hci
  simp only [VInductDecl.constructorConstants, List.mem_flatMap] at hci
  obtain ⟨t, ht, hci⟩ := hci
  obtain ⟨_, _, Ht⟩ := List.Forall₂.forall_exists_r R.core.types t ht
  obtain ⟨_, _, Hc⟩ := List.Forall₂.forall_exists_r Ht.ctors ci hci
  exact Hc.wf

end ConstructorCheck


end VerifyInductive
end Lean4Lean
