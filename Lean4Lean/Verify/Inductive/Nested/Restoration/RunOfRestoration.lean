import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceDeclaration
import Lean4Lean.Verify.Inductive.Nested.Restoration.RestorationRun
import Lean4Lean.Verify.Inductive.Nested.Restoration.LoweredRun
import Lean4Lean.Verify.Inductive.Nested.Restoration.Nonprimitive
import Lean4Lean.Verify.Inductive.Nested.Restoration.SideEnvironment.Environment
import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.ParameterPrefix
import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.Passes
import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.Checks
import Lean4Lean.Verify.Inductive.Nested.Lowering.OccurrenceTyping

/-! # The nested run of a successful restoration

`NestedRun.ofRestoration` assembles the `NestedRun` record from the lowering certificate
(`NestedLoweringOutput`), the lowered run (`LoweredRun`) and the executable restoration
(`RestorationRun`): the restoration folds and the side environments are read off the
runs recorded by `RestorationRun`, the source declaration is reconstructed by
`NestedLoweringOutputClosed.sourceCore`, and the cached nested occurrences are typed in the
header side environment (`validateNestedAuxiliaries.WF_typing`), whose checker environment is
`ValidationHeaderEnvironment.checkerEnvOfLowering`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The lowered family and constructor names are not checker primitives when the lowered run
does not allow primitives (`ConstructorCheck.nonprimitive`, recorded by the constructor phase). -/
theorem LoweredRun.loweredNonprimitive {c : AddInductive.Context} {Hc : ContextWF c}
    {nparams : Nat} {indTypes : Array InductiveType} {loweredEnv : Environment}
    (L : LoweredRun Hc nparams indTypes loweredEnv) (hallow : c.allowPrimitive = false) :
    ∀ n ∈ InductiveSignature.familyNames L.loweredDecl.types,
      ¬ Kernel.Environment.primitives.contains n := by
  intro n hn
  obtain ⟨T, hT, hn⟩ := List.mem_flatMap.mp hn
  have H := L.constructors.nonprimitive (L.phase.allowPrimitive_eq.trans hallow) T hT
  rcases List.mem_cons.mp hn with rfl | hn
  · exact H.1
  · obtain ⟨ctor, hctor, rfl⟩ := List.mem_map.mp hn
    exact H.2 ctor hctor

theorem LoweredRun.loweredHeadersNonprimitive {c : AddInductive.Context} {Hc : ContextWF c}
    {nparams : Nat} {indTypes : Array InductiveType} {loweredEnv : Environment}
    (L : LoweredRun Hc nparams indTypes loweredEnv) (hallow : c.allowPrimitive = false) :
    ∀ t ∈ L.loweredDecl.types, ¬ Kernel.Environment.primitives.contains t.name := by
  intro t ht
  exact L.loweredNonprimitive hallow t.name
    (List.mem_flatMap.mpr ⟨t, ht, List.mem_cons_self⟩)

private theorem inductiveSafety_ne_safe (isUnsafe : Bool) :
    ((if isUnsafe then DefinitionSafety.unsafe else .safe) != .safe) = isUnsafe := by
  cases isUnsafe <;> rfl

/-- **The nested run of a successful restoration.** The lowering certificate, the lowered run
and the executable restoration determine a `NestedRun` over the lowered run. -/
theorem NestedRun.ofRestoration {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {lparams : List Name} {nparams : Nat} {sourceTypes : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {res : ElimNestedInductive.Result} {loweredEnv outEnv : Environment}
    (Hsources : SourceSyntaxChecks env sourceTypes)
    (Hout : NestedLoweringOutput env fuel.inductiveFuel nparams sourceTypes lparams res)
    (hnested : res.aux2nested.size ≠ 0)
    (L : LoweredRun (ContextWF.initial wf (if isUnsafe then .unsafe else .safe) lparams false
      fuel) nparams res.types.toArray loweredEnv)
    (V : RestorationRun res loweredEnv env lparams sourceTypes
      (if isUnsafe then .unsafe else .safe) false fuel outEnv) :
    ∃ decl, Nonempty <| NestedRun res env sourceTypes
        (ContextWF.initial wf (if isUnsafe then .unsafe else .safe) lparams false fuel).venv
        decl lparams nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L := by
  have := hnested
  let Hc0 := ContextWF.initial wf (if isUnsafe then .unsafe else .safe) lparams false fuel
  have hsourceWF : env.constants.WF := Hc0.map_wf
  -- the lowering certificate
  have Hlow := Hout.closed
  have HlowRun : NestedLoweringRun env fuel.inductiveFuel nparams sourceTypes
      { ({ lvls := lparams.map .param, newTypes := #[] } : ElimNestedInductive.State) with
        newTypes := sourceTypes.toArray } res := Hlow.toResult
  -- the restoration folds
  have Htypes := L.recursors.restorationSourcesOfLowering L.Hc' HlowRun
  have Haux := L.recursors.auxRestorationSourcesOfLowering L.Hc' HlowRun
  rw [← Hout.nparams_eq] at Htypes Haux
  have Hrefines := restoreNestedDeclarations_refines_primitiveSafe res loweredEnv env
    (auxRecNameMap loweredEnv sourceTypes) (sourceTypes.map (·.name)) false sourceTypes
    (auxRecNames loweredEnv sourceTypes) Htypes Haux hsourceWF
  have hrestored := V.restored
  unfold StateT.run at hrestored
  obtain ⟨⟨Hfolds⟩, Hprim⟩ := Hrefines _ hrestored
  -- the side environments
  obtain ⟨validationEnv, hvrun, hrecTypes⟩ := V.validation
  unfold StateT.run at hvrun
  obtain ⟨-, ⟨HV⟩⟩ := restoreNestedConstructors_validationWF res loweredEnv env
    (sourceTypes.map (·.name)) false sourceTypes
    (fun t ht => let ⟨o, h, _⟩ := Htypes t ht; ⟨o, h⟩) _ hvrun
  obtain ⟨auxiliaryHeaderEnv, hhrun, hparams, hauxRun⟩ := V.headers
  unfold StateT.run at hhrun
  obtain ⟨-, ⟨HH⟩⟩ := restoreNestedHeaders_validationWF loweredEnv env
    (sourceTypes.map (·.name)) false sourceTypes _ hhrun
  -- the source declaration
  have hallow : L.c.allowPrimitive = false := L.phase.allowPrimitive_eq
  have hvisible : L.c.safety ≤
      (if ((if isUnsafe then DefinitionSafety.unsafe else .safe) != .safe) then
        DefinitionSafety.unsafe else .safe) := by
    rw [L.safety_eq]
    change (if isUnsafe then DefinitionSafety.unsafe else .safe) ≤ _
    cases isUnsafe <;> decide
  have hN := NestedLoweringOutputClosed.sourceCore (R := L.constructors)
    (initialState := { lvls := lparams.map .param, newTypes := #[] })
    (by rw [L.env_eq]; exact Hlow) L.Hc' L.recursors
    (checkInductiveSources_refines env sourceTypes () Hsources)
    L.Hc'.checking.constructorOwners rfl
    (by rw [L.env_eq]; exact Hfolds) (by rw [L.env_eq]; exact HV) (by rw [L.env_eq]; exact HH)
    (by rw [L.lparams_eq, L.safety_eq]; exact hparams)
    (SourceSyntaxChecks.ctorTypesClosed Hsources) hvisible
    (L.loweredHeadersNonprimitive rfl)
  rw [L.venv_eq, L.lparams_eq, L.safety_eq] at hN
  change Nonempty (NestedSourceDeclaration _ lparams nparams sourceTypes
    ((if isUnsafe then DefinitionSafety.unsafe else .safe) != .safe) _
    (if isUnsafe then .unsafe else .safe) validationEnv auxiliaryHeaderEnv) at hN
  rw [inductiveSafety_ne_safe] at hN
  obtain ⟨N⟩ := hN
  -- the auxiliary occurrences, typed in the header side environment
  have Caux := ValidationHeaderEnvironment.checkerEnvOfLowering (c := initialContext env lparams
    (if isUnsafe then .unsafe else .safe) false fuel) Hc0.checkerEnv HH N.sourceAdded
    N.headerValidationValid
  have Hfirst : ∀ first rest, sourceTypes = first :: rest →
      ∃ target, TrExprS N.envTypes lparams [] first.type target := by
    intro first rest h
    have hs := N.sourceHeaders
    obtain ⟨_, -, hh⟩ := Lean4Lean.List.Forall₂.forall_exists_l hs first (by simp [h])
    exact ⟨_, hh.type.mono (VEnv.addConstVals_le N.sourceAdded)⟩
  obtain ⟨mlctx, hmlctx, hlctx, hfresh, hfvars⟩ := Hout.parameterMLCtx Caux.wf Hfirst
  have Hvalidated : NestedOccurrencesTyped N.envTypes lparams mlctx.vlctx res :=
    validateNestedAuxiliaries.WF_typing Caux lparams fuel res mlctx hmlctx hlctx hfresh hfvars
      hauxRun
  obtain ⟨finalState, HlowNested, -, -⟩ := Hlow
  obtain ⟨selection, Htranslations⟩ :=
    HlowNested.validatedAuxiliaryResidualTranslations Caux.wf mlctx hmlctx hlctx Hvalidated
  refine ⟨N.sourceDecl, ⟨{
    context_env := L.env_eq
    context_lparams := L.lparams_eq
    context_safety := L.safety_eq
    lowered_isUnsafe_source := inductiveSafety_ne_safe isUnsafe
    lowered_initialEnv := L.venv_eq
    validationFuel := fuel
    lowering := Hout.closed
    restoration := Hfolds
    primitiveSafe := Hprim
    validationEnv := validationEnv
    validationEnvironment := HV
    recursorTypeValidation := hrecTypes
    recursorRuleValidation := V.rules
    auxiliaryHeaderEnv := auxiliaryHeaderEnv
    headerValidationEnvironment := HH
    auxiliaryVEnv := N.envTypes
    auxiliarySelection := selection
    auxiliaryTranslations := Htranslations
    sourceCore := N
    sourceCoreDecl_eq := rfl
    auxiliaryVEnv_eq_sourceCore := rfl
    loweredNonprimitive := L.loweredNonprimitive rfl }⟩⟩

end VerifyInductive
end Lean4Lean
