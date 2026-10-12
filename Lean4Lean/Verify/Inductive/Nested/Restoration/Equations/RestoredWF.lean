import Lean4Lean.Verify.Inductive.Nested.Restoration.Equations.ProjNames
import Lean4Lean.Verify.Inductive.Nested.Restoration.Equations.AuxiliaryConstructors
import Lean4Lean.Verify.Inductive.Nested.Restoration.AuxiliaryProjections

/-! # The typing of the restored generated equations of a nested run

`NestedRun.hrestoredWF_of`: every restored generated equation of a validated nested run is
well formed in the recursor stage of a restored block base in which the stripped output
environment is valid. It is `restoredEquationsWF_of_substitutionPremises`
(`Equations/WF.lean`) with the substitution premises supplied by `restoredEquationGaps`:
the projection names (`Equations/ProjNames.lean`), the auxiliary constructor lambdas
(`Equations/AuxiliaryConstructors.lean`) and the projection rules
(`Restoration/AuxiliaryProjections.lean`). The field `RestoredBlock.restoredEquationsWF`
(produced in `nestedRestoredBlock`) is read off this theorem. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-- The premises of the restoration substitution of a nested run. -/
theorem NestedRun.restoredEquationGaps
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ B : RestoredBlockBase E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        B.loweredDecl = E.lowered.loweredDecl →
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) B.recursorVEnv →
        RestorationSubstitutionPremises E B auxiliaries := by
  refine E.restoredEquationGaps_of wf Hsources fun auxiliaries D B hB hV =>
    ⟨E.restoredEquationAuxiliaryConstructors_of wf Hsources auxiliaries D, ?_⟩
  intro entry hentry
  by_cases hTN : entry.typeName ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames
  · exact E.projectionAuxiliaryOnCtx_of wf Hsources auxiliaries D B hB hV entry hentry hTN
  · exact E.projectionSourceOnCtx_of wf Hsources auxiliaries D B hB hV entry hentry hTN

/-- **The restored generated equations are well formed** in the recursor stage of a restored
block base in which the stripped output environment is valid. -/
theorem NestedRun.hrestoredWF_of
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ B : RestoredBlockBase E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        B.loweredDecl = E.lowered.loweredDecl →
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) B.recursorVEnv →
        ∀ (k : Fin E.lowered.recursors.generationSignature.constructors.size)
          (rule : VDefEq),
          (compilationRestoration sourceDecl auxiliaries).equation
              (E.lowered.recursors.canonicalGeneration.equation k) =
            some rule →
          rule.WF B.recursorVEnv :=
  E.restoredEquationsWF_of_substitutionPremises wf Hsources (E.restoredEquationGaps wf Hsources)

end VerifyInductive
end Lean4Lean
