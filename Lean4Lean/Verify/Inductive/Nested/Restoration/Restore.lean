import Lean4Lean.Verify.Inductive.Nested.Restoration.Certificate
import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.Passes

/-! # The restored block of a nested run (owner: Restoration-B)

The boundary theorem of the restoration: a lowered run `L` on the lowered block, a successful
restoration `V` and the lowering's certificate `Hout` yield the `RestoredBlock`. The source
branch's material is `Nested/Restoration/**` minus `Equations/` and the Restoration-A files:
the refinement of the restoration folds (`Steps.lean`: `restoreNestedDeclarations_refines`,
`FreshExtension`, `NestedRestorationFolds`), the restored source declaration
(`SourceDeclaration`, `SourceHeaders`, `SourceConstructors`, `SourceConstructorTypes`,
`SourceTranslations`, `HeaderRenaming`, `InstalledFamilyLookups`, `InstalledConstructorTypes`),
the specialization table (`Tables`, `TableAgreement`, `ContainerSpecializations`,
`AuxiliaryHeaders`, `AuxiliaryConstructors`, `AuxiliaryProjections`, `ExpansionInverse`,
`Commutation*`, `TranslationPreservation`, `Translations`, `HeadTranslation`), the restored
recursors (`Recursors`, `RecursorTypes`, `RecursorRenaming`, `RecursorShape`,
`RecursorAlignment`, `AuxiliaryRecursorsWF`, `TrRestoredRecursorVal`, `LoweredRuleAvoidance`,
`Nonprimitive`), the compilation data (`CompilationData`, `CompilationDataConstructors`,
`ConstructorTelescopes`, `ConstructorTranslations`, `FreshExtensions`, `ExprReplace`,
`ParameterOpening`), and `Install/{Permutation,RecursorTranslations,DependencyOrder,
ConstructorCoherence}.lean` for the kernel order and the recursor translations. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The checker context of the nested branch: the executable's own
(`Environment.addInductiveAfterLowering`, with `allowPrimitive := false`). -/
abbrev nestedContext (env : Environment) (lparams : List Name) (isUnsafe : Bool)
    (fuel : FuelConfig) : AddInductive.Context :=
  initialContext env lparams (if isUnsafe then .unsafe else .safe) false fuel

/-- **The restoration boundary theorem.** -/
theorem nestedRestoredBlock {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {lparams : List Name} {nparams : Nat} {sourceTypes : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {res : ElimNestedInductive.Result} {loweredEnv outEnv : Environment}
    (Hsources : SourceSyntaxChecks env sourceTypes)
    (Hout : NestedLoweringOutput env fuel.inductiveFuel nparams sourceTypes lparams res)
    (hnested : res.aux2nested.size ≠ 0)
    (L : LoweredRun (ContextWF.initial wf (if isUnsafe then .unsafe else .safe) lparams false
      fuel) nparams res.types.toArray loweredEnv)
    (V : RestorationRun res loweredEnv env lparams sourceTypes
      (if isUnsafe then .unsafe else .safe) false fuel outEnv) :
    Nonempty (RestoredBlock L sourceTypes isUnsafe outEnv) := by
  -- WAVE 3 STUB (Restoration-B): the source branch's `NestedRun` from
  -- `nestedValidatedRawSourceWF`, `NestedRun.assemblyOfRun` (`Install/CertificateOfRun.lean`)
  -- and `RestoredBlockCertificate.blockCertificate` (`Install/BlockCertificate.lean`), without
  -- the rule typing (`RestoredBlock.rulesWF`, Equations) and the environment-side facts
  -- (`RestoredBlock.installedFacts`, Install). The validation passes enter through
  -- `Validation/Passes.lean`.
  have := wf; have := Hsources; have := Hout; have := hnested; have := L; have := V; sorry

end VerifyInductive
end Lean4Lean
