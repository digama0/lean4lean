import Lean4Lean.Verify.Inductive.Nested.Restoration.Certificate
import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.Passes
import Lean4Lean.Verify.Inductive.Nested.Restoration.RunOfRestoration
import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceParametersRun
import Lean4Lean.Verify.Inductive.Nested.Restoration.AssemblyBase
import Lean4Lean.Verify.Inductive.Nested.Restoration.TableAgreement
import Lean4Lean.Verify.Inductive.Nested.Restoration.KernelData
import Lean4Lean.Verify.Inductive.Nested.Restoration.FormationWithRecs
import Lean4Lean.Verify.Inductive.Nested.Restoration.AssemblyTypes
import Lean4Lean.Verify.Inductive.Nested.Restoration.AssemblyKernel
import Lean4Lean.Verify.Inductive.Nested.Restoration.AssemblyRecursors
import Lean4Lean.Verify.Inductive.Nested.Restoration.StrippedFacts

/-! # The restored block of a nested run

The boundary theorem of the restoration: a lowered run `L` on the lowered block, a successful
restoration `V` and the lowering's certificate `Hout` yield the `RestoredBlock`. It assembles
the refinement of the restoration folds (`Steps.lean`: `restoreNestedDeclarations_refines`,
`FreshExtension`, `NestedRestorationFolds`), the restored source declaration
(`SourceDeclaration`, `SourceHeaders`, `SourceConstructors`, `SourceConstructorTypes`,
`SourceTranslations`, `HeaderRenaming`, `InstalledFamilyLookups`),
the specialization table (`Tables`, `TableAgreement`, `ContainerSpecializations`,
`AuxiliaryHeaders`, `AuxiliaryConstructors`, `AuxiliaryProjections`, `ExpansionInverse`,
`Commutation*`, `TranslationProjNames`, `Translations`), the restored
recursors (`Recursors`, `RecursorTypes`, `RecursorRenaming`, `RecursorShape`,
`RecursorAlignment`, `TrRestoredRecursorVal`, `LoweredRuleAvoidance`,
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
  have := hnested
  obtain ⟨runDecl, ⟨E⟩⟩ := NestedRun.ofRestoration wf Hsources Hout hnested L V
  have Hchecked := checkInductiveSources_refines env sourceTypes _ Hsources
  have Hparameters := E.sourceParameterWF wf Hchecked
  obtain ⟨⟨B, hBlowered, hBperm⟩⟩ := E.assemblyBase wf rfl Hsources Hparameters (by cases isUnsafe <;> decide)
  obtain ⟨hperm, hfresh, hmap, hquot⟩ :=
    E.restoration.kernelOrder (ContextWF.initial wf (if isUnsafe then .unsafe else .safe) lparams
      false fuel).map_wf
  obtain ⟨hV, Cstrip⟩ := E.strippedChecker B hBlowered wf Hchecked Hparameters hnested
  obtain ⟨recs, auxiliaries, block, envR, outVEnv, hcontainers, hcompiled, hrecsOf, hrecsAdded,
    htrRecs, hrecs_wf, hrec_shape, hrules_nodup, hrules_ctor, hrules_ctorParams, hrule_shape,
    hrules_closed, hrulesAdded, hrecShapes, hrecK, henvR, hequationsWF⟩ :=
    E.assemblyRecursors wf Hchecked hnested B hBlowered hBperm Cstrip hV
  refine ⟨{
    decl := runDecl.withRecs recs
    envTypes := E.sourceCore.envTypes
    envCtors := E.sourceCore.envCtors
    source := ?source
    formation := VerifyInductive.NestedFormationWF.withRecs recs B.formationAssembly.formation
    auxiliaries := auxiliaries
    containers := hcontainers
    block := block
    compiled := hcompiled
    recsOf := hrecsOf
    ivals := E.restoration.ivals
    rvals := E.restoration.rvals
    trTypes := E.trTypes B hBlowered
    envR := envR
    recsAdded := hrecsAdded
    trRecs := htrRecs
    order := E.restoration.entries
    order_perm := hperm
    fresh := hfresh
    map_eq := hmap
    quotInit_eq := hquot
    newUnsafe := E.newUnsafe
    recs_wf := hrecs_wf
    rec_shape := hrec_shape
    rules_nodup := hrules_nodup
    rules_ctor := hrules_ctor
    rules_ctorParams := hrules_ctorParams
    rule_shape := hrule_shape
    rules_closed := hrules_closed
    outVEnv := outVEnv
    rulesAdded := hrulesAdded
    recShapes := hrecShapes
    recK := hrecK
    runDecl := runDecl
    run := E
    run_decl := ?run_decl
    sourceSyntaxChecked := Hchecked
    constructorArityPrefix := ?arity
    recMajor := E.recMajor wf Hchecked
    constructorParameterAlignment := E.constructorParameterAlignment B hBlowered wf Hchecked
      (henvR ▸ VEnv.addRules_le hrulesAdded)
    restoredEquationsWF := hequationsWF }⟩
  case arity =>
    have h := B.formationAssembly.constructorArityPrefix
    rw [B.formationExpanded, hBlowered] at h
    exact h
  case run_decl => simp [VInductDecl.withRecs]
  case source =>
    have h := E.sourceCore.core
    rw [E.sourceCoreDecl_eq] at h
    exact TrInductDeclCore.withRecs h recs

end VerifyInductive
end Lean4Lean
