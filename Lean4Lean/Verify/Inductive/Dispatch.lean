import Lean4Lean.Verify.Inductive.Install.OrdinaryExtension
import Lean4Lean.Verify.Inductive.Primitive.Extension

/-! # Dispatch of inductive declarations

The primitive, ordinary and nested paths each produce an `InductiveExtension`; this file
combines them along the executable's own branch selection (section 3.1 of the design notes):
the primitive recognizer first (`Primitive.checkInductive`), then the number of auxiliary
families returned by lowering (`res.aux2nested.size`).

The nested branch is the hypothesis `NestedInductivePreserves` (wave 3 proves it, as the source
branch's `Environment.addInductiveAfterLowering.nestedInductiveExtensionWF`); everything else is
proved from the ordinary and primitive pipelines. `Verify/Environment.lean` consumes
`addInductiveDeclaration.WF_preserves` for `addDecl.WF`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The nested branch of `addInductiveAfterLowering`: a lowering result with auxiliary families
(after the source checks) is restored and validated into an extension of the model for the
submitted source declaration. Wave 3 (`Nested/**`) proves this statement. -/
def NestedInductivePreserves : Prop :=
  ∀ (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (res : ElimNestedInductive.Result) (ves : VEnvs), ves.WF env →
    SourceSyntaxChecks env sourceTypes →
    loweringRun env fuel.inductiveFuel nparams sourceTypes lparams = .ok res →
    res.aux2nested.size ≠ 0 →
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe false fuel res).WF fun outEnv =>
        Nonempty (InductiveExtension env outEnv ves lparams nparams sourceTypes isUnsafe)

/-- `InductiveExtension` for the ordinary branch after lowering (no auxiliary families). -/
theorem Environment.addInductiveAfterLowering.ordinaryInductiveExtensionWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WF env)
    (htypes : res.types = sourceTypes) (hnonempty : sourceTypes ≠ [])
    (haux : res.aux2nested.size = 0) :
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe false fuel res).WF fun outEnv =>
        Nonempty (InductiveExtension env outEnv ves lparams nparams sourceTypes isUnsafe) :=
  (Environment.addInductiveAfterLowering.ordinaryExtensionModelWF
    env lparams nparams sourceTypes isUnsafe fuel res ves wf htypes hnonempty haux).mono
      fun _ ⟨ves', wf', hle, ⟨Hspec⟩⟩ => ⟨InductiveExtension.ofModel ves' wf' hle Hspec⟩

/-- `InductiveExtension` for `Environment.addInductive` on the canonical primitive
Bool/Nat declarations. -/
theorem Environment.addInductive.primitiveInductiveExtensionWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe) :
    (Environment.addInductive env lparams nparams types isUnsafe true fuel).WF fun outEnv =>
      Nonempty (InductiveExtension env outEnv ves lparams nparams types isUnsafe) := by
  have hisUnsafe : isUnsafe = false := Hshape.isUnsafe_eq
  subst isUnsafe
  exact (Environment.addInductive.primitiveExtensionModelWF
      env lparams nparams types false fuel ves wf Hshape).mono
    fun _ ⟨ves', wf', hle, ⟨Hspec⟩⟩ =>
      ⟨{ targetModels := ves', wf := wf', mono := hle, specification := Hspec }⟩

/-- Dispatch over the actual lowering result. The source-facing specification requires the
source declaration to have no loose bound variables (`SourceBVarClosed`): lowering re-closes
constructor types over the opened parameters, which would silently repair such variables, so
the checked block is literally the source only under that hypothesis. The case without
auxiliary families is the ordinary branch; otherwise the nested branch receives the checked
lowering output selected by execution. -/
theorem Environment.addInductive.inductiveExtensionWF
    (hnested : NestedInductivePreserves)
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env)
    (HsourcesB : SourceBVarClosed types) :
    (Environment.addInductive env lparams nparams types isUnsafe false fuel).WF fun outEnv =>
      Nonempty (InductiveExtension env outEnv ves lparams nparams types isUnsafe) := by
  refine Environment.addInductive.WF env lparams nparams types isUnsafe false fuel _
    fun res Hsources Hlower => ?_
  by_cases haux : res.aux2nested.size = 0
  · -- WAVE 3 COMPAT (lowering): the lowering consequences take `wf` and `Hsources`
    have htypes := loweringRun.ordinary_types_eq_source wf Hsources HsourcesB Hlower haux
    exact Environment.addInductiveAfterLowering.ordinaryInductiveExtensionWF
      env lparams nparams types isUnsafe fuel res ves wf htypes
      (htypes ▸ loweringRun.types_nonempty wf Hsources Hlower) haux
  · exact hnested env lparams nparams types isUnsafe fuel res ves wf Hsources Hlower haux

/-- Model preservation alone for the non-primitive branch, without any hypothesis on the source
syntax: the ordinary branch installs whatever lowering produced. -/
theorem Environment.addInductive.preservesWF
    (hnested : NestedInductivePreserves)
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env) :
    (Environment.addInductive env lparams nparams types isUnsafe false fuel).WF fun outEnv =>
      ∃ ves' : VEnvs, ves'.WF outEnv ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  refine Environment.addInductive.WF env lparams nparams types isUnsafe false fuel _
    fun res Hsources Hlower => ?_
  by_cases haux : res.aux2nested.size = 0
  · exact Environment.addInductiveAfterLowering.ordinaryInstalledModelWF
      env lparams nparams types isUnsafe fuel res ves wf
      (loweringRun.types_nonempty wf Hsources Hlower) haux -- WAVE 3 COMPAT (lowering)
  · exact (hnested env lparams nparams types isUnsafe fuel res ves wf Hsources Hlower haux).mono
      fun _ ⟨E⟩ => E.modelExtension

/-- Dispatch of an inductive declaration: `addDecl` satisfies `Q` if, for every result
`allowPrimitive` of the primitive-family precheck `Primitive.checkInductive`, the call to
`Environment.addInductive` with that bit does. The premise keeps the precheck so that the
verified continuation receives the same `allowPrimitive` bit as the executable branch. -/
theorem addInductiveDeclaration.WF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (Q : Environment → Prop)
    (Hadd : ∀ allowPrimitive,
      Primitive.checkInductive env lparams nparams types isUnsafe = .ok allowPrimitive →
      (Environment.addInductive env lparams nparams types isUnsafe allowPrimitive fuel).WF Q) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF Q := by
  have Hcheck : (Primitive.checkInductive env lparams nparams types isUnsafe).WF
      fun allowPrimitive =>
        (Environment.addInductive env lparams nparams types isUnsafe allowPrimitive fuel).WF Q :=
    fun allowPrimitive hallow => Hadd allowPrimitive hallow
  simpa [addDecl] using Hcheck.bind fun _ Hrun => Hrun

/-- The source-facing specification of a checked inductive declaration: the output environment
has a well-formed model extending the source models and carrying the
`InductiveExtension` of the submitted declaration. The executable primitive precheck selects the
primitive path for the canonical `Bool`/`Nat` declarations and the ordinary or nested path
otherwise. -/
theorem addInductiveDeclaration.WF_spec
    (hnested : NestedInductivePreserves)
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig)
    (HsourcesB : SourceBVarClosed types) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun outEnv =>
        Nonempty (InductiveExtension env outEnv ves lparams nparams types isUnsafe) := by
  apply addInductiveDeclaration.WF env lparams nparams types isUnsafe fuel
  intro allowPrimitive hcheck
  cases allowPrimitive with
  | true =>
    exact Environment.addInductive.primitiveInductiveExtensionWF env lparams nparams types
      isUnsafe fuel ves wf ((checkPrimitiveInductive_eq_true_iff env lparams nparams types
        isUnsafe).mp hcheck)
  | false =>
    exact Environment.addInductive.inductiveExtensionWF hnested env lparams nparams types
      isUnsafe fuel ves wf HsourcesB

/-- A checked inductive declaration, at any fuel, preserves the invariant `VEnvs.WF` and extends
every safety-indexed abstract environment (the statement `InductiveDeclPreserves` of
`Verify/Environment.lean`), given the nested branch. -/
theorem addInductiveDeclaration.WF_preserves
    (hnested : NestedInductivePreserves)
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun outEnv =>
        ∃ ves' : VEnvs, ves'.WF outEnv ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  apply addInductiveDeclaration.WF env lparams nparams types isUnsafe fuel
  intro allowPrimitive hcheck
  cases allowPrimitive with
  | true =>
    exact (Environment.addInductive.primitiveInductiveExtensionWF env lparams nparams types
      isUnsafe fuel ves wf ((checkPrimitiveInductive_eq_true_iff env lparams nparams types
        isUnsafe).mp hcheck)).mono fun _ ⟨E⟩ => E.modelExtension
  | false =>
    exact Environment.addInductive.preservesWF hnested env lparams nparams types isUnsafe fuel
      ves wf

end VerifyInductive
end Lean4Lean
