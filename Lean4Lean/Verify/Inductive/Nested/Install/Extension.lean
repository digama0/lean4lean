import Lean4Lean.Verify.Inductive.Nested.Install.Result
import Lean4Lean.Verify.Inductive.Nested.Restoration.Restore
import Lean4Lean.Verify.Inductive.Install.OrdinaryExtension

/-! # The nested branch of `addInductiveAfterLowering`

`Environment.addInductiveAfterLowering.nestedInductiveExtensionWF`: a lowering result with
auxiliary families is restored and validated into an extension of the model for the submitted
source declaration. The proof composes the ordinary pipeline on the lowered block
(`AddInductive.run.loweredRun`), the restoration steps (`Environment.restoreNestedAfterInstall.WF`),
the lowering's certificate (`loweringRun.WF`), the restored block (`nestedRestoredBlock`), its
environment-side facts (`RestoredBlock.installedFacts`) and the installation of its block
certificate (`NestedCertificate.inductiveExtension`). `Dispatch.lean` selects this branch. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- **The nested branch.** -/
theorem Environment.addInductiveAfterLowering.nestedInductiveExtensionWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (res : ElimNestedInductive.Result) (ves : VEnvs) (wf : ves.WF env)
    (Hsources : SourceSyntaxChecks env sourceTypes)
    (Hlower : loweringRun env fuel.inductiveFuel nparams sourceTypes lparams = .ok res)
    (hnested : res.aux2nested.size ≠ 0) :
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe false fuel res).WF fun outEnv =>
        Nonempty (InductiveExtension env outEnv ves lparams nparams sourceTypes isUnsafe) := by
  have Hout := loweringRun.WF wf Hsources Hlower
  let safety : DefinitionSafety := if isUnsafe then .unsafe else .safe
  let c := initialContext env lparams safety false fuel
  let Hc : ContextWF c := ContextWF.initial wf safety lparams false fuel
  have hnotPartial : c.safety ≠ .partial := by
    cases isUnsafe <;> simp [c, safety, initialContext]
  have hvisible : c.safety ≤ (if isUnsafe then DefinitionSafety.unsafe else .safe) := by
    cases isUnsafe <;> exact DefinitionSafety.le_rfl
  have Hrun := AddInductive.run.loweredRun (c := c) Hc nparams res.aux2nested.size res.types
    wf.inductivesClosed wf.listedConstructorsPresent rfl Hout.types_size_pos hnotPartial rfl
  unfold Environment.addInductiveAfterLowering
  show (AddInductive.run nparams res.types res.aux2nested.size c >>= fun env' =>
    if res.aux2nested.size = 0 then pure env' else
      Environment.restoreNestedAfterInstall env env' lparams sourceTypes safety false fuel
        res).WF _
  refine Except.WF.bind Hrun fun loweredEnv ⟨L⟩ => ?_
  rw [if_neg hnested]
  refine (Environment.restoreNestedAfterInstall.WF env loweredEnv lparams sourceTypes safety
    false fuel res).mono fun outEnv V => ?_
  obtain ⟨B⟩ := nestedRestoredBlock wf Hsources Hout hnested L V
  -- the base translation, complete blocks and alignment from `wf`
  have I := B.installedFacts Hout.source_nonempty hvisible wf.tr wf.blocks
    wf.constructorParameterAlignment
  exact (NestedCertificate.ofRestoredBlock B I Hout.source_nonempty).inductiveExtension wf

end VerifyInductive
end Lean4Lean
