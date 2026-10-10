import Lean4Lean.Verify.Inductive.Nested.Install.Result
import Lean4Lean.Verify.Inductive.Nested.Restoration.Restore
import Lean4Lean.Verify.Inductive.Dispatch

/-! # The nested branch of `addInductiveAfterLowering`

`nestedInductivePreserves` proves wave 2's hypothesis `NestedInductivePreserves` through the
nested pipeline: the ordinary pipeline on the lowered block (`AddInductive.run.loweredRun`),
the restoration steps (`Environment.restoreNestedAfterInstall.WF`), the lowering's
certificate (`loweringRun.WF`), the restored block (`nestedRestoredBlock`), its
environment-side facts (`RestoredBlock.installedFacts`) and the installation of its block
certificate (`NestedCertificate.inductiveExtension`). The dispatch theorems of
`Dispatch.lean` then hold without hypothesis (`addInductiveDeclaration.spec`,
`addInductiveDeclaration.preserves`), and `addDecl.WF` (`Verify/Environment.lean`) loses its
last one. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- **The nested branch.** -/
theorem nestedInductivePreserves : NestedInductivePreserves := by
  intro env lparams nparams sourceTypes isUnsafe fuel res ves wf Hsources Hlower hnested
  have Hout := loweringRun.WF wf Hsources Hlower -- WAVE 3 COMPAT (lowering)
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
  -- WAVE 3 eqinst COMPAT: the base translation, complete blocks and alignment from `wf`
  have I := B.installedFacts Hout.source_nonempty hvisible wf.tr wf.blocks
    wf.constructorParameterAlignment
  exact (NestedCertificate.ofRestoredBlock B I Hout.source_nonempty).inductiveExtension wf

/-- `addInductiveDeclaration.WF_spec` without hypothesis. -/
theorem addInductiveDeclaration.spec {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig) (HsourcesB : SourceBVarClosed types) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun outEnv =>
        Nonempty (InductiveExtension env outEnv ves lparams nparams types isUnsafe) :=
  addInductiveDeclaration.WF_spec nestedInductivePreserves wf lparams nparams types isUnsafe fuel
    HsourcesB

/-- `addInductiveDeclaration.WF_preserves` without hypothesis. -/
theorem addInductiveDeclaration.preserves {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun outEnv =>
        ∃ ves' : VEnvs, ves'.WF outEnv ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety :=
  addInductiveDeclaration.WF_preserves nestedInductivePreserves wf lparams nparams types isUnsafe
    fuel

end VerifyInductive
end Lean4Lean
