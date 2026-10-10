import Lean4Lean.Verify.Inductive.Install.Ordinary
import Lean4Lean.Verify.Inductive.Lowering

/-! The ordinary path of section 3.1 of the design notes: a successful ordinary run extends the
safety-indexed environment model, and a lowering result without auxiliary families leaves the
source declaration literally unchanged, so the ordinary branch of `addInductiveAfterLowering`
yields an `InductiveExtension` for the submitted declaration.

Wave 2 scaffold: owned by the `Install/` agent; the glue is in place, the assembly of the
block certificate (`RecursorCheck.blockCertificate`) and its installation
(`BlockCertificate.extend*Exact`) are the named stubs of `Install/BlockCertificate.lean`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A successful safe ordinary run extends the complete safety-indexed model. -/
theorem OrdinaryInstallation.extendSafeExact {ves : VEnvs}
    (Hrun : OrdinaryInstallation c stats nparams depth indTypes isUnsafe sourceEnv outEnv)
    (wf : ves.WF c.env) (hsafety : c.safety = .safe) (hsource : sourceEnv = ves.venv .safe)
    (hproduction : isUnsafe = (c.safety != .safe)) (hnonempty : indTypes.toList ≠ []) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      Nonempty (SourceAddInduct (ves.venv .safe) c.lparams nparams indTypes.toList isUnsafe
        (ves'.venv .safe)) := by
  subst hsource
  obtain ⟨decl, ctorEnv, R, ⟨H⟩⟩ := Hrun
  obtain ⟨B⟩ := H.blockCertificate H.generatedRuleTranslation hnonempty
  rw [hsafety] at B
  have hsafe : H.decl'.isUnsafe = false := by
    show decl.isUnsafe = false
    rw [R.core.isUnsafe, hproduction, hsafety]; rfl
  obtain ⟨ves', wf', hle, heq⟩ := B.extendSafeExact wf hsafe
  refine ⟨ves', wf', hle, ⟨?_⟩⟩
  exact { decl := H.decl'
          envTypes := R.headerVEnv
          envCtors := R.ctorVEnv
          source := TrInductDeclCore.withRecs R.core H.recs
          wf := B.wf
          installed := heq ▸ B.installed }

/-- A successful unsafe ordinary run extends the unsafe model and is hidden from the partial and
safe observers. -/
theorem OrdinaryInstallation.extendUnsafeExact {ves : VEnvs}
    (Hrun : OrdinaryInstallation c stats nparams depth indTypes isUnsafe sourceEnv outEnv)
    (wf : ves.WF c.env) (hsafety : c.safety = .unsafe) (hsource : sourceEnv = ves.venv .unsafe)
    (hproduction : isUnsafe = (c.safety != .safe)) (hnonempty : indTypes.toList ≠ []) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      Nonempty (SourceAddInduct (ves.venv .unsafe) c.lparams nparams indTypes.toList isUnsafe
        (ves'.venv .unsafe)) := by
  subst hsource
  obtain ⟨decl, ctorEnv, R, ⟨H⟩⟩ := Hrun
  obtain ⟨B⟩ := H.blockCertificate H.generatedRuleTranslation hnonempty
  rw [hsafety] at B
  have hunsafe : H.decl'.isUnsafe = true := by
    show decl.isUnsafe = true
    rw [R.core.isUnsafe, hproduction, hsafety]; rfl
  obtain ⟨ves', wf', hle, heq⟩ := B.extendUnsafeExact wf hunsafe
  refine ⟨ves', wf', hle, ⟨?_⟩⟩
  exact { decl := H.decl'
          envTypes := R.headerVEnv
          envCtors := R.ctorVEnv
          source := TrInductDeclCore.withRecs R.core H.recs
          wf := B.wf
          installed := heq ▸ B.installed }

/-- The ordinary run result extends the model, with the independent source judgment. -/
theorem OrdinaryRunResult.extendWithSpecification {ves : VEnvs} {source : AddInductive.Context}
    {Hsource : ContextWF source}
    (Hrun : OrdinaryRunResult source Hsource nparams types outEnv)
    (wf : ves.WF source.env) (hsource : Hsource.venv = ves.venv source.safety)
    (hnotPartial : source.safety ≠ .partial) (hnonempty : types ≠ []) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      Nonempty (SourceAddInduct (ves.venv source.safety) source.lparams nparams types
        (source.safety != .safe)
        (ves'.venv (if source.safety != .safe then .unsafe else .safe))) := by
  obtain ⟨c', stats, Hc', P, Hphases⟩ := Hrun
  have wf' : ves.WF c'.env := by rw [P.env_eq]; exact wf
  have hnonempty' : types.toArray.toList ≠ [] := by simpa using hnonempty
  have hvenv : Hc'.venv = ves.venv source.safety := P.venv_eq.trans hsource
  have hproduction : (source.safety != .safe) = (c'.safety != .safe) := by rw [P.safety_eq]
  cases hs : source.safety with
  | «unsafe» =>
    have hcSafety : c'.safety = .unsafe := P.safety_eq.trans hs
    obtain ⟨ves', wf', hle, ⟨S⟩⟩ := OrdinaryInstallation.extendUnsafeExact Hphases wf'
      hcSafety (by rw [hvenv, hs]) hproduction hnonempty'
    refine ⟨ves', wf', hle, ⟨?_⟩⟩
    rw [hs, P.lparams_eq] at S
    simpa using S
  | safe =>
    have hcSafety : c'.safety = .safe := P.safety_eq.trans hs
    obtain ⟨ves', wf', hle, ⟨S⟩⟩ := OrdinaryInstallation.extendSafeExact Hphases wf'
      hcSafety (by rw [hvenv, hs]) hproduction hnonempty'
    refine ⟨ves', wf', hle, ⟨?_⟩⟩
    rw [hs, P.lparams_eq] at S
    simpa using S
  | «partial» => exact (hnotPartial hs).elim

/-- Complete ordinary refinement retaining the independent source judgment. -/
theorem AddInductive.run.extensionModelWF {ves : VEnvs} {c : AddInductive.Context}
    {types : List InductiveType}
    (nparams numNested : Nat) (Hc : ContextWF c) (wf : ves.WF c.env)
    (hsource : Hc.venv = ves.venv c.safety)
    (hctx : Hc.mlctx.vlctx = []) (hnonempty : types ≠ []) (HnotPartial : c.safety ≠ .partial)
    (Hinputs : ∀ {c' : AddInductive.Context} {stats : AddInductive.InductiveStats},
      (Hc' : ContextWF c') → HeaderPhase Hc nparams types.toArray c' Hc' stats →
      PrimitiveNamesFresh c' stats nparams numNested types.toArray (c.safety != .safe)) :
    (AddInductive.run nparams types numNested c).WF fun outEnv =>
      ∃ ves' : VEnvs, ves'.WF outEnv ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        Nonempty (OrdinarySourceAddInduct (ves.venv c.safety) c.lparams nparams types
          (c.safety != .safe) (ves'.venv (if c.safety != .safe then .unsafe else .safe))) := by
  have hsize : 0 < types.toArray.size := by
    cases htypes : types with
    | nil => simp [htypes] at hnonempty
    | cons _ _ => simp
  exact (AddInductive.run.sourceAlignedWF nparams numNested Hc wf.inductivesClosed
    wf.listedConstructorsPresent hctx hsize HnotPartial Hinputs).mono fun _ Hrun =>
      Hrun.extendWithSpecification wf hsource HnotPartial hnonempty

/-- Well-formedness of the ordinary (zero-auxiliary) branch alone. Unlike the
specification-facing endpoint below, this needs no closedness of the source syntax: the
checked block is whatever lowering produced. -/
theorem Environment.addInductiveAfterLowering.ordinaryInstalledModelWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WF env)
    (hnonempty : res.types ≠ [])
    (haux : res.aux2nested.size = 0) :
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe false fuel res).WF fun outEnv =>
        ∃ ves' : VEnvs, ves'.WF outEnv ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) := by
  let safety : DefinitionSafety := if isUnsafe then .unsafe else .safe
  let c := initialContext env lparams safety false fuel
  let Hc : ContextWF c := ContextWF.initial wf safety lparams false fuel
  have hnotPartial : c.safety ≠ .partial := by
    cases isUnsafe <;> simp [c, safety, initialContext]
  have Hrun := AddInductive.run.extensionModelWF (c := c) (types := res.types) (ves := ves)
    nparams 0 Hc wf rfl rfl hnonempty hnotPartial fun _ P =>
      PrimitiveNamesFresh.ofAllowPrimitiveFalse (P.allowPrimitive_eq.trans rfl)
  unfold Environment.addInductiveAfterLowering
  rw [haux]
  intro outEnv hout
  have hout' : AddInductive.run nparams res.types 0 c = .ok outEnv := by
    simpa [c, safety, initialContext] using hout
  obtain ⟨ves', wf', hle, -⟩ := Hrun outEnv hout'
  exact ⟨ves', wf', hle⟩

/-- Source-facing ordinary refinement of `addInductiveAfterLowering`: the successful source
checks and a zero-auxiliary lowering run prove that the block checked by `AddInductive.run` is
literally the source declaration. -/
theorem Environment.addInductiveAfterLowering.ordinaryExtensionModelWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WF env)
    (htypes : res.types = sourceTypes) (hnonempty : sourceTypes ≠ [])
    (haux : res.aux2nested.size = 0) :
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe false fuel res).WF fun outEnv =>
        ∃ ves' : VEnvs, ves'.WF outEnv ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          Nonempty (SourceAddInduct
            (ves.venv (if isUnsafe then .unsafe else .safe)) lparams nparams
            sourceTypes isUnsafe
            (ves'.venv (if isUnsafe then .unsafe else .safe))) := by
  let safety : DefinitionSafety := if isUnsafe then .unsafe else .safe
  let c := initialContext env lparams safety false fuel
  let Hc : ContextWF c := ContextWF.initial wf safety lparams false fuel
  have hnotPartial : c.safety ≠ .partial := by
    cases isUnsafe <;> simp [c, safety, initialContext]
  have Hrun := AddInductive.run.extensionModelWF (c := c) (types := res.types) (ves := ves)
    nparams 0 Hc wf rfl rfl (htypes ▸ hnonempty) hnotPartial fun _ P =>
      PrimitiveNamesFresh.ofAllowPrimitiveFalse (P.allowPrimitive_eq.trans rfl)
  unfold Environment.addInductiveAfterLowering
  rw [haux]
  intro outEnv hout
  have hout' : AddInductive.run nparams res.types 0 c = .ok outEnv := by
    simpa [c, safety, initialContext] using hout
  obtain ⟨ves', wf', hle, ⟨S⟩⟩ := Hrun outEnv hout'
  refine ⟨ves', wf', hle, ⟨?_⟩⟩
  rw [htypes] at S
  have hisUnsafe : (c.safety != .safe) = isUnsafe := by
    cases isUnsafe <;> rfl
  rw [hisUnsafe] at S
  simpa [c, safety, initialContext] using S

end VerifyInductive
end Lean4Lean
