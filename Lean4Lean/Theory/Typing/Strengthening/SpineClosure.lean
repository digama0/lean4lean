import Lean4Lean.Theory.Typing.Strengthening.EtaClosure
import Lean4Lean.Theory.Typing.Strengthening.Closures

/-! # Typing strengthening: spine exposure over the eta-normal closure

Direction F. Direction E derived the projection
closure `ProjFrontN` from `EtaReplay` (`SpineExposure.lean`), which B3 refuted
(`not_etaReplay`). This file restates E's spine exposure over the proved closure of the eta-normal
relation (`upStepFClosure`, `EtaClosure.lean`), mirroring `piExposureRed_of_etaReplayNE`:

* `LStep.chain_descend`: a chain of recorded left steps at the root of a lift descends, one
  step at a time (`ParRed.descend`, `DeltaPar.descend`, `MajorEtaIotaC.descend`);
* `EtaNE.const_spine_inv_lift`: a lift of a type related to a constant spine reduces below to a
  spine with the same head and levels (`EtaNE.const_spine_inv`, the structure-eta alternative
  excluded by the sort typing);
* `spineExposureRed_of_closure : SpineExposureRedN` and `ProjFrontN.of_closure`, with the same
  hypotheses as `cancel_iff_typedFront_B3` plus `ProjFieldFrontN`. -/

namespace Lean4Lean.VEnv.StrengtheningSpineClosure
open VExpr VEnv.StrengtheningTypingFront VEnv.StrengtheningReplay VEnv.StrengtheningExposure
  VEnv.StrengtheningEtaNormal VEnv.StrengtheningEtaPostponement VEnv.StrengtheningEtaClosure
  VEnv.StrengtheningSpineExposure VEnv.StrengtheningClosures

variable {env : VEnv}

section
open VEnv.Params
variable [VEnv.Params]

/-- A chain of recorded left steps (`LStep`) from the lift of a term typed below descends: each
step is an eta-free parallel step (`ParRed.descend`, `DeltaPar.descend`) or a composite
major-eta-then-fire step (`MajorEtaIotaC.descend`). -/
theorem LStep.chain_descend (hTF : TypedFrontN Params.env) (hcase : CaseRedexDescends)
    (hunfold : UnfoldingCheckDescends)
    (hcv : ∀ {p : Pattern} {r : p.RHS × p.Check}, Pat p r → CheckVars r.2)
    (hmajor : MajorEtaDescends) {k : Nat} {Γ Γ' : List VExpr} {e T s' : VExpr}
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (he : Params.env.HasType univs Γ e T)
    (H : ReflTransGen (LStep Γ') (e.liftN 1 k) s') :
    ∃ e', s' = e'.liftN 1 k ∧ FullReduction Γ e e' := by
  generalize hs : e.liftN 1 k = s at H
  induction H using ReflTransGen.headIndOn generalizing e with
  | rfl => exact ⟨e, hs.symm, .rfl⟩
  | head step tail ih =>
    subst hs
    rcases step with (h | h) | h
    · obtain ⟨e₁, rfl, h'⟩ := ParRed.descend hTF hcase hcv W hΓ hΓ' he h
      obtain ⟨e', rfl, hred⟩ := ih ((FullStep.core h').hasType hΓ he) rfl
      exact ⟨e', rfl, (ReflTransGen.tail .rfl (.core h')).trans hred⟩
    · obtain ⟨e₁, rfl, h'⟩ := DeltaPar.descend hTF hunfold W hΓ hΓ' he h
      obtain ⟨e', rfl, hred⟩ := ih (h'.full.hasType hΓ he) rfl
      exact ⟨e', rfl, h'.full.trans hred⟩
    · obtain ⟨e₁, rfl, h'⟩ := MajorEtaIotaC.descend hmajor W hΓ hΓ' he h
      obtain ⟨e', rfl, hred⟩ := ih (h'.hasType hΓ he) rfl
      exact ⟨e', rfl, h'.trans hred⟩

/-- A lift of a type related (`EtaNE`) to a constant spine reduces below to a spine with the
same head and levels: the recorded steps at the root descend, and the structure-eta alternative
of `EtaNE.const_spine_inv` is excluded by the sort typing. -/
theorem EtaNE.const_spine_inv_lift (hTF : TypedFrontN Params.env) (hcase : CaseRedexDescends)
    (hunfold : UnfoldingCheckDescends)
    (hcv : ∀ {p : Pattern} {r : p.RHS × p.Check}, Pat p r → CheckVars r.2)
    (hmajor : MajorEtaDescends) {k : Nat} {Γ Γ' : List VExpr} {F : VExpr} {u : VLevel}
    {S : Name} {ls : List VLevel} {args : List VExpr}
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (hF : Params.env.HasType univs Γ F (.sort u))
    (H : EtaNE Γ' (F.liftN 1 k) (mkApps (.const S ls) args)) :
    ∃ args₀, FullReduction Γ F (mkApps (.const S ls) args₀) := by
  obtain ⟨s', hch, hc⟩ := EtaNE.const_spine_inv hΓ' H (hF.weakN henv.ordered W) rfl
  obtain ⟨F', rfl, hred⟩ := LStep.chain_descend hTF hcase hunfold hcv hmajor W hΓ hΓ' hF hch
  have hF' : Params.env.HasType univs Γ' (F'.liftN 1 k) (.sort u) :=
    (hred.hasType hΓ hF).weakN henv.ordered W
  rcases hc with ⟨args_s, hs, -⟩ | ⟨family, info, params, hl, -, -, -, hs', -, -, -⟩
  · obtain ⟨args₀, rfl, -⟩ := liftN_eq_mkApps_const_inv hs
    exact ⟨args₀, hred⟩
  · exact (type_not_structure hΓ' hF' hl hs').elim

end

/-- Reduction-form spine exposure from the typed front, the guard descents and the proved
closure `upStepFClosure` (the `EtaNE` form of direction E's `spineExposureRed_of_etaReplay`,
whose hypothesis `EtaReplay` is false). -/
theorem spineExposureRed_of_closure (henv : env.WF) (heq : env.HasCanonicalEq)
    (hTF : StrengtheningKripke.TypedFront env)
    (hcase : ∀ U, @CaseRedexDescends (henv.params U))
    (hunfold : ∀ U, @UnfoldingCheckDescends (henv.params U))
    (hmajor : ∀ U, @MajorEtaDescends (henv.params U)) : SpineExposureRedN henv := by
  intro U k Γ Γ' f F u S ls args W hΓ hΓ' _ hF hr
  letI := henv.params U
  obtain ⟨F', hred, hne⟩ := path_replayNE (etaReplayNE_of_closure upStepFClosure) W hΓ hΓ' hF
    (FullReduction.upSteps hr)
  obtain ⟨args₀, hred'⟩ := EtaNE.const_spine_inv_lift
    ((typedFrontN_iff_typedFront henv heq).mpr hTF) (hcase U) (hunfold U)
    (fun hp => Params.checkVars henv U hp) (hmajor U) W hΓ hΓ' (hred.hasType hΓ hF) hne
  exact ⟨args₀, hred.trans hred'⟩

/-- The projection closure from the proved eta closure, the guard descents and the field-type
closure, with no false hypothesis. -/
theorem ProjFrontN.of_closure (henv : env.WF) (heq : env.HasCanonicalEq)
    (hTF : StrengtheningKripke.TypedFront env)
    (hcase : ∀ U, @CaseRedexDescends (henv.params U))
    (hunfold : ∀ U, @UnfoldingCheckDescends (henv.params U))
    (hmajor : ∀ U, @MajorEtaDescends (henv.params U))
    (hField : ProjFieldFrontN env) : ProjFrontN env :=
  ProjFrontN.of_spineExposure henv heq
    (spineExposureRed_of_closure henv heq hTF hcase hunfold hmajor) hField

end Lean4Lean.VEnv.StrengtheningSpineClosure
