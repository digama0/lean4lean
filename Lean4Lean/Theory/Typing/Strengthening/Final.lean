import Lean4Lean.Theory.Typing.Strengthening.Descents
import Lean4Lean.Theory.Typing.Strengthening.SpineClosure
import Lean4Lean.Theory.Typing.Strengthening.MajorEta
import Lean4Lean.Theory.Typing.Strengthening.Unfolding

/-! # Typing strengthening: the final theorem

Direction F. Under `env.WF` and canonical `Eq`:

```
Strengthening ⇔ Cancel ⇔ TypedFront
```

given three environment-level typing facts about closed terms, each a `def` with a docstring in
its file:

* `GenericTypesTyped₀` (`Closures.lean`): the generic case type of every registered schema is
  typed at a sort in `[]`; it gives `ElimFrontN`, the component of `Cancel` for eliminator
  symbols (exact variant: `cancel_iff_typedFront_and_elim`, with `ElimFrontN` itself, which
  `Cancel` implies);
* `GenericRulesTyped₀` (`Closures.lean`): the generic case equations are typed in `[]`; with
  `TypedFront` it gives the descent of the case-iota guard (`caseRedexDescends`);
* `ProjFieldFrontPropN` (`SpineExposure.lean`): the field-type closure for structures whose sort
  is not never-zero (free outside `Prop`, `projField_of_neverZero`); it gives `ProjFrontN`
  through spine exposure and the descent of the composite major-eta step (`majorEtaDescends`),
  whose structure eta step below needs the projections of the major typed below.

All reduction guards descend from `TypedFront`: stored-rule checks (`Check.OK.descend`), case
iota (`caseRedexDescends`), prefix unfolding (`DeltaPar.descend'`) and the composite major-eta
step (`majorEtaDescends`); eta is handled by the eta-normal closure (`upStepFClosure`). -/

namespace Lean4Lean.VEnv.StrengtheningFinal
open VExpr VEnv.StrengtheningTypingFront VEnv.StrengtheningReplay VEnv.StrengtheningExposure
  VEnv.StrengtheningEtaNormal VEnv.StrengtheningEtaPostponement VEnv.StrengtheningEtaClosure
  VEnv.StrengtheningSpineExposure VEnv.StrengtheningClosures VEnv.StrengtheningDescents
  VEnv.StrengtheningSpineClosure VEnv.StrengtheningMajorEta VEnv.StrengtheningUnfolding

variable {env : VEnv}

/-- The guard descents from the typed front: the case-iota guard (`caseRedexDescends`) and the
composite major-eta step (`majorEtaDescends`), at every universe bound. -/
theorem descents_of_typedFront (henv : env.WF) (heq : env.HasCanonicalEq)
    (hTF : StrengtheningKripke.TypedFront env) (hRules : GenericRulesTyped₀ env)
    (hField : ProjFieldFrontN env) :
    (∀ U, @CaseRedexDescends (henv.params U)) ∧ (∀ U, @MajorEtaDescends (henv.params U)) := by
  have hTFN := (typedFrontN_iff_typedFront henv heq).mpr hTF
  have hcase : ∀ U, @CaseRedexDescends (henv.params U) := fun U =>
    letI := henv.params U
    caseRedexDescends hTFN hRules
  refine ⟨hcase, fun U => ?_⟩
  letI := henv.params U
  exact majorEtaDescends hTFN (hcase U) (fun hp => Params.checkVars henv U hp) hField

/-- Reduction-form `Π`-exposure from the typed front: path replay through the eta-normal closure,
then descent of the recorded steps at the root of the lift. -/
theorem piExposureRed_final (henv : env.WF) (heq : env.HasCanonicalEq)
    (hTF : StrengtheningKripke.TypedFront env) (hRules : GenericRulesTyped₀ env)
    (hField : ProjFieldFrontN env) : PiExposureRedN henv := by
  intro U k Γ Γ' f F u A B W hΓ hΓ' _ hF hr
  letI := henv.params U
  obtain ⟨F', hred, hne⟩ := path_replayNE (etaReplayNE_of_closure upStepFClosure) W hΓ hΓ' hF
    (FullReduction.upSteps hr)
  have hTFN := (typedFrontN_iff_typedFront henv heq).mpr hTF
  obtain ⟨hcase, hmajor⟩ := descents_of_typedFront henv heq hTF hRules hField
  obtain ⟨A₀, B₀, hred'⟩ := EtaNE.forallE_inv_lift' heq hTFN (hcase U)
    (fun hp => Params.checkVars henv U hp) (hmajor U) W hΓ hΓ' (hred.hasType hΓ hF) hne
  exact ⟨A₀, B₀, hred.trans hred'⟩

/-- Reduction-form spine exposure from the typed front. -/
theorem spineExposureRed_final (henv : env.WF) (heq : env.HasCanonicalEq)
    (hTF : StrengtheningKripke.TypedFront env) (hRules : GenericRulesTyped₀ env)
    (hField : ProjFieldFrontN env) : SpineExposureRedN henv := by
  intro U k Γ Γ' f F u S ls args W hΓ hΓ' _ hF hr
  letI := henv.params U
  obtain ⟨F', hred, hne⟩ := path_replayNE (etaReplayNE_of_closure upStepFClosure) W hΓ hΓ' hF
    (FullReduction.upSteps hr)
  have hTFN := (typedFrontN_iff_typedFront henv heq).mpr hTF
  obtain ⟨hcase, hmajor⟩ := descents_of_typedFront henv heq hTF hRules hField
  obtain ⟨args₀, hred'⟩ := EtaNE.const_spine_inv_lift' heq hTFN (hcase U)
    (fun hp => Params.checkVars henv U hp) (hmajor U) W hΓ hΓ' (hred.hasType hΓ hF) hne
  exact ⟨args₀, hred.trans hred'⟩

/-- `TypedFront → Cancel` given the generic rule typings, the field-type closure in `Prop` and
the eliminator closure. -/
theorem cancel_of_typedFront_final (henv : env.WF) (heq : env.HasCanonicalEq)
    (hTF : StrengtheningKripke.TypedFront env) (hRules : GenericRulesTyped₀ env)
    (hField : ProjFieldFrontPropN env) (hElim : ElimFrontN env) : Cancel env := by
  have hFieldN := ProjFieldFrontN.of_notNeverZero henv hField
  exact cancel_of_piExposureRed henv heq (piExposureRed_final henv heq hTF hRules hFieldN)
    ((typeFrontN_iff_typedFront henv heq).mpr hTF)
    (ProjFrontN.of_spineExposure henv heq (spineExposureRed_final henv heq hTF hRules hFieldN)
      hFieldN) hElim

/-- `Cancel ↔ TypedFront ∧ ElimFrontN`, given the generic rule typings and the field-type closure
in `Prop`. The `ElimFrontN` component is exact: `Cancel` implies it
(`cancel_iff_typedFront_and_closures`). -/
theorem cancel_iff_typedFront_and_elim (henv : env.WF) (heq : env.HasCanonicalEq)
    (hRules : GenericRulesTyped₀ env) (hField : ProjFieldFrontPropN env) :
    Cancel env ↔ StrengtheningKripke.TypedFront env ∧ ElimFrontN env := by
  constructor
  · intro hc
    have h := (cancel_iff_typedFront_and_closures henv heq).mp hc
    exact ⟨h.1, h.2.2.2⟩
  · rintro ⟨hTF, hElim⟩
    exact cancel_of_typedFront_final henv heq hTF hRules hField hElim

/-- The final theorem: under `WF` and canonical `Eq`, `Cancel ↔ TypedFront` given the generic
type and rule typings of the registered case schemas and the field-type closure for structures
in `Prop`. -/
theorem cancel_iff_typedFront_final (henv : env.WF) (heq : env.HasCanonicalEq)
    (hGen : GenericTypesTyped₀ env) (hRules : GenericRulesTyped₀ env)
    (hField : ProjFieldFrontPropN env) :
    Cancel env ↔ StrengtheningKripke.TypedFront env :=
  ⟨fun hc => ((cancel_iff_typedFront_and_elim henv heq hRules hField).mp hc).1,
    fun hTF => (cancel_iff_typedFront_and_elim henv heq hRules hField).mpr
      ⟨hTF, ElimFrontN.of_generic henv hGen⟩⟩

/-- Typing strengthening itself, in the same terms. -/
theorem strengthening_iff_typedFront_final (henv : env.WF) (heq : env.HasCanonicalEq)
    (hGen : GenericTypesTyped₀ env) (hRules : GenericRulesTyped₀ env)
    (hField : ProjFieldFrontPropN env) :
    env.Strengthening ↔ StrengtheningKripke.TypedFront env :=
  (strengthening_iff_cancel henv).trans (cancel_iff_typedFront_final henv heq hGen hRules hField)

end Lean4Lean.VEnv.StrengtheningFinal
