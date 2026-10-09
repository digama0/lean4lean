import Lean4Lean.Theory.Typing.Strengthening.JoinRepair

/-! # Checked obstructions for proofs of `Cancel`

Each theorem here refutes one proposed route to `Cancel` precisely, or repairs one such
refutation:

* `eta_does_not_preserve_support`: `FullStep.funEta` can rewrite a closed term to one whose
  domain annotation mentions the inserted variable, so a direct descent of arbitrary
  `FullReduction` witnesses is impossible; `eta_obstruction_repaired`: this instance is
  repaired by choosing the supported domain and beta-reducing the bad one underneath.
* `compress_domain_equality`: `NormalEqN.lamDF` hides an arbitrary domain conversion at index
  one. `DomainCountedN` counts lambda domains and proof-irrelevance type comparisons and has
  admissible transitivity (`DomainCountedN.trans`), yet `alignment_can_be_hidden` shows it
  still hides arbitrary conversions through its freely chosen typing witnesses: the typing
  certificates themselves must be structural and counted.
* `no_source_only_substitution_bound`: a structural typing certificate cannot be bounded
  under substitution by the source certificate alone; a rank must be substitution-aware.
* `fixed_oi_counterexample`, `empty_domain_all_sets`, `fixed_target_not_reflecting`: the
  observation model's fixed-target interpretation does not reflect definitional equality
  (distinct variables have equal observations; every abstraction over an uninhabited domain
  has the same observations); `retraction_requires_inhabitant`: an identity-tail anchor into
  `Γ` supplies an inhabitant of the removed binder.

Astra's second-opinion derivations (2026-10-08), kernel-checked outside this repository as
`StrengtheningPartial_2026-10-08.lean` and
`StrengtheningContinuation_2026-10-08.lean`, adapted. -/

namespace Lean4Lean
namespace VEnv.StrengtheningObstructions
open VEnv VExpr

section EtaSupport
open VEnv.Params
variable [VEnv.Params]


theorem compress_domain_equality {Γ : List VExpr} {A B : VExpr} {u : VLevel}
    (H : env.IsDefEq univs Γ A B (.sort u)) :
    NormalEqN false 1 Γ (.lam A (.sort .zero)) (.lam B (.sort .zero)) :=
  .lamDF H.hasType.1 H (.refl (.sort trivial))

def idProp : VExpr := .lam (.sort .zero) (.bvar 0)
def badDomain : VExpr := .app (.lam (.sort .zero) (.sort .zero)) (.bvar 0)

theorem eta_does_not_preserve_support :
    ∃ t, FullStep [.sort .zero] idProp.lift t ∧ ¬t.Skips 1 0 := by
  have hs {Δ : List VExpr} : env.HasType univs Δ (.sort .zero) (.sort (.succ .zero)) :=
    .sort trivial
  have hx : env.HasType univs [.sort .zero] (.bvar 0) (.sort .zero) := .bvar .zero
  have hd : env.IsDefEq univs [.sort .zero] badDomain (.sort .zero) (.sort (.succ .zero)) :=
    .beta hs hx
  have hf : env.HasType univs [.sort .zero] idProp (.forallE (.sort .zero) (.sort .zero)) :=
    .lamDF hs (.bvar .zero)
  have hp := IsDefEq.forallEDF hd.symm (hs (Δ := [.sort .zero, .sort .zero]))
  have hf' : env.HasType univs [.sort .zero] idProp (.forallE badDomain (.sort .zero)) :=
    .defeqDF hp hf
  refine ⟨.lam badDomain (.app idProp.lift (.bvar 0)), ?_, ?_⟩
  · simpa [idProp, lift, liftN, liftVar] using FullStep.funEta hf'
  · simp [VExpr.skips_iff, VExpr.Skips', badDomain]
end EtaSupport


/-- An uninhabited domain has no typed key in the observation model's target context. -/
theorem no_typed_key {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} {Q : VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hQ : ∀ q, ¬ env.HasType U Γ q Q) {c : VExpr → Prop} :
    ¬ Model.TypedElCls env U Γ (Model.TyCls env U Γ Q) c := by
  rintro ⟨q, X, hX, hq, _⟩
  exact hQ q (Model.TyCls.defeq henv hΓ hX hq)

/-- This is about a fixed target context, not about all Kripke extensions. -/
theorem no_lam_observation {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} {Q body : VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hQ : ∀ q, ¬ env.HasType U Γ q Q) :
    ∀ o, ¬ Model.OI env U Γ (.lam Q body) o := by
  intro o ho
  obtain ⟨c, K, x, τs, p, _, hc, _⟩ := Model.Obs.lam_iff.mp ho
  simp only [VExpr.subst_id] at hc
  exact no_typed_key henv hΓ hQ hc

/-- Fixed-target observations identify any two abstractions over an uninhabited domain. -/
theorem empty_domain_observation_eq {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} {Q a b : VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hQ : ∀ q, ¬ env.HasType U Γ q Q) :
    Model.OI env U Γ (.lam Q a) = Model.OI env U Γ (.lam Q b) := by
  funext o
  exact propext ⟨fun h => (no_lam_observation henv hΓ hQ o h).elim,
    fun h => (no_lam_observation henv hΓ hQ o h).elim⟩

/-- These two bodies have the same type Sort 1, but different type-former heads. -/
def bodySort : VExpr := .sort .zero
def bodyPi : VExpr := .forallE (.sort .zero) (.sort .zero)

theorem bodySort_typed {env : VEnv} {U : Nat} {Γ : List VExpr} :
    env.HasType U Γ bodySort (.sort (.succ .zero)) := .sort trivial

theorem bodyPi_typed {env : VEnv} {U : Nat} {Γ : List VExpr} :
    env.HasType U Γ bodyPi (.sort (.succ .zero)) := by
  have h : env.HasType U Γ bodyPi (.sort (.imax (.succ .zero) (.succ .zero))) :=
    .forallE (.sort trivial) (.sort trivial)
  exact .defeqDF (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero))
    (l' := .succ .zero) ⟨trivial, trivial⟩ trivial rfl) h

/-- A precise failure of reflection for the existing model at one fixed target.
The endpoints are typed at the SAME type; this is not a comparison of ill-typed terms.
The uninhabited-domain premise is explicit; no consistency theorem is assumed silently. -/
theorem fixed_target_not_reflecting {env : VEnv} (henv : env.WF)
    {U : Nat} {Γ : List VExpr} {Q : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (htQ : env.IsType U Γ Q)
    (hQ : ∀ q, ¬ env.HasType U Γ q Q) :
    ∃ a b T, env.HasType U Γ a T ∧ env.HasType U Γ b T ∧
      Model.OI env U Γ a = Model.OI env U Γ b ∧ ¬ env.IsDefEqU U Γ a b := by
  obtain ⟨u, htQ⟩ := htQ
  refine ⟨.lam Q bodySort, .lam Q bodyPi, .forallE Q (.sort (.succ .zero)),
    .lamDF htQ bodySort_typed, .lamDF htQ bodyPi_typed,
    empty_domain_observation_eq henv.ordered hΓ hQ, ?_⟩
  intro h
  have hΓQ : OnCtx (Q :: Γ) (env.IsType U) := ⟨hΓ, u, htQ⟩
  exact IsDefEqU.sort_forallE_inv henv hΓQ (IsDefEqU.lam_body henv hΓ h)

/-- Any substitution retraction with identity tail supplies an inhabitant of Q.
Thus a semantic anchor in the original target cannot evade the inhabited-binder case. -/
theorem retraction_requires_inhabitant {env : VEnv} {U : Nat} {Γ : List VExpr}
    {Q : VExpr} {σ : VExpr.Subst}
    (hσ : Ctx.SubstEq env U Γ σ σ (Q :: Γ)) (htail : σ.tail = .id) :
    env.HasType U Γ σ.head Q := by
  cases hσ with
  | cons _ _ h =>
    change env.IsDefEq U Γ σ.head σ.head Q
    simpa only [htail, VExpr.subst_id] using h

/-- The empty-domain obstruction is independent of the observation sets:
all valuations with identity anchor in this target context see no lambda output. -/
theorem empty_domain_all_sets {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} {Q a b : VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hQ : ∀ q, ¬ env.HasType U Γ q Q) (S : Model.ObSets) :
    Model.Obs env U Γ .id S (.lam Q a) = Model.Obs env U Γ .id S (.lam Q b) := by
  have hnone (body : VExpr) (o : Model.Ob) :
      ¬ Model.Obs env U Γ .id S (.lam Q body) o := by
    intro ho
    obtain ⟨c, K, x, τs, p, _, hc, _⟩ := Model.Obs.lam_iff.mp ho
    simp only [VExpr.subst_id] at hc
    exact no_typed_key henv hΓ hQ hc
  funext o
  exact propext ⟨fun h => (hnone a o h).elim, fun h => (hnone b o h).elim⟩

/-- An unconditional limitation of OI: its variable observation sets are empty.
The two variables are unequal, as witnessed by substitution of Sort 0 and a Pi.
This is valid for every WF environment, including any with canonical Eq. -/
theorem fixed_oi_counterexample {env : VEnv} (henv : env.WF) (U : Nat) :
    ∃ Γ a b T, OnCtx Γ (env.IsType U) ∧
      env.HasType U Γ a T ∧ env.HasType U Γ b T ∧
      Model.OI env U Γ a = Model.OI env U Γ b ∧ ¬ env.IsDefEqU U Γ a b := by
  let S : VExpr := .sort (.succ .zero)
  let Γ : List VExpr := [S, S]
  have hs {Δ : List VExpr} : env.HasType U Δ S (.sort (.succ (.succ .zero))) :=
    .sort trivial
  have hΓ : OnCtx Γ (env.IsType U) := ⟨⟨trivial, _, hs⟩, _, hs⟩
  refine ⟨Γ, .bvar 0, .bvar 1, S, hΓ, .bvar .zero, .bvar (.succ .zero), ?_, ?_⟩
  · funext o
    apply propext
    simp [Model.OI, Model.Obs.bvar_iff, Model.ObSets.empty]
  · intro H
    have H₁ := H.instN henv.ordered Ctx.InstN.zero
      (bodySort_typed (env := env) (U := U) (Γ := [S]))
    have H₂ := H₁.instN henv.ordered Ctx.InstN.zero
      (bodyPi_typed (env := env) (U := U) (Γ := []))
    have H₃ : env.IsDefEqU U [] (.sort .zero) (.forallE (.sort .zero) (.sort .zero)) := by
      simpa [bodySort, bodyPi, VExpr.inst, VExpr.instVar] using H₂
    exact IsDefEqU.sort_forallE_inv henv (show OnCtx [] (env.IsType U) from trivial) H₃


section EtaRepair
open VEnv.Params
variable [VEnv.Params]


def etaGood : VExpr := .lam (.sort .zero) (.app idProp.lift (.bvar 0))
def etaBad : VExpr := .lam badDomain (.app idProp.lift (.bvar 0))

theorem eta_good_step : FullStep [] idProp etaGood := by
  have hs : env.HasType univs [] (.sort .zero) (.sort (.succ .zero)) := .sort trivial
  exact .funEta (IsDefEq.lamDF hs (.bvar .zero))

theorem eta_bad_repair_step : FullStep [.sort .zero] etaBad etaGood.lift := by
  have h : FullStep [.sort .zero] etaBad etaGood :=
    .lam (.core (.beta .rfl .rfl)) .rfl
  simpa [etaGood, idProp, lift, liftN, liftVar] using h

omit [Params] in
theorem eta_good_supported : etaGood.lift.Skips 1 0 := by
  simp [VExpr.skips_iff, VExpr.Skips', etaGood, idProp, lift, liftN, liftVar]

/-- Repair of the precise support counterexample from the previous attempt. -/
theorem eta_obstruction_repaired :
    ∃ t, FullStep [] idProp t ∧ FullStep [.sort .zero] etaBad t.lift ∧ t.lift.Skips 1 0 :=
  ⟨etaGood, eta_good_step, eta_bad_repair_step, eta_good_supported⟩
end EtaRepair

section DomainCounting
open VEnv.Params
variable [VEnv.Params]


inductive DomainCountedN : Nat → List VExpr → VExpr → VExpr → Prop where
  | refl : env.HasType univs Γ e A → DomainCountedN 0 Γ e e
  | lam : env.HasType univs Γ A (.sort u) →
      DomainCountedN n Γ A B → DomainCountedN m (A :: Γ) a b →
      DomainCountedN (n + m + 1) Γ (.lam A a) (.lam B b)
  | proofIrrel : env.HasType univs Γ P (.sort .zero) →
      env.HasType univs Γ Q (.sort .zero) →
      env.HasType univs Γ a P → env.HasType univs Γ b Q →
      DomainCountedN n Γ P Q → DomainCountedN (n + 1) Γ a b

theorem DomainCountedN.toNormal {Γ : List VExpr} {a b : VExpr}
    (hΓ : OnCtx Γ (env.IsType univs)) (H : DomainCountedN n Γ a b) :
    NormalEq Γ a b := by
  induction H with
  | refl h => exact .refl h
  | lam hA _ _ ihA ihb =>
    have hd := ((ihA hΓ).defeq hΓ).of_l henv hΓ hA
    exact .lamDF hA hd (ihb ⟨hΓ, _, hA⟩)
  | proofIrrel hP _ ha hb _ ih =>
    have hPQ := ((ih hΓ).defeq hΓ).of_l henv hΓ hP
    exact .proofIrrel hP ha (.defeqDF hPQ.symm hb)

/-- Context transport preserves this candidate's rank only because the
transported typing witnesses remain opaque, uncounted declarative derivations. -/
theorem DomainCountedN.defeqDFC {Γ₀ Γ₁ Γ₂ : List VExpr}
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    {a b : VExpr} (H : DomainCountedN n Γ₁ a b) : DomainCountedN n Γ₂ a b := by
  induction H generalizing Γ₂ with
  | refl h => exact .refl (h.defeqDFC henv W)
  | lam hA _ _ ihA ihb =>
    exact .lam (hA.defeqDFC henv W) (ihA W) (ihb (.succ W hA))
  | proofIrrel hP hQ ha hb _ ih =>
    exact .proofIrrel (hP.defeqDFC henv W) (hQ.defeqDFC henv W)
      (ha.defeqDFC henv W) (hb.defeqDFC henv W) (ih W)

/-- Transitivity of the candidate fragment, by n₁+n₂. Both lambda domain
composition and body composition decrease that sum. This does not supply a
rank for recursively certified typing or reduction-side certificates. -/
theorem DomainCountedN.trans (hΓ : OnCtx Γ (env.IsType univs)) :
    DomainCountedN n₁ Γ a b → DomainCountedN n₂ Γ b c →
    ∃ n, DomainCountedN n Γ a c
  | .refl _, H => ⟨_, H⟩
  | H, .refl _ => ⟨_, H⟩
  | .proofIrrel hP hQ ha hb hPQ, H => by
    have hBP : env.HasType univs Γ _ _ :=
      IsDefEq.defeqDF (((hPQ.toNormal hΓ).defeq hΓ).of_l henv hΓ hP).symm hb
    have hCP := hBP.defeqU_l henv hΓ ((H.toNormal hΓ).defeq hΓ)
    exact ⟨1, .proofIrrel hP hP ha hCP (.refl hP)⟩
  | H, .proofIrrel hP hQ hb hc hPQ => by
    have hAP := hb.defeqU_l henv hΓ ((H.toNormal hΓ).defeq hΓ).symm
    exact ⟨_, .proofIrrel hP hQ hAP hc hPQ⟩
  | .lam hA hAB hab, .lam hB hBC hbc => by
    obtain ⟨nd, hd⟩ := hAB.trans hΓ hBC
    have hBA := (((hAB.toNormal hΓ).defeq hΓ).of_l henv hΓ hA).symm
    have hbc' := hbc.defeqDFC (.succ (.zero (Γ₀ := Γ)) hBA)
    obtain ⟨nb, hb⟩ := hab.trans (Γ := _ :: Γ) ⟨hΓ, _, hA⟩ hbc'
    exact ⟨nd + nb + 1, .lam hA hd hb⟩
termination_by n₁ + n₂

/-- The lambda domain really is charged, instead of using NormalEqN.lamDF's
opaque domain equality. -/
theorem domain_counted {Γ : List VExpr} {A B : VExpr} {u : VLevel}
    (hA : env.HasType univs Γ A (.sort u)) (h : DomainCountedN n Γ A B) :
    DomainCountedN (n + 1) Γ (.lam A (.sort .zero)) (.lam B (.sort .zero)) := by
  exact .lam hA h (.refl (HasType.sort (l := .zero) trivial))

/-- Yet arbitrary type agreement can still be hidden at index ONE, by
moving the conversion into the right-hand typing witness and choosing P=P.
Thus witnessed agreement of two freely chosen types is insufficient. -/
theorem alignment_can_be_hidden {Γ : List VExpr} {P Q a b : VExpr}
    (H : env.IsDefEq univs Γ P Q (.sort .zero))
    (ha : env.HasType univs Γ a P) (hb : env.HasType univs Γ b Q) :
    DomainCountedN 1 Γ a b :=
  .proofIrrel H.hasType.1 H.hasType.1 ha
    (.defeqDF H.symm hb) (.refl H.hasType.1)
end DomainCounting


/-! If typing certificates are also made structural, their size cannot stay
bounded under arbitrary typed substitution by a function of the source size
alone. The example below keeps the source term, source type and both contexts
fixed. Only the substitution witness varies. -/

def typeTower : Nat → VExpr
  | 0 => .sort .zero
  | n + 1 => .forallE (.sort .zero) (typeTower n)

/-- Counts nested displayed binders on the body's path; defined on all syntax. -/
def binderDepth : VExpr → Nat
  | .lam _ b | .forallE _ b => binderDepth b + 1
  | _ => 0

theorem typeTower_depth (n : Nat) : binderDepth (typeTower n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [typeTower, binderDepth, ih]

theorem typeTower_typed {env : VEnv} {U : Nat} (n : Nat) (Γ : List VExpr) :
    env.HasType U Γ (typeTower n) (.sort (.succ .zero)) := by
  induction n generalizing Γ with
  | zero => exact .sort trivial
  | succ n ih =>
    have h : env.HasType U Γ (typeTower (n + 1))
        (.sort (.imax (.succ .zero) (.succ .zero))) :=
      .forallE (.sort trivial) (ih _)
    exact .defeqDF (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero))
      (l' := .succ .zero) ⟨trivial, trivial⟩ trivial rfl) h

/-- A fixed, typed variable has substitutions of unbounded displayed depth.
This refutes a source-only size bound, not every possible cut-elimination rank. -/
theorem typed_substitution_unbounded {env : VEnv} {U : Nat} (N : Nat) :
    ∃ σ : VExpr.Subst,
      Ctx.SubstEq env U [] σ σ [.sort (.succ .zero)] ∧
      env.HasType U [.sort (.succ .zero)] (.bvar 0) (.sort (.succ .zero)) ∧
      N < binderDepth ((.bvar 0 : VExpr).subst σ) := by
  let σ : VExpr.Subst := VExpr.Subst.id.cons (typeTower (N + 1))
  have hσ : Ctx.SubstEq env U [] σ σ [.sort (.succ .zero)] :=
    .cons .nil (HasType.sort trivial) (typeTower_typed (N + 1) [])
  refine ⟨σ, hσ, .bvar .zero, ?_⟩
  change N < binderDepth (typeTower (N + 1))
  rw [typeTower_depth]
  omega

/-- No substitution-independent numeric bound exists even for this fixed source. -/
theorem no_source_only_substitution_bound {env : VEnv} {U : Nat} :
    ¬ ∃ N, ∀ σ : VExpr.Subst,
      Ctx.SubstEq env U [] σ σ [.sort (.succ .zero)] →
      binderDepth ((.bvar 0 : VExpr).subst σ) ≤ N := by
  rintro ⟨N, hN⟩
  obtain ⟨σ, hσ, _, hlt⟩ := typed_substitution_unbounded (env := env) (U := U) N
  have := hN σ hσ
  omega

end VEnv.StrengtheningObstructions
end Lean4Lean
