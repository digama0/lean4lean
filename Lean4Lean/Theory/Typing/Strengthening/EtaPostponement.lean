import Lean4Lean.Theory.Typing.Strengthening.EtaNormal

/-! # Typing strengthening: eta postponement

Direction B3.

## The exact obligation `EtaReplay` of `Exposure.lean` is false

`EtaReplay` asks for an *eta chain* `e'↑ ⇝η* Y` at the end. An eta expansion above may
annotate its binder with any type convertible to the domain, including one that mentions the
inserted variable; a following beta inside the body collapses the expansion but keeps the
annotation. The result is a lambda whose annotation is not a lift and is not an eta reduct of any
lift, so no eta chain from a lift reaches it (`not_etaReplay`). The instance needs no constant:
`e = λ (x : Prop). x` below, annotation `(λ (X : Prop). Prop) q` above with `q : Prop`.

## The weakened obligation `EtaReplayN`

Replace the eta chain by normal equality (`NormalEq`: structural congruence up to universe
levels, proof irrelevance, convertible binder annotations and eta). It is weaker than `EtaReplay`
(`etaReplayN_of_etaReplay`), it survives the counterexample (`counterexample_etaReplayN`), the
eta step and the empty-chain descent go through unchanged (`etaReplayN_eta`,
`etaReplayN_descent`), and the end lemma still holds: a type normally equal to a `Π` is a `Π`
(`normalEqN_forallE_inv_r`). Hence `TypedFront ∧ EtaReplayN → PiExposureRedN`
(`piExposureRed_of_etaReplayN`) and `Cancel ↔ TypedFront` given `EtaReplayN`, `ProjFrontN` and
`ElimFrontN` (`cancel_iff_typedFront_ofN`). -/

namespace Lean4Lean.VEnv.StrengtheningEtaPostponement
open VExpr VEnv.StrengtheningTypingFront VEnv.StrengtheningReplay VEnv.StrengtheningExposure
  VEnv.StrengtheningEtaNormal
variable {env : VEnv} {U k : Nat} {Γ Γ' : List VExpr} {A B F T e : VExpr}

theorem mkApps_const_ne_bvar {c : Name} {ls : List VLevel} (args : List VExpr) {i : Nat} :
    VExpr.mkApps (.const c ls) args ≠ .bvar i := by
  rcases eq_nil_or_snoc' args with rfl | ⟨L, b, rfl⟩
  · simp [VExpr.mkApps]
  · rw [VExpr.mkApps_snoc]; simp

section
open VEnv.Params
variable [VEnv.Params]

/-! ## The counterexample to `EtaReplay` -/

/-- Only a variable eta-expands to a variable. -/
theorem EtaPar.bvar_inv_r {x : VExpr} {i : Nat} (H : EtaPar Γ x (.bvar i)) : x = .bvar i := by
  generalize he : VExpr.bvar i = r at H
  cases H with
  | bvar => rfl
  | funEta => cases he
  | structEta =>
    unfold VEnv.structExpand at he
    exact (mkApps_const_ne_bvar _ he.symm).elim
  | _ => cases he

/-- The shape `λ (f q). q` (a lambda whose annotation is an application to the first variable and
whose body is the first variable) is reached by eta expansion only from the same shape, given the
source is a function `Prop → Prop`. -/
theorem EtaPar.badShape_inv_r {Z f : VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : EtaPar Γ Z (.lam (.app f (.bvar 0)) (.bvar 0)))
    (hZ : Params.env.HasType univs Γ Z (.forallE (.sort .zero) (.sort .zero))) :
    ∃ f', Z = .lam (.app f' (.bvar 0)) (.bvar 0) := by
  generalize he : VExpr.lam (.app f (.bvar 0)) (.bvar 0) = r at H
  cases H with
  | @lam _ A₀ _ b₀ _ hA hb =>
    cases he
    cases EtaPar.bvar_inv_r hb
    generalize hA' : VExpr.app f (.bvar 0) = r at hA
    cases hA with
    | app hf hx =>
      cases hA'
      cases EtaPar.bvar_inv_r hx
      exact ⟨_, rfl⟩
    | funEta => cases hA'
    | structEta _ _ _ hl _ _ hs _ =>
      obtain ⟨⟨u, hA₀⟩, -⟩ := hZ.lam_inv henv hΓ
      exact (type_not_structure hΓ hA₀ hl hs).elim
    | _ => cases hA'
  | funEta => cases he
  | structEta =>
    unfold VEnv.structExpand at he
    exact (VExpr.mkApps_ne_lam (by intros; intro h; cases h) _ he.symm).elim
  | _ => cases he

theorem EtaChain.badShape_inv_r {Z f : VExpr} (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : EtaChain Γ Z (.lam (.app f (.bvar 0)) (.bvar 0)))
    (hZ : Params.env.HasType univs Γ Z (.forallE (.sort .zero) (.sort .zero))) :
    ∃ f', Z = .lam (.app f' (.bvar 0)) (.bvar 0) := by
  generalize he : VExpr.lam (.app f (.bvar 0)) (.bvar 0) = r at H
  induction H generalizing f with
  | rfl => exact ⟨_, he.symm⟩
  | tail hchain hstep ih =>
    subst he
    obtain ⟨f₁, rfl⟩ := EtaPar.badShape_inv_r hΓ hstep (EtaChain.hasType hΓ hchain hZ)
    exact ih rfl

omit [Params] in
/-- No lift has the shape `λ (f q). q` when `q` is the inserted variable. -/
theorem liftN_ne_badShape {e f : VExpr} : e.liftN 1 0 ≠ .lam (.app f (.bvar 0)) (.bvar 0) := by
  intro h
  obtain ⟨A₁, b₁, rfl, hA, -⟩ := liftN_eq_lam_inv h
  obtain ⟨f₁, x₁, rfl, -, hx⟩ := liftN_eq_app_inv hA.symm
  cases x₁ <;> simp [liftN, liftVar] at hx <;> omega

/-- The identity `λ (x : Prop). x`, typed below. -/
theorem idProp_hasType :
    Params.env.HasType univs Γ StrengtheningObstructions.idProp
      (.forallE (.sort .zero) (.sort .zero)) :=
  .lamDF (HasType.sort (l := .zero) trivial) (.bvar .zero)

/-- The annotation `(λ (X : Prop). Prop) q`, convertible to `Prop` in `Prop :: Γ`. -/
theorem badDomain_defeq :
    Params.env.IsDefEq univs (.sort .zero :: Γ) StrengtheningObstructions.badDomain (.sort .zero)
      (.sort (.succ .zero)) :=
  .beta (HasType.sort (l := .zero) trivial) (.bvar .zero)

/-- The identity above, typed at the bad annotation. -/
theorem idProp_hasType_bad :
    Params.env.HasType univs (.sort .zero :: Γ) StrengtheningObstructions.idProp
      (.forallE StrengtheningObstructions.badDomain (.sort .zero)) :=
  IsDefEq.defeq (IsDefEq.forallEDF badDomain_defeq.symm
    (HasType.sort (env := Params.env) (U := univs) (Γ := .sort .zero :: .sort .zero :: Γ)
      (l := .zero) trivial)) idProp_hasType

/-- The eta step of the counterexample: expand the identity with the bad annotation. -/
theorem etaPar_counterexample :
    EtaPar (.sort .zero :: Γ) StrengtheningObstructions.idProp
      (.lam StrengtheningObstructions.badDomain
        (.app StrengtheningObstructions.idProp (.bvar 0))) := by
  simpa [StrengtheningObstructions.idProp, lift, liftN, liftVar] using
    EtaPar.funEta (e' := StrengtheningObstructions.idProp)
      (A' := StrengtheningObstructions.badDomain) .rfl .rfl idProp_hasType_bad

/-- The beta step of the counterexample, inside the expansion. -/
theorem parRed_counterexample :
    ParRed (.sort .zero :: Γ)
      (.lam StrengtheningObstructions.badDomain (.app StrengtheningObstructions.idProp (.bvar 0)))
      (.lam StrengtheningObstructions.badDomain (.bvar 0)) := by
  simpa [StrengtheningObstructions.idProp, inst, instVar] using
    ParRed.lam (Γ := .sort .zero :: Γ) (A := StrengtheningObstructions.badDomain) .rfl
      (ParRed.beta (A := .sort .zero) (e₁ := .bvar 0) (e₂ := .bvar 0) .rfl .rfl)

/-- `EtaReplay` is false in every parameter environment: after the eta step with the bad
annotation and the beta step inside, the reduct `λ ((λ X. Prop) q). q` is not an eta chain of any
lift (its annotation mentions the inserted variable), while the source is `λ (x : Prop). x`. -/
theorem not_etaReplay : ¬ EtaReplay := by
  intro H
  have hΓ : OnCtx ([] : List VExpr) (Params.env.IsType univs) := trivial
  have hΓ' : OnCtx [VExpr.sort .zero] (Params.env.IsType univs) :=
    ⟨trivial, _, HasType.sort (l := .zero) trivial⟩
  have he : Params.env.HasType univs [] StrengtheningObstructions.idProp
      (.forallE (.sort .zero) (.sort .zero)) := idProp_hasType
  have hX : EtaChain [VExpr.sort .zero] (StrengtheningObstructions.idProp.liftN 1 0)
      (.lam StrengtheningObstructions.badDomain
        (.app StrengtheningObstructions.idProp (.bvar 0))) := by
    refine .tail .rfl ?_
    simpa [StrengtheningObstructions.idProp, liftN, liftVar] using
      etaPar_counterexample (Γ := [])
  obtain ⟨e', hred, hchain⟩ := H (Ctx.LiftN.one) hΓ hΓ' he hX (.inl parRed_counterexample)
  have hT : Params.env.HasType univs [VExpr.sort .zero] (e'.liftN 1 0)
      (.forallE (.sort .zero) (.sort .zero)) := by
    simpa [liftN] using (hred.hasType hΓ he).weakN henv.ordered (Ctx.LiftN.one (A := .sort .zero))
  obtain ⟨f', hf⟩ := EtaChain.badShape_inv_r hΓ' hchain hT
  exact liftN_ne_badShape hf

/-! ## The weakened obligation: an eta chain, then normal equality without eta -/

/-- The replay obligation with the reduct related to the lift by an eta chain followed by a
normal equality without eta (`NormalEq₀`: structural congruence up to universe levels, proof
irrelevance and convertible binder annotations). -/
def EtaReplay₀ : Prop :=
  ∀ ⦃k Γ Γ' e T X Y⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (Params.env.IsType univs) →
    OnCtx Γ' (Params.env.IsType univs) → Params.env.HasType univs Γ e T →
    EtaChain Γ' (e.liftN 1 k) X → UpStep Γ' X Y →
    ∃ e' Z, FullReduction Γ e e' ∧ EtaChain Γ' (e'.liftN 1 k) Z ∧ NormalEq₀ Γ' Z Y

/-- The counterexample to `EtaReplay` is an instance of `EtaReplay₀`: the source itself is
normally equal to the reduct (convertible annotations). -/
theorem counterexample_etaReplay₀ :
    NormalEq₀ (.sort .zero :: Γ) (StrengtheningObstructions.idProp.liftN 1 0)
      (.lam StrengtheningObstructions.badDomain (.bvar 0)) := by
  have h := NormalEqN.lamDF (Γ := .sort .zero :: Γ) (A := .sort .zero) (b := false)
    (HasType.sort (l := .zero) trivial) badDomain_defeq.symm (NormalEqN.refl (.bvar .zero))
  exact ⟨_, by simpa [StrengtheningObstructions.idProp, liftN, liftVar] using h⟩

theorem UpStep.hasType (hΓ : OnCtx Γ (Params.env.IsType univs)) (H : UpStep Γ a b)
    (ha : Params.env.HasType univs Γ a A) : Params.env.HasType univs Γ b A := by
  rcases H with h | h | h
  · exact (h.defeq hΓ ha).hasType.2
  · exact (DeltaPar.full h).hasType hΓ ha
  · exact (EtaPar.full hΓ h ha).hasType hΓ ha

theorem UpStep.path_hasType (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : ReflTransGen (UpStep Γ) a b) (ha : Params.env.HasType univs Γ a A) :
    Params.env.HasType univs Γ b A := by
  induction H with
  | rfl => exact ha
  | tail _ s ih => exact UpStep.hasType hΓ s ih

/-- A parallel step mirrors through a normal equality without eta (the library's three mirror
lemmas), as a step of the same kind. -/
theorem UpStep.normalEq₀_mirror (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : UpStep Γ a b) (hc : NormalEq₀ Γ c a) (ha : Params.env.HasType univs Γ a A) :
    ∃ c', UpStep Γ c c' ∧ NormalEq₀ Γ c' b := by
  rcases H with h | h | h
  · obtain ⟨c', h', hn⟩ := h.normalEq₀_mirror hΓ hc ha
    exact ⟨c', .inl h', hn⟩
  · obtain ⟨c', h', hn⟩ := h.normalEq₀_mirror hΓ hc ha
    exact ⟨c', .inr (.inl h'), hn⟩
  · obtain ⟨c', h', hn⟩ := h.normalEq₀_mirror hΓ hc ha
    exact ⟨c', .inr (.inr h'), hn⟩

/-- The eta case of `EtaReplay₀` is trivial. -/
theorem etaReplay₀_eta (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    (hX : Params.env.HasType univs Γ' X T) (hc : EtaChain Γ' (e.liftN 1 k) X) (hY : EtaPar Γ' X Y) :
    ∃ e' Z, FullReduction Γ e e' ∧ EtaChain Γ' (e'.liftN 1 k) Z ∧ NormalEq₀ Γ' Z Y :=
  ⟨e, Y, .rfl, hc.tail hY, .refl ((EtaPar.full hΓ' hY hX).hasType hΓ' hX)⟩

/-- On the empty chain, `EtaReplay₀` is the descent of `Replay.lean`. -/
theorem etaReplay₀_of_descent (hTF : TypedFrontN Params.env) (hcase : CaseRedexDescends)
    (hunfold : UnfoldingCheckDescends)
    (hcv : ∀ {p : Pattern} {r : p.RHS × p.Check}, Pat p r → CheckVars r.2)
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (he : Params.env.HasType univs Γ e T)
    (hY : UpStep Γ' (e.liftN 1 k) Y) :
    ∃ e' Z, FullReduction Γ e e' ∧ EtaChain Γ' (e'.liftN 1 k) Z ∧ NormalEq₀ Γ' Z Y := by
  have hX := he.weakN henv.ordered W
  have hY' := UpStep.hasType hΓ' hY hX
  rcases hY with h | h | h
  · obtain ⟨e', rfl, h'⟩ := ParRed.descend hTF hcase hcv W hΓ hΓ' he h
    exact ⟨e', _, .tail .rfl (.core h'), .rfl, .refl hY'⟩
  · obtain ⟨e', rfl, h'⟩ := DeltaPar.descend hTF hunfold W hΓ hΓ' he h
    exact ⟨e', _, h'.full, .rfl, .refl hY'⟩
  · exact etaReplay₀_eta hΓ' hX .rfl h

/-- Path replay with the invariant "an eta chain of a lift, then a normal equality without eta":
induction on the above `UpStep` path; each step is first mirrored through the normal equality. -/
theorem path_replay₀ (H : EtaReplay₀) (W : Ctx.LiftN 1 k Γ Γ')
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    (he : Params.env.HasType univs Γ e T)
    (hr : ReflTransGen (UpStep Γ') (e.liftN 1 k) X) :
    ∃ e' Z, FullReduction Γ e e' ∧ EtaChain Γ' (e'.liftN 1 k) Z ∧ NormalEq₀ Γ' Z X := by
  induction hr with
  | rfl => exact ⟨e, _, .rfl, .rfl, .refl (he.weakN henv.ordered W)⟩
  | @tail X₁ X₂ hpath step ih =>
    obtain ⟨e₁, Z, hred, hchain, hn⟩ := ih
    have hX : Params.env.HasType univs Γ' X₁ (T.liftN 1 k) :=
      UpStep.path_hasType hΓ' hpath (he.weakN henv.ordered W)
    obtain ⟨Z', step', hn'⟩ := UpStep.normalEq₀_mirror hΓ' step hn hX
    obtain ⟨e₂, Z'', hred₂, hchain₂, hn₂⟩ := H W hΓ hΓ' (hred.hasType hΓ he) hchain step'
    exact ⟨e₂, Z'', hred.trans hred₂, hchain₂, hn₂.trans hΓ' hn'⟩

/-- A term normally equal (without eta) to a `Π`, typed at a sort, is a `Π`. -/
theorem normalEq₀_forallE_inv {Z : VExpr} {u : VLevel}
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hZ : Params.env.HasType univs Γ Z (.sort u))
    (H : NormalEq₀ Γ Z (.forallE A B)) : ∃ A' B', Z = .forallE A' B' := by
  obtain ⟨n, H⟩ := H
  have hPi : Params.env.HasType univs Γ (.forallE A B) (.sort u) :=
    ((H.defeq hΓ).of_l henv hΓ hZ).hasType.2
  exact normalEqN_forallE_inv_r hΓ hPi H

end

/-- Reduction-form exposure from the typed front and the weakened replay obligation. -/
theorem piExposureRed_of_etaReplay₀ (henv : env.WF)
    (H : ∀ U, @EtaReplay₀ (henv.params U)) : PiExposureRedN henv := by
  intro U k Γ Γ' f F u A B W hΓ hΓ' _ hF hr
  letI := henv.params U
  obtain ⟨F', Z, hred, hchain, hn⟩ := path_replay₀ (H U) W hΓ hΓ' hF (FullReduction.upSteps hr)
  have hF' : env.HasType U Γ' (F'.liftN 1 k) (.sort u) :=
    (hred.hasType hΓ hF).weakN henv.ordered W
  have hZ : env.HasType U Γ' Z (.sort u) := EtaChain.hasType hΓ' hchain hF'
  obtain ⟨A₁, B₁, rfl⟩ := normalEq₀_forallE_inv hΓ' hZ hn
  obtain ⟨A₂, B₂, hPi⟩ := EtaChain.forallE_inv hΓ' hchain hF'
  obtain ⟨A₀, B₀, rfl, -, -⟩ := liftN_eq_forallE_inv hPi
  exact ⟨A₀, B₀, hred⟩

/-- `TypedFront → Cancel`, given the weakened replay obligation and the projection and
eliminator closures. -/
theorem cancel_of_typedFront_of₀ (henv : env.WF) (heq : env.HasCanonicalEq)
    (hTF : StrengtheningKripke.TypedFront env) (H : ∀ U, @EtaReplay₀ (henv.params U))
    (hProj : ProjFrontN env) (hElim : ElimFrontN env) : Cancel env :=
  cancel_of_piExposureRed henv heq (piExposureRed_of_etaReplay₀ henv H)
    ((typeFrontN_iff_typedFront henv heq).mpr hTF) hProj hElim

theorem cancel_iff_typedFront_of₀ (henv : env.WF) (heq : env.HasCanonicalEq)
    (H : ∀ U, @EtaReplay₀ (henv.params U)) (hProj : ProjFrontN env) (hElim : ElimFrontN env) :
    Cancel env ↔ StrengtheningKripke.TypedFront env :=
  ⟨fun hc => ((cancel_iff_typedFront_and_closures henv heq).mp hc).1,
    fun hTF => cancel_of_typedFront_of₀ henv heq hTF H hProj hElim⟩

/-- The weakened obligation holds on empty chains from the typed front and the two guard
descents, in every well-formed environment. -/
theorem etaReplay₀_empty_chain (henv : env.WF) (heq : env.HasCanonicalEq)
    (hTF : StrengtheningKripke.TypedFront env) (U : Nat)
    (hcase : @CaseRedexDescends (henv.params U)) (hunfold : @UnfoldingCheckDescends (henv.params U))
    {k : Nat} {Γ Γ' : List VExpr} {e T Y : VExpr}
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    (he : env.HasType U Γ e T) (hY : @UpStep (henv.params U) Γ' (e.liftN 1 k) Y) :
    letI := henv.params U
    ∃ e' Z, FullReduction Γ e e' ∧ EtaChain Γ' (e'.liftN 1 k) Z ∧ NormalEq₀ Γ' Z Y := by
  letI := henv.params U
  exact etaReplay₀_of_descent ((typedFrontN_iff_typedFront henv heq).mpr hTF) hcase hunfold
    (fun hp => Params.checkVars henv U hp) W hΓ hΓ' he hY

/-! ## The obligation in eta-normal form

`EtaNE` (`EtaNormal.lean`) records eta-free steps on the source side and eta expansions on the
reduct side; it contains every eta chain of a typed term and is closed under eta steps on the
right. The invariant "the reduct is an eta-normal reduct of the lift" therefore absorbs the eta
steps of the path above, and its preservation under an eta-free step is the closure of `EtaNE`
under eta-free steps on the right (`UpStepFClosure`, the content of `EtaClosure.lean`). The end
lemma `EtaNE.forallE_inv_lift` descends the recorded steps at the root of the lift and finds the
`Π` below. -/

section
open VEnv.Params
variable [VEnv.Params]

/-- The replay obligation in eta-normal form: an eta-normal reduct above of the lift of a term
typed below, followed by one `UpStep`, is simulated by a reduction below, up to eta-normal
reduction. -/
def EtaReplayNE : Prop :=
  ∀ ⦃k Γ Γ' e T X Y⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (Params.env.IsType univs) →
    OnCtx Γ' (Params.env.IsType univs) → Params.env.HasType univs Γ e T →
    EtaNE Γ' (e.liftN 1 k) X → UpStep Γ' X Y →
    ∃ e', FullReduction Γ e e' ∧ EtaNE Γ' (e'.liftN 1 k) Y

/-- Closure of the eta-normal relation under eta-free parallel steps on the right (the content of
the replay obligation; `EtaClosure.lean`). -/
def UpStepFClosure : Prop :=
  ∀ ⦃Γ s X Y T⦄, OnCtx Γ (Params.env.IsType univs) → Params.env.HasType univs Γ s T →
    EtaNE Γ s X → UpStepF Γ X Y → EtaNE Γ s Y

/-- The eta case of `EtaReplayNE` is the closure of `EtaNE` under eta steps on the right. -/
theorem etaReplayNE_eta (W : Ctx.LiftN 1 k Γ Γ') (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    (he : Params.env.HasType univs Γ e T) (hX : EtaNE Γ' (e.liftN 1 k) X) (hY : EtaPar Γ' X Y) :
    ∃ e', FullReduction Γ e e' ∧ EtaNE Γ' (e'.liftN 1 k) Y :=
  ⟨e, .rfl, hX.etaPar_r hΓ' (he.weakN henv.ordered W) hY⟩

/-- The replay obligation follows from the closure, with no reduction below. -/
theorem etaReplayNE_of_closure (H : UpStepFClosure) : EtaReplayNE := by
  intro k Γ Γ' e T X Y W hΓ hΓ' he hX hY
  rcases hY with h | h | h
  · exact ⟨e, .rfl, H hΓ' (he.weakN henv.ordered W) hX (.inl h)⟩
  · exact ⟨e, .rfl, H hΓ' (he.weakN henv.ordered W) hX (.inr h)⟩
  · exact etaReplayNE_eta W hΓ' he hX h

/-- Path replay with the eta-normal invariant: induction on the above `UpStep` path. -/
theorem path_replayNE (H : EtaReplayNE) (W : Ctx.LiftN 1 k Γ Γ')
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    (he : Params.env.HasType univs Γ e T)
    (hr : ReflTransGen (UpStep Γ') (e.liftN 1 k) X) :
    ∃ e', FullReduction Γ e e' ∧ EtaNE Γ' (e'.liftN 1 k) X := by
  induction hr with
  | rfl => exact ⟨e, .rfl, EtaNE.rfl⟩
  | tail _ step ih =>
    obtain ⟨e₁, hred, hne⟩ := ih
    obtain ⟨e₂, hred₂, hne₂⟩ := H W hΓ hΓ' (hred.hasType hΓ he) hne step
    exact ⟨e₂, hred.trans hred₂, hne₂⟩

end

/-- Reduction-form exposure from the typed front, the guard descents and the eta-normal replay
obligation. -/
theorem piExposureRed_of_etaReplayNE (henv : env.WF) (heq : env.HasCanonicalEq)
    (hTF : StrengtheningKripke.TypedFront env)
    (hcase : ∀ U, @CaseRedexDescends (henv.params U))
    (hunfold : ∀ U, @UnfoldingCheckDescends (henv.params U))
    (hmajor : ∀ U, @MajorEtaDescends (henv.params U))
    (H : ∀ U, @EtaReplayNE (henv.params U)) : PiExposureRedN henv := by
  intro U k Γ Γ' f F u A B W hΓ hΓ' _ hF hr
  letI := henv.params U
  obtain ⟨F', hred, hne⟩ := path_replayNE (H U) W hΓ hΓ' hF (FullReduction.upSteps hr)
  obtain ⟨A₀, B₀, hred'⟩ := EtaNE.forallE_inv_lift ((typedFrontN_iff_typedFront henv heq).mpr hTF)
    (hcase U) (hunfold U) (fun hp => Params.checkVars henv U hp) (hmajor U) W hΓ hΓ'
    (hred.hasType hΓ hF) hne
  exact ⟨A₀, B₀, hred.trans hred'⟩

/-- `TypedFront → Cancel`, given the guard descents, the eta-normal replay obligation and the
projection and eliminator closures. -/
theorem cancel_of_typedFront_ofNE (henv : env.WF) (heq : env.HasCanonicalEq)
    (hTF : StrengtheningKripke.TypedFront env)
    (hcase : ∀ U, @CaseRedexDescends (henv.params U))
    (hunfold : ∀ U, @UnfoldingCheckDescends (henv.params U))
    (hmajor : ∀ U, @MajorEtaDescends (henv.params U))
    (H : ∀ U, @EtaReplayNE (henv.params U))
    (hProj : ProjFrontN env) (hElim : ElimFrontN env) : Cancel env :=
  cancel_of_piExposureRed henv heq
    (piExposureRed_of_etaReplayNE henv heq hTF hcase hunfold hmajor H)
    ((typeFrontN_iff_typedFront henv heq).mpr hTF) hProj hElim

theorem cancel_iff_typedFront_ofNE (henv : env.WF) (heq : env.HasCanonicalEq)
    (hcase : ∀ U, @CaseRedexDescends (henv.params U))
    (hunfold : ∀ U, @UnfoldingCheckDescends (henv.params U))
    (hmajor : ∀ U, @MajorEtaDescends (henv.params U))
    (H : ∀ U, @EtaReplayNE (henv.params U)) (hProj : ProjFrontN env) (hElim : ElimFrontN env) :
    Cancel env ↔ StrengtheningKripke.TypedFront env :=
  ⟨fun hc => ((cancel_iff_typedFront_and_closures henv heq).mp hc).1,
    fun hTF => cancel_of_typedFront_ofNE henv heq hTF hcase hunfold hmajor H hProj hElim⟩

/-- `Cancel ↔ TypedFront` given the closure of `EtaNE` under eta-free steps, the three descents
(`CaseRedexDescends`, `UnfoldingCheckDescends`, `MajorEtaDescends`), `ProjFrontN` and
`ElimFrontN`. -/
theorem cancel_iff_typedFront_of_closure (henv : env.WF) (heq : env.HasCanonicalEq)
    (hcase : ∀ U, @CaseRedexDescends (henv.params U))
    (hunfold : ∀ U, @UnfoldingCheckDescends (henv.params U))
    (hmajor : ∀ U, @MajorEtaDescends (henv.params U))
    (H : ∀ U, @UpStepFClosure (henv.params U)) (hProj : ProjFrontN env) (hElim : ElimFrontN env) :
    Cancel env ↔ StrengtheningKripke.TypedFront env :=
  cancel_iff_typedFront_ofNE henv heq hcase hunfold hmajor
    (fun U => letI := henv.params U; etaReplayNE_of_closure (H U)) hProj hElim

end Lean4Lean.VEnv.StrengtheningEtaPostponement
