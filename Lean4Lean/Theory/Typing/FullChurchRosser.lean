import Lean4Lean.Theory.Typing.LevelledReduction
import Lean4Lean.Theory.Typing.UnitLikeConstructor

namespace Lean4Lean.VEnv
open VExpr Params
variable [Params]

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:36 => NormalEq Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫* " e2:36 => FullReduction Γ e1 e2

def FullCRDefEq (Γ : List VExpr) (left right : VExpr) : Prop :=
  (∃ type, HasType env univs Γ left type) ∧ (∃ type, HasType env univs Γ right type) ∧
  ∃ left' right', FullReduction Γ left left' ∧ FullReduction Γ right right' ∧ NormalEq Γ left' right'

local notation:65 Γ " ⊢ " e1 " ≫≪ " e2:36 => FullCRDefEq Γ e1 e2

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem FullCRDefEq.normalEq (H : Γ ⊢ e₁ ≡ₚ e₂) : Γ ⊢ e₁ ≫≪ e₂ :=
  let ⟨_, h⟩ := H.defeq hΓ; ⟨⟨_, h.hasType.1⟩, ⟨_, h.hasType.2⟩, _, _, .rfl, .rfl, H⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem FullCRDefEq.refl (H : Γ ⊢ e : A) : Γ ⊢ e ≫≪ e := .normalEq hΓ (.refl H)

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem FullCRDefEq.symm : Γ ⊢ e₁ ≫≪ e₂ → Γ ⊢ e₂ ≫≪ e₁
  | ⟨h1, h2, _, _, h3, h4, h5⟩ => ⟨h2, h1, _, _, h4, h3, h5.symm hΓ⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem FullCRDefEq.trans : Γ ⊢ e₁ ≫≪ e₂ → Γ ⊢ e₂ ≫≪ e₃ → Γ ⊢ e₁ ≫≪ e₃
  | ⟨l1, ⟨_, l2⟩, _, _, l3, l4, l5⟩, ⟨_, r2, _, _, r3, r4, r5⟩ => by
    obtain ⟨_, _, m1, m2, m3⟩ := l4.church_rosser hΓ l2 r3
    obtain ⟨_, a1, a2⟩ := l5.fullReduction hΓ m1
    obtain ⟨_, b1, b2⟩ := (r5.symm hΓ).fullReduction hΓ m2
    exact ⟨l1, r2, _, _, l3.trans a1, r4.trans b1, a2.trans hΓ (m3.trans hΓ (b2.symm hΓ))⟩

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem IsDefEq.church_rosser [FullEquationCoverage]
    (H : Γ ⊢ e₁ ≡ e₂ : A) : Γ ⊢ e₁ ≫≪ e₂ := by
  have mk {Γ e₁ e₂ A e₁' e₂'} (H : Γ ⊢ e₁ ≡ e₂ : A)
      (h1 : Γ ⊢ e₁ ≫* e₁') (h2 : Γ ⊢ e₂ ≫* e₂') (h3 : Γ ⊢ e₁' ≡ₚ e₂') : Γ ⊢ e₁≫≪ e₂ :=
    ⟨⟨_, H.hasType.1⟩, ⟨_, H.hasType.2⟩, _, _, h1, h2, h3⟩
  induction H with
  | elimDF hl ht hc hp hr he hty _ =>
    exact .normalEq hΓ (.elimDF (.elimDF hl ht hc hp hr he hty) he)
  | elimIota hl hg hm hc hp ht hr _ _ =>
    obtain ⟨rule, hgen, heq⟩ := InductiveSignature.CaseSchema.generates_of_genericEquation hg hm
    cases heq
    have hbody := generated_case_body henv hΓ hl hgen hc hp ht hr
    have hred := ParRed.wrapLams (ParRed.of_schema hbody.2)
    obtain ⟨hlhs, hrhs, _⟩ := hgen.body_exact
    simp only [← VExpr.instL_wrapLams, hlhs, hrhs] at hred
    exact mk (.elimIota hl hg hm hc hp ht hr) (.tail .rfl (.core hred)) .rfl (.refl hr)
  | bvar h => exact .refl hΓ (.bvar h)
  | symm _ ih => exact (ih hΓ).symm hΓ
  | trans _ _ ih1 ih2 => exact (ih1 hΓ).trans hΓ (ih2 hΓ)
  | sortDF h1 h2 h3 => exact .normalEq hΓ (.sortDF h1 h2 h3)
  | constDF h1 h2 h3 h4 h5 => exact .normalEq hΓ (.constDF h1 h2 h3 h4 h5)
  | appDF h1 h2 ih1 ih2 =>
    obtain ⟨-, -, _, _, a1, a2, a3⟩ := ih1 hΓ
    obtain ⟨-, -, _, _, b1, b2, b3⟩ := ih2 hΓ
    exact mk (.appDF h1 h2) (.app a1 b1) (.app a2 b2) <|
      .appDF (a1.hasType hΓ h1.hasType.1) (a2.hasType hΓ h1.hasType.2)
        (b1.hasType hΓ h2.hasType.1) (b2.hasType hΓ h2.hasType.2) a3 b3
  | projDF hinfo hlevels huvars hparams hindices hfield hfieldTyping
      hLeft hRight hclosed hguard ihField ihLeft ihRight =>
    have majorCR := (ihLeft hΓ).symm hΓ |>.trans hΓ (ihRight hΓ)
    obtain ⟨-, -, _, _, majorLeft, majorRight, majorNormal⟩ := majorCR
    have original := IsDefEq.projDF hinfo hlevels huvars hparams hindices hfield
      hfieldTyping hLeft hRight hclosed hguard
    have reducedAtLeft := majorLeft.proj.hasType hΓ original.hasType.1
    exact mk original majorLeft.proj majorRight.proj <|
      .projDF reducedAtLeft majorNormal
  | lamDF h1 h2 ih1 ih2 =>
    obtain ⟨-, -, _, _, a1, a2, a3⟩ := ih1 hΓ
    obtain ⟨-, -, _, _, b1, b2, b3⟩ := ih2 ⟨hΓ, _, h1.hasType.1⟩
    have b2' := b2.defeqDFC hΓ (.succ .zero h1) h2.hasType.2
    have := (a1.defeq hΓ h1.hasType.1).symm
    exact mk (.lamDF h1 h2) (.lam a1 b1) (.lam a2 b2') <|
      .lamDF this.symm (this.symm.transU_l henv hΓ (a3.defeq hΓ)) b3
  | forallEDF h1 h2 ih1 ih2 =>
    obtain ⟨-, -, _, _, a1, a2, a3⟩ := ih1 hΓ
    refine have hΓ' := ⟨hΓ, _, h1.hasType.1⟩; have ⟨_, _, _, _, b1, b2, b3⟩ := ih2 hΓ'; ?_
    have b2' := b2.defeqDFC hΓ (.succ .zero h1) h2.hasType.2
    exact mk (.forallEDF h1 h2) (.forallE a1 b1) (.forallE a2 b2') <|
      .forallEDF (a1.defeq hΓ h1.hasType.1) a3 (b1.hasType hΓ' h2.hasType.1) b3
  | defeqDF _ _ _ ih2 => exact ih2 hΓ
  | beta h1 h2 ih1 ih2 =>
    refine have h := .beta h1 h2; mk h (.tail .rfl (.core (.beta .rfl .rfl))) .rfl ?_
    exact .refl h.hasType.2
  | eta h1 ih1 =>
    have := h1.hasType.1
    exact .normalEq hΓ <| .etaL this <| .refl <| .app (this.weak henv) (.bvar .zero)
  | proofIrrel h1 h2 h3 ih1 ih2 ih3 =>
    exact .normalEq hΓ <| .proofIrrel h1.hasType.1 h2.hasType.1 h3.hasType.1
  | @extra _ _ Γ h1 h2 h3 =>
    obtain ⟨_, _, hleft, hright, hnormal⟩ := FullEquationCoverage.equations hΓ h1 h2 h3
    exact mk (.extra h1 h2 h3) hleft hright hnormal
  | projIota hl hs hi ht _ _ =>
    have heq := IsDefEq.projIota hl hs hi ht
    exact mk heq (.tail .rfl (.projIota hl hs hi ht)) .rfl (.refl ht)
  | structEta hl hp hi hs ht _ _ =>
    have heq := IsDefEq.structEta hl hp hi hs ht
    exact mk heq .rfl (.tail .rfl (.structEta hl hp hi hs ht)) (.refl ht)
  | unitLike hl hp hi hf hs ht _ _ =>
    have hc := HasType.unitLike_constructor henv hΓ hl hp hi hf hs
    have stepLeft := FullStep.structEta hl hp hi hs (by simpa only [hf, List.range_zero,
      List.map_nil, List.append_nil] using hc)
    have stepRight := FullStep.structEta hl hp hi ht (by simpa only [hf, List.range_zero,
      List.map_nil, List.append_nil] using hc)
    simp only [hf, List.range_zero, List.map_nil, List.append_nil] at stepLeft stepRight
    exact mk (.unitLike hl hp hi hf hs ht) (.tail .rfl stepLeft) (.tail .rfl stepRight) (.refl hc)

variable! (hΓ : OnCtx Γ (IsType env univs)) in
theorem IsDefEq.full_church_rosser [FullEquationCoverage]
    (H : Γ ⊢ e₁ ≡ e₂ : A) : Γ ⊢ e₁ ≫≪ e₂ := H.church_rosser hΓ

end Lean4Lean.VEnv
