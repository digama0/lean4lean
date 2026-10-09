import Lean4Lean.Theory.Typing.Strengthening.Cancel

/-! # A support-preserving certificate calculus: the pilot fragment

The fragment of `IsDefEq` with sorts, variables, constants, `Π`, `λ`, application, beta,
closed stored equations (`extra`), typed eta and typed proof irrelevance, presented as
certificates whose every term is a subterm, a synthesised type or a reduct of the endpoints
(the pilot of the strengthening study):

* `CTy Γ e T`: syntax-directed synthesis; the function type of an application is exposed to
  a `Π` by certified reduction, the argument's synthesised type is converted by a certificate;
* `CStep`: parallel reduction; eta expands at the domain exposed from the synthesised type;
* `CNorm`: normal equality whose `λ`/`Π` domain comparisons are certificates, whose eta
  domains are exposed from synthesised types, and whose proof-irrelevance leaf compares the
  synthesised propositions by a certificate;
* `CConv`: joinability by `CStep` modulo `CNorm`.

Proved: soundness into `IsDefEq` (for typed endpoints) and **descent**: a certificate between
lifted terms in a larger context is the lift of a certificate in the smaller one. Descent is
what the three checked obstructions of `Obstructions.lean` deny to the declarative
witnesses (`FullStep.funEta` with a free domain, `NormalEqN.lamDF` with an uncounted domain
conversion, freely chosen typing witnesses at proof irrelevance): this calculus passes them by
construction.

Not proved, and the open problem of the attempt: transitivity of `CConv` (`CConv.Trans`),
equivalently completeness `IsDefEq ⊆ CConv` (`CComplete`). `Cancel.of_cComplete` shows that
completeness would give `Cancel`; the fragment omits projections, eliminators and the
singleton and quotient unfoldings, so `CComplete` fails in environments that use them, and
the theorem is the template of the argument, not a reduction of the full problem. -/

namespace Lean4Lean
namespace VEnv
open VExpr

variable (env : VEnv) (U : Nat)

/-- The kinds of certificate: synthesis, parallel step, reduction, normal equality,
conversion. One inductive family indexed by the kind stands for the mutual definition, so that
a single `induction` covers the five judgements. -/
inductive CKind | ty | step | red | norm | conv

/-- Certificates. `Cert .ty Γ e T` is synthesis, `Cert .step Γ a b` a parallel step,
`Cert .red Γ a b` a reduction, `Cert .norm Γ a b` normal equality and `Cert .conv Γ a b`
conversion (a join modulo normal equality). -/
inductive Cert : CKind → List VExpr → VExpr → VExpr → Prop
  -- synthesis
  | ty_bvar : Lookup Γ i A → Cert .ty Γ (.bvar i) A
  | ty_sort : l.WF U → Cert .ty Γ (.sort l) (.sort (.succ l))
  | ty_const : env.constants c = some ci → (∀ l ∈ ls, l.WF U) → ls.length = ci.uvars →
      Cert .ty Γ (.const c ls) (ci.type.instL ls)
  | ty_app : Cert .ty Γ f F → Cert .red Γ F (.forallE A B) → Cert .ty Γ a A' →
      Cert .conv Γ A' A → Cert .ty Γ (.app f a) (B.inst a)
  | ty_lam : Cert .ty Γ A S → Cert .red Γ S (.sort u) → Cert .ty (A::Γ) b B →
      Cert .ty Γ (.lam A b) (.forallE A B)
  | ty_forallE : Cert .ty Γ A S → Cert .red Γ S (.sort u) → Cert .ty (A::Γ) B S' →
      Cert .red (A::Γ) S' (.sort v) → Cert .ty Γ (.forallE A B) (.sort (.imax u v))
  -- parallel step
  | step_bvar : Cert .step Γ (.bvar i) (.bvar i)
  | step_sort : Cert .step Γ (.sort l) (.sort l)
  | step_const : Cert .step Γ (.const c ls) (.const c ls)
  | step_app : Cert .step Γ f f' → Cert .step Γ a a' → Cert .step Γ (.app f a) (.app f' a')
  | step_lam : Cert .step Γ A A' → Cert .step (A::Γ) b b' →
      Cert .step Γ (.lam A b) (.lam A' b')
  | step_forallE : Cert .step Γ A A' → Cert .step (A::Γ) B B' →
      Cert .step Γ (.forallE A B) (.forallE A' B')
  | step_beta : Cert .step (A::Γ) b b' → Cert .step Γ a a' →
      Cert .step Γ (.app (.lam A b) a) (b'.inst a')
  | step_extra : env.defeqs df → (∀ l ∈ ls, l.WF U) → ls.length = df.uvars →
      Cert .step Γ (df.lhs.instL ls) (df.rhs.instL ls)
  | step_eta : Cert .ty Γ e F → Cert .red Γ F (.forallE A B) →
      Cert .step Γ e (.lam A (.app e.lift (.bvar 0)))
  -- reduction
  | red_refl : Cert .red Γ e e
  | red_step : Cert .step Γ a b → Cert .red Γ b c → Cert .red Γ a c
  -- normal equality
  | norm_bvar : Cert .norm Γ (.bvar i) (.bvar i)
  | norm_sort : l₁.WF U → l₂.WF U → l₁ ≈ l₂ → Cert .norm Γ (.sort l₁) (.sort l₂)
  | norm_const : env.constants c = some ci → (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) →
      ls.length = ci.uvars → List.Forall₂ (· ≈ ·) ls ls' →
      Cert .norm Γ (.const c ls) (.const c ls')
  | norm_app : Cert .norm Γ f f' → Cert .norm Γ a a' → Cert .norm Γ (.app f a) (.app f' a')
  | norm_lam : Cert .conv Γ A A' → Cert .norm (A::Γ) b b' →
      Cert .norm Γ (.lam A b) (.lam A' b')
  | norm_forallE : Cert .conv Γ A A' → Cert .norm (A::Γ) B B' →
      Cert .norm Γ (.forallE A B) (.forallE A' B')
  | norm_etaL : Cert .ty Γ e' F → Cert .red Γ F (.forallE A' B) → Cert .conv Γ A A' →
      Cert .norm (A::Γ) e (.app e'.lift (.bvar 0)) → Cert .norm Γ (.lam A e) e'
  | norm_etaR : Cert .ty Γ e F → Cert .red Γ F (.forallE A' B) → Cert .conv Γ A A' →
      Cert .norm (A::Γ) (.app e.lift (.bvar 0)) e' → Cert .norm Γ e (.lam A e')
  | norm_etaBoth : Cert .ty Γ e F → Cert .red Γ F (.forallE A B) → Cert .ty Γ e' F' →
      Cert .red Γ F' (.forallE A' B') → Cert .conv Γ A A' →
      Cert .norm (A::Γ) (.app e.lift (.bvar 0)) (.app e'.lift (.bvar 0)) →
      Cert .norm Γ e e'
  | norm_proofIrrel : Cert .ty Γ h p → Cert .ty Γ h' p' → Cert .conv Γ p p' →
      Cert .ty Γ p S → Cert .red Γ S (.sort .zero) → Cert .norm Γ h h'
  -- conversion
  | conv_mk : Cert .red Γ a a' → Cert .red Γ b b' → Cert .norm Γ a' b' → Cert .conv Γ a b

/-- Certified synthesis. -/
abbrev CTy := Cert env U .ty
/-- Certified parallel step. -/
abbrev CStep := Cert env U .step
/-- Certified reduction. -/
abbrev CRed := Cert env U .red
/-- Certified normal equality. -/
abbrev CNorm := Cert env U .norm
/-- Certified conversion. -/
abbrev CConv := Cert env U .conv

variable {env U}

/-! ## Soundness -/

/-- The soundness statement of each kind. -/
def Cert.Sound (env : VEnv) (U : Nat) : CKind → List VExpr → VExpr → VExpr → Prop
  | .ty, Γ, e, T => OnCtx Γ (env.IsType U) → env.HasType U Γ e T
  | .step, Γ, a, b | .red, Γ, a, b =>
    OnCtx Γ (env.IsType U) → ∀ A, env.HasType U Γ a A → env.IsDefEq U Γ a b A
  | .norm, Γ, a, b | .conv, Γ, a, b =>
    OnCtx Γ (env.IsType U) → ∀ A B, env.HasType U Γ a A → env.HasType U Γ b B →
      env.IsDefEqU U Γ a b

theorem Cert.sound (henv : env.WF) (H : Cert env U k Γ a b) : Cert.Sound env U k Γ a b := by
  induction H with
  | ty_bvar h => exact fun _ => .bvar h
  | ty_sort h => exact fun _ => .sort h
  | ty_const h1 h2 h3 => exact fun _ => .const h1 h2 h3
  | ty_app _ _ _ _ ihf ihF iha ihA =>
    intro hΓ
    have hf := ihf hΓ
    have ⟨_, hFt⟩ := hf.isType henv.ordered hΓ
    have hF := ihF hΓ _ hFt
    have ha := iha hΓ
    have ⟨_, hA't⟩ := ha.isType henv.ordered hΓ
    have ⟨⟨_, hAt⟩, _⟩ := hF.hasType.2.forallE_inv henv.ordered
    have hA := ihA hΓ _ _ hA't hAt
    exact .app (.defeqDF hF hf) (hA.defeqDF henv hΓ ha)
  | ty_lam _ _ _ ihA ihS ihb =>
    intro hΓ
    have hA := ihA hΓ
    have ⟨_, hSt⟩ := hA.isType henv.ordered hΓ
    have hA := IsDefEq.defeqDF (ihS hΓ _ hSt) hA
    exact .lam hA (ihb ⟨hΓ, _, hA⟩)
  | ty_forallE _ _ _ _ ihA ihS ihB ihS' =>
    intro hΓ
    have hA := ihA hΓ
    have ⟨_, hSt⟩ := hA.isType henv.ordered hΓ
    have hA := IsDefEq.defeqDF (ihS hΓ _ hSt) hA
    have hΓ' : OnCtx (_ :: _) (env.IsType U) := ⟨hΓ, _, hA⟩
    have hB := ihB hΓ'
    have ⟨_, hS't⟩ := hB.isType henv.ordered hΓ'
    exact .forallE hA (IsDefEq.defeqDF (ihS' hΓ' _ hS't) hB)
  | step_bvar | step_sort | step_const => exact fun _ _ ha => ha
  | step_app _ _ ihf iha =>
    intro hΓ A ha
    have ⟨_, _, h1, h2⟩ := ha.app_inv henv hΓ
    exact ha.trans_l henv hΓ (.appDF (ihf hΓ _ h1) (iha hΓ _ h2))
  | step_lam _ _ ihA ihb =>
    intro hΓ A ha
    have ⟨⟨_, h1⟩, _, h2⟩ := ha.lam_inv henv hΓ
    exact ha.trans_l henv hΓ (.lamDF (ihA hΓ _ h1) (ihb ⟨hΓ, _, h1⟩ _ h2))
  | step_forallE _ _ ihA ihB =>
    intro hΓ A ha
    have ⟨⟨_, h1⟩, _, h2⟩ := ha.forallE_inv henv.ordered
    exact ha.trans_l henv hΓ (.forallEDF (ihA hΓ _ h1) (ihB ⟨hΓ, _, h1⟩ _ h2))
  | step_beta _ _ ihb iha =>
    intro hΓ A ha
    have ⟨_, _, h1, h2⟩ := ha.app_inv henv hΓ
    have ⟨⟨_, hAt⟩, _, hbt⟩ := h1.lam_inv henv hΓ
    have hl : env.HasType U _ (.lam _ _) (.forallE _ _) := .lam hAt hbt
    have ⟨_, hPi⟩ := hl.uniq henv hΓ h1
    have ⟨⟨_, hAA⟩, _⟩ := IsDefEqU.forallE_inv henv hΓ ⟨_, hPi⟩
    have h2' : env.HasType U _ _ _ := .defeqDF hAA.symm h2
    have hβ := IsDefEq.beta hbt h2'
    exact ha.trans_l henv hΓ
      (hβ.trans (IsDefEq.instDF henv.ordered hΓ (ihb ⟨hΓ, _, hAt⟩ _ hbt) (iha hΓ _ h2')))
  | step_extra h1 h2 h3 => exact fun hΓ _ ha => ha.trans_l henv hΓ (.extra h1 h2 h3)
  | step_eta _ _ ihe ihF =>
    intro hΓ A ha
    have he := ihe hΓ
    have ⟨_, hFt⟩ := he.isType henv.ordered hΓ
    exact ha.trans_l henv hΓ (IsDefEq.eta (.defeqDF (ihF hΓ _ hFt) he)).symm
  | red_refl => exact fun _ _ ha => ha
  | red_step _ _ ih1 ih2 =>
    intro hΓ A ha
    have h1 := ih1 hΓ _ ha
    exact h1.trans (ih2 hΓ _ h1.hasType.2)
  | norm_bvar => exact fun _ _ _ ha _ => ⟨_, ha⟩
  | norm_sort h1 h2 h3 => exact fun _ _ _ _ _ => ⟨_, .sortDF h1 h2 h3⟩
  | norm_const h1 h2 h3 h4 h5 => exact fun _ _ _ _ _ => ⟨_, .constDF h1 h2 h3 h4 h5⟩
  | norm_app _ _ ihf iha =>
    intro hΓ A B ha hb
    have ⟨_, _, h1, h2⟩ := ha.app_inv henv hΓ
    have ⟨_, _, h3, h4⟩ := hb.app_inv henv hΓ
    exact ⟨_, .appDF ((ihf hΓ _ _ h1 h3).of_l henv hΓ h1) ((iha hΓ _ _ h2 h4).of_l henv hΓ h2)⟩
  | norm_lam _ _ ihA ihb =>
    intro hΓ A B ha hb
    have ⟨⟨_, h1⟩, _, h2⟩ := ha.lam_inv henv hΓ
    have ⟨⟨_, h3⟩, _, h4⟩ := hb.lam_inv henv hΓ
    have hA := (ihA hΓ _ _ h1 h3).of_l henv hΓ h1
    have h4 := h4.defeqDFC henv.ordered (.succ (.zero (Γ₀ := _)) hA.symm)
    have hΓ' : OnCtx (_ :: _) (env.IsType U) := ⟨hΓ, _, h1⟩
    exact ⟨_, .lamDF hA ((ihb hΓ' _ _ h2 h4).of_l henv hΓ' h2)⟩
  | norm_forallE _ _ ihA ihB =>
    intro hΓ A B ha hb
    have ⟨⟨_, h1⟩, _, h2⟩ := ha.forallE_inv henv.ordered
    have ⟨⟨_, h3⟩, _, h4⟩ := hb.forallE_inv henv.ordered
    have hA := (ihA hΓ _ _ h1 h3).of_l henv hΓ h1
    have h4 := h4.defeqDFC henv.ordered (.succ (.zero (Γ₀ := _)) hA.symm)
    have hΓ' : OnCtx (_ :: _) (env.IsType U) := ⟨hΓ, _, h1⟩
    exact ⟨_, .forallEDF hA ((ihB hΓ' _ _ h2 h4).of_l henv hΓ' h2)⟩
  | norm_etaL _ _ _ _ ihe' ihF ihA ihe =>
    intro hΓ A B ha hb
    have ⟨⟨_, hAt⟩, _, het⟩ := ha.lam_inv henv hΓ
    have he' := ihe' hΓ
    have ⟨_, hFt⟩ := he'.isType henv.ordered hΓ
    have hePi' := IsDefEq.defeqDF (ihF hΓ _ hFt) he'
    have ⟨_, hPiT⟩ := hePi'.isType henv.ordered hΓ
    have ⟨⟨_, hA't⟩, _, hB⟩ := hPiT.forallE_inv henv.ordered
    have hA := (ihA hΓ _ _ hAt hA't).of_l henv hΓ hAt
    have he'A : env.HasType U _ _ (.forallE _ _) := .defeqDF (.forallEDF hA.symm hB) hePi'
    have hΓ' : OnCtx (_ :: _) (env.IsType U) := ⟨hΓ, _, hAt⟩
    have happ : env.HasType U (_ :: _) (.app _ (.bvar 0)) _ :=
      .app (he'A.weakN henv.ordered .one) (.bvar .zero)
    have he := (ihe hΓ' _ _ het happ).of_l henv hΓ' het
    exact IsDefEqU.trans henv hΓ ⟨_, IsDefEq.lamDF hAt he⟩ ⟨_, IsDefEq.eta he'A⟩
  | norm_etaR _ _ _ _ ihe ihF ihA ihe' =>
    intro hΓ A B ha hb
    have ⟨⟨_, hAt⟩, _, he't⟩ := hb.lam_inv henv hΓ
    have he := ihe hΓ
    have ⟨_, hFt⟩ := he.isType henv.ordered hΓ
    have hePi := IsDefEq.defeqDF (ihF hΓ _ hFt) he
    have ⟨_, hPiT⟩ := hePi.isType henv.ordered hΓ
    have ⟨⟨_, hA't⟩, _, hB⟩ := hPiT.forallE_inv henv.ordered
    have hA := (ihA hΓ _ _ hAt hA't).of_l henv hΓ hAt
    have heA : env.HasType U _ _ (.forallE _ _) := .defeqDF (.forallEDF hA.symm hB) hePi
    have hΓ' : OnCtx (_ :: _) (env.IsType U) := ⟨hΓ, _, hAt⟩
    have happ : env.HasType U (_ :: _) (.app _ (.bvar 0)) _ :=
      .app (heA.weakN henv.ordered .one) (.bvar .zero)
    have he' := (ihe' hΓ' _ _ happ he't).of_r henv hΓ' he't
    exact IsDefEqU.trans henv hΓ ⟨_, (IsDefEq.eta heA).symm⟩ ⟨_, IsDefEq.lamDF hAt he'⟩
  | norm_etaBoth _ _ _ _ _ _ ihe ihF ihe' ihF' ihA ihb =>
    intro hΓ A B ha hb
    have he := ihe hΓ
    have ⟨_, hFt⟩ := he.isType henv.ordered hΓ
    have hePi := IsDefEq.defeqDF (ihF hΓ _ hFt) he
    have he' := ihe' hΓ
    have ⟨_, hF't⟩ := he'.isType henv.ordered hΓ
    have hePi' := IsDefEq.defeqDF (ihF' hΓ _ hF't) he'
    have ⟨_, hPiT⟩ := hePi.isType henv.ordered hΓ
    have ⟨⟨_, hAt⟩, _, _⟩ := hPiT.forallE_inv henv.ordered
    have ⟨_, hPiT'⟩ := hePi'.isType henv.ordered hΓ
    have ⟨⟨_, hA't⟩, _, hB'⟩ := hPiT'.forallE_inv henv.ordered
    have hA := (ihA hΓ _ _ hAt hA't).of_l henv hΓ hAt
    have he'A : env.HasType U _ _ (.forallE _ _) := .defeqDF (.forallEDF hA.symm hB') hePi'
    have hΓ' : OnCtx (_ :: _) (env.IsType U) := ⟨hΓ, _, hAt⟩
    have happ : env.HasType U (_ :: _) (.app _ (.bvar 0)) _ :=
      .app (hePi.weakN henv.ordered .one) (.bvar .zero)
    have happ' : env.HasType U (_ :: _) (.app _ (.bvar 0)) _ :=
      .app (he'A.weakN henv.ordered .one) (.bvar .zero)
    have hb' := (ihb hΓ' _ _ happ happ').of_l henv hΓ' happ
    exact (IsDefEqU.trans henv hΓ ⟨_, (IsDefEq.eta hePi).symm⟩ ⟨_, IsDefEq.lamDF hAt hb'⟩).trans
      henv hΓ ⟨_, IsDefEq.eta he'A⟩
  | norm_proofIrrel _ _ _ _ _ ihh ihh' ihp ihS ihz =>
    intro hΓ A B _ _
    have hh := ihh hΓ
    have hh' := ihh' hΓ
    have hS := ihS hΓ
    have ⟨_, hSt⟩ := hS.isType henv.ordered hΓ
    have hpP : env.HasType U _ _ (.sort .zero) := .defeqDF (ihz hΓ _ hSt) hS
    have ⟨_, hp't⟩ := hh'.isType henv.ordered hΓ
    have hp := (ihp hΓ _ _ hpP hp't).of_l henv hΓ hpP
    exact ⟨_, .proofIrrel hpP hh (.defeqDF hp.symm hh')⟩
  | conv_mk _ _ _ ih1 ih2 ih3 =>
    intro hΓ A B ha hb
    have h1 := ih1 hΓ _ ha
    have h2 := ih2 hΓ _ hb
    exact (IsDefEqU.trans henv hΓ ⟨_, h1⟩ (ih3 hΓ _ _ h1.hasType.2 h2.hasType.2)).trans
      henv hΓ ⟨_, h2.symm⟩

theorem CTy.hasType (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) (H : CTy env U Γ e T) :
    env.HasType U Γ e T := H.sound henv hΓ

theorem CRed.defeq (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) (H : CRed env U Γ a b)
    (ha : env.HasType U Γ a A) : env.IsDefEq U Γ a b A := H.sound henv hΓ _ ha

theorem CConv.defeq (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) (H : CConv env U Γ a b)
    (ha : env.HasType U Γ a A) (hb : env.HasType U Γ b B) : env.IsDefEqU U Γ a b :=
  H.sound henv hΓ _ _ ha hb

/-! ## Descent: certificates between lifts are lifts of certificates -/

section LiftShapes
open VExpr

theorem _root_.Lean4Lean.VExpr.liftN_eq_bvar (h : liftN n e k = .bvar i) :
    ∃ i₀, e = .bvar i₀ ∧ i = liftVar n i₀ k := by
  cases e <;> simp [liftN] at h; exact ⟨_, rfl, h.symm⟩

theorem _root_.Lean4Lean.VExpr.liftN_eq_sort (h : liftN n e k = .sort l) : e = .sort l := by
  cases e <;> simp [liftN] at h; simp [h]

theorem _root_.Lean4Lean.VExpr.liftN_eq_const (h : liftN n e k = .const c ls) :
    e = .const c ls := by
  cases e <;> simp [liftN] at h; simp [h]

theorem _root_.Lean4Lean.VExpr.liftN_eq_app (h : liftN n e k = .app f a) :
    ∃ f₀ a₀, e = .app f₀ a₀ ∧ f = f₀.liftN n k ∧ a = a₀.liftN n k := by
  cases e <;> simp [liftN] at h; exact ⟨_, _, rfl, h.1.symm, h.2.symm⟩

theorem _root_.Lean4Lean.VExpr.liftN_eq_lam (h : liftN n e k = .lam A b) :
    ∃ A₀ b₀, e = .lam A₀ b₀ ∧ A = A₀.liftN n k ∧ b = b₀.liftN n (k+1) := by
  cases e <;> simp [liftN] at h; exact ⟨_, _, rfl, h.1.symm, h.2.symm⟩

theorem _root_.Lean4Lean.VExpr.liftN_eq_forallE (h : liftN n e k = .forallE A b) :
    ∃ A₀ b₀, e = .forallE A₀ b₀ ∧ A = A₀.liftN n k ∧ b = b₀.liftN n (k+1) := by
  cases e <;> simp [liftN] at h; exact ⟨_, _, rfl, h.1.symm, h.2.symm⟩

/-- Lifting the body of the eta expansion of `e` under its binder. -/
theorem _root_.Lean4Lean.VExpr.liftN_etaBody (e : VExpr) :
    (VExpr.app e.lift (.bvar 0)).liftN n (k+1) = .app (e.liftN n k).lift (.bvar 0) := by
  simp [liftN, lift_liftN']

/-- Lifting the eta expansion of `e` is the eta expansion of the lift. -/
theorem _root_.Lean4Lean.VExpr.liftN_etaExpand (e A : VExpr) :
    (VExpr.lam A (.app e.lift (.bvar 0))).liftN n k =
      .lam (A.liftN n k) (.app (e.liftN n k).lift (.bvar 0)) := by
  simp [liftN, lift_liftN']

end LiftShapes

theorem Lookup.liftN_inv (W : Ctx.LiftN n k Γ Γ') (H : Lookup Γ' (liftVar n i k) A') :
    ∃ A, A' = A.liftN n k ∧ Lookup Γ i A := by
  rw [← Lift.liftVar_consN_skipN] at H
  obtain ⟨A, rfl, h⟩ := H.weakU_inv (Ctx.liftN_iff_lift'.1 W)
  exact ⟨A, by rw [VExpr.lift'_consN_skipN], h⟩

/-- The descent statement of each kind. -/
def Cert.Descends (env : VEnv) (U : Nat) : CKind → List VExpr → VExpr → VExpr → Prop
  | .ty, Γ', e', T' => ∀ {n k Γ e}, Ctx.LiftN n k Γ Γ' → e' = e.liftN n k →
      ∃ T, T' = T.liftN n k ∧ Cert env U .ty Γ e T
  | .step, Γ', a', b' => ∀ {n k Γ a}, Ctx.LiftN n k Γ Γ' → a' = a.liftN n k →
      ∃ b, b' = b.liftN n k ∧ Cert env U .step Γ a b
  | .red, Γ', a', b' => ∀ {n k Γ a}, Ctx.LiftN n k Γ Γ' → a' = a.liftN n k →
      ∃ b, b' = b.liftN n k ∧ Cert env U .red Γ a b
  | .norm, Γ', a', b' => ∀ {n k Γ a b}, Ctx.LiftN n k Γ Γ' → a' = a.liftN n k →
      b' = b.liftN n k → Cert env U .norm Γ a b
  | .conv, Γ', a', b' => ∀ {n k Γ a b}, Ctx.LiftN n k Γ Γ' → a' = a.liftN n k →
      b' = b.liftN n k → Cert env U .conv Γ a b

/-- **Descent.** Every certificate between lifted terms, in a context with inserted binders,
is the lift of a certificate in the smaller context: every term in a certificate is a subterm,
a synthesised type or a reduct of its endpoints, and these are lifts when the endpoints are.
The eta constructors expand at the exposed synthesised domain, the `λ`/`Π` comparisons carry
their domain certificate, and the proof-irrelevance leaf compares synthesised propositions; this
is what makes the induction structural. -/
theorem Cert.descend (henv : env.WF) (H : Cert env U k Γ' a' b') :
    Cert.Descends env U k Γ' a' b' := by
  induction H with
  | ty_bvar h =>
    intro n k Γ e W he
    obtain ⟨i₀, rfl, rfl⟩ := VExpr.liftN_eq_bvar he.symm
    obtain ⟨A, rfl, h'⟩ := Lookup.liftN_inv W h
    exact ⟨A, rfl, .ty_bvar h'⟩
  | ty_sort h =>
    intro n k Γ e W he
    obtain rfl := VExpr.liftN_eq_sort he.symm
    exact ⟨_, rfl, .ty_sort h⟩
  | ty_const h1 h2 h3 =>
    intro n k Γ e W he
    obtain rfl := VExpr.liftN_eq_const he.symm
    exact ⟨_, ((henv.ordered.closedC h1).instL.liftN_eq (Nat.zero_le _)).symm, .ty_const h1 h2 h3⟩
  | ty_app _ _ _ _ ihf ihF iha ihA =>
    intro n k Γ e W he
    obtain ⟨f₀, a₀, rfl, rfl, rfl⟩ := VExpr.liftN_eq_app he.symm
    obtain ⟨F₀, rfl, hf⟩ := ihf W rfl
    obtain ⟨X, hX, hF⟩ := ihF W rfl
    obtain ⟨A₀, B₀, rfl, rfl, rfl⟩ := VExpr.liftN_eq_forallE hX.symm
    obtain ⟨A₀', rfl, ha⟩ := iha W rfl
    have hA := ihA W rfl rfl
    exact ⟨_, (VExpr.liftN_inst_hi ..).symm, .ty_app hf hF ha hA⟩
  | ty_lam _ _ _ ihA ihS ihb =>
    intro n k Γ e W he
    obtain ⟨A₀, b₀, rfl, rfl, rfl⟩ := VExpr.liftN_eq_lam he.symm
    obtain ⟨S₀, rfl, hA⟩ := ihA W rfl
    obtain ⟨X, hX, hS⟩ := ihS W rfl
    obtain rfl := VExpr.liftN_eq_sort hX.symm
    obtain ⟨B₀, rfl, hb⟩ := ihb W.succ rfl
    exact ⟨_, rfl, .ty_lam hA hS hb⟩
  | ty_forallE _ _ _ _ ihA ihS ihB ihS' =>
    intro n k Γ e W he
    obtain ⟨A₀, B₀, rfl, rfl, rfl⟩ := VExpr.liftN_eq_forallE he.symm
    obtain ⟨S₀, rfl, hA⟩ := ihA W rfl
    obtain ⟨X, hX, hS⟩ := ihS W rfl
    obtain rfl := VExpr.liftN_eq_sort hX.symm
    obtain ⟨S₀', rfl, hB⟩ := ihB W.succ rfl
    obtain ⟨X', hX', hS'⟩ := ihS' W.succ rfl
    obtain rfl := VExpr.liftN_eq_sort hX'.symm
    exact ⟨_, rfl, .ty_forallE hA hS hB hS'⟩
  | step_bvar =>
    intro n k Γ a W ha
    obtain ⟨_, rfl, rfl⟩ := VExpr.liftN_eq_bvar ha.symm
    exact ⟨_, rfl, .step_bvar⟩
  | step_sort =>
    intro n k Γ a W ha
    obtain rfl := VExpr.liftN_eq_sort ha.symm
    exact ⟨_, rfl, .step_sort⟩
  | step_const =>
    intro n k Γ a W ha
    obtain rfl := VExpr.liftN_eq_const ha.symm
    exact ⟨_, rfl, .step_const⟩
  | step_app _ _ ihf iha =>
    intro n k Γ a W ha
    obtain ⟨f₀, a₀, rfl, rfl, rfl⟩ := VExpr.liftN_eq_app ha.symm
    obtain ⟨_, rfl, hf⟩ := ihf W rfl
    obtain ⟨_, rfl, ha⟩ := iha W rfl
    exact ⟨_, rfl, .step_app hf ha⟩
  | step_lam _ _ ihA ihb =>
    intro n k Γ a W ha
    obtain ⟨A₀, b₀, rfl, rfl, rfl⟩ := VExpr.liftN_eq_lam ha.symm
    obtain ⟨_, rfl, hA⟩ := ihA W rfl
    obtain ⟨_, rfl, hb⟩ := ihb W.succ rfl
    exact ⟨_, rfl, .step_lam hA hb⟩
  | step_forallE _ _ ihA ihB =>
    intro n k Γ a W ha
    obtain ⟨A₀, B₀, rfl, rfl, rfl⟩ := VExpr.liftN_eq_forallE ha.symm
    obtain ⟨_, rfl, hA⟩ := ihA W rfl
    obtain ⟨_, rfl, hB⟩ := ihB W.succ rfl
    exact ⟨_, rfl, .step_forallE hA hB⟩
  | step_beta _ _ ihb iha =>
    intro n k Γ a W ha
    obtain ⟨f₀, a₀, rfl, hf, rfl⟩ := VExpr.liftN_eq_app ha.symm
    obtain ⟨A₀, b₀, rfl, rfl, rfl⟩ := VExpr.liftN_eq_lam hf.symm
    obtain ⟨_, rfl, hb⟩ := ihb W.succ rfl
    obtain ⟨_, rfl, ha⟩ := iha W rfl
    exact ⟨_, (VExpr.liftN_inst_hi ..).symm, .step_beta hb ha⟩
  | step_extra h1 h2 h3 =>
    rename_i df ls _
    intro n k Γ a W ha
    have ⟨hl, hr⟩ := henv.ordered.defEqWF h1
    have cl : (df.lhs.instL ls).liftN n k = df.lhs.instL ls :=
      ((hl.closedN henv.ordered ⟨⟩).instL).liftN_eq (Nat.zero_le _)
    have cr : (df.rhs.instL ls).liftN n k = df.rhs.instL ls :=
      ((hr.closedN henv.ordered ⟨⟩).instL).liftN_eq (Nat.zero_le _)
    obtain rfl : a = df.lhs.instL ls := VExpr.liftN_inj.1 (ha.symm.trans cl.symm)
    exact ⟨_, cr.symm, .step_extra h1 h2 h3⟩
  | step_eta _ _ ihe ihF =>
    intro n k Γ a W ha
    subst ha
    obtain ⟨_, rfl, he⟩ := ihe W rfl
    obtain ⟨X, hX, hF⟩ := ihF W rfl
    obtain ⟨A₀, B₀, rfl, rfl, rfl⟩ := VExpr.liftN_eq_forallE hX.symm
    exact ⟨_, (VExpr.liftN_etaExpand ..).symm, .step_eta he hF⟩
  | red_refl => intro n k Γ a W ha; exact ⟨_, ha, .red_refl⟩
  | red_step _ _ ih1 ih2 =>
    intro n k Γ a W ha
    obtain ⟨_, rfl, h1⟩ := ih1 W ha
    obtain ⟨_, rfl, h2⟩ := ih2 W rfl
    exact ⟨_, rfl, .red_step h1 h2⟩
  | norm_bvar =>
    intro n k Γ a b W ha hb
    obtain ⟨_, rfl, rfl⟩ := VExpr.liftN_eq_bvar ha.symm
    obtain ⟨_, rfl, h⟩ := VExpr.liftN_eq_bvar hb.symm
    obtain rfl := VExpr.liftVar_inj.1 h
    exact .norm_bvar
  | norm_sort h1 h2 h3 =>
    intro n k Γ a b W ha hb
    obtain rfl := VExpr.liftN_eq_sort ha.symm
    obtain rfl := VExpr.liftN_eq_sort hb.symm
    exact .norm_sort h1 h2 h3
  | norm_const h1 h2 h3 h4 h5 =>
    intro n k Γ a b W ha hb
    obtain rfl := VExpr.liftN_eq_const ha.symm
    obtain rfl := VExpr.liftN_eq_const hb.symm
    exact .norm_const h1 h2 h3 h4 h5
  | norm_app _ _ ihf iha =>
    intro n k Γ a b W ha hb
    obtain ⟨_, _, rfl, rfl, rfl⟩ := VExpr.liftN_eq_app ha.symm
    obtain ⟨_, _, rfl, rfl, rfl⟩ := VExpr.liftN_eq_app hb.symm
    exact .norm_app (ihf W rfl rfl) (iha W rfl rfl)
  | norm_lam _ _ ihA ihb =>
    intro n k Γ a b W ha hb
    obtain ⟨_, _, rfl, rfl, rfl⟩ := VExpr.liftN_eq_lam ha.symm
    obtain ⟨_, _, rfl, rfl, rfl⟩ := VExpr.liftN_eq_lam hb.symm
    exact .norm_lam (ihA W rfl rfl) (ihb W.succ rfl rfl)
  | norm_forallE _ _ ihA ihB =>
    intro n k Γ a b W ha hb
    obtain ⟨_, _, rfl, rfl, rfl⟩ := VExpr.liftN_eq_forallE ha.symm
    obtain ⟨_, _, rfl, rfl, rfl⟩ := VExpr.liftN_eq_forallE hb.symm
    exact .norm_forallE (ihA W rfl rfl) (ihB W.succ rfl rfl)
  | norm_etaL _ _ _ _ ihe' ihF ihA ihe =>
    intro n k Γ a b W ha hb
    obtain ⟨_, _, rfl, rfl, rfl⟩ := VExpr.liftN_eq_lam ha.symm
    subst hb
    obtain ⟨_, rfl, he'⟩ := ihe' W rfl
    obtain ⟨X, hX, hF⟩ := ihF W rfl
    obtain ⟨_, _, rfl, rfl, rfl⟩ := VExpr.liftN_eq_forallE hX.symm
    have hA := ihA W rfl rfl
    have he := ihe W.succ rfl (VExpr.liftN_etaBody _).symm
    exact .norm_etaL he' hF hA he
  | norm_etaR _ _ _ _ ihe ihF ihA ihe' =>
    intro n k Γ a b W ha hb
    obtain ⟨_, _, rfl, rfl, rfl⟩ := VExpr.liftN_eq_lam hb.symm
    subst ha
    obtain ⟨_, rfl, he⟩ := ihe W rfl
    obtain ⟨X, hX, hF⟩ := ihF W rfl
    obtain ⟨_, _, rfl, rfl, rfl⟩ := VExpr.liftN_eq_forallE hX.symm
    have hA := ihA W rfl rfl
    have he' := ihe' W.succ (VExpr.liftN_etaBody _).symm rfl
    exact .norm_etaR he hF hA he'
  | norm_etaBoth _ _ _ _ _ _ ihe ihF ihe' ihF' ihA ihb =>
    intro n k Γ a b W ha hb
    subst ha hb
    obtain ⟨_, rfl, he⟩ := ihe W rfl
    obtain ⟨X, hX, hF⟩ := ihF W rfl
    obtain ⟨_, _, rfl, rfl, rfl⟩ := VExpr.liftN_eq_forallE hX.symm
    obtain ⟨_, rfl, he'⟩ := ihe' W rfl
    obtain ⟨X', hX', hF'⟩ := ihF' W rfl
    obtain ⟨_, _, rfl, rfl, rfl⟩ := VExpr.liftN_eq_forallE hX'.symm
    have hA := ihA W rfl rfl
    have hb := ihb W.succ (VExpr.liftN_etaBody _).symm (VExpr.liftN_etaBody _).symm
    exact .norm_etaBoth he hF he' hF' hA hb
  | norm_proofIrrel _ _ _ _ _ ihh ihh' ihp ihS ihz =>
    intro n k Γ a b W ha hb
    subst ha hb
    obtain ⟨_, rfl, hh⟩ := ihh W rfl
    obtain ⟨_, rfl, hh'⟩ := ihh' W rfl
    have hp := ihp W rfl rfl
    obtain ⟨_, rfl, hS⟩ := ihS W rfl
    obtain ⟨X, hX, hz⟩ := ihz W rfl
    obtain rfl := VExpr.liftN_eq_sort hX.symm
    exact .norm_proofIrrel hh hh' hp hS hz
  | conv_mk _ _ _ ih1 ih2 ih3 =>
    intro n k Γ a b W ha hb
    obtain ⟨_, rfl, h1⟩ := ih1 W ha
    obtain ⟨_, rfl, h2⟩ := ih2 W hb
    exact .conv_mk h1 h2 (ih3 W rfl rfl)

theorem CConv.descend (henv : env.WF) (W : Ctx.LiftN n k Γ Γ')
    (H : CConv env U Γ' (a.liftN n k) (b.liftN n k)) : CConv env U Γ a b :=
  Cert.descend henv H W rfl rfl

theorem CTy.descend (henv : env.WF) (W : Ctx.LiftN n k Γ Γ')
    (H : CTy env U Γ' (e.liftN n k) T') : ∃ T, T' = T.liftN n k ∧ CTy env U Γ e T :=
  Cert.descend henv H W rfl

end VEnv
end Lean4Lean
