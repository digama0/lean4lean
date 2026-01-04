import Lean4Lean.Theory.Typing.Lemmas

namespace Lean4Lean

open VExpr

variable (IsDefEq : List VExpr → VExpr → VExpr → Prop) (Γ₀ : List VExpr) in
inductive IsDefEqCtx : List VExpr → List VExpr → Prop
  | zero : IsDefEqCtx Γ₀ Γ₀
  | succ : IsDefEqCtx Γ₁ Γ₂ → IsDefEq Γ₁ A₁ A₂ → IsDefEqCtx (A₁ :: Γ₁) (A₂ :: Γ₂)

inductive Pattern where
  | const (c : Name)
  | app (f a : Pattern)
  | var (f : Pattern)

inductive Subpattern (p : Pattern) : Pattern → Prop where
  | refl : Subpattern p p
  | appL : Subpattern p f → Subpattern p (.app f a)
  | appR : Subpattern p a → Subpattern p (.app f a)
  | varL : Subpattern p f → Subpattern p (.var f)

theorem Subpattern.trans {p₁ p₂ p₃} (H₁ : Subpattern p₁ p₂) (H₂ : Subpattern p₂ p₃) : Subpattern p₁ p₃ := by
  induction H₂ with
  | refl => exact H₁
  | appL _ ih => exact .appL ih
  | appR _ ih => exact .appR ih
  | varL _ ih => exact .varL ih

theorem Subpattern.sizeOf_le {p₁ p₂} (H₁ : Subpattern p₁ p₂) : sizeOf p₁ ≤ sizeOf p₂ := by
  induction H₁ <;> simp <;> omega

theorem Subpattern.antisymm {p₁ p₂} (H₁ : Subpattern p₁ p₂) (H₂ : Subpattern p₂ p₁) : p₂ = p₁ := by
  cases id H₂ with
  | refl => rfl
  | _ h₂ =>
    have H₁ := H₁.sizeOf_le
    have h₂ := h₂.sizeOf_le
    simp at H₁; omega

def Pattern.inter : Pattern → Pattern → Option Pattern
  | .const c, .const c' => if c = c' then some (.const c) else none
  | .app f a, .app f' a' => return .app (← f.inter f') (← a.inter a')
  | .var f, .var f' => return .var (← f.inter f')
  | .app f a, .var f' => return .app (← f.inter f') a
  | .var f, .app f' a' => return .app (← f.inter f') a'
  | _, _ => none

theorem Pattern.inter_self (p : Pattern) : p.inter p = some p := by induction p <;> simp [*, inter]

inductive Pattern.LE : Pattern → Pattern → Prop where
  | refl : LE p p
  | var : LE f f' → LE (.var f) (.var f')
  | app : LE f f' → LE a a' → LE (.app f a) (.app f' a')
  | app_var : LE f f' → LE (.app f a) (.var f')

def Pattern.Path : Pattern → Type × Type
  | .const _ => (Unit, Empty)
  | .app f a => (f.Path.1 ⊕ a.Path.1, f.Path.2 ⊕ a.Path.2)
  | .var f => (f.Path.1, Option f.Path.2)

inductive Pattern.Matches : (p : Pattern) → VExpr → (p.Path.1 → List VLevel) → (p.Path.2 → VExpr) → Prop
  | const : Matches (.const c) (.const c ls) (fun _ => ls) nofun
  | var : Matches f f' f1 g1 → Matches (.var f) (.app f' a') f1 (·.elim a' g1)
  | app : Matches f f' f1 g1 → Matches a a' f2 g2 →
    Matches (.app f a) (.app f' a') (Sum.elim f1 f2) (Sum.elim g1 g2)

theorem Pattern.Matches.uniq {p : Pattern} {e : VExpr} {m1 m2 m1' m2'}
    (H1 : Pattern.Matches p e m1 m2) (H2 : Pattern.Matches p e m1' m2') : m1 = m1' ∧ m2 = m2' := by
  induction H1 <;> cases H2
  · simp
  · next ih _ h => simp [ih h]
  · next ih1 ih2 _ _ _ _ h1 h2 => simp [ih1 h1, ih2 h2]

inductive Pattern.RHS (p : Pattern) where
  | fixed (e : p.Path.1) (c : VExpr) (_ : c.Closed)
  | app (f a : RHS p)
  | var (e : p.Path.2)

inductive Pattern.Check (p : Pattern) where
  | true
  | defeq (x y : RHS p) (rest : Check p)

def Pattern.RHS.apply {p : Pattern}
    (m1 : p.Path.1 → List VLevel) (m2 : p.Path.2 → VExpr) : p.RHS → VExpr
  | .fixed path c _ => c.instL (m1 path)
  | .var path => m2 path
  | .app f a => .app (f.apply m1 m2) (a.apply m1 m2)

theorem Pattern.RHS.liftN_apply {p : Pattern} {m1 m2} (r : p.RHS) :
    (r.apply m1 m2).liftN n k = (r.apply m1 fun x => (m2 x).liftN n k) := by
  induction r <;> simp [*, apply, liftN, ← instL_liftN]
  rw [ClosedN.liftN_eq ‹_› (Nat.zero_le _)]

theorem Pattern.matches_liftN {p : Pattern} {e : VExpr} {m1 m2'} :
    p.Matches (e.liftN n k) m1 m2' ↔
    ∃ m2, p.Matches e m1 m2 ∧ ∀ x, m2' x = (m2 x).liftN n k := by
  constructor
  · intro h; generalize eq : e.liftN n k = e' at h
    induction h generalizing e with
    | const => cases e <;> cases eq; exact ⟨_, .const, nofun⟩
    | var _ ih =>
      cases e <;> cases eq
      have ⟨_, l1, l2⟩ := ih rfl
      refine ⟨_, .var l1, ?_⟩
      rintro (_|_) <;> solve_by_elim
    | app _ _ ih1 ih2 =>
      cases e <;> cases eq
      have ⟨_, l1, l2⟩ := ih1 rfl
      have ⟨_, r1, r2⟩ := ih2 rfl
      refine ⟨_, .app l1 r1, ?_⟩
      rintro (_|_) <;> solve_by_elim
  · intro ⟨m2, h1, h2⟩
    induction h1 with
    | const => exact (show m2' = _ by ext ⟨⟩) ▸ .const
    | var _ ih =>
      have := (ih (h2 <| some ·)).var (a' := ?_)
      rwa [(_ : m2' = _)]; ext (_|_) <;> simp [h2 none]
    | app _ _ ih1 ih2 =>
      have := (ih1 (h2 <| .inl ·)).app (ih2 (h2 <| .inr ·))
      rwa [(_ : m2' = _)]; ext (_|_) <;> rfl

theorem Pattern.RHS.instN_apply {p : Pattern} {m1 m2} (r : p.RHS) :
    (r.apply m1 m2).inst e₀ k = (r.apply m1 fun x => (m2 x).inst e₀ k) := by
  induction r <;> simp [*, apply, inst]
  rw [(ClosedN.instL ‹_›).instN_eq (Nat.zero_le _)]

theorem Pattern.matches_instN {p : Pattern} {e : VExpr} {m1 m2} (H : p.Matches e m1 m2) :
    p.Matches (e.inst e₀ k) m1 fun x => (m2 x).inst e₀ k := by
  induction H with
  | const => erw [show (fun _ : Empty => _) = _ by ext ⟨⟩]; exact .const
  | var _ ih =>
    rw [(_ : (fun _ => _) = _)]; exact ih.var
    ext (_|_) <;> rfl
  | app _ _ ih1 ih2 =>
    rw [(_ : (fun _ => _) = _)]; exact ih1.app ih2
    ext (_|_) <;> rfl

theorem Pattern.matches_inter {p q : Pattern} {e : VExpr} :
    (∃ m1 m2, p.Matches e m1 m2) ∧ (∃ m1 m2, q.Matches e m1 m2) ↔
    (∃ r m1 m2, p.inter q = some r ∧ r.Matches e m1 m2) := by
  constructor
  · rintro ⟨⟨m1, m2, hp⟩, ⟨m3, m4, hq⟩⟩
    induction hp generalizing q  <;> cases hq <;> simp [inter]
    · case const.const => exact ⟨_, _, .const⟩
    · case var.var ih _ _ _ ih' =>
      have ⟨rf, mf1, mf2, hf1, hf2⟩ := ih _ _ ih'
      exact ⟨_, ⟨_, hf1, rfl⟩, _, _, .var hf2⟩
    · case var.app ihf _ _ _ _ _ _ ihf' ha2 =>
      have ⟨rf, mf1, mf2, hf1, hf2⟩ := ihf _ _ ihf'
      exact ⟨_, ⟨_, hf1, rfl⟩, _, _, .app hf2 ha2⟩
    · case app.var ha2 ihf _ _ _ _ ihf' =>
      have ⟨rf, mf1, mf2, hf1, hf2⟩ := ihf _ _ ihf'
      exact ⟨_, ⟨_, hf1, rfl⟩, _, _, .app hf2 ha2⟩
    · case app.app ihf iha _ _ _ _ _ _ ihf' iha' =>
      have ⟨rf, mf1, mf2, hf1, hf2⟩ := ihf _ _ ihf'
      have ⟨ra, ma1, ma2, ha1, ha2⟩ := iha _ _ iha'
      exact ⟨_, ⟨_, hf1, _, ha1, rfl⟩, _, _, .app hf2 ha2⟩
  · rintro ⟨r, m1, m2, h1, h2⟩
    induction p generalizing q e r <;> cases q <;> simp [inter] at h1 <;> [
        obtain ⟨rfl, rfl⟩ := h1; obtain ⟨_, wf, _, wa, rfl⟩ := h1;
        obtain ⟨_, wf, rfl⟩ := h1; obtain ⟨_, wf, rfl⟩ := h1; obtain ⟨_, wf, rfl⟩ := h1
      ] <;> cases h2
    · exact ⟨⟨_, _, .const⟩, ⟨_, _, .const⟩⟩
    · next ihf iha _ _ _ _ _ _ _ _ hf _ _ ha =>
      have ⟨⟨mf1, mf2, hf⟩, ⟨mf1', mf2', hf'⟩⟩ := ihf _ _ _ wf hf
      have ⟨⟨ma1, ma2, ha⟩, ⟨ma1', ma2', ha'⟩⟩ := iha _ _ _ wa ha
      exact ⟨⟨_, _, .app hf ha⟩, ⟨_, _, .app hf' ha'⟩⟩
    · next ihf _ _ _ _ _ _ _ hf _ _ ha =>
      have ⟨⟨mf1, mf2, hf⟩, ⟨mf1', mf2', hf'⟩⟩ := ihf _ _ _ wf hf
      exact ⟨⟨_, _, .app hf ha⟩, ⟨_, _, .var hf'⟩⟩
    · next ihf _ _ _ _ _ _ _ hf _ _ ha' =>
      have ⟨⟨mf1, mf2, hf⟩, ⟨mf1', mf2', hf'⟩⟩ := ihf _ _ _ wf hf
      exact ⟨⟨_, _, .var hf⟩, ⟨_, _, .app hf' ha'⟩⟩
    · next ihf _ _ _ _ _ hf =>
      have ⟨⟨mf1, mf2, hf⟩, ⟨mf1', mf2', hf'⟩⟩ := ihf _ _ _ wf hf
      exact ⟨⟨_, _, .var hf⟩, ⟨_, _, .var hf'⟩⟩

def Pattern.Check.OK (defeq : VExpr → VExpr → Prop) {p : Pattern}
    (m1 : p.Path.1 → List VLevel) (m2 : p.Path.2 → VExpr) : p.Check → Prop
  | .true => True
  | .defeq a b rest => defeq (RHS.apply m1 m2 a) (RHS.apply m1 m2 b) ∧ rest.OK defeq m1 m2

theorem Pattern.Check.OK.map
    {df df' : VExpr → VExpr → Prop} {p : Pattern} {ck : p.Check} {m1 m2 m1' m2'}
    (h : ∀ a b : p.RHS,
      df (a.apply m1 m2) (b.apply m1 m2) → df' (a.apply m1' m2') (b.apply m1' m2'))
    (H : ck.OK df m1 m2) : ck.OK df' m1' m2' := by
  induction ck <;> simp [OK, *] at H ⊢; cases H; constructor <;> solve_by_elim

section
set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEq Γ e1 e2
structure Typing where
  env : VEnv
  -- henv : env.Ordered
  univs : Nat
  IsDefEq : List VExpr → VExpr → VExpr → Prop
  HasType : List VExpr → VExpr → VExpr → Prop
  Pat : (p : Pattern) → p.RHS × p.Check → Prop
  refl : Γ ⊢ e : A → Γ ⊢ e ≡ e
  symm : Γ ⊢ e₁ ≡ e₂ → Γ ⊢ e₂ ≡ e₁
  trans : Γ ⊢ e₁ ≡ e₂ → Γ ⊢ e₂ ≡ e₃ → Γ ⊢ e₁ ≡ e₃
  bvar : Lookup Γ i A → Γ ⊢ .bvar i : A
  sort : u.WF univs → Γ ⊢ .sort u : .sort u.succ
  sortDF : u.WF univs → v.WF univs → u ≈ v → Γ ⊢ .sort u ≡ .sort v
  constDF :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF univs) → (∀ l ∈ ls', l.WF univs) →
    ls.length = ci.uvars → List.Forall₂ (· ≈ ·) ls ls' →
    Γ ⊢ .const c ls ≡ .const c ls'
  appDF : Γ ⊢ f : .forallE A B → Γ ⊢ f ≡ f' → Γ ⊢ a : A → Γ ⊢ a ≡ a' → Γ ⊢ .app f a ≡ .app f' a'
  lamDF : Γ ⊢ A : .sort u → Γ ⊢ A ≡ A' → A::Γ ⊢ body ≡ body' → Γ ⊢ .lam A body ≡ .lam A' body'
  forallEDF :
    Γ ⊢ A : .sort u → Γ ⊢ A ≡ A' →
    A::Γ ⊢ body : .sort v → A::Γ ⊢ body ≡ body' →
    Γ ⊢ .forallE A body ≡ .forallE A' body'
  const :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF univs) → ls.length = ci.uvars →
    Γ ⊢ .const c ls : ci.type.instL ls
  app : Γ ⊢ f : .forallE A B → Γ ⊢ a : A → Γ ⊢ .app f a : .inst B a
  lam : Γ ⊢ A : .sort u → A::Γ ⊢ body : B → Γ ⊢ .lam A body : .forallE A B
  forallE : Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v → Γ ⊢ .forallE A B : .sort (.imax u v)
  beta : A::Γ ⊢ e : B → Γ ⊢ e' : A → Γ ⊢ .app (.lam A e) e' ≡ e.inst e'
  eta : Γ ⊢ e : .forallE A B → Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e
  proofIrrel : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ h'
  extraDF : env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
    Γ ⊢ df.lhs.instL ls ≡ df.rhs.instL ls
  extra : env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
    Γ ⊢ df.lhs.instL ls : df.type.instL ls
  isDefEq_weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    Γ' ⊢ e1.liftN n k ≡ e2.liftN n k ↔ Γ ⊢ e1 ≡ e2
  hasType_weakN_iff (W : Ctx.LiftN n k Γ Γ') : Γ' ⊢ e.liftN n k : A.liftN n k ↔ Γ ⊢ e : A
  hasTypeU_weakN_inv (W : Ctx.LiftN n k Γ Γ') : Γ' ⊢ e.liftN n k : A → ∃ A', Γ ⊢ e : A'
  isDefEq_instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (H : Γ₁ ⊢ e1 ≡ e2) (h₀ : Γ₀ ⊢ e₀ : A₀) : Γ ⊢ e1.inst e₀ k ≡ e2.inst e₀ k
  hasType_instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (H : Γ₁ ⊢ e1 : A) (h₀ : Γ₀ ⊢ e₀ : A₀) : Γ ⊢ e1.inst e₀ k : A.inst e₀ k
  isDefEq_instL (hls : ∀ l ∈ ls, l.WF U')
    (H : Γ ⊢ e1 ≡ e2) : Γ.map (VExpr.instL ls) ⊢ e1.instL ls ≡ e2.instL ls
  hasType_instL (hls : ∀ l ∈ ls, l.WF U')
    (H : Γ ⊢ e : A) : Γ.map (VExpr.instL ls) ⊢ e.instL ls : A.instL ls
  instL_congr : (∀ l ∈ ls, l.WF univs) → (∀ l ∈ ls', l.WF univs) → List.Forall₂ (· ≈ ·) ls ls' →
    Γ ⊢ e : A → Γ.map (VExpr.instL ls) ⊢ e.instL ls ≡ e.instL ls'
  isDefEq_DFC : IsDefEqCtx IsDefEq Γ₀ Γ₁ Γ₂ → Γ₁ ⊢ e1 ≡ e2 → Γ₂ ⊢ e1 ≡ e2
  hasType_DFC : IsDefEqCtx IsDefEq Γ₀ Γ₁ Γ₂ → Γ₁ ⊢ e : A → Γ₂ ⊢ e : A
  has_type : Γ ⊢ e₁ ≡ e₂ → ∃ A, Γ ⊢ e₁ : A
  is_type : Γ ⊢ e : A → ∃ u, Γ ⊢ A : .sort u
  bvar_inv : Γ ⊢ .bvar i : V → ∃ A, Lookup Γ i A
  sort_inv : Γ ⊢ .sort u : V → u.WF univs
  const_inv : Γ ⊢ .const c ls : V →
    ∃ ci, env.constants c = some ci ∧ (∀ l ∈ ls, l.WF univs) ∧ ls.length = ci.uvars
  forallE_inv : Γ ⊢ .forallE A B : V → ∃ u v, Γ ⊢ A : .sort u ∧ A::Γ ⊢ B : .sort v
  app_inv : Γ ⊢ .app f a : V → ∃ A B, Γ ⊢ f : .forallE A B ∧ Γ ⊢ a : A
  lam_inv : Γ ⊢ .lam A e : V → ∃ u B, Γ ⊢ A : .sort u ∧ A::Γ ⊢ e : B
  uniq : Γ ⊢ e : A₁ → Γ ⊢ e : A₂ → Γ ⊢ A₁ ≡ A₂
  defeq_l : Γ ⊢ e₁ ≡ e₂ → Γ ⊢ e₁ : A → Γ ⊢ e₂ : A
  defeq_r : Γ ⊢ A₁ ≡ A₂ → Γ ⊢ e : A₁ → Γ ⊢ e : A₂
  univ_defInv : Γ ⊢ .sort u ≡ .sort v → u ≈ v
  forallE_defInv : Γ ⊢ .forallE A B ≡ .forallE A' B' → Γ ⊢ A ≡ A' ∧ A::Γ ⊢ B ≡ B'
  pat_not_var : ¬Pat (.var p) r
  pat_uniq : Pat p₁ r → Pat p₂ r' → Subpattern p₃ p₁ → p₂.inter p₃ = some p₄ →
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r'
  pat_wf : Pat p r → p.Matches e m1 m2 → Γ ⊢ e : A →
    r.2.OK (IsDefEq Γ) m1 m2 → Γ ⊢ e ≡ r.1.apply m1 m2
  extra_pat : env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
    ∃ p r m1 m2, Pat p r ∧ p.Matches (df.lhs.instL ls) m1 m2 ∧ r.2.OK (IsDefEq Γ) m1 m2 ∧
    df.rhs.instL ls = r.1.apply m1 m2

variable {TY : Typing}

theorem Typing.symm_ctx (H : IsDefEqCtx TY.IsDefEq Γ₀ Γ₁ Γ₂) : IsDefEqCtx TY.IsDefEq Γ₀ Γ₂ Γ₁ := by
  induction H with
  | zero => exact .zero
  | succ h1 h2 ih => exact .succ ih (TY.isDefEq_DFC h1 (TY.symm h2))

theorem Typing.IsDefEq.weakN (W : Ctx.LiftN n k Γ Γ') :
    TY.IsDefEq Γ e1 e2 → TY.IsDefEq Γ' (e1.liftN n k) (e2.liftN n k) := (TY.isDefEq_weakN_iff W).2
theorem Typing.HasType.weakN (W : Ctx.LiftN n k Γ Γ') :
    TY.HasType Γ e A → TY.HasType Γ' (e.liftN n k) (A.liftN n k) := (TY.hasType_weakN_iff W).2

theorem Typing.IsDefEq.instN : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → TY.IsDefEq Γ₁ e1 e2 →
    TY.HasType Γ₀ e₀ A₀ → TY.IsDefEq Γ (e1.inst e₀ k) (e2.inst e₀ k) := TY.isDefEq_instN
theorem Typing.HasType.instN : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → TY.HasType Γ₁ e A →
    TY.HasType Γ₀ e₀ A₀ → TY.HasType Γ (e.inst e₀ k) (A.inst e₀ k) := TY.hasType_instN

theorem Pattern.Check.OK.weakN (W : Ctx.LiftN n k Γ Γ') {p : Pattern}
    (ck : p.Check) {m1 m2} (H : ck.OK (TY.IsDefEq Γ) m1 m2) :
    ck.OK (TY.IsDefEq Γ') m1 fun x => (m2 x).liftN n k := by
  refine H.map fun a b h => ?_
  simp only [← Pattern.RHS.liftN_apply]
  exact h.weakN W

theorem Pattern.Check.OK.instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H₀ : TY.HasType Γ₀ e₀ A₀)
    {p : Pattern} (ck : p.Check) {m1 m2} (H : ck.OK (TY.IsDefEq Γ₁) m1 m2) :
    ck.OK (TY.IsDefEq Γ) m1 fun x => (m2 x).inst e₀ k := by
  refine H.map fun a b h => ?_
  simp only [← Pattern.RHS.instN_apply]
  exact h.instN W H₀

open Pattern.RHS in
theorem Typing.IsDefEq.apply_pat
    (ih : ∀ a A, TY.HasType Γ (m2 a) A →  TY.IsDefEq Γ (m2 a) (m2' a))
    (he : TY.HasType Γ (apply m1 m2 r) A) :
     TY.IsDefEq Γ (apply m1 m2 r) (apply m1 m2' r) := by
  induction r generalizing A with simp [apply] at he ⊢
  | fixed path c _ => exact TY.refl he
  | app hf ha ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := TY.app_inv he
    exact TY.appDF h1 (ih1 h1) h2 (ih2 h2)
  | var path => exact ih path _ he

theorem Pattern.Matches.hasType {p : Pattern} {e : VExpr} {m1 m2}
    (H : p.Matches e m1 m2) (H2 : TY.HasType Γ e V) (a) : ∃ A, TY.HasType Γ (m2 a) A := by
  induction H generalizing V with
  | const => cases a
  | var _ ih =>
    have ⟨_, _, hf, ha⟩ := TY.app_inv H2
    exact a.rec ⟨_, ha⟩ (ih hf)
  | app _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := TY.app_inv H2
    exact a.rec (ih1 hf) (ih2 ha)

end

section
set_option hygiene false
variable (TY : Typing)
local notation:65 Γ " ⊢ " e " : " A:30 => TY.HasType Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:30 => TY.IsDefEq Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2

inductive NormalEq : List VExpr → VExpr → VExpr → Prop where
  | refl : Γ ⊢ e : A → Γ ⊢ e ≡ₚ e
  | sortDF : l₁.WF TY.univs → l₂.WF TY.univs → l₁ ≈ l₂ → Γ ⊢ .sort l₁ ≡ₚ .sort l₂
  | constDF :
    TY.env.constants c = some ci →
    (∀ l ∈ ls, l.WF TY.univs) →
    (∀ l ∈ ls', l.WF TY.univs) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    Γ ⊢ .const c ls ≡ₚ .const c ls'
  | appDF :
    Γ ⊢ f₁ : .forallE A B → Γ ⊢ f₂ : .forallE A B →
    Γ ⊢ a₁ : A → Γ ⊢ a₂ : A →
    Γ ⊢ f₁ ≡ₚ f₂ → Γ ⊢ a₁ ≡ₚ a₂ →
    Γ ⊢ .app f₁ a₁ ≡ₚ .app f₂ a₂
  | lamDF :
    Γ ⊢ A : .sort u → Γ ⊢ A₁ ≡ A → Γ ⊢ A₂ ≡ A →
    A::Γ ⊢ body₁ ≡ₚ body₂ →
    Γ ⊢ .lam A₁ body₁ ≡ₚ .lam A₂ body₂
  | forallEDF :
    Γ ⊢ A : .sort u → Γ ⊢ A₁ ≡ A → Γ ⊢ A₁ ≡ₚ A₂ →
    A::Γ ⊢ B₁ : .sort v → A::Γ ⊢ B₁ ≡ₚ B₂ →
    Γ ⊢ .forallE A₁ B₁ ≡ₚ .forallE A₂ B₂
  | etaL :
    Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ e ≡ₚ .app e'.lift (.bvar 0) →
    Γ ⊢ .lam A e ≡ₚ e'
  | etaR :
    Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ .app e'.lift (.bvar 0) ≡ₚ e →
    Γ ⊢ e' ≡ₚ .lam A e
  | proofIrrel :
    Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p →
    Γ ⊢ h ≡ₚ h'

end

theorem NormalEq.defeq (H : NormalEq TY Γ e1 e2) : TY.IsDefEq Γ e1 e2 := by
  induction H with
  | refl h => exact TY.refl h
  | sortDF h1 h2 h3 => exact TY.sortDF h1 h2 h3
  | appDF hf₁ _ ha₁ _ _ _ ih1 ih2 => exact TY.appDF hf₁ ih1 ha₁ ih2
  | constDF h1 h2 h3 h4 h5 => exact TY.constDF h1 h2 h3 h4 h5
  | lamDF hA hA₁ hA₂ _ ihB =>
    have ⟨_, hB⟩ := TY.has_type ihB
    exact TY.trans (TY.symm <| TY.lamDF hA (TY.symm hA₁) (TY.refl hB))
      (TY.lamDF hA (TY.symm hA₂) ihB)
  | forallEDF hA hA₁ _ hB₁ _ ihA ihB =>
    exact TY.trans (TY.symm <| TY.forallEDF hA (TY.symm hA₁) hB₁ (TY.refl hB₁))
      (TY.forallEDF hA (TY.trans (TY.symm hA₁) ihA) hB₁ ihB)
  | etaL h1 _ ih =>
    have ⟨_, AB⟩ := TY.is_type h1
    have ⟨_, _, hA, _⟩ := TY.forallE_inv AB
    exact TY.trans (TY.lamDF hA (TY.refl hA) ih) (TY.eta h1)
  | etaR h1 _ ih =>
    have ⟨_, AB⟩ := TY.is_type h1
    have ⟨_, _, hA, _⟩ := TY.forallE_inv AB
    exact TY.trans (TY.symm (TY.eta h1)) (TY.lamDF hA (TY.refl hA) ih)
  | proofIrrel h1 h2 h3 => exact TY.proofIrrel h1 h2 h3

theorem NormalEq.symm (H : NormalEq TY Γ e1 e2) : NormalEq TY Γ e2 e1 := by
  induction H with
  | refl h => exact .refl h
  | sortDF h1 h2 h3 => exact .sortDF h2 h1 h3.symm
  | constDF h1 h2 h3 h4 h5 =>
    exact .constDF h1 h3 h2 (h5.length_eq.symm.trans h4) (h5.flip.imp (fun _ _ h => h.symm))
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 => exact .appDF h2 h1 h4 h3 ih1 ih2
  | lamDF h1 h2 h3 _ ih1 => exact .lamDF h1 h3 h2 ih1
  | forallEDF h1 h2 _ h4 h5 ih1 ih2 =>
    exact .forallEDF h1 (TY.trans ih1.defeq h2) ih1 (TY.defeq_l h5.defeq h4) ih2
  | etaL h1 _ ih => exact .etaR h1 ih
  | etaR h1 _ ih => exact .etaL h1 ih
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h3 h2

theorem NormalEq.weakN (W : Ctx.LiftN n k Γ Γ') (H : NormalEq TY Γ e1 e2) :
    NormalEq TY Γ' (e1.liftN n k) (e2.liftN n k) := by
  induction H generalizing k Γ' with
  | refl h => exact .refl (h.weakN W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (h1.weakN W) (h2.weakN W) (h3.weakN W) (h4.weakN W) (ih1 W) (ih2 W)
  | lamDF h1 h2 h3 _ ih1 => exact .lamDF (h1.weakN W) (h2.weakN W) (h3.weakN W) (ih1 W.succ)
  | forallEDF h1 h2 _ h4 _ ih1 ih2 =>
    exact .forallEDF (h1.weakN W) (h2.weakN W) (ih1 W) (h4.weakN W.succ) (ih2 W.succ)
  | etaL h1 _ ih =>
    refine .etaL (h1.weakN W) ?_
    have := ih W.succ
    simp [liftN] at this; rwa [lift_liftN']
  | etaR h1 _ ih =>
    refine .etaR (h1.weakN W) ?_
    have := ih W.succ
    simp [liftN] at this; rwa [lift_liftN']
  | proofIrrel h1 h2 h3 =>
    exact .proofIrrel (h1.weakN W) (h2.weakN W) (h3.weakN W)

variable! (h₀ : Typing.HasType TY Γ₀ e₀ A₀) in
theorem NormalEq.instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : NormalEq TY Γ₁ e1 e2) :
    NormalEq TY Γ (e1.inst e₀ k) (e2.inst e₀ k) := by
  induction H generalizing Γ k with
  | refl h => exact .refl (h.instN W h₀)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (h1.instN W h₀) (h2.instN W h₀) (h3.instN W h₀) (h4.instN W h₀) (ih1 W) (ih2 W)
  | lamDF h1 h2 h3 _ ih1 =>
    exact .lamDF (h1.instN W h₀) (h2.instN W h₀) (h3.instN W h₀) (ih1 W.succ)
  | forallEDF h1 h2 _ h4 _ ih1 ih2 =>
    exact .forallEDF (h1.instN W h₀) (h2.instN W h₀) (ih1 W) (h4.instN W.succ h₀) (ih2 W.succ)
  | etaL h1 _ ih =>
    refine .etaL (h1.instN W h₀) ?_
    simpa [inst, lift_instN_lo] using ih W.succ
  | etaR h1 _ ih =>
    refine .etaR (h1.instN W h₀) ?_
    simpa [inst, lift_instN_lo] using ih W.succ
  | proofIrrel h1 h2 h3 => exact .proofIrrel (h1.instN W h₀) (h2.instN W h₀) (h3.instN W h₀)

variable! (h₀ : Typing.HasType TY Γ₀ e₀ A₀) (H' : NormalEq TY Γ₀ e₀ e₀') in
theorem NormalEq.instN_r (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : Typing.HasType TY Γ₁ e A) :
    NormalEq TY Γ (e.inst e₀ k) (e.inst e₀' k) := by
  induction e generalizing Γ₁ Γ k A with dsimp [inst]
  | bvar i =>
    have ⟨ty, h⟩ := TY.bvar_inv H; clear H
    induction W generalizing i ty with
    | zero =>
      cases h with simp
      | zero => exact H'
      | succ h => exact .refl (TY.bvar h)
    | succ _ ih =>
      cases h with simp
      | zero => exact .refl (TY.bvar .zero)
      | succ h => exact (ih _ _ h).weakN .one
  | sort => exact .refl (TY.sort (TY.sort_inv H))
  | const =>
    let ⟨_, h1, h2, h3⟩ := TY.const_inv H
    exact .refl (TY.const h1 h2 h3)
  | app fn arg ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := TY.app_inv H
    specialize ih1 W h1; have hf := h1.instN W h₀
    specialize ih2 W h2; have ha := h2.instN W h₀
    exact .appDF hf (TY.defeq_l ih1.defeq hf) ha (TY.defeq_l ih2.defeq ha) ih1 ih2
  | lam A body ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := TY.lam_inv H
    have hA := h1.instN W h₀
    exact .lamDF hA (TY.refl hA) (ih1 W h1).symm.defeq (ih2 W.succ h2)
  | forallE A B ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := TY.forallE_inv H
    have hA := h1.instN W h₀
    exact .forallEDF hA (TY.refl hA) (ih1 W h1) (h2.instN W.succ h₀) (ih2 W.succ h2)

variable {TY : Typing} in
theorem NormalEq.defeqDFC (W : IsDefEqCtx TY.IsDefEq Γ₀ Γ₁ Γ₂)
    (H : NormalEq TY Γ₁ e1 e2) : NormalEq TY Γ₂ e1 e2 := by
  induction H generalizing Γ₂ with
  | refl h => refine .refl (TY.hasType_DFC W h)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (TY.hasType_DFC W h1) (TY.hasType_DFC W h2)
      (TY.hasType_DFC W h3) (TY.hasType_DFC W h4) (ih1 W) (ih2 W)
  | lamDF h1 h2 h3 _ ih1 =>
    exact .lamDF (TY.hasType_DFC W h1) (TY.isDefEq_DFC W h2) (TY.isDefEq_DFC W h3)
      (ih1 (W.succ (TY.refl h1)))
  | forallEDF h1 h2 _ h4 _ ih1 ih2 =>
    exact .forallEDF (TY.hasType_DFC W h1) (TY.isDefEq_DFC W h2) (ih1 W)
      (TY.hasType_DFC (W.succ (TY.refl h1)) h4) (ih2 (W.succ (TY.refl h1)))
  | etaL h1 _ ih =>
    have ⟨_, _, h2, _⟩ := let ⟨_, h⟩ := TY.is_type h1; TY.forallE_inv h
    refine .etaL (TY.hasType_DFC W h1) (ih (W.succ (TY.refl h2)))
  | etaR h1 _ ih =>
    have ⟨_, _, h2, _⟩ := let ⟨_, h⟩ := TY.is_type h1; TY.forallE_inv h
    refine .etaR (TY.hasType_DFC W h1) (ih (W.succ (TY.refl h2)))
  | proofIrrel h1 h2 h3 =>
    exact .proofIrrel (TY.hasType_DFC W h1)
      (TY.hasType_DFC W h2) (TY.hasType_DFC W h3)

theorem NormalEq.defeq_l (W : TY.IsDefEq Γ A A') (H : NormalEq TY (A::Γ) e1 e2) :
    NormalEq TY (A'::Γ) e1 e2 := defeqDFC (.succ .zero W) H

theorem NormalEq.weakN_inv_DFC (W : Ctx.LiftN n k Γ Γ₂) (W₂ : IsDefEqCtx TY.IsDefEq Γ₀ Γ₁ Γ₂)
    (H : NormalEq TY Γ₁ (e1.liftN n k) (e2.liftN n k)) : NormalEq TY Γ e1 e2 := by
  generalize eq1 : e1.liftN n k = e1' at H
  generalize eq2 : e2.liftN n k = e2' at H
  induction H generalizing Γ Γ₂ e1 e2 k with
  | refl h =>
    cases eq2; cases liftN_inj.1 eq1
    have ⟨_, h'⟩ := TY.hasTypeU_weakN_inv W (TY.hasType_DFC W₂ h)
    exact .refl h'
  | sortDF h1 h2 h3 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    replace h1 := TY.hasType_DFC W₂ h1
    replace h2 := TY.hasType_DFC W₂ h2
    replace h3 := TY.hasType_DFC W₂ h3
    replace h4 := TY.hasType_DFC W₂ h4
    have ⟨_, _, l1, l2⟩ :=
      let ⟨_, h⟩ := TY.hasTypeU_weakN_inv W (TY.app h1 h3) (e := .app ..); TY.app_inv h
    have ⟨_, _, r1, r2⟩ :=
      let ⟨_, h⟩ := TY.hasTypeU_weakN_inv W (TY.app h2 h4) (e := .app ..); TY.app_inv h
    have := (TY.isDefEq_weakN_iff W).1
      (TY.trans (TY.uniq (l1.weakN W) h1) (TY.uniq h2 (r1.weakN W)))
    exact .appDF (TY.defeq_r this l1) r1
      (TY.defeq_r (TY.forallE_defInv this).1 l2) r2 (ih1 W W₂ rfl rfl) (ih2 W W₂ rfl rfl)
  | lamDF h1 h2 h3 _ ih1 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    have := (TY.hasType_weakN_iff (A := .sort ..) W).1 <|
      TY.hasType_DFC W₂ (TY.defeq_l (TY.symm h2) h1)
    have h5 := (TY.isDefEq_weakN_iff W).1 <| TY.isDefEq_DFC W₂ (TY.trans h3 (TY.symm h2))
    exact .lamDF this (TY.refl this) h5 (ih1 W.succ (W₂.succ (TY.symm h2)) rfl rfl)
  | forallEDF h1 h2 _ h4 _ ih1 ih2 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    replace h4 := (TY.hasType_weakN_iff (A := .sort ..) W.succ).1 <|
      TY.hasType_DFC (W₂.succ (TY.symm h2)) h4
    have := (TY.hasType_weakN_iff (A := .sort ..) W).1 <|
      TY.hasType_DFC W₂ (TY.defeq_l (TY.symm h2) h1)
    exact .forallEDF this (TY.refl this)
      (ih1 W W₂ rfl rfl) h4 (ih2 W.succ (W₂.succ (TY.symm h2)) rfl rfl)
  | etaL h1 _ ih =>
    cases e1 <;> cases eq1
    subst eq2
    have ⟨_, _, hA, hB⟩ := let ⟨_, h⟩ := TY.is_type h1; TY.forallE_inv h
    have h1' := TY.hasType_DFC W₂ h1
    have hA' := TY.hasType_DFC W₂ hA
    have hB' := TY.hasType_DFC (W₂.succ (TY.refl hA)) hB
    have := TY.app (h1'.weakN .one) (TY.bvar .zero)
    rw [instN_bvar0, ← lift, lift_liftN',
      ← show liftN n (.bvar 0) (k+1) = bvar 0 by simp [liftN],
      ← liftN] at this
    have ⟨C, hC⟩ := TY.hasTypeU_weakN_inv W.succ this
    have := (TY.hasType_weakN_iff (A := .forallE ..) W).1 <|
      TY.defeq_r (TY.forallEDF hA' (TY.refl hA') hB' (TY.uniq this (hC.weakN W.succ))) h1'
    refine .etaL this (ih W.succ (W₂.succ (TY.refl hA)) rfl (by simp [liftN, lift_liftN']))
  | etaR h1 _ ih =>
    subst eq1
    cases e2 <;> cases eq2
    have ⟨_, _, hA, hB⟩ := let ⟨_, h⟩ := TY.is_type h1; TY.forallE_inv h
    have h1' := TY.hasType_DFC W₂ h1
    have hA' := TY.hasType_DFC W₂ hA
    have hB' := TY.hasType_DFC (W₂.succ (TY.refl hA)) hB
    have := TY.app (h1'.weakN .one) (TY.bvar .zero)
    rw [instN_bvar0, ← lift, lift_liftN',
      ← show liftN n (.bvar 0) (k+1) = bvar 0 by simp [liftN],
      ← liftN] at this
    have ⟨C, hC⟩ := TY.hasTypeU_weakN_inv W.succ this
    have := (TY.hasType_weakN_iff (A := .forallE ..) W).1 <|
      TY.defeq_r (TY.forallEDF hA' (TY.refl hA') hB' (TY.uniq this (hC.weakN W.succ))) h1'
    refine .etaR this (ih W.succ (W₂.succ (TY.refl hA)) (by simp [liftN, lift_liftN']) rfl)
  | proofIrrel h1 h2 h3 =>
    subst eq1; subst eq2
    have h1' := TY.hasType_DFC W₂ h1
    have h2' := TY.hasType_DFC W₂ h2
    have h3' := TY.hasType_DFC W₂ h3
    have ⟨_, h⟩ := TY.hasTypeU_weakN_inv W h2'
    have hw := TY.uniq h2' (h.weakN W)
    exact .proofIrrel
      ((TY.hasType_weakN_iff (A := .sort ..) W).1 (TY.defeq_l hw h1'))
      ((TY.hasType_weakN_iff W).1 (TY.defeq_r hw h2'))
      ((TY.hasType_weakN_iff W).1 (TY.defeq_r hw h3'))

theorem NormalEq.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    NormalEq TY Γ' (e1.liftN n k) (e2.liftN n k) ↔ NormalEq TY Γ e1 e2 :=
  ⟨fun H => H.weakN_inv_DFC W .zero, fun H => H.weakN W⟩

private def meas : VExpr → Nat
  | .app f a
  | .forallE f a => meas f + meas a + 1
  | .bvar _ | .const .. | .sort _ => 0
  | .lam A e => meas A + meas e + 3

private theorem meas_liftN : meas (e.liftN n k) = meas e := by
  induction e generalizing k <;> simp [*, meas, liftN]
private theorem meas_lift : meas e.lift = meas e := meas_liftN

attribute [local simp] meas meas_lift in
theorem NormalEq.trans : NormalEq TY Γ e1 e2 → NormalEq TY Γ e2 e3 → NormalEq TY Γ e1 e3
  | .sortDF l1 _ l3, .sortDF r1 r2 r3 => .sortDF l1 r2 (l3.trans r3)
  | .constDF l1 l2 _ l4 l5, .constDF _ _ r3 r4 r5 =>
    .constDF l1 l2 r3 l4 (l5.trans (fun _ _ _ h1 => h1.trans) r5)
  | .appDF l1 l2 l3 l4 l5 l6, .appDF r1 r2 r3 r4 r5 r6 =>
    .appDF l1 (TY.defeq_r (TY.uniq r1 l2) r2) l3
      (TY.defeq_r (TY.uniq r3 l4) r4) (NormalEq.trans l5 r5) (NormalEq.trans l6 r6)
  | .lamDF l1 l2 l3 l4, .lamDF _ r2 r3 r4 =>
    have aa := TY.trans (TY.symm r2) l3
    .lamDF l1 l2 (TY.trans r3 aa) (NormalEq.trans l4 (r4.defeq_l aa))
  | .forallEDF l1 l2 l3 l4 l5, .forallEDF _ r2 r3 r4 r5 =>
    have r5' := r5.defeq_l (TY.trans (TY.symm (TY.trans l3.defeq r2)) l2)
    .forallEDF l1 l2 (NormalEq.trans l3 r3) l4 (NormalEq.trans l5 r5')
  | .etaR l1 ih, .lamDF _ r2 r3 r4 =>
    have ⟨_, _, hA, hB⟩ := let ⟨_, h⟩ := TY.is_type l1; TY.forallE_inv h
    have eq := TY.trans r2 (TY.symm r3)
    .etaR (TY.defeq_r (TY.forallEDF hA eq hB (TY.refl hB)) l1)
      (NormalEq.trans (ih.defeq_l eq) (r4.defeq_l (TY.symm r3)))
  | .lamDF _ l2 l3 l4, .etaL r1 ih =>
    have ⟨_, _, hA, hB⟩ := let ⟨_, h⟩ := TY.is_type r1; TY.forallE_inv h
    have eq := TY.trans l3 (TY.symm l2)
    .etaL (TY.defeq_r (TY.forallEDF hA eq hB (TY.refl hB)) r1)
      (NormalEq.trans (l4.defeq_l (TY.symm l2)) (ih.defeq_l eq))
  | H1@(.etaR l1 ihl), .etaL r1 ihr => by
    have := NormalEq.trans ihl ihr
    generalize eq : e1.lift = e1' at this
    have ⟨_, _, hA, _⟩ := let ⟨_, h⟩ := TY.is_type l1; TY.forallE_inv h
    cases this with first | cases eq | cases liftN_inj.1 eq
    | refl h => exact .refl r1
    | proofIrrel h1 h2 h3 =>
      refine .proofIrrel (TY.defeq_r ?_ (TY.forallE hA h1))
        (TY.defeq_l (TY.eta l1) (TY.lam hA h2)) (TY.defeq_l (TY.eta r1) (TY.lam hA h3))
      have hw := let ⟨_, h⟩ := TY.is_type hA; TY.sort_inv h
      exact TY.sortDF ⟨hw, ⟨⟩⟩ ⟨⟩ rfl
    | appDF _ _ _ _ ih => exact (NormalEq.weakN_iff .one).1 ih
  | .refl h, H2 => H2
  | .proofIrrel l1 l2 l3, H2 => .proofIrrel l1 l2 (TY.defeq_l H2.defeq l3)
  | .etaL l1 ih, H2 => by
    refine .etaL (TY.defeq_l H2.defeq l1) (NormalEq.trans ih ?_)
    exact .appDF (l1.weakN .one)
      ((TY.defeq_l H2.defeq l1).weakN .one) (TY.bvar .zero) (TY.bvar .zero)
      (.weakN .one H2) (.refl (TY.bvar .zero))
  | H1, .refl _ => H1
  | H1, .etaR r1 ih => by
    refine .etaR (TY.defeq_l H1.symm.defeq r1) (NormalEq.trans ?_ ih)
    refine .appDF ((TY.defeq_l H1.symm.defeq r1).weakN .one)
      (r1.weakN .one) (TY.bvar .zero) (TY.bvar .zero)
      (.weakN .one H1) (.refl (TY.bvar .zero))
  | H1, .proofIrrel h1 h2 h3 => .proofIrrel h1 (TY.defeq_l H1.symm.defeq h2) h3
termination_by meas e1 + meas e2 + meas e3

open Pattern.RHS in
theorem NormalEq.apply_pat
    (ih : ∀ a A, TY.HasType Γ (m2 a) A → NormalEq TY Γ (m2 a) (m2' a))
    (he : TY.HasType Γ (apply m1 m2 r) A) :
    NormalEq TY Γ (apply m1 m2 r) (apply m1 m2' r) := by
  induction r generalizing A with simp [apply] at he ⊢
  | fixed path c _ => exact .refl he
  | app hf ha ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := TY.app_inv he
    exact .appDF h1 (TY.defeq_l (ih1 h1).defeq h1)
      h2 (TY.defeq_l (ih2 h2).defeq h2) (ih1 h1) (ih2 h2)
  | var path => exact ih path _ he
