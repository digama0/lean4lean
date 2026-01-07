import Lean4Lean.Theory.VExpr

namespace Lean4Lean

open VExpr

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

def Pattern.OnArgs (P : VExpr → Prop) : Pattern → Prop
  | .const .. => True
  | .var f => f.OnArgs P
  | .app f a => f.OnArgs P ∧ a.OnArgs P ∧ ∀ e m1 m2, a.Matches e m1 m2 → P e

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
