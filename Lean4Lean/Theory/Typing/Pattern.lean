import Lean4Lean.Theory.VExpr
import Batteries.Tactic.Init

namespace Lean4Lean

open VExpr

inductive Pattern where
  | const (c : Name)
  | app (f a : Pattern)
  | var (f : Pattern)

def Pattern.varN (p : Pattern) : Nat → Pattern
  | 0 => p
  | n+1 => (p.varN n).var

inductive Subpattern (p : Pattern) : Pattern → Prop where
  | refl : Subpattern p p
  | appL : Subpattern p f → Subpattern p (.app f a)
  | appR : Subpattern p a → Subpattern p (.app f a)
  | varL : Subpattern p f → Subpattern p (.var f)

theorem Subpattern.varN (h : Subpattern p f) : ∀ {n}, Subpattern p (.varN f n)
  | 0 => h
  | _+1 => .varL (.varN h)

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

inductive Arity (p : Pattern) : Nat → Pattern → Prop where
  | refl : Arity p 0 p
  | app : Arity p n f → Arity p (n+1) (.app f a)
  | var : Arity p n f → Arity p (n+1) (.var f)

theorem Arity.subpattern : Arity p n p' → Subpattern p p'
  | .refl => .refl
  | .app h => .appL h.subpattern
  | .var h => .varL h.subpattern

def Pattern.inter : Pattern → Pattern → Option Pattern
  | .const c, .const c' => if c = c' then some (.const c) else none
  | .app f a, .app f' a' => return .app (← f.inter f') (← a.inter a')
  | .var f, .var f' => return .var (← f.inter f')
  | .app f a, .var f' => return .app (← f.inter f') a
  | .var f, .app f' a' => return .app (← f.inter f') a'
  | _, _ => none

theorem Pattern.inter_self (p : Pattern) : p.inter p = some p := by induction p <;> simp [*, inter]

theorem Pattern.inter_comm (p q : Pattern) : p.inter q = q.inter p := by
  induction p generalizing q <;> cases q <;> simp [*, eq_comm, inter] <;> split <;> simp [*]

/-! ### Combinatorics of constructor spines `(.const c).varN k`

An ι redex is built from spines `(.const c).varN k`; these lemmas record that a
spine has no application node and that two spines intersect only when their heads
and lengths agree. -/

/-- Every subpattern of a constructor spine `(.const c).varN k` is a shorter spine
`(.const c).varN i` with `i ≤ k`. -/
theorem Pattern.subpattern_varN_const {c : Name} {q : Pattern} :
    ∀ {k}, Subpattern q ((Pattern.const c).varN k) → ∃ i ≤ k, q = (Pattern.const c).varN i
  | 0, h => by
    simp only [Pattern.varN] at h
    cases h; exact ⟨0, Nat.le_refl _, rfl⟩
  | k+1, h => by
    simp only [Pattern.varN] at h
    cases h with
    | refl => exact ⟨k+1, Nat.le_refl _, rfl⟩
    | varL h =>
      obtain ⟨i, hi, rfl⟩ := subpattern_varN_const h
      exact ⟨i, Nat.le_succ_of_le hi, rfl⟩

/-- A constructor spine `(.const c).varN k` contains no application subpattern:
it is a stack of `.var`s over a `.const`. -/
theorem Pattern.not_app_subpattern_varN_const {c : Name} {a b : Pattern} {k} :
    ¬ Subpattern (.app a b) ((Pattern.const c).varN k) := by
  intro h
  obtain ⟨i, _, hi⟩ := Pattern.subpattern_varN_const h
  cases i <;> simp [Pattern.varN] at hi

/-- Two constructor spines intersect (`Pattern.inter`) to `some` only when their
heads *and* lengths agree, and then the intersection is that same spine. -/
theorem Pattern.varN_const_inter {a b : Name} :
    ∀ {m n r}, ((Pattern.const a).varN m).inter ((Pattern.const b).varN n) = some r →
      a = b ∧ m = n ∧ r = (Pattern.const a).varN m
  | 0, 0, r, h => by
    simp only [Pattern.varN, Pattern.inter] at h
    split at h <;> simp_all [Pattern.varN]
  | 0, n+1, r, h => by simp [Pattern.varN, Pattern.inter] at h
  | m+1, 0, r, h => by simp [Pattern.varN, Pattern.inter] at h
  | m+1, n+1, r, h => by
    simp only [Pattern.varN, Pattern.inter] at h
    cases hr' : ((Pattern.const a).varN m).inter ((Pattern.const b).varN n) with
    | none => rw [hr'] at h; simp at h
    | some r' =>
      obtain ⟨rfl, rfl, rfl⟩ := Pattern.varN_const_inter hr'
      rw [hr'] at h
      simp at h
      exact ⟨rfl, rfl, by simp only [Pattern.varN, ← h]⟩

/-- Constructor spines are equal only when heads and lengths agree: `(.const _).varN`
is injective in both its head and its arity. -/
theorem Pattern.varN_const_inj {a b : Name} {m n}
    (h : (Pattern.const a).varN m = (Pattern.const b).varN n) : a = b ∧ m = n := by
  have hi : ((Pattern.const a).varN m).inter ((Pattern.const b).varN n)
      = some ((Pattern.const a).varN m) := by rw [← h]; exact Pattern.inter_self _
  obtain ⟨rfl, rfl, _⟩ := Pattern.varN_const_inter hi
  exact ⟨rfl, rfl⟩

inductive Pattern.LE : Pattern → Pattern → Prop where
  | refl : LE p p
  | var : LE f f' → LE (.var f) (.var f')
  | app : LE f f' → LE a a' → LE (.app f a) (.app f' a')
  | app_var : LE f f' → LE (.app f a) (.var f')

def Pattern.Path : Pattern → Type
  | .const _ => Empty
  | .app f a => f.Path ⊕ a.Path
  | .var f => Option f.Path

inductive Pattern.Matches : (p : Pattern) → VExpr → List VLevel → (p.Path → VExpr) → Prop
  | const : Matches (.const c) (.const c ls) ls nofun
  | var : Matches f f' f1 g1 → Matches (.var f) (.app f' a') f1 (·.elim a' g1)
  | app : Matches f f' f1 g1 → Matches a a' f2 g2 →
    Matches (.app f a) (.app f' a') f1 (Sum.elim g1 g2)

theorem Pattern.Matches.uniq {p : Pattern} {e : VExpr} {m1 m2 m1' m2'}
    (H1 : Pattern.Matches p e m1 m2) (H2 : Pattern.Matches p e m1' m2') : m1 = m1' ∧ m2 = m2' := by
  induction H1 generalizing m1' with cases H2
  | const => simp
  | var _ ih => rename_i h; simp [ih h]
  | app _ _ ih1 ih2 => rename_i h2 h1; simp [ih1 h1, ih2 h2]; rfl

def Pattern.OnArgs (P : VExpr → Prop) : Pattern → Prop
  | .const .. => True
  | .var f => f.OnArgs P
  | .app f a => f.OnArgs P ∧ a.OnArgs P ∧ ∀ e m1 m2, a.Matches e m1 m2 → P e

inductive Pattern.RHS (p : Pattern) where
  | fixed (c : VExpr) (_ : c.Closed)
  | app (f a : RHS p)
  | var (e : p.Path)

inductive Pattern.Check (p : Pattern) where
  | true
  | defeq (x y : RHS p) (rest : Check p)

def Pattern.RHS.apply {p : Pattern} (m1 : List VLevel) (m2 : p.Path → VExpr) : p.RHS → VExpr
  | .fixed c _ => c.instL m1
  | .var path => m2 path
  | .app f a => .app (f.apply m1 m2) (a.apply m1 m2)

/-- The holes an `RHS` mentions. -/
def Pattern.RHS.Uses {p : Pattern} : p.RHS → p.Path → Prop
  | .fixed _ _, _ => False
  | .var y, x => x = y
  | .app f a, x => f.Uses x ∨ a.Uses x

/-- `m2` instantiates the holes `r` uses generically over a context of length `n`: those
holes are pairwise distinct variables below `n`, and every variable below `n` is one of
them. The holes `r` does not use are unconstrained here — for an ι rule the index arguments
and the constructor's parameter arguments, arbitrary terms over the context. What ties them
to the recursor's arguments is not this predicate but the well-formedness of the block
(`VInductDecl.WF.rules_ctor`, `rec_shape`) together with the typing of an instance. -/
def Pattern.RHS.Generic {p : Pattern} (r : p.RHS) (m2 : p.Path → VExpr) (n : Nat) : Prop :=
  (∀ x, r.Uses x → ∃ i < n, m2 x = .bvar i) ∧
  (∀ x y, r.Uses x → r.Uses y → m2 x = m2 y → x = y) ∧
  (∀ i < n, ∃ x, r.Uses x ∧ m2 x = .bvar i)

theorem Pattern.RHS.lift'_apply {p : Pattern} {m1 m2} (r : p.RHS) :
    (r.apply m1 m2).lift' ρ = (r.apply m1 fun x => (m2 x).lift' ρ) := by
  induction r <;> simp [*, apply, lift', ← instL_lift']
  rw [ClosedN.lift'_eq ‹_› (by trivial)]

theorem Pattern.RHS.liftN_apply {p : Pattern} {m1 m2} (r : p.RHS) :
    (r.apply m1 m2).liftN n k = (r.apply m1 fun x => (m2 x).liftN n k) := by
  simp [← lift'_consN_skipN, lift'_apply]

theorem Pattern.matches_lift' {p : Pattern} {e : VExpr} {m1 m2'} :
    p.Matches (e.lift' ρ) m1 m2' ↔
    ∃ m2, p.Matches e m1 m2 ∧ ∀ x, m2' x = (m2 x).lift' ρ := by
  constructor
  · intro h; generalize eq : e.lift' ρ = e' at h
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

theorem Pattern.matches_liftN {p : Pattern} {e : VExpr} {m1 m2'} :
    p.Matches (e.liftN n k) m1 m2' ↔ ∃ m2, p.Matches e m1 m2 ∧ ∀ x, m2' x = (m2 x).liftN n k := by
  simp only [← lift'_consN_skipN]; exact p.matches_lift'

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
    induction hp generalizing q m3 <;> cases hq <;> simp [inter]
    · case const.const => exact ⟨_, _, .const⟩
    · case var.var ih _ _ ih' =>
      have ⟨rf, mf1, mf2, hf1, hf2⟩ := ih _ _ ih'
      exact ⟨_, ⟨_, hf1, rfl⟩, _, _, .var hf2⟩
    · case var.app ihf _ _ _ _ _ ha2 ihf' =>
      have ⟨rf, mf1, mf2, hf1, hf2⟩ := ihf _ _ ihf'
      exact ⟨_, ⟨_, hf1, rfl⟩, _, _, .app hf2 ha2⟩
    · case app.var ha2 ihf _ _ _ ihf' =>
      have ⟨rf, mf1, mf2, hf1, hf2⟩ := ihf _ _ ihf'
      exact ⟨_, ⟨_, hf1, rfl⟩, _, _, .app hf2 ha2⟩
    · case app.app ihf iha _ _ _ _ _ iha' ihf' =>
      have ⟨rf, mf1, mf2, hf1, hf2⟩ := ihf _ _ ihf'
      have ⟨ra, ma1, ma2, ha1, ha2⟩ := iha _ _ iha'
      exact ⟨_, ⟨_, hf1, _, ha1, rfl⟩, _, _, .app hf2 ha2⟩
  · rintro ⟨r, m1, m2, h1, h2⟩
    induction p generalizing q e r m1 <;> cases q <;> simp [inter] at h1 <;> [
        obtain ⟨rfl, rfl⟩ := h1; obtain ⟨_, wf, _, wa, rfl⟩ := h1;
        obtain ⟨_, wf, rfl⟩ := h1; obtain ⟨_, wf, rfl⟩ := h1; obtain ⟨_, wf, rfl⟩ := h1
      ] <;> cases h2
    · exact ⟨⟨_, _, .const⟩, ⟨_, _, .const⟩⟩
    · next ihf iha _ _ _ _ _ _ _ _ _ ha hf =>
      have ⟨⟨mf1, mf2, hf⟩, ⟨mf1', mf2', hf'⟩⟩ := ihf _ _ _ wf hf
      have ⟨⟨ma1, ma2, ha⟩, ⟨ma1', ma2', ha'⟩⟩ := iha _ _ _ wa ha
      exact ⟨⟨_, _, .app hf ha⟩, ⟨_, _, .app hf' ha'⟩⟩
    · next ihf _ _ _ _ _ _ _ _ ha hf =>
      have ⟨⟨mf1, mf2, hf⟩, ⟨mf1', mf2', hf'⟩⟩ := ihf _ _ _ wf hf
      exact ⟨⟨_, _, .app hf ha⟩, ⟨_, _, .var hf'⟩⟩
    · next ihf _ _ _ _ _ _ _ _ ha' hf =>
      have ⟨⟨mf1, mf2, hf⟩, ⟨mf1', mf2', hf'⟩⟩ := ihf _ _ _ wf hf
      exact ⟨⟨_, _, .var hf⟩, ⟨_, _, .app hf' ha'⟩⟩
    · next ihf _ _ _ _ _ hf =>
      have ⟨⟨mf1, mf2, hf⟩, ⟨mf1', mf2', hf'⟩⟩ := ihf _ _ _ wf hf
      exact ⟨⟨_, _, .var hf⟩, ⟨_, _, .var hf'⟩⟩

theorem Pattern.matches_determ
    (h1 : Matches p e m1 m2) (h2 : Matches p e m1' m2') : m1 = m1' ∧ m2 = m2' := by
  induction h1 generalizing m1' with
  | const => let .const := h2; simp
  | app l1 l2 ih1 ih2 => let .app r1 r2 := h2; simp [ih1 r1, ih2 r2]; rfl
  | var l1 ih1 => let .var r1 := h2; simp [ih1 r1]

def Pattern.Check.OK (defeq : VExpr → VExpr → Prop) {p : Pattern}
    (m1 : List VLevel) (m2 : p.Path → VExpr) : p.Check → Prop
  | .true => True
  | .defeq a b rest => defeq (RHS.apply m1 m2 a) (RHS.apply m1 m2 b) ∧ rest.OK defeq m1 m2

theorem Pattern.Check.OK.map
    {df df' : VExpr → VExpr → Prop} {p : Pattern} {ck : p.Check} {m1 m2 m1' m2'}
    (h : ∀ a b : p.RHS,
      df (a.apply m1 m2) (b.apply m1 m2) → df' (a.apply m1' m2') (b.apply m1' m2'))
    (H : ck.OK df m1 m2) : ck.OK df' m1' m2' := by
  induction ck <;> simp [OK, *] at H ⊢; cases H; constructor <;> solve_by_elim

/-- `ck.Realizes m1 m2 chk` says the typed-triple list `chk : List (lhs, rhs, ty)`
enumerates exactly the `defeq` entries of `ck`, each triple's `lhs`/`rhs` being the
corresponding `RHS.apply`ied sides. Being a pure predicate (no defeq relation), it
can sit positively in the `IsDefEq` inductive; bridged to `Check.OK` by
`Realizes.toOK` / `OK.exists_realizer`. -/
def Pattern.Check.Realizes {p : Pattern} (m1 : List VLevel) (m2 : p.Path → VExpr) :
    p.Check → List (VExpr × VExpr × VExpr) → Prop
  | .true, [] => True
  | .true, _ :: _ => False
  | .defeq a b rest, t :: ts =>
    t.1 = RHS.apply m1 m2 a ∧ t.2.1 = RHS.apply m1 m2 b ∧ rest.Realizes m1 m2 ts
  | .defeq _ _ _, [] => False

/-- If `chk` realizes `ck` and every triple in `chk` is related by `rel` at its
type, then `ck.OK (untyped rel) holds`. Used to feed the `pat` rule's premises
into the abstract `Check.OK`-based development. -/
theorem Pattern.Check.Realizes.toOK {defeq : VExpr → VExpr → Prop} {p : Pattern}
    {ck : p.Check} {m1 m2 chk} (hr : ck.Realizes m1 m2 chk)
    (h : ∀ t ∈ chk, defeq t.1 t.2.1) : ck.OK defeq m1 m2 := by
  induction ck generalizing chk with
  | true => trivial
  | defeq a b rest ih =>
    match chk, hr with
    | t :: ts, ⟨e1, e2, hr⟩ =>
      exact ⟨e1 ▸ e2 ▸ h t (.head _), ih hr fun t ht => h t (.tail _ ht)⟩

/-- Conversely, from `ck.OK (fun a b => ∃ t, rel a b t)` extract a realizer
`chk` (choosing each type from the existential) together with the per-triple
relation. Used to *construct* a `pat` derivation from an abstract
`Check.OK (IsDefEqU …)` hypothesis. -/
theorem Pattern.Check.OK.exists_realizer {rel : VExpr → VExpr → VExpr → Prop} {p : Pattern}
    {ck : p.Check} {m1 m2} (H : ck.OK (fun a b => ∃ t, rel a b t) m1 m2) :
    ∃ chk, ck.Realizes m1 m2 chk ∧ ∀ t ∈ chk, rel t.1 t.2.1 t.2.2 := by
  induction ck with
  | true => exact ⟨[], trivial, nofun⟩
  | defeq a b rest ih =>
    obtain ⟨⟨t, h1⟩, h2⟩ := H
    obtain ⟨chk, hr, hall⟩ := ih h2
    refine ⟨(_, _, t) :: chk, ⟨rfl, rfl, hr⟩, ?_⟩
    rintro t' ht'
    rcases List.mem_cons.1 ht' with rfl | ht'
    · exact h1
    · exact hall _ ht'

/-! ### Transport helpers for the `pat` reduction rule

Commute `RHS.apply` / `Matches` / `Realizes` with `ClosedN`, `LevelWF`, lifting,
instantiation and level-instantiation, making the `pat` cases of the `IsDefEq`
recursions mechanical. -/

/-- If every hole `m2 x` is `ClosedN k`, then the reduct `r.apply m1 m2` is
`ClosedN k`. -/
theorem Pattern.RHS.apply_closedN {p : Pattern} {m1 : List VLevel} {m2 : p.Path → VExpr} {k}
    (hm : ∀ x, (m2 x).ClosedN k) : ∀ r : p.RHS, (r.apply m1 m2).ClosedN k
  | .fixed _ hc => (VExpr.ClosedN.instL (ls := m1) hc).mono (Nat.zero_le _)
  | .var path => hm path
  | .app f a => ⟨apply_closedN hm f, apply_closedN hm a⟩

/-- The holes produced by matching a `ClosedN k`-bounded expression are all
`ClosedN k`. -/
theorem Pattern.Matches.closedN {p : Pattern} {e m1 m2 k}
    (H : p.Matches e m1 m2) (he : e.ClosedN k) : ∀ x, (m2 x).ClosedN k := by
  induction H with
  | const => exact nofun
  | var _ ih => rintro (_|x); exacts [he.2, ih he.1 x]
  | app _ _ ih1 ih2 => rintro (x|x); exacts [ih1 he.1 x, ih2 he.2 x]

/-- If the match levels `m1` are all `WF U` and every hole is `LevelWF U`, then
the reduct `r.apply m1 m2` is `LevelWF U`. -/
theorem Pattern.RHS.apply_levelWF {p : Pattern} {m1 : List VLevel} {m2 : p.Path → VExpr} {U}
    (hm1 : ∀ l ∈ m1, l.WF U) (hm2 : ∀ x, (m2 x).LevelWF U) :
    ∀ r : p.RHS, (r.apply m1 m2).LevelWF U
  | .fixed _ _ => VExpr.LevelWF.instL hm1
  | .var path => hm2 path
  | .app f a => ⟨apply_levelWF hm1 hm2 f, apply_levelWF hm1 hm2 a⟩

/-- Matching a `LevelWF U` expression yields `WF U` levels and `LevelWF U`
holes. -/
theorem Pattern.Matches.levelWF {p : Pattern} {e m1 m2 U}
    (H : p.Matches e m1 m2) (he : e.LevelWF U) :
    (∀ l ∈ m1, l.WF U) ∧ (∀ x, (m2 x).LevelWF U) := by
  induction H with
  | const => exact ⟨he, nofun⟩
  | var _ ih =>
    obtain ⟨h1, h2⟩ := ih he.1
    exact ⟨h1, by rintro (_|x); exacts [he.2, h2 x]⟩
  | app _ _ ih1 ih2 =>
    obtain ⟨h1, h2⟩ := ih1 he.1; obtain ⟨_, h3⟩ := ih2 he.2
    exact ⟨h1, by rintro (x|x); exacts [h2 x, h3 x]⟩

/-- `RHS.apply` commutes with level instantiation. -/
theorem Pattern.RHS.instL_apply {p : Pattern} {m1 : List VLevel} {m2 : p.Path → VExpr} {ls}
    (r : p.RHS) :
    (r.apply m1 m2).instL ls = r.apply (m1.map (VLevel.inst ls)) (fun x => (m2 x).instL ls) := by
  induction r with
  | fixed c hc => simp [apply, VExpr.instL_instL]
  | var path => simp [apply]
  | app f a ihf iha => simp [apply, VExpr.instL, ihf, iha]

/-- `Matches` transports under level instantiation. -/
theorem Pattern.matches_instL {p : Pattern} {e m1 m2 ls}
    (H : p.Matches e m1 m2) :
    p.Matches (e.instL ls) (m1.map (VLevel.inst ls)) fun x => (m2 x).instL ls := by
  induction H with
  | const => erw [show (fun _ : Empty => _) = _ by ext ⟨⟩]; exact .const
  | var _ ih =>
    rw [(_ : (fun _ => _) = _)]; exact ih.var
    ext (_|_) <;> rfl
  | app _ _ ih1 ih2 =>
    rw [(_ : (fun _ => _) = _)]; exact ih1.app ih2
    ext (_|_) <;> rfl

/-- `Realizes` transports under lifting: lifting all three components of every
triple keeps the realizer valid for the lifted holes. -/
theorem Pattern.Check.Realizes.map_liftN {p : Pattern} {m1 m2} {ck : p.Check} {chk} {n k}
    (hr : ck.Realizes m1 m2 chk) :
    ck.Realizes m1 (fun x => (m2 x).liftN n k)
      (chk.map fun t => (t.1.liftN n k, t.2.1.liftN n k, t.2.2.liftN n k)) := by
  induction ck generalizing chk with
  | true => cases chk <;> simp_all [Realizes]
  | defeq a b rest ih =>
    match chk, hr with
    | t :: ts, ⟨h1, h2, hr⟩ =>
      exact ⟨by simp [h1, RHS.liftN_apply], by simp [h2, RHS.liftN_apply], ih hr⟩

/-- `Realizes` transports under instantiation. -/
theorem Pattern.Check.Realizes.map_instN {p : Pattern} {m1 m2} {ck : p.Check} {chk} {e₀ k}
    (hr : ck.Realizes m1 m2 chk) :
    ck.Realizes m1 (fun x => (m2 x).inst e₀ k)
      (chk.map fun t => (t.1.inst e₀ k, t.2.1.inst e₀ k, t.2.2.inst e₀ k)) := by
  induction ck generalizing chk with
  | true => cases chk <;> simp_all [Realizes]
  | defeq a b rest ih =>
    match chk, hr with
    | t :: ts, ⟨h1, h2, hr⟩ =>
      exact ⟨by simp [h1, RHS.instN_apply], by simp [h2, RHS.instN_apply], ih hr⟩

/-- `Realizes` transports under level instantiation. -/
theorem Pattern.Check.Realizes.map_instL {p : Pattern} {m1 m2} {ck : p.Check} {chk} {ls}
    (hr : ck.Realizes m1 m2 chk) :
    ck.Realizes (m1.map (VLevel.inst ls)) (fun x => (m2 x).instL ls)
      (chk.map fun t => (t.1.instL ls, t.2.1.instL ls, t.2.2.instL ls)) := by
  induction ck generalizing chk with
  | true => cases chk <;> simp_all [Realizes]
  | defeq a b rest ih =>
    match chk, hr with
    | t :: ts, ⟨h1, h2, hr⟩ =>
      exact ⟨by simp [h1, RHS.instL_apply], by simp [h2, RHS.instL_apply], ih hr⟩

/-- `RHS.apply` commutes with substitution: the `fixed` parts are closed, so a
substitution only touches the holes. -/
theorem Pattern.RHS.subst_apply {p : Pattern} {m1 m2} {σ : Subst} (r : p.RHS) :
    (r.apply m1 m2).subst σ = r.apply m1 fun x => (m2 x).subst σ := by
  induction r <;> simp [*, apply]
  rw [(ClosedN.instL ‹_›).subst_eq .zero]

/-- A match survives an arbitrary substitution: patterns are `const`/`app` trees,
which `subst` maps homomorphically. -/
theorem Pattern.matches_subst {p : Pattern} {e : VExpr} {m1 m2} {σ : Subst}
    (H : p.Matches e m1 m2) :
    p.Matches (e.subst σ) m1 fun x => (m2 x).subst σ := by
  induction H with
  | const => erw [show (fun _ : Empty => _) = _ by ext ⟨⟩]; exact .const
  | var _ ih =>
    rw [(_ : (fun _ => _) = _)]; exact ih.var
    ext (_|_) <;> rfl
  | app _ _ ih1 ih2 =>
    rw [(_ : (fun _ => _) = _)]; exact ih1.app ih2
    ext (_|_) <;> rfl

/-- `Realizes` transports under substitution. -/
theorem Pattern.Check.Realizes.map_subst {p : Pattern} {m1 m2} {ck : p.Check} {chk}
    {σ : Subst} (hr : ck.Realizes m1 m2 chk) :
    ck.Realizes m1 (fun x => (m2 x).subst σ)
      (chk.map fun t => (t.1.subst σ, t.2.1.subst σ, t.2.2.subst σ)) := by
  induction ck generalizing chk with
  | true => cases chk <;> simp_all [Realizes]
  | defeq a b rest ih =>
    match chk, hr with
    | t :: ts, ⟨h1, h2, hr⟩ =>
      exact ⟨by simp [h1, RHS.subst_apply], by simp [h2, RHS.subst_apply], ih hr⟩

inductive SimplePattern where
  | iota (recursor : Name) (major : Nat) (constr : Name) (args : Nat)
  | defn (head : Name)

def SimplePattern.toPattern : SimplePattern → Pattern
  | .defn c => .const c
  | .iota r m c n => .app (.varN (.const r) m) (.varN (.const c) n)

/-- The path selecting the `i`-th argument (0-indexed) of a `q.varN k` spine
pattern: argument `i` sits at `someᵏ⁻¹⁻ⁱ none`. -/
def Pattern.varN_pathOf {q : Pattern} : (k i : Nat) → i < k → (q.varN k).Path
  | k+1, i, _ =>
    if _hik : i = k then (none : Option (q.varN k).Path)
    else some (Pattern.varN_pathOf (q := q) k i (by omega))

/-! ### The ι reduct and what it retains

`SimplePattern.iotaRHS` builds the reduct of an ι rule as a pattern `RHS`: the closed
rule template applied to the recursor's parameters, motives and minors and to the
constructor's fields. `Pattern.RHS.spine`/`iotaCounts` read such a reduct back — the
template and the numbers of recursor-side and constructor-side holes — which is all of
the recursor's telescope the reduct retains: it depends on the motive/minor split only
through `nm + nmin`, exactly like `inductiveReduceRec` and the thesis's
`rec_P C e p[b] (c b) ≡ e_c b v`. -/

/-- Decompose an `RHS` of the form `fixed c` applied (left-nested) to `var` holes into
the head `c` and its holes, first hole first; `none` for any other shape. -/
def Pattern.RHS.spine {p : Pattern} : p.RHS → Option (VExpr × List p.Path)
  | .fixed c _ => some (c, [])
  | .app f (.var x) => do let (c, xs) ← f.spine; some (c, xs ++ [x])
  | _ => none

theorem Pattern.RHS.spine_foldl_var {p : Pattern} {c : VExpr} :
    ∀ (l : List p.Path) (f : p.RHS) (xs : List p.Path), f.spine = some (c, xs) →
      ((l.map Pattern.RHS.var).foldl Pattern.RHS.app f).spine = some (c, xs ++ l)
  | [], f, xs, h => by simpa using h
  | x :: l, f, xs, h => by
    have := spine_foldl_var (c := c) l (f.app (.var x)) (xs ++ [x]) (by simp [spine, h])
    rw [List.map_cons, List.foldl_cons, this]; simp

/-- The data an ι reduct retains: its template and the numbers of holes into the
recursor spine (`Sum.inl`) and into the constructor spine (`Sum.inr`). -/
def Pattern.RHS.iotaCounts {r M c N} (R : (SimplePattern.iota r M c N).toPattern.RHS) :
    Option (VExpr × Nat × Nat) := do
  let (hd, xs) ← R.spine
  some (hd, xs.countP Sum.isLeft, xs.countP Sum.isRight)

/-- The holes of an ι reduct: the recursor spine's first `k` arguments (of `k + nind`:
the parameters, motives and minors, `inductiveReduceRec`'s `[0, getFirstIndexIdx)`
slice) followed by the constructor spine's last `nf` arguments (of `cnp + nf`: the
fields). -/
def SimplePattern.iotaPaths (r c : Name) (k nind cnp nf : Nat) :
    List (SimplePattern.iota r (k+nind) c (cnp+nf)).toPattern.Path :=
  (List.range k).pmap
    (fun i (hi : i < k+nind) =>
      (Sum.inl (Pattern.varN_pathOf (q := .const r) (k+nind) i hi) :
        (SimplePattern.iota r (k+nind) c (cnp+nf)).toPattern.Path))
    (fun _ hi => by have := List.mem_range.1 hi; omega) ++
  (List.range nf).pmap
    (fun j (hj : cnp+j < cnp+nf) =>
      (Sum.inr (Pattern.varN_pathOf (q := .const c) (cnp+nf) (cnp+j) hj) :
        (SimplePattern.iota r (k+nind) c (cnp+nf)).toPattern.Path))
    (fun _ hj => by have := List.mem_range.1 hj; omega)

theorem SimplePattern.iotaPaths_countP_isLeft (r c : Name) (k nind cnp nf : Nat) :
    (iotaPaths r c k nind cnp nf).countP Sum.isLeft = k := by
  unfold iotaPaths
  rw [List.countP_append, List.countP_eq_length.2, List.countP_eq_zero.2, List.length_pmap,
    List.length_range, Nat.add_zero]
  · intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_pmap.1 ha; exact Bool.false_ne_true
  · intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_pmap.1 ha; rfl

theorem SimplePattern.iotaPaths_countP_isRight (r c : Name) (k nind cnp nf : Nat) :
    (iotaPaths r c k nind cnp nf).countP Sum.isRight = nf := by
  unfold iotaPaths
  rw [List.countP_append, List.countP_eq_zero.2, List.countP_eq_length.2, List.length_pmap,
    List.length_range, Nat.zero_add]
  · intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_pmap.1 ha; rfl
  · intro a ha; obtain ⟨_, _, rfl⟩ := List.mem_pmap.1 ha; exact Bool.false_ne_true

/-- The ι-reduction reduct at an undifferentiated parameters/motives/minors prefix `k`:
the closed template `rhs` applied to the recursor spine's first `k` arguments and to
the constructor spine's last `nf` arguments. This is the shape reduction sees; the
split of `k` into parameters, motives and minors is typing information, recorded in
the recursor's type (`VExpr.RecShape`). -/
def SimplePattern.iotaRHS' (r c : Name) (k nind cnp nf : Nat) (rhs : VExpr) (hrhs : rhs.Closed) :
    (SimplePattern.iota r (k+nind) c (cnp+nf)).toPattern.RHS :=
  ((iotaPaths r c k nind cnp nf).map Pattern.RHS.var).foldl Pattern.RHS.app (.fixed rhs hrhs)

/-- The ι-reduction reduct as a pattern `RHS`, for a recursor with `np` parameters,
`nm` motives, `nmin` minors, `nind` indices, firing on a constructor with `cnp`
parameters and `nf` fields. Applies the closed rule template `rhs` to the recursor's
parameters/motives/minors (spine positions `[0, np+nm+nmin)`) and the constructor's
fields (spine positions `[cnp, cnp+nf)`), matching the argument slicing of
`inductiveReduceRec` (which takes the *last* `nfields` constructor arguments). `cnp`
is the constructor's own `numParams`: it differs from `np` for the auxiliary
recursors of nested inductives. -/
def SimplePattern.iotaRHS (r c : Name) (np nm nmin nind cnp nf : Nat)
    (rhs : VExpr) (hrhs : rhs.Closed) :
    (SimplePattern.iota r (np+nm+nmin+nind) c (cnp+nf)).toPattern.RHS :=
  SimplePattern.iotaRHS' r c (np+nm+nmin) nind cnp nf rhs hrhs

/-- The instance of a template applied to holes: the instance of the template applied to
the holes' values. -/
theorem Pattern.RHS.apply_foldl_var {p : Pattern} {m1 : List VLevel} {m2 : p.Path → VExpr} :
    ∀ (l : List p.Path) (f : p.RHS),
      ((l.map Pattern.RHS.var).foldl Pattern.RHS.app f).apply m1 m2 =
        (f.apply m1 m2).mkApps (l.map m2)
  | [], _ => rfl
  | x :: l, f => by
    rw [List.map_cons, List.foldl_cons, apply_foldl_var l, List.map_cons, VExpr.mkApps_cons]; rfl

/-- A constant applied to `n` arguments matches the spine pattern `(.const c).varN n`, the
hole of argument `i` (`Pattern.varN_pathOf`) holding that argument. -/
theorem Pattern.matches_varN_const {c : Name} {ls : List VLevel} :
    ∀ (n : Nat) (args : List VExpr) (h : args.length = n),
      ∃ g, ((Pattern.const c).varN n).Matches ((VExpr.const c ls).mkApps args) ls g ∧
        ∀ i (hi : i < n), g (Pattern.varN_pathOf n i hi) = args[i]'(by omega)
  | 0, [], _ => ⟨nofun, .const, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | 0, _ :: _, h => nomatch h
  | n+1, args, h => by
    obtain ⟨as, a, rfl⟩ : ∃ as a, args = as ++ [a] := by
      rcases List.eq_nil_or_concat args with rfl | ⟨as, a, rfl⟩
      · cases h
      · exact ⟨as, a, List.concat_eq_append ..⟩
    have hlen : as.length = n := by simpa using h
    obtain ⟨g, hm, hg⟩ := matches_varN_const n as hlen
    refine ⟨fun x => x.elim a g, ?_, fun i hi => ?_⟩
    · rw [VExpr.mkApps_append, VExpr.mkApps_cons, VExpr.mkApps_nil]; exact .var hm
    · have key : (Pattern.varN_pathOf (q := Pattern.const c) (n+1) i hi :
          Option ((Pattern.const c).varN n).Path) =
          if hik : i = n then none else some (Pattern.varN_pathOf n i (by omega)) := rfl
      show Option.elim (Pattern.varN_pathOf (q := Pattern.const c) (n+1) i hi :
          Option ((Pattern.const c).varN n).Path) a g = _
      rw [key]
      by_cases hik : i = n
      · subst hik; rw [dif_pos rfl]; simp [hlen]
      · rw [dif_neg hik, Option.elim, hg i (by omega), List.getElem_append_left (by omega)]

/-- The ι reduct on a match: the template, level-instantiated, applied to the recursor
spine's first `k` arguments and the constructor spine's last `nf` arguments. -/
theorem SimplePattern.iotaRHS'_apply (r c : Name) (k nind cnp nf : Nat) (rhs : VExpr)
    (hc : rhs.Closed) (m1 : List VLevel)
    (m2 : (SimplePattern.iota r (k+nind) c (cnp+nf)).toPattern.Path → VExpr)
    {recArgs ctorArgs : List VExpr} (h1 : recArgs.length = k + nind)
    (h2 : ctorArgs.length = cnp + nf)
    (hg1 : ∀ i (hi : i < k + nind),
      m2 (Sum.inl (Pattern.varN_pathOf (k+nind) i hi)) = recArgs[i]'(h1 ▸ hi))
    (hg2 : ∀ i (hi : i < cnp + nf),
      m2 (Sum.inr (Pattern.varN_pathOf (cnp+nf) i hi)) = ctorArgs[i]'(h2 ▸ hi)) :
    (iotaRHS' r c k nind cnp nf rhs hc).apply m1 m2 =
      (rhs.instL m1).mkApps (recArgs.take k ++ ctorArgs.drop cnp) := by
  unfold iotaRHS'
  rw [Pattern.RHS.apply_foldl_var]
  show (rhs.instL m1).mkApps _ = _
  congr 1
  have e1 : (iotaPaths r c k nind cnp nf).map m2 =
      (List.range k).pmap
        (fun i (hi : i < k+nind) => m2 (Sum.inl (Pattern.varN_pathOf (k+nind) i hi)))
        (fun _ hi => by have := List.mem_range.1 hi; omega) ++
      (List.range nf).pmap
        (fun j (hj : cnp+j < cnp+nf) => m2 (Sum.inr (Pattern.varN_pathOf (cnp+nf) (cnp+j) hj)))
        (fun _ hj => by have := List.mem_range.1 hj; omega) := by
    unfold iotaPaths
    exact (List.map_append ..).trans
      (congr (congrArg (· ++ ·) (List.map_pmap ..)) (List.map_pmap ..))
  rw [e1]
  congr 1
  · apply List.ext_getElem
    · simp [List.length_take]; omega
    · intro t ht1 ht2
      simp only [List.getElem_pmap, List.getElem_range, List.getElem_take]
      exact hg1 t _
  · apply List.ext_getElem
    · simp [List.length_drop]; omega
    · intro t ht1 ht2
      simp only [List.getElem_pmap, List.getElem_range, List.getElem_drop]
      exact hg2 (cnp + t) _

theorem SimplePattern.iotaRHS'_spine (r c : Name) (k nind cnp nf : Nat) (rhs : VExpr)
    (hrhs : rhs.Closed) :
    (iotaRHS' r c k nind cnp nf rhs hrhs).spine = some (rhs, iotaPaths r c k nind cnp nf) :=
  Pattern.RHS.spine_foldl_var _ _ [] rfl

theorem SimplePattern.iotaRHS'_iotaCounts (r c : Name) (k nind cnp nf : Nat) (rhs : VExpr)
    (hrhs : rhs.Closed) :
    (iotaRHS' r c k nind cnp nf rhs hrhs).iotaCounts = some (rhs, k, nf) := by
  simp [Pattern.RHS.iotaCounts, iotaRHS'_spine, iotaPaths_countP_isLeft, iotaPaths_countP_isRight]

/-- An ι reduct retains its template, the size `np + nm + nmin` of its recursor prefix
and the field count `nf` — and nothing else of the telescope split. -/
theorem SimplePattern.iotaRHS_iotaCounts (r c : Name) (np nm nmin nind cnp nf : Nat)
    (rhs : VExpr) (hrhs : rhs.Closed) :
    (iotaRHS r c np nm nmin nind cnp nf rhs hrhs).iotaCounts = some (rhs, np+nm+nmin, nf) :=
  iotaRHS'_iotaCounts ..

/-! ### Template-headed reducts

The reduct of an ι rule is a closed λ-template applied to holes (`SimplePattern.iotaRHS`).
`Pattern.RHS.TemplateHeaded` pins its head shape — a fixed closed `lam` applied to any
arguments, the arguments themselves unconstrained — the computational half of a well-formed
reduction rule (`VEnv.PatWF`): under every instantiation such a reduct is an application or
an abstraction, its head fixed by the rule (`apply_lam_or_app`) — in particular never a sort
or a Π-type (`apply_ne_sort`, `apply_ne_forallE`). -/

/-- An `RHS` that is a λ-abstraction template applied to (any number of) arguments. -/
inductive Pattern.RHS.TemplateHeaded {p : Pattern} : p.RHS → Prop
  | lam {A b h} : TemplateHeaded (.fixed (.lam A b) h)
  | app {f a} : TemplateHeaded f → TemplateHeaded (.app f a)

theorem Pattern.RHS.TemplateHeaded.foldl_app {p : Pattern} {f : p.RHS}
    (h : f.TemplateHeaded) : ∀ l : List p.RHS, (l.foldl Pattern.RHS.app f).TemplateHeaded
  | [] => h
  | _ :: l => TemplateHeaded.foldl_app h.app l

/-- Every instance of a template-headed reduct is an application or an abstraction. -/
theorem Pattern.RHS.TemplateHeaded.apply_lam_or_app {p : Pattern} {r : p.RHS}
    (h : r.TemplateHeaded) (m1 : List VLevel) (m2 : p.Path → VExpr) :
    (∃ A b, r.apply m1 m2 = .lam A b) ∨ ∃ f a, r.apply m1 m2 = .app f a := by
  induction h with
  | lam => exact .inl ⟨_, _, rfl⟩
  | app _ _ => exact .inr ⟨_, _, rfl⟩

theorem Pattern.RHS.TemplateHeaded.apply_ne_forallE {p : Pattern} {r : p.RHS}
    (h : r.TemplateHeaded) {m1 m2 A B} : r.apply m1 m2 ≠ .forallE A B := by
  rcases h.apply_lam_or_app m1 m2 with ⟨_, _, e⟩ | ⟨_, _, e⟩ <;> rw [e] <;> nofun

theorem Pattern.RHS.TemplateHeaded.apply_ne_sort {p : Pattern} {r : p.RHS}
    (h : r.TemplateHeaded) {m1 m2 u} : r.apply m1 m2 ≠ .sort u := by
  rcases h.apply_lam_or_app m1 m2 with ⟨_, _, e⟩ | ⟨_, _, e⟩ <;> rw [e] <;> nofun

/-- An ι reduct over a λ-template is template-headed. -/
theorem SimplePattern.iotaRHS'_templateHeaded {r c : Name} {k nind cnp nf : Nat} {A b : VExpr}
    (h : (VExpr.lam A b).Closed) :
    (iotaRHS' r c k nind cnp nf (.lam A b) h).TemplateHeaded :=
  Pattern.RHS.TemplateHeaded.foldl_app .lam _

theorem SimplePattern.iotaRHS_templateHeaded {r c : Name} {np nm nmin nind cnp nf : Nat}
    {rhs : VExpr} (hl : ∃ A b, rhs = .lam A b) (h : rhs.Closed) :
    (iotaRHS r c np nm nmin nind cnp nf rhs h).TemplateHeaded := by
  obtain ⟨A, b, rfl⟩ := hl
  exact iotaRHS'_templateHeaded h
