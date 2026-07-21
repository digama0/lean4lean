import Lean4Lean.Theory.VExpr

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

def Subpattern.varN (h : Subpattern p f) : ∀ {n}, Subpattern p (.varN f n)
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
  | app _ _ ih1 ih2 => rename_i h2 h1; simp [ih1 h1, ih2 h2]

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
  | app l1 l2 ih1 ih2 => let .app r1 r2 := h2; simp [ih1 r1, ih2 r2]
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
enumerates exactly the `defeq` entries of `ck`, with each triple's `lhs`/`rhs`
being the corresponding `RHS.apply`ied sides (the type is carried by `chk`,
since `Check` does not record it). This is a *pure* predicate — it mentions no
definitional-equality relation — so it can sit in the `IsDefEq` inductive
alongside the strictly-positive premise `∀ t ∈ chk, IsDefEq Γ t.1 t.2.1 t.2.2`
without tripping the positivity checker. Bridged to `Check.OK` by
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

These bridge `Pattern.RHS.apply` / `Pattern.Matches` / `Pattern.Check.Realizes`
with `ClosedN`, `LevelWF`, lifting, instantiation and level-instantiation, so
that the `pat` cases of the `IsDefEq` recursions in `Theory.Typing` are
mechanical. -/

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

inductive SimplePattern where
  | iota (recursor : Name) (major : Nat) (constr : Name) (args : Nat)
  | defn (head : Name)

def SimplePattern.toPattern : SimplePattern → Pattern
  | .defn c => .const c
  | .iota r m c n => .app (.varN (.const r) m) (.varN (.const c) n)

/-- The path selecting the `i`-th argument (0-indexed) of a `q.varN k`
sub-pattern. A `q.varN k` pattern matches a spine `q' a₀ … a_{k-1}`; the
outermost `.var` (added last) captures the last argument `a_{k-1}` at path
`none`, so argument `i` sits at `someᵏ⁻¹⁻ⁱ none`. Validated against
`Pattern.Matches`: for a spine, the matcher's hole function composed with
`varN_pathOf k i` returns `aᵢ`. -/
def Pattern.varN_pathOf {q : Pattern} : (k i : Nat) → i < k → (q.varN k).Path
  | k+1, i, _ =>
    if _hik : i = k then (none : Option (q.varN k).Path)
    else some (Pattern.varN_pathOf (q := q) k i (by omega))

/-- The ι-reduction reduct as a pattern `RHS`, for a recursor with `np`
parameters, `nm` motives, `nmin` minors, `nind` indices, firing on a
constructor with `nf` fields. `rhs` is the closed kernel rule template
`fun params motives minors fields => …`. The reduct applies `rhs` to the
recursor's parameters/motives/minors (rec-side holes `[0, np+nm+nmin)`) and
then the constructor's fields (ctor-side holes `[np, np+nf)`) — exactly the
argument slicing performed by `inductiveReduceRec` (drop the recursor's own
indices and major; take the constructor arguments past its parameters). The
recursive calls, if any, are already inside `rhs` and re-fire through this same
rule. -/
def SimplePattern.iotaRHS (r c : Name) (np nm nmin nind nf : Nat)
    (rhs : VExpr) (hrhs : rhs.Closed) :
    (SimplePattern.iota r (np+nm+nmin+nind) c (np+nf)).toPattern.RHS :=
  let recHoles : List (SimplePattern.iota r (np+nm+nmin+nind) c (np+nf)).toPattern.RHS :=
    (List.range (np+nm+nmin)).pmap
      (fun i (hi : i < np+nm+nmin+nind) =>
        Pattern.RHS.var (Sum.inl (Pattern.varN_pathOf (q := .const r) (np+nm+nmin+nind) i hi)))
      (fun _ hi => by have := List.mem_range.1 hi; omega)
  let ctorHoles : List (SimplePattern.iota r (np+nm+nmin+nind) c (np+nf)).toPattern.RHS :=
    (List.range nf).pmap
      (fun j (hj : np+j < np+nf) =>
        Pattern.RHS.var (Sum.inr (Pattern.varN_pathOf (q := .const c) (np+nf) (np+j) hj)))
      (fun _ hj => by have := List.mem_range.1 hj; omega)
  (recHoles ++ ctorHoles).foldl Pattern.RHS.app (Pattern.RHS.fixed rhs hrhs)
