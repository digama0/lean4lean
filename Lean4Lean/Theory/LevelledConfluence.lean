import Lean4Lean.Std.Basic

/-! # Confluence from levelled local diagrams

An abstract confluence criterion in the style of decreasing diagrams, for a
family of relations `R n` indexed by levels. Write `Lo n` for the union of the
relations below level `n`. If the relations below level `n` are confluent and
every local peak involving a level-`n` step closes as follows, then the
relations up to level `n` are confluent:

* two level-`n` steps (`Peak₁`): each side closes by lower steps, at most one
  level-`n` step, and lower steps;
* a level-`n` step against a lower step (`Peak₂`): the level-`n` side closes by
  lower steps only, and the lower side by at most one level-`n` step followed by
  lower steps.

The second shape is decreasing diagrams without a lower prefix on the lower
side. With it, a counting argument suffices: no multiset ordering is needed.
Joins add, on each side, at most as many level-`n` steps as the other side had.
-/

namespace Lean4Lean.Levelled

variable {α : Type u} (R : Nat → α → α → Prop)

/-- Steps below level `n`. -/
def Lo (n : Nat) (a b : α) : Prop := ∃ k, k < n ∧ R k a b

/-- Lower-steps reductions. -/
abbrev LoStar (n : Nat) := ReflTransGen (Lo R n)

/-- At most one level-`n` step. -/
def Opt (n : Nat) (a b : α) : Prop := a = b ∨ R n a b

/-- Lower steps, at most one level-`n` step, lower steps. -/
def LoOptLo (n : Nat) (a d : α) : Prop :=
  ∃ b c, LoStar R n a b ∧ Opt R n b c ∧ LoStar R n c d

/-- At most one level-`n` step, then lower steps. -/
def OptLo (n : Nat) (a d : α) : Prop := ∃ b, Opt R n a b ∧ LoStar R n b d

def Joinable (r : α → α → Prop) : Prop :=
  ∀ a b c, ReflTransGen r a b → ReflTransGen r a c → ∃ d, ReflTransGen r b d ∧ ReflTransGen r c d

/-- Reductions up to level `n` with exactly `k` level-`n` steps. -/
inductive NPath (n : Nat) : α → α → Nat → Prop where
  | rfl : NPath n a a 0
  | lo : Lo R n a b → NPath n b c k → NPath n a c k
  | hi : R n a b → NPath n b c k → NPath n a c (k + 1)

/-- Paths with at most `k` level-`n` steps. -/
def NLe (n : Nat) (a b : α) (k : Nat) : Prop := ∃ k', k' ≤ k ∧ NPath R n a b k'

variable {R}

theorem NPath.append (H1 : NPath R n a b k₁) (H2 : NPath R n b c k₂) :
    NPath R n a c (k₁ + k₂) := by
  induction H1 with
  | rfl => simpa using H2
  | lo h _ ih => exact .lo h (ih H2)
  | hi h _ ih => simpa [Nat.add_right_comm] using NPath.hi h (ih H2)

theorem NPath.ofLoStar (H : LoStar R n a b) : NPath R n a b 0 := by
  induction H using ReflTransGen.headIndOn with
  | rfl => exact .rfl
  | head h _ ih => exact .lo h ih

theorem NPath.toLoStar (H : NPath R n a b 0) : LoStar R n a b := by
  generalize hk : 0 = k at H
  induction H with
  | rfl => exact .rfl
  | lo h _ ih => exact ReflTransGen.trans (.tail .rfl h) (ih hk)
  | hi => cases hk

theorem NLe.append (H1 : NLe R n a b k₁) (H2 : NLe R n b c k₂) : NLe R n a c (k₁ + k₂) :=
  let ⟨_, h1, p1⟩ := H1; let ⟨_, h2, p2⟩ := H2; ⟨_, Nat.add_le_add h1 h2, p1.append p2⟩

theorem NLe.mono (H : NLe R n a b k) (h : k ≤ k') : NLe R n a b k' :=
  let ⟨_, h1, p⟩ := H; ⟨_, Nat.le_trans h1 h, p⟩

theorem NLe.ofLoStar (H : LoStar R n a b) : NLe R n a b 0 := ⟨0, Nat.le_refl _, .ofLoStar H⟩

theorem NLe.ofOptLo (H : OptLo R n a b) : NLe R n a b 1 := by
  obtain ⟨c, h1, h2⟩ := H
  rcases h1 with rfl | h1
  · exact (NLe.ofLoStar h2).mono (Nat.zero_le _)
  · exact ⟨1, Nat.le_refl _, .hi h1 (.ofLoStar h2)⟩

theorem NLe.ofLoOptLo (H : LoOptLo R n a b) : NLe R n a b 1 := by
  obtain ⟨b₁, c, h1, h2, h3⟩ := H
  simpa using (NLe.ofLoStar h1).append (NLe.ofOptLo ⟨c, h2, h3⟩)

theorem NLe.zero (H : NLe R n a b 0) : LoStar R n a b := by
  obtain ⟨k, hk, p⟩ := H
  cases Nat.le_zero.mp hk
  exact p.toLoStar

/-- Decompose a path with at least one level-`n` step. -/
theorem NPath.split (H : NPath R n a b (k + 1)) :
    ∃ x y, LoStar R n a x ∧ R n x y ∧ NPath R n y b k := by
  generalize hk : k + 1 = k' at H
  induction H generalizing k with
  | rfl => cases hk
  | lo h _ ih =>
    obtain ⟨x, y, h1, h2, h3⟩ := ih hk
    exact ⟨x, y, ReflTransGen.trans (.tail .rfl h) h1, h2, h3⟩
  | hi h p => cases hk; exact ⟨_, _, .rfl, h, p⟩

section Level
variable (n : Nat)
  (conf : Joinable (Lo R n))
  (peak₁ : ∀ a b c, R n a b → R n a c → ∃ d, LoOptLo R n b d ∧ LoOptLo R n c d)
  (peak₂ : ∀ a b c, R n a b → Lo R n a c → ∃ d, LoStar R n b d ∧ OptLo R n c d)
include conf peak₂

/-- A level-`n` step against a lower reduction. -/
theorem strip_lo (h : R n a b) (H : LoStar R n a c) :
    ∃ d, LoStar R n b d ∧ OptLo R n c d := by
  induction H using ReflTransGen.headIndOn generalizing b with
  | rfl => exact ⟨b, .rfl, b, .inr h, .rfl⟩
  | @head a a₁ h₁ hrest ih =>
    obtain ⟨d₁, hb, e, he, hed⟩ := peak₂ _ _ _ h h₁
    rcases he with rfl | he
    · obtain ⟨d, h1, h2⟩ := conf _ _ _ hed hrest
      exact ⟨d, ReflTransGen.trans hb h1, _, .inl rfl, h2⟩
    · obtain ⟨f, hf, g, hg, hgf⟩ := ih he
      obtain ⟨d, h1, h2⟩ := conf _ _ _ hed hf
      exact ⟨d, ReflTransGen.trans hb h1, g, hg, ReflTransGen.trans hgf h2⟩

include peak₁ in
theorem claim : ∀ s k₁ k₂, k₁ + k₂ ≤ s → NPath R n a b k₁ → NPath R n a c k₂ →
    ∃ d, NLe R n b d k₂ ∧ NLe R n c d k₁ := by
  intro s
  induction s using Nat.strongRecOn generalizing a b c with | _ s ih => ?_
  intro k₁ k₂ hs H1 H2
  -- the case without level-`n` steps on one side
  have lowSide : ∀ {a b c k}, k ≤ s → LoStar R n a b → NPath R n a c k →
      (∀ {a b c k'}, k' < k → LoStar R n a b → NPath R n a c k' →
        ∃ d, NLe R n b d k' ∧ NLe R n c d 0) →
      ∃ d, NLe R n b d k ∧ NLe R n c d 0 := by
    intro a b c k _ hb hc ih0
    cases k with
    | zero =>
      obtain ⟨d, h1, h2⟩ := conf _ _ _ hb hc.toLoStar
      exact ⟨d, .ofLoStar h1, .ofLoStar h2⟩
    | succ k =>
      obtain ⟨x, y, hx, hxy, hyc⟩ := hc.split
      obtain ⟨u, hbu, hxu⟩ := conf _ _ _ hb hx
      obtain ⟨v, hyv, hu⟩ := strip_lo n conf peak₂ hxy hxu
      obtain ⟨f, hvf, hcf⟩ := ih0 (Nat.lt_succ_self k) hyv hyc
      refine ⟨f, ?_, hcf⟩
      have := ((NLe.ofLoStar hbu).append (NLe.ofOptLo hu)).append hvf
      exact this.mono (by omega)
  cases k₁ with
  | zero =>
    have hb := H1.toLoStar
    -- induct on k₂ using the outer hypothesis
    have := lowSide (k := k₂) (by omega) hb H2 (fun {a b c k'} hk hb hc => by
      obtain ⟨d, h1, h2⟩ := ih k' (by omega) (a := a) (b := b) (c := c) 0 k' (by omega)
        (.ofLoStar hb) hc
      exact ⟨d, h1, h2⟩)
    exact this
  | succ k₁ =>
    cases k₂ with
    | zero =>
      have hc := H2.toLoStar
      have := lowSide (k := k₁ + 1) (by omega) hc H1 (fun {a b c k'} hk hb hc => by
        obtain ⟨d, h1, h2⟩ := ih k' (by omega) (a := a) (b := b) (c := c) 0 k' (by omega)
          (.ofLoStar hb) hc
        exact ⟨d, h1, h2⟩)
      obtain ⟨d, h1, h2⟩ := this
      exact ⟨d, h2, h1⟩
    | succ k₂ =>
      obtain ⟨x₁, y₁, hx₁, h₁, hy₁⟩ := H1.split
      obtain ⟨x₂, y₂, hx₂, h₂, hy₂⟩ := H2.split
      obtain ⟨u, hx₁u, hx₂u⟩ := conf _ _ _ hx₁ hx₂
      obtain ⟨v₁, hy₁v₁, e₁, he₁, he₁v₁⟩ := strip_lo n conf peak₂ h₁ hx₁u
      obtain ⟨v₂, hy₂v₂, e₂, he₂, he₂v₂⟩ := strip_lo n conf peak₂ h₂ hx₂u
      -- small joins via the induction hypothesis at total count at most one
      have small : ∀ {a b c}, LoStar R n a b → NLe R n a c 1 →
          ∃ d, NLe R n b d 1 ∧ NLe R n c d 0 := by
        intro a b c hb hc
        obtain ⟨k, hk, p⟩ := hc
        obtain ⟨d, h1, h2⟩ := ih k (by omega) (a := a) 0 k (by omega) (.ofLoStar hb) p
        exact ⟨d, h1.mono hk, h2⟩
      -- the two optional level-`n` steps at `u`
      obtain ⟨z, hv₁z, hv₂z⟩ : ∃ z, NLe R n v₁ z 1 ∧ NLe R n v₂ z 1 := by
        rcases he₁ with rfl | he₁
        · obtain ⟨z, h1, h2⟩ := small he₁v₁ (NLe.ofOptLo ⟨e₂, he₂, he₂v₂⟩)
          exact ⟨z, h1, h2.mono (Nat.zero_le _)⟩
        · rcases he₂ with rfl | he₂
          · obtain ⟨z, h1, h2⟩ := small he₂v₂ (NLe.ofOptLo ⟨e₁, .inr he₁, he₁v₁⟩)
            exact ⟨z, h2.mono (Nat.zero_le _), h1⟩
          · obtain ⟨g, hg₁, hg₂⟩ := peak₁ _ _ _ he₁ he₂
            obtain ⟨z₁, h1, h2⟩ := small he₁v₁ (NLe.ofLoOptLo hg₁)
            obtain ⟨z₂, h3, h4⟩ := small he₂v₂ (NLe.ofLoOptLo hg₂)
            obtain ⟨z, h5, h6⟩ := conf _ _ _ h2.zero h4.zero
            exact ⟨z, by simpa using h1.append (NLe.ofLoStar h5),
              by simpa using h3.append (NLe.ofLoStar h6)⟩
      -- continue along `y₁ ⇝ b` and `y₂ ⇝ c`
      have hy₁z : NLe R n y₁ z 1 := by simpa using (NLe.ofLoStar hy₁v₁).append hv₁z
      have hy₂z : NLe R n y₂ z 1 := by simpa using (NLe.ofLoStar hy₂v₂).append hv₂z
      obtain ⟨k₃, hk₃, p₃⟩ := hy₁z
      obtain ⟨k₄, hk₄, p₄⟩ := hy₂z
      obtain ⟨e₁', hb₁, hz₁⟩ := ih (k₁ + k₃) (by omega) k₁ k₃ (Nat.le_refl _) hy₁ p₃
      obtain ⟨e₂', hc₂, hz₂⟩ := ih (k₂ + k₄) (by omega) k₂ k₄ (Nat.le_refl _) hy₂ p₄
      obtain ⟨k₅, hk₅, p₅⟩ := hz₁
      obtain ⟨k₆, hk₆, p₆⟩ := hz₂
      obtain ⟨f, hf₁, hf₂⟩ := ih (k₅ + k₆) (by omega) k₅ k₆ (Nat.le_refl _) p₅ p₆
      refine ⟨f, (hb₁.append hf₁).mono (by omega), (hc₂.append hf₂).mono (by omega)⟩

include peak₁ in
/-- Confluence up to level `n`. -/
theorem joinable_succ : Joinable (Lo R (n + 1)) := by
  have toPath : ∀ {a b}, ReflTransGen (Lo R (n + 1)) a b → ∃ k, NPath R n a b k := by
    intro a b H
    induction H using ReflTransGen.headIndOn with
    | rfl => exact ⟨0, .rfl⟩
    | head h _ ih =>
      obtain ⟨k, p⟩ := ih
      obtain ⟨j, hj, h⟩ := h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact ⟨k, .lo ⟨j, hj, h⟩ p⟩
      · exact ⟨k + 1, .hi h p⟩
  have ofPath : ∀ {a b k}, NPath R n a b k → ReflTransGen (Lo R (n + 1)) a b := by
    intro a b k H
    induction H with
    | rfl => exact .rfl
    | lo h _ ih =>
      obtain ⟨j, hj, h⟩ := h
      exact ReflTransGen.trans (.tail .rfl ⟨j, Nat.lt_succ_of_lt hj, h⟩) ih
    | hi h _ ih => exact ReflTransGen.trans (.tail .rfl ⟨n, Nat.lt_succ_self _, h⟩) ih
  intro a b c hb hc
  obtain ⟨k₁, p₁⟩ := toPath hb
  obtain ⟨k₂, p₂⟩ := toPath hc
  obtain ⟨d, ⟨_, _, q₁⟩, ⟨_, _, q₂⟩⟩ := claim n conf peak₁ peak₂ (k₁ + k₂) k₁ k₂ (Nat.le_refl _) p₁ p₂
  exact ⟨d, ofPath q₁, ofPath q₂⟩

end Level

/-- Confluence of all levels below `N`, from confluence of level zero and the
local diagrams at every positive level. -/
theorem joinable
    (conf₀ : Joinable (R 0))
    (peak₁ : ∀ n, 0 < n → ∀ a b c, R n a b → R n a c → ∃ d, LoOptLo R n b d ∧ LoOptLo R n c d)
    (peak₂ : ∀ n, 0 < n → ∀ a b c, R n a b → Lo R n a c → ∃ d, LoStar R n b d ∧ OptLo R n c d) :
    ∀ N, Joinable (Lo R (N + 1)) := by
  intro N
  induction N with
  | zero =>
    have e : ∀ a b, Lo R 1 a b ↔ R 0 a b := fun a b =>
      ⟨fun ⟨k, hk, h⟩ => by cases Nat.lt_one_iff.mp hk; exact h, fun h => ⟨0, by decide, h⟩⟩
    have conv : ∀ {a b}, ReflTransGen (Lo R 1) a b ↔ ReflTransGen (R 0) a b := by
      intro a b
      constructor <;> intro H <;> induction H with
      | rfl => exact .rfl
      | tail _ h ih => exact .tail ih (by first | exact (e _ _).1 h | exact (e _ _).2 h)
    intro a b c hb hc
    obtain ⟨d, h1, h2⟩ := conf₀ a b c (conv.1 hb) (conv.1 hc)
    exact ⟨d, conv.2 h1, conv.2 h2⟩
  | succ N ih =>
    exact joinable_succ (N + 1) ih (peak₁ _ (Nat.succ_pos _)) (peak₂ _ (Nat.succ_pos _))

end Lean4Lean.Levelled
