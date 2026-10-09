import Lean4Lean.Std.Basic

/-! List lemmas shared by the verification, in `namespace Lean4Lean` like `Std/Basic.lean`. -/

namespace Lean4Lean

theorem List.forall₂_drop {R : α → β → Prop} :
    ∀ {l : List α} {r : List β} (_ : List.Forall₂ R l r) (k : Nat),
      List.Forall₂ R (l.drop k) (r.drop k)
  | _, _, .nil, _ => by simp
  | _, _, .cons h t, 0 => by simpa using List.Forall₂.cons h t
  | _, _, .cons _ t, k + 1 => by
    simp only [List.drop_succ_cons]
    exact forall₂_drop t k

theorem List.nodup_map_inj {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by simp at hx
  | a :: l, hnd, x, y, hx, hy, hxy => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hx with hx' | hx' <;> rcases List.mem_cons.mp hy with hy' | hy'
    · exact hx'.trans hy'.symm
    · subst hx'; exact absurd ⟨y, hy', hxy.symm⟩ hnd.1
    · subst hy'; exact absurd ⟨x, hx', hxy⟩ hnd.1
    · exact nodup_map_inj hnd.2 hx' hy' hxy

theorem List.forall₂_take {R : α → β → Prop} (H : List.Forall₂ R l l') (k : Nat) :
    List.Forall₂ R (l.take k) (l'.take k) := by
  induction H generalizing k with
  | nil => simp
  | cons h _ ih => cases k with
    | zero => exact .nil
    | succ k => exact .cons h (ih k)

theorem _root_.List.Forall₂.append' {R : α → β → Prop} {a b : List α} {c d : List β}
    (h1 : List.Forall₂ R a c) (h2 : List.Forall₂ R b d) : List.Forall₂ R (a ++ b) (c ++ d) := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact .cons h ih

theorem List.forall₂_getElem {R : α → β → Prop} :
    ∀ {a : List α} {b : List β}, List.Forall₂ R a b → ∀ (i : Nat) (h : i < a.length)
      (h' : i < b.length), R a[i] b[i]
  | _, _, .cons h _, 0, _, _ => h
  | _, _, .cons _ H, i + 1, hi, hi' =>
    List.forall₂_getElem H i (by simpa using hi) (by simpa using hi')

theorem List.forall₂_getElem_exists {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ i (h₁ : i < l₁.length),
      ∃ h₂ : i < l₂.length, R l₁[i] l₂[i]
  | _, _, .nil, _, h => nomatch h
  | _, _, .cons h _, 0, _ => ⟨Nat.zero_lt_succ _, h⟩
  | _, _, .cons _ H, i+1, h₁ =>
    let ⟨h₂, h⟩ := forall₂_getElem_exists H i (Nat.lt_of_succ_lt_succ h₁)
    ⟨Nat.succ_lt_succ h₂, h⟩

theorem List.forall₂_of_getElem {R : α → β → Prop} {a : List α} {b : List β}
    (hlen : a.length = b.length) (h : ∀ i (hi : i < a.length) (hi' : i < b.length), R a[i] b[i]) :
    List.Forall₂ R a b := by
  induction a generalizing b with
  | nil => cases b with | nil => exact .nil | cons => simp at hlen
  | cons x xs ih =>
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      exact .cons (h 0 (by simp) (by simp)) (ih (by simpa using hlen) fun i hi hi' =>
        h (i + 1) (by simpa using hi) (by simpa using hi'))

/-- Split a `Forall₂` whose left list ends in a known element. -/
theorem List.forall₂_snoc_left {R : α → β → Prop} :
    ∀ {l₀ : List α} {a : α} {l : List β}, List.Forall₂ R (l₀ ++ [a]) l →
    ∃ l₀' b, l = l₀' ++ [b] ∧ List.Forall₂ R l₀ l₀' ∧ R a b
  | [], _, _, .cons h .nil => ⟨[], _, rfl, .nil, h⟩
  | _ :: _, _, _, .cons h t =>
    let ⟨l₀', b, e, t', h'⟩ := forall₂_snoc_left t
    ⟨_ :: l₀', b, by rw [e]; rfl, .cons h t', h'⟩

/-- Split a `Forall₂` whose right list ends in a known element. -/
theorem List.forall₂_snoc_right {R : α → β → Prop} :
    ∀ {l : List α} {l₀ : List β} {b : β}, List.Forall₂ R l (l₀ ++ [b]) →
    ∃ l₀' a, l = l₀' ++ [a] ∧ List.Forall₂ R l₀' l₀ ∧ R a b
  | _, [], _, .cons h .nil => ⟨[], _, rfl, .nil, h⟩
  | _, _ :: _, _, .cons h t =>
    let ⟨l₀', a, e, t', h'⟩ := forall₂_snoc_right t
    ⟨_ :: l₀', a, by rw [e]; rfl, .cons h t', h'⟩

theorem List.Forall₂.leftSingleton (H : List.Forall₂ R [a] bs) : ∃ b, bs = [b] ∧ R a b := by
  cases H with
  | cons hab Htail =>
    cases Htail
    exact ⟨_, rfl, hab⟩

theorem List.property_of_mem_zipWith (f : α → β → γ) (P : γ → Prop)
    (hproperty : ∀ a b, P (f a b)) :
    ∀ {as : List α} {bs : List β} {value : γ},
      value ∈ List.zipWith f as bs → P value := by
  intro as
  induction as with
  | nil => simp
  | cons a as ih =>
    intro bs value hmem
    cases bs with
    | nil => simp at hmem
    | cons b bs =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact hproperty a b
      · exact ih htail

theorem List.exists_snoc_of_length_succ {α : Type _} {l : List α} {n : Nat}
    (h : l.length = n + 1) : ∃ l' x, l = l' ++ [x] ∧ l'.length = n :=
  ⟨l.dropLast, l.getLast (by intro h'; simp [h'] at h),
    (List.dropLast_concat_getLast _).symm, by simp [h]⟩

theorem List.snoc_induction {α} {P : List α → Prop} (nil : P [])
    (snoc : ∀ l a, P l → P (l ++ [a])) : ∀ l, P l := by
  intro l
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => simpa using nil
  | cons a t ih => simpa using snoc _ a ih

end Lean4Lean
