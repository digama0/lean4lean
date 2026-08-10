import Lean.Level
import Lean4Lean.Verify.Name
import Lean4Lean.Std.Ord
import Lean4Lean.Verify.Axioms

/-!
`Lean.Level.normLt` is the order used to sort the arguments of a `max` in
`Lean.Level.normalize`. This file shows it is a strict weak order, which is what the
`Array.qsort` specification requires.

The proof identifies `normLt` with an `Ordering`-valued comparison `normCmp`, which compares
levels by (base, offset) lexicographically, bases being compared structurally. `normCmp` is
then given the `Std` order instances (`ReflCmp`, `TransCmp`, `LawfulEqCmp`), from which the
strict weak order properties `normLt` needs follow. Transitivity uses `Lean4Lean.Rot`, the
lexicographic-product device shared with `Name.cmp` in `Lean4Lean.Verify.Name`.
-/

open Std Lean4Lean

namespace Lean.Level

instance : LawfulBEq LMVarId where
  eq_of_beq := @fun ⟨a⟩ ⟨b⟩ h => by cases LawfulBEq.eq_of_beq (α := Name) h; rfl
  rfl := BEq.rfl (α := Name)

/-- The structural size of a level. -/
private def size : Level → Nat
  | .zero | .param _ | .mvar _ => 1
  | .succ l => size l + 1
  | .max a b | .imax a b => size a + size b + 1

private theorem size_max {a b : Level} : size (.max a b) = size a + size b + 1 := rfl
private theorem size_imax {a b : Level} : size (.imax a b) = size a + size b + 1 := rfl

private theorem one_le_size : ∀ l : Level, 1 ≤ size l
  | .zero | .param _ | .mvar _ => Nat.le_refl _
  | .succ l => Nat.le_succ_of_le (one_le_size l)
  | .max a b | .imax a b => by have := one_le_size a; simp only [size]; omega

private theorem size_getLevelOffset_le : ∀ l : Level, size l.getLevelOffset ≤ size l
  | .succ l => Nat.le_trans (size_getLevelOffset_le l) (Nat.le_succ _)
  | .zero | .param _ | .mvar _ | .max .. | .imax .. => Nat.le_refl _

/-- Structural comparison of level *bases* (levels that are not `succ`s).
Sub-levels are compared by `normCmp`, i.e. base first, then offset. -/
def baseCmp : Level → Level → Ordering
  | .max a b, .max c d =>
    ((baseCmp a.getLevelOffset c.getLevelOffset).then (compare a.getOffset c.getOffset)).then
      ((baseCmp b.getLevelOffset d.getLevelOffset).then (compare b.getOffset d.getOffset))
  | .imax a b, .imax c d =>
    ((baseCmp a.getLevelOffset c.getLevelOffset).then (compare a.getOffset c.getOffset)).then
      ((baseCmp b.getLevelOffset d.getLevelOffset).then (compare b.getOffset d.getOffset))
  | .param n₁, .param n₂ => Name.cmp n₁ n₂
  | .mvar n₁, .mvar n₂ => Name.cmp n₁.name n₂.name
  | l₁, l₂ => compare l₁.ctorToNat l₂.ctorToNat
termination_by l₁ l₂ => size l₁ + size l₂
decreasing_by
  all_goals
    first
    | (exact Nat.lt_of_le_of_lt
        (Nat.add_le_add (size_getLevelOffset_le _) (size_getLevelOffset_le _))
        (by simp only [size]; omega))

/-- Comparison of levels: base first, then offset. -/
def normCmp (l₁ l₂ : Level) : Ordering :=
  (baseCmp l₁.getLevelOffset l₂.getLevelOffset).then (compare l₁.getOffset l₂.getOffset)

/-- The same-constructor part of `baseCmp`. It is `.eq` when the constructors differ, in which
case the `ctorToNat` comparison of `baseCmp_eq` already decides the comparison. -/
private def structCmp : Level → Level → Ordering
  | .max a b, .max c d => (normCmp a c).then (normCmp b d)
  | .imax a b, .imax c d => (normCmp a c).then (normCmp b d)
  | .param n₁, .param n₂ => Name.cmp n₁ n₂
  | .mvar n₁, .mvar n₂ => Name.cmp n₁.name n₂.name
  | _, _ => .eq

/-- `baseCmp` is the lexicographic product of the constructor tags with `structCmp`. -/
private theorem baseCmp_eq : ∀ l₁ l₂ : Level,
    baseCmp l₁ l₂ = (compare l₁.ctorToNat l₂.ctorToNat).then (structCmp l₁ l₂) := by
  intro l₁ l₂
  cases l₁ <;> cases l₂ <;> simp [baseCmp, structCmp, normCmp, ctorToNat]

private theorem baseCmp_swap : ∀ l₁ l₂ : Level, baseCmp l₂ l₁ = (baseCmp l₁ l₂).swap := by
  intro l₁ l₂
  induction l₁, l₂ using baseCmp.induct with
  | case1 a b c d ih₁ ih₂ | case2 a b c d ih₁ ih₂ =>
    rw [baseCmp, baseCmp]
    simp only [Ordering.swap_then]
    rw [← ih₁, ← ih₂,
      ← OrientedCmp.eq_swap (cmp := compare (α := Nat)) (a := c.getOffset) (b := a.getOffset),
      ← OrientedCmp.eq_swap (cmp := compare (α := Nat)) (a := d.getOffset) (b := b.getOffset)]
  | case3 n₁ n₂ | case4 n₁ n₂ =>
    rw [baseCmp, baseCmp]; exact OrientedCmp.eq_swap
  | case5 l₁ l₂ h₁ h₂ h₃ h₄ =>
    rw [baseCmp, baseCmp]
    · exact OrientedCmp.eq_swap
    all_goals grind

theorem normCmp_swap (l₁ l₂ : Level) : normCmp l₂ l₁ = (normCmp l₁ l₂).swap := by
  rw [normCmp, normCmp, Ordering.swap_then, ← baseCmp_swap,
    ← OrientedCmp.eq_swap (cmp := compare (α := Nat))]

private theorem normCmp_rot_of {a b c : Level}
    (h : Rot (baseCmp a.getLevelOffset b.getLevelOffset)
      (baseCmp b.getLevelOffset c.getLevelOffset) (baseCmp a.getLevelOffset c.getLevelOffset)) :
    Rot (normCmp a b) (normCmp b c) (normCmp a c) :=
  h.then (Rot.of_transCmp a.getOffset b.getOffset c.getOffset)

private theorem baseCmp_rot : ∀ l₁ l₂ l₃ : Level,
    Rot (baseCmp l₁ l₂) (baseCmp l₂ l₃) (baseCmp l₁ l₃) := by
  suffices key : ∀ n l₁ l₂ l₃, size l₁ + size l₂ + size l₃ ≤ n →
      Rot (baseCmp l₁ l₂) (baseCmp l₂ l₃) (baseCmp l₁ l₃) from
    fun l₁ l₂ l₃ => key _ l₁ l₂ l₃ (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro l₁ l₂ l₃ h
    have := one_le_size l₁; have := one_le_size l₂; have := one_le_size l₃
    omega
  | succ n ih =>
    intro l₁ l₂ l₃ hn
    rw [baseCmp_eq, baseCmp_eq, baseCmp_eq]
    refine (Rot.of_transCmp ..).then' fun e₁ e₂ e₃ => ?_
    -- the sub-level comparisons are on strictly smaller levels
    have small : ∀ x y z : Level, size x + size y + size z < size l₁ + size l₂ + size l₃ →
        Rot (normCmp x y) (normCmp y z) (normCmp x z) := by
      intro x y z hxyz
      refine normCmp_rot_of (ih _ _ _ ?_)
      have := size_getLevelOffset_le x
      have := size_getLevelOffset_le y
      have := size_getLevelOffset_le z
      omega
    -- all three constructor tags agree, so all three levels share a constructor
    have hc₁ : l₁.ctorToNat = l₂.ctorToNat := Nat.compare_eq_eq.1 e₁
    have hc₂ : l₂.ctorToNat = l₃.ctorToNat := Nat.compare_eq_eq.1 e₂
    clear e₁ e₂ e₃ hn
    cases l₁ <;> cases l₂ <;> cases hc₁ <;> cases l₃ <;> cases hc₂ <;> simp only [structCmp]
    · exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    · exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    · refine Rot.then (small _ _ _ ?_) (small _ _ _ ?_) <;> (simp only [size_max]; omega)
    · refine Rot.then (small _ _ _ ?_) (small _ _ _ ?_) <;> (simp only [size_imax]; omega)
    · exact Rot.of_transCmp ..
    · exact Rot.of_transCmp ..

theorem normCmp_rot (a b c : Level) : Rot (normCmp a b) (normCmp b c) (normCmp a c) :=
  normCmp_rot_of (baseCmp_rot ..)

instance : TransCmp baseCmp := TransCmp.of_rot (fun a b => baseCmp_swap b a) baseCmp_rot
instance : TransCmp normCmp := TransCmp.of_rot (fun a b => normCmp_swap b a) normCmp_rot

private theorem getOffsetAux_eq : ∀ (l : Level) (k), l.getOffsetAux k = l.getOffset + k := by
  intro l
  induction l with
  | succ l ih =>
    intro k
    show l.getOffsetAux (k+1) = l.getOffsetAux 1 + k
    rw [ih (k+1), ih 1]; omega
  | _ => intro k; simp [getOffsetAux, getOffset]

private theorem getOffset_succ {l : Level} : (Level.succ l).getOffset = l.getOffset + 1 := by
  show l.getOffsetAux 1 = _
  rw [getOffsetAux_eq]

private theorem getLevelOffset_succ {l : Level} :
    (Level.succ l).getLevelOffset = l.getLevelOffset := rfl

/-! ### Reflexivity and antisymmetry -/

private theorem baseCmp_refl : ∀ l : Level, baseCmp l l = .eq := by
  suffices key : ∀ n l, size l ≤ n → baseCmp l l = .eq from fun l => key _ l (Nat.le_refl _)
  intro n
  induction n with
  | zero => intro l h; have := one_le_size l; omega
  | succ n ih =>
    intro l hn
    have hnorm x (hx : size x ≤ n) : normCmp x x = .eq := by
      rw [normCmp, ih _ (Nat.le_trans (size_getLevelOffset_le x) hx), Nat.compare_eq_eq.2 rfl]; rfl
    rw [baseCmp_eq, Nat.compare_eq_eq.2 rfl]
    show structCmp l l = .eq
    cases l with simp only [structCmp]
    | max a b | imax a b =>
      rw [hnorm a, hnorm b]; rfl
      all_goals simp only [size] at hn ⊢; omega
    | _ => exact LawfulBEqCmp.compare_eq_iff_beq.2 (beq_self_eq_true _)

theorem normCmp_refl (l : Level) : normCmp l l = .eq := by
  rw [normCmp, baseCmp_refl, Nat.compare_eq_eq.2 rfl]; rfl

instance : ReflCmp baseCmp where compare_self := baseCmp_refl _
instance : ReflCmp normCmp where compare_self := normCmp_refl _

/-- A level is determined by its base and its offset. -/
private theorem level_ext : ∀ {l₁ l₂ : Level}, l₁.getLevelOffset = l₂.getLevelOffset →
    l₁.getOffset = l₂.getOffset → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | succ a ih =>
    intro l₂
    cases l₂ with
    | succ b =>
      intro h₁ h₂
      rw [getLevelOffset_succ, getLevelOffset_succ] at h₁
      rw [getOffset_succ, getOffset_succ] at h₂
      exact congrArg Level.succ (ih h₁ (by omega))
    | _ => intro h₁ h₂; rw [getOffset_succ] at h₂; simp [getOffset, getOffsetAux] at h₂
  | _ =>
    intro l₂
    cases l₂ with
    | succ b => intro h₁ h₂; rw [getOffset_succ] at h₂; simp [getOffset, getOffsetAux] at h₂
    | _ => intro h₁ h₂; exact h₁

private theorem getLevelOffset_ne_succ : ∀ (l a : Level), l.getLevelOffset ≠ .succ a := by
  intro l
  induction l with
  | succ b ih => exact ih
  | _ => intro a h; cases h

theorem eq_of_normCmp_eq : ∀ {l₁ l₂ : Level}, normCmp l₁ l₂ = .eq → l₁ = l₂ := by
  suffices key : ∀ n (l₁ l₂ : Level), size l₁ + size l₂ ≤ n → normCmp l₁ l₂ = .eq → l₁ = l₂ from
    fun {l₁ l₂} h => key _ l₁ l₂ (Nat.le_refl _) h
  intro n
  induction n with
  | zero => intro l₁ l₂ h; have := one_le_size l₁; have := one_le_size l₂; omega
  | succ n ih =>
    intro l₁ l₂ hn h
    rw [normCmp, baseCmp_eq] at h
    obtain ⟨h₁, hoff⟩ := Ordering.then_eq_eq.1 h
    obtain ⟨hc, hs⟩ := Ordering.then_eq_eq.1 h₁
    refine level_ext ?_ (Nat.compare_eq_eq.1 hoff)
    have hb₁ := size_getLevelOffset_le l₁
    have hb₂ := size_getLevelOffset_le l₂
    have hns₁ := getLevelOffset_ne_succ l₁
    have hns₂ := getLevelOffset_ne_succ l₂
    clear h h₁ hoff
    generalize l₁.getLevelOffset = b₁ at *
    generalize l₂.getLevelOffset = b₂ at *
    replace hc := Nat.compare_eq_eq.1 hc
    cases b₁ <;> cases b₂ <;> try simp only [ctorToNat, Nat.reduceEqDiff] at hc
    · rfl
    · exact absurd rfl (hns₁ _)
    · obtain ⟨e₁, e₂⟩ := Ordering.then_eq_eq.1 hs
      rw [ih _ _ _ e₁, ih _ _ _ e₂] <;> (simp only [size_max] at hb₁ hb₂ ⊢; omega)
    · obtain ⟨e₁, e₂⟩ := Ordering.then_eq_eq.1 hs
      rw [ih _ _ _ e₁, ih _ _ _ e₂] <;> (simp only [size_imax] at hb₁ hb₂ ⊢; omega)
    · simp only [structCmp] at hs
      rw [eq_of_beq (LawfulBEqCmp.compare_eq_iff_beq.1 hs)]
    · rename_i x y
      have : x.name = y.name := eq_of_beq (LawfulBEqCmp.compare_eq_iff_beq.1 hs)
      cases x; cases y; simp_all

instance : LawfulEqCmp normCmp where eq_of_compare := eq_of_normCmp_eq

/-! ### `normLt` in terms of `normCmp` -/

private theorem compare_beq_lt (a b : Nat) : (compare a b == Ordering.lt) = decide (a < b) := by
  apply Bool.eq_iff_iff.2; simp [Nat.compare_eq_lt]

private theorem base_max {a b : Level} : (Level.max a b).getLevelOffset = .max a b := rfl
private theorem base_imax {a b : Level} : (Level.imax a b).getLevelOffset = .imax a b := rfl
private theorem off_max {a b : Level} : (Level.max a b).getOffset = 0 := rfl
private theorem off_imax {a b : Level} : (Level.imax a b).getOffset = 0 := rfl

/-- `normLtAux` accumulates the `succ`s into the offsets and then runs `normCmp`. -/
private theorem normLtAux_eq : ∀ (l₁ : Level) (k₁ : Nat) (l₂ : Level) (k₂ : Nat),
    normLtAux l₁ k₁ l₂ k₂ =
      ((baseCmp l₁.getLevelOffset l₂.getLevelOffset).then
        (compare (l₁.getOffset + k₁) (l₂.getOffset + k₂)) == .lt) := by
  intro l₁ k₁ l₂ k₂
  induction l₁, k₁, l₂, k₂ using normLtAux.induct with
  | case1 l₁ k₁ l₂ k₂ ih =>
    rw [normLtAux, ih]
    simp only [getLevelOffset_succ, getOffset_succ]
    rw [show l₁.getOffset + 1 + k₁ = l₁.getOffset + (k₁ + 1) by omega]
  | case2 l₁ k₁ l₂ k₂ hns ih =>
    rw [normLtAux, ih]
    simp only [getLevelOffset_succ, getOffset_succ]
    rw [show l₂.getOffset + 1 + k₂ = l₂.getOffset + (k₂ + 1) by omega]
    exact hns
  | case3 a b k₁ c d k₂ hbeq | case6 a b k₁ c d k₂ hbeq =>
    -- the two levels are syntactically equal: the offsets decide
    rw [normLtAux, if_pos hbeq, Bool.eq_iff_iff]
    cases eq_of_beq hbeq
    show _ ↔ ((baseCmp _ _).then (compare (0 + k₁) (0 + k₂)) == _)
    rw [baseCmp_refl]
    simp only [decide_eq_true_eq, Ordering.then, Nat.zero_add, beq_iff_eq, Nat.compare_eq_lt]
  | case4 a b k₁ c d k₂ hbeq hne ih | case7 a b k₁ c d k₂ hbeq hne ih =>
    -- the heads differ, so the head comparison decides
    rw [normLtAux, if_neg (by simpa using hbeq), if_pos hne, ih]
    have hne' : a ≠ c := by simpa using hne
    have hac : normCmp a c ≠ .eq := fun h => hne' (eq_of_normCmp_eq h)
    simp only [base_max, base_imax, off_max, off_imax, Nat.add_zero, Nat.zero_add]
    rw [baseCmp]
    show ((normCmp a c) == _) = (((normCmp a c).then (normCmp b d)).then (compare k₁ k₂) == _)
    cases h : normCmp a c <;> simp_all [Ordering.then]
  | case5 a b k₁ c d k₂ hbeq hne ih | case8 a b k₁ c d k₂ hbeq hne ih =>
    -- the heads agree, so the tail comparison decides
    rw [normLtAux, if_neg (by simpa using hbeq), if_neg hne, ih]
    have hac : a = c := by simpa using hne
    subst hac
    have hne' : b ≠ d := by rintro rfl; exact absurd (by simp) hbeq
    have hbd : normCmp b d ≠ .eq := fun h => hne' (eq_of_normCmp_eq h)
    simp only [base_max, base_imax, off_max, off_imax, Nat.add_zero, Nat.zero_add]
    rw [baseCmp]
    show ((normCmp b d) == _) = (((normCmp a a).then (normCmp b d)).then (compare k₁ k₂) == _)
    rw [normCmp_refl]
    cases h : normCmp b d <;> simp_all [Ordering.then]
  | case9 n₁ k₁ n₂ k₂ hbeq =>
    rw [normLtAux, if_pos hbeq, Bool.eq_iff_iff]
    cases eq_of_beq hbeq
    show _ ↔ ((baseCmp (Level.param n₁) (Level.param n₁)).then (compare (0 + k₁) (0 + k₂)) == _)
    rw [baseCmp_refl]
    simp only [decide_eq_true_eq, Ordering.then, Nat.zero_add, beq_iff_eq, Nat.compare_eq_lt]
  | case11 n₁ k₁ n₂ k₂ hbeq =>
    rw [normLtAux, if_pos hbeq, Bool.eq_iff_iff]
    cases eq_of_beq hbeq
    show _ ↔ ((baseCmp (Level.mvar n₁) (Level.mvar n₁)).then (compare (0 + k₁) (0 + k₂)) == _)
    rw [baseCmp_refl]
    simp only [decide_eq_true_eq, Ordering.then, Nat.zero_add, beq_iff_eq, Nat.compare_eq_lt]
  | case10 n₁ k₁ n₂ k₂ hbeq =>
    rw [normLtAux, if_neg hbeq]
    show _ = ((baseCmp (Level.param n₁) (Level.param n₂)).then
      (compare (0 + k₁) (0 + k₂)) == _)
    rw [baseCmp]
    have : Name.cmp n₁ n₂ ≠ .eq := fun h =>
      hbeq (LawfulBEqCmp.compare_eq_iff_beq.1 h)
    cases h : Name.cmp n₁ n₂ <;> simp_all [Name.lt, Ordering.then]
  | case12 n₁ k₁ n₂ k₂ hbeq =>
    rw [normLtAux, if_neg hbeq]
    show _ = ((baseCmp (Level.mvar n₁) (Level.mvar n₂)).then
      (compare (0 + k₁) (0 + k₂)) == _)
    rw [baseCmp]
    have : Name.cmp n₁.name n₂.name ≠ .eq := fun h => hbeq (by
      have := eq_of_beq (LawfulBEqCmp.compare_eq_iff_beq.1 h)
      cases n₁; cases n₂; simp_all)
    cases h : Name.cmp n₁.name n₂.name <;> simp_all [Name.lt, Ordering.then]
  | case13 l₁ k₁ l₂ k₂ hs₁ hs₂ hmax himax hpar hmvar hbeq
  | case14 l₁ k₁ l₂ k₂ hs₁ hs₂ hmax himax hpar hmvar hbeq =>
    -- neither level is a `succ` and their constructors differ, so the tags decide
    rw [normLtAux, baseCmp_eq]
    · cases l₁ <;> cases l₂ <;>
        simp_all [structCmp, ctorToNat, Ordering.then, compare_beq_lt, getLevelOffset, getOffset,
          getOffsetAux] <;> grind
    all_goals assumption

theorem normLt_eq (l₁ l₂ : Level) : normLt l₁ l₂ = (normCmp l₁ l₂ == .lt) := by
  rw [normLt, normLtAux_eq, normCmp, Nat.add_zero, Nat.add_zero]

/-! ### `normLt` is a strict weak order -/

theorem normLt_asymm {a b : Level} (h : normLt a b) : ¬normLt b a := by
  simp only [normLt_eq, beq_iff_eq] at h ⊢
  exact OrientedCmp.not_lt_of_lt h

theorem normLt_le_trans {a b c : Level} (h₁ : ¬normLt b a) (h₂ : ¬normLt c b) : ¬normLt c a := by
  simp only [normLt_eq, beq_iff_eq, ← Ordering.isGE_iff_ne_lt] at h₁ h₂ ⊢
  exact TransCmp.isGE_trans h₂ h₁

/-- On levels with equal bases, `normLt` compares the offsets. -/
theorem normLt_same_base {l₁ l₂ : Level} (h : l₁.getLevelOffset = l₂.getLevelOffset) :
    normLt l₁ l₂ = decide (l₁.getOffset < l₂.getOffset) := by
  rw [normLt_eq, normCmp, h, baseCmp_refl]
  simp only [Ordering.then, compare_beq_lt]

end Lean.Level
