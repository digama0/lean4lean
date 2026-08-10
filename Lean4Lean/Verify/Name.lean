import Lean.Data.NameMap.Basic
import Lean4Lean.Std.Ord
import Std.Data.TreeSet.Lemmas

/-!
Order properties of `Lean.Name.cmp` and `Lean.Name.quickCmp`.
-/

namespace Lean

namespace Name
open _root_.Std Lean4Lean

theorem cmp_eq_swap {a b : Name} : a.cmp b = (b.cmp a).swap := by
  induction a generalizing b with obtain _|⟨b₁,b₂⟩|⟨b₁,b₂⟩ := b <;> simp [cmp]
  | str a₁ a₂ ih | num a₁ a₂ ih =>
    rw [ih]; cases b₁.cmp a₁ <;> simp [← OrientedOrd.eq_swap]

instance : TransCmp cmp := by
  refine TransCmp.of_rot (fun _ _ => cmp_eq_swap) fun a b c => ?_
  induction a generalizing b c with
  | anonymous =>
    obtain _|⟨b₁,b₂⟩|⟨b₁,b₂⟩ := b <;> obtain _|⟨c₁,c₂⟩|⟨c₁,c₂⟩ := c <;> simp [cmp, Rot]
  | str a₁ a₂ ih | num a₁ a₂ ih =>
    obtain _|⟨b₁,b₂⟩|⟨b₁,b₂⟩ := b <;> obtain _|⟨c₁,c₂⟩|⟨c₁,c₂⟩ := c <;>
      first
      | exact (ih ..).then (Rot.of_transCmp ..)
      | simp [cmp, Rot]

instance : LawfulBEqCmp cmp where
  compare_eq_iff_beq {a b} := by
    simp; refine ⟨?_, fun h => h ▸ ReflCmp.compare_self⟩
    induction a generalizing b with obtain _|⟨b₁,b₂⟩|⟨b₁,b₂⟩ := b <;> simp [cmp]
    | str a₁ a₂ ih | num a₁ a₂ ih =>
      refine ?_ ∘ Ordering.then_eq_eq.1
      simp +contextual; exact fun h _ => ih h

instance : TransCmp quickCmp where
  eq_swap {a b} := by
    simp [quickCmp]
    rw [OrientedOrd.eq_swap]
    cases compare b.hash a.hash <;> simp
    induction a generalizing b with obtain _|⟨b₁,b₂⟩|⟨b₁,b₂⟩ := b <;> simp [quickCmpAux]
    | str a₁ a₂ ih | num a₁ a₂ ih =>
      rw [OrientedOrd.eq_swap]
      cases compare b₂ a₂ <;> simp [ih]
  isLE_trans {a b c} := by
    have {α} [Ord α] [TransOrd α] {a₁ b₁ c₁ : α} {a₂ b₂ c₂}
        (H : (quickCmpAux a₂ b₂).isLE → (quickCmpAux b₂ c₂).isLE → (quickCmpAux a₂ c₂).isLE) :
        ((compare a₁ b₁).then (quickCmpAux a₂ b₂)).isLE →
        ((compare b₁ c₁).then (quickCmpAux b₂ c₂)).isLE →
        ((compare a₁ c₁).then (quickCmpAux a₂ c₂)).isLE := by
      simp [Ordering.isLE_then_iff_and]
      intro h1 h2 h3 h4
      refine ⟨TransCmp.isLE_trans h1 h3, ?_⟩
      refine h2.elim (fun h2 => .inl <| TransCmp.lt_of_lt_of_isLE h2 h3) fun h2 => ?_
      refine h4.elim (fun h4 => .inl <| TransCmp.lt_of_isLE_of_lt h1 h4) fun h4 => .inr (H h2 h4)
    apply this
    induction a generalizing b c with
      obtain _|⟨b₁,b₂⟩|⟨b₁,b₂⟩ := b <;> simp [quickCmpAux] at * <;>
      obtain _|⟨c₁,c₂⟩|⟨c₁,c₂⟩ := c <;> simp [quickCmpAux] at *
    | str a₁ a₂ ih | num a₁ a₂ ih => apply this ih

instance : LawfulBEqCmp quickCmp where
  compare_eq_iff_beq {a b} := by
    simp; refine ⟨fun h => ?_, fun h => h ▸ ReflCmp.compare_self⟩
    replace h := (Ordering.then_eq_eq.1 h).2; revert h
    induction a generalizing b with obtain _|⟨b₁,b₂⟩|⟨b₁,b₂⟩ := b <;> simp [quickCmpAux]
    | str a₁ a₂ ih | num a₁ a₂ ih =>
      refine ?_ ∘ Ordering.then_eq_eq.1
      simp +contextual; exact fun _ => ih

end Name

namespace NameSet
open _root_.Std

theorem contains_insert {s : NameSet} {a b : Name} :
    (s.insert a).contains b = (a == b || s.contains b) := by
  have key : (Name.quickCmp a b == Ordering.eq) = (a == b) := by
    have := @LawfulBEqCmp.compare_eq_iff_beq _ _ Name.quickCmp _ a b
    cases h : Name.quickCmp a b <;> simp_all
  have h : (s.insert a).contains b
      = (Name.quickCmp a b == Ordering.eq || s.contains b) :=
    Std.TreeSet.contains_insert (t := s) (k := a) (a := b)
  rw [h, key]

@[simp] theorem contains_empty {a : Name} : (∅ : NameSet).contains a = false := rfl

end NameSet
