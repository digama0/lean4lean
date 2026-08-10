import Init.Data.Order.Ord

/-!
A device for proving `Std.TransCmp` for comparisons defined by *lexicographic products*, used for
`Lean.Name.cmp` in `Lean4Lean.Verify.Name` and for the level order in `Lean4Lean.Verify.NormLt`.

Transitivity of a lexicographic product needs more than transitivity of its components: when the
first components compare `.eq` one has to know they compare `.eq` *in both directions* before the
second components can be consulted. Recursive comparisons therefore do not prove `isLE_trans` at a
triple `(a, b, c)` from `isLE_trans` at the sub-triple alone; one needs its rotations too. `Rot`
below packages the three rotations, which is exactly the statement that goes through the induction.
-/

namespace Lean4Lean
open Std

/-- The three rotations of transitivity for a comparison at a triple `a`, `b`, `c`, where
`x = cmp a b`, `y = cmp b c`, `z = cmp a c`. Note that the second and third components are the
first one at the rotated triples `(c, a, b)` and `(b, c, a)`, rewritten with `Ordering.swap`. -/
def Rot (x y z : Ordering) : Prop :=
  (x.isLE → y.isLE → z.isLE) ∧
  (z.swap.isLE → x.isLE → y.swap.isLE) ∧
  (y.isLE → z.swap.isLE → x.swap.isLE)

/-- Lexicographic products satisfy `Rot` if the components do. The second component's rotations
are only required when the first components are all `.eq`; this matters when the second component
is a comparison that is only meaningful where the first component does not already decide, as for
the level order, whose structural component compares unrelated constructors as `.eq`. -/
theorem Rot.then' : Rot x y z → (x = .eq → y = .eq → z = .eq → Rot x' y' z') →
    Rot (x.then x') (y.then y') (z.then z') := by
  cases x <;> cases y <;> simp_all [Rot]; cases z <;> simp

theorem Rot.then {x y z x' y' z' : Ordering}
    (R : Rot x y z) (R' : Rot x' y' z') : Rot (x.then x') (y.then y') (z.then z') :=
  R.then' fun _ _ _ => R'

/-- Any `TransCmp` gives `Rot` at every triple: the rotations are `isLE_trans` at the rotated
triples, rewritten with `OrientedCmp.eq_swap`. -/
theorem Rot.of_transCmp {α} {cmp : α → α → Ordering} [TransCmp cmp] (a b c : α) :
    Rot (cmp a b) (cmp b c) (cmp a c) := by
  refine ⟨fun h₁ h₂ => TransCmp.isLE_trans h₁ h₂, fun h₁ h₂ => ?_, fun h₁ h₂ => ?_⟩ <;>
    rw [← OrientedCmp.eq_swap (cmp := cmp)] at * <;>
    exact TransCmp.isLE_trans h₁ h₂

/-- `Rot` at every triple, plus orientedness, is exactly `TransCmp`. -/
theorem TransCmp.of_rot {α} {cmp : α → α → Ordering}
    (swap : ∀ a b : α, cmp a b = (cmp b a).swap)
    (rot : ∀ a b c : α, Rot (cmp a b) (cmp b c) (cmp a c)) : TransCmp cmp where
  eq_swap := swap ..
  isLE_trans h₁ h₂ := (rot ..).1 h₁ h₂

end Lean4Lean
