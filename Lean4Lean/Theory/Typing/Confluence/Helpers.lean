import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.Typing.RecursorLemmas

/-! Generic syntactic helpers of the confluence development. -/

namespace Lean4Lean
namespace VExpr

theorem Subst.ofList_ge (args : List VExpr) (h : args.length ≤ k) :
    Subst.ofList args k = .bvar (k - args.length) := dif_neg (Nat.not_lt.2 h)

/-- Lifting an instantiation lifts the arguments. -/
theorem liftN_instOuter (X : VExpr) (args : List VExpr) (hX : X.ClosedN args.length) (n : Nat) :
    (X.instOuter args).liftN n = X.instOuter (args.map (·.liftN n)) := by
  simp only [instOuter_eq_subst, liftN_eq_subst]
  rw [subst_subst]
  apply subst_congr_closedN hX
  intro i hi
  simp only [Subst.comp, Subst.ofList_lt _ hi, List.length_map,
    Subst.ofList_lt (args.map _) (by simpa using hi), List.getElem_map]

end VExpr
end Lean4Lean
