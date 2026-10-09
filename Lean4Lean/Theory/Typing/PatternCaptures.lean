import Lean4Lean.Theory.Typing.Pattern

/-! Ordered finite argument captures for stored-rule patterns. -/

namespace Lean4Lean

def Pattern.RHS.mapPaths {p q : Pattern} (f : p.Path → q.Path) : p.RHS → q.RHS
  | .fixed e h => .fixed e h
  | .var i => .var (f i)
  | .app fn arg => .app (fn.mapPaths f) (arg.mapPaths f)

theorem Pattern.RHS.mapPaths_apply {p q : Pattern} (f : p.Path → q.Path)
    (rhs : p.RHS) {values : q.Path → VExpr} : (rhs.mapPaths f).apply levels values = rhs.apply levels (values ∘ f) := by
  induction rhs <;> simp [Pattern.RHS.mapPaths, Pattern.RHS.apply, *]

/-- Captured arguments in source order, excluding captures inside the base pattern. -/
def Pattern.argumentRHS (p : Pattern) : (n : Nat) → List (p.varN n).RHS
  | 0 => []
  | n + 1 => ((p.argumentRHS n).map (Pattern.RHS.mapPaths some)) ++ [.var none]

theorem Pattern.argumentRHS_length (p : Pattern) (n : Nat) : (p.argumentRHS n).length = n := by
  induction n <;> simp [Pattern.argumentRHS, *]

/-- A matching constant spine has exactly the ordered captured arguments. -/
theorem Pattern.Matches.const_arguments
    (H : ((Pattern.const name).varN n).Matches expr levels values) :
    expr = VExpr.mkApps (.const name levels)
      (((Pattern.const name).argumentRHS n).map (fun rhs => rhs.apply levels values)) := by
  induction n generalizing expr with
  | zero => cases H; rfl
  | succ n ih =>
    cases H with
    | var hp =>
      rename_i f' a' values
      have hmap (x : ((Pattern.const name).varN n).RHS) :
          (x.mapPaths (q := ((Pattern.const name).varN n).var) some).apply levels
            (fun p => Option.elim p a' values) = x.apply levels values :=
        Pattern.RHS.mapPaths_apply _ _
      rw [ih hp]
      simp only [Pattern.argumentRHS, List.map_append, List.map_map,
        List.map_cons, List.map_nil, Pattern.RHS.apply,
        Function.comp_def, Option.elim_none]
      simp only [VExpr.mkApps, List.foldl_append, List.foldl_cons, List.foldl_nil]
      congr 2
      apply List.map_congr_left
      intro x _
      exact (hmap x).symm

end Lean4Lean
