import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Inductive.CompilationLemmas

/-! The ill-typed sort equation `Prop ≡ Prop → Prop` occurs in no block derived by the finite
compilation judgment `CompiledInductive`, whatever the source declaration and environment.
-/

namespace Lean4Lean.Tests.SortEquationRejection

/-- The equation `Prop ≡ Prop → Prop` at `Type`. -/
def sortEquation : VDefEq where
  uvars := 0
  lhs := .sort .zero
  rhs := .forallE (.sort .zero) (.sort .zero)
  type := .sort (.succ .zero)

/-- This excludes the bad equation in any position of any candidate block,
not merely one chosen signature or one chosen auxiliary expansion. -/
theorem sortEquation_not_compiled {env : VEnv} {source : VInductDecl}
    {block : VInductBlock} (h : sortEquation ∈ block.rules) :
    ¬ CompiledInductive env source block :=
  CompiledInductive.reject_sort_lhs h rfl

/-- Adding otherwise valid generated equations before or after the bad rule
cannot make the resulting block a finite compilation. -/
theorem sortEquation_not_compiled_among_rules {env : VEnv} {source : VInductDecl}
    {block : VInductBlock} {before after : List VDefEq}
    (h : block.rules = before ++ sortEquation :: after) :
    ¬ CompiledInductive env source block := by
  apply sortEquation_not_compiled
  simp [h]

/-- `VInductDecl.CompilesTo`, which installation reads, also rejects the sort equation:
it carries the finite derivation. -/
theorem compilesTo_rejects_sortEquation {env : VEnv} {source : VInductDecl}
    {block : VInductBlock} (h : sortEquation ∈ block.rules) :
    ¬ source.CompilesTo env block := by
  intro H
  exact sortEquation_not_compiled h H

/-- Rejection is independent of the bad rule's position in the block. -/
theorem compilesTo_rejects_sortEquation_among_rules
    {env : VEnv} {source : VInductDecl} {block : VInductBlock}
    {before after : List VDefEq} (h : block.rules = before ++ sortEquation :: after) :
    ¬ source.CompilesTo env block := by
  apply compilesTo_rejects_sortEquation
  simp [h]

#print axioms sortEquation_not_compiled
#print axioms sortEquation_not_compiled_among_rules
#print axioms compilesTo_rejects_sortEquation
#print axioms compilesTo_rejects_sortEquation_among_rules

end Lean4Lean.Tests.SortEquationRejection
