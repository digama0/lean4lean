import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Typing.LevelEquiv

/-! # Moving telescope instances between related telescopes

Arguments typed along a closed telescope are typed along any telescope that is pointwise
definitionally equal to it in the prefix contexts (`IsDefEqCtx` over the empty context), or
pointwise level-equivalent to it. -/

namespace Lean4Lean.VEnv
open VExpr

variable {env : VEnv} {U : Nat}

/-- An `IsDefEqCtx` over reversed telescopes, split at the last binder. -/
theorem IsDefEqCtx.snoc_inv
    (H : IsDefEqCtx env U [] (A ++ [a]).reverse (B ++ [b]).reverse) :
    IsDefEqCtx env U [] A.reverse B.reverse ∧ ∃ u, env.IsDefEq U A.reverse a b (.sort u) := by
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append] at H
  cases H with
  | succ h1 h2 => exact ⟨h1, _, h2⟩

end Lean4Lean.VEnv
