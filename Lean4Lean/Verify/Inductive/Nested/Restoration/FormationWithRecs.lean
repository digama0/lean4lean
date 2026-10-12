import Lean4Lean.Verify.Inductive.Formation

/-! # Nested formation does not read the recursors

The nested formation judgment (`VInductDecl.NestedFormationWF`) and its expansion relations read
the source declaration's families, universes, parameters and safety only, so it holds for the
declaration with any recursor list (`VInductDecl.NestedFormationWF.withRecs`); the restored
block's declaration is the run's declaration with the restored recursors. -/

namespace Lean4Lean

open VInductDecl

namespace VerifyInductive

mutual

theorem NestedOccurrenceReplacement.withRecs {env : VEnv} {source : VInductDecl}
    {generated : List VInductiveType} {depth : Nat} {input output : VExpr}
    (recs : List VRecursor) :
    NestedOccurrenceReplacement env source generated depth input output →
    NestedOccurrenceReplacement env (source.withRecs recs) generated depth input output
  | .intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 =>
    .intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
      (NestedExprWFExpansion.withRecs recs h14) (NestedExprWFExpansion.withRecs recs h15)
      h16 h17

theorem NestedExprWFExpansion.withRecs {env : VEnv} {source : VInductDecl}
    {generated : List VInductiveType} {depth : Nat} {input output : VExpr}
    (recs : List VRecursor) :
    NestedExprWFExpansion env source generated depth input output →
    NestedExprWFExpansion env (source.withRecs recs) generated depth input output
  | .occurrence h1 h2 => .occurrence h1 (NestedOccurrenceReplacement.withRecs recs h2)
  | .bvar => .bvar
  | .sort => .sort
  | .const => .const
  | .proj h => .proj (NestedExprWFExpansion.withRecs recs h)
  | .app h1 h2 =>
    .app (NestedExprWFExpansion.withRecs recs h1) (NestedExprWFExpansion.withRecs recs h2)
  | .lam h1 h2 =>
    .lam (NestedExprWFExpansion.withRecs recs h1) (NestedExprWFExpansion.withRecs recs h2)
  | .forallE h1 h2 =>
    .forallE (NestedExprWFExpansion.withRecs recs h1) (NestedExprWFExpansion.withRecs recs h2)

theorem NestedForallPrefixWFExpansion.withRecs {env : VEnv} {source : VInductDecl}
    {generated : List VInductiveType} {depth arity : Nat} {input output : VExpr}
    (recs : List VRecursor) :
    NestedForallPrefixWFExpansion env source generated depth arity input output →
    NestedForallPrefixWFExpansion env (source.withRecs recs) generated depth arity input output
  | .nil h => .nil (NestedExprWFExpansion.withRecs recs h)
  | .cons h t => .cons (NestedExprWFExpansion.withRecs recs h)
      (NestedForallPrefixWFExpansion.withRecs recs t)

theorem NestedConstructorWFExpansions.withRecs {env : VEnv} {source : VInductDecl}
    {generated : List VInductiveType} {sources targets : List VConstVal}
    (recs : List VRecursor) :
    NestedConstructorWFExpansions env source generated sources targets →
    NestedConstructorWFExpansions env (source.withRecs recs) generated sources targets
  | .nil => .nil
  | .cons h1 h2 h3 t => .cons h1 h2 (NestedForallPrefixWFExpansion.withRecs recs h3)
      (NestedConstructorWFExpansions.withRecs recs t)

theorem NestedTypeWFExpansions.withRecs {env : VEnv} {source : VInductDecl}
    {generated sources targets : List VInductiveType}
    (recs : List VRecursor) :
    NestedTypeWFExpansions env source generated sources targets →
    NestedTypeWFExpansions env (source.withRecs recs) generated sources targets
  | .nil => .nil
  | .cons h1 h2 h3 h4 h5 h6 t => .cons h1 h2 h3 h4 h5
      (NestedConstructorWFExpansions.withRecs recs h6) (NestedTypeWFExpansions.withRecs recs t)

end

theorem NestedFormationWF.withRecs {env : VEnv} {source : VInductDecl}
    (recs : List VRecursor) (H : NestedFormationWF env source) :
    NestedFormationWF env (source.withRecs recs) := by
  cases H with
  | intro h1 h2 h3 h4 h5 h6 h7 =>
    exact .intro h1 h2 h3 h4 h5 h6 (NestedTypeWFExpansions.withRecs recs h7)

end VerifyInductive
end Lean4Lean
