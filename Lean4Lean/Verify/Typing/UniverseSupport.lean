import Lean4Lean.Verify.ExprUniverses
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Std.Basic

/-! Strict translation checks every universe parameter in the source syntax. -/

namespace Lean4Lean
open Lean

theorem TrExprS.levelParamsIn (H : TrExprS env Us Δ e e') : e.levelParamsIn Us = true :=
  H.toTrSyn.levelParamsIn

theorem TrExpr.levelParamsIn (H : TrExpr env Us Δ e target) : e.levelParamsIn Us = true := by
  obtain ⟨_, htr, _⟩ := H
  exact htr.levelParamsIn

theorem BetaReduce.levelParamsIn (H : BetaReduce e e')
    (hs : e.levelParamsIn params = true) : e'.levelParamsIn params = true := by
  induction H with
  | refl => exact hs
  | trans _ _ ih1 ih2 => exact ih2 (ih1 hs)
  | app _ ih =>
    simp only [Expr.levelParamsIn, Bool.and_eq_true] at hs ⊢
    exact ⟨ih hs.1, hs.2⟩
  | beta =>
    simp only [Expr.levelParamsIn, Bool.and_eq_true] at hs
    exact Expr.levelParamsIn_instantiate1 hs.1.2 hs.2
end Lean4Lean
