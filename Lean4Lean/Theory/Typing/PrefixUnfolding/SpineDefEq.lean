import Lean4Lean.Theory.Typing.CaseMajorDomain
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Typing.EtaOpening

namespace Lean4Lean.VEnv
open VExpr

/-- Matching reconstructed dependent indices keeps the literal recursor head
and compares its scoped universe packets by level equivalence. Only the finite generated argument positions are
compared; an arbitrary source major is never matched through equality. -/
def ConstSpineDefEq (env : VEnv) (U : Nat) (Γ : List VExpr)
    (actual expected : VExpr) : Prop :=
  ∃ name levels levels' args args', actual = mkApps (.const name levels) args ∧
    expected = mkApps (.const name levels') args' ∧
    (∀ level ∈ levels, level.WF U) ∧ (∀ level ∈ levels', level.WF U) ∧
    List.Forall₂ (· ≈ ·) levels levels' ∧
    List.Forall₂ (env.IsDefEqU U Γ) args args'

private theorem constSpine_congr {env : VEnv} {U : Nat} {Γ : List VExpr}
    {fn fn' type : VExpr} {args args' : List VExpr} (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : List.Forall₂ (env.IsDefEqU U Γ) args args')
    (head : env.IsDefEqU U Γ fn fn') (ht : env.HasType U Γ (mkApps fn args) type) :
    env.IsDefEqU U Γ (mkApps fn args) (mkApps fn' args') := by
  induction H generalizing fn fn' with
  | nil => exact head
  | cons h _ ih =>
    have happ := VExpr.WF.of_mkApps henv.ordered hΓ (f := .app fn _) ⟨_, ht⟩
    obtain ⟨_, _, hf, ha⟩ := happ.app_inv henv.ordered hΓ
    exact ih ⟨_, IsDefEq.appDF (head.of_l henv hΓ hf) (h.of_l henv hΓ ha)⟩ ht

theorem ConstSpineDefEq.defeq (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : ConstSpineDefEq env U Γ actual expected)
    (ht : env.HasType U Γ actual type) : env.IsDefEqU U Γ actual expected := by
  obtain ⟨name, levels, levels', args, args', rfl, rfl, hw, hw', heq, hargs⟩ := H
  have hhead := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, ht⟩
  obtain ⟨_, hhead⟩ := hhead
  exact constSpine_congr henv hΓ hargs
    ⟨_, hhead.eqUpToLevels henv.ordered hΓ (.const hw hw' heq)⟩ ht

theorem ConstSpineDefEq.defeqDFC (henv : env.WF)
    (W : IsDefEqCtx env U Γ₀ Γ₁ Γ₂)
    (H : ConstSpineDefEq env U Γ₁ actual expected) :
    ConstSpineDefEq env U Γ₂ actual expected := by
  obtain ⟨name, levels, levels', args, args', ha, he, hw, hw', heq, hargs⟩ := H
  refine ⟨name, levels, levels', args, args', ha, he, hw, hw', heq, ?_⟩
  clear ha he actual expected
  induction hargs with
  | nil => exact .nil
  | cons h _ ih => exact .cons (h.defeqDFC henv W) ih

end Lean4Lean.VEnv
