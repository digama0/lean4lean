import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Inductive.CaseFormation

/-! # Typed terms project only out of registered structures

The only typing rule that introduces a projection node is `projDF`, whose premise registers the
structure. In the strong typing judgment every term of a rule's conclusion is a term of one of its
premises or is introduced by the rule itself, so both sides of a strong judgment project only out
of registered structures. -/

namespace Lean4Lean
namespace VEnv
open VExpr

theorem IsDefEqStrong.projNamesOK {env : VEnv} {U : Nat} {Γ : List VExpr} {e1 e2 A : VExpr}
    (H : env.IsDefEqStrong U Γ e1 e2 A) :
    e1.ProjNamesOK (fun S => ∃ info, env.projections S info) ∧
      e2.ProjNamesOK (fun S => ∃ info, env.projections S info) := by
  induction H with
  | bvar => exact ⟨trivial, trivial⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2⟩
  | sortDF => exact ⟨trivial, trivial⟩
  | constDF => exact ⟨trivial, trivial⟩
  | elimDF => exact ⟨trivial, trivial⟩
  | appDF _ _ _ _ _ _ _ _ _ ihf iha _ => exact ⟨⟨ihf.1, iha.1⟩, ⟨ihf.2, iha.2⟩⟩
  | projDF hp _ _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    exact ⟨⟨⟨_, hp⟩, ih1.2⟩, ⟨⟨_, hp⟩, ih2.2⟩⟩
  | lamDF _ _ _ _ _ _ _ ihA _ _ ihb _ => exact ⟨⟨ihA.1, ihb.1⟩, ⟨ihA.2, ihb.2⟩⟩
  | forallEDF _ _ _ _ _ ihA ihb _ => exact ⟨⟨ihA.1, ihb.1⟩, ⟨ihA.2, ihb.2⟩⟩
  | defeqDF _ _ _ _ ih => exact ih
  | beta _ _ _ _ _ _ _ _ ihA _ ihe ihe' _ ihi => exact ⟨⟨⟨ihA.1, ihe.1⟩, ihe'.1⟩, ihi.1⟩
  | eta _ _ _ _ _ _ _ _ ihA _ _ ihe _ _ =>
    exact ⟨⟨ihA.1, ⟨ProjNamesOK.liftN ihe.1, trivial⟩⟩, ihe.1⟩
  | proofIrrel _ _ _ _ ih1 ih2 => exact ⟨ih1.1, ih2.1⟩
  | extra _ _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 => exact ⟨ih1.1, ih2.1⟩
  | elimIota _ _ _ _ _ _ _ _ _ _ ih1 ih2 => exact ⟨ih1.1, ih2.1⟩
  | projIota _ _ _ _ ih1 ih2 => exact ⟨ih1.1, ih2.1⟩
  | structEta _ _ _ _ _ ih1 ih2 => exact ⟨ih2.1, ih1.1⟩
  | unitLike _ _ _ _ _ _ ih1 ih2 => exact ⟨ih1.1, ih2.1⟩

theorem IsDefEq.projNamesOK {env : VEnv} {U : Nat} {Γ : List VExpr} {e1 e2 A : VExpr}
    (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U)) (H : env.IsDefEq U Γ e1 e2 A) :
    e1.ProjNamesOK (fun S => ∃ info, env.projections S info) ∧
      e2.ProjNamesOK (fun S => ∃ info, env.projections S info) :=
  (H.strong henv hΓ).projNamesOK

end VEnv
end Lean4Lean
