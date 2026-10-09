import Lean4Lean.Theory.Inductive.CaseRegistration
import Lean4Lean.Theory.Typing.HeadInversion
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.CanonicalEq

/-! # Unique typing and its consequences.

Uniqueness of types for well-formed environments: the chain-level uniqueness and its collapse
to a single definitional equality are proved in `HeadInjectivity/Uniqueness.lean`
(`HasTypeStrong.uniq_chain_of_chainHeadInjectivity`,
`TypeChain.collapse_of_chainHeadInjectivity`) from the model's chain-level head injectivity
(`VEnv.WF.chainHeadInjectivity`). This file states the public consequences. -/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env U Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEq env U Γ e1 e2 A

theorem IsDefEq.uniq (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : Γ ⊢ e₁ ≡ e₂ : A) (h2 : Γ ⊢ e₂ ≡ e₃ : B) : ∃ u, Γ ⊢ A ≡ B : .sort u := by
  have core := henv.chainHeadInjectivity
  have H := HasTypeStrong.uniq_chain_of_chainHeadInjectivity henv core hΓ
    (h1.strong henv.ordered hΓ).hasType'.2 (h2.strong henv.ordered hΓ).hasType'.1
  have ⟨_, hA⟩ := h1.isType henv.ordered hΓ
  exact ⟨_, H.collapse_of_chainHeadInjectivity henv core hΓ hA⟩

theorem IsDefEq.uniqU (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEq U Γ e₁ e₂ A) (h2 : env.IsDefEq U Γ e₂ e₃ B) :
    env.IsDefEqU U Γ A B := let ⟨_, h⟩ := h1.uniq henv hΓ h2; ⟨_, h⟩

theorem isDefEq_iff (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    env.IsDefEq U Γ e₁ e₂ A ↔
    env.HasType U Γ e₁ A ∧ env.HasType U Γ e₂ A ∧ env.IsDefEqU U Γ e₁ e₂ := by
  refine ⟨fun h => ⟨h.hasType.1, h.hasType.2, _, h⟩, fun ⟨_, h2, _, h3⟩ => ?_⟩
  have ⟨_, h⟩ := h3.uniq henv hΓ h2
  exact h.defeqDF h3

theorem IsDefEq.trans_r (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : env.IsDefEq U Γ e₁ e₂ A) (h₂ : env.IsDefEq U Γ e₂ e₃ B) :
    env.IsDefEq U Γ e₁ e₃ B := have ⟨_, h⟩ := h₁.uniq henv hΓ h₂; .trans (.defeqDF h h₁) h₂

theorem IsDefEq.trans_l (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : env.IsDefEq U Γ e₁ e₂ A) (h₂ : env.IsDefEq U Γ e₂ e₃ B) :
    env.IsDefEq U Γ e₁ e₃ A := have ⟨_, h⟩ := h₁.uniq henv hΓ h₂; h₁.trans (.defeqDF (.symm h) h₂)

theorem IsDefEq.transU_r (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : env.IsDefEqU U Γ e₁ e₂) (h₂ : env.IsDefEq U Γ e₂ e₃ A) :
    env.IsDefEq U Γ e₁ e₃ A := have ⟨_, h₁⟩ := h₁; .trans_r henv hΓ h₁ h₂

theorem IsDefEq.transU_l (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : env.IsDefEq U Γ e₁ e₂ A) (h₂ : env.IsDefEqU U Γ e₂ e₃) :
    env.IsDefEq U Γ e₁ e₃ A := have ⟨_, h₂⟩ := h₂; .trans_l henv hΓ h₁ h₂

theorem IsDefEqU.defeqDF (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : env.IsDefEqU U Γ A B) (h₂ : env.IsDefEq U Γ e₁ e₂ A) :
    env.IsDefEq U Γ e₁ e₂ B := by
  have ⟨_, h₁⟩ := h₁
  have ⟨_, hA⟩ := h₂.isType henv hΓ
  exact .defeqDF (hA.trans_l henv hΓ h₁) h₂

theorem IsDefEqU.of_l (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ e₁ e₂) (h2 : env.HasType U Γ e₁ A) :
    env.IsDefEq U Γ e₁ e₂ A := let ⟨_, h⟩ := h1; h2.trans_l henv hΓ h

theorem HasType.defeqU_l (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ e₁ e₂) (h2 : env.HasType U Γ e₁ A) :
    env.HasType U Γ e₂ A := (h1.of_l henv hΓ h2).hasType.2

theorem IsType.defeqU_l (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ A₁ A₂) (h2 : env.IsType U Γ A₁) :
    env.IsType U Γ A₂ := h2.imp fun _ h2 => h2.defeqU_l henv hΓ h1

theorem IsDefEqU.of_r (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ e₁ e₂) (h2 : env.HasType U Γ e₂ A) :
    env.IsDefEq U Γ e₁ e₂ A := (h1.symm.of_l henv hΓ h2).symm

theorem HasType.defeqU_r (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ A₁ A₂) (h2 : env.HasType U Γ e A₁) :
    env.HasType U Γ e A₂ := h1.defeqDF henv hΓ h2

theorem IsDefEqU.trans (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ e₁ e₂) (h2 : env.IsDefEqU U Γ e₂ e₃) :
    env.IsDefEqU U Γ e₁ e₃ := h1.imp fun _ h1 => let ⟨_, h2⟩ := h2; h1.trans_l henv hΓ h2
