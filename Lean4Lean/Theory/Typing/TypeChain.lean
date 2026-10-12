import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Strong

/-! # Chains of sort-typed definitional equalities

`TypeChain` (the closure of type-level definitional equality under heterogeneous
transitivity) and `SpineArgsEq` (arguments related along a Pi telescope), with the
structural chain lemmas. Uniqueness-free: imported by both `HeadInversion.lean` and the
injectivity development `HeadInjectivity/`, which must not import `HeadInversion.lean`
(whose theorem it helps prove). -/

namespace Lean4Lean
namespace VEnv

/-- Nonempty chains of definitional equalities, each link typed at some sort.

This is the closure of type-level definitional equality under heterogeneous
transitivity: consecutive links may be typed at different sorts. Without uniqueness of
types two links cannot be composed into one, so uniqueness is first proved up to such a
chain (`HasTypeStrong.uniq_chain_of_chainHeadInjectivity`) and then collapsed
(`TypeChain.collapse_of_chainHeadInjectivity`). -/
def TypeChain (env : VEnv) (U : Nat) (Γ : List VExpr) : VExpr → VExpr → Prop :=
  Relation.TransGen fun A B => ∃ u, env.IsDefEq U Γ A B (.sort u)

/-- Arguments related pointwise at the domains of a Pi telescope, each domain
instantiated by the left arguments already consumed. -/
inductive SpineArgsEq (env : VEnv) (U : Nat) (Γ : List VExpr) :
    VExpr → List VExpr → List VExpr → Prop
  | nil : SpineArgsEq env U Γ T [] []
  | cons : env.IsDefEq U Γ a a' A → SpineArgsEq env U Γ (B.inst a) as as' →
      SpineArgsEq env U Γ (.forallE A B) (a :: as) (a' :: as')

/-! ## Chain lemmas

Chains inherit the structural operations of `IsDefEq` link by link; none of these
lemmas uses uniqueness. -/

section
variable {env : VEnv} {U : Nat} {Γ : List VExpr}

theorem TypeChain.single (h : env.IsDefEq U Γ A B (.sort u)) : env.TypeChain U Γ A B :=
  Relation.TransGen.single ⟨_, h⟩

theorem TypeChain.refl (h : env.HasType U Γ A (.sort u)) : env.TypeChain U Γ A A :=
  .single h

theorem TypeChain.trans (h1 : env.TypeChain U Γ A B) (h2 : env.TypeChain U Γ B C) :
    env.TypeChain U Γ A C := Relation.TransGen.trans h1 h2

theorem TypeChain.symm (h : env.TypeChain U Γ A B) : env.TypeChain U Γ B A := by
  induction h with
  | single h => let ⟨_, h⟩ := h; exact .single h.symm
  | tail _ h ih => let ⟨_, h⟩ := h; exact (TypeChain.single h.symm).trans ih

theorem TypeChain.head (h1 : env.IsDefEq U Γ A B (.sort u)) (h2 : env.TypeChain U Γ B C) :
    env.TypeChain U Γ A C := (TypeChain.single h1).trans h2

theorem TypeChain.tail (h1 : env.TypeChain U Γ A B) (h2 : env.IsDefEq U Γ B C (.sort u)) :
    env.TypeChain U Γ A C := h1.trans (.single h2)

/-- Map every link of a chain through a function on single links. -/
theorem TypeChain.map {env' : VEnv} {U' : Nat} {Γ' : List VExpr} {f : VExpr → VExpr}
    (hf : ∀ {A B u}, env.IsDefEq U Γ A B (.sort u) →
      ∃ v, env'.IsDefEq U' Γ' (f A) (f B) (.sort v))
    (h : env.TypeChain U Γ A B) : env'.TypeChain U' Γ' (f A) (f B) := by
  induction h with
  | single h => let ⟨_, h⟩ := h; exact Relation.TransGen.single (hf h)
  | tail _ h ih => let ⟨_, h⟩ := h; exact Relation.TransGen.tail ih (hf h)

/-- Transport a definitional equality along a chain, one `defeqDF` step per link. -/
theorem TypeChain.defeqDF (H : env.TypeChain U Γ A B) (h : env.IsDefEq U Γ e₁ e₂ A) :
    env.IsDefEq U Γ e₁ e₂ B := by
  induction H with
  | single h' => let ⟨_, h'⟩ := h'; exact .defeqDF h' h
  | tail _ h' ih => let ⟨_, h'⟩ := h'; exact .defeqDF h' ih

/-- The left endpoint of a chain is a type. -/
theorem TypeChain.isType_l (H : env.TypeChain U Γ A B) : env.IsType U Γ A := by
  induction H with
  | single h => let ⟨_, h⟩ := h; exact ⟨_, h.hasType.1⟩
  | tail _ _ ih => exact ih

/-- The right endpoint of a chain is a type. -/
theorem TypeChain.isType_r (H : env.TypeChain U Γ A B) : env.IsType U Γ B := by
  induction H with
  | single h => let ⟨_, h⟩ := h; exact ⟨_, h.hasType.2⟩
  | tail _ h _ => let ⟨_, h⟩ := h; exact ⟨_, h.hasType.2⟩

theorem TypeChain.weakN (henv : env.Ordered) (W : Ctx.LiftN n k Γ Γ')
    (H : env.TypeChain U Γ A B) : env.TypeChain U Γ' (A.liftN n k) (B.liftN n k) :=
  H.map fun h => ⟨_, h.weakN henv W⟩

theorem TypeChain.instN (henv : env.Ordered) (h₀ : env.HasType U Γ₀ e₀ A₀)
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : env.TypeChain U Γ₁ A B) :
    env.TypeChain U Γ (A.inst e₀ k) (B.inst e₀ k) :=
  H.map fun h => ⟨_, h.instN henv h₀ W⟩

end

end VEnv
end Lean4Lean
