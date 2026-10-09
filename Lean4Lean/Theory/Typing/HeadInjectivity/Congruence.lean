import Lean4Lean.Theory.Typing.HeadInjectivity.ChainInjectivity

/-! # Congruence up to definitionally equal leaves

`CongrUB env U Γ₀ k t₁ t₂` says that `t₁` and `t₂` are the same term, under `k` binders
above the base context `Γ₀`, except at leaves, where they are the `k`-fold lifts of two
terms definitionally equal (at some type) in `Γ₀`, and at universe levels, which may differ
up to `≈` (the right side's levels being well formed, as `sortDF`, `constDF` and `elimDF`
require).

This is the relation along which field types of two typings of a projection are compared
(`HeadInjectivity/FieldType.lean`), and along which the uniqueness induction
(`HeadInjectivity/Uniqueness.lean`) produces definitional equalities: the comparison
follows the typing derivation of the left side, so leaves that are never typed (unused
earlier projections of a structure) are never visited. -/

namespace Lean4Lean
open Lean4Lean
namespace VEnv

inductive CongrUB (env : VEnv) (U : Nat) (Γ₀ : List VExpr) : Nat → VExpr → VExpr → Prop
  | leaf : env.IsDefEqU U Γ₀ a₁ a₂ → CongrUB env U Γ₀ k (a₁.liftN k) (a₂.liftN k)
  | bvar : CongrUB env U Γ₀ k (.bvar i) (.bvar i)
  | sort : l'.WF U → l ≈ l' → CongrUB env U Γ₀ k (.sort l) (.sort l')
  | const : (∀ l ∈ ls', l.WF U) → List.Forall₂ (· ≈ ·) ls ls' →
    CongrUB env U Γ₀ k (.const c ls) (.const c ls')
  | elim : (∀ l ∈ ls', l.WF U) → List.Forall₂ (· ≈ ·) ls ls' →
    CongrUB env U Γ₀ k (.elim block owner ls) (.elim block owner ls')
  | app : CongrUB env U Γ₀ k f f' → CongrUB env U Γ₀ k a a' →
    CongrUB env U Γ₀ k (.app f a) (.app f' a')
  | proj : CongrUB env U Γ₀ k e e' → CongrUB env U Γ₀ k (.proj s i e) (.proj s i e')
  | lam : CongrUB env U Γ₀ k A A' → CongrUB env U Γ₀ (k+1) b b' →
    CongrUB env U Γ₀ k (.lam A b) (.lam A' b')
  | forallE : CongrUB env U Γ₀ k A A' → CongrUB env U Γ₀ (k+1) b b' →
    CongrUB env U Γ₀ k (.forallE A b) (.forallE A' b')

namespace CongrUB
variable {env : VEnv} {U : Nat} {Γ₀ : List VExpr}

theorem leaf0 (h : env.IsDefEqU U Γ₀ a₁ a₂) : CongrUB env U Γ₀ 0 a₁ a₂ := by
  simpa using CongrUB.leaf (k := 0) h

theorem liftN (H : CongrUB env U Γ₀ k t₁ t₂) (hc : c ≤ k) :
    CongrUB env U Γ₀ (k+n) (t₁.liftN n c) (t₂.liftN n c) := by
  induction H generalizing c with
  | @leaf a₁ a₂ k h =>
    rw [VExpr.liftN'_liftN' (Nat.zero_le _) (by simpa using hc),
      VExpr.liftN'_liftN' (Nat.zero_le _) (by simpa using hc)]
    exact .leaf h
  | bvar => exact .bvar
  | sort h1 h2 => exact .sort h1 h2
  | const h1 h2 => exact .const h1 h2
  | elim h1 h2 => exact .elim h1 h2
  | app _ _ ih1 ih2 => exact .app (ih1 hc) (ih2 hc)
  | proj _ ih => exact .proj (ih hc)
  | lam _ _ ih1 ih2 =>
    exact .lam (ih1 hc) (by simpa [Nat.add_right_comm] using ih2 (Nat.succ_le_succ hc))
  | forallE _ _ ih1 ih2 =>
    exact .forallE (ih1 hc) (by simpa [Nat.add_right_comm] using ih2 (Nat.succ_le_succ hc))

theorem inst (H : CongrUB env U Γ₀ (k+1) B₁ B₂) (hp : CongrUB env U Γ₀ 0 p₁ p₂) :
    CongrUB env U Γ₀ k (B₁.inst p₁ k) (B₂.inst p₂ k) := by
  generalize hm : k + 1 = m at H
  induction H generalizing k with
  | @leaf a₁ a₂ m h =>
    subst hm
    rw [VExpr.inst_liftN_lo, VExpr.inst_liftN_lo]
    exact .leaf h
  | @bvar m i =>
    subst hm
    simp only [VExpr.inst, VExpr.instVar]
    split
    · exact .bvar
    · split
      · simpa using hp.liftN (n := k) (Nat.le_refl _)
      · exact .bvar
  | sort h1 h2 => exact .sort h1 h2
  | const h1 h2 => exact .const h1 h2
  | elim h1 h2 => exact .elim h1 h2
  | app _ _ ih1 ih2 => exact .app (ih1 hm) (ih2 hm)
  | proj _ ih => exact .proj (ih hm)
  | lam _ _ ih1 ih2 => exact .lam (ih1 hm) (ih2 (by omega))
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 hm) (ih2 (by omega))

theorem forall₂_inst_congr {ls₁ ls₂ : List VLevel} (h : List.Forall₂ (· ≈ ·) ls₁ ls₂)
    (us : List VLevel) :
    List.Forall₂ (· ≈ ·) (us.map (VLevel.inst ls₁)) (us.map (VLevel.inst ls₂)) := by
  induction us with
  | nil => exact .nil
  | cons u us ih => exact .cons (VLevel.inst_congr rfl h) ih

/-- Instantiating one term at two pointwise-equivalent level lists. -/
theorem instL_self {ls₁ ls₂ : List VLevel} (h : List.Forall₂ (· ≈ ·) ls₁ ls₂)
    (hwf : ∀ l ∈ ls₂, l.WF U) (T : VExpr) :
    CongrUB env U Γ₀ k (T.instL ls₁) (T.instL ls₂) := by
  induction T generalizing k with
  | bvar => exact .bvar
  | sort u => exact .sort (VLevel.WF.inst hwf) (VLevel.inst_congr rfl h)
  | const c us =>
    refine .const ?_ (forall₂_inst_congr h us)
    intro l hl
    obtain ⟨u, _, rfl⟩ := List.mem_map.1 hl
    exact VLevel.WF.inst hwf
  | elim b o us =>
    refine .elim ?_ (forall₂_inst_congr h us)
    intro l hl
    obtain ⟨u, _, rfl⟩ := List.mem_map.1 hl
    exact VLevel.WF.inst hwf
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | proj _ _ _ ih => exact .proj ih
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2

end CongrUB

end VEnv
end Lean4Lean
