import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.NameGenerator

namespace Lean4Lean
open VEnv Lean

def ConditionallyTyped
    (ngen : NameGenerator) (env : VEnv) (Us : List Name) (Δ : VLCtx) (e : Expr) : Prop :=
  InScope ngen.Reserves e ∧ (InScope (· ∈ Δ.fvars) e → ∃ e', TrExpr env Us Δ e e')

theorem ConditionallyTyped.mono (H : ngen₁ ≤ ngen₂) :
    ConditionallyTyped ngen₁ env Us Δ e → ConditionallyTyped ngen₂ env Us Δ e
  | ⟨h1, h2⟩ => ⟨h1.mono fun _ h => h.mono H, h2⟩

theorem ConditionallyTyped.liftN_inv
    (H : ConditionallyTyped ngen env Us (d :: Δ) e) : ConditionallyTyped ngen env Us Δ e := by
  refine H.imp_right fun H1 H2 => ?_
  have ⟨e', H⟩ := H1 <| H2.mono fun _ h => by
    simp [VLCtx.fvars]; split <;> [exact h; exact h.tail _]
  sorry
  -- induction H with
  -- | bvar h1 | fvar h1 => exact ⟨_, hΔ.find?_wf henv h1⟩
  -- | sort h1 => exact ⟨_, .sort (.of_ofLevel h1)⟩
  -- | const h1 h2 h3 =>
  --   simp [List.mapM_eq_some] at h2
  --   refine ⟨_, .const h1 (fun l hl => ?_) (h2.length_eq.symm.trans h3)⟩
  --   have ⟨_, _, h⟩ := h2.forall_exists_r _ hl; exact .of_ofLevel h
  -- | app h1 h2 => exact ⟨_, .app h1 h2⟩
  -- | lam h1 _ _ _ ih2 =>
  --   have ⟨_, h1'⟩ := h1
  --   have ⟨_, h2'⟩ := ih2 ⟨hΔ, rfl, h1⟩
  --   refine ⟨_, .lam h1' h2'⟩
  -- | forallE h1 h2 => have ⟨_, h1'⟩ := h1; have ⟨_, h2'⟩ := h2; exact ⟨_, .forallE h1' h2'⟩
  -- | letE h1 _ _ _ _ _ ih3 => exact ih3 ⟨hΔ, rfl, h1⟩
  -- | lit _ ih | mdata _ ih => exact ih hΔ
  -- | proj _ h2 ih => exact h2.wf (ih hΔ)
