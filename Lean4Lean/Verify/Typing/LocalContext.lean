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

theorem ConditionallyTyped.weakN_inv
    (henv : Ordered env) (hΔ : VLCtx.WF env Us.length ((some fv, d) :: Δ))
    (H : ConditionallyTyped ngen env Us ((some fv, d) :: Δ) e) :
    ConditionallyTyped ngen env Us Δ e := by
  refine H.imp_right fun H1 H2 => ?_
  have ⟨e', H⟩ := H1 H2.fvars_cons
  exact TrExpr.weakN_inv henv (.skip_fvar _ _ .refl) (.refl henv hΔ) H H2
