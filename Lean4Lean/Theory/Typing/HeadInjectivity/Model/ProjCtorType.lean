import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Tele
import Lean4Lean.Theory.Typing.HeadInjectivity.Projections.Declaration

/-! # Soundness of telescopes typed in an earlier environment

A constructor type registered by a projection entry is well formed in an earlier environment
`E` of the declaration history (`VEnv.ProjDecl`). Given soundness of `E`'s derivations in the
model of the final environment (`SoundIn`, which the history induction of
`Model/EnvValid.lean` provides), a Pi telescope typed in `E`, such as that constructor type, is
sound domain by domain (`piSD_of`). This depends only on `SoundAt`, `SD` and `PiSD`, not on
the observation clauses. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env E : VEnv} {U : Nat} {Δ : List VExpr}

/-- The soundness hypothesis on an earlier environment `E`. -/
def SoundIn (env E : VEnv) (U : Nat) (Δ : List VExpr) : Prop :=
  ∀ {Γ t t' T}, E.IsDefEqStrong U Γ t t' T → SoundAt env U Δ Γ t t' T

/-- The domains and codomains of a Pi telescope typed in `E` are sound, with strong
derivations in any extension `env` of `E`. -/
theorem piSD_of (hE : E.Ordered) (hle : E ≤ env) (hsE : SoundIn env E U Δ) :
    ∀ {Γ ds R u}, OnCtx Γ (E.IsType U) → E.HasType U Γ (VExpr.wrapForalls ds R) (.sort u) →
      PiSD env U Δ Γ ds R
  | _, [], _, _, _, _ => .nil
  | Γ, A :: ds, R, u, hΓ, h => by
    obtain ⟨⟨v, hA⟩, ⟨w, hB⟩⟩ := HasType.forallE_inv hE h
    have sA := IsDefEq.strong hE hΓ hA
    have hΓ' : OnCtx (A :: Γ) (E.IsType U) := ⟨hΓ, v, hA⟩
    have sB := IsDefEq.strong hE hΓ' hB
    exact .cons ⟨sA.mono hle, hsE sA⟩ ⟨sB.mono hle, hsE sB⟩ (piSD_of hE hle hsE hΓ' hB)

end Model
end VEnv
end Lean4Lean
