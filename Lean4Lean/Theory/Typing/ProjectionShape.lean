import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.Typing.Injectivity

/-!
# Chained parameter agreement for registered projections

`Ordered.projectionShape` relates the header and constructor parameter
telescopes of a registered projection entry to one common declaration
parameter context.  Composing the two conversions needs transitivity of
definitional equality across differently typed sides, which is available only
through the uniqueness-of-typing development; the composed form is therefore
kept in this separate module.
-/

namespace Lean4Lean
namespace VEnv

/-- Compose two context conversions over the empty base.  The domain proof of
the second conversion is transported back across the already composed prefix
before transitivity is applied. -/
theorem IsDefEqCtx.trans_empty (henv : VEnv.WF env)
    (H₁ : IsDefEqCtx env U [] Γ₁ Γ₂) (H₂ : IsDefEqCtx env U [] Γ₂ Γ₃) :
    IsDefEqCtx env U [] Γ₁ Γ₃ := by
  induction H₁ generalizing Γ₃ with
  | zero => exact H₂
  | @succ Γ₁ Γ₂ A₁ A₂ u H₁ hdom ih =>
    cases H₂ with
    | succ H₂ hdom₂ =>
      have Hprefix := ih H₂
      have hdom₂' := hdom₂.defeqDFC henv.ordered (H₁.symm henv.ordered)
      exact .succ Hprefix (hdom.trans_r henv H₁.isType hdom₂')

end VEnv
end Lean4Lean
