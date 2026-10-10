import Lean4Lean.Verify.Typing.Telescope
import Lean4Lean.Theory.Typing.ProjectionShape

/-! Context conversions used by the rule typing (source branch: `Install/Lookups.lean`). -/

namespace Lean4Lean

namespace VerifyInductive

/-- Rebase a conversion between two dependent prefixes along a conversion
of their common suffix.  Both prefix contexts are known well formed from the
given conversion, so changing the suffix on each side is admissible even
when the two dependent prefixes use different representatives. -/
theorem VEnv.IsDefEqCtx.rebaseCommonSuffix
    (henv : env.WF)
    (Hsuffix : VEnv.IsDefEqCtx env U [] outer inner)
    (Hprefix : VEnv.IsDefEqCtx env U []
      (left ++ inner) (right ++ inner)) :
    VEnv.IsDefEqCtx env U []
      (left ++ outer) (right ++ outer) := by
  have HleftToOuter :=
    VEnv.IsDefEqCtx.extendSamePrefix
      (Hsuffix.symm henv.ordered) Hprefix.isType
  have HrightInner := (Hprefix.symm henv.ordered).isType
  have HrightToOuter :=
    VEnv.IsDefEqCtx.extendSamePrefix
      (Hsuffix.symm henv.ordered) HrightInner
  exact Lean4Lean.VEnv.IsDefEqCtx.trans_empty henv
    (HleftToOuter.symm henv.ordered) <|
      Lean4Lean.VEnv.IsDefEqCtx.trans_empty henv Hprefix HrightToOuter

end VerifyInductive
end Lean4Lean
