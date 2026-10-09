import Lean4Lean.Theory.Typing.PrefixUnfolding.GenerationLevels
import Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLift

/-! Fixed-context universe congruence of concrete singleton and primitive
quotient prefix reconstruction. -/

namespace Lean4Lean.VEnv
open VExpr InductiveSignature InductiveSignature.RecursorData

theorem PrefixUnfold.congr_levels {name : Name} {levels levels' : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : PrefixUnfold env U registry Γ name levels args rhs)
    (hw' : ∀ level ∈ levels', level.WF U)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (ha : List.Forall₂ (EqUpToLevels U) args args') :
    ∃ rhs', PrefixUnfold env U registry Γ name levels' args' rhs' ∧ EqUpToLevels U rhs rhs' := by
  cases H with
  | @intro data program hlookup hregistered hname hlarge hw hz hg replay =>
    obtain ⟨program', hg', hp⟩ := singletonUnfolding_levels hw hw' he ha hg
    have hs := EqUpToLevels.mkApps_args (EqUpToLevels.const (c := name) hw hw' he) ha
    have replay' := replay.congr_levels henv hΓ hp hs
    have hz' : data.sourceLevel levels' ≈ .zero :=
      (VLevel.inst_congr rfl he).symm.trans hz
    exact ⟨_, .intro hlookup hregistered hname hlarge hw' hz' hg' replay', hp.rhs replay.levels_wf⟩

theorem QuotPrefixUnfold.congr_levels {levels levels' : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : QuotPrefixUnfold env U Γ levels args rhs)
    (hw' : ∀ level ∈ levels', level.WF U)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (ha : List.Forall₂ (EqUpToLevels U) args args') :
    ∃ rhs', QuotPrefixUnfold env U Γ levels' args' rhs' ∧ EqUpToLevels U rhs rhs' := by
  cases H with
  | intro hregistered hw hz hg replay =>
    obtain ⟨program', hg', hp⟩ := QuotPrefixUnfolding.generate_levels hw hw' he ha hg
    have hs := EqUpToLevels.mkApps_args (EqUpToLevels.const (c := ``Quot.lift) hw hw' he) ha
    have replay' := replay.congr_levels henv hΓ hp hs
    have hz' : levels'[0]?.getD .zero ≈ .zero := by
      have hlen := (QuotPrefixUnfolding.generate_spec hg).1
      cases he with
      | nil => simp at hlen
      | cons h hs => exact h.symm.trans hz
    exact ⟨_, .intro hregistered hw' hz' hg' replay', hp.rhs replay.levels_wf⟩

end Lean4Lean.VEnv
