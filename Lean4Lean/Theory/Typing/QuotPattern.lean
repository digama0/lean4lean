import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.Typing.QuotLemmas

namespace Lean4Lean

def quotLiftPattern : Pattern :=
  .app (.varN (.const ``Quot.lift) 5) (.varN (.const ``Quot.mk) 3)

def quotLiftPatternResult : quotLiftPattern.RHS :=
  .app (.var (.inl (some none))) (.var (.inr none))

def quotLiftPatternCheck : quotLiftPattern.Check :=
  .defeq (.var (.inl (some (some (some (some none))))))
    (.var (.inr (some (some none))))
    (.defeq (.var (.inl (some (some (some none))))) (.var (.inr (some none))) .true)

theorem quotLiftPattern.simple :
    quotLiftPattern = (SimplePattern.iota ``Quot.lift 5 ``Quot.mk 3).toPattern := rfl

theorem quotDefEq.not_matches (pattern : Pattern) {values : pattern.Path → VExpr} :
    ¬pattern.Matches (quotDefEq.lhs.instL levels) matchedLevels values := by
  exact Pattern.Matches.not_lam

theorem quotDefEq.patternEquation
    (registered : patterns quotLiftPattern (quotLiftPatternResult, quotLiftPatternCheck)) :
    Pattern.Equation patterns (VEnv.IsDefEqU environment universes) locals
      (quotDefEq.lhs.instL levels) (quotDefEq.rhs.instL levels) := by
  dsimp [quotDefEq, VExpr.instL]
  repeat' apply Pattern.Equation.lam
  have functionMatched := Pattern.Matches.const (c := ``Quot.lift)
    (ls := [VLevel.param 0, VLevel.param 1].map (VLevel.inst levels))
    |>.var (a' := .bvar 5) |>.var (a' := .bvar 4) |>.var (a' := .bvar 3)
    |>.var (a' := .bvar 2) |>.var (a' := .bvar 1)
  have constructorMatched := Pattern.Matches.const (c := ``Quot.mk)
    (ls := [VLevel.param 0].map (VLevel.inst levels))
    |>.var (a' := .bvar 5) |>.var (a' := .bvar 4) |>.var (a' := .bvar 0)
  have matched := functionMatched.app constructorMatched
  refine Pattern.Equation.rule registered matched ?_
  exact ⟨⟨_, .bvar (.succ (.succ (.succ (.succ (.succ .zero)))))⟩,
    ⟨⟨_, .bvar (.succ (.succ (.succ (.succ .zero))))⟩, trivial⟩⟩

end Lean4Lean
