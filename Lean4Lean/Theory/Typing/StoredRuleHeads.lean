import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.Typing.Pattern

namespace Lean4Lean

/-- The computational head of an equation, after its argument telescope. -/
def VExpr.equationHead : VExpr → VExpr
  | .lam _ body => body.equationHead
  | e => e.getAppFnArgs.1

theorem VExpr.equationHead_eq (e : VExpr) :
    e.equationHead = e.stripLams.getAppFnArgs.1 := by
  induction e with
  | lam _ _ _ ih => exact ih
  | _ => rfl

/-- The fixed constant head of a pattern (none for an eliminator head). -/
def Pattern.constHead : Pattern → Option Name
  | .const name => some name
  | .elim .. => none
  | .app fn _ | .var fn => fn.constHead

/-- Stored-rule computation must originate at an equation actually present in the
environment. Typing soundness alone would also permit invented reflexive or
eta rules at constructor heads, which are not executable equations. -/
def VEnv.PatternHeadsStoredRule (env : VEnv) (pattern : Pattern) : Prop :=
  ∃ equation name levels, env.defeqs equation ∧ pattern.constHead = some name ∧
    equation.lhs.equationHead = .const name levels

end Lean4Lean
