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

/-- The fixed constant head of a pattern. -/
def Pattern.constHead : Pattern → Option Name
  | .const name => some name
  | .app fn _ | .var fn => fn.constHead

theorem Pattern.constHead_eq (p : Pattern) : p.constHead = some p.headConst := by
  induction p <;> simp [constHead, headConst, *]

/-- Pattern computation must originate at a rule actually present in the environment: a
stored equation (`VEnv.defeqs`, the definition unfoldings and the quotient rule) or a
registered reduction rule (`VEnv.pats`, the ι rules) headed by the pattern's constant. Typing
soundness alone would also permit invented reflexive or eta rules at constructor heads, which
are not executable rules. The two alternatives are the two fields of `VEnv.Rigid`. -/
def VEnv.PatternHeadsStoredRule (env : VEnv) (pattern : Pattern) : Prop :=
  ∃ name, pattern.constHead = some name ∧
    ((∃ equation levels, env.defeqs equation ∧ equation.lhs.equationHead = .const name levels) ∨
      ∃ (p : Pattern) (r : p.RHS × p.Check), env.pats p r ∧ p.headConst = name)

/-- A rigid constant heads no pattern that heads a rule. -/
theorem VEnv.Rigid.not_patternHeadsStoredRule {env : VEnv} {c : Name} (hr : env.Rigid c)
    {pattern : Pattern} (H : env.PatternHeadsStoredRule pattern) :
    pattern.constHead ≠ some c := by
  obtain ⟨name, hname, h | h⟩ := H
  · rintro h'
    rw [hname] at h'; cases h'
    obtain ⟨equation, levels, hdf, hhead⟩ := h
    rw [VExpr.equationHead_eq] at hhead
    exact hr.defeqs equation hdf levels hhead
  · rintro h'
    rw [hname] at h'; cases h'
    obtain ⟨p, r, hp, hhead⟩ := h
    exact hr.pats p r hp hhead

end Lean4Lean
