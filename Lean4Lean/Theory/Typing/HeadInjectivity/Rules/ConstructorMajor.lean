import Lean4Lean.Theory.Typing.ProjectionRigidity

/-! # Constructor majors of computation rules

The syntactic notions the observation model reads off a computation rule's major premise:
the constructor heading the final argument of a λ-wrapped definitional axiom
(`VDefEq.HasConstructorMajor`, the quotient rule), the constructor of a registered ι pattern
(`VEnv.IsPatCtor`, `SimplePattern.iota`), and the codomain head of a constructor type
(`VExpr.forallResult`, `VEnv.CtorResultRigid`). On the ι pattern calculus the recursor rules
live in `VEnv.pats`, so the only `defeqs` entry with a constructor major is the quotient rule. -/

deriving instance DecidableEq for Lean4Lean.VLevel
deriving instance DecidableEq for Lean4Lean.VExpr

namespace Lean4Lean

/-- The final major argument of a λ-wrapped definitional axiom is headed by `name`. -/
def VDefEq.HasConstructorMajor (equation : VDefEq) (name : Name) : Prop :=
  ∃ fn levels args, equation.lhs.stripLams = .app fn (VExpr.mkApps (.const name levels) args)

/-- The codomain of a syntactic forall telescope. -/
def VExpr.forallResult : VExpr → VExpr
  | .forallE _ body => body.forallResult
  | e => e

theorem VExpr.forallResult_wrapForalls (doms : List VExpr) (body : VExpr) :
    (VExpr.wrapForalls doms body).forallResult = body.forallResult := by
  induction doms with
  | nil => rfl
  | cons d ds ih => exact ih

namespace VEnv

/-- `name` is the constructor of a registered ι pattern (`SimplePattern.iota`). -/
def IsPatCtor (env : VEnv) (name : Name) : Prop :=
  ∃ (p : Pattern) (r : p.RHS × p.Check) (recN : Name) (M N : Nat), env.pats p r ∧
    p = (SimplePattern.iota recN M name N).toPattern

/-- `name` is a constant whose type returns an application of a declared constant `F` at which
no rule computes. This holds for the majors of computation rules. -/
def CtorResultRigid (env : VEnv) (name : Name) : Prop :=
  ∃ ci, env.constants name = some ci ∧ ∃ F ls, ci.type.forallResult.getAppFnArgs.1 = .const F ls ∧
    (∃ ciF, env.constants F = some ciF) ∧ env.Rigid F

end VEnv
end Lean4Lean
