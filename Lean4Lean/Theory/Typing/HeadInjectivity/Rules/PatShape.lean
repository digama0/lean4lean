import Lean4Lean.Theory.VExpr.TelescopeLemmas
import Lean4Lean.Theory.VDecl

/-! The pattern shape of computation rules.

A computation rule has the pattern shape when its left-hand side is
`wrapLams doms (mkApps head args)` whose arguments are either absent (a
definition) or leading arguments followed by a constructor-application major
whose trailing arguments are distinct bound variables, every binder occurring
as a bare leading argument or among those trailing variables. This file defines
the shape. On the ι pattern calculus the only stored rule of this shape is the quotient
rule; recursor rules are registered patterns (`VEnv.pats`). Purely syntactic: no typing. -/

namespace Lean4Lean

/-- Arguments of a rule's left-hand side under `n` binders: either no arguments (a
definition), or leading arguments followed by a major `mkApps (const ctor ls) (ms ++ fs)`
whose trailing arguments `fs` are distinct bound variables, such that every binder
`x < n` occurs as a bare leading argument `bvar x` or in `fs`. -/
def PatArgs (n : Nat) (args : List VExpr) : Prop :=
  (args = [] ∧ n = 0) ∨
  ∃ (lead : List VExpr) (ctor : Name) (ls : List VLevel) (ms : List VExpr) (fs : List Nat),
    args = lead ++ [VExpr.mkApps (.const ctor ls) (ms ++ fs.map .bvar)] ∧
    fs.Nodup ∧ (∀ i ∈ fs, i < n) ∧
    ∀ x < n, VExpr.bvar x ∈ lead ∨ x ∈ fs

/-- A rule whose left-hand side is a lambda-wrapped application of `head` to pattern
arguments; the right-hand side and the type are wrapped by the same binder domains. -/
structure VDefEq.PatShape (df : VDefEq) (head : VExpr) : Prop where
  shape : ∃ doms args body T, df.lhs = VExpr.wrapLams doms (VExpr.mkApps head args) ∧
    df.rhs = VExpr.wrapLams doms body ∧ df.type = VExpr.wrapForalls doms T ∧
    PatArgs doms.length args

theorem VExpr.wrapLams_mkApps_snoc_ne_const {ds as : List VExpr} {f a : VExpr} :
    VExpr.wrapLams ds (VExpr.mkApps f (as ++ [a])) ≠ .const n ls := by
  cases ds with
  | cons => simp [VExpr.wrapLams]
  | nil =>
    simp only [VExpr.wrapLams, List.foldr_nil, VExpr.mkApps, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    nofun

/-- The head of a lambda-wrapped constant spine. -/
theorem VExpr.stripLams_wrapLams_mkApps_head {ds args : List VExpr} :
    (VExpr.wrapLams ds (VExpr.mkApps (.const n ls) args)).stripLams.getAppFnArgs.1 =
      .const n ls := by
  rw [VExpr.stripLams_wrapLams]
  cases args with
  | nil => rfl
  | cons a as =>
    rw [show VExpr.mkApps (.const n ls) (a :: as) = VExpr.mkApps (.app (.const n ls) a) as
      from rfl]
    have : ∀ (f : VExpr) (as : List VExpr),
        (VExpr.mkApps (.app f a) as).stripLams = VExpr.mkApps (.app f a) as := by
      intro f as
      induction as generalizing f a with
      | nil => rfl
      | cons b bs ih => exact ih _ _
    rw [this, VExpr.getAppFnArgs, VExpr.getAppFnArgs_go_mkApps]
    rfl

end Lean4Lean
