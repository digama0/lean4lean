import Lean4Lean.Theory.Inductive.RecursorData

/-! Prefix unfolding of a recursor at a singleton:
the recursor applied to arguments up to its major is unfolded to a lambda whose body is the
singleton iota equation at the reconstructed constructor (`prefixUnfolding`). The constructor
is reconstructed only after checking its indices. The program may be exposed at any prefix: the unsupplied telescope
is opened with fresh variables, and later closed over the generated body.
For equality, opening an arbitrary endpoint does not make reflexivity a
constructor at that endpoint. The typing rule must check that alignment.
-/

namespace Lean4Lean.InductiveSignature.RecursorData

structure PrefixUnfolding where
  domains : List VExpr
  result : VExpr
  constructor : VExpr
  equation : VDefEq
  equationBody : RecursorSchema.EquationBody
  captures : List VExpr
  levels : List VLevel

def PrefixUnfolding.type (program : PrefixUnfolding) : VExpr :=
  VExpr.wrapForalls program.domains program.result

def PrefixUnfolding.rhs (program : PrefixUnfolding) : VExpr :=
  VExpr.wrapLams program.domains (instantiateParams (program.equationBody.rhs.instL program.levels) program.captures)

/-- Instantiate a dependent forall type with the supplied prefix of arguments. -/
def supplyType : List VExpr → VExpr → Option VExpr
  | [], type => some type
  | arg :: args, .forallE _ type => supplyType args (type.inst arg)
  | _ :: _, _ => none

end Lean4Lean.InductiveSignature.RecursorData
