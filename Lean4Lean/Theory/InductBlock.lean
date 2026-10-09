import Lean4Lean.Theory.Inductive.CaseSchema

namespace Lean4Lean

/-- The output of compiling an inductive declaration. `VInductBlock.install` adds the types, the
constructors, the case eliminators, the projections, the recursors and the rules, in that
order. The case eliminators are installed
after the constructors and before the projections, so that every family with registered
projections has a registered case eliminator; their certification is part of `VEnv.AddInduct`. -/
structure VInductBlock where
  types : List VConstVal
  ctors : List VConstVal
  recursors : List VConstVal
  rules : List VDefEq
  projections : List VProjectionEntry
  eliminators : List (Name × InductiveSignature.CaseSchema) := []

end Lean4Lean
