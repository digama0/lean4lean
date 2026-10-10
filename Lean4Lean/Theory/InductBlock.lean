import Lean4Lean.Theory.DeclarationData

namespace Lean4Lean

/-- The output of compiling an inductive declaration. `VInductBlock.install` adds the types, the
constructors, the projections, the recursors and the rules, in that order. The projections are
installed after the constructors and before the recursors, so that the recursors are checked
in an environment where the block's structures already have their projections. -/
structure VInductBlock where
  types : List VConstVal
  ctors : List VConstVal
  recursors : List VConstVal
  rules : List VDefEq
  projections : List VProjectionEntry

end Lean4Lean
