import Lean4Lean.EquivManager

/-! # The equivalence manager's hash test is not invariant under renaming free variables

`checkRecursiveFields` (see `divergences.md`) compares two classifications of each constructor
field computed by `whnf` runs whose inputs differ by a renaming of free variables: the
positivity check opens the fields with one set of fresh identifiers of the inductive checker's
name generator (`_ind_fresh.i`), the minor pass of the recursor construction with another.
Replacing the comparison by a theorem would need the decisions of the checker to be invariant
under such a renaming. `whnf` asks `isDefEq` when it reduces a K-like recursor
(`toCtorWhenK`), and `isDefEqCore'` first asks the equivalence manager with `useHash := true`,
which answers `false` without consulting the union-find structure when the two hashes differ.
Hashes are not invariant under renaming: `_ind_fresh.39618` and `_ind_fresh.78546` give free
variables with the same `Expr.hash`, `_ind_fresh.0` and `_ind_fresh.1` do not. After the same
merge, the hash test answers `true` for the first pair and `false` for its renaming to the
second. (The other source of name dependence, the pointer-equality tests `ptrEqExpr` in
`isEquiv` and `isDefEqCore'`, is opaque in the model, so no relation between its answers on a
term and on its renaming is derivable at all.) The manager's answers are not only an
optimization: a conversion fact it records can decide a later comparison that the conversion
check would not otherwise settle (`Tests/CacheScope.lean`, with the C++ kernel's manager). -/

namespace Lean4Lean.Tests.FVarRenamingEquivManager
open Lean

def fresh (i : Nat) : Expr := .fvar ⟨.num `_ind_fresh i⟩

/-- Merge `a` and `b`, then ask the manager about them as `isDefEqCore'` does first. -/
def mergedThenAsked (useHash : Bool) (a b : Expr) : Bool :=
  ((EquivManager.isEquiv useHash a b).run (({} : EquivManager).addEquiv a b)).1

-- A hash collision between two identifiers of the inductive checker's name generator.
#guard (fresh 39618).hash == (fresh 78546).hash
#guard (fresh 0).hash != (fresh 1).hash

-- Without the hash test both pairs are found merged.
#guard mergedThenAsked false (fresh 39618) (fresh 78546)
#guard mergedThenAsked false (fresh 0) (fresh 1)

-- With it, the answer depends on the names: `true` for the colliding pair, `false` for its
-- renaming `_ind_fresh.39618 ↦ _ind_fresh.0`, `_ind_fresh.78546 ↦ _ind_fresh.1`.
#guard mergedThenAsked true (fresh 39618) (fresh 78546)
#guard !mergedThenAsked true (fresh 0) (fresh 1)

end Lean4Lean.Tests.FVarRenamingEquivManager
