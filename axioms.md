# Axioms used in the main theorem

Here is a complete listing and breakdown of the axioms used in
[`Lean4Lean.TypeChecker.checkType.WF`](Lean4Lean/Verify/TypeChecker.lean) and friends:

## • Lean builtin axioms

These are normal in all Lean projects.

* `propext`
* `Classical.choice`
* `Quot.sound`

## • Axioms from [Axioms.lean](Lean4Lean/Verify/Axioms.lean)

This file contains axioms which allow us to reason about the behavior of opaque
functions. See [Axioms.lean](Lean4Lean/Verify/Axioms.lean) for more details about
each axiom. This is the main coordination point for adapting to changes to Lean core.
We use axioms deliberately here, rather than reimplementing verified versions of the
functions (which can be done in many cases, and in fact most of these axioms assert
that a function from core is equal to a simpler executable spec function), because
a we want to ensure that we use the same function as the upstream kernel where possible.

* `Lean.PersistentArray.toList'_push`
* `Lean.PersistentHashMap.WF.toList'_insert`
* `Lean.PersistentHashMap.WF.find?_eq`
* `Lean.PersistentHashMap.findAux_isSome`
* `Lean.Expr.mkAppRangeAux.eq_def`
* `Lean.Substring.beq_refl`
* `Lean.Syntax.structEq_eq`
* `Lean.Level.hasParam_eq`
* `Lean.Level.hasMVar_eq`
* `Lean.Level.instLawfulBEqLevel`
* `Lean.Expr.hasLevelParam_eq`
* `Lean.Expr.looseBVarRange_eq`
* `Lean.Expr.replace_eq`
* `Lean.Expr.lowerLooseBVars_eq`
* `Lean.Expr.instantiate1_eq`
* `Lean.Expr.instantiate_eq`
* `Lean.Expr.instantiateRev_eq`
* `Lean.Expr.instantiateRange_eq`
* `Lean.Expr.instantiateRevRange_eq`
* `Lean.Expr.abstract_eq`
* `Lean.Expr.abstractRange_eq`
* `Lean.Expr.hasLooseBVar_eq`
* `Lean.Expr.eqv_eq`

## • Axioms about [ptrEq](Lean4Lean/PtrEq.lean)

See [PtrEq.lean](Lean4Lean/PtrEq.lean). Pointer equality does not behave like a
regular function, so we have to be careful with its use, but it is an important
part of the kernel. We only care about one property, which is that if two objects
are pointer-equal then they are propositionally equal, but while this is true for
`ptrEq` generic over all types, the function itself is unsafe so we can't assume it
outright. Even this form is questionable, but to mitigate possible issues with pointer identity of closures (function types), we specialize to `Expr` and `ConstantInfo`.

* `Lean4Lean.ptrEqExpr_eq`
* `Lean4Lean.ptrEqConstantInfo_eq`

## • Sorries related to inductive types

Currently inductive types are not modeled in the theory, so the parts of the kernel that deal with inductive types are sorried. (The "(sorry)" in these entries below mean
that these are not real axioms, they can be proved in the future but are converted to axioms for ease of tracking.)

* `Lean4Lean.VInductDecl.WF` (sorry)
* `Lean4Lean.VEnv.addInduct` (sorry)
* `Lean4Lean.VEnv.addInduct_WF` (sorry)

The type checker functions which manipulate inductive types are not proved for the same reason.

* `Lean4Lean.TypeChecker.Inner.isDefEqUnitLike.WF` (sorry)
* `Lean4Lean.TypeChecker.Inner.reduceRecursor.WF` (sorry)
* `Lean4Lean.TypeChecker.Inner.tryEtaStructCore.WF` (sorry)

## • Sorries related to [TrProj](Lean4Lean/Verify/Typing/Expr.lean)

Continuation of the above. Projections expand to a recursor application, so this also requires details of structures (which are a kind of inductive type). These axioms correspond essentially to the `proj` case of each main theorem about `TrExprS`.

* `Lean4Lean.TrProj` (sorry)
* `Lean4Lean.TrProj.defeqDFC` (sorry)
* `Lean4Lean.TrProj.instL` (sorry)
* `Lean4Lean.TrProj.instN` (sorry)
* `Lean4Lean.TrProj.uniq` (sorry)
* `Lean4Lean.TrProj.weak'` (sorry)
* `Lean4Lean.TrProj.weak'_inv` (sorry)
* `Lean4Lean.TrProj.wf` (sorry)

The typechecker functions which manipulate projections are not proved for the same reason.

* `Lean4Lean.TypeChecker.Inner.inferProj.WF` (sorry)
* `Lean4Lean.TypeChecker.Inner.reduceProj.WF` (sorry)

## • Sorries related to [unique typing](Lean4Lean/Theory/Typing/UniqueTyping.lean)

This is the main conjecture discussed in the paper.

* `Lean4Lean.VEnv.IsDefEq.uniq` (sorry)
* `Lean4Lean.VEnv.IsDefEqU.forallE_inv` (sorry)
* `Lean4Lean.VEnv.IsDefEqU.weakN_inv` (sorry)

## • Sorries related to the new [`isEquiv'`](Lean4Lean/Level.lean)

This relates to an experiment to replace the `isEquiv` function with a version `isEquiv'`
which should be a complete normalization algorithm for level expressions. It is
significantly more complex, however, and it hasn't been proved correct yet.
It would be nice to prove it complete too, although in general completeness is
not a goal of the typechecker.

* `Lean.Level.isEquiv'_wf` (sorry)
