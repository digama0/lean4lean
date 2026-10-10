import Lean4Lean.Inductive.Add

/-!
Nested lowering does not install the source constructor type verbatim.

Two nested occurrences whose parameters are `Expr.eqv`-equal (equal up to
binder names and binder annotations) share one auxiliary family: the second is
a cache hit in `findCachedAux?`, and restoration rebuilds it from the
parameters recorded for the first. Below, the source constructor

  `CE.T.mk : List ((a : Nat) → CE.T) → List ({b : Nat} → CE.T) → CE.T`

is installed with type

  `List ((a : Nat) → CE.T) → List ((a : Nat) → CE.T) → CE.T`.

The two types are `==` (`Expr.eqv`) but not `Expr.equal`. See
`Lean4Lean.Verify.Inductive.Nested.Restoration.InstalledConstructorTypes`.
-/

namespace Lean4Lean.Tests.NestedConstructorRoundTrip

open Lean

run_meta do
  let env := (← getEnv).toKernelEnv
  let T := mkConst `CE.T
  let nat := mkConst ``Nat
  let list (x : Expr) := mkApp (mkConst ``List [0]) x
  let first := Expr.forallE `a nat T .default
  let second := Expr.forallE `b nat T .implicit
  let sourceType :=
    Expr.forallE `x (list first) (.forallE `y (list second) T .default) .default
  let types : List InductiveType :=
    [{ name := `CE.T, type := .sort 1,
       ctors := [{ name := `CE.T.mk, type := sourceType }] }]
  match Lean4Lean.Environment.addInductive env [] 0 types false false with
  | .error e => throwError "rejected: {e.toMessageData {}}"
  | .ok env' =>
    let some (.ctorInfo info) := env'.find? `CE.T.mk
      | throwError "constructor not installed"
    unless info.type == sourceType do
      throwError "installed type is not Expr.eqv to the source type"
    if info.type.equal sourceType then
      throwError "installed type is literally the source type"
    let expected :=
      Expr.forallE `x (list first) (.forallE `y (list first) T .default) .default
    unless info.type.equal expected do
      throwError "unexpected installed type {info.type}"

end Lean4Lean.Tests.NestedConstructorRoundTrip
