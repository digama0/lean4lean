import Lean4Lean.Environment

/-! K reduction must use a proposition's normalized header. The executable
installer retains the source expression `id Prop`, which is not a literal
sort. The equality below requires K reduction on a variable major premise. -/

namespace Lean4Lean.Tests.KNormalization
open Lean

private def header : Expr := mkApp2 (mkConst ``id [2]) (.sort 1) (.sort 0)
private def family : Expr := mkConst `L4LAliasProp

private def declaration : Declaration := .inductDecl [] 0 [{
  name := `L4LAliasProp
  type := header
  ctors := [{ name := `L4LAliasProp.mk, type := family }]
}] false

private def computation : Declaration :=
  let nat := mkConst ``Nat
  let zero := mkConst ``Nat.zero
  let motive := .lam `self family nat .default
  let result := mkApp3 (mkConst `L4LAliasProp.rec [1]) motive zero (.bvar 0)
  .thmDecl {
    name := `L4LAliasProp.compute
    levelParams := []
    type := .forallE `p family (mkApp3 (mkConst ``Eq [1]) nat result zero) .default
    value := .lam `p family (mkApp2 (mkConst ``Eq.refl [1]) nat zero) .default
  }

run_meta do
  let source := (← getEnv).toKernelEnv
  let .ok installed := Lean4Lean.addDecl source declaration
    | throwError "inductive with reducible proposition header was rejected"
  let some (.inductInfo info) := installed.find? `L4LAliasProp
    | throwError "missing inductive header"
  unless info.type == header do
    throwError "test requires the original, unreduced header to be retained"
  let some (.recInfo rec) := installed.find? `L4LAliasProp.rec
    | throwError "missing recursor"
  unless rec.k do
    throwError "the singleton proposition's recursor must support K"
  match Lean4Lean.addDecl installed computation with
  | .ok _ => pure ()
  | .error e =>
    throwError "K reduction with reducible header failed: {← (e.toMessageData {}).toString}"

end Lean4Lean.Tests.KNormalization
