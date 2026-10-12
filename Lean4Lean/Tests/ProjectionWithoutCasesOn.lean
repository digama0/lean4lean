import Lean4Lean.Environment

/-!
Primitive projection inference depends only on the installed inductive and
constructor metadata.  The kernel-facing installer does not create the later
elaborator `.casesOn` auxiliary, and projection checking must not require it.
-/

namespace Lean4Lean.Tests.ProjectionWithoutCasesOn

open Lean

private def structureDecl : Declaration :=
  .inductDecl [] 0 [{
    name := `L4LProjectionFresh
    type := .sort 1
    ctors := [{
      name := `L4LProjectionFresh.mk
      type := .forallE `value (.const ``Nat [])
        (.const `L4LProjectionFresh []) .default
    }]
  }] false

private def projectionDecl : Declaration :=
  .defnDecl {
    name := `L4LProjectionFresh.value
    levelParams := []
    type := .forallE `self (.const `L4LProjectionFresh [])
      (.const ``Nat []) .default
    value := .lam `self (.const `L4LProjectionFresh [])
      (.proj `L4LProjectionFresh 0 (.bvar 0)) .default
    hints := .abbrev
    safety := .safe
  }

run_meta do
  let source := (← getEnv).toKernelEnv
  let .ok installed := Lean4Lean.addDecl source structureDecl
    | throwError "fresh projection structure was rejected"
  if installed.find? (mkCasesOnName `L4LProjectionFresh) |>.isSome then
    throwError "inductive installation unexpectedly added `.casesOn`"
  let .ok projected := Lean4Lean.addDecl installed projectionDecl
    | throwError "projection without `.casesOn` was rejected"
  unless projected.contains `L4LProjectionFresh.value do
    throwError "accepted projection declaration was not installed"

end Lean4Lean.Tests.ProjectionWithoutCasesOn
