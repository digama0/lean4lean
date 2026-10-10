import Lean4Lean.Environment

/-! The kernel-generated recursor is fixed before universe specialization. A typed
projection can become a large elimination after specialization even when that
recursor only eliminates into Prop. Desugaring projections therefore needs admissible
abstract case eliminator instances, not just the kernel-generated `.rec`. -/

namespace Lean4Lean.Tests.ProjectionSpecialization
open Lean

private def boxDecl : Declaration :=
  let u := Level.param `u
  .inductDecl [`u] 1 [{
    name := `L4LSortBox
    type := .forallE `α (.sort u) (.sort u) .default
    ctors := [{
      name := `L4LSortBox.mk
      type := .forallE `α (.sort u)
        (.forallE `value (.bvar 0)
          (.app (.const `L4LSortBox [u]) (.bvar 1)) .default) .default
    }]
  }] false

private def projectionDecl : Declaration :=
  let boxNat := mkApp (mkConst `L4LSortBox [1]) (mkConst ``Nat)
  .defnDecl {
    name := `L4LSortBox.specializedValue
    levelParams := []
    type := .forallE `self boxNat (mkConst ``Nat) .default
    value := .lam `self boxNat (.proj `L4LSortBox 0 (.bvar 0)) .default
    hints := .abbrev
    safety := .safe
  }

run_meta do
  let source := (← getEnv).toKernelEnv
  let .ok installed := Lean4Lean.addDecl source boxDecl
    | throwError "sort-polymorphic box was rejected"
  let some (.recInfo rec) := installed.find? `L4LSortBox.rec
    | throwError "sort-polymorphic box has no recursor"
  unless rec.levelParams == [`u] do
    throwError "test expects a recursor with no independent elimination universe"
  -- Inspect the motive's codomain, rather than merely counting universes.
  let .forallE _ _ (.forallE _ motive _ _) _ := rec.type
    | throwError "unexpected box recursor telescope"
  let .forallE _ _ (.sort .zero) _ := motive
    | throwError "test expects a recursor restricted to elimination into Prop"
  if installed.contains (mkCasesOnName `L4LSortBox) then
    throwError "inductive installation unexpectedly supplied casesOn"
  match Lean4Lean.addDecl installed projectionDecl with
  | .ok _ => pure ()
  | .error e =>
    throwError "large projection after specialization was rejected: {← (e.toMessageData {}).toString}"

end Lean4Lean.Tests.ProjectionSpecialization
