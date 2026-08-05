import Lean4Lean.Environment

/-!
Front-end declaration checks that are not covered by `Lean4Lean.Tests.KernelHardening`.

The mutual-block level parameter and duplicate name checks live there, since v4.33.0-rc2
made the kernel reject both (lean4#14608).
-/

namespace Lean4Lean.Tests.Environment

open Lean

run_meta
  let env ← Lean.getEnv
  let some (.defnInfo natAdd) := env.toKernelEnv.find? ``Nat.add
    | throwError "Nat.add is not a definition"
  let partialNatAdd := { natAdd with safety := DefinitionSafety.partial }
  match (Lean4Lean.Environment.checkPrimitiveDef partialNatAdd).run env.toKernelEnv
      (lparams := partialNatAdd.levelParams) with
  | .ok false => pure ()
  | .ok true => throwError "a partial definition was accepted as a primitive"
  | .error _ => throwError "the partial primitive check failed unexpectedly"

end Lean4Lean.Tests.Environment
