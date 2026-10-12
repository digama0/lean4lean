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
  match (Primitive.checkDef partialNatAdd).run env.toKernelEnv
      (lparams := partialNatAdd.levelParams) with
  | .error _ => pure ()
  | .ok true => throwError "a partial definition was accepted as a primitive"
  | .ok false => throwError "a partial definition was reported as a non-primitive"

/- The primitive recognizer accepts the prelude's definitions of the primitives whose checks go
through a `reflectNatNat` condition (`Nat.div`, `Nat.mod`, `Nat.land`, ...) or a well-founded
unfolding (`Nat.gcd`, `Nat.bitwise`). The condition's pieces and the fixpoint functional are read
only under binders; this exercises those readings outside a full replay. -/
run_meta
  let env ← Lean.getEnv
  for n in [``Nat.div, ``Nat.mod, ``Nat.gcd, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.beq,
      ``Nat.ble] do
    let some (.defnInfo v) := env.toKernelEnv.find? n
      | throwError "{n} is not a definition"
    match (Primitive.checkDef v).run env.toKernelEnv (lparams := v.levelParams) with
    | .ok true => pure ()
    | .ok false => throwError "{n} was reported as a non-primitive"
    | .error e => throwError "{n} was rejected as a primitive: {e.toMessageData .empty}"
  -- and it is not vacuous: `Nat.gcd` and `Nat.div` with `Nat.mod`'s value are rejected
  let some (.defnInfo natMod) := env.toKernelEnv.find? ``Nat.mod
    | throwError "Nat.mod is not a definition"
  for n in [``Nat.gcd, ``Nat.div] do
    let some (.defnInfo v) := env.toKernelEnv.find? n
      | throwError "{n} is not a definition"
    let v := { v with value := natMod.value }
    match (Primitive.checkDef v).run env.toKernelEnv (lparams := v.levelParams) with
    | .error _ => pure ()
    | .ok _ => throwError "{n} with the value of Nat.mod was accepted"

end Lean4Lean.Tests.Environment
