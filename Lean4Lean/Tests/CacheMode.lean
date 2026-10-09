import Lean4Lean.Verify.Replay

/-! # The cache-mode plumbing in the scoped mode is the identity

The checker's cache mode (`Lean4Lean.CacheMode`) is a field of `FuelConfig` whose default is
`.scoped`. This file checks that

* the default configuration is the scoped one, so every statement about `fuel := {}` is a
  statement about the scoped mode;
* leaving a binder in the scoped mode is `State.leaveScope`, the restoring exit;
* a configuration file cannot select the global mode (it needs a `GlobalCacheLicense`, a proof);
* replays with the default configuration and with the explicitly scoped one give the same
  results on oracle declarations: the same number of added declarations, the same checked
  constants, and the same constant at every name.

No license is constructed here: none is known to exist, and the global mode is not exercised. -/

namespace Lean4Lean.Tests.CacheMode
open Lean Lean4Lean Lean4Lean.Replay

example : ({} : FuelConfig).cacheMode = .scoped := rfl
example : ({} : FuelConfig) = { cacheMode := .scoped } := rfl
example : ({} : FuelConfig).cacheMode.isGlobal = false := rfl
example (saved s : TypeChecker.State) :
    TypeChecker.State.exitScope .scoped saved s = saved.leaveScope s := rfl

/--
info: scoped mode from JSON: true
---
info: global mode from JSON rejected: true
-/
#guard_msgs in
run_meta do
  let j := toJson ({} : FuelConfig)
  let back : Except String FuelConfig := fromJson? j
  logInfo s!"scoped mode from JSON: {match back with
    | .ok c => !c.cacheMode.isGlobal | .error _ => false}"
  let bad := j.setObjVal! "cacheMode" (toJson "global")
  let r : Except String FuelConfig := fromJson? bad
  logInfo s!"global mode from JSON rejected: {r matches .error _}"

/-- Oracle declarations: their dependency cones cover inductive types with recursors, structures,
nested and mutual declarations, well-founded and structural definitions, and the quotient. -/
def oracleTargets : List Name :=
  [``List.map, ``Nat.add_comm, ``Array.push, ``String.append, ``Quot.lift, ``Lean.Syntax,
    ``Option.bind, ``Prod.mk, ``Decidable.decide]

def errorText : ReplayError → String
  | .kernel n _ => s!"kernel error at {n}"
  | .msg s => s

/--
info: the scoped mode agrees with the default on 9 oracle cones
-/
#guard_msgs in
run_meta do
  let src : Std.HashMap Name ConstantInfo :=
    (← getEnv).constants.fold (init := {}) fun m n ci => m.insert n ci
  let mut agreeing : Nat := 0
  for d in oracleTargets do
    let r₁ := replayFresh src .anonymous {} (some d)
    let r₂ := replayFresh src .anonymous { cacheMode := .scoped } (some d)
    match r₁, r₂ with
    | .ok a, .ok b =>
      unless a.numAdded == b.numAdded && a.checked == b.checked do
        throwError "{d}: the two replays checked different declarations"
      for n in a.checked do
        unless a.env.find? n == b.env.find? n do
          throwError "{d}: the two replays disagree at {n}"
      agreeing := agreeing + 1
    | .error e₁, .error e₂ =>
      throwError "{d}: both replays failed: {errorText e₁} / {errorText e₂}"
    | _, _ => throwError "{d}: one replay failed and the other succeeded"
  logInfo s!"the scoped mode agrees with the default on {agreeing} oracle cones"

end Lean4Lean.Tests.CacheMode
