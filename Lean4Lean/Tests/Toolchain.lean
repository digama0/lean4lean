import Lean4Lean.Replay

namespace Lean4Lean.Tests.Toolchain

open Lean Lean4Lean TypeChecker TypeChecker.Inner

theorem theoremDelta : True := trivial

theorem proofOnlyDependency : True := trivial
theorem dependencyOnlyInProof : True := proofOnlyDependency

theorem stringProof (_ : String) : True := trivial
theorem stringOnlyInProof : True := stringProof "audit"

run_meta
  let env ← getEnv
  let kenv := env.toKernelEnv

  let some thmInfo := kenv.find? ``theoremDelta
    | throwError "theorem-delta test declaration is missing"
  -- lean4#12973 flipped `ConstantInfo.hasValue` for theorems, but left
  -- `constant_info::has_value()` -- the predicate `type_checker::is_delta` consults --
  -- alone, so the kernel still delta-unfolds theorems. `isDelta` must follow the kernel,
  -- not `hasValue`.
  unless !thmInfo.hasValue do
    throwError "expected `ConstantInfo.hasValue` to exclude theorems as of lean4#12973"
  unless thmInfo.deltaValue?.isSome do
    throwError "theorem values must remain delta-reducible"
  unless (isDelta kenv (.const ``theoremDelta [])).isSome do
    throwError "isDelta rejected a theorem, diverging from `type_checker::is_delta`"

  unless (isDelta kenv (.const ``Nat.add [.zero])).isNone do
    throwError "isDelta accepted an invalid universe arity"
  unless (isDelta kenv (.const ``Nat.add [])).isSome do
    throwError "isDelta rejected a valid definition"

  let some depInfo := env.find? ``dependencyOnlyInProof
    | throwError "proof-dependency test declaration is missing"
  unless depInfo.getUsedConstants.contains ``proofOnlyDependency do
    throwError "theorem proof dependency was omitted during replay analysis"

  let some strInfo := env.find? ``stringOnlyInProof
    | throwError "string-literal test declaration is missing"
  unless strInfo.hasStrLit do
    throwError "string literal in theorem proof was omitted during replay analysis"

end Lean4Lean.Tests.Toolchain
