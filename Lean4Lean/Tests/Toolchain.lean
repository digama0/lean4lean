import Main

namespace Lean4Lean.Tests.Toolchain

open Lean Lean4Lean TypeChecker TypeChecker.Inner

theorem theoremOpacity : True := trivial

theorem proofOnlyDependency : True := trivial
theorem dependencyOnlyInProof : True := proofOnlyDependency

def stringProof (_ : String) : True := trivial
theorem stringOnlyInProof : True := stringProof "audit"

run_meta
  let env ← getEnv
  let kenv := env.toKernelEnv

  let some thmInfo := kenv.find? ``theoremOpacity
    | throwError "theorem-opacity test declaration is missing"
  unless !thmInfo.hasValue do
    throwError "theorem values must not be delta-reducible"

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
