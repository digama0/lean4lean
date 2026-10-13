import Lean4Lean.Verify.TypeChecker
import Lean.Util.CollectAxioms

namespace Lean4Lean.Tests.InductiveRecursorRejection

open Lean Lean4Lean Lean4Lean.TypeChecker Lean4Lean.TypeChecker.Inner

example {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (inductiveReduceRec context.env expression Inner.whnf
        inferType isDefEq).WF context state
      (fun outcome _ => outcome = none) :=
  inductiveReduceRec.none_of_translation translated

example {context : VContext} {state : VState}
    (notInitialized : context.env.quotInit = false)
    (translated : context.TrExprS expression semantic) :
    (reduceRecursor expression).WF context state
      (fun outcome _ => outcome = none) :=
  reduceRecursor.none_of_translation notInitialized translated

run_meta
  let baseline ← collectAxioms ``Methods.withFuel.WF
  for theoremName in [``Inner.inductiveReduceRec.none_of_translation,
      ``Inner.reduceRecursor.none_of_translation] do
    let information ← getConstInfo theoremName
    if information matches .axiomInfo _ then
      throwError "inductive recursor rejection theorem is an axiom: {theoremName}"
    let dependencies ← collectAxioms theoremName
    for dependency in dependencies do
      unless baseline.contains dependency do
        throwError "unexpected inductive recursor rejection dependency: {dependency}"
  logInfo m!"inductive recursor rejection proofs compile without a direct admission; inherited semantic/native baseline remains explicit: {repr baseline}"

end Lean4Lean.Tests.InductiveRecursorRejection
