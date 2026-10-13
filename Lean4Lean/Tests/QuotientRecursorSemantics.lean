import Lean4Lean.Verify.TypeChecker
import Lean.Util.CollectAxioms

namespace Lean4Lean.Tests.QuotientRecursorSemantics
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.TypeChecker

example {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (quotReduceRec expression Inner.whnf).WF context state
      (fun outcome _ => ∀ reduced, outcome = some reduced →
        context.FVarsBelow expression reduced) :=
  Inner.quotReduceRec.fvarsBelow translated

run_meta
  let baseline ← collectAxioms ``Methods.withFuel.WF
  let theoremName := ``Inner.quotReduceRec.fvarsBelow
  let information ← getConstInfo theoremName
  if information matches .axiomInfo _ then
    throwError "quotient recursion theorem is an axiom"
  let dependencies ← collectAxioms theoremName
  for dependency in dependencies do
    unless baseline.contains dependency do
      throwError "unexpected quotient recursion dependency: {dependency}"
  logInfo m!"quotient recursion free-variable preservation compiles without a direct admission; inherited semantic/native baseline remains explicit: {repr baseline}"

end Lean4Lean.Tests.QuotientRecursorSemantics
