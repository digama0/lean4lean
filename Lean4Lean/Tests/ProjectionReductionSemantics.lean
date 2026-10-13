import Lean4Lean.Verify.TypeChecker
import Lean.Util.CollectAxioms

namespace Lean4Lean.Tests.ProjectionReductionSemantics
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.TypeChecker

example {context : VContext} {state : VState}
    (translated : context.TrExprS source semantic) :
    (Inner.reduceProj index source cheapProj).WF context state
      (fun outcome _ => outcome = none) :=
  Inner.reduceProj.none_of_translation translated

example {context : VContext} {state : VState}
    (translated : context.TrExprS (.proj name index source) semantic) :
    (Inner.reduceProj index source cheapProj).WF context state
      (fun outcome _ => ∀ reduced, outcome = some reduced →
        context.FVarsBelow (.proj name index source) reduced ∧ context.TrExpr reduced semantic) :=
  Inner.reduceProj.WF translated

example {context : VContext} {state : VState}
    (translated : context.TrExprS source semantic) :
    (Inner.reduceProjCore index source).WF context state
      (fun outcome _ => outcome = none) :=
  Inner.reduceProjCore.none_of_translation translated

example {environment : Kernel.Environment} {environments : VEnvs}
    (wellFormed : environments.WF environment)
    (translated : (VContext.mk' wellFormed safety levels fuel).TrExprS source semantic) :
    (M.run environment safety {} levels fuel
      (RecM.run (Inner.reduceProj index source cheapProj))).WF (fun outcome => outcome = none) :=
  M.WF.run wellFormed (Inner.reduceProj.none_of_translation translated).run

run_meta
  let baseline ← collectAxioms ``Methods.withFuel.WF
  for theoremName in #[``Inner.reduceProjCore.none_of_translation,
      ``Inner.reduceProj.none_of_translation, ``Inner.reduceProj.WF] do
    let information ← getConstInfo theoremName
    if information matches .axiomInfo _ then
      throwError "projection theorem is an axiom: {theoremName}"
    let dependencies ← collectAxioms theoremName
    for dependency in dependencies do
      unless baseline.contains dependency do
        throwError "unexpected projection theorem dependency: {dependency} in {theoremName}"
  logInfo m!"projection rejection and soundness contracts compile without direct admissions; inherited semantic/native baseline remains explicit: {repr baseline}"

end Lean4Lean.Tests.ProjectionReductionSemantics
