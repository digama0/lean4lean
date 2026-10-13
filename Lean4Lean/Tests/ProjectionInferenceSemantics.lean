import Lean4Lean.Verify.TypeChecker
import Lean.Util.CollectAxioms

namespace Lean4Lean.Tests.ProjectionInferenceSemantics
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.TypeChecker

example {context : VContext} {state : VState}
    (translated : context.TrExprS structureType semanticType) :
    (Inner.inferProj structureName index source structureType).WF context state
      (fun _ _ => False) :=
  Inner.inferProj.rejects translated

example {context : VContext} {state : VState}
    (sourceTranslation : context.TrExprS source sourceSemantic)
    (typeTranslation : context.TrExprS structureType typeSemantic)
    (sourceType : context.HasType sourceSemantic sourceTypeSemantic) :
    (Inner.inferProj structureName index source structureType).WF context state
      (fun result _ => ∃ projectedType,
        context.TrTyping (.proj structureName index source) result sourceSemantic projectedType) :=
  Inner.inferProj.WF (st := structureName) (i := index) (e := source)
    (ety := structureType) sourceTranslation typeTranslation sourceType

run_meta
  let baseline ← collectAxioms ``Lean4Lean.TypeChecker.Methods.withFuel.WF
  for theoremName in #[``Inner.inferProj.rejects, ``Inner.inferProj.WF] do
    let information ← getConstInfo theoremName
    if information matches .axiomInfo _ then
      throwError "projection inference theorem is an axiom: {theoremName}"
    let dependencies ← collectAxioms theoremName
    for dependency in dependencies do
      unless baseline.contains dependency do
        throwError "unexpected projection inference dependency: {dependency} in {theoremName}"
  logInfo m!"projection inference rejection and WF contracts compile without direct admissions; inherited semantic/native baseline remains explicit: {repr baseline}"

end Lean4Lean.Tests.ProjectionInferenceSemantics
