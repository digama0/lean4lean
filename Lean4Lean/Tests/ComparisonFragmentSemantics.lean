import Lean4Lean.Verify.TypeChecker
import Lean.Util.CollectAxioms

namespace Lean4Lean.Tests.ComparisonFragmentSemantics
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.TypeChecker

example {context : VContext} {state : VState}
    (translated : context.TrExprS second semantic) :
    (Inner.tryEtaStructCore first second).WF context state
      (fun equal _ => equal = false) :=
  Inner.tryEtaStructCore.false_of_translation translated

example {context : VContext} {state : VState}
    (leftTranslation : context.TrExprS first firstSemantic)
    (rightTranslation : context.TrExprS second secondSemantic) :
    (Inner.tryEtaStructCore first second).WF context state
      (fun equal _ => equal = true → context.IsDefEqU firstSemantic secondSemantic) :=
  Inner.tryEtaStructCore.WF leftTranslation rightTranslation

example {context : VContext} {state : VState}
    (translated : context.TrExprS first semantic) :
    (Inner.isDefEqUnitLike first second).WF context state
      (fun equal _ => equal = false) :=
  Inner.isDefEqUnitLike.false_of_translation translated

example {context : VContext} {state : VState}
    (leftTranslation : context.TrExprS first firstSemantic)
    (rightTranslation : context.TrExprS second secondSemantic) :
    (Inner.isDefEqUnitLike first second).WF context state
      (fun equal _ => equal = true → context.IsDefEqU firstSemantic secondSemantic) :=
  Inner.isDefEqUnitLike.WF leftTranslation rightTranslation

run_meta
  let baseline ← collectAxioms ``Methods.withFuel.WF
  for theoremName in #[``Inner.tryEtaStructCore.false_of_translation,
      ``Inner.tryEtaStructCore.WF, ``Inner.isDefEqUnitLike.false_of_translation,
      ``Inner.isDefEqUnitLike.WF] do
    let information ← getConstInfo theoremName
    if information matches .axiomInfo _ then
      throwError "comparison theorem is an axiom: {theoremName}"
    let dependencies ← collectAxioms theoremName
    for dependency in dependencies do
      unless baseline.contains dependency do
        throwError "unexpected comparison dependency: {dependency} in {theoremName}"
  logInfo m!"structure-eta and unit-like comparison rejection contracts compile without direct admissions; inherited semantic/native baseline remains explicit: {repr baseline}"

end Lean4Lean.Tests.ComparisonFragmentSemantics
