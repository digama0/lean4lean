import Lean4Lean.Theory.Typing.QuotPattern
import Lean4Lean.Theory.Typing.ChurchRosser
import Lean.Util.CollectAxioms

namespace QuotientPatternEquationTest
open Lean hiding Environment Exception
open Lean4Lean

example (pattern : Pattern) {values : pattern.Path → VExpr} :
    ¬pattern.Matches (quotDefEq.lhs.instL levels) matchedLevels values :=
  quotDefEq.not_matches pattern

example : quotLiftPattern = (SimplePattern.iota ``Quot.lift 5 ``Quot.mk 3).toPattern :=
  quotLiftPattern.simple

example (root : ∃ pattern result levels values, registered pattern result ∧
    pattern.Matches left levels values ∧ result.2.OK (equal locals) levels values ∧
    right = result.1.apply levels values) :
    Pattern.Equation registered equal locals left right :=
  .of_root root

example (root : ∃ pattern result levels values, registered pattern result ∧
    pattern.Matches left levels values ∧ result.2.OK (equal (domain :: locals)) levels values ∧
    right = result.1.apply levels values) :
    Pattern.Equation registered equal locals (.lam domain left) (.lam domain right) :=
  .lam (.of_root root)

example (registered : patterns quotLiftPattern (quotLiftPatternResult, quotLiftPatternCheck)) :
    Pattern.Equation patterns (VEnv.IsDefEqU environment universes) locals
      (quotDefEq.lhs.instL levels) (quotDefEq.rhs.instL levels) :=
  quotDefEq.patternEquation registered

example (registered : patterns quotLiftPattern (quotLiftPatternResult, quotLiftPatternCheck)) :
    Pattern.Equation patterns (VEnv.IsDefEqU environment universes) locals
      (quotDefEq.lhs.instL []) (quotDefEq.rhs.instL []) :=
  quotDefEq.patternEquation registered

example (registered : patterns quotLiftPattern (quotLiftPatternResult, quotLiftPatternCheck)) :
    Pattern.Equation patterns (VEnv.IsDefEqU environment universes) locals
      (quotDefEq.lhs.instL [.max .zero (.param 0), .succ (.param 1)])
      (quotDefEq.rhs.instL [.max .zero (.param 0), .succ (.param 1)]) :=
  quotDefEq.patternEquation registered

section
variable [VEnv.Params]
open VEnv.Params

example (equation : Pattern.Equation Pat (VEnv.IsDefEqU env univs) locals left right) :
    VEnv.ParRed locals left right :=
  equation.parRed

example (registered : Pat quotLiftPattern (quotLiftPatternResult, quotLiftPatternCheck)) :
    VEnv.ParRed locals (quotDefEq.lhs.instL levels) (quotDefEq.rhs.instL levels) :=
  (quotDefEq.patternEquation (environment := env) (universes := univs) registered).parRed

example (registered : env.defeqs quotDefEq)
    (levelsWF : ∀ level ∈ levels, level.WF univs)
    (arity : levels.length = quotDefEq.uvars) :
    Pattern.Equation Pat (VEnv.IsDefEqU env univs) locals
      (quotDefEq.lhs.instL levels) (quotDefEq.rhs.instL levels) :=
  extra_pat registered levelsWF arity

end

run_meta
  let pureTheorems := #[``Pattern.Matches.not_lam, ``Pattern.Equation.of_root,
    ``quotLiftPattern.simple, ``quotDefEq.not_matches, ``quotDefEq.patternEquation]
  for name in pureTheorems do
    let information ← getConstInfo name
    if information matches .axiomInfo _ then throwError "quotient equation axiom: {name}"
    let some proof := information.value? (allowOpaque := true) |
      throwError "quotient equation proof absent: {name}"
    if proof.hasSorry then throwError "quotient equation direct admission: {name}"
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Quot.sound].contains dependency do
        throwError "quotient equation inherited admission/interface: {dependency} in {name}"
    logInfo m!"{name}: {repr dependencies}"
  let bridge := ``Pattern.Equation.parRed
  let information ← getConstInfo bridge
  if information matches .axiomInfo _ then throwError "equation reduction bridge is an axiom"
  let some proof := information.value? (allowOpaque := true) |
    throwError "equation reduction bridge proof absent"
  if proof.hasSorry then throwError "equation reduction bridge has a direct admission"
  let baseline ← collectAxioms ``VEnv.NormalEq.defeq
  let dependencies ← collectAxioms bridge
  for dependency in dependencies do
    unless baseline.contains dependency do throwError "unexpected equation reduction dependency: {dependency}"
  let forbidden := #[``VEnv.NormalEq.parRed, ``VEnv.NormalEq.parRedS,
    ``VEnv.IsDefEq.church_rosser]
  let environment ← getEnv
  let mut pending := #[bridge]
  let mut visited : NameSet := {}
  for _ in [:100000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "equation reduction uses admitted confluence: {name}"
    if let some information := environment.find? name then
      pending := pending ++ information.type.getUsedConstants
      if let some value := information.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants
  unless pending.isEmpty do throwError "equation reduction dependency traversal exceeded its bound"
  logInfo m!"the actual six-binder quotient equation has an admission-free guarded pattern certificate at arbitrary level instances; old root-pattern certificates remain valid; its direct parallel-reduction bridge avoids admitted confluence and retains only the existing Params/model baseline {repr dependencies}; no concrete quotient Params instance or full confluence theorem is claimed"

end QuotientPatternEquationTest
