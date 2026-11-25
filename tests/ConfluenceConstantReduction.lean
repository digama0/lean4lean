import Lean4Lean.Theory.Typing.ChurchRosser
import Lean.Util.CollectAxioms

namespace ConfluenceConstantReductionTest
open Lean hiding Environment Exception
open Lean4Lean

example (expression : VExpr)
    (leftWF : ∀ level ∈ leftLevels, level.WF universes)
    (rightWF : ∀ level ∈ rightLevels, level.WF universes)
    (levelsEqual : List.Forall₂ (· ≈ ·) leftLevels rightLevels) :
    VEnv.EqUpToLevels universes (expression.instL leftLevels) (expression.instL rightLevels) :=
  .instL_of_levels expression leftWF rightWF levelsEqual

example (level : VLevel) (levelWF : level.WF universes) :
    VEnv.EqUpToLevels universes
      ((VExpr.lam (.sort (.param 0)) (.bvar 0)).instL [.max .zero level])
      ((VExpr.lam (.sort (.param 0)) (.bvar 0)).instL [level]) := by
  apply VEnv.EqUpToLevels.instL_of_levels
  · simpa [VLevel.WF] using levelWF
  · simpa using levelWF
  · exact .cons (by simp [VLevel.equiv_def, VLevel.eval]) .nil

example (result : (Pattern.const name).RHS)
    (leftWF : ∀ level ∈ leftLevels, level.WF universes)
    (rightWF : ∀ level ∈ rightLevels, level.WF universes)
    (levelsEqual : List.Forall₂ (· ≈ ·) leftLevels rightLevels) :
    VEnv.EqUpToLevels universes (result.apply leftLevels leftValues)
      (result.apply rightLevels rightValues) :=
  result.eqUpToLevels_const leftWF rightWF levelsEqual

section
variable [VEnv.Params]
open VEnv.Params

example (localsWF : OnCtx locals (env.IsType univs))
    (typed : env.HasType univs locals expression type)
    (equal : VEnv.EqUpToLevels univs expression changed) :
    VEnv.NormalEq locals expression changed :=
  .of_eqUpToLevels localsWF typed equal

example (localsWF : OnCtx locals (env.IsType univs))
    (registered : env.constants name = some constant)
    (leftWF : ∀ level ∈ leftLevels, level.WF univs)
    (rightWF : ∀ level ∈ rightLevels, level.WF univs)
    (arity : leftLevels.length = constant.uvars)
    (levelsEqual : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (reduction : VEnv.ParRed locals (.const name rightLevels) reduced) :
    ∃ leftReduced, VEnv.ParRedS locals (.const name leftLevels) leftReduced ∧
      VEnv.NormalEq locals leftReduced reduced :=
  VEnv.NormalEq.parRed_constDF localsWF registered leftWF rightWF arity levelsEqual reduction

example (localsWF : OnCtx locals (env.IsType univs))
    (registered : env.constants name = some constant)
    (leftWF : ∀ level ∈ leftLevels, level.WF univs)
    (rightWF : ∀ level ∈ rightLevels, level.WF univs)
    (arity : leftLevels.length = constant.uvars)
    (levelsEqual : List.Forall₂ (· ≈ ·) leftLevels rightLevels) :
    ∃ leftReduced, VEnv.ParRedS locals (.const name leftLevels) leftReduced ∧
      VEnv.NormalEq locals leftReduced (.const name rightLevels) :=
  VEnv.NormalEq.parRed_constDF localsWF registered leftWF rightWF arity levelsEqual .const

example (localsWF : OnCtx locals (env.IsType univs))
    (registered : env.constants name = some constant)
    (leftWF : ∀ level ∈ leftLevels, level.WF univs)
    (rightWF : ∀ level ∈ rightLevels, level.WF univs)
    (arity : leftLevels.length = constant.uvars)
    (levelsEqual : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (body : VExpr) (closed : body.Closed)
    (rule : Pat (.const name) (.fixed body closed, .true)) :
    ∃ leftReduced, VEnv.ParRedS locals (.const name leftLevels) leftReduced ∧
      VEnv.NormalEq locals leftReduced (body.instL rightLevels) := by
  have reduction : VEnv.ParRed locals (.const name rightLevels) (body.instL rightLevels) :=
    .extra (m2' := fun path : (Pattern.const name).Path => nomatch path)
      rule .const trivial (fun path => nomatch path)
  exact VEnv.NormalEq.parRed_constDF localsWF registered leftWF rightWF arity levelsEqual reduction

example (localsWF : OnCtx locals (env.IsType univs))
    (leftWF : ∀ level ∈ leftLevels, level.WF univs)
    (rightWF : ∀ level ∈ rightLevels, level.WF univs)
    (levelsEqual : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (leftBody rightBody : VExpr) (leftClosed : leftBody.Closed) (rightClosed : rightBody.Closed)
    (equal : env.IsDefEqU univs locals (leftBody.instL leftLevels) (rightBody.instL leftLevels)) :
    env.IsDefEqU univs locals (leftBody.instL rightLevels) (rightBody.instL rightLevels) := by
  let check : (Pattern.const `checkedDefinition).Check :=
    .defeq (.fixed leftBody leftClosed) (.fixed rightBody rightClosed) .true
  let values : (Pattern.const `checkedDefinition).Path → VExpr := nofun
  have checked : check.OK (env.IsDefEqU univs locals) leftLevels values := ⟨equal, trivial⟩
  have transported := checked.const_levels localsWF check (rightValues := values)
    leftWF rightWF levelsEqual
  exact transported.1

end

run_meta
  let owned := #[``VEnv.EqUpToLevels.instL_of_levels, ``VEnv.NormalEq.of_eqUpToLevels,
    ``Pattern.RHS.eqUpToLevels_const, ``Pattern.Check.OK.const_levels,
    ``VEnv.NormalEq.parRed_constDF]
  let pureTheorems := #[``VEnv.EqUpToLevels.instL_of_levels, ``Pattern.RHS.eqUpToLevels_const]
  let baseline ← collectAxioms ``VEnv.NormalEq.defeq
  for name in owned do
    let information ← getConstInfo name
    if information matches .axiomInfo _ then throwError "constant confluence axiom: {name}"
    let some proof := information.value? (allowOpaque := true) |
      throwError "constant confluence proof absent: {name}"
    if proof.hasSorry then throwError "constant confluence direct admission: {name}"
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless baseline.contains dependency do
        throwError "unexpected constant confluence dependency: {dependency} in {name}"
      if pureTheorems.contains name then
        unless #[``propext, ``Quot.sound].contains dependency do
          throwError "structural universe transport inherited a metatheory admission: {dependency}"
    logInfo m!"{name}: {repr dependencies}"
  let environment ← getEnv
  let forbidden := #[``VEnv.NormalEq.parRed, ``VEnv.NormalEq.parRedS,
    ``VEnv.ParRedS.church_rosser, ``VEnv.IsDefEq.church_rosser]
  let mut pending := #[``VEnv.NormalEq.parRed_constDF]
  let mut visited : NameSet := {}
  for _ in [:100000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    if forbidden.contains name then throwError "circular constant confluence dependency: {name}"
    if let some information := environment.find? name then
      pending := pending ++ information.type.getUsedConstants
      if let some proof := information.value? (allowOpaque := true) then
        pending := pending ++ proof.getUsedConstants
  unless pending.isEmpty do throwError "constant confluence dependency traversal exceeded its bound"
  logInfo m!"five owned proofs have no direct admissions or axioms; two structural transports exclude inherited metatheory admissions; the constant extra-reduction branch is independent of the remaining application/extra confluence admission; existing semantic baseline: {repr baseline}"

end ConfluenceConstantReductionTest
