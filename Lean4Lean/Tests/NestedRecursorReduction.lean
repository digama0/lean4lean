import Lean4Lean.Environment

/-! Restored recursors eliminate specialized containers. Their parameters are
not the parameters of the container's constructor. Exercise reduction itself,
including reapplication of arguments after the major premise. -/

namespace Lean4Lean.Tests.NestedRecursorReduction
open Lean

private def checkRule (recName ctorName : Name) (parameters fields : Array Expr) : MetaM Unit := do
  let .recInfo rec ← getConstInfo recName | throwError "expected recursor {recName}"
  let .ctorInfo ctor ← getConstInfo ctorName | throwError "expected constructor {ctorName}"
  unless ctor.numParams == parameters.size && ctor.numFields == fields.size do
    throwError "test arguments disagree with {ctorName}'s telescope"
  unless rec.numParams != ctor.numParams do
    throwError "{recName} no longer exercises specialized constructor parameters"
  let some rule := rec.rules.find? (·.ctor == ctorName)
    | throwError "{recName} has no rule for {ctorName}"
  unless rule.nfields == fields.size do
    throwError "{recName}'s field count disagrees with {ctorName}"
  let levels := rec.levelParams.map fun _ => Level.zero
  let ctorLevels := ctor.levelParams.map fun _ => Level.zero
  let major := mkAppN (.const ctorName ctorLevels) (parameters ++ fields)
  let leadingArgs := Array.ofFn (n := rec.getFirstIndexIdx) fun i => Expr.bvar i
  let indices := Array.ofFn (n := rec.numIndices) fun i => Expr.bvar (leadingArgs.size + i)
  -- This is a test of the pure spine operation; the leadingArgs variables stand for
  -- the parameters, motives, and minors, without needing to choose particular motives.
  let args := leadingArgs ++ indices ++ #[major]
  let expected := mkAppN
    (mkAppN (rule.rhs.instantiateLevelParams rec.levelParams levels) leadingArgs) fields
  unless inductiveReduceRecTail rec levels args major == some expected do
    throwError "{recName} failed to reduce {ctorName} with specialized parameters"
  let extra := Expr.bvar (leadingArgs.size + indices.size)
  unless inductiveReduceRecTail rec levels (args.push extra) major ==
      some (.app expected extra) do
    throwError "{recName} failed to reapply the argument after its major premise"
  if rule.nfields > 0 then
    unless (inductiveReduceRecTail rec levels args (.const ctorName ctorLevels)).isNone do
      throwError "{recName} accepted a major premise missing its fields"
  unless (inductiveReduceRecTail rec (Level.zero :: levels) args major).isNone do
    throwError "{recName} accepted the wrong number of universe arguments"

run_meta do
  let syntaxType := mkConst ``Lean.Syntax
  let nil := mkApp (mkConst ``List.nil [.zero]) syntaxType
  let item := mkConst ``Lean.Syntax.missing
  checkRule ``Lean.Syntax.rec_1 ``Array.mk #[syntaxType] #[nil]
  checkRule ``Lean.Syntax.rec_2 ``List.nil #[syntaxType] #[]
  checkRule ``Lean.Syntax.rec_2 ``List.cons #[syntaxType] #[item, nil]

end Lean4Lean.Tests.NestedRecursorReduction
