import Lean4Lean.TypeChecker
import Lean4Lean.Quot
import Lean4Lean.Inductive.Add
import Lean4Lean.Primitive

namespace Lean4Lean
open Lean hiding Environment Exception
open TypeChecker Kernel Environment

open private Lean.Kernel.Environment.add from Lean.Environment

def checkConstantValBody (env : Environment) (v : ConstantVal) : M Unit := do
  checkDuplicatedUnivParams v.levelParams
  checkNoMVarNoFVar env v.name v.type
  let sort ← checkType v.type
  _ ← ensureSort sort v.type

def checkConstantVal (env : Environment) (v : ConstantVal) (allowPrimitive := false) : M Unit := do
  checkName env v.name allowPrimitive
  checkConstantValBody env v

def checkDefinitionBody (env : Environment) (v : DefinitionVal) : M Unit := do
  checkConstantValBody env v.toConstantVal
  checkNoMVarNoFVar env v.name v.value
  let valType ← TypeChecker.checkType v.value
  if !(← isDefEq valType v.type) then
    throw <| .declTypeMismatch env (.defnDecl v) valType

def addAxiom (env : Environment) (v : AxiomVal) (check := true) (fuel : FuelConfig := {}) :
    Except Exception Environment := do
  if check then
    _ ← (checkConstantVal env v.toConstantVal).run env
      (safety := if v.isUnsafe then .unsafe else .safe) (lparams := v.levelParams) (fuel := fuel)
  return env.add (.axiomInfo v)

def addDefinition (env : Environment) (v : DefinitionVal)
    (check := true) (fuel : FuelConfig := {}) : Except Exception Environment := do
  if let .unsafe := v.safety then
    -- Meta definition can be recursive.
    -- So, we check the header, add, and then type check the body.
    if check then
      _ ← (checkConstantVal env v.toConstantVal).run env
        (safety := .unsafe) (lparams := v.levelParams) (fuel := fuel)
    -- Check a recursive unsafe body against an opaque self header.  Exposing
    -- the value here lets definitional equality unfold the declaration whose
    -- well-typedness is exactly what this check is trying to establish.
    let header : AxiomVal := { v.toConstantVal with isUnsafe := true }
    let env' := env.add (.axiomInfo header)
    if check then
      checkNoMVarNoFVar env' v.name v.value
      M.run env' (safety := .unsafe) (lctx := {}) (lparams := v.levelParams) (fuel := fuel) do
        let valType ← TypeChecker.checkType v.value
        if !(← isDefEq valType v.type) then
          throw <| .declTypeMismatch env' (.defnDecl v) valType
    return env.add (.defnInfo v)
  else
    if check then
      M.run env (safety := .safe) (lctx := {}) (lparams := v.levelParams) (fuel := fuel) do
        -- Establish the header and body typing facts before checking primitive
        -- equations.  The verification of `checkPrimitiveDef` needs these facts
        -- to justify its calls to `isDefEq`; the reserved-name check can safely
        -- wait until the primitive result is available.
        checkDefinitionBody env v
        let allowPrimitive ← checkPrimitiveDef v
        if allowPrimitive && v.safety != .safe then
          throw <| .other s!"primitive definition {v.name} must be safe"
        checkName env v.name allowPrimitive
    return env.add (.defnInfo v)

def addTheorem (env : Environment) (v : TheoremVal) (check := true) (fuel : FuelConfig := {}) :
    Except Exception Environment := do
  if check then
    -- TODO(Leo): we must add support for handling tasks here
    M.run env (safety := .safe) (lctx := {}) (lparams := v.levelParams) (fuel := fuel) do
      if !(← isProp v.type) then
        throw <| .thmTypeIsNotProp env v.name v.type
      checkConstantVal env v.toConstantVal
      let valType ← TypeChecker.checkType v.value
      if !(← isDefEq valType v.type) then
        throw <| .declTypeMismatch env (.thmDecl v) valType
  return env.add (.thmInfo v)

def addOpaque (env : Environment) (v : OpaqueVal) (check := true) (fuel : FuelConfig := {}) :
    Except Exception Environment := do
  if check then
    M.run env (safety := .safe) (lctx := {}) (lparams := v.levelParams) (fuel := fuel) do
      checkConstantVal env v.toConstantVal
      let valType ← TypeChecker.checkType v.value
      if !(← isDefEq valType v.type) then
        throw <| .declTypeMismatch env (.opaqueDecl v) valType
  return env.add (.opaqueInfo v)

def addMutual (env : Environment) (vs : List DefinitionVal)
    (check := true) (fuel : FuelConfig := {}) : Except Exception Environment := do
  let v₀ :: _ := vs | throw <| .other "invalid empty mutual definition"
  if let .safe := v₀.safety then
    throw <| .other "invalid mutual definition, declaration is not tagged as unsafe/partial"
  if check then
    M.run env (safety := v₀.safety) (lctx := {}) (lparams := v₀.levelParams) (fuel := fuel) do
      for v in vs do
        if v.safety != v₀.safety then
          throw <| .other
            "invalid mutual definition, declarations must have the same safety annotation"
        checkConstantVal env v.toConstantVal
  let mut env' := env
  for v in vs do
    env' := env'.add (.defnInfo v)
  if check then
    M.run env' (safety := v₀.safety) (lctx := {}) (lparams := v₀.levelParams) (fuel := fuel) do
      for v in vs do
        checkNoMVarNoFVar env' v.name v.value
        let valType ← TypeChecker.checkType v.value
        if !(← isDefEq valType v.type) then
          throw <| .declTypeMismatch env' (.mutualDefnDecl vs) valType
  return env'

/-- Type check given declaration and add it to the environment -/
def addDecl (env : Environment) (decl : Declaration) (check := true) (fuel : FuelConfig := {}) :
    Except Exception Environment := do
  match decl with
  | .axiomDecl v => addAxiom env v check fuel
  | .defnDecl v => addDefinition env v check fuel
  | .thmDecl v => addTheorem env v check fuel
  | .opaqueDecl v => addOpaque env v check fuel
  | .mutualDefnDecl v => addMutual env v check fuel
  | .quotDecl => addQuot env
  | .inductDecl lparams nparams types isUnsafe =>
    let allowPrimitive ← checkPrimitiveInductive env lparams nparams types isUnsafe
    addInductive env lparams nparams types isUnsafe allowPrimitive fuel
