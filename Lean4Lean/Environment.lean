import Lean4Lean.TypeChecker
import Lean4Lean.Quot
import Lean4Lean.Inductive.Add
import Lean4Lean.Primitive

namespace Lean4Lean
open Lean hiding Environment Exception
open TypeChecker Kernel Environment

open private Lean.Kernel.Environment.add from Lean.Environment

def checkConstantVal (env : Environment) (v : ConstantVal) (allowPrimitive := false) : M Unit := do
  checkName env v.name allowPrimitive
  checkDuplicatedUnivParams v.levelParams
  checkNoMVarNoFVar env v.name v.type
  let sort ← checkType v.type
  _ ← ensureSort sort v.type

def addAxiom (env : Environment) (v : AxiomVal) (check := true) :
    Except Exception Environment := do
  if check then
    _ ← (checkConstantVal env v.toConstantVal).run env
      (safety := if v.isUnsafe then .unsafe else .safe) (lparams := v.levelParams)
  return env.add (.axiomInfo v)

def addDefinition (env : Environment) (v : DefinitionVal) (check := true) :
    Except Exception Environment := do
  if let .unsafe := v.safety then
    -- Meta definition can be recursive.
    -- So, we check the header, add, and then type check the body.
    if check then
      _ ← (checkConstantVal env v.toConstantVal).run env
        (safety := .unsafe) (lparams := v.levelParams)
    let env' := env.add (.defnInfo v)
    if check then
      checkNoMVarNoFVar env' v.name v.value
      M.run env' (safety := .unsafe) (lctx := {}) (lparams := v.levelParams) do
        let valType ← TypeChecker.checkType v.value
        if !(← isDefEq valType v.type) then
          throw <| .declTypeMismatch env' (.defnDecl v) valType
    return env'
  else
    if check then
      M.run env (safety := .safe) (lctx := {}) (lparams := v.levelParams) do
        checkConstantVal env v.toConstantVal (← checkPrimitiveDef v)
        let valType ← TypeChecker.checkType v.value
        if !(← isDefEq valType v.type) then
          throw <| .declTypeMismatch env (.defnDecl v) valType
    return env.add (.defnInfo v)

def addTheorem (env : Environment) (v : TheoremVal) (check := true) :
    Except Exception Environment := do
  if check then
    -- TODO(Leo): we must add support for handling tasks here
    M.run env (safety := .safe) (lctx := {}) (lparams := v.levelParams) do
      if !(← isProp v.type) then
        throw <| .thmTypeIsNotProp env v.name v.type
      checkConstantVal env v.toConstantVal
      let valType ← TypeChecker.checkType v.value
      if !(← isDefEq valType v.type) then
        throw <| .declTypeMismatch env (.thmDecl v) valType
  return env.add (.thmInfo v)

def addOpaque (env : Environment) (v : OpaqueVal) (check := true) :
    Except Exception Environment := do
  if check then
    M.run env (safety := .safe) (lctx := {}) (lparams := v.levelParams) do
      checkConstantVal env v.toConstantVal
      let valType ← TypeChecker.checkType v.value
      if !(← isDefEq valType v.type) then
        throw <| .declTypeMismatch env (.opaqueDecl v) valType
  return env.add (.opaqueInfo v)

def addMutual (env : Environment) (vs : List DefinitionVal) (check := true) :
    Except Exception Environment := do
  let v₀ :: _ := vs | throw <| .other "invalid empty mutual definition"
  if let .safe := v₀.safety then
    throw <| .other "invalid mutual definition, declaration is not tagged as unsafe/partial"
  if check then
    M.run env (safety := v₀.safety) (lctx := {}) (lparams := v₀.levelParams) do
      for v in vs do
        if v.safety != v₀.safety then
          throw <| .other
            "invalid mutual definition, declarations must have the same safety annotation"
        checkConstantVal env v.toConstantVal
  let mut env' := env
  for v in vs do
    env' := env'.add (.defnInfo v)
  if check then
    M.run env' (safety := v₀.safety) (lctx := {}) (lparams := v₀.levelParams) do
      for v in vs do
        checkNoMVarNoFVar env' v.name v.value
        let valType ← TypeChecker.checkType v.value
        if !(← isDefEq valType v.type) then
          throw <| .declTypeMismatch env' (.mutualDefnDecl vs) valType
  return env'

/-- Type check given declaration and add it to the environment -/
def addDecl (env : Environment) (decl : Declaration) (check := true) :
    Except Exception Environment := do
  match decl with
  | .axiomDecl v => addAxiom env v check
  | .defnDecl v => addDefinition env v check
  | .thmDecl v => addTheorem env v check
  | .opaqueDecl v => addOpaque env v check
  | .mutualDefnDecl v => addMutual env v check
  | .quotDecl => addQuot env
  | .inductDecl lparams nparams types isUnsafe =>
    let allowPrimitive ← checkPrimitiveInductive env lparams nparams types isUnsafe
    addInductive env lparams nparams types isUnsafe allowPrimitive
