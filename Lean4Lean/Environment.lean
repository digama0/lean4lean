import Lean4Lean.TypeChecker
import Lean4Lean.Quot
import Lean4Lean.Inductive.Add

namespace Lean
namespace Environment
open TypeChecker

def checkConstantVal (env : Environment) (v : ConstantVal) : M Unit := do
  checkName env v.name
  checkDuplicatedUnivParams v.levelParams
  checkNoMVarNoFVar env v.name v.type
  let sort ← check v.type v.levelParams
  _ ← ensureSort sort v.type

def addAxiom (env : Environment) (v : AxiomVal) (check := true) :
    Except KernelException Environment := do
  if check then
    _ ← (checkConstantVal env v.toConstantVal).run env
      (safety := if v.isUnsafe then .unsafe else .safe)
  return env.add (.axiomInfo v)

def addDefinition (env : Environment) (v : DefinitionVal) (check := true) :
    Except KernelException Environment := do
  if let .unsafe := v.safety then
    -- Meta definition can be recursive.
    -- So, we check the header, add, and then type check the body.
    if check then
      _ ← (checkConstantVal env v.toConstantVal).run env (safety := .unsafe)
    let env' := env.add (.defnInfo v)
    if check then
      checkNoMVarNoFVar env' v.name v.value
      M.run env' (safety := .unsafe) (lctx := {}) do
        let valType ← TypeChecker.check v.value v.levelParams
        if !(← isDefEq valType v.type) then
          throw <| .declTypeMismatch env' (.defnDecl v) valType
    return env'
  else
    if check then
      M.run env (safety := .safe) (lctx := {}) do
        checkConstantVal env v.toConstantVal
        checkNoMVarNoFVar env v.name v.value
        let valType ← TypeChecker.check v.value v.levelParams
        if !(← isDefEq valType v.type) then
          throw <| .declTypeMismatch env (.defnDecl v) valType
    return env.add (.defnInfo v)

def addTheorem (env : Environment) (v : TheoremVal) (check := true) :
    Except KernelException Environment := do
  if check then
    -- TODO(Leo): we must add support for handling tasks here
    M.run env (safety := .safe) (lctx := {}) do
      checkConstantVal env v.toConstantVal
      checkNoMVarNoFVar env v.name v.value
      let valType ← TypeChecker.check v.value v.levelParams
      if !(← isDefEq valType v.type) then
        throw <| .declTypeMismatch env (.thmDecl v) valType
  return env.add (.thmInfo v)

def addOpaque (env : Environment) (v : OpaqueVal) (check := true) :
    Except KernelException Environment := do
  if check then
    M.run env (safety := .safe) (lctx := {}) do
      checkConstantVal env v.toConstantVal
      let valType ← TypeChecker.check v.value v.levelParams
      if !(← isDefEq valType v.type) then
        throw <| .declTypeMismatch env (.opaqueDecl v) valType
  return env.add (.opaqueInfo v)

def addMutual (env : Environment) (vs : List DefinitionVal) (check := true) :
    Except KernelException Environment := do
  let v₀ :: _ := vs | throw <| .other "invalid empty mutual definition"
  if let .safe := v₀.safety then
    throw <| .other "invalid mutual definition, declaration is not tagged as unsafe/partial"
  if check then
    M.run env (safety := v₀.safety) (lctx := {}) do
      for v in vs do
        if v.safety != v₀.safety then
          throw <| .other
            "invalid mutual definition, declarations must have the same safety annotation"
        checkConstantVal env v.toConstantVal
  let mut env' := env
  for v in vs do
    env' := env'.add (.defnInfo v)
  if check then
    M.run env (safety := v₀.safety) (lctx := {}) do
      for v in vs do
        checkNoMVarNoFVar env' v.name v.value
        let valType ← TypeChecker.check v.value v.levelParams
        if !(← isDefEq valType v.type) then
          throw <| .declTypeMismatch env' (.mutualDefnDecl vs) valType
  return env'

/-- Type check given declaration and add it to the environment -/
def addDecl' (env : Environment) (decl : @& Declaration) (check := true) :
    Except KernelException Environment := do
  match decl with
  | .axiomDecl v => addAxiom env v check
  | .defnDecl v => addDefinition env v check
  | .thmDecl v => addTheorem env v check
  | .opaqueDecl v => addOpaque env v check
  | .mutualDefnDecl v => addMutual env v check
  | .quotDecl => addQuot env
  | .inductDecl lparams nparams types isUnsafe => addInductive env lparams nparams types isUnsafe
