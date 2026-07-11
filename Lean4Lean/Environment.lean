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
    let env' := env.add (.defnInfo v)
    if check then
      checkNoMVarNoFVar env' v.name v.value
      M.run env' (safety := .unsafe) (lctx := {}) (lparams := v.levelParams) (fuel := fuel) do
        let valType ← TypeChecker.checkType v.value
        if !(← isDefEq valType v.type) then
          throw <| .declTypeMismatch env' (.defnDecl v) valType
    return env'
  else
    if check then
      M.run env (safety := .safe) (lctx := {}) (lparams := v.levelParams) (fuel := fuel) do
        checkConstantVal env v.toConstantVal (← checkPrimitiveDef v)
        let valType ← TypeChecker.checkType v.value
        if !(← isDefEq valType v.type) then
          throw <| .declTypeMismatch env (.defnDecl v) valType
    return env.add (.defnInfo v)

/-- Same as `addDefinition` but returns final `Stats` for the (last) `M.run`. -/
def addDefinitionWithStats (env : Environment) (v : DefinitionVal)
    (fuel : FuelConfig := {}) : Except Exception (Environment × TypeChecker.Stats) := do
  if let .unsafe := v.safety then
    _ ← (checkConstantVal env v.toConstantVal).run env
      (safety := .unsafe) (lparams := v.levelParams) (fuel := fuel)
    let env' := env.add (.defnInfo v)
    checkNoMVarNoFVar env' v.name v.value
    let (_, s) ← M.runWithState env' (safety := .unsafe) (lctx := {}) (lparams := v.levelParams)
        (fuel := fuel) do
      let valType ← TypeChecker.checkType v.value
      if !(← isDefEq valType v.type) then
        throw <| .declTypeMismatch env' (.defnDecl v) valType
    return (env', s.stats)
  else
    let (_, s) ← M.runWithState env (safety := .safe) (lctx := {}) (lparams := v.levelParams)
        (fuel := fuel) do
      checkConstantVal env v.toConstantVal (← checkPrimitiveDef v)
      let valType ← TypeChecker.checkType v.value
      if !(← isDefEq valType v.type) then
        throw <| .declTypeMismatch env (.defnDecl v) valType
    return (env.add (.defnInfo v), s.stats)

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

/-- Enabled at module load if the `LEAN4LEAN_TCSTEP` env var is set. Guards the
intra-decl `TCSTEP`/`TCTAG` bisection dumps in `addTheoremWithStats`. -/
initialize tcStepEnabled : Bool ← return (← IO.getEnv "LEAN4LEAN_TCSTEP").isSome

/-- Same as `addTheorem` but returns the final `Stats` alongside the environment.

When `LEAN4LEAN_TCSTEP` is set, emits `TCSTEP {label} isdefeq=N deq_fp=H` (and
per-tag `TCTAG` lines) at each labeled step inside the theorem-check path.
Off by default so full-mathlib runs don't drown in intra-decl trace. -/
def addTheoremWithStats (env : Environment) (v : TheoremVal)
    (fuel : FuelConfig := {}) : Except Exception (Environment × TypeChecker.Stats) := do
  let (_, s) ← M.runWithState env (safety := .safe) (lctx := {}) (lparams := v.levelParams)
      (fuel := fuel) do
    let step (label : String) : M Unit := do
      unless tcStepEnabled do return
      let st ← get
      dbg_trace "TCSTEP {label} isdefeq={st.stats.isDefEq} deq_fp={st.stats.deqFingerprint}"
      let sortedTags := st.stats.deqPerTag.toArray.qsort (·.2 > ·.2)
      for (tag, cnt) in sortedTags do
        dbg_trace "TCTAG {label} {tag}={cnt}"
    step "thm.start"
    if !(← isProp v.type) then
      throw <| .thmTypeIsNotProp env v.name v.type
    step "thm.after_is_prop"
    checkConstantVal env v.toConstantVal
    step "thm.after_check_const_val"
    let valType ← TypeChecker.checkType v.value
    step "thm.after_check_val"
    if !(← isDefEq valType v.type) then
      throw <| .declTypeMismatch env (.thmDecl v) valType
    step "thm.after_final_defeq"
  return (env.add (.thmInfo v), s.stats)

def addOpaque (env : Environment) (v : OpaqueVal) (check := true) (fuel : FuelConfig := {}) :
    Except Exception Environment := do
  if check then
    M.run env (safety := .safe) (lctx := {}) (lparams := v.levelParams) (fuel := fuel) do
      checkConstantVal env v.toConstantVal
      let valType ← TypeChecker.checkType v.value
      if !(← isDefEq valType v.type) then
        throw <| .declTypeMismatch env (.opaqueDecl v) valType
  return env.add (.opaqueInfo v)

/-- Same as `addOpaque` but returns the final `Stats` alongside the environment. -/
def addOpaqueWithStats (env : Environment) (v : OpaqueVal)
    (fuel : FuelConfig := {}) : Except Exception (Environment × TypeChecker.Stats) := do
  let (_, s) ← M.runWithState env (safety := .safe) (lctx := {}) (lparams := v.levelParams)
      (fuel := fuel) do
    checkConstantVal env v.toConstantVal
    let valType ← TypeChecker.checkType v.value
    if !(← isDefEq valType v.type) then
      throw <| .declTypeMismatch env (.opaqueDecl v) valType
  return (env.add (.opaqueInfo v), s.stats)

/-- Same as `addAxiom` but returns the final `Stats` alongside the environment. -/
def addAxiomWithStats (env : Environment) (v : AxiomVal)
    (fuel : FuelConfig := {}) : Except Exception (Environment × TypeChecker.Stats) := do
  let (_, s) ← M.runWithState env
      (safety := if v.isUnsafe then .unsafe else .safe) (lctx := {}) (lparams := v.levelParams)
      (fuel := fuel) do
    checkConstantVal env v.toConstantVal
  return (env.add (.axiomInfo v), s.stats)

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

/--
Same as `addDecl` but returns `TypeChecker.Stats` for the checked pass.
Only the primary type-check path (theorem / definition) reports non-empty stats;
other decl kinds return `{}`.
-/
def addDeclWithStats (env : Environment) (decl : Declaration) (fuel : FuelConfig := {}) :
    Except Exception (Environment × TypeChecker.Stats) := do
  match decl with
  | .thmDecl v => addTheoremWithStats env v fuel
  | .defnDecl v => addDefinitionWithStats env v fuel
  | .opaqueDecl v => addOpaqueWithStats env v fuel
  | .axiomDecl v => addAxiomWithStats env v fuel
  | _ =>
    let env' ← addDecl env decl true fuel
    return (env', {})
