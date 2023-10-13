import Lean.Environment

namespace Lean.Environment

def get (env : Environment) (n : Name) : Except KernelException ConstantInfo :=
  match env.find? n with
  | some ci => pure ci
  | none => throw <| .unknownConstant env n

def checkDuplicatedUnivParams : List Name → Except KernelException Unit
  | [] => pure ()
  | p :: ls => do
    if p ∈ ls then
      throw <| .other
        s!"failed to add declaration to environment, duplicate universe level parameter: '{p}'"
    checkDuplicatedUnivParams ls

def checkNoMVar (env : Environment) (n : Name) (e : Expr) : Except KernelException Unit := do
  if e.hasMVar then
    throw <| .declHasMVars env n e

def checkNoFVar (env : Environment) (n : Name) (e : Expr) : Except KernelException Unit := do
  if e.hasFVar then
    throw <| .declHasFVars env n e

def checkNoMVarNoFVar (env : Environment) (n : Name) (e : Expr) : Except KernelException Unit := do
  checkNoMVar env n e
  checkNoFVar env n e

def checkName (env : Environment) (n : Name) : Except KernelException Unit := do
  if env.contains n then
    throw <| .alreadyDeclared env n
