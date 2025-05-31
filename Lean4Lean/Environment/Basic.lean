import Lean.Environment

namespace Lean.Kernel.Environment

def contains (env : Environment) (n : Name) : Bool :=
  env.constants.contains n

def get (env : Environment) (n : Name) : Except Exception ConstantInfo :=
  match env.find? n with
  | some ci => pure ci
  | none => throw <| .unknownConstant env n

def checkDuplicatedUnivParams : List Name → Except Exception Unit
  | [] => pure ()
  | p :: ls => do
    if p ∈ ls then
      throw <| .other
        s!"failed to add declaration to environment, duplicate universe level parameter: '{p}'"
    checkDuplicatedUnivParams ls

def checkNoMVar (env : Environment) (n : Name) (e : Expr) : Except Exception Unit := do
  if e.hasMVar then
    throw <| .declHasMVars env n e

def checkNoFVar (env : Environment) (n : Name) (e : Expr) : Except Exception Unit := do
  if e.hasFVar then
    throw <| .declHasFVars env n e

def checkNoMVarNoFVar (env : Environment) (n : Name) (e : Expr) : Except Exception Unit := do
  checkNoMVar env n e
  checkNoFVar env n e

def primitives : NameSet := .ofList [
  ``Bool, ``Bool.false, ``Bool.true,
  ``Nat, ``Nat.zero, ``Nat.succ,
  ``Nat.add, ``Nat.pred, ``Nat.sub, ``Nat.mul, ``Nat.pow,
  ``Nat.gcd, ``Nat.mod, ``Nat.div, ``Nat.beq, ``Nat.ble,
  ``String, ``String.mk]

/--
Returns true iff `constName` is a non-recursive inductive datatype that has only one constructor and no indices.

Such types have special kernel support. This must be in sync with `is_structure_like`.
-/
def isStructureLike (env : Environment) (constName : Name) : Bool :=
  match env.find? constName with
  | some (.inductInfo { isRec := false, ctors := [_], numIndices := 0, .. }) => true
  | _ => false

def checkName (env : Environment) (n : Name)
    (allowPrimitive := false) : Except Exception Unit := do
  if env.contains n then
    throw <| .alreadyDeclared env n
  unless allowPrimitive do
    if primitives.contains n then
      throw <| .other s!"unexpected use of primitive name {n}"
