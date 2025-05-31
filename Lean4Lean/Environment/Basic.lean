import Lean.Environment
import Batteries.Tactic.OpenPrivate

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

open private equivInfo Kernel.Environment.mk from Lean.Environment

def empty (mainModule : Name) (trustLevel : UInt32 := 0) : Environment :=
  Kernel.Environment.mk
    (const2ModIdx := {})
    (constants := {})
    (quotInit := false)
    (diagnostics := {})
    (extraConstNames := {})
    (header := { mainModule, trustLevel })
    (extensions := #[])

def finalizeImport (s : ImportState) (imports : Array Import) (mainModule : Name)
    (trustLevel : UInt32 := 0) : Except Exception Environment := do
  let numConsts := s.moduleData.foldl (init := 0) fun numConsts mod =>
    numConsts + mod.constants.size + mod.extraConstNames.size
  let mut const2ModIdx : Std.HashMap Name ModuleIdx := Std.HashMap.emptyWithCapacity (capacity := numConsts)
  let mut constantMap : Std.HashMap Name ConstantInfo := Std.HashMap.emptyWithCapacity (capacity := numConsts)
  for h : modIdx in [0:s.moduleData.size] do
    let mod := s.moduleData[modIdx]
    for cname in mod.constNames, cinfo in mod.constants do
      match constantMap.getThenInsertIfNew? cname cinfo with
      | (cinfoPrev?, constantMap') =>
        constantMap := constantMap'
        if let some cinfoPrev := cinfoPrev? then
          -- Recall that the map has not been modified when `cinfoPrev? = some _`.
          unless equivInfo cinfoPrev cinfo do
            let modName := s.moduleNames[modIdx]!
            let constModName := s.moduleNames[const2ModIdx[cname]!.toNat]!
            throw <| .other s!"import {modName} failed, environment already contains '{cname}' from {constModName}"
      const2ModIdx := const2ModIdx.insertIfNew cname modIdx
    for cname in mod.extraConstNames do
      const2ModIdx := const2ModIdx.insertIfNew cname modIdx
  let constants : ConstMap := SMap.fromHashMap constantMap false
  return Kernel.Environment.mk
    (const2ModIdx := const2ModIdx)
    (constants := constants)
    (quotInit := !imports.isEmpty) -- We assume `core.lean` initializes quotient module
    (diagnostics := {})
    (extraConstNames := {})
    (extensions := #[])
    (header := {
      trustLevel, imports, mainModule
      regions      := s.regions
      moduleNames  := s.moduleNames
      moduleData   := s.moduleData
    })
