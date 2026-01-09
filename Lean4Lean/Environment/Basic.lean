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
  ``Nat.bitwise, ``Nat.land, ``Nat.lor, ``Nat.xor,
  ``Nat.shiftLeft, ``Nat.shiftRight,
  ``String.ofList, ``Char.ofNat]

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

open private subsumesInfo Kernel.Environment.mk moduleNames moduleNameMap parts toEffectiveImport
  interpData? from Lean.Environment

def empty (mainModule : Name) (trustLevel : UInt32 := 0) : Environment :=
  Kernel.Environment.mk
    (constants := {})
    (quotInit := false)
    (diagnostics := {})
    (const2ModIdx := {})
    (extensions := #[])
    (irBaseExts := #[])
    (header := { mainModule, trustLevel })

def throwAlreadyImported (s : ImportState) (const2ModIdx : Std.HashMap Name ModuleIdx)
    (modIdx : Nat) (cname : Name) : Except Exception α := do
  let modName := (moduleNames s)[modIdx]!
  let constModName := (moduleNames s)[const2ModIdx[cname]!.toNat]!
  throw <| .other
    s!"import {modName} failed, environment already contains '{cname}' from {constModName}"

def finalizeImport (s : ImportState) (imports : Array Import) (mainModule : Name)
    (trustLevel : UInt32 := 0) : Except Exception Environment := do
  let modules := (moduleNames s).filterMap ((moduleNameMap s)[·]?)
  let moduleData ← modules.mapM fun mod => do
    let some data := interpData? mod .private |
      throw <| .other s!"missing data file for module {mod.module}"
    return data
  let numPrivateConsts := moduleData.foldl (init := 0) fun numPrivateConsts data => Id.run do
    numPrivateConsts + data.constants.size + data.extraConstNames.size
  let mut const2ModIdx := .emptyWithCapacity (capacity := numPrivateConsts)
  let mut privateConstantMap := .emptyWithCapacity (capacity := numPrivateConsts)
  for h : modIdx in [0:moduleData.size] do
    let data := moduleData[modIdx]
    for cname in data.constNames, cinfo in data.constants do
      match privateConstantMap.getThenInsertIfNew? cname cinfo with
      | (cinfoPrev?, constantMap') =>
        privateConstantMap := constantMap'
        if let some cinfoPrev := cinfoPrev? then
          -- Recall that the map has not been modified when `cinfoPrev? = some _`.
          if subsumesInfo privateConstantMap cinfo cinfoPrev then
            privateConstantMap := privateConstantMap.insert cname cinfo
          else if !subsumesInfo privateConstantMap cinfoPrev cinfo then
            throwAlreadyImported s const2ModIdx modIdx cname
      const2ModIdx := const2ModIdx.insertIfNew cname modIdx
    for cname in data.extraConstNames do
      const2ModIdx := const2ModIdx.insertIfNew cname modIdx

  return Kernel.Environment.mk
    (constants := SMap.fromHashMap privateConstantMap false)
    (quotInit := !imports.isEmpty) -- We assume `Init.Prelude` initializes quotient module
    (diagnostics := {})
    (const2ModIdx := const2ModIdx)
    (extensions := #[])
    (irBaseExts := #[])
    (header := {
      trustLevel, imports, moduleData, mainModule, isModule := false
      regions := modules.flatMap (parts · |>.map (·.2))
      modules := modules.map toEffectiveImport
    })
