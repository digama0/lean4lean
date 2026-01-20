/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.CoreM
import Lean.Util.FoldConsts
import Lean4Lean.Environment
import Lake.Load.Manifest

namespace Lean

def HashMap.keyNameSet (m : Std.HashMap Name α) : NameSet :=
  m.fold (fun s n _ => s.insert n) {}

namespace Environment

def importsOf (env : Environment) (n : Name) : Array Import :=
  if n = env.header.mainModule then
    env.header.imports
  else match env.getModuleIdx? n with
    | .some idx => env.header.moduleData[idx.toNat]!.imports
    | .none => #[]

end Environment

/-- Like `Expr.getUsedConstants`, but produce a `NameSet`. -/
def Expr.getUsedConstants' (e : Expr) : NameSet :=
  e.foldConsts {} fun c cs => cs.insert c

namespace ConstantInfo

/-- Return all names appearing in the type or value of a `ConstantInfo`. -/
def getUsedConstants (c : ConstantInfo) : NameSet :=
  c.type.getUsedConstants' ++ match c.value? with
  | some v => v.getUsedConstants'
  | none => match c with
    | .inductInfo val => .ofList val.ctors
    | .opaqueInfo val => val.value.getUsedConstants'
    | .ctorInfo val => ({} : NameSet).insert val.name
    | .recInfo val => .ofList val.all
    | _ => {}

end ConstantInfo

end Lean

open Lean hiding Environment Exception
open Kernel

structure Context where
  newConstants : Std.HashMap Name ConstantInfo
  verbose := false
  compare := false
  checkQuot := true

structure State where
  env : Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}
  numAdded : Nat := 0
  hasStrings := false

abbrev M := ReaderT Context <| StateRefT State IO

/-- Check if a `Name` still needs processing. If so, move it from `remaining` to `pending`. -/
def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

def Lean.Kernel.Exception.mapEnvM [Monad m]
    (ex : Exception) (f : Environment → m Environment) : m Exception := do
  match ex with
  | unknownConstant env c => return .unknownConstant (← f env) c
  | alreadyDeclared env c => return .alreadyDeclared (← f env) c
  | declTypeMismatch env d t => return .declTypeMismatch env d t
  | declHasMVars env c e => return declHasMVars (← f env) c e
  | declHasFVars env c e => return declHasFVars (← f env) c e
  | funExpected env lctx e => return funExpected (← f env) lctx e
  | typeExpected env lctx e => return typeExpected (← f env) lctx e
  | letTypeMismatch  env lctx n t1 t2 => return letTypeMismatch (← f env) lctx n t1 t2
  | exprTypeMismatch env lctx e t => return exprTypeMismatch (← f env) lctx e t
  | appTypeMismatch  env lctx e fn arg => return appTypeMismatch (← f env) lctx e fn arg
  | invalidProj env lctx e => return invalidProj (← f env) lctx e
  | thmTypeIsNotProp env c t => return thmTypeIsNotProp (← f env) c t
  | other _
  | deterministicTimeout
  | excessiveMemory
  | deepRecursion
  | interrupted => return ex

/-- Use the current `Environment` to throw a `Kernel.Exception`. -/
def throwKernelException (ex : Exception) : M α := do
  let options := pp.match.set (pp.rawOnError.set {} true) false
  -- Note: because the environment we are using has no extension state,
  -- we cannot safely use it with lean functions like the pretty printer.
  -- Here we instead create a fresh environment, which is good enough to get
  -- basic pretty printing working.
  let env ← mkEmptyEnvironment
  let ex ← ex.mapEnvM fun _ => return env.toKernelEnv
  Prod.fst <$> (Lean.Core.CoreM.toIO · { fileName := "", options, fileMap := default } { env }) do
    Lean.throwKernelException ex

def Lean.Declaration.name : Declaration → String
  | .axiomDecl d => s!"axiomDecl {d.name}"
  | .defnDecl d => s!"defnDecl {d.name}"
  | .thmDecl d => s!"thmDecl {d.name}"
  | .opaqueDecl d => s!"opaqueDecl {d.name}"
  | .quotDecl => s!"quotDecl"
  | .mutualDefnDecl d => s!"mutualDefnDecl {d.map (·.name)}"
  | .inductDecl _ _ d _ => s!"inductDecl {d.map (·.name)}"

/-- Add a declaration, possibly throwing a `KernelException`. -/
def addDecl (d : Declaration) : M Unit := do
  if (← read).verbose then
    println! "adding {d.name}"
  let t1 ← IO.monoMsNow
  match Lean4Lean.addDecl (← get).env d true with
  | .ok env =>
    let t2 ← IO.monoMsNow
    if t2 - t1 > 1000 then
      if (← read).compare then
        let t3 ← match (← get).env.addDecl {} d with
        | .ok _ => IO.monoMsNow
        | .error ex => _root_.throwKernelException ex
        if (t2 - t1) > 2 * (t3 - t2) then
          println!
            "{(← get).env.header.mainModule}:{d.name}: lean took {t3 - t2}, lean4lean took {t2 - t1}"
        else
          println! "{(← get).env.header.mainModule}:{d.name}: lean4lean took {t2 - t1}"
      else
        println! "{(← get).env.header.mainModule}:{d.name}: lean4lean took {t2 - t1}"
    modify fun s => { s with env, numAdded := s.numAdded + 1 }
  | .error ex =>
    throwKernelException ex

deriving instance BEq for ConstantVal
deriving instance BEq for ConstructorVal
deriving instance BEq for RecursorRule
deriving instance BEq for RecursorVal

def Lean.Expr.hasStrLit (e : Expr) : Bool := (e.find? isStringLit).isSome

def Lean.ConstantInfo.hasStrLit (ci : ConstantInfo) : Bool :=
  ci.type.hasStrLit || ci.value?.any (·.hasStrLit)

mutual
/--
Check if a `Name` still needs to be processed (i.e. is in `remaining`).

If so, recursively replay any constants it refers to,
to ensure we add declarations in the right order.

The construct the `Declaration` from its stored `ConstantInfo`,
and add it to the environment.
-/
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants[name]? | unreachable!
    let mut usedConstants := ci.getUsedConstants
    -- We want `String.ofList` to be available when encountering string literals.
    -- Presumably faster to first check if we already have it, before traversing
    -- the declaration
    unless (← get).hasStrings do
      if ci.hasStrLit then
        usedConstants := usedConstants.insert ``String.ofList
        usedConstants := usedConstants.insert ``Char.ofNat
        modify ({· with hasStrings := true })
    replayConstants usedConstants
    -- Check that this name is still pending: a mutual block may have taken care of it.
    if (← get).pending.contains name then
      let addDeclAt (d : Declaration) :=
        try addDecl d catch e => throw <| IO.userError s!"at {name}: {e.toString}"
      match ci with
      | .defnInfo   info => addDeclAt (.defnDecl   info)
      | .thmInfo    info => addDeclAt (.thmDecl    info)
      | .axiomInfo  info => addDeclAt (.axiomDecl  info)
      | .opaqueInfo info => addDeclAt (.opaqueDecl info)
      | .inductInfo info =>
        let lparams := info.levelParams
        let nparams := info.numParams
        let all ← info.all.mapM fun n => do pure <| (← read).newConstants[n]!
        for o in all do
          modify fun s =>
            { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
        let ctorInfo ← all.mapM fun ci => do
          pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do
            pure (← read).newConstants[n]!)
        -- Make sure we are really finished with the constructors.
        for (_, ctors) in ctorInfo do
          for ctor in ctors do
            replayConstants ctor.getUsedConstants
        let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
          { name := ci.name
            type := ci.type
            ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
        addDeclAt (.inductDecl lparams nparams types false)
      -- We postpone checking constructors,
      -- and at the end make sure they are identical
      -- to the constructors generated when we replay the inductives.
      | .ctorInfo info =>
        modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
      -- Similarly we postpone checking recursors.
      | .recInfo info =>
        modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
      | .quotInfo _ => addDeclAt .quotDecl
      modify fun s => { s with pending := s.pending.erase name }

/-- Replay a set of constants one at a time. -/
partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n

end

/--
Check that all postponed constructors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedConstructors : M Unit := do
  for ctor in (← get).postponedConstructors do
    match (← get).env.constants.find? ctor, (← read).newConstants[ctor]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      unless info == info' do throw <| IO.userError s!"Invalid constructor {ctor}"
    | _, _ => throw <| IO.userError s!"No such constructor {ctor}"

/--
Check that all postponed recursors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedRecursors : M Unit := do
  for ctor in (← get).postponedRecursors do
    match (← get).env.constants.find? ctor, (← read).newConstants[ctor]? with
    | some (.recInfo info), some (.recInfo info') =>
      unless info == info' do throw <| IO.userError s!"Invalid recursor {ctor}"
    | _, _ => throw <| IO.userError s!"No such recursor {ctor}"

/--
Check that at the end of (any) file, the quotient module is initialized by the end.
(It will already be initialized at the beginning, unless this is the very first file,
`Init.Core`, which is responsible for initializing it.)
This is needed because it is an assumption in `finalizeImport`.
-/
def checkQuotInit : M Unit := do
  unless (← get).env.quotInit do
    throw <| IO.userError s!"initial import (Init.Prelude) didn't initialize quotient module"

/-- "Replay" some constants into an `Environment`, sending them to the kernel for checking. -/
def replay (ctx : Context) (env : Environment) (decl : Option Name := none) :
    IO (Nat × Environment) := do
  let mut remaining : NameSet := ∅
  for (n, ci) in ctx.newConstants.toList do
    -- We skip unsafe constants, and also partial constants.
    -- Later we may want to handle partial constants.
    if !ci.isUnsafe && !ci.isPartial then
      remaining := remaining.insert n
  let (_, s) ← StateRefT'.run (s := { env, remaining }) do
    ReaderT.run (r := ctx) do
      match decl with
      | some d => replayConstant d
      | none =>
        for n in remaining do
          replayConstant n
      checkPostponedConstructors
      checkPostponedRecursors
      if (← read).checkQuot then checkQuotInit
  return (s.numAdded, s.env)

open private ImportedModule.mk from Lean.Environment in
unsafe def replayFromImports (module : Name) (verbose := false) (compare := false) : IO Nat := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let (mod, region) ← readModuleData mFile
  let (_, s) ← (importModulesCore mod.imports).run
  let env ← match Kernel.Environment.finalizeImport s mod.imports module 0 with
    | .ok env => pure env
    | .error e => throw <| .userError <| ← (e.toMessageData {}).toString
  let mut newConstants := {}
  for name in mod.constNames, ci in mod.constants do
    newConstants := newConstants.insert name ci
  let (n, env') ← replay { newConstants, verbose, compare } env
  (Environment.ofKernelEnv env').freeRegions
  region.free
  pure n

unsafe def replayFromFresh (module : Name)
    (verbose := false) (compare := false) (decl : Option Name := none) : IO Nat := do
  Lean.withImportModules #[module] {} (trustLevel := 0) fun env => do
    let ctx := { newConstants := env.constants.map₁, verbose, compare, checkQuot := false }
    Prod.fst <$> replay ctx (.empty module) decl

/-- Read the name of the main module from the `lake-manifest`. -/
-- This has been copied from `ImportGraph.getCurrentModule` in the
-- https://github.com/leanprover-community/import-graph repository.
def getCurrentModule : IO Name := do
  match (← Lake.Manifest.load? ⟨"lake-manifest.json"⟩) with
  | none =>
    -- TODO: should this be caught?
    pure .anonymous
  | some manifest =>
    -- TODO: This assumes that the `package` and the default `lean_lib`
    -- have the same name up to capitalisation.
    -- Would be better to read the `.defaultTargets` from the
    -- `← getRootPackage` from `Lake`, but I can't make that work with the monads involved.
    return manifest.name.capitalize

/--
Run as e.g. `lake exe lean4lean` to check everything in the current project.
or e.g. `lake exe lean4lean Mathlib.Data.Nat` to check everything with module name
starting with `Mathlib.Data.Nat`.

This will replay all the new declarations from the target file into the `Environment`
as it was at the beginning of the file, using the kernel to check them.

You can also use `lake exe lean4lean --fresh Mathlib.Data.Nat.Basic` to replay all the constants
(both imported and defined in that file) into a fresh environment,
but this can only be used on a single file.
-/
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (flags, args) := args.partition fun s => s.startsWith "-"
  let verbose := "-v" ∈ flags || "--verbose" ∈ flags
  let fresh : Bool := "--fresh" ∈ flags
  let compare : Bool := "--compare" ∈ flags
  let targets ← do
    match args with
    | [] => pure [← getCurrentModule]
    | args => args.mapM fun arg => do
      let mod := arg.toName
      if mod.isAnonymous then
        throw <| IO.userError s!"Could not resolve module: {arg}"
      else
        pure mod
  let mut targetModules := []
  let sp ← searchPathRef.get
  for target in targets do
    let mut found := false
    for path in (← SearchPath.findAllWithExt sp "olean") do
      if let some m := (← searchModuleNameOfFileName path sp) then
        if target.isPrefixOf m then
          targetModules := targetModules.insert m
          found := true
    if not found then
      throw <| IO.userError <| match args with
      | [] => s!"Could not infer main module (tried {target}). \
        Use `lake exe lean4lean <target>` instead"
      | _ => s!"Could not find any oleans for: {target}"
  let mut n := 0
  if fresh then
    if targetModules.length != 1 then
      throw <| IO.userError s!"--fresh flag is only valid when specifying a single module:\n\
        {targetModules}"
    for m in targetModules do
      if verbose then IO.println s!"replaying {m} with --fresh"
      n := n + (← replayFromFresh m verbose compare)
  else
    let mut tasks := #[]
    for m in targetModules do
      tasks := tasks.push (m, ← IO.asTask (replayFromImports m verbose compare))
    let mut err := false
    for (m, t) in tasks do
      if verbose then IO.println s!"replaying {m}"
      match t.get with
      | .error e =>
        IO.eprintln s!"lean4lean found a problem in {m}:\n{e.toString}"
        err := true
      | .ok n' => n := n + n'
    if err then return 1
  println! "checked {n} declarations"
  return 0
