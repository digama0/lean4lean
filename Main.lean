/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean4Lean.Replay
import Lake.Load.Manifest

open Lean hiding Environment Exception
open Kernel Lean4Lean.Replay

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

namespace Lean4Lean.FuelConfig

/-- Serialize `cfg` to its JSON object map, or panic — it's derived so it must be an object. -/
private def toObj (cfg : FuelConfig) : Std.TreeMap.Raw String Lean.Json compare :=
  match Lean.toJson cfg with
  | .obj m => m
  | _ => panic! "FuelConfig.toJson produced a non-object"

/-- Field names that `FuelConfig` accepts (derived from its JSON encoding). -/
private def fieldNames : List String :=
  (toObj {}).foldr (fun k _ acc => k :: acc) []

/-- Layer a JSON object over an existing `FuelConfig`.

Unknown fields are rejected up front (the derived `FromJson` silently ignores
them, which we don't want for a config file); known fields are overlaid on top
of the base config's own JSON serialization and the merged object is fed back
through `fromJson?`, so value validation stays entirely in the derived parser. -/
private def ofJson? (base : FuelConfig) (j : Lean.Json) : Except String FuelConfig := do
  let .obj m := j | throw "config JSON must be an object"
  let baseObj := toObj base
  m.foldlM (init := ()) fun _ k _ => do
    unless baseObj.contains k do
      throw s!"unknown field '{k}' in config JSON (valid: {fieldNames})"
  let merged := m.foldl (init := baseObj) (·.insert · ·)
  Lean.fromJson? (.obj merged)

/-- Read + parse a config file, layering over an existing base. -/
private def ofFile (base : FuelConfig) (path : System.FilePath) : IO FuelConfig := do
  let raw ← IO.FS.readFile path
  let j ← IO.ofExcept (Lean.Json.parse raw)
  IO.ofExcept (ofJson? base j)

/-- Apply a single `--config:field=value` override.

Value is parsed as JSON, then routed through `fuelConfigOfJson?` — so the CLI
path and the file path share the same parser (and produce the same error
messages for e.g. non-numeric values or unknown fields). -/
private def applyFlag (cfg : FuelConfig) (field value : String) :
    Except String FuelConfig := do
  let jval ← match Lean.Json.parse value with
    | .ok j => pure j
    | .error _ => throw s!"could not parse value '{value}' for --config:{field} as JSON"
  ofJson? cfg (.obj (Std.TreeMap.Raw.empty.insert field jval))
    |>.mapError (s!"in --config:{field}={value}: " ++ ·)

end Lean4Lean.FuelConfig

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
  let mut fuel : Lean4Lean.FuelConfig := {}
  for flag in flags do
    if let some path := flag.dropPrefix? "--config=" then
      fuel ← Lean4Lean.FuelConfig.ofFile fuel ⟨path.toString⟩
    else if let some rest := flag.dropPrefix? "--config:" then
      let [field, value] := rest.toString.splitOn "="
        | throw <| IO.userError s!"malformed flag {flag}: expected --config:<field>=<value>"
      match fuel.applyFlag field value with
      | .ok f => fuel := f
      | .error e => throw <| IO.userError e
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
      n := n + (← replayFromFresh m verbose compare (fuel := fuel))
  else
    let mut tasks := #[]
    for m in targetModules do
      tasks := tasks.push (m, ← IO.asTask (replayFromImports m verbose compare (fuel := fuel)))
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
