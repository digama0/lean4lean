import Lean4Lean.Environment

namespace Lean4Lean.Tests.Environment

open Lean
open Lean.Kernel

private def kernelAccepts (env : Kernel.Environment) (decl : Declaration) : Bool :=
  match env.addDeclCore 0 decl none with
  | .ok _ => true
  | .error _ => false

private def lean4leanAccepts (env : Kernel.Environment) (decl : Declaration) : Bool :=
  match Lean4Lean.addDecl env decl with
  | .ok _ => true
  | .error _ => false

private def checkParity (env : Kernel.Environment) (decl : Declaration) : MetaM Unit :=
  unless kernelAccepts env decl == lean4leanAccepts env decl do
    throwError "lean4lean disagrees with the kernel on a synthetic declaration"

private def sortDef (name : Name) (levelParams : List Name) (level : Level)
    (safety := DefinitionSafety.unsafe) : DefinitionVal where
  name := name
  levelParams := levelParams
  type := .sort (.succ level)
  value := .sort level
  hints := .regular 0
  safety := safety

run_meta
  let empty := Kernel.Environment.empty `Lean4Lean.Tests.Environment

  -- The C++ kernel checks each member of a mutual block under that member's universe
  -- parameters, rather than reusing the parameters of the first declaration.
  let u := Level.param `u
  let vw := Level.max (Level.param `v) (Level.param `w)
  let variedParams := Declaration.mutualDefnDecl [
    sortDef `Lean4Lean.Tests.Environment.first [`u] u,
    sortDef `Lean4Lean.Tests.Environment.second [`v, `w] vw]
  checkParity empty variedParams
  unless kernelAccepts empty variedParams do
    throwError "the varied-universe mutual declaration should be accepted"

  -- Repeated names within a mutual block are intentionally not pre-rejected: both
  -- implementations retain the last entry.
  let duplicateName := `Lean4Lean.Tests.Environment.duplicate
  let duplicate := Declaration.mutualDefnDecl [
    sortDef duplicateName [] .zero,
    sortDef duplicateName [`u] u]
  checkParity empty duplicate
  let .ok kernelDuplicate := empty.addDeclCore 0 duplicate none
    | throwError "the kernel rejected the duplicate-name mutual declaration"
  let .ok lean4leanDuplicate := Lean4Lean.addDecl empty duplicate
    | throwError "lean4lean rejected the duplicate-name mutual declaration"
  match kernelDuplicate.find? duplicateName, lean4leanDuplicate.find? duplicateName with
  | some (.defnInfo kernelVal), some (.defnInfo lean4leanVal) =>
    unless kernelVal == lean4leanVal do
      throwError "lean4lean and the kernel retained different mutual entries"
  | _, _ => throwError "the duplicate-name mutual declaration did not retain a definition"

  let free := Expr.fvar ⟨`free⟩
  let badDef := Declaration.defnDecl {
    sortDef `Lean4Lean.Tests.Environment.freeDefinition [] .zero (.safe) with
    value := free }
  checkParity empty badDef
  unless !kernelAccepts empty badDef do
    throwError "the kernel unexpectedly accepted a free variable in a definition body"

  let badTheorem := Declaration.thmDecl {
    name := `Lean4Lean.Tests.Environment.freeTheorem
    levelParams := []
    type := .forallE `p (.sort .zero) (.bvar 0) .default
    value := free }
  checkParity empty badTheorem
  unless !kernelAccepts empty badTheorem do
    throwError "the kernel unexpectedly accepted a free variable in a theorem body"

  let env ← Lean.getEnv
  let some (.defnInfo natAdd) := env.toKernelEnv.find? ``Nat.add
    | throwError "Nat.add is not a definition"
  let partialNatAdd := { natAdd with safety := DefinitionSafety.partial }
  match (Lean4Lean.Environment.checkPrimitiveDef partialNatAdd).run env.toKernelEnv
      (lparams := partialNatAdd.levelParams) with
  | .ok false => pure ()
  | .ok true => throwError "a partial definition was accepted as a primitive"
  | .error _ => throwError "the partial primitive check failed unexpectedly"

end Lean4Lean.Tests.Environment
