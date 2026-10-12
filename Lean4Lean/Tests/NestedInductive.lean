import Lean4Lean.Environment

/-!
Regression tests for the nested-inductive parameter check added for
leanprover/lean4#14577.

When a nested occurrence `I Ds is` is eliminated, the parametric arguments `Ds` are dropped
from the generated auxiliary type, so they escape the ordinary type checking of the
declaration. The kernel checks them separately at the end; so must we.

Both declarations are built by hand rather than elaborated, so that the environment does
not already contain them and only the kernel path is exercised.
-/

namespace Lean4Lean.Tests.NestedInductive

open Lean

/-- `inductive Tree0 (α : Type) | node : Array (Tree0 α) → Tree0 α` -/
def treeDecl : Declaration :=
  let tree := fun a => mkApp (mkConst `Tree0 []) a
  .inductDecl [] 1
    [{ name := `Tree0
       type := .forallE `α (.sort 1) (.sort 1) .default
       ctors := [{
         name := `Tree0.node
         type := .forallE `α (.sort 1)
           (.forallE `es (mkApp (mkConst ``Array [.zero]) (tree (.bvar 0)))
             (tree (.bvar 1)) .default) .default }] }]
    false

/-- As above, but the dropped parametric argument `Tree0 Bool.true` is ill typed. -/
def badDecl : Declaration :=
  .inductDecl [] 1
    [{ name := `Bad0
       type := .forallE `α (.sort 1) (.sort 1) .default
       ctors := [{
         name := `Bad0.node
         type := .forallE `α (.sort 1)
           (.forallE `es
             (mkApp (mkConst ``Array [.zero])
               (mkApp (mkConst `Bad0 []) (mkConst ``Bool.true)))
             (mkApp (mkConst `Bad0 []) (.bvar 1)) .default) .default }] }]
    false

/-- A direct recursive declaration, exercising the ordinary recursor/rule
path without nested lowering. -/
def recursiveDecl : Declaration :=
  let nat := mkConst `VerifiedNat []
  let zero : Constructor := { name := `VerifiedNat.zero, type := nat }
  let succ : Constructor := {
    name := `VerifiedNat.succ
    type := .forallE `pred nat nat .default }
  let info : InductiveType := {
    name := `VerifiedNat
    type := .sort 1
    ctors := [zero, succ] }
  .inductDecl [] 0 [info] false

/-- A mutually recursive block whose first family contains a nested
occurrence of the second under `Array`. -/
def mutualNestedDecl : Declaration :=
  let forest := fun a => mkApp (mkConst `VerifiedForest []) a
  let tree := fun a => mkApp (mkConst `VerifiedTree []) a
  let forestNode : Constructor := {
    name := `VerifiedForest.node
    type := .forallE `α (.sort 1)
      (.forallE `trees
        (mkApp (mkConst ``Array [.zero]) (tree (.bvar 0)))
        (forest (.bvar 1)) .default) .default }
  let treeNode : Constructor := {
    name := `VerifiedTree.node
    type := .forallE `α (.sort 1)
      (.forallE `value (.bvar 0)
        (.forallE `children (forest (.bvar 1))
          (tree (.bvar 2)) .default) .default) .default }
  let forestInfo : InductiveType := {
    name := `VerifiedForest
    type := .forallE `α (.sort 1) (.sort 1) .default
    ctors := [forestNode] }
  let treeInfo : InductiveType := {
    name := `VerifiedTree
    type := .forallE `α (.sort 1) (.sort 1) .default
    ctors := [treeNode] }
  .inductDecl [] 1 [forestInfo, treeInfo] false

run_meta do
  let kenv := (← getEnv).toKernelEnv

  -- A well-formed nested inductive must be accepted. Storing `aux2nested` abstracted over
  -- the parameters while checking it against a context of free variables regressed this
  -- into "type checker does not support loose bound variables" (#17).
  match Lean4Lean.addDecl kenv treeDecl with
  | .ok _ => pure ()
  | .error e =>
    throwError "nested inductive was rejected: {← (e.toMessageData {}).toString}"

  -- ... and an ill-typed dropped parameter must still be caught.
  match Lean4Lean.addDecl kenv badDecl with
  | .ok _ => throwError "nested inductive with an ill-typed parameter was accepted"
  | .error _ => pure ()

  match Lean4Lean.addDecl kenv recursiveDecl with
  | .error e =>
    throwError "recursive inductive was rejected: {← (e.toMessageData {}).toString}"
  | .ok env =>
    unless env.contains `VerifiedNat.rec do
      throwError "recursive inductive did not install its recursor"

  match Lean4Lean.addDecl kenv mutualNestedDecl with
  | .error e =>
    throwError "mutual nested inductive was rejected: {← (e.toMessageData {}).toString}"
  | .ok env =>
    unless env.contains `VerifiedForest.rec && env.contains `VerifiedTree.rec do
      throwError "mutual nested inductive did not install both primary recursors"

end Lean4Lean.Tests.NestedInductive
