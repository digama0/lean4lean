import Lean4Lean.Environment

/-!
Nested occurrences of indexed families (`divergences.md`,
`Lean4Lean.validateNestedAuxiliaries`).

Nested lowering stores each nested occurrence `I Ds` applied to the parameters
of `I` only, so for a family with indices the stored term is a type family,
not a type, and the generated auxiliary family is itself indexed
(`Vec VTree 2` lowers to `_nested.Vec_1 2` with `_nested.Vec_1 : Nat → Type`).
The C++ kernel only type-checks the stored term, and so does lean4lean.

Each block below is accepted by the C++ kernel (it is elaborated here); it is
re-added under fresh names through `Lean4Lean.addDecl`, and the inductive
types, constructors and recursors lean4lean generates (including the
auxiliary recursors `rec_1`, ... and every rule) are compared with the C++
kernel's, as in `Tests/RecursorOracle.lean`.  The blocks with parameters
(`VTree4`, `VTree5`, `IT`, `IT2`) also exercise the restored-rule check of an
indexed family below its index binders.
-/

namespace Lean4Lean.Tests.NestedIndexedFamily

open Lean

/-- Rename every constant of the block `all` to a fresh copy. -/
def renameIn (all : List Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls =>
      match all.find? (·.isPrefixOf n) with
      | some i => some (.const (n.replacePrefix i (i.appendAfter "_copy")) ls)
      | none => none
    | _ => none

def rename (all : List Name) (n : Name) : Name :=
  match all.find? (·.isPrefixOf n) with
  | some i => n.replacePrefix i (i.appendAfter "_copy")
  | none => n

def sameRecursor (all : List Name) (r r' : RecursorVal) : Bool :=
  renameIn all r.type == r'.type && r.numParams == r'.numParams &&
  r.numIndices == r'.numIndices && r.numMotives == r'.numMotives &&
  r.numMinors == r'.numMinors && r.k == r'.k && r.isUnsafe == r'.isUnsafe &&
  r.rules.length == r'.rules.length &&
  (r.rules.zip r'.rules).all fun (a, b) =>
    rename all a.ctor == b.ctor && a.nfields == b.nfields &&
    renameIn all a.rhs == b.rhs

/-- Re-add the mutual block of `I` through `Lean4Lean.addDecl` and compare its
types, constructors and recursors with the C++ kernel's. -/
def oracle (I : Name) : MetaM Unit := do
  let env ← getEnv
  let some (.inductInfo v) := env.find? I | throwError "{I} is not an inductive type"
  let all := v.all
  let types ← all.mapM fun n => do
    let some (.inductInfo w) := env.find? n | throwError "missing {n}"
    let ctors ← w.ctors.mapM fun c => do
      let some (.ctorInfo cv) := env.find? c | throwError "missing {c}"
      pure { name := rename all c, type := renameIn all cv.type : Constructor }
    pure { name := rename all n, type := renameIn all w.type, ctors : InductiveType }
  let decl := Declaration.inductDecl v.levelParams v.numParams types v.isUnsafe
  match Lean4Lean.addDecl env.toKernelEnv decl with
  | .error e => throwError "Lean4Lean.addDecl rejected {I}: {← (e.toMessageData {}).toString}"
  | .ok kenv =>
    for n in all do
      let some (.inductInfo w) := env.find? n | unreachable!
      let some (.inductInfo w') := kenv.find? (rename all n)
        | throwError "Lean4Lean generated no inductive for {n}"
      unless renameIn all w.type == w'.type && w.numParams == w'.numParams &&
          w.numIndices == w'.numIndices && w.numNested == w'.numNested &&
          w.isRec == w'.isRec && w.ctors.map (rename all) == w'.ctors do
        throwError "generated inductive {n} differs from Lean's"
      for c in w.ctors do
        let some (.ctorInfo a) := env.find? c | unreachable!
        let some (.ctorInfo b) := kenv.find? (rename all c)
          | throwError "Lean4Lean generated no constructor for {c}"
        unless renameIn all a.type == b.type && a.numParams == b.numParams &&
            a.numFields == b.numFields && a.cidx == b.cidx do
          throwError "generated constructor {c} differs from Lean's:\n{b.type}"
      let some (.recInfo r) := env.find? (n ++ `rec) | throwError "Lean has no {n}.rec"
      let some (.recInfo r') := kenv.find? (rename all (n ++ `rec))
        | throwError "Lean4Lean generated no recursor for {n}"
      unless sameRecursor all r r' do
        throwError "generated recursor for {n} differs from Lean's:\n{r'.type}\n{r'.rules.map (·.rhs)}"
    let mut i := 1
    repeat
      let auxName := (I ++ `rec).appendIndexAfter i
      match env.find? auxName, kenv.find? (rename all auxName) with
      | some (.recInfo r), some (.recInfo r') =>
        unless sameRecursor all r r' do
          throwError "generated auxiliary recursor {auxName} differs from Lean's:\n{r'.type}\n{r'.rules.map (·.rhs)}"
        i := i + 1
      | none, none => break
      | _, _ => throwError "auxiliary recursor {auxName} present on one side only"
    if i == 1 then
      throwError "{I} has no auxiliary recursor: it is not a nested inductive"

inductive Vec (α : Type) : Nat → Type
  | nil : Vec α 0
  | cons {n} : α → Vec α n → Vec α (n + 1)

/-- `Vec VTree 2` is a nested occurrence of an indexed family. -/
inductive VTree
  | node : Vec VTree 2 → VTree

/-- The index varies with a constructor field. -/
inductive VTree2
  | leaf
  | node (n : Nat) : Vec VTree2 n → VTree2

/-- A parameter, with the index fixed. -/
inductive VTree4 (β : Type)
  | leaf : β → VTree4 β
  | node : Vec (VTree4 β) 2 → VTree4 β

/-- A parameter, with the index varying. -/
inductive VTree5 (β : Type)
  | leaf : β → VTree5 β
  | node (n : Nat) : Vec (VTree5 β) n → VTree5 β

/-- A nested indexed structure: its auxiliary family is an indexed structure. -/
inductive IBox (α : Type) : Nat → Type
  | mk : α → IBox α 0

inductive ITree
  | node : IBox ITree 0 → ITree

/-- An indexed family nested inside an indexed family. -/
inductive Deep
  | node : Vec (Vec Deep 1) 2 → Deep

-- A mutual block whose nested occurrence is indexed.
mutual
inductive MA
  | mk : Vec MB 3 → MA
inductive MB
  | mk : List MA → MB
end

-- Indexed families with parameters inside a nested block (the nested
-- occurrence itself is not indexed).
inductive IT (β : Type) : Nat → Type
  | leaf : β → IT β 0
  | node : List (IT β 0) → IT β 1

inductive IT2 (β : Type) : Nat → Type
  | leaf : β → IT2 β 0
  | node : List (IT2 β 0) → (n : Nat) → IT2 β n → IT2 β (n + 1)

run_meta do
  for I in [``VTree, ``VTree2, ``VTree4, ``VTree5, ``ITree, ``Deep, ``MA, ``IT, ``IT2] do
    oracle I

end Lean4Lean.Tests.NestedIndexedFamily
