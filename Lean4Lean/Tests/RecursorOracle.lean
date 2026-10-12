import Lean4Lean.Environment
import Init.Internal.Order.Basic

/-! Oracle tests for the executable recursor construction.

Each inductive below is re-added through `Lean4Lean.addDecl` under a fresh name and the
generated `RecursorVal`s (type, metadata, and every rule RHS) are compared with the recursors
Lean's kernel produced for the copied declaration.  Acceptance alone is not enough: the
regression this guards against (a recursor placeholder captured by the field binders of a
higher-order recursive field) produced *accepted* declarations whose iota rules were wrong,
and was only visible by comparing the generated rules with Lean's.

The last block pins the behaviour of `Expr.abstract` on loose bound variables that the
verification's abstraction model (`Expr.abstractN`) relies on. -/

open Lean Meta Elab Term

namespace Lean4Lean.Tests.RecursorOracle

/-- Rename every constant belonging to the block `all` to a fresh copy. -/
def renameIn (all : List Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls =>
      match all.find? (fun i => i.isPrefixOf n) with
      | some i => some (.const (n.replacePrefix i (i.appendAfter "_oracleCopy")) ls)
      | none => none
    | _ => none

def sameRecursor (all : List Name) (r r' : RecursorVal) : Bool :=
  renameIn all r.type == r'.type && r.numParams == r'.numParams &&
  r.numIndices == r'.numIndices && r.numMotives == r'.numMotives &&
  r.numMinors == r'.numMinors && r.k == r'.k && r.isUnsafe == r'.isUnsafe &&
  r.rules.length == r'.rules.length &&
  (r.rules.zip r'.rules).all fun (a, b) =>
    a.nfields == b.nfields && renameIn all a.rhs == b.rhs

/-- Re-add `id`'s mutual block through `Lean4Lean.addDecl` and compare all its recursors
(including auxiliary nested recursors `rec_1`, `rec_2`, ...) with Lean's. -/
elab "#recursor_oracle " id:ident : command => Command.liftTermElabM do
  let env ← getEnv
  let name ← realizeGlobalConstNoOverload id
  let some (.inductInfo I) := env.find? name | throwError "{id} is not an inductive type"
  let all := I.all
  let types ← all.mapM fun n => do
    let some (.inductInfo v) := env.find? n | throwError "missing {n}"
    let ctors ← v.ctors.mapM fun c => do
      let some (.ctorInfo cv) := env.find? c | throwError "missing {c}"
      pure { name := c.replacePrefix n (n.appendAfter "_oracleCopy"),
             type := renameIn all cv.type : Constructor }
    pure { name := n.appendAfter "_oracleCopy", type := renameIn all v.type, ctors : InductiveType }
  let decl := Declaration.inductDecl I.levelParams I.numParams types I.isUnsafe
  match Lean4Lean.addDecl env.toKernelEnv decl (check := true) with
  | .error e => throwError "Lean4Lean.addDecl rejected {id}: {e.toMessageData {}}"
  | .ok kenv =>
    for n in all do
      let recName := n ++ `rec
      let some (.recInfo r) := env.find? recName | throwError "Lean has no {recName}"
      let some (.recInfo r') := kenv.find? ((n.appendAfter "_oracleCopy") ++ `rec)
        | throwError "Lean4Lean generated no recursor for {n}"
      unless sameRecursor all r r' do
        throwError "generated recursor for {n} differs from Lean's:\n{r'.type}\n{r'.rules.map (·.rhs)}"
    let mut i := 1
    repeat
      let auxName := (I.name ++ `rec).appendIndexAfter i
      match env.find? auxName,
          kenv.find? (((I.name.appendAfter "_oracleCopy") ++ `rec).appendIndexAfter i) with
      | some (.recInfo r), some (.recInfo r') =>
        unless sameRecursor all r r' do
          throwError "generated auxiliary recursor {auxName} differs from Lean's"
        i := i + 1
      | none, none => break
      | _, _ => throwError "auxiliary recursor {auxName} present on one side only"

-- Higher-order recursive fields (`∀ y, r y x → Acc r y`): the bug this guards against made
-- `Acc.rec`'s rule `intro x h fun y a => a y (h y a)`.
#recursor_oracle Acc
-- Two binders under the recursive occurrence, in a predicate with a non-recursive field.
#recursor_oracle Lean.Order.iterates
-- Ordinary, mutual-free, first-order recursion, and a structure.
#recursor_oracle Nat
#recursor_oracle List
#recursor_oracle Prod
-- Nested inductives: auxiliary recursors and restoration.
#recursor_oracle Lean.Json
#recursor_oracle Lean.Expr
#recursor_oracle Lean.Level
#recursor_oracle Lean.Name
#recursor_oracle Lean.MessageData

-- Nested inductive whose constructor types contain a `TSyntax` field with string literals in
-- its type; the guard check used to run out of fuel on the literal expansion.
inductive WithSyntaxField
  | one (name : Lean.TSyntax ``Lean.binderIdent)
  | clear
  | tuple (args : List WithSyntaxField)
#recursor_oracle WithSyntaxField

-- Higher-order recursive field with several binders, and a dependent later field.
inductive HigherOrder (α : Type) : Nat → Prop
  | leaf : HigherOrder α 0
  | node (n : Nat) (f : ∀ (_ : α) (b : Bool) (k : Nat), b = true → HigherOrder α k)
      (h : n = n) : HigherOrder α (n + 1)
#recursor_oracle HigherOrder

/-! `Expr.abstract` leaves loose bound variables unshifted and picks the last occurrence of a
duplicated variable; `Expr.abstractN` is the model of exactly this behaviour. -/

def x : Expr := .fvar ⟨`x⟩
def y : Expr := .fvar ⟨`y⟩

example : ((Expr.bvar 0).abstract #[x] == .bvar 0) = true := by native_decide
example : ((Expr.app (.bvar 3) x).abstract #[x, y] == .app (.bvar 3) (.bvar 1)) = true := by
  native_decide
example : (x.abstract #[x, x] == .bvar 0) = true := by native_decide
example : ((Expr.lam `z (.const `Nat []) (.app (.bvar 0) x) .default).abstract #[x] ==
    .lam `z (.const `Nat []) (.app (.bvar 0) (.bvar 1)) .default) = true := by native_decide

end Lean4Lean.Tests.RecursorOracle
