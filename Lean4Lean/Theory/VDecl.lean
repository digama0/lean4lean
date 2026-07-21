import Lean4Lean.Theory.VEnv

namespace Lean4Lean

structure VConstVal extends VConstant where
  name : Name

structure VDefVal extends VConstVal where
  value : VExpr

def VDefVal.toDefEq (v : VDefVal) : VDefEq :=
  ⟨v.uvars, .const v.name (VLevel.params v.uvars), v.value, v.type⟩

structure VInductiveType extends VConstVal where
  ctors : List VConstVal

/-- One recursor computation (ι) rule, mirroring `Lean.RecursorRule`: it fires
on constructor `ctor` (which has `nfields` non-parameter arguments) and rewrites
to `rhs` applied to the recursor's parameters/motives/minors and the
constructor's fields. `rhs` is the closed, universe-abstracted reduct template
`fun params motives minors fields => minorᵢ fields recursiveCalls` — the
recursive calls are already baked in (they reference the recursor by name and
re-fire through this same rule), exactly as the kernel builds it. -/
structure VRecRule where
  ctor : Name
  nfields : Nat
  rhs : VExpr

/-- A recursor, mirroring `Lean.RecursorVal`. Extends `VConstVal` with the
recursor's own name/universe-count/type; the `num*` fields record the telescope
segmentation (`getMajorIdx = numParams + numMotives + numMinors + numIndices`),
`k` flags K-like reduction, and `rules` holds one ι rule per constructor. -/
structure VRecursor extends VConstVal where
  all : List Name
  numParams : Nat
  numMotives : Nat
  numMinors : Nat
  numIndices : Nat
  k : Bool
  rules : List VRecRule

/-- The recursor argument index of the major premise: everything to its left
(parameters, motives, minors, indices) precedes it in an application spine.
Mirrors `Lean.RecursorVal.getMajorIdx`. -/
def VRecursor.getMajorIdx (r : VRecursor) : Nat :=
  r.numParams + r.numMotives + r.numMinors + r.numIndices

/-- The recursor argument index of the first index (equivalently, the count of
parameters + motives + minors). Mirrors `Lean.RecursorVal.getFirstIndexIdx`. -/
def VRecursor.getFirstIndexIdx (r : VRecursor) : Nat :=
  r.numParams + r.numMotives + r.numMinors

structure VInductDecl where
  uvars : Nat
  nparams : Nat
  types : List VInductiveType
  recs : List VRecursor

inductive VDecl where
  /-- Reserve a constant name, which cannot be used in expressions.
  Used to represent unsafe declarations in safe mode -/
  | block (n : Name)
  | axiom (_ : VConstVal)
  | def (_ : VDefVal)
  | opaque (_ : VDefVal)
  | example (_ : VDefVal)
  | quot
  | induct (_ : VInductDecl)
