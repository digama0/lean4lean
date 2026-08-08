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

/-- One recursor computation (ι) rule, mirroring `Lean.RecursorRule`: firing on
constructor `ctor` (with `nfields` non-parameter arguments) rewrites to the
closed reduct template `rhs`. -/
structure VRecRule where
  ctor : Name
  nfields : Nat
  rhs : VExpr

/-- A recursor, mirroring `Lean.RecursorVal`: the `num*` fields record the
telescope segmentation, `k` flags K-like reduction, and `rules` holds one ι rule
per constructor. -/
structure VRecursor extends VConstVal where
  all : List Name
  numParams : Nat
  numMotives : Nat
  numMinors : Nat
  numIndices : Nat
  k : Bool
  rules : List VRecRule

/-- The recursor argument index of the major premise. Mirrors
`Lean.RecursorVal.getMajorIdx`. -/
def VRecursor.getMajorIdx (r : VRecursor) : Nat :=
  r.numParams + r.numMotives + r.numMinors + r.numIndices

/-- The recursor argument index of the first index. Mirrors
`Lean.RecursorVal.getFirstIndexIdx`. -/
def VRecursor.getFirstIndexIdx (r : VRecursor) : Nat :=
  r.numParams + r.numMotives + r.numMinors

structure VInductDecl where
  uvars : Nat
  nparams : Nat
  types : List VInductiveType
  recs : List VRecursor

inductive VDecl where
  | axiom (_ : VConstVal)
  | def (_ : VDefVal)
  | opaque (_ : VDefVal)
  | example (_ : VDefVal)
  | quot
  | induct (_ : VInductDecl)
  | mutualDef (_ : List VDefVal)
