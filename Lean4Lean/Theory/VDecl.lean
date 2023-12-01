import Lean4Lean.Theory.VEnv

namespace Lean4Lean

open Lean (Name)

structure VConstVal extends VConstant where
  name : Name

structure VDefVal extends VConstVal where
  value : VExpr

def VDefVal.toDefEq (v : VDefVal) : VDefEq :=
  ⟨v.uvars, .const v.name ((List.range v.uvars).map .param), v.value, v.type⟩

structure VInductiveType extends VConstVal where
  ctors : List VConstVal

structure VInductDecl where
  uvars : Nat
  nparams : Nat
  types : List VInductiveType

inductive VDecl where
  /-- Reserve a constant name, which cannot be used in expressions.
  Used to represent unsafe declarations in safe mode -/
  | block (n : Name)
  | axiom (_ : VConstVal)
  | def (_ : VDefVal)
  | opaque (_ : VDefVal)
  | example (_ : VConstant)
  | quot
  | induct (_ : VInductDecl)
