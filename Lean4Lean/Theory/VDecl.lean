import Lean4Lean.Theory.VEnv

namespace Lean4Lean

structure VConstVal extends VConstant where
  name : Name

structure VDefVal extends VConstVal where
  value : VExpr

def VDefVal.toDefEq (v : VDefVal) : VDefEq :=
  ⟨v.uvars, .const v.name (VLevel.params v.uvars), v.value, v.type⟩

def VEnv.addMutualHeaders : VEnv → List VDefVal → Option VEnv
  | env, [] => some env
  | env, v :: vs => do
    let env ← env.addConst v.name v.toVConstant
    env.addMutualHeaders vs

def VEnv.addMutualDefEqs (env : VEnv) (vs : List VDefVal) : VEnv :=
  vs.foldl (fun env v => env.addDefEq v.toDefEq) env

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
  | mutual (_ : List VDefVal)
  | example (_ : VDefVal)
  | quot
  | induct (_ : VInductDecl)
