import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.Meta

namespace Lean4Lean

open Lean (Name FVarId)

def VEnv.QuotReady (env : VEnv) : Prop :=
  env.constants ``Eq = some vconst(type_of% @Eq)

def VEnv.addQuot (env : VEnv) : Option VEnv := do
  let env ← env.addConst ``Quot vconst(type_of% @Quot)
  let env ← env.addConst ``Quot.mk vconst(type_of% @Quot.mk)
  let env ← env.addConst ``Quot.ind vconst(type_of% @Quot.ind)
  let env ← env.addConst ``Quot.lift vconst(type_of% @Quot.lift)
  env.addDefEq vdefeq(α r β f c a => @Quot.lift α r β f c (Quot.mk r a) ≡ f a)
