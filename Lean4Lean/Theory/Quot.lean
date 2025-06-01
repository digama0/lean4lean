import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.Meta

namespace Lean4Lean

def eqConst := vconst(type_of% @Eq)
def quotConst := vconst(type_of% @Quot)
def quotMkConst := vconst(type_of% @Quot.mk)
def quotLiftConst := vconst(type_of% @Quot.lift)
def quotIndConst := vconst(type_of% @Quot.ind)
def quotDefEq := vdefeq(α r β f c a => @Quot.lift α r β f c (Quot.mk r a) ≡ f a)

def VEnv.QuotReady (env : VEnv) : Prop :=
  env.constants ``Eq = some eqConst

def VEnv.addQuot (env : VEnv) : Option VEnv := do
  let env ← env.addConst ``Quot quotConst
  let env ← env.addConst ``Quot.mk quotMkConst
  let env ← env.addConst ``Quot.lift quotLiftConst
  let env ← env.addConst ``Quot.ind quotIndConst
  env.addDefEq quotDefEq
