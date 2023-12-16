import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Inductive

namespace Lean4Lean

def VDefVal.WF (env : VEnv) (ci : VDefVal) : Prop := env.HasType ci.uvars [] ci.value ci.type

inductive VDecl.WF : VEnv → VDecl → VEnv → Prop where
  | block :
    env.addConst n none = some env' →
    VDecl.WF env (.block n) env'
  | axiom :
    ci.WF env →
    env.addConst ci.name (some ci.toVConstant) = some env' →
    VDecl.WF env (.axiom ci) env'
  | def :
    ci.WF env →
    env.addConst ci.name (some ci.toVConstant) = some env' →
    VDecl.WF env (.def ci) (env'.addDefEq ci.toDefEq)
  | opaque :
    ci.WF env →
    env.addConst ci.name (some ci.toVConstant) = some env' →
    VDecl.WF env (.opaque ci) env'
  | example :
    ci.WF env →
    VDecl.WF env (.example ci) env
  | quot :
    env.QuotReady →
    env.addQuot = some env' →
    VDecl.WF env .quot env'
  | induct :
    decl.WF env →
    env.addInduct decl = some env' →
    VDecl.WF env (.induct decl) env'

inductive VEnv.WF : List VDecl → VEnv → Prop where
  | empty : VEnv.WF [] .empty
  | decl {env} : VDecl.WF env d env' → env.WF ds → env'.WF (d::ds)
