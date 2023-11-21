import Lean4Lean.Theory.Typing
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Inductive

namespace Lean4Lean

open Lean (Name FVarId)

def VConstant.WF (env : VEnv) (ci : VConstant) : Prop := IsType env ci.uvars [] ci.type
def VDefVal.WF (env : VEnv) (ci : VDefVal) : Prop := HasType env ci.uvars [] ci.value ci.type

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

inductive VEnv.WF : VEnv → List VDecl → Prop where
  | empty : VEnv.empty.WF []
  | decl : VDecl.WF env d env' → env.WF ds → env.WF (d::ds)
