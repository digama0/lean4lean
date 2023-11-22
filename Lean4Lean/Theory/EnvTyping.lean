import Lean4Lean.Theory.Typing
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Inductive

namespace Lean4Lean

open Lean (Name FVarId)

def VDefVal.WF (env : VPreEnv) (ci : VDefVal) : Prop := env.HasType ci.uvars [] ci.value ci.type

inductive VDecl.WF : VPreEnv → VDecl → VEnv → Prop where
  | block :
    env.env.addConst n none = some env' →
    VDecl.WF env (.block n) env'
  | axiom :
    ci.WF env.T →
    env.env.addConst ci.name (some ci.toVConstant) = some env' →
    VDecl.WF env (.axiom ci) env'
  | def :
    ci.WF env →
    env.env.addConst ci.name (some ci.toVConstant) = some env' →
    VDecl.WF env (.def ci) (env'.addDefEq ci.toDefEq)
  | opaque :
    ci.WF env →
    env.env.addConst ci.name (some ci.toVConstant) = some env' →
    VDecl.WF env (.opaque ci) env'
  | example :
    ci.WF env.T →
    VDecl.WF env (.example ci) env.env
  | quot :
    env.env.QuotReady →
    env.env.addQuot = some env' →
    VDecl.WF env .quot env'
  | induct :
    decl.WF env.env →
    env.env.addInduct decl = some env' →
    VDecl.WF env (.induct decl) env'

def Typing.withEnv (env : VEnv) (T : Typing) : Typing :=
  (VPreEnv.mk env T).HasType

def Typing.empty : Typing := Typing.withEnv .empty fun _ _ _ _ => False

inductive VEnv.WF : VEnv → List VDecl → Typing → Prop where
  | empty : VEnv.WF .empty [] Typing.empty
  | decl {env} :
    VDecl.WF ⟨env, T⟩ d env' →
    env.WF ds T →
    env.WF (d::ds) (T.withEnv env')
