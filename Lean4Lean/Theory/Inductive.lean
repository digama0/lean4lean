import Lean4Lean.Theory.VDecl

namespace Lean4Lean

open Lean (Name FVarId)

def VInductDecl.WF (env : VEnv) (decl : VInductDecl) : Prop := sorry

def VEnv.addInduct (env : VEnv) (decl : VInductDecl) : Option VEnv := sorry
