import Lean4Lean.Theory.VDecl

namespace Lean4Lean

def VInductDecl.WF (env : VEnv) (decl : VInductDecl) : Prop := sorry

def VEnv.addInduct (env : VEnv) (decl : VInductDecl) : Option VEnv := sorry
