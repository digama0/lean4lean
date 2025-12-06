import Lean4Lean.Theory.VDecl

namespace Lean4Lean

axiom VInductDecl.WF (env : VEnv) (decl : VInductDecl) : Prop -- := sorry

axiom VEnv.addInduct (env : VEnv) (decl : VInductDecl) : Option VEnv -- := sorry
