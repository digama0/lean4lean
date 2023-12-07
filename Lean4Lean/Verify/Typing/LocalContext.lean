import Lean4Lean.Verify.LocalContext

namespace Lean4Lean

def VLCtx.toCtx : VLCtx → List VExpr
  | [] => []
  | (_, .vlam ty) :: Δ => ty :: VLCtx.toCtx Δ
  | (_, .vlet _ _) :: Δ => VLCtx.toCtx Δ

def VLocalDecl.WF (env : VEnv) (U : Nat) (Δ : VLCtx) : VLocalDecl → Prop
  | .vlam type => env.IsType U Δ.toCtx type
  | .vlet type value => env.HasType U Δ.toCtx value type

variable (env : VEnv) (U : Nat) in
def VLCtx.WF : VLCtx → Prop
  | [] => True
  | (ofv, d) :: (Δ : VLCtx) =>
    VLCtx.WF Δ ∧ (do Δ.lookup (some (← ofv))) = none ∧ VLocalDecl.WF env U Δ d
