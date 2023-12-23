import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Verify.NameGenerator
import Lean4Lean.Verify.VLCtx

namespace Lean4Lean
open Lean

variable (fvars : FVarId → Prop) in
def InScope : Expr → (k :_:= 0) → Prop
  | .bvar i, k => i < k
  | .fvar fv, _ => fvars fv
  | .sort .., _ | .const .., _ | .lit .., _ => True
  | .app f a, k => InScope f k ∧ InScope a k
  | .lam _ d b _, k
  | .forallE _ d b _, k => InScope d k ∧ InScope b (k+1)
  | .letE _ d v b _, k => InScope d k ∧ InScope v k ∧ InScope b (k+1)
  | .proj _ _ e, k | .mdata _ e, k => InScope e k
  | .mvar .., _ => False

def VLocalDecl.WF (env : VEnv) (U : Nat) (Δ : VLCtx) : VLocalDecl → Prop
  | .vlam type => env.IsType U Δ.toCtx type
  | .vlet type value => env.HasType U Δ.toCtx value type

variable (env : VEnv) (U : Nat) in
def VLCtx.WF : VLCtx → Prop
  | [] => True
  | (ofv, d) :: (Δ : VLCtx) =>
    VLCtx.WF Δ ∧ (do Δ.lookup (some (← ofv))) = none ∧ VLocalDecl.WF env U Δ d

def TrProj (Δ : VLCtx) (structName : Name) (idx : Nat) (e : VExpr) : VExpr → Prop := sorry

variable (env : VEnv) (Us : List Name) in
inductive TrExpr : VLCtx → Expr → VExpr → Prop
  | bvar : Δ.find? (.inl i) = some (e, A) → TrExpr Δ (.bvar i) e
  | fvar : Δ.find? (.inr fv) = some (e, A) → TrExpr Δ (.fvar fv) e
  | sort : VLevel.ofLevel Us u = some u' → TrExpr Δ (.sort u) (.sort u')
  | const :
    env.constants c = some (some ci) →
    us.mapM (VLevel.ofLevel Us) = some us' →
    us.length = ci.uvars →
    TrExpr Δ (.const c us) (.const c us')
  | app :
    env.HasType Us.length Δ.toCtx f' (.forallE A B) →
    env.HasType Us.length Δ.toCtx a' A →
    TrExpr Δ f f' → TrExpr Δ a a' → TrExpr Δ (.app f a) (.app f' a')
  | lam :
    env.IsType Us.length Δ.toCtx ty' →
    TrExpr Δ ty ty' → TrExpr ((none, .vlam ty') :: Δ) body body' →
    TrExpr Δ (.lam name ty body bi) (.lam ty' body')
  | forallE :
    env.IsType Us.length Δ.toCtx ty' →
    env.IsType Us.length (ty' :: Δ.toCtx) body' →
    TrExpr Δ ty ty' → TrExpr ((none, .vlam ty') :: Δ) body body' →
    TrExpr Δ (.forallE name ty body bi) (.forallE ty' body')
  | letE :
    env.HasType Us.length Δ.toCtx val' ty' →
    TrExpr Δ ty ty' → TrExpr Δ val val' →
    TrExpr ((none, .vlet ty' val') :: Δ) body body' →
    TrExpr Δ (.letE name ty val body bi) body'
  | lit : TrExpr Δ l.toConstructor e → TrExpr Δ (.lit l) e
  | mdata : TrExpr Δ e e' → TrExpr Δ (.mdata d e) e'
  | proj : TrExpr Δ e e' → TrProj Δ s i e' e'' → TrExpr Δ (.proj s i e) e''
