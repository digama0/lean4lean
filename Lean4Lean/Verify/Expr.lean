import Lean4Lean.Expr
import Lean4Lean.Theory.VExpr
import Lean4Lean.Verify.Level

namespace Lean4Lean

open Lean (FVarId Expr)

inductive VLocalDecl where
  | vlam (type : VExpr)
  | vlet (type value : VExpr)

def VLocalDecl.depth : VLocalDecl → Nat
  | .vlam .. => 1
  | .vlet .. => 0

def VLocalDecl.value : VLocalDecl → VExpr
  | .vlam .. => .bvar 0
  | .vlet _ e => e

def VLCtx := List (Option FVarId × VLocalDecl)

namespace VLCtx

def next : Option FVarId → Nat ⊕ FVarId → Option (Nat ⊕ FVarId)
  | none, .inl 0 => none
  | none, .inl (n+1) => some (.inl n)
  | some _, .inl n => some (.inl n)
  | none, .inr fv' => some (.inr fv')
  | some fv, .inr fv' => if fv == fv' then none else some (.inr fv')

def find? : VLCtx → Nat ⊕ FVarId → Option (VLocalDecl × Nat)
  | [], _ => none
  | (ofv, d) :: Λ, v =>
    match next ofv v with
    | none => some (d, 0)
    | some v => do let (d, i) ← find? Λ v; some (d, i + d.depth)

end VLCtx

def TrProj (Δ : VLCtx) (structName : Name) (idx : Nat) (e : VExpr) : VExpr → Prop := sorry

variable (Us : List Name) in
inductive TrExpr : VLCtx → Expr → VExpr → Prop
  | bvar : Δ.find? (.inl i) = some (d, n) → TrExpr Δ (.bvar i) (d.value.liftN n)
  | fvar : Δ.find? (.inr fv) = some (d, n) → TrExpr Δ (.fvar fv) (d.value.liftN n)
  | sort : VLevel.ofLevel Us u = some u' → TrExpr Δ (.sort u) (.sort u')
  | const : us.mapM (VLevel.ofLevel Us) = some us' → TrExpr Δ (.const c us) (.const c us')
  | app : TrExpr Δ f f' → TrExpr Δ a a' → TrExpr Δ (.app f a) (.app f' a')
  | lam :
    TrExpr Δ ty ty' → TrExpr ((none, .vlam ty') :: Δ) body body' →
    TrExpr Δ (.lam name ty body bi) (.lam ty' body')
  | forallE :
    TrExpr Δ ty ty' → TrExpr ((none, .vlam ty') :: Δ) body body' →
    TrExpr Δ (.forallE name ty body bi) (.forallE ty' body')
  | letE :
    TrExpr Δ ty ty' → TrExpr Δ val val' →
    TrExpr ((none, .vlet ty' val') :: Δ) body body' →
    TrExpr Δ (.letE name ty val body bi) body'
  | lit : TrExpr Δ l.toConstructor e → TrExpr Δ (.lit l) e
  | proj : TrExpr Δ e e' → TrProj Δ s i e' e'' → TrExpr Δ (.proj s i e) e''
