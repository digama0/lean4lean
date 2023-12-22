import Lean4Lean.Expr
import Lean4Lean.Theory.VExpr

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

def VLocalDecl.type' : VLocalDecl → VExpr
  | .vlam A
  | .vlet A _ => A

def VLocalDecl.type : VLocalDecl → VExpr
  | .vlam A => A.lift
  | .vlet A _ => A

def VLCtx := List (Option FVarId × VLocalDecl)

namespace VLCtx

def next : Option FVarId → Nat ⊕ FVarId → Option (Nat ⊕ FVarId)
  | none, .inl 0 => none
  | none, .inl (n+1) => some (.inl n)
  | some _, .inl n => some (.inl n)
  | none, .inr fv' => some (.inr fv')
  | some fv, .inr fv' => if fv == fv' then none else some (.inr fv')

def find? : VLCtx → Nat ⊕ FVarId → Option (VExpr × VExpr)
  | [], _ => none
  | (ofv, d) :: Δ, v =>
    match next ofv v with
    | none => some (d.value, d.type)
    | some v => do let (e, A) ← find? Δ v; some (e.liftN d.depth, A.liftN d.depth)

def fvars (Δ : VLCtx) : List FVarId := Δ.filterMap (·.1)

def toCtx : VLCtx → List VExpr
  | [] => []
  | (_, .vlam ty) :: Δ => ty :: VLCtx.toCtx Δ
  | (_, .vlet _ _) :: Δ => VLCtx.toCtx Δ

theorem lookup_isSome : ∀ {Δ : VLCtx}, (Δ.lookup (some fv)).isSome = (Δ.find? (.inr fv)).isSome
  | [] => rfl
  | (ofv, d) :: Δ => by
    simp [List.lookup, find?, next]
    cases ofv with
    | none =>
      simp [show (some fv == none) = false from rfl, lookup_isSome]
      cases find? Δ (.inr fv) <;> simp [bind]
    | some fv' =>
      simp [show (some fv == some fv') = (fv == fv') from rfl, beq_comm fv]
      cases fv' == fv <;> simp [lookup_isSome]
      cases find? Δ (.inr fv) <;> simp [bind]

theorem lookup_eq_none {Δ : VLCtx} : Δ.lookup (some fv) = none ↔ Δ.find? (.inr fv) = none := by
  simp only [← Option.not_isSome_iff_eq_none, lookup_isSome]

end VLCtx
