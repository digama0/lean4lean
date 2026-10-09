import Lean4Lean.Verify.Expr
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

def VLocalDecl.lift' : VLocalDecl → Lift → VLocalDecl
  | .vlam A, n => .vlam (A.lift' n)
  | .vlet A e, n => .vlet (A.lift' n) (e.lift' n)

def VLocalDecl.liftN : VLocalDecl → Nat → Nat → VLocalDecl
  | .vlam A, n, k => .vlam (A.liftN n k)
  | .vlet A e, n, k => .vlet (A.liftN n k) (e.liftN n k)

def VLocalDecl.inst : VLocalDecl → VExpr → (k : Nat := 0) → VLocalDecl
  | .vlam A, e₀, k => .vlam (A.inst e₀ k)
  | .vlet A e, e₀, k => .vlet (A.inst e₀ k) (e.inst e₀ k)

def VLocalDecl.instL : VLocalDecl → List VLevel → VLocalDecl
  | .vlam A, ls => .vlam (A.instL ls)
  | .vlet A e, ls => .vlet (A.instL ls) (e.instL ls)

@[reducible] def VLCtx := List (Option (FVarId × List FVarId) × VLocalDecl)

namespace VLCtx

def bvars : VLCtx → Nat
  | [] => 0
  | (none, _) :: Δ => bvars Δ + 1
  | (some _, _) :: Δ => bvars Δ

@[simp] theorem bvars_append (left right : VLCtx) :
    (left ++ right).bvars = left.bvars + right.bvars := by
  induction left with
  | nil => simp [bvars]
  | cons entry left ih =>
    rcases entry with ⟨ofv, d⟩
    cases ofv <;>
      simp [bvars, ih, Nat.add_comm, Nat.add_left_comm]

abbrev NoBV (Δ : VLCtx) : Prop := Δ.bvars = 0

theorem NoBV.leftOfAppend (left right : VLCtx)
    (H : (left ++ right).NoBV) : left.NoBV := by
  change (left ++ right).bvars = 0 at H
  change left.bvars = 0
  rw [bvars_append] at H
  exact Nat.eq_zero_of_add_eq_zero_right H

def next : Option (FVarId × List FVarId) → Nat ⊕ FVarId → Option (Nat ⊕ FVarId)
  | none, .inl 0 => none
  | none, .inl (n+1) => some (.inl n)
  | some _, .inl n => some (.inl n)
  | none, .inr fv' => some (.inr fv')
  | some (fv, _), .inr fv' => if fv == fv' then none else some (.inr fv')

def find? : VLCtx → Nat ⊕ FVarId → Option (VExpr × VExpr)
  | [], _ => none
  | (ofv, d) :: Δ, v =>
    match next ofv v with
    | none => some (d.value, d.type)
    | some v => do let (e, A) ← find? Δ v; some (e.liftN d.depth, A.liftN d.depth)

def liftVar (n k : Nat) : Nat ⊕ FVarId → Nat ⊕ FVarId
  | .inl i => .inl (if i < k then i else i + n)
  | .inr fv => .inr fv

def varToExpr : Nat ⊕ FVarId → Expr
  | .inl i => .bvar i
  | .inr fv => .fvar fv

def vlamName : VLCtx → Nat → Option (Option (FVarId × List FVarId))
  | [], _ => none
  | (_, .vlet ..) :: Δ, i
  | (_, .vlam ..) :: Δ, i+1 => vlamName Δ i
  | (ofv, .vlam ..) :: _, 0 => some ofv

def fvars (Δ : VLCtx) : List FVarId := Δ.filterMap (·.1.map (·.1))

@[simp] theorem fvars_nil : fvars [] = [] := rfl
@[simp] theorem fvars_cons_none {Δ : VLCtx} : fvars ((none, d) :: Δ) = fvars Δ := rfl
@[simp] theorem fvars_cons_some {Δ : VLCtx} :
    fvars ((some fv, d) :: Δ) = fv.1 :: fvars Δ := rfl

@[simp] theorem fvars_append (left right : VLCtx) :
    fvars (left ++ right) = fvars left ++ fvars right := by
  simp [fvars, List.filterMap_append]

def toCtx : VLCtx → List VExpr
  | [] => []
  | (_, .vlam ty) :: Δ => ty :: VLCtx.toCtx Δ
  | (_, .vlet _ _) :: Δ => VLCtx.toCtx Δ

@[simp] theorem toCtx_append (left right : VLCtx) :
    toCtx (left ++ right) = toCtx left ++ toCtx right := by
  induction left with
  | nil => rfl
  | cons entry left ih =>
    rcases entry with ⟨ofv, decl⟩
    cases decl <;> simp [toCtx, ih]

@[simp] theorem toCtx_map_anonymousLams (types : List VExpr) :
    VLCtx.toCtx (types.map fun type =>
      ((none, .vlam type) :
        Option (FVarId × List FVarId) × VLocalDecl)) = types := by
  induction types with
  | nil => rfl
  | cons type types ih => simp [VLCtx.toCtx, ih]

/-- A context made only of `vlam` entries named by a list of free variables has one typing-context
entry per declaration. -/
theorem toCtx_length_of_forall₂_vlam {fvars : List FVarId} {scope : VLCtx}
    (H : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type)) fvars scope) :
    scope.toCtx.length = scope.length := by
  induction H with
  | nil => rfl
  | cons h _ ih =>
    rcases h with ⟨deps, type, rfl⟩
    simp [VLCtx.toCtx, ih]

def instL (Δ : VLCtx) (ls : List VLevel) : VLCtx :=
  match Δ with
  | [] => []
  | (ofv, d) :: Δ => (ofv, d.instL ls) :: instL Δ ls

theorem find?_eq_some : (∃ x, Δ.find? (.inr fv) = some x) ↔ fv ∈ fvars Δ := by
  induction Δ with simp [find?] | cons d Δ ih
  match d with
  | (none, _) => simp [next, ← ih]; grind
  | (some (fv',  _), _) =>
    simp [next]; rw [@eq_comm _ fv]
    by_cases h : fv' == fv <;> simp [h] <;> simp at h <;> simp [h]; grind

theorem vlamName_mem_fvars :
    ∀ {Δ : VLCtx} {i}, Δ.vlamName i = some (some fv) → fv.1 ∈ fvars Δ
  | (none, .vlet ..) :: Δ, _, h
  | (none, .vlam ..) :: Δ, _+1, h => vlamName_mem_fvars (Δ := Δ) h
  | (some _, .vlet ..) :: Δ, _, h
  | (some _, .vlam ..) :: Δ, _+1, h => .tail _ <| vlamName_mem_fvars (Δ := Δ) h
  | (some _fv, .vlam ..) :: _, 0, rfl => .head _

end VLCtx
