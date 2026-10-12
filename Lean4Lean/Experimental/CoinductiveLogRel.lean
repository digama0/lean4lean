import Lean4Lean.Theory.Typing.HeadReduction

namespace Lean4Lean
namespace VEnv

variable [Params]
open Params

local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ⤳* " e2:36 => WHRedS Γ e1 e2

structure Classifier' where
  HasTy : VExpr → Prop
  IsTy : List VExpr → VExpr → VLevel → Prop
def Classifier (_Γ : List VExpr) (_A : VExpr) (_u : VLevel) := Classifier'

/-
def IsTyNormal (R : Classifier Γ A u) : VExpr → VLevel → Prop
  | .sort u, l => l = u.succ
  | .forallE A B, l => ∃ u v, Γ ⊢ A ▷* .sort u ∧ A::Γ ⊢ B ▷* .sort v ∧
    A::Γ ⊢ B : .sort v ∧ R.IsTy Γ A u ∧ R.IsTy (A::Γ) B v ∧ l = u.imax v
  | _, _ => True

def IsTy (R : LogRel) (Γ : List VExpr) (A : VExpr) (u : VLevel) : Prop :=
  Γ ⊢ A ▷* .sort u ∧ Γ ⊢ A : .sort u ∧
    ∀ A', Γ ⊢ A ⤳* A' → Γ ⊢ A ≡ A' : .sort u ∧ IsTyNormal R Γ A' u

def HasTyNormal (R : LogRel) (Γ : List VExpr) (e : VExpr) : VExpr → Prop
  | .sort u => R.IsTy Γ e u
  | .forallE A B => ∃ u v, Γ ⊢ A ▷* .sort u ∧ A::Γ ⊢ B ▷* .sort v ∧
    A::Γ ⊢ B : .sort v ∧ R.IsTy Γ A u ∧ R.IsTy (A::Γ) B v
  | _ => True

def HasTy (R : LogRel) (Γ : List VExpr) (e A : VExpr) (u : VLevel) : Prop :=
  IsTy R Γ A u ∧ Γ ⊢ e : A ∧ ∀ A', Γ ⊢ A ⤳* A' → HasTyNormal R Γ e A'

coinductive LogRel : ∀ Γ A u, Classifier Γ A u → Prop where
  | mk : IsTy R Γ A u ∧ Γ ⊢ e : A ∧ ∀ A', Γ ⊢ A ⤳* A' → HasTyNormal R Γ e A'
  -- | stuck :
  --   (∀ A', Γ ⊢ A ⤳* A' → ¬NormalType A') →
  --   Γ ⊢ A ▷* .sort u → Γ ⊢ A : .sort u → LogRel Γ A u {}
  | sort : Γ ⊢ A ⤳* .sort l → Γ ⊢ A ▷* .sort l.succ → Γ ⊢ A ≡ .sort l : .sort l.succ →
    LogRel Γ A (.succ l) { EqTy' A := Γ ⊢ A ⤳* .sort l }
  | forallE
    {RA : ∀ {ρ Δ}, Ctx.Lift' ρ Γ Δ → Classifier Δ (A.lift' ρ) u}
    {RB : ∀ {ρ Δ} (W : Ctx.Lift' ρ Γ Δ) {a},
      (@RA ρ Δ W).HasTy a → Classifier Δ ((B.lift' ρ.cons).inst a) v} :
    Γ ⊢ X ⤳* .forallE A B → Γ ⊢ X ▷* .sort (.imax u v) →
    A::Γ ⊢ B ▷* .sort v → A::Γ ⊢ B : .sort v → Γ ⊢ X ≡ .forallE A B : .sort (.imax u v) →
    (∀ {ρ Δ} W, LogRel Δ (A.lift' ρ) u (@RA ρ Δ W)) →
    (∀ {ρ Δ} W {a} (ha : (@RA ρ Δ W).HasTy a), LogRel Δ ((B.lift' ρ.cons).inst a) v (RB W ha)) →
    (∀ {ρ Δ} W {a b} (ab : (@RA ρ Δ W).DefEq a b), (RB W ab.left).EqTy ((B.lift' ρ.cons).inst b)) →
    LogRel Γ X (.imax u v) (.forallE @RA @RB)

-- def logRel : Nat → LogRel
--   | 0 => { IsTy _ _ _ := True, HasTy _ _ _ _ := True }
--   | n+1 => { IsTy := IsTy (logRel n), HasTy := HasTy (logRel n) }
-/
