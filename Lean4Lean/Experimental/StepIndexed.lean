module

public import Lean4Lean.Experimental.SExpr

@[expose] public section

namespace Lean4Lean

namespace SExpr
variable [Params]

structure Classifier' where
  level : SLevel
  HasTy' (e : SExpr) : Prop
def Classifier (_Γ : List SExpr) (_A : SExpr) := Classifier'

def Classifier.HasTy (C : Classifier Γ A) (e : SExpr) : Prop := Γ ⊢ e : A ∧ C.HasTy' e

-- structure LogRel where
--   IsTy (Γ : List SExpr) (A : SExpr) (R : Classifier Γ A) : Prop

-- def IsTyNormal (R : LogRel) (Γ : List SExpr) : SExpr → Prop
--   | .sort u, l => R.level = u.succ
--   | .forallE A B, l => ∃ u v, Γ ⊢ A ▷* .sort u ∧ A::Γ ⊢ B ▷* .sort v ∧
--     A::Γ ⊢ B :↑ .sort v ∧ ∃ K, R.IsTy Γ A K ∧ ∃ K', R.IsTy (A::Γ) B K' ∧ l = u.imax v
--   | _, _ => True

-- def IsTy (R : LogRel) (Γ : List SExpr) (A : SExpr) (u : SLevel) (K : Classifier Γ A u) : Prop :=
--   Γ ⊢ A ▷* .sort u ∧ Γ ⊢ A :↑ .sort u ∧
--     ∀ A', Γ ⊢ A ⤳* A' → Γ ⊢ A ≡ A' :↑ .sort u ∧ IsTyNormal R Γ A' u

-- def HasTyNormal (R : LogRel) (Γ : List SExpr) (e : SExpr) : SExpr → Prop
--   | .sort u => R.IsTy Γ e u {}
--   | .forallE A B => ∃ u v, Γ ⊢ A ▷* .sort u ∧ A::Γ ⊢ B ▷* .sort v ∧
--     A::Γ ⊢ B :↑ .sort v ∧ R.IsTy Γ A u ∧ R.IsTy (A::Γ) B v
--   | _ => True

-- def HasTy (R : LogRel) (Γ : List SExpr) (e A : SExpr) (u : SLevel) : Prop :=
--   IsTy R Γ A u ∧ Γ ⊢ e :↑ A ∧ ∀ A', Γ ⊢ A ⤳* A' → HasTyNormal R Γ e A'

-- def logRel : Nat → LogRel
--   | 0 => { IsTy _ _ _ _ := True }
--   | n+1 => { IsTy := IsTy (logRel n), HasTy := HasTy (logRel n) }

def NormalType : SExpr → Prop | .sort _ | .forallE .. => True | _ => False

noncomputable def normalize (Γ : List SExpr) (A : SExpr) : Option SExpr :=
  open Classical in if h : ∃ A', NormalType A' ∧ Γ ⊢ A ⤳* A' then some h.choose else none

theorem normalize_prop (h1 : normalize Γ A = some A') : NormalType A' ∧ Γ ⊢ A ⤳* A' := by
  unfold normalize at h1; split at h1 <;> cases h1
  rename_i h; exact h.choose_spec

coinductive IsTy' : ∀ Γ A, Classifier Γ A → Prop where
  | sort : Γ ⊢ A ▷* .sort u → normalize Γ A = some (.sort l) → u = l.succ →
    IsTy' Γ A { level := u, HasTy' _ := True }
  | forallE : Γ ⊢ A ▷* .sort u → normalize Γ A = some (.forallE A B) →
    IsTy' Γ A CA → IsTy' (A::Γ) B CB → u = CA.level.imax CB.level →
    IsTy' Γ A { level := u, HasTy' f := ∀ x, CA.HasTy x → CB.HasTy (f.app x) }
  | stuck : Γ ⊢ A ▷* .sort u → normalize Γ A = none →
    IsTy' Γ A { level := u, HasTy' _ := True }

axiom IsTy (Γ : List SExpr) (A : SExpr) (C : Classifier Γ A) : Prop
axiom IsTyN (Γ : List SExpr) (A : SExpr) (C : Classifier Γ A) : Prop

axiom IsTy.def : IsTy Γ A C ↔ Γ ⊢ A ▷* .sort C.level ∧
  match normalize Γ A with
  | some (.sort l) => C = {
      level := l.succ
      HasTy' e := ∃ C, C.level = l ∧ IsTy Γ e C }
  | some (.forallE A B) => ∃ CA CB, IsTy Γ A CA ∧ IsTy (A::Γ) B CB ∧ C = {
      level := CA.level.imax CB.level
      HasTy' f := ∀ x, CA.HasTy x → CB.HasTy (f.app x) }
  | _ => C.HasTy' = fun _ => True

-- #check IsTy'.coinduct

-- example (Γ Ω Z)
--     (h0 : Γ ⊢ Ω ▷* .sort u)
--     (h1 : normalize Γ Ω = some (.forallE Ω Z))
--     (h2 : ∀ e, ¬Γ ⊢ e : Z)
--     (hZ1 : normalize Γ Z = none)
--     (hZ2 : ∀ Γ, Γ ⊢ ℤ ▷* .sort u) : False := by
--   have {C} (H : IsTy' Γ Ω C) : False := by
--     have := IsTy'.forallE h0 h1 H _ _
--     refine IsTy'.coinduct (fun Γ' A' _ => True) ?_ _ _ _ trivial
--     intro _ _ C _
--     refine .inr <| .inl ⟨_, _, _, _, _, h1, ⟨rfl, rfl⟩, _⟩


-- theorem IsTy.uniq : IsTy Γ A C₁ → IsTy Γ A C₂ → C₁ = C₂ := by
--   intro H1 H2
