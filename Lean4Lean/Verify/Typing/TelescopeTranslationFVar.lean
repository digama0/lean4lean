import Lean4Lean.Verify.Typing.TelescopeTranslation

/-!
# Telescope translations: free-variable lemmas

Auxiliary lemmas for producing the telescope certificate `TelTrN` from a run of the checker,
which opens one free variable per binder: instantiation by free variables, deletion of an unused binder under instantiation,
and syntactic uniqueness of translations.
-/

namespace Lean4Lean
open Lean

namespace TelTrFVar

theorem instantiate1'_fvar_forallE {e : Expr} {f : FVarId} {k : Nat}
    (h : e.instantiate1' (.fvar f) k = .forallE n d b bi) :
    ∃ d₀ b₀, e = .forallE n d₀ b₀ bi := by
  cases e with
  | bvar i =>
    simp only [Expr.instantiate1'] at h
    split at h
    · cases h
    · split at h
      · simp [Expr.liftLooseBVars'] at h
      · cases h
  | forallE n' d' b' bi' =>
    simp only [Expr.instantiate1', Expr.forallE.injEq] at h
    obtain ⟨rfl, -, -, rfl⟩ := h; exact ⟨_, _, rfl⟩
  | _ => simp [Expr.instantiate1'] at h

/-- Instantiating by free variables does not create a `forallE`. -/
theorem instantiateList_fvars_forallE {e : Expr} {as : List Expr} {k : Nat}
    (has : ∀ a ∈ as, ∃ f, a = .fvar f)
    (h : e.instantiateList as k = .forallE n d b bi) :
    ∃ d₀ b₀, e = .forallE n d₀ b₀ bi := by
  induction as generalizing e with
  | nil => exact ⟨_, _, h⟩
  | cons a as ih =>
    obtain ⟨f, rfl⟩ := has a (.head _)
    obtain ⟨d₁, b₁, h1⟩ := ih (fun a h => has a (.tail _ h)) h
    exact instantiate1'_fvar_forallE h1

/-- `instantiateList_instantiate1_comm` at an arbitrary depth. -/
theorem instantiateList_instantiate1_comm {e a : Expr} {as : List Expr} {k : Nat}
    (ha : a.looseBVarRange' = 0) (has : ∀ x ∈ as, x.looseBVarRange' = 0) :
    (e.instantiateList as (k + 1)).instantiate1' a k =
    (e.instantiate1' a k).instantiateList as k := by
  induction as generalizing e with
  | nil => rfl
  | cons x as ih =>
    simp only [Expr.instantiateList]
    rw [ih (fun y h => has y (.tail _ h)), Expr.instantiate1'_instantiate1',
      Expr.liftLooseBVars_eq_self (by simp [ha])]

/-- Deleting an unused binder commutes with instantiating the outer binders. -/
theorem instantiateList_delete {b₀ g : Expr} {as : List Expr}
    (hg : g.looseBVarRange' = 0) (has : ∀ x ∈ as, x.looseBVarRange' = 0) :
    ((b₀.liftLooseBVars' 0 1).instantiateList as 1).instantiate1' g =
    b₀.instantiateList as := by
  rw [instantiateList_instantiate1_comm (k := 0) hg has, Expr.instantiate1'_liftLooseBVars_0]

theorem FVarsIn.of_liftLooseBVars {P : FVarId → Prop} {e : Expr} {s d : Nat}
    (h : FVarsIn P (e.liftLooseBVars' s d)) : FVarsIn P e := by
  induction e generalizing s with
  | bvar => trivial
  | app _ _ ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩
  | lam _ _ _ _ ih1 ih2 | forallE _ _ _ _ ih1 ih2 => exact ⟨ih1 h.1, ih2 h.2⟩
  | letE _ _ _ _ _ ih1 ih2 ih3 => exact ⟨ih1 h.1, ih2 h.2.1, ih3 h.2.2⟩
  | mdata _ _ ih | proj _ _ _ ih => exact ih h
  | _ => exact h

theorem fvarsList_instantiateLevelParamsCore' {e : Expr} :
    (Expr.instantiateLevelParamsCore' red s e).fvarsList = e.fvarsList := by
  induction e <;> simp_all [Expr.instantiateLevelParamsCore', Expr.fvarsList]

theorem fvarsList_instantiateLevelParams {e : Expr} :
    (e.instantiateLevelParams ps ls).fvarsList = e.fvarsList := by
  rw [Expr.instantiateLevelParams_eq, fvarsList_instantiateLevelParamsCore']

end TelTrFVar

end Lean4Lean
