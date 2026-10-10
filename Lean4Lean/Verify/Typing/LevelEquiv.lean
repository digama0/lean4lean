import Lean4Lean.Theory.Typing.LevelEquiv
import Lean4Lean.Verify.Typing.Lemmas

/-!
# Syntactic facts about translation

* `TrExprS.instL_lequiv`: the translation of a level-instantiated expression is `LEquiv` to the
  syntactic level instantiation of the translation of the original.
-/

namespace Lean4Lean
open VEnv Lean

/-! ### Level instantiation -/

section
variable {Us ps : List Name} {ls : List Level} {ls' : List VLevel}
  (Hls : ls.mapM (VLevel.ofLevel Us) = some ls')
  (eq : ps.length = ls.length)
include Hls eq

/-- Two translations, of an expression and of its level instantiation, in level-equivalent
contexts, are level equivalent. -/
theorem TrExprS.instL_lequiv_of (H : TrExprS env ps Δ e e')
    (hΔ₂ : VLCtx.LEquiv Us.length Δ₂ (Δ.instL ls'))
    (H2 : TrExprS env Us Δ₂ (e.instantiateLevelParams ps ls) e₁) :
    VExpr.LEquiv Us.length e₁ (e'.instL ls') :=
  H.toTrSyn.instL_lequiv_of Hls eq hΔ₂ H2.toTrSyn

theorem TrExprS.instL_lequiv (henv : VEnv.WF env) (hΔ : VLCtx.WF env ls'.length Δ)
    (H : TrExprS env ps Δ e e') :
    ∃ e₁, TrExprS env Us (Δ.instL ls') (e.instantiateLevelParams ps ls) e₁ ∧
      VExpr.LEquiv Us.length e₁ (e'.instL ls') :=
  let ⟨e₁, h1, _⟩ := H.instL henv hΔ Hls eq
  ⟨e₁, h1, H.instL_lequiv_of Hls eq (.refl _) h1⟩

end

/-! ### Inverse bound-variable weakening -/

theorem VLCtx.BVLift.find?_exists (W : VLCtx.BVLift Δ Δ' dn dk n k)
    (hv : ∀ i, v = .inl i → i < dk) (h : ∃ x, Δ'.find? v = some x) : ∃ x, Δ.find? v = some x := by
  induction W generalizing v with
  | refl => exact h
  | skip d _ ih =>
    obtain _ | fv := v
    · cases Nat.not_lt_zero _ (hv _ rfl)
    · have ⟨_, h⟩ := h
      simp [VLCtx.find?, VLCtx.next, bind] at h
      obtain ⟨_, _, h, -⟩ := h
      exact ih nofun ⟨_, h⟩
  | cons d _ ih =>
    obtain (_ | i) | fv := v
    · exact ⟨_, rfl⟩
    · have ⟨_, h⟩ := h
      simp [VLCtx.find?, VLCtx.next, bind] at h
      obtain ⟨_, _, h, -⟩ := h
      have ⟨⟨e, A⟩, h'⟩ :=
        ih (v := .inl i) (fun _ e => Nat.lt_of_succ_lt_succ (by cases e; exact hv _ rfl)) ⟨_, h⟩
      exact ⟨(e.liftN d.depth, A.liftN d.depth), by simp [VLCtx.find?, VLCtx.next, bind, h']⟩
    · have ⟨_, h⟩ := h
      simp [VLCtx.find?, VLCtx.next, bind] at h
      obtain ⟨_, _, h, -⟩ := h
      have ⟨⟨e, A⟩, h'⟩ := ih (v := .inr fv) nofun ⟨_, h⟩
      exact ⟨(e.liftN d.depth, A.liftN d.depth), by simp [VLCtx.find?, VLCtx.next, bind, h']⟩

theorem Closed.of_closed_looseBVarRange {e : Expr} {k j : Nat}
    (hc : Closed e k) (hb : e.looseBVarRange' ≤ j) : Closed e j := by
  induction e generalizing k j with
  | bvar => simp [Closed, Expr.looseBVarRange'] at hc hb ⊢; omega
  | mvar => exact hc.elim
  | app _ _ ih1 ih2 =>
    simp only [Expr.looseBVarRange', Nat.max_le] at hb
    exact ⟨ih1 hc.1 hb.1, ih2 hc.2 hb.2⟩
  | lam _ _ _ _ ih1 ih2 | forallE _ _ _ _ ih1 ih2 =>
    simp only [Expr.looseBVarRange', Nat.max_le] at hb
    exact ⟨ih1 hc.1 hb.1, ih2 hc.2 (by omega)⟩
  | letE _ _ _ _ _ ih1 ih2 ih3 =>
    simp only [Expr.looseBVarRange', Nat.max_le] at hb
    exact ⟨ih1 hc.1 hb.1.1, ih2 hc.2.1 hb.1.2, ih3 hc.2.2 (by omega)⟩
  | proj _ _ _ ih | mdata _ _ ih => exact ih hc hb
  | _ => trivial

end Lean4Lean
