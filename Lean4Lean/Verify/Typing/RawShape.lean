import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Theory.Inductive.CaseProjections
import Lean4Lean.Theory.Inductive.RawShape

/-! Two translations of the same source agree on their constructor skeleton
(`VExpr.RawShapeRel`): translation is structural, and a projection translates to the primitive
`.proj` node. -/

namespace Lean4Lean
open Lean

inductive TrExprS.RawShapeDecl : VLocalDecl → VLocalDecl → Prop
  | vlam : RawShapeDecl (.vlam ty) (.vlam ty')
  | vlet : VExpr.RawShapeRel val val' → RawShapeDecl (.vlet ty val) (.vlet ty' val')

inductive TrExprS.RawShapeCtx : VLCtx → VLCtx → Prop
  | base : RawShapeCtx Δ Δ
  | cons : RawShapeCtx Δ₁ Δ₂ → RawShapeDecl d₁ d₂ →
      RawShapeCtx ((ofv, d₁) :: Δ₁) ((ofv, d₂) :: Δ₂)

theorem TrExprS.RawShapeCtx.find?_rel (hΔ : RawShapeCtx Δ₁ Δ₂)
    (H1 : Δ₁.find? v = some (e₁, A₁)) (H2 : Δ₂.find? v = some (e₂, A₂)) :
    VExpr.RawShapeRel e₁ e₂ := by
  induction hΔ generalizing v e₁ e₂ A₁ A₂ with
  | base => cases H1.symm.trans H2; exact .refl _
  | @cons _ _ _ _ ofv _ hd ih =>
    revert H1 H2
    simp [VLCtx.find?]
    split
    · rintro ⟨⟩ ⟨⟩
      cases hd with
      | vlam => exact .bvar
      | vlet h => exact h
    · simp
      rintro _ _ h1 rfl rfl _ _ h2 rfl rfl
      have h := ih h1 h2
      cases hd <;> exact h.liftN

theorem TrExprS.IsUniqueCtx.rawShape (H : IsUniqueCtx Δ₁ Δ₂) : RawShapeCtx Δ₁ Δ₂ := by
  induction H with
  | base => exact .base
  | cons _ hd ih =>
    cases hd with
    | vlam => exact .cons ih .vlam
    | vlet => exact .cons ih (.vlet (.refl _))

/-- Two syntactic translations agree on their constructor skeleton. The context
relation permits different translated values in preceding let declarations. -/
theorem TrSyn.rawShape {Us : List Name} (hΔ : TrExprS.RawShapeCtx Δ₁ Δ₂)
    (H1 : TrSyn Us Δ₁ e e₁) (H2 : TrSyn Us Δ₂ e e₂) : VExpr.RawShapeRel e₁ e₂ := by
  induction H1 generalizing Δ₂ e₂ with
  | bvar h => cases H2 with | bvar h' => exact hΔ.find?_rel h h'
  | fvar h => cases H2 with | fvar h' => exact hΔ.find?_rel h h'
  | sort => cases H2; exact .sort
  | const h => cases H2 with | const h' => cases h.symm.trans h'; exact .const
  | app _ _ ih1 ih2 => cases H2 with | app h1 h2 => exact .app (ih1 hΔ h1) (ih2 hΔ h2)
  | lam => cases H2; exact .lam
  | forallE _ _ _ ih => cases H2 with | forallE _ h2 => exact .forallE (ih (hΔ.cons .vlam) h2)
  | letE _ _ _ _ ih2 ih3 =>
    cases H2 with | letE _ hv hb => exact ih3 (hΔ.cons (.vlet (ih2 hΔ hv))) hb
  | lit _ ih => cases H2 with | lit h => exact ih hΔ h
  | mdata _ ih => cases H2 with | mdata h => exact ih hΔ h
  | proj => cases H2; exact .proj

/-- Two translations agree on their constructor skeleton. -/
theorem TrExprS.rawShape (hΔ : TrExprS.RawShapeCtx Δ₁ Δ₂)
    (H1 : TrExprS env Us Δ₁ e e₁) (H2 : TrExprS env Us Δ₂ e e₂) :
    VExpr.RawShapeRel e₁ e₂ :=
  H1.toTrSyn.rawShape hΔ H2.toTrSyn

end Lean4Lean
