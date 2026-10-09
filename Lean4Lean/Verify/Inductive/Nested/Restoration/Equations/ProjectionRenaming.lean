import Lean4Lean.Verify.Inductive.Nested.Restoration.Equations.AuxiliaryConstructors
import Lean4Lean.Verify.Inductive.Nested.Restoration.Equations.ProjNames

/-! Beta reduction and the projection clause of a source structure.

The lowered constructor type of a source structure restores syntactically to the source
constructor type. The interpretation of the lowered constructor type by an agreeing
interpretation beta reduces to its restoration (`Restoration.Agrees.expr_betaRed`): each inserted
restoration lambda `λ params, target levels args` meets a complete parameter spine. Field types
commute with the interpretation (`VProjectionInfo.fieldType_interpret`), and field types computed
from a beta reduct of the constructor type are beta reducts of the field types
(`VProjectionInfo.fieldType_betaRed`), as instantiating parameters and preceding fields is
substitution. The projection clause for well-formed contexts (`VEnv.TypedCtx`) receives the
well-formedness of the image context in every projection rule, so beta subject reduction
(`VExpr.BetaRed.simAt`) applies and the projection clause of a source structure needs no
hypothesis (`ProjectionClause.of_ctorType_betaRed`). Auxiliary structure-like families are
handled in `Nested/Restoration/AuxiliaryProjections.lean`.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VProjectionInfo

theorem instantiateProjectionParameters_betaRed :
    ∀ (params : List VExpr) {A B X : VExpr}, VExpr.BetaRed A B →
      instantiateProjectionParameters A params = some X →
      ∃ Y, instantiateProjectionParameters B params = some Y ∧ VExpr.BetaRed X Y
  | [], A, B, X, h, hX => by
    simp only [instantiateProjectionParameters, Option.some.injEq] at hX ⊢
    subst hX
    exact ⟨_, rfl, h⟩
  | p :: ps, A, B, X, h, hX => by
    cases A with
    | forallE d b =>
      obtain ⟨d', b', rfl, -, hb⟩ := h.forallE_inv
      simp only [instantiateProjectionParameters] at hX ⊢
      exact instantiateProjectionParameters_betaRed ps (hb.instN p 0) hX
    | _ => simp [instantiateProjectionParameters] at hX

theorem instantiateProjectionFields_betaRed {typeName : Name} {major : VExpr} {wanted : Nat} :
    ∀ (fuel : Nat) {current : Nat} {A B X : VExpr}, VExpr.BetaRed A B →
      instantiateProjectionFields typeName major wanted current fuel A = some X →
      ∃ Y, instantiateProjectionFields typeName major wanted current fuel B = some Y ∧
        VExpr.BetaRed X Y
  | 0, _, _, _, _, _, hX => by simp [instantiateProjectionFields] at hX
  | fuel + 1, current, A, B, X, h, hX => by
    cases A with
    | forallE d b =>
      obtain ⟨d', b', rfl, hd, hb⟩ := h.forallE_inv
      simp only [instantiateProjectionFields] at hX ⊢
      by_cases hw : wanted = current
      · rw [if_pos hw] at hX ⊢
        cases hX
        exact ⟨_, rfl, hd⟩
      · rw [if_neg hw] at hX ⊢
        exact instantiateProjectionFields_betaRed fuel (hb.instN _ 0) hX
    | _ => simp [instantiateProjectionFields] at hX

/-- Field types computed from a beta-reduced constructor type are beta
reducts of the field types of the unreduced constructor type. -/
theorem fieldType_betaRed {info : VProjectionInfo} {ctorType' : VExpr}
    {typeName : Name} {levels : List VLevel} {params : List VExpr} {index : Nat}
    {major X : VExpr} (h : VExpr.BetaRed info.ctorType ctorType')
    (H : info.fieldType typeName levels params index major = some X) :
    ∃ Y, { info with ctorType := ctorType' }.fieldType typeName levels params index major =
      some Y ∧ VExpr.BetaRed X Y := by
  unfold fieldType at H ⊢
  split at H
  · cases H
  · next hvalid =>
    rw [if_neg hvalid]
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at H ⊢
    obtain ⟨tail, htail, hX⟩ := H
    obtain ⟨tail', htail', hrel⟩ := instantiateProjectionParameters_betaRed params (h.instL levels) htail
    obtain ⟨Y, hY, hXY⟩ := instantiateProjectionFields_betaRed _ hrel hX
    exact ⟨Y, ⟨tail', htail', hY⟩, hXY⟩

end VProjectionInfo

/-! ### The projection clause of a source structure -/

namespace VEnv.Interpretation

/-- A projection whose owner and constructor the interpretation fixes, registered in `envS` with
a constructor type that is a beta reduct of the interpreted constructor type (of the same
syntactic arity), satisfies the projection clause in well-formed contexts, by beta subject
reduction of `envS`. -/
theorem ProjectionClause.of_ctorType_betaRed {envS : VEnv} {I : Interpretation}
    {typeName : Name} {info : VProjectionInfo} {ctorType' : VExpr}
    (henv : envS.Ordered) (hβ : ∀ U, envS.BetaSubjectReduction U)
    (hI : I.Closed) (hT : I.PreservesTelescopes)
    (hS : envS.projections typeName { info with ctorType := ctorType' })
    (htn : I.consts typeName = none) (hrtn : I.rename typeName = typeName)
    (hptn : I.projOwner typeName = typeName)
    (hctorName : I.consts info.ctorName = none) (hrctor : I.rename info.ctorName = info.ctorName)
    (hclosed : ctorType'.Closed) (harity : ctorType'.forallArity = info.ctorType.forallArity)
    (hBR : VExpr.BetaRed (I.expr info.ctorType) ctorType') :
    I.ProjectionClause envS envS.TypedCtx typeName info where
  projDF := by
    intro U Γ levels params index sourceMajor fieldType fieldLevel major indexArgs major'
      hΓ hlevels huvars hparams hindices hfield _ hguard ihField ihLeft ihRight
    have h1 := VProjectionInfo.fieldType_interpret (typeName := typeName) (levels := levels)
      (params := params) (index := index) (major := sourceMajor) hI hT info
    rw [hfield, hptn] at h1
    obtain ⟨fieldType', hfield', hXY⟩ :=
      VProjectionInfo.fieldType_betaRed (ctorType' := ctorType') hBR h1
    have hfield'' : ({ info with ctorType := ctorType' } : VProjectionInfo).fieldType typeName
        levels (params.map I.expr) index (I.expr sourceMajor) = some fieldType' := hfield'
    have hdefF := (hXY.simAt henv (hβ U) hΓ _ ihField).symm
    simp only [expr_mkApps, List.map_append, expr_const_none htn, hrtn] at ihLeft ihRight
    simp only [expr_proj, hptn]
    exact .defeqDF hdefF (.projDF hS hlevels huvars (by simpa using hparams)
      (by simpa using hindices) hfield'' hdefF.hasType.1 ihLeft ihRight hclosed hguard)
  projIota := by
    intro U Γ index levels args field fieldType _ ih1 h3 ih2
    simp only [expr_proj, expr_mkApps, expr_const_none hctorName, hrctor, hptn] at ih1 ⊢
    exact .projIota (info := { info with ctorType := ctorType' }) hS ih1 (by simp [h3]) ih2
  structEta := by
    intro U Γ levels params e _ h2 h3 ih1 ih2
    have hnf : ({ info with ctorType := ctorType' } : VProjectionInfo).numFields =
        info.numFields := by
      simp only [VProjectionInfo.numFields, harity]
    simp only [expr_proj, expr_mkApps, List.map_append, List.map_map, Function.comp_def,
      expr_const_none hctorName, expr_const_none htn, hrctor, hrtn, hptn] at ih1 ih2 ⊢
    rw [← hnf] at ih2 ⊢
    exact .structEta hS (by simpa using h2) h3 ih1 ih2
  unitLike := by
    intro U Γ levels params e e' _ h2 h3 h4 ih1 ih2
    have hnf : ({ info with ctorType := ctorType' } : VProjectionInfo).numFields =
        info.numFields := by
      simp only [VProjectionInfo.numFields, harity]
    simp only [expr_mkApps, expr_const_none htn, hrtn] at ih1 ih2 ⊢
    exact .unitLike hS (by simpa using h2) h3 (hnf.trans h4) ih1 ih2

end VEnv.Interpretation

end Lean4Lean
