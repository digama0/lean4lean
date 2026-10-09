import Lean4Lean.Theory.Inductive.Restoration

/-! Universe instantiation commutes with total restoration. -/

namespace Lean4Lean
namespace VExpr

theorem instL_subst (e : VExpr) (σ : Subst) (levels : List VLevel) :
    (e.subst σ).instL levels = (e.instL levels).subst (fun i => (σ i).instL levels) := by
  have hlift (σ : Subst) : (fun i => (σ.lift i).instL levels) =
      Subst.lift (fun i => (σ i).instL levels) := by
    funext i
    cases i <;> simp [Subst.lift, instL]
  induction e generalizing σ with
  | bvar | sort | const | elim => rfl
  | app _ _ ihf iha => simp only [subst, instL, ihf, iha]
  | lam _ _ ihd ihb | forallE _ _ ihd ihb => simp only [subst, instL, ihd, ihb, hlift]
  | proj _ _ _ ih => simp only [subst, instL, ih]

end VExpr
namespace InductiveSignature

theorem instantiateParams_instL (e : VExpr) (args : List VExpr) (levels : List VLevel) :
    (instantiateParams e args).instL levels =
      instantiateParams (e.instL levels) (args.map (·.instL levels)) := by
  let σ : VExpr.Subst := fun i =>
    if hi : i < args.length then args[args.length - 1 - i] else .bvar (i - args.length)
  change (e.subst σ).instL levels = _
  rw [VExpr.instL_subst]
  unfold instantiateParams
  dsimp only [σ]
  congr 1
  funext i
  simp only [List.length_map]
  split
  · simp only [List.getElem_map]
  · rfl

private theorem HeadSpecialization.apply_instL (h : HeadSpecialization)
    (levels packed : List VLevel) (args : List VExpr) :
    (h.apply levels args).map (·.instL packed) =
      h.apply (levels.map (·.inst packed)) (args.map (·.instL packed)) := by
  unfold HeadSpecialization.apply
  simp only [List.length_map]
  split
  · rfl
  · simp only [Option.pure_def, Option.map_some, VExpr.instL_mkApps, VExpr.instL, List.map_append,
      List.map_map, Function.comp_def, VLevel.inst_inst, List.map_take, List.map_drop,
      instantiateParams_instL, VExpr.instL_instL]

/-- The restoration program commutes with occurrence universe substitution,
including specialized head levels and simultaneous constructor parameters. -/
theorem Restoration.expr_instL (r : Restoration) (e : VExpr) (packed : List VLevel) :
    (r.expr e).map (·.instL packed) = r.expr (e.instL packed) := by
  suffices ∀ args, (Restoration.expr.go r e args).map (·.instL packed) =
      Restoration.expr.go r (e.instL packed) (args.map (·.instL packed)) from this []
  induction e with
  | app fn arg ihf iha =>
    intro args
    simp only [VExpr.instL, Restoration.expr.go]
    cases h : Restoration.expr.go r arg [] with
    | none =>
      have ha := iha []
      simp only [h, List.map_nil, Option.map_none] at ha
      simp only [bind, ← ha]
      rfl
    | some a =>
      have ha := iha []
      simp only [h, List.map_nil, Option.map_some] at ha
      simp only [bind, Option.bind_some, ← ha]
      exact ihf (a :: args)
  | const name levels =>
    intro args
    simp only [VExpr.instL, Restoration.expr.go]
    split
    · exact HeadSpecialization.apply_instL _ _ _ _
    · simp [VExpr.instL_mkApps, VExpr.instL]
  | bvar | sort | elim => intro args; simp [Restoration.expr.go, VExpr.instL_mkApps, VExpr.instL]
  | lam domain body ihd ihb | forallE domain body ihd ihb =>
    intro args
    simp only [VExpr.instL, Restoration.expr.go]
    have hd := ihd []
    have hb := ihb []
    simp only [List.map_nil] at hd hb
    rw [← hd, ← hb]
    cases Restoration.expr.go r domain [] <;> cases Restoration.expr.go r body [] <;>
      simp [VExpr.instL_mkApps, VExpr.instL]
  | proj name field major ih =>
    intro args
    simp only [VExpr.instL, Restoration.expr.go]
    have hm := ih []
    simp only [List.map_nil] at hm
    rw [← hm]
    cases Restoration.expr.go r major [] <;> simp [VExpr.instL_mkApps, VExpr.instL]

end InductiveSignature
end Lean4Lean
