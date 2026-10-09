import Lean4Lean.Theory.Typing.HeadInjectivity.Congruence

/-! # Field types of two projection typings are congruent

`fieldType_congr`: if two field types are computed by `VProjectionInfo.fieldType` from
pointwise-equivalent levels, pointwise definitionally equal parameters, and definitionally
equal source majors, then they are related by `CongrUB` at depth `0`.

The walk of `fieldType` only peels the syntactic `forallE` spine of the constructor type.
That spine is fixed by the raw constructor shape (`Ordered.projection_rawShape`): the
constructor type is `wrapForalls doms result` with `result` an application of a constant,
and instantiation keeps `result` an application of a constant (`HeadConst`), so no
parameter substituted for a variable can contribute binders to the spine. Both walks
therefore peel the same binders, and the invariant `SpineCongr` (same spine, domains and
result related by `CongrUB` at their depths) is preserved by each instantiation with a
`CongrUB`-related pair at depth `0`: parameters (leaves) and earlier projections
`proj typeName j sourceMajor` (projections of leaves). -/

namespace Lean4Lean
open Lean4Lean
namespace VEnv

/-- The raw shape of the constructor type recorded by projection metadata. -/
theorem Ordered.projection_rawShape {env : VEnv} (H : env.Ordered)
    (hprojection : env.projections name info) :
    ∃ doms result, info.ctorType = VExpr.wrapForalls doms result ∧
      info.nparams ≤ doms.length ∧ ∃ c ls, result.getAppFnArgs.1 = .const c ls := by
  induction H with
  | eliminator _ ih => exact ih hprojection
  | empty => cases hprojection
  | const _ _ hadd ih =>
    rw [VEnv.addConst_projections hadd] at hprojection
    exact ih hprojection
  | defeq _ _ ih => exact ih hprojection
  | @inductProjections base envTypes envCtors decl block _es
      hbase hctorsOrdered hsource htypesWF hconstructorUvars _hctorsWF _hparams hshape
      htypesSource hctorsSource hprojections htypes hctors ihBase ihCtors =>
    rw [VEnv.addProjections_iff] at hprojection
    rcases hprojection with hnew | hold
    · rcases hnew with ⟨entry, hentry, rfl, rfl⟩
      rw [hprojections] at hentry
      rcases VInductDecl.projectionEntries_origin hentry with
        ⟨type, htype, ctor, htypeCtors, rfl⟩
      obtain ⟨doms, result, h1, h2, _, h4⟩ := hshape type htype ctor (by simp [htypeCtors])
      exact ⟨doms, result, h1, h2, _, _, h4⟩
    · rw [VEnv.addEliminators_projections] at hold
      exact ihCtors hold

/-- Application of a constant to arguments. -/
def HeadConst : VExpr → Prop
  | .const .. => True
  | .app f _ => HeadConst f
  | _ => False

theorem HeadConst.of_getAppFnArgs_go {e : VExpr} {args : List VExpr}
    (h : (VExpr.getAppFnArgs.go e args).1 = .const c ls) : HeadConst e := by
  induction e generalizing args with
  | app f a ihf _ => exact ihf (args := a :: args) h
  | const => trivial
  | _ => simp [VExpr.getAppFnArgs.go] at h

theorem HeadConst.of_getAppFnArgs {e : VExpr}
    (h : e.getAppFnArgs.1 = .const c ls) : HeadConst e := .of_getAppFnArgs_go h

theorem HeadConst.inst {e : VExpr} (h : HeadConst e) : HeadConst (e.inst p k) := by
  induction e with
  | app f a ihf _ => exact ihf h
  | const => trivial
  | _ => exact h.elim

theorem HeadConst.instL {e : VExpr} (h : HeadConst e) : HeadConst (e.instL ls) := by
  induction e with
  | app f a ihf _ => exact ihf h
  | const => trivial
  | _ => exact h.elim

/-- Two terms with the same syntactic `forallE` spine ending in applications of
constants, whose domains and results are related by `CongrUB` at their depths. -/
inductive SpineCongr (env : VEnv) (U : Nat) (Γ₀ : List VExpr) : Nat → VExpr → VExpr → Prop
  | result : HeadConst r₁ → CongrUB env U Γ₀ k r₁ r₂ → SpineCongr env U Γ₀ k r₁ r₂
  | forallE : CongrUB env U Γ₀ k d₁ d₂ → SpineCongr env U Γ₀ (k+1) B₁ B₂ →
    SpineCongr env U Γ₀ k (.forallE d₁ B₁) (.forallE d₂ B₂)

namespace SpineCongr
variable {env : VEnv} {U : Nat} {Γ₀ : List VExpr}

theorem inst (H : SpineCongr env U Γ₀ (k+1) X₁ X₂) (hp : CongrUB env U Γ₀ 0 p₁ p₂) :
    SpineCongr env U Γ₀ k (X₁.inst p₁ k) (X₂.inst p₂ k) := by
  generalize hm : k + 1 = m at H
  induction H generalizing k with
  | result hr hc => subst hm; exact .result hr.inst (hc.inst hp)
  | forallE hd _ ih =>
    subst hm
    exact .forallE (hd.inst hp) (ih rfl)

theorem instL_wrap {ls₁ ls₂ : List VLevel} (hr : HeadConst r)
    (h : List.Forall₂ (· ≈ ·) ls₁ ls₂) (hwf : ∀ l ∈ ls₂, l.WF U) (ds : List VExpr) :
    SpineCongr env U Γ₀ k ((VExpr.wrapForalls ds r).instL ls₁)
      ((VExpr.wrapForalls ds r).instL ls₂) := by
  induction ds generalizing k with
  | nil => exact .result hr.instL (.instL_self h hwf r)
  | cons d ds ih => exact .forallE (.instL_self h hwf d) ih

theorem params (H : SpineCongr env U Γ₀ 0 X₁ X₂)
    (hps : List.Forall₂ (env.IsDefEqU U Γ₀) ps₁ ps₂)
    (h1 : VProjectionInfo.instantiateProjectionParameters X₁ ps₁ = some R₁)
    (h2 : VProjectionInfo.instantiateProjectionParameters X₂ ps₂ = some R₂) :
    SpineCongr env U Γ₀ 0 R₁ R₂ := by
  induction hps generalizing X₁ X₂ with
  | nil =>
    simp only [VProjectionInfo.instantiateProjectionParameters, Option.some.injEq] at h1 h2
    subst h1 h2; exact H
  | cons hp _ ih =>
    cases H with
    | result hr _ =>
      cases X₁ <;> first
        | exact hr.elim
        | simp [VProjectionInfo.instantiateProjectionParameters] at h1
    | forallE _ hB =>
      simp only [VProjectionInfo.instantiateProjectionParameters] at h1 h2
      exact ih (hB.inst (.leaf0 hp)) h1 h2

theorem fields (H : SpineCongr env U Γ₀ 0 X₁ X₂) (hm : env.IsDefEqU U Γ₀ m₁ m₂)
    (h1 : VProjectionInfo.instantiateProjectionFields typeName m₁ wanted current fuel X₁ =
      some F₁)
    (h2 : VProjectionInfo.instantiateProjectionFields typeName m₂ wanted current fuel X₂ =
      some F₂) :
    CongrUB env U Γ₀ 0 F₁ F₂ := by
  induction fuel generalizing X₁ X₂ current with
  | zero => simp [VProjectionInfo.instantiateProjectionFields] at h1
  | succ fuel ih =>
    cases H with
    | result hr _ =>
      cases X₁ <;> first
        | exact hr.elim
        | simp [VProjectionInfo.instantiateProjectionFields] at h1
    | forallE hd hB =>
      simp only [VProjectionInfo.instantiateProjectionFields] at h1 h2
      by_cases hw : wanted = current
      · simp only [hw, if_true, Option.some.injEq] at h1 h2
        subst h1 h2; exact hd
      · simp only [hw, if_false] at h1 h2
        exact ih (hB.inst (.proj (.leaf0 hm))) h1 h2

end SpineCongr

/-- Field-type congruence: the field types selected by two projection typings with
equivalent levels, definitionally equal parameters and definitionally equal source majors
are related by `CongrUB` at depth `0`. -/
theorem fieldType_congr {env : VEnv} {U : Nat} {Γ₀ : List VExpr} (henv : env.Ordered)
    (hprojection : env.projections typeName info)
    {ls₁ ls₂ : List VLevel} (hls : List.Forall₂ (· ≈ ·) ls₁ ls₂)
    (hwf : ∀ l ∈ ls₂, l.WF U)
    (hps : List.Forall₂ (env.IsDefEqU U Γ₀) ps₁ ps₂)
    (hsm : env.IsDefEqU U Γ₀ sm₁ sm₂)
    (h1 : info.fieldType typeName ls₁ ps₁ i sm₁ = some F₁)
    (h2 : info.fieldType typeName ls₂ ps₂ i sm₂ = some F₂) :
    CongrUB env U Γ₀ 0 F₁ F₂ := by
  obtain ⟨doms, result, hT, -, c, cls, hr⟩ := henv.projection_rawShape hprojection
  unfold VProjectionInfo.fieldType at h1 h2
  split at h1
  · contradiction
  split at h2
  · contradiction
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h1 h2
  obtain ⟨t₁, ht₁, hf₁⟩ := h1
  obtain ⟨t₂, ht₂, hf₂⟩ := h2
  have H : SpineCongr env U Γ₀ 0 (info.ctorType.instL ls₁) (info.ctorType.instL ls₂) := by
    rw [hT]; exact .instL_wrap (.of_getAppFnArgs hr) hls hwf doms
  exact (H.params hps ht₁ ht₂).fields hsm hf₁ hf₂

end VEnv
end Lean4Lean
