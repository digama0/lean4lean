import Lean4Lean.Theory.Typing.HeadInjectivity.Model.EnvValid

/-! # Head separation from the glued model

A chain of sort-typed equalities carries the observations of its left end into those of its
right end, up to subsumption (`Model.chain_sub`). Subsumption keeps the head constructor of
`sort` and `piDom` observations. A sort has a `sort` observation and a Pi type a `piDom`
observation. Neither a Pi type has a `sort` observation, nor does a spine of a rigid constant
have a `sort` or a `piDom` observation. So no chain relates a sort to a Pi type or to a rigid
spine, or a Pi type to a rigid spine. These are the separation fields `sort_forallE`,
`sort_rigid` and `forallE_rigid` of `VEnv.HeadInversion`. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat}

/-- A Pi type has no `sort` observation. -/
theorem forallE_not_sort {Δ : List VExpr} {σ : VExpr.Subst} {S : ObSets}
    (h : Obs env U Δ σ S (.forallE A B) (.sort z)) : False := by
  rcases Obs.forallE_iff.1 h with h | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, _, _, h, _⟩ <;>
    cases h

/-- A spine of a rigid constant has neither a `sort` nor a `piDom` observation. -/
theorem rigid_spine_not {Δ : List VExpr} {σ : VExpr.Subst} {S : ObSets} {o : Ob}
    (hrig : env.Rigid c) (h : Obs env U Δ σ S (.mkApps (.const c ls) args) o)
    (ho : (∃ z, o = .sort z) ∨ ∃ D, o = .piDom D) : False :=
  rigid_spine_not_pi hrig h (ho.imp_right .inl)

theorem sort_forallE (henv : env.Ordered) (hnr : SoundEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (h : env.TypeChain U Γ (.sort u) (.forallE A B)) : False := by
  obtain ⟨o, ho, l⟩ := chain_sub henv hnr hΓ h _ .sort
  rw [l.sort_inv] at ho
  exact forallE_not_sort ho

theorem sort_rigid (henv : env.Ordered) (hnr : SoundEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (hrig : env.Rigid c) (h : env.TypeChain U Γ (.sort u) (.mkApps (.const c ls) args)) :
    False := by
  obtain ⟨o, ho, l⟩ := chain_sub henv hnr hΓ h _ .sort
  rw [l.sort_inv] at ho
  exact rigid_spine_not hrig ho (.inl ⟨_, rfl⟩)

theorem forallE_rigid (henv : env.Ordered) (hnr : SoundEnv env) (hΓ : OnCtx Γ (env.IsType U))
    (hrig : env.Rigid c) (h : env.TypeChain U Γ (.forallE A B) (.mkApps (.const c ls) args)) :
    False := by
  obtain ⟨o, ho, l⟩ := chain_sub henv hnr hΓ h _ (.piDom (A := A) (B := B))
  rw [l.piDom_inv] at ho
  exact rigid_spine_not hrig ho (.inr ⟨_, rfl⟩)

end Model

/-- **Head separation from soundness** of the observation model. -/
theorem WF.headSeparation_of_sound {env : VEnv} (henv : env.WF) (hnr : Model.SoundEnv env) :
    env.HeadSeparation where
  sort_sort hΓ h := (WF.chainHeadInjectivity_of_sound henv hnr).sort_sort hΓ h
  rigid_heads hΓ hc hc' h :=
    let r := (WF.chainHeadInjectivity_of_sound henv hnr).rigid_rigid hΓ hc hc' h; ⟨r.1, r.2.1⟩
  sort_forallE hΓ h := Model.sort_forallE henv.ordered hnr hΓ h
  sort_rigid hΓ hrig h := Model.sort_rigid henv.ordered hnr hΓ hrig h
  forallE_rigid hΓ hrig h := Model.forallE_rigid henv.ordered hnr hΓ hrig h

/-- **Head separation** for every well-formed environment, from the glued model. -/
theorem WF.headSeparationModel {env : VEnv} (henv : env.WF) : env.HeadSeparation :=
  WF.headSeparation_of_sound henv henv.soundEnv

end VEnv
end Lean4Lean
