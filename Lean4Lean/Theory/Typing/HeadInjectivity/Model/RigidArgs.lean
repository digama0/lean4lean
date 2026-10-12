import Lean4Lean.Theory.Typing.HeadInjectivity.Model.RuleLemmas

/-! # Argument observations of rigid spines

A semantically typed spine of a rigid constant has, among its observations, the observations
of each of its arguments (`rigid_argOb`, through `RigidEnd`'s `rigidArgOb` clause); conversely
such an observation of a rigid spine comes from an observation of the argument
(`rigid_spine_argOb_inv`). Hence a subsumption between the observations of two rigid spines
of the same constant, as soundness gives for definitionally equal spines, is a subsumption
between the observations of corresponding arguments (`rigid_args_sub`). This is what lets the
ι rule of an instance `rec P M m a (c x h)` with `a ≡ x`, forced by the typing of the redex,
exchange the observations of the index argument `a` and of the field `x`. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-- The demands of a spine lemma: `K` at position `i`, nothing elsewhere. -/
def demandAt (n i : Nat) (K : List Ob) : List (List Ob) :=
  (List.range n).map fun j => if j = i then K else []

theorem demandAt_length (n i : Nat) (K : List Ob) : (demandAt n i K).length = n := by
  simp [demandAt]

theorem demandAt_getElem (n i : Nat) (K : List Ob) {j : Nat} (hj : j < n) :
    (demandAt n i K)[j]'(by simp [demandAt_length, hj]) = if j = i then K else [] := by
  simp [demandAt]

theorem demandAt_forall₂ {σ : VExpr.Subst} {S : ObSets} {args : List VExpr} {i : Nat}
    {K : List Ob} (hi : i < args.length) (hK : ∀ x ∈ K, Obs' σ S args[i] x) :
    List.Forall₂ (fun K a => ∀ x ∈ K, Obs' σ S a x) (demandAt args.length i K) args := by
  refine List.forall₂_of_getElem (by simp [demandAt_length]) fun j hj hj' => ?_
  rw [demandAt_getElem _ _ _ hj']
  split
  · subst ‹j = i›; exact hK
  · intro x hx; cases hx

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- **Argument observations of a rigid spine.** -/
theorem rigid_argOb {Γ : List VExpr} {c : Name} {ls : List VLevel} {args : List VExpr} {u : VLevel}
    {σ : VExpr.Subst} {S : ObSets}
    (H : HTS env U Δ Γ (.mkApps (.const c ls) args) (.sort u)) (W : Ctx.SubstEq env U Δ σ σ Γ)
    (tv : TV env U Δ Γ σ S) (hrig : env.Rigid c) {i : Nat} (hi : i < args.length) {k : Ob}
    (hk : Obs' σ S args[i] k) :
    Obs' σ S (.mkApps (.const c ls) args) (.rigidArgOb i k) := by
  obtain ⟨ci, info, hci, -, -, hinfo, hKsi, P1, -, -⟩ :=
    H.spine henv hΔ rfl W tv (demandAt args.length i [k])
      (demandAt_forall₂ hi fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact hk)
      [.sort u.eval] (fun τ hτ => by rw [List.mem_singleton] at hτ; subst hτ; exact .sort)
  have hlen : info.length = args.length := List.Forall₂.length_eq hinfo
  have hi' : i < info.length := by omega
  have hmem : k ∈ (info[i]).1.2.2 := by
    obtain ⟨_, h⟩ := List.forall₂_getElem_exists hKsi i (by simp [demandAt_length, hi])
    rw [demandAt_getElem _ _ _ hi, if_pos rfl] at h
    exact h k (List.mem_singleton_self _)
  have hr : RigidEnd c (ls.map (·.eval)) (info.map (·.1)) (.rigidArgOb i k) :=
    .inr (.inr ⟨i, by simpa using hi', k, by simpa using hmem, rfl⟩)
  obtain ⟨τ₀, hτ₀, hty₀⟩ := P1 _ (.rigidArgOb (List.mem_singleton_self _))
  exact obs_mkApps_of_wrap (KeyData.forall₂_keys hinfo) (.const hrig hci hτ₀ hty₀ hr)

end

/-- An argument observation of a spine of a rigid constant comes from an observation of the
argument. -/
theorem rigid_spine_argOb_inv {σ : VExpr.Subst} {S : ObSets} {c : Name} {ls : List VLevel}
    {args : List VExpr} {i : Nat} {k : Ob} (hrig : env.Rigid c)
    (h : Obs' σ S (.mkApps (.const c ls) args) (.rigidArgOb i k)) :
    ∃ a, args[i]? = some a ∧ ∃ k', Obs' σ S a k' ∧ k' ≼ k := by
  obtain ⟨keys, hk, hw⟩ := wrap_of_obs_mkApps_le h
  have hna : Ob.NotApp (.rigidArgOb i k) := trivial
  rcases Obs.const_iff.1 hw with ⟨_, _, keys', r', e, _, _, _, _, hr'⟩ |
    ⟨df, _, _, hdf, hlhs, _⟩ | ⟨_, _, keys', r', e, _, _, _, _, _, hr', _⟩ |
    ⟨df, _, lsP, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdf, hlhs, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp, _⟩ |
    ⟨_, _, _, _, keys', r', e, _, _, _, _, _, _, ⟨_, _, _, rfl, _⟩, _⟩ |
    ⟨_, _, _, keys', _, _, _, _, _, _, _, e, _⟩ | ⟨_, _, _, keys', _, _, _, _, _, _, e, _⟩
  · obtain ⟨rfl, rfl⟩ := wrap_inj e hna hr'.notApp
    rcases hr' with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨j, hj, k', hk', h⟩
    · cases h
    · cases h
    · obtain ⟨e1, e2⟩ := Ob.rigidArgOb.inj h
      have hjl : j < args.length := by rw [← List.Forall₂.length_eq hk]; exact hj
      obtain ⟨_, hR⟩ := List.forall₂_getElem_exists hk j hj
      obtain ⟨k'', hk'', l⟩ := hR.2 _ hk'
      subst e1
      exact ⟨_, List.getElem?_eq_getElem hjl, k'', hk'', e2 ▸ l⟩
  · exact absurd (by rw [hlhs]; rfl) (hrig.defeqs df hdf _)
  · have hrn : r'.NotApp := by
      rcases hr' with rfl | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> trivial
    obtain ⟨rfl, rfl⟩ := wrap_inj e hna hrn
    rcases hr' with h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h
  · exact absurd (by rw [hlhs]; exact VExpr.stripLams_wrapLams_mkApps_head) (hrig.defeqs df hdf lsP)
  · exact absurd (SimplePattern.iota_headConst ..) (hrig.pats _ _ hp)
  · obtain ⟨rfl, h⟩ := wrap_inj e hna trivial; cases h
  · obtain ⟨rfl, h⟩ := wrap_inj e hna trivial; cases h
  · obtain ⟨rfl, h⟩ := wrap_inj e hna trivial; cases h

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- **Argument subsumption from spine subsumption**: if the observations of a typed rigid spine
are subsumed by those of another spine of the same rigid constant, the observations of each
argument of the first are subsumed by those of the corresponding argument of the second. -/
theorem rigid_args_sub {Γ : List VExpr} {c : Name} {ls ls' : List VLevel} {args args' : List VExpr}
    {u : VLevel} {σ σ' : VExpr.Subst} {S S' : ObSets}
    (H : HTS env U Δ Γ (.mkApps (.const c ls) args) (.sort u)) (W : Ctx.SubstEq env U Δ σ σ Γ)
    (tv : TV env U Δ Γ σ S) (hrig : env.Rigid c)
    (hsub : Ob.Sub (Obs' σ S (.mkApps (.const c ls) args))
      (Obs' σ' S' (.mkApps (.const c ls') args')))
    {i : Nat} (hi : i < args.length) {a' : VExpr} (ha' : args'[i]? = some a') :
    Ob.Sub (Obs' σ S args[i]) (Obs' σ' S' a') := by
  intro k hk
  obtain ⟨o', ho', l⟩ := hsub _ (rigid_argOb henv hΔ H W tv hrig hi hk)
  obtain ⟨k', rfl, lk⟩ := l.rigidArgOb_inv
  obtain ⟨a'', ha'', k'', hk'', l''⟩ := rigid_spine_argOb_inv hrig ho'
  rw [ha'] at ha''
  cases ha''
  exact ⟨k'', hk'', l''.trans lk⟩

end

end Model
end VEnv
end Lean4Lean
