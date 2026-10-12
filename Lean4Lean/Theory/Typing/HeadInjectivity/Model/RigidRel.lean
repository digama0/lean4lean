import Lean4Lean.Theory.Typing.HeadInjectivity.Model.RigidArgs
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Extract

/-! # Related rigid spines

Two sort-typed spines of the same rigid constant whose observations subsume each other (as the
soundness of a conversion between them gives) have the same number of arguments, equivalent
levels, and pointwise related arguments: the observations of corresponding arguments subsume
each other (`rigid_args_sub`), and corresponding arguments are definitionally equal in the
target context at the type of the left argument (`rigid_spines_rel`). The definitional
equality is read off the argument class observations `rigidArg i c` of the spines: subsumption
preserves them (`Ob.Le.rigidArg_inv`), so the class of the left argument is the class of the
right one, and the collapse lemma turns membership into a definitional equality. This is the
argument of `rigid_analysis` (`Model/Extract.lean`) with the subsumption taken as a
hypothesis, so that it can be fed by the semantic typing of a redex rather than by the
soundness of the whole environment. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- A semantically typed rigid spine has the class observation of each of its arguments, at the
type class of the argument's domain in the derivation. -/
theorem rigid_arg_cls_obs {Γ : List VExpr} {c : Name} {ls : List VLevel} {args : List VExpr}
    {u : VLevel} {σ : VExpr.Subst} {S : ObSets}
    (H : HTS env U Δ Γ (.mkApps (.const c ls) args) (.sort u)) (W : Ctx.SubstEq env U Δ σ σ Γ)
    (tv : TV env U Δ Γ σ S) (hrig : env.Rigid c) {i : Nat} (hi : i < args.length) :
    ∃ A, HTS env U Δ Γ args[i] A ∧ SD env U Δ Γ args[i] args[i] A ∧
      Obs' σ S (.mkApps (.const c ls) args)
        (.rigidArg i (ElCls env U Δ (TyCls env U Δ (A.subst σ)) (args[i].subst σ))) := by
  obtain ⟨ci, info, hci, -, -, hinfo, -, P1, -, -⟩ :=
    H.spine henv hΔ rfl W tv (args.map fun _ => []) (forall₂_nil_lists args)
      [.sort u.eval] (fun τ hτ => by rw [List.mem_singleton] at hτ; subst hτ; exact .sort)
  have hlen : info.length = args.length := List.Forall₂.length_eq hinfo
  have hi' : i < info.length := by omega
  obtain ⟨_, hd⟩ := List.forall₂_getElem_exists hinfo i hi'
  obtain ⟨h1, -, h3, h4, h5, -⟩ := hd
  have hr : RigidEnd c (ls.map (·.eval)) (info.map (·.1)) (.rigidArg i (info[i]).1.2.1) :=
    .inr (.inl ⟨i, by simpa using hi', by simp⟩)
  obtain ⟨τ₀, hτ₀, hty₀⟩ := P1 _ (.rigidArg (List.mem_singleton_self _))
  refine ⟨(info[i]).2, h4, h5, ?_⟩
  have := obs_mkApps_of_wrap (KeyData.forall₂_keys hinfo) (.const hrig hci hτ₀ hty₀ hr)
  rwa [h1, h3] at this

/-- **Related rigid spines**: two sort-typed spines of the rigid constant `c` whose observations
subsume each other have the same arity, equivalent levels, and pointwise related arguments. -/
theorem rigid_spines_rel {Γ₁ Γ₂ : List VExpr} {c : Name} {ls₁ ls₂ : List VLevel}
    {args₁ args₂ : List VExpr} {u₁ u₂ : VLevel} {σ₁ σ₂ : VExpr.Subst} {S₁ S₂ : ObSets}
    (H₁ : HTS env U Δ Γ₁ (.mkApps (.const c ls₁) args₁) (.sort u₁))
    (W₁ : Ctx.SubstEq env U Δ σ₁ σ₁ Γ₁) (tv₁ : TV env U Δ Γ₁ σ₁ S₁)
    (H₂ : HTS env U Δ Γ₂ (.mkApps (.const c ls₂) args₂) (.sort u₂))
    (W₂ : Ctx.SubstEq env U Δ σ₂ σ₂ Γ₂) (tv₂ : TV env U Δ Γ₂ σ₂ S₂) (hrig : env.Rigid c)
    (hsub : Ob.Sub (Obs' σ₁ S₁ (.mkApps (.const c ls₁) args₁))
      (Obs' σ₂ S₂ (.mkApps (.const c ls₂) args₂)))
    (hsub' : Ob.Sub (Obs' σ₂ S₂ (.mkApps (.const c ls₂) args₂))
      (Obs' σ₁ S₁ (.mkApps (.const c ls₁) args₁))) :
    args₁.length = args₂.length ∧ List.Forall₂ (· ≈ ·) ls₁ ls₂ ∧
    ∀ i (hi : i < args₁.length) (hi' : i < args₂.length),
      Ob.Sub (Obs' σ₁ S₁ args₁[i]) (Obs' σ₂ S₂ args₂[i]) ∧
      Ob.Sub (Obs' σ₂ S₂ args₂[i]) (Obs' σ₁ S₁ args₁[i]) ∧
      ∃ A₁, HTS env U Δ Γ₁ args₁[i] A₁ ∧ SD env U Δ Γ₁ args₁[i] args₁[i] A₁ ∧
        env.IsDefEq U Δ (args₁[i].subst σ₁) (args₂[i].subst σ₂) (A₁.subst σ₁) := by
  -- the head observation
  have hr := spine_rigid_obs henv hΔ H₁ W₁ tv₁ hrig
  obtain ⟨o', ho', l⟩ := hsub _ hr
  rw [l.rigid_inv] at ho'
  obtain ⟨keys₂, hk₂, hw₂⟩ := wrap_of_obs_mkApps ho'
  have hend := const_wrap_inv hrig hw₂ (.inl ⟨_, _, _, _, rfl⟩)
  obtain ⟨hlen, hls⟩ : args₁.length = args₂.length ∧ ls₁.map (·.eval) = ls₂.map (·.eval) := by
    rcases hend with ⟨s, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, _, e⟩
    · injection e with _ e1 e2
      exact ⟨e2.trans (List.Forall₂.length_eq hk₂), e1⟩
    · cases e
    · cases e
  refine ⟨hlen, forall₂_equiv_of_map_eval hls, fun i hi hi' => ?_⟩
  refine ⟨rigid_args_sub henv hΔ H₁ W₁ tv₁ hrig hsub hi (List.getElem?_eq_getElem hi'),
    rigid_args_sub henv hΔ H₂ W₂ tv₂ hrig hsub' hi' (List.getElem?_eq_getElem hi), ?_⟩
  -- the class observation of the left argument
  obtain ⟨A₁, hA₁, hsA₁, hcls⟩ := rigid_arg_cls_obs henv hΔ H₁ W₁ tv₁ hrig hi
  obtain ⟨o', ho', l⟩ := hsub _ hcls
  rw [l.rigidArg_inv] at ho'
  obtain ⟨keys', hk', hw'⟩ := wrap_of_obs_mkApps ho'
  have hend' := const_wrap_inv hrig hw' (.inr ⟨_, _, rfl⟩)
  have hkl : keys'.length = args₂.length := List.Forall₂.length_eq hk'
  obtain ⟨j, hj, e⟩ : ∃ j, ∃ h : j < keys'.length,
      Ob.rigidArg i (ElCls env U Δ (TyCls env U Δ (A₁.subst σ₁)) (args₁[i].subst σ₁)) =
        .rigidArg j (keys'[j]).2.1 := by
    rcases hend' with ⟨_, e⟩ | ⟨j, hj, e⟩ | ⟨_, _, _, _, e⟩
    · cases e
    · exact ⟨j, hj, e⟩
    · cases e
  injection e with e1 e2
  subst e1
  obtain ⟨_, hcl⟩ := List.forall₂_getElem_exists hk' i hj
  have hmem : ElCls env U Δ (TyCls env U Δ (A₁.subst σ₁)) (args₁[i].subst σ₁)
      (args₂[i].subst σ₂) := by
    rw [e2, hcl]; exact ElCls.self
  have ha : env.HasType U Δ (args₁[i].subst σ₁) (A₁.subst σ₁) :=
    hsA₁.1.defeq.hasType.1.substDF henv W₁.wf hΔ W₁
  exact ⟨A₁, hA₁, hsA₁, ElCls.collapse henv hΔ ha TyCls.self hmem⟩

end

end Model
end VEnv
end Lean4Lean
