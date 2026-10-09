import Lean4Lean.Theory.Typing.ChurchRosser

namespace Lean4Lean.VEnv
open VExpr Params
variable [Params]

/-- Normal equality is preserved by a simultaneous substitution. Unchanged
entries need no separate typing witness; the actual substituted term supplies
one whenever such an entry occurs. -/
theorem NormalEqF.subst_args {e : VExpr} {σ σ' : VExpr.Subst} (hΓ : OnCtx Γ (env.IsType univs))
    (hs : ∀ i, σ i = σ' i ∨ NormalEqF η Γ (σ i) (σ' i))
    (ht : HasType env univs Γ (e.subst σ) type) :
    NormalEqF η Γ (e.subst σ) (e.subst σ') := by
  induction e generalizing Γ σ σ' type with
  | bvar i =>
    rcases hs i with he | he
    · rw [VExpr.subst, VExpr.subst, ← he]
      exact .refl ht
    · exact he
  | sort | const | elim => exact .refl ht
  | app fn arg ihf iha =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    have hnf := ihf hΓ hs hf
    have hna := iha hΓ hs ha
    exact .appDF hf ((hnf.defeq hΓ).of_l henv hΓ hf).hasType.2
      ha ((hna.defeq hΓ).of_l henv hΓ ha).hasType.2 hnf hna
  | proj family index major ih =>
    obtain ⟨info, levels, params, indices, major', field, level, hi, hlu, hun, hp, hix, hf,
      hfield, hmajor, hclosed, hguard⟩ := ht.proj_inv henv hΓ
    exact .projDF ht (ih hΓ hs hmajor.hasType.2)
  | lam domain body ihd ihb =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hctx : OnCtx (domain.subst σ :: Γ) (env.IsType univs) := ⟨hΓ, _, hd⟩
    have hdn := ihd hΓ hs hd
    refine .lamDF hd ((hdn.defeq hΓ).of_l henv hΓ hd) (ihb hctx ?_ hb)
    intro i
    cases i with
    | zero => exact .inl rfl
    | succ i =>
      rcases hs i with he | he
      · exact .inl (congrArg VExpr.lift he)
      · exact .inr (he.weakN .one)
  | forallE domain body ihd ihb =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := ht.forallE_inv henv
    have hctx : OnCtx (domain.subst σ :: Γ) (env.IsType univs) := ⟨hΓ, _, hd⟩
    refine .forallEDF hd (ihd hΓ hs hd) hb (ihb hctx ?_ hb)
    intro i
    cases i with
    | zero => exact .inl rfl
    | succ i =>
      rcases hs i with he | he
      · exact .inl (congrArg VExpr.lift he)
      · exact .inr (he.weakN .one)


theorem NormalEqF.instantiateParams_args (hΓ : OnCtx Γ (env.IsType univs))
    (hs : List.Forall₂ (NormalEqF η Γ) args args')
    (ht : HasType env univs Γ (InductiveSignature.instantiateParams e args) type) :
    NormalEqF η Γ (InductiveSignature.instantiateParams e args)
      (InductiveSignature.instantiateParams e args') := by
  apply NormalEqF.subst_args hΓ ?_ ht
  intro i
  have hlen := Lean4Lean.List.Forall₂.length_eq hs
  simp only [← hlen]
  split
  · rename_i hi
    exact .inr (List.forall₂_getElem hs _ (by omega) (by omega))
  · exact .inl rfl

theorem NormalEqF.wrapLams_congr (hΓ : OnCtx Γ (env.IsType univs))
    (hlen : domains.length = domains'.length)
    (ht : IsDefEqU env univs Γ (wrapForalls domains result) (wrapForalls domains' result'))
    (hb : NormalEqF η (domains.reverse ++ Γ) body body') :
    NormalEqF η Γ (wrapLams domains body) (wrapLams domains' body') := by
  induction domains generalizing Γ domains' with
  | nil =>
    have he : domains' = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst domains'
    exact hb
  | cons d ds ih =>
    cases domains' with
    | nil => simp at hlen
    | cons d' ds' =>
      obtain ⟨⟨u, hd⟩, _, hrest⟩ := ht.forallE_inv henv hΓ
      have hctx : OnCtx (d :: Γ) (env.IsType univs) := ⟨hΓ, _, hd.hasType.1⟩
      apply NormalEqF.lamDF hd.hasType.1 hd
      apply ih hctx (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen) ⟨_, hrest⟩
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hb

omit [Params] in
theorem IsDefEqU.wrapForalls_context {env : VEnv} (henv : env.WF) (hΓ : OnCtx Γ₀ (env.IsType U))
    (W : IsDefEqCtx env U Γ₀ Γ₁ Γ₂)
    (hlen : domains.length = domains'.length)
    (ht : IsDefEqU env U Γ₁ (wrapForalls domains result) (wrapForalls domains' result')) :
    IsDefEqCtx env U Γ₀ (domains.reverse ++ Γ₁) (domains'.reverse ++ Γ₂) := by
  induction domains generalizing Γ₁ Γ₂ domains' with
  | nil =>
    have he : domains' = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst domains'
    exact W
  | cons d ds ih =>
    cases domains' with
    | nil => simp at hlen
    | cons d' ds' =>
      obtain ⟨⟨u, hd⟩, _, hrest⟩ := ht.forallE_inv henv (W.isType' hΓ)
      have hh := ih (.succ W hd) (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen) ⟨_, hrest⟩
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hh

alias NormalEq.subst_args := NormalEqF.subst_args
alias NormalEq.instantiateParams_args := NormalEqF.instantiateParams_args
alias NormalEq.wrapLams_congr := NormalEqF.wrapLams_congr

end Lean4Lean.VEnv
