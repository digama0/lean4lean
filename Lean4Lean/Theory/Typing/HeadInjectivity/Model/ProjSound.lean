import Lean4Lean.Theory.Typing.HeadInjectivity.Model.CtorFieldObs

/-! # Soundness of the projection rules

The cases `projDF`, `projIota`, `structEta` and `unitLike` of `Model.sound`, for a projection
entry that is valid in the model (`ProjValid`). Each lemma takes the premises of the rule (in the
model's environment) with their soundness and semantic typing derivations, and gives `SoundAt` of
the conclusion and `HTS` of both sides.

* `sound_projDF`: congruence (`fieldOb S j L o ≼ fieldOb S j L' o'` iff `o ≼ o'`); the typing
  invariant is `proj_obs_typed`.
* `sound_projIota`: left to right by inversion of the constructor spine's field observations;
  right to left by `ctor_field_obs` when the entry is never zero at the major type's levels (the
  spine then has the constructor's arity and the entry is never zero at the constructor's levels,
  `ctor_spine_fam`), and otherwise by proof irrelevance (the field type is a proposition).
* `sound_structEta`: the typed observations of both sides are field observations
  (`typed_fam_fieldOb`); left to right by inversion of the spine, right to left by
  `ctor_field_obs` on the spine of projections.
* `sound_unitLike`: a structure without fields has no typed observations. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

theorem sound_projDF {S : Name} {info : VProjectionInfo} (hp : env.projections S info)
    (hPV : ProjValid env S info) {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U)
    (hlen : ls.length = info.uvars) {ps idx : List VExpr} (hps : ps.length = info.nparams)
    (hidx : idx.length = info.nindices) {j : Nat} {e₀ e₁ e₂ F : VExpr} {fl : VLevel}
    (hF : info.fieldType S ls ps j e₀ = some F)
    (hFty : env.IsDefEqStrong U Γ F F (.sort fl))
    (h1 : env.IsDefEqStrong U Γ e₀ e₁ (.mkApps (.const S ls) (ps ++ idx)))
    (h2 : env.IsDefEqStrong U Γ e₀ e₂ (.mkApps (.const S ls) (ps ++ idx)))
    (hcl : info.ctorType.Closed)
    (hguard : (info.resultLevel.inst ls).IsNeverZero ∨ fl ≈ .zero)
    (ihF : SoundAt env U Δ Γ F F (.sort fl) ∧ HTS env U Δ Γ F (.sort fl))
    (ih1 : SoundAt env U Δ Γ e₀ e₁ (.mkApps (.const S ls) (ps ++ idx)) ∧
      HTS env U Δ Γ e₁ (.mkApps (.const S ls) (ps ++ idx)))
    (ih2 : SoundAt env U Δ Γ e₀ e₂ (.mkApps (.const S ls) (ps ++ idx)) ∧
      HTS env U Δ Γ e₂ (.mkApps (.const S ls) (ps ++ idx))) :
    SoundAt env U Δ Γ (.proj S j e₁) (.proj S j e₂) F ∧ HTS env U Δ Γ (.proj S j e₁) F ∧
      HTS env U Δ Γ (.proj S j e₂) F := by
  refine ⟨?_, .proj hp hls hlen hps hidx hF ⟨hFty, ihF.1⟩ ih1.2 ⟨h1, ih1.1⟩ hguard,
    .proj hp hls hlen hps hidx hF ⟨hFty, ihF.1⟩ ih2.2 ⟨h2, ih2.1⟩ hguard⟩
  obtain ⟨doms, idx', famType, hdoms, C⟩ := ProjValid.ctx henv hΔ hp hPV hls
  have hrig := hPV.1.famRigid
  have SA : SoundAt env U Δ Γ e₁ e₂ (.mkApps (.const S ls) (ps ++ idx)) :=
    (ih1.1.symm henv hΔ).trans henv hΔ ih2.1
  intro σ σ' S0 W tv tv'
  have W' := SubstEq.right henv hΔ W
  refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, fun o h => ?_⟩
  · obtain ⟨L, h⟩ := Obs.proj_iff.1 h
    obtain ⟨o', h', l⟩ := (SA σ σ' S0 W tv tv').1 _ h
    obtain ⟨L', y, rfl, ly⟩ := l.fieldOb_inv
    exact ⟨y, .proj h', ly⟩
  · obtain ⟨L, h⟩ := Obs.proj_iff.1 h
    obtain ⟨o', h', l⟩ := (SA σ σ' S0 W tv tv').2.1 _ h
    obtain ⟨L', y, rfl, ly⟩ := l.fieldOb_inv
    exact ⟨y, .proj h', ly⟩
  · obtain ⟨L, h⟩ := Obs.proj_iff.1 h
    exact proj_obs_typed henv hΔ hp hcl hrig hls hlen C.tele C.piSD W.left tv hps hidx
      h1.defeq.symm ((ih1.1.symm henv hΔ) σ σ S0 W.left tv tv).1 hF h
      ((ih1.1 σ σ S0 W.left tv tv).2.2.2 _ h)
  · obtain ⟨L, h⟩ := Obs.proj_iff.1 h
    exact proj_obs_typed henv hΔ hp hcl hrig hls hlen C.tele C.piSD W' tv' hps hidx
      h2.defeq.symm ((ih2.1.symm henv hΔ) σ' σ' S0 W' tv' tv').1 hF h
      ((ih2.1 σ' σ' S0 W' tv' tv').2.2.2 _ h)

theorem sound_projIota {S : Name} {info : VProjectionInfo} (hp : env.projections S info)
    (hPV : ProjValid env S info) {j : Nat} {ls : List VLevel} {args : List VExpr}
    {field T : VExpr} (hfield : args[info.nparams + j]? = some field)
    (ihp : SoundAt env U Δ Γ (.proj S j (.mkApps (.const info.ctorName ls) args))
        (.proj S j (.mkApps (.const info.ctorName ls) args)) T ∧
      HTS env U Δ Γ (.proj S j (.mkApps (.const info.ctorName ls) args)) T)
    (ihf : SoundAt env U Δ Γ field field T ∧ HTS env U Δ Γ field T) :
    SoundAt env U Δ Γ (.proj S j (.mkApps (.const info.ctorName ls) args)) field T ∧
      HTS env U Δ Γ (.proj S j (.mkApps (.const info.ctorName ls) args)) T ∧
      HTS env U Δ Γ field T := by
  refine ⟨?_, ihp.2, ihf.2⟩
  have hrigC := hPV.1.ctorRigid
  have hja : info.nparams + j < args.length := (List.getElem?_eq_some_iff.1 hfield).1
  intro σ σ' S0 W tv tv'
  have W' := SubstEq.right henv hΔ W
  have IHp := ihp.1 σ σ' S0 W tv tv'
  have IHf := ihf.1 σ σ' S0 W tv tv'
  refine ⟨fun o h => ?_, fun o h => ?_, IHp.2.2.1, IHf.2.2.2⟩
  · obtain ⟨L, h⟩ := Obs.proj_iff.1 h
    obtain ⟨-, -, a, ha, k', hk', l⟩ := Obs.ctorSpine_fieldOb_inv henv hp hrigC h
    cases hfield.symm.trans ha
    obtain ⟨k'', hk'', l'⟩ := IHf.1 k' hk'
    exact ⟨k'', hk'', l'.trans l⟩
  · obtain ⟨info', ls', ps, idx, F, fl, e', hp', -, -, -, -, -, hFsd, hHe, -, hguard, hsub⟩ :=
      HTS.proj_inv ihp.2 rfl
    cases henv.projections_unique hp hp'
    rcases hguard with hnz | hfl
    · -- the spine is a full constructor spine, never zero at its levels
      obtain ⟨hlsm, hlenm, hal, hnzm⟩ := ctor_spine_fam henv hΔ hp hPV W.left tv hHe hnz
      obtain ⟨o₁, ho₁, l₁⟩ := IHf.2.1 o h
      have hsplit := (List.take_append_drop info.nparams args).symm
      have hpl : (args.take info.nparams).length = info.nparams := by simp; omega
      have hfl : (args.drop info.nparams).length = info.numFields := by simp; omega
      have hj : j < (args.drop info.nparams).length := by simp; omega
      have hfj : (args.drop info.nparams)[j] = field := by
        rw [List.getElem_drop]; exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hfield)
      rw [hsplit] at hHe
      obtain ⟨L, hL⟩ := ctor_field_obs henv hΔ hp hPV hlsm hlenm hnzm W.left tv hHe hpl hfl hj
        (k := o₁) (by rw [hfj]; exact ho₁)
      rw [← hsplit] at hL
      exact ⟨o₁, .proj hL, l₁⟩
    · -- the field type is a proposition: the field has no observations
      obtain ⟨τs, hτs, hto⟩ := IHf.2.2.2 o h
      obtain ⟨τs', hτs', hcov⟩ := exists_list_cover (R := fun y x => y ≼ x)
        fun τ hτ => hsub σ' S0 W' tv' τ (hτs τ hτ)
      exact ((hto.strengthen hcov).not_prop fun τ hτ =>
        ⟨_, (typedAt_sort_iff.1 ((hFsd.2 σ' σ' S0 W' tv' tv').2.2.1 τ (hτs' τ hτ))).sort_congr
          fun ns => VLevel.equiv_def.1 hfl ns⟩).elim

theorem sound_structEta {S : Name} {info : VProjectionInfo} (hp : env.projections S info)
    (hPV : ProjValid env S info) {ls : List VLevel} {params : List VExpr} {e : VExpr}
    (hpl : params.length = info.nparams)
    (ihe : SoundAt env U Δ Γ e e (.mkApps (.const S ls) params) ∧
      HTS env U Δ Γ e (.mkApps (.const S ls) params))
    (ihm : SoundAt env U Δ Γ (.mkApps (.const info.ctorName ls)
        (params ++ (List.range info.numFields).map fun i => .proj S i e))
        (.mkApps (.const info.ctorName ls)
          (params ++ (List.range info.numFields).map fun i => .proj S i e))
        (.mkApps (.const S ls) params) ∧
      HTS env U Δ Γ (.mkApps (.const info.ctorName ls)
        (params ++ (List.range info.numFields).map fun i => .proj S i e))
        (.mkApps (.const S ls) params)) :
    SoundAt env U Δ Γ (.mkApps (.const info.ctorName ls)
        (params ++ (List.range info.numFields).map fun i => .proj S i e)) e
        (.mkApps (.const S ls) params) ∧
      HTS env U Δ Γ (.mkApps (.const info.ctorName ls)
        (params ++ (List.range info.numFields).map fun i => .proj S i e))
        (.mkApps (.const S ls) params) ∧
      HTS env U Δ Γ e (.mkApps (.const S ls) params) := by
  refine ⟨?_, ihm.2, ihe.2⟩
  have hst := hPV.1
  intro σ σ' S0 W tv tv'
  have IHe := ihe.1 σ σ' S0 W tv tv'
  have IHm := ihm.1 σ σ' S0 W tv tv'
  have hfs : ∀ i (hi : i < info.numFields),
      ((List.range info.numFields).map fun i => VExpr.proj S i e)[i]'(by simpa using hi) =
        .proj S i e := by
    intro i hi; simp
  refine ⟨fun o h => ?_, fun o h => ?_, IHm.2.2.1, IHe.2.2.2⟩
  · obtain ⟨τs, hτs, hto⟩ := IHm.2.2.1 o h
    obtain ⟨j, L, k, rfl, hj, -⟩ := typed_fam_fieldOb henv hp hst.famRigid hst.famNotProjCtor hto hτs
    obtain ⟨-, -, a, ha, k', hk', l⟩ := Obs.ctorSpine_fieldOb_inv henv hp hst.ctorRigid h
    have ea : a = .proj S j e := by
      rw [List.getElem?_append_right (by omega), hpl, Nat.add_sub_cancel_left,
        List.getElem?_eq_getElem (by simpa using hj), hfs j hj] at ha
      exact (Option.some.inj ha).symm
    subst ea
    obtain ⟨L', hk''⟩ := Obs.proj_iff.1 hk'
    obtain ⟨o', ho', l'⟩ := IHe.1 _ hk''
    obtain ⟨L'', y, rfl, ly⟩ := l'.fieldOb_inv
    exact ⟨_, ho', .fieldOb (ly.trans l)⟩
  · obtain ⟨τs, hτs, hto⟩ := IHe.2.2.2 o h
    obtain ⟨j, L, k, rfl, hj, hnz⟩ :=
      typed_fam_fieldOb henv hp hst.famRigid hst.famNotProjCtor hto hτs
    obtain ⟨o₁, ho₁, l₁⟩ := IHe.2.1 _ h
    obtain ⟨L₁, k₁, rfl, lk⟩ := l₁.fieldOb_inv
    obtain ⟨ci, hci, hls, hlen, -⟩ := HTS.spineCod henv hΔ ihm.2 rfl W.left tv
    cases hci.symm.trans (henv.projectionConstructor hp)
    obtain ⟨L₂, hL₂⟩ := ctor_field_obs henv hΔ hp hPV hls hlen hnz W.left tv ihm.2 hpl
      (by simp) (j := j) (by simpa using hj) (k := k₁) (by rw [hfs j hj]; exact .proj ho₁)
    exact ⟨_, hL₂, .fieldOb lk⟩

omit hΔ in
theorem sound_unitLike {S : Name} {info : VProjectionInfo} (hp : env.projections S info)
    (hPV : ProjValid env S info) (hnf : info.numFields = 0) {ls : List VLevel}
    {params : List VExpr} {e e' : VExpr}
    (ihe : SoundAt env U Δ Γ e e (.mkApps (.const S ls) params) ∧
      HTS env U Δ Γ e (.mkApps (.const S ls) params))
    (ihe' : SoundAt env U Δ Γ e' e' (.mkApps (.const S ls) params) ∧
      HTS env U Δ Γ e' (.mkApps (.const S ls) params)) :
    SoundAt env U Δ Γ e e' (.mkApps (.const S ls) params) ∧
      HTS env U Δ Γ e (.mkApps (.const S ls) params) ∧
      HTS env U Δ Γ e' (.mkApps (.const S ls) params) := by
  refine ⟨?_, ihe.2, ihe'.2⟩
  have hst := hPV.1
  intro σ σ' S0 W tv tv'
  have n1 : ∀ o, ¬ Obs' σ S0 e o := fun o h => by
    obtain ⟨τs, hτs, hto⟩ := (ihe.1 σ σ' S0 W tv tv').2.2.1 o h
    obtain ⟨_, _, _, -, hj, -⟩ := typed_fam_fieldOb henv hp hst.famRigid hst.famNotProjCtor hto hτs
    omega
  have n2 : ∀ o, ¬ Obs' σ' S0 e' o := fun o h => by
    obtain ⟨τs, hτs, hto⟩ := (ihe'.1 σ σ' S0 W tv tv').2.2.2 o h
    obtain ⟨_, _, _, -, hj, -⟩ := typed_fam_fieldOb henv hp hst.famRigid hst.famNotProjCtor hto hτs
    omega
  exact ⟨fun o h => (n1 o h).elim, fun o h => (n2 o h).elim, fun o h => (n1 o h).elim,
    fun o h => (n2 o h).elim⟩

end

end Model
end VEnv
end Lean4Lean
