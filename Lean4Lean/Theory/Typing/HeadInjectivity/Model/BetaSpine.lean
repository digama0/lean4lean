import Lean4Lean.Theory.Typing.HeadInjectivity.Model.SpineCongr
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.TeleCompact
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.RuleSound

/-! # Soundness of a β-spine

`beta_spine_sub`: a closed, semantically typed and sound lambda telescope `wrapLams D G`
applied to arguments that are typed along `D` (a typed valuation of `D.reverse` by the
arguments, as `spine_tele` produces) has, up to subsumption in both directions, the
observations of the instantiated body `G.subst (argSubst args)` (right to left without
subsumption: every observation of the body is one of the application). Left to right the keys of the
application are typed keys along `D` (`Obs.wrapLams_iff`) whose anchors are related to the
arguments (`TeleKeys.substEq`), so the soundness of the body (`HTS.wrapLams_body`) changes the
anchors to the arguments and monotonicity enlarges the key observations to the arguments'
observations. Right to left, compactness (`Obs.compact_all`) bounds the observations of the
arguments the body observation needs, and `tele_compact` builds typed keys at the arguments
containing them.

`Obs.subst_argSubst` is the substitution lemma for the argument substitution: the observations
of `G.subst (argSubst args)` under `(σ, S)` are those of `G` under the argument valuation. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-- The substitution lemma for the argument substitution. -/
theorem Obs.subst_argSubst {G : VExpr} {args : List VExpr} (hG : G.ClosedN args.length)
    {σ : VExpr.Subst} {S : ObSets} {o : Ob} :
    Obs' σ S (G.subst (VExpr.argSubst args)) o ↔
      Obs' (VExpr.argSubst (args.map (·.subst σ))) (argSets env U Δ σ S args) G o := by
  rw [Obs.subst_iff]
  refine Obs.closed_iff hG (fun i hi => ?_) (fun i hi => ?_)
  · show ((VExpr.argSubst args) i).subst σ = _
    simp only [VExpr.argSubst, VExpr.foldl_cons_apply, List.length_map, hi, dite_true,
      List.getElem_map]
  · funext y
    simp only [VExpr.argSubst, VExpr.foldl_cons_apply, argSets, hi, dite_true]

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- **Soundness of a β-spine.** -/
theorem beta_spine_sub {D : List VExpr} {G P : VExpr} {args : List VExpr} {σ : VExpr.Subst}
    {S : ObSets} (hcl : (VExpr.wrapLams D G).ClosedN)
    (hL : HTS env U Δ [] (.wrapLams D G) P)
    (hLs : SoundAt env U Δ [] (.wrapLams D G) (.wrapLams D G) P) (has : args.length = D.length)
    (W : Ctx.SubstEq env U Δ (VExpr.argSubst (args.map (·.subst σ)))
      (VExpr.argSubst (args.map (·.subst σ))) D.reverse)
    (tv : TV env U Δ D.reverse (VExpr.argSubst (args.map (·.subst σ)))
      (argSets env U Δ σ S args)) :
    Ob.Sub (Obs' σ S (.mkApps (.wrapLams D G) args)) (Obs' σ S (G.subst (VExpr.argSubst args))) ∧
    ∀ o, Obs' σ S (G.subst (VExpr.argSubst args)) o → Obs' σ S (.mkApps (.wrapLams D G) args) o := by
  obtain ⟨hGcl, hDcl⟩ := closedN_wrapLams hcl
  simp only [Nat.zero_add] at hGcl hDcl
  rw [← has] at hGcl
  obtain ⟨B, hGs, hdoms⟩ := HTS.wrapLams_body hL hLs
  rw [List.append_nil] at hGs
  have hasl : (args.map (·.subst σ)).length = D.length := by simp [has]
  refine ⟨fun o ho => ?_, fun o ho => ?_⟩
  · obtain ⟨keys, hk, hw⟩ := wrap_of_obs_mkApps_le ho
    rw [Obs.closed_iff_id hcl] at hw
    obtain ⟨keys', v, vS, p, hTK, e, hp⟩ := Obs.wrapLams_iff.1 hw
    have hkl : keys.length = D.length := (List.Forall₂.length_eq hk).trans has
    obtain ⟨rfl, rfl⟩ := wrap_inj_len (by rw [hkl, hTK.length]) e
    have hcls := keys_cls_self hk
    have W' := hTK.substEq henv hΔ (v := .id) hdoms .nil hcls
    rw [List.append_nil] at W'
    have W'' : Ctx.SubstEq env U Δ v (VExpr.argSubst (args.map (·.subst σ))) D.reverse := W'
    have hctx : CtxSD env U Δ [] D.reverse := by
      have := DomsSD.ctxSD (L := []) (Γ := []) hdoms .nil
      simpa using this
    have hout : ∀ x, D.reverse.length ≤ x →
        VExpr.argSubst (args.map (·.subst σ)) x = v x := by
      intro x hx
      simp only [List.length_reverse] at hx
      obtain ⟨y, rfl⟩ : ∃ y, x = y + D.length := ⟨x - D.length, by omega⟩
      rw [(hTK.outer y).1, VExpr.argSubst_ge _ (by simp [has])]
      simp [has]; rfl
    obtain ⟨Wv, tvv⟩ := hTK.typed henv hΔ hdoms .nil TV.empty
    rw [List.append_nil] at Wv tvv
    have tv' : TV env U Δ D.reverse (VExpr.argSubst (args.map (·.subst σ))) vS := by
      have := TV.transfer henv hΔ (Γ := []) hctx (by simpa using SubstEq.symm henv hΔ W'')
        (by simpa using hout) (by simpa using tvv)
      simpa using this
    obtain ⟨o₁, ho₁, l₁⟩ := (hGs _ _ _ W'' tvv tv').1 o hp
    obtain ⟨ys, -, hvS, -, -, -⟩ := hTK.data
    have hk' : List.Forall₂ (fun (k : Key) a => ∀ y ∈ k.2.2, ∃ y₀, Obs' σ S a y₀ ∧ y₀ ≼ y)
        keys args := List.Forall₂.imp (fun _ _ h => h.2) hk
    obtain ⟨o₂, ho₂, l₂⟩ := ho₁.mono_le (S' := argSets env U Δ σ S args) fun i x hx => by
      rw [hvS] at hx
      exact extS_cover hk' i x hx
    exact ⟨o₂, (Obs.subst_argSubst hGcl).2 ho₂, l₂.trans l₁⟩
  · have ho' := (Obs.subst_argSubst hGcl).1 ho
    obtain ⟨Gs, hGl, hGS, hG⟩ := Obs.compact_all hGcl (τs := [o])
      (fun τ hτ => by rw [List.mem_singleton] at hτ; subst hτ; exact ho')
    obtain ⟨keys, S', hTK, hkl, hS', hkeys⟩ := tele_compact hDcl hasl W tv Gs.reverse
      (by simp [hGl, has]) (fun i Fi hFi y hy => by
        have hil : i < Gs.length := by
          have := (List.getElem?_eq_some_iff.1 hFi).1; simpa using this
        rw [List.getElem?_reverse hil, List.getElem?_eq_getElem (by omega)] at hFi
        cases hFi
        have := hGS (Gs.length - 1 - i) (by omega) y hy
        rwa [hGl, has] at this)
    have hG' : Obs' (VExpr.argSubst (args.map (·.subst σ))) S' G o := by
      refine hG S' (fun m hm y hy => ?_) o (List.mem_singleton_self _)
      have hmD : m < D.length := by rw [← has, ← hGl]; exact hm
      have hkD : D.length - 1 - m < keys.length := by omega
      refine (hS' m keys[D.length - 1 - m] (List.getElem?_eq_getElem hkD) hmD y).2 ?_
      refine (hkeys _ _ (List.getElem?_eq_getElem hkD)).1 Gs[m] ?_ y hy
      rw [List.getElem?_reverse (by omega), List.getElem?_eq_getElem (by omega)]
      congr 2; omega
    have hw : Obs' .id .empty (.wrapLams D G) (wrap keys o) :=
      Obs.wrapLams_iff.2 ⟨keys, _, _, o, hTK, rfl, hG'⟩
    refine obs_mkApps_of_wrap_le ?_ ((Obs.closed_iff_id hcl).2 hw)
    obtain ⟨ys, hv, -, hyl, -, hd⟩ := hTK.data
    have hys : ys = args.map (·.subst σ) := argSubst_inj (by rw [hyl, hasl]) hv.symm
    subst hys
    refine List.forall₂_of_getElem (by rw [hkl, has]) fun i hi hi' => ?_
    have hiD : i < D.length := by omega
    obtain ⟨-, hsub, a, A, ha, hA, hcl'⟩ := hkeys i keys[i] (List.getElem?_eq_getElem hi)
    rw [List.getElem?_map, List.getElem?_eq_getElem hi'] at ha
    rw [List.getElem?_eq_getElem hiD] at hA
    cases ha; cases hA
    obtain ⟨hk1, -, -, -, -⟩ := hd i keys[i] ((args.map (·.subst σ))[i]'(by simpa using hi'))
      D[i] (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem _)
      (List.getElem?_eq_getElem hiD)
    refine ⟨?_, keys[i].2.2, fun y hy => ?_, Covers.refl⟩
    · have e : keys[i].1 = TyCls env U Δ (D[i].subst
          (VExpr.argSubst (((args.map (·.subst σ)).take i)))) := hk1
      rw [hcl', e]
    · have := hsub y hy
      rw [← has] at this
      exact (argSets_get (List.getElem?_eq_getElem hi')).1 this

end

end Model
end VEnv
end Lean4Lean
