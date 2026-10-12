import Lean4Lean.Theory.Typing.HeadInjectivity.Model.TeleSound
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.MajorRel
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.IotaGeneric

/-! # Soundness of an instance of an ι rule

An instance of a registered ι rule is a redex `e = rec m1 (recArgs ++ [ctor lsC ctorArgs])`
with arbitrary terms at the index and constructor-parameter holes, and its reduct
`red = (rhs.instL m1) argsR` with `argsR = recArgs.take k ++ ctorArgs.drop cnp` (the
parameters, motives, minors and fields). The two directions of its soundness are read at the
*argument valuation* `v = argSubst (argsR σ)`, `vS = argSets σ S argsR` of the reduct
template's binders:

* left to right (`iota_lhs_sub_inst`): an observation of the redex comes from the `pat` clause
  of the recursor, whose binding `τ` of the template's variables is definitionally equal to
  `v` (a leading argument by the key class, an index-bound field by the relation of the index
  argument to the field, `hlead`; a constructor field by the constructor class of the major;
  a projection field by the eta anchor; a proof field by proof irrelevance), so the body
  observation transfers to `v` and the β-spine (`beta_spine_sub`) makes it one of the reduct.

The typing of the arguments along the template (`Wv`, `tvv`) and the relation of the index
arguments to the fields they bind (`hlead`) are hypotheses here; `Model/IotaRel.lean` derives
them for the rules of ordinary blocks. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

theorem iotaFs_getElem? {nf j x : Nat} (h : (iotaFs nf)[j]? = some x) : j < nf ∧ x = nf - 1 - j := by
  simp only [iotaFs, List.getElem?_eq_some_iff, List.length_reverse,
    List.length_range] at h
  obtain ⟨hj, e⟩ := h
  simp only [List.getElem_reverse, List.getElem_range, List.length_range] at e
  exact ⟨hj, e.symm⟩

/-- The argument of the reduct at a field variable. -/
theorem argsR_field {argsR recArgs ctorArgs : List VExpr} {k cnp nf j : Nat}
    (hargs : argsR = recArgs.take k ++ ctorArgs.drop cnp) (hrA : k ≤ recArgs.length)
    (hcA : ctorArgs.length = cnp + nf) (hj : j < nf) :
    argsR.length = k + nf ∧ ∃ h : argsR.length - 1 - (nf - 1 - j) < argsR.length,
      argsR[argsR.length - 1 - (nf - 1 - j)] = ctorArgs[cnp + j]'(by omega) := by
  subst hargs
  have hl : (recArgs.take k ++ ctorArgs.drop cnp).length = k + nf := by simp; omega
  refine ⟨hl, by omega, ?_⟩
  rw [List.getElem_append_right (by simp; omega)]
  simp only [List.getElem_drop, List.length_take]
  congr 1; simp; omega

theorem argSubst_field {argsR recArgs ctorArgs : List VExpr} {k cnp nf j : Nat} {σ : VExpr.Subst}
    (hargs : argsR = recArgs.take k ++ ctorArgs.drop cnp) (hrA : k ≤ recArgs.length)
    (hcA : ctorArgs.length = cnp + nf) (hj : j < nf) :
    VExpr.argSubst (argsR.map (·.subst σ)) (nf - 1 - j) =
      (ctorArgs[cnp + j]'(by omega)).subst σ := by
  obtain ⟨hl, h, e⟩ := argsR_field (j := j) hargs hrA hcA hj
  rw [VExpr.argSubst_lt _ (by simp; omega)]
  simp only [List.getElem_map, List.length_map]
  rw [e]

theorem argSets_field {argsR recArgs ctorArgs : List VExpr} {k cnp nf j : Nat} {σ : VExpr.Subst}
    {S : ObSets} (hargs : argsR = recArgs.take k ++ ctorArgs.drop cnp) (hrA : k ≤ recArgs.length)
    (hcA : ctorArgs.length = cnp + nf) (hj : j < nf) :
    argSets env U Δ σ S argsR (nf - 1 - j) = Obs' σ S (ctorArgs[cnp + j]'(by omega)) := by
  obtain ⟨hl, h, e⟩ := argsR_field (j := j) hargs hrA hcA hj
  simp only [argSets, show nf - 1 - j < argsR.length by omega, dite_true]
  rw [e]

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- **The eta binding class** (right to left) at an arbitrary argument of the constructor
spine: the class of the projections onto the field at `q` of the class of the spine at its
type is the class of the argument at any type `A₀` whose class is the domain class of the spine
at `q`. -/
theorem eta_field_cls_gen {I : Name} {info : VProjectionInfo} (hp : env.projections I info)
    (hPV : ProjValid env I info)
    {Γ' : List VExpr} {v : VExpr.Subst} {vS : ObSets} (Wv : Ctx.SubstEq env U Δ v v Γ')
    (tvv : TV env U Δ Γ' v vS) {lsc : List VLevel} {margs : List VExpr} {Tm : VExpr}
    (H : HTS env U Δ Γ' (.mkApps (.const info.ctorName lsc) margs) Tm)
    (hsd : SD env U Δ Γ' (.mkApps (.const info.ctorName lsc) margs)
      (.mkApps (.const info.ctorName lsc) margs) Tm)
    (hlen : margs.length = info.nparams + info.numFields)
    (hnz : (info.resultLevel.inst lsc).IsNeverZero)
    {q : Nat} (hql : q < margs.length) (hnq : info.nparams ≤ q) {A₀ : VExpr}
    (hA : ∀ Aq Bq, HTS env U Δ Γ' (.mkApps (.const info.ctorName lsc) (margs.take q))
      (.forallE Aq Bq) → TyCls env U Δ A₀ = TyCls env U Δ (Aq.subst v)) :
    projCls env U Δ I (q - info.nparams)
        (ElCls env U Δ (TyCls env U Δ (Tm.subst v))
          ((VExpr.mkApps (.const info.ctorName lsc) margs).subst v))
        (TyCls env U Δ A₀) = ElCls env U Δ (TyCls env U Δ A₀) ((margs[q]'hql).subst v) ∧
    env.HasType U Δ ((margs[q]'hql).subst v) A₀ := by
  obtain ⟨Aq, Bq, hfq, -, hsq⟩ := HTS.spine_at _ rfl H q hql
  have eAq := hA Aq Bq hfq
  have hvx : env.HasType U Δ ((margs[q]'hql).subst v) A₀ := by
    have h := hsq.1.defeq.hasType.1.substDF henv Wv.wf hΔ Wv
    have hm : TyCls env U Δ (Aq.subst v) A₀ := by rw [← eAq]; exact TyCls.self
    exact TyCls.defeq_rev henv hΔ hm h
  refine ⟨?_, hvx⟩
  obtain ⟨hst, envTypes, hOrig, hsnd⟩ := hPV
  have hctor := henv.ordered.projectionConstructor hp
  obtain ⟨doms, idx, hshape, hnpD, hidx⟩ := hOrig.origin.ctorType_shape
  obtain ⟨base, dsb, decl, type, ctor, hbase, htypes, hle, hord, -, -, -, hu, -, -, -, -, hct,
    -, hwfE, -⟩ := hOrig
  have hwf : env.IsType info.uvars [] info.ctorType := by
    rw [hu, hct]; exact hwfE.mono hle
  -- the levels
  have hMσ : env.HasType U Δ (VExpr.mkApps (.const info.ctorName lsc) (margs.map (·.subst v)))
      (Tm.subst v) := by
    have := hsd.1.defeq.hasType.1.substDF henv Wv.wf hΔ Wv
    rw [VExpr.subst_mkApps] at this; exact this
  obtain ⟨_, hc⟩ := HasType.mkApps_fn henv hΔ hMσ
  obtain ⟨ci', hci', hls, hlsl⟩ := HasType.const_inv henv hΔ hc
  rw [hctor] at hci'
  cases hci'
  -- the telescope
  generalize hRdef : VExpr.mkApps (.const I (VLevel.params info.uvars))
    ((List.range info.nparams).reverse.map
      (fun i => VExpr.bvar (doms.length - info.nparams + i)) ++ idx) = R at hshape
  have eT : info.ctorType.instL lsc =
      VExpr.wrapForalls (doms.map (·.instL lsc)) (R.instL lsc) := by
    rw [hshape, VExpr.instL_wrapForalls]
  have hTW : Ob.Sub (Obs' .id .empty ((⟨info.uvars, info.ctorType⟩ : VConstant).type.instL lsc))
      (Obs' .id .empty (.wrapForalls (doms.map (·.instL lsc)) (R.instL lsc))) :=
    fun o h => ⟨o, by rw [← eT]; exact h, .refl⟩
  have hpi : PiSD env U Δ [] (doms.map (·.instL lsc)) (R.instL lsc) := by
    obtain ⟨w, h⟩ := IsType.instL hls hwfE
    rw [← hct, hshape, VExpr.instL_wrapForalls] at h
    exact piSD_of hord.orderedStrong hle (SoundTypedIn.soundIn (hsnd U Δ hΔ)) trivial h
  have hnf := (ProjTele.of (S := I) henv (hRdef ▸ hshape) hwf hls).numFields
  simp only [List.length_map] at hnf
  have hDl : (doms.map (·.instL lsc)).length = margs.length := by simp; omega
  have hpre := spine_tele_prefix henv hΔ H Wv tvv hctor hTW hpi (by omega)
  -- the substituted arguments, typed along the constructor telescope
  generalize hmσ : margs.map (·.subst v) = mσ at hMσ
  have hmσl : mσ.length = margs.length := by rw [← hmσ]; simp
  have hpre' : ∀ i ≤ mσ.length, Ctx.SubstEq env U Δ (VExpr.argSubst (mσ.take i))
      (VExpr.argSubst (mσ.take i)) ((doms.map (·.instL lsc)).take i).reverse := by
    intro i hi
    have := (hpre i (by omega)).1
    rwa [List.map_take, hmσ] at this
  have hargs := ArgsTyped.of_prefixes (R0 := R.instL lsc) hpre' (by omega)
  rw [← eT, ← List.take_append_drop info.nparams mσ] at hargs
  have hpl : (mσ.take info.nparams).length = info.nparams := by simp; omega
  have hfl : (mσ.drop info.nparams).length = info.numFields := by simp; omega
  have hi : q - info.nparams < (mσ.drop info.nparams).length := by rw [hfl]; omega
  have hfx : (mσ.drop info.nparams)[q - info.nparams] = (margs[q]'hql).subst v := by
    rw [List.getElem_drop]
    have : mσ[q]'(by omega) = (margs[q]'hql).subst v := by
      subst hmσ; rw [List.getElem_map]
    rw [← this]; congr 1; omega
  obtain ⟨hmk, F, hF, -, heq⟩ := ctor_projCls henv hΔ hp hst.ctorClosed hls hlsl hnz
    (hRdef ▸ hshape) hidx hwf hctor hargs hpl hfl hi
  -- the class of the major key is the class of the constructor's result
  have e5 : TyCls env U Δ (Tm.subst v) = TyCls env U Δ (VExpr.mkApps (.const I lsc)
      (mσ.take info.nparams ++ idx.map fun e =>
        (e.instL lsc).subst (VExpr.argSubst (mσ.take info.nparams ++ mσ.drop info.nparams)))) := by
    have := spine_res_cls henv hΔ hctor hTW hpi (by omega)
      (fun h => by simp [h] at hql) Wv tvv H
    rw [hmσ, ← List.take_append_drop info.nparams mσ, ← hRdef] at this
    rw [this, spine_result hlsl hpl (by simp; omega)]
  -- the class of the field is the class of the projection's field type
  have e1 : TyCls env U Δ A₀ = TyCls env U Δ (Aq.subst v) := eAq
  have e2 := spine_dom_cls henv hΔ hctor hTW hpi (by simp; omega) Wv tvv hfq
  have W0 := hpre' info.nparams (by omega)
  obtain ⟨d, u, hd, hconv⟩ := proj_fieldTy_conv henv hΔ hp hst.ctorClosed hls hlsl hnz
    (hRdef ▸ hshape) hidx hwf hctor hargs hpl hfl W0 hi hF
  have e3 := TyCls.eq_of_defeq hconv
  have hd' : (doms.map (·.instL lsc))[(margs.take q).length]'(by simp; omega) = d := by
    rw [← Option.some_inj, ← List.getElem?_eq_getElem, ← hd]
    congr 1; simp; omega
  have hmq : (margs.take q).map (·.subst v) =
      mσ.take info.nparams ++ (mσ.drop info.nparams).take (q - info.nparams) := by
    rw [List.map_take, hmσ, ← List.take_add, Nat.add_sub_cancel' hnq]
  have eA : TyCls env U Δ A₀ = TyCls env U Δ F := by
    rw [e1, e2, hd', hmq, e3]
  rw [List.take_append_drop] at heq e5
  rw [e5, eA, VExpr.subst_mkApps, hmσ]
  simp only [VExpr.subst]
  rw [heq, hfx]


/-- **Left to right** for an instance of an ι rule. -/
theorem iota_lhs_sub_inst {n ctor : Name} {k nind cnp nf : Nat} {rhs : VExpr} {hc : rhs.Closed}
    {doms : List VExpr} {body : VExpr}
    (hp : env.pats (SimplePattern.iota n (k + nind) ctor (cnp + nf)).toPattern
      (SimplePattern.iotaRHS' n ctor k nind cnp nf rhs hc, .true))
    (hr : rhs = .wrapLams doms body)
    {ci : VConstant} {dsH : List VExpr} {RH : VExpr} {I : Name} {lsI : List VLevel}
    {iargs lead : List VExpr}
    (hci : env.constants n = some ci)
    (hstat : IotaStatic ci ctor k nind nf doms dsH RH I lsI iargs lead)
    (hleadU : LeadUniq ci ctor k nind nf lead)
    (huniq : PatUniq env n ctor k nind cnp nf rhs)
    (hcrig : env.Rigid ctor) (hctor : ∀ c, IsCtor env c → env.Rigid c)
    (hpctor : ∀ c, IsProjCtor env c → env.Rigid c)
    (hnodf : ∀ df', env.defeqs df' → ∀ ls', df'.lhs.stripLams.getAppFnArgs.1 ≠ .const n ls')
    (hfam : MajorFamEntry env I ctor)
    {m1 lsC : List VLevel} {recArgs ctorArgs argsR : List VExpr}
    (hrA : recArgs.length = k + nind) (hcA : ctorArgs.length = cnp + nf)
    (hargs : argsR = recArgs.take k ++ ctorArgs.drop cnp)
    {T : VExpr} (hRH : HTS env U Δ [] (rhs.instL m1) T)
    (hRS : SoundAt env U Δ [] (rhs.instL m1) (rhs.instL m1) T)
    {σ v : VExpr.Subst} {S vS : ObSets}
    (hv : v = VExpr.argSubst (argsR.map (·.subst σ))) (hvS : vS = argSets env U Δ σ S argsR)
    (Wv : Ctx.SubstEq env U Δ v v (doms.map (·.instL m1)).reverse)
    (tvv : TV env U Δ (doms.map (·.instL m1)).reverse v vS)
    (hlead : ∀ (i x : Nat), lead[i]? = some (VExpr.bvar x) → x < doms.length →
      (∀ j < i, lead[j]? ≠ some (VExpr.bvar x)) → ∃ a : VExpr, recArgs[i]? = some a ∧
        (∃ X, TyCls env U Δ ((binderTy doms m1 x).subst v) X ∧
          env.IsDefEq U Δ (a.subst σ) (v x) X) ∧ Ob.Sub (Obs' σ S a) (vS x)) :
    Ob.Sub (Obs' σ S (.mkApps (.const n m1) (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs])))
      (Obs' σ S (.mkApps (rhs.instL m1) argsR)) := by
  have hrcl : rhs.ClosedN := hc
  have hleadl : lead.length = k + nind := hstat.lead_length
  obtain ⟨hdl, eH, hlenH0, hkH0, -⟩ := hstat
  have hlenH : dsH.length = lead.length + 1 := by rw [hleadl]; exact hlenH0
  have hkH : dsH[lead.length]? = some (.mkApps (.const I lsI) iargs) := by rw [hleadl]; exact hkH0
  have hal : argsR.length = doms.length := by subst hargs; simp; omega
  -- the reduct template
  have eR : rhs.instL m1 = .wrapLams (doms.map (·.instL m1)) (body.instL m1) := by
    rw [hr, VExpr.instL_wrapLams]
  have hbcl : (body.instL m1).ClosedN doms.length := by
    have := (closedN_wrapLams (hr ▸ hrcl : (VExpr.wrapLams doms body).ClosedN 0)).1
    simpa using this.instL
  have hdcl : ∀ i (h : i < doms.length), (doms[i]).ClosedN i := by
    have := (closedN_wrapLams (hr ▸ hrcl : (VExpr.wrapLams doms body).ClosedN 0)).2
    simpa using this
  rw [eR] at hRH hRS
  obtain ⟨B, hBs, hdomsR⟩ := HTS.wrapLams_body hRH hRS
  rw [List.append_nil] at hBs
  intro o ho
  obtain ⟨keys, hkeys, hc'⟩ := wrap_of_obs_mkApps_le ho
  have hnrig : ¬ env.Rigid n := fun hrig => hrig.pats _ _ hp (SimplePattern.iota_headConst ..)
  rcases Obs.const_iff.1 hc' with ⟨_, _, _, _, _, hrig, _⟩ | ⟨df', _, _, hdf', hlhs', _⟩ |
    ⟨_, _, _, _, _, hcn, _⟩ |
    ⟨df', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdf', hl', _⟩ |
    ⟨k'', nind'', ctor'', cnp'', nf'', rhs'', hc'', doms'', body'', ci', τs, lkeys, Dm, cm, Km,
      p'', mC, τ, S'', I', ℓsI', mI', dsH', RH', lsI', iargs', lead'', e, hp'', hr'', hstatic,
      hci'', -, -, hlen'', hsingle, -, hhd, hbind, -, hbody⟩ |
    ⟨fam, info, _, _, _, _, _, hpi, hcn, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hrig, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, hrig, _⟩
  · exact absurd hrig hnrig
  · exact absurd (by rw [hlhs']; rfl) (hnodf df' hdf' _)
  · exact absurd (hctor n hcn) hnrig
  · exact absurd (by rw [hl']; exact VExpr.stripLams_wrapLams_mkApps_head) (hnodf df' hdf' _)
  rotate_left
  · exact absurd (hpctor n ⟨fam, info, hpi, hcn⟩) hnrig
  · exact absurd hrig hnrig
  · exact absurd hrig hnrig
  obtain ⟨hleadlen, huq⟩ := huniq _ _ _ _ _ _ _ hp''
  have hklen : keys.length = lead.length + 1 := by
    have := List.Forall₂.length_eq hkeys; simp at this; omega
  obtain ⟨ekeys, rfl⟩ := wrap_inj_len (by simp [hklen, hlen'', hleadlen, hleadl]) e
  subst ekeys
  obtain ⟨lkeys', mk, ekl, hkeysL, hkM⟩ := List.forall₂_snoc_right hkeys
  obtain ⟨rfl, emk⟩ := List.append_inj' ekl (by simp)
  cases emk
  obtain ⟨hcmM, hKmcov⟩ := hkM
  cases hci.symm.trans hci''
  -- the clause's constructor is the rule's
  have hctor_eq : ctor'' = ctor := by
    cases mC with
    | true =>
      obtain ⟨h, -⟩ := hsingle rfl _ _ hp (SimplePattern.iota_headConst ..)
      exact (iota_toPattern_inj h).2.2.1.symm
    | false =>
      rcases hhd rfl with ⟨ℓs, hmem⟩ | hEH
      · obtain ⟨y, hy, ly⟩ := hKmcov _ hmem
        rw [ly.ctorHead_inv] at hy
        obtain ⟨_, _, hend⟩ := ctor_spine_inv hcrig hy (.inl ⟨_, _, _, rfl⟩)
        rcases hend with h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩
        · injection h
        · cases h
        · cases h
      · have hll : lkeys.length = lead.length := by rw [hlen'', hleadlen, hleadl]
        obtain ⟨rfl, info', hpi', hcn'⟩ :=
          hEH.fam eH (by rw [hll]; exact hlenH) (by rw [hll]; exact hkH)
        rcases hfam with ⟨hnp, -⟩ | ⟨info, hpi, hcn⟩
        · exact absurd hpi' (hnp _)
        · cases henv.ordered.projections_unique hpi hpi'
          exact hcn'.symm.trans hcn
  subst ctor''
  obtain ⟨hk1, hk2, hk3, hk4, hrhs⟩ := huq rfl
  subst k'' nind'' cnp'' nf''
  subst hrhs
  have hdl'' : doms''.length = doms.length := by rw [hstatic.1, hdl]
  obtain ⟨hd1, hd2⟩ := wrapLams_inj_len hdl'' (hr''.symm.trans hr)
  subst doms'' body''
  have hlead_eq : lead'' = lead := hleadU _ _ _ _ _ _ _ hstatic
  subst lead''
  -- the fields of the major
  have hkr : k ≤ recArgs.length := by omega
  have hvF : ∀ j x, (iotaFs nf)[j]? = some x → ∃ h : cnp + j < ctorArgs.length,
      v x = (ctorArgs[cnp + j]'h).subst σ ∧ vS x = Obs' σ S (ctorArgs[cnp + j]'h) := by
    intro j x hj
    obtain ⟨hjn, rfl⟩ := iotaFs_getElem? hj
    refine ⟨by omega, ?_, ?_⟩
    · rw [hv]; exact argSubst_field hargs hkr hcA hjn
    · rw [hvS]; exact argSets_field hargs hkr hcA hjn
  have argOf : ∀ j x cl, (iotaFs nf)[j]? = some x → .ctorArg (cnp + j) cl ∈ Km → cl (v x) := by
    intro j x cl hj hcl
    obtain ⟨y, hy, ly⟩ := hKmcov _ hcl
    rw [ly.ctorArg_inv] at hy
    obtain ⟨ckeys, hck, hend⟩ := ctor_spine_inv hcrig hy (.inr (.inl ⟨_, _, rfl⟩))
    rcases hend with h | ⟨i, hi, h⟩ | ⟨_, _, _, _, h⟩
    · cases h
    · injection h with e1 e2; subst e1; subst e2
      obtain ⟨hil, hvx, -⟩ := hvF j x hj
      obtain ⟨_, hci', -⟩ := List.forall₂_getElem_exists hck _ hi
      rw [hci', hvx]; exact ElCls.self
    · cases h
  have argObOf : ∀ j x pre k, (iotaFs nf)[j]? = some x →
      .ctorArgOb (cnp + j) pre k ∈ Km → ∃ k', vS x k' ∧ k' ≼ k := by
    intro j x pre k hj hk
    obtain ⟨y, hy, ly⟩ := hKmcov _ hk
    obtain ⟨k₀, rfl, l₀⟩ := ly.ctorArgOb_inv
    obtain ⟨ckeys, hck, hend⟩ := ctor_spine_inv hcrig hy (.inr (.inr ⟨_, _, _, rfl⟩))
    rcases hend with h | ⟨_, _, h⟩ | ⟨i, hi, k', hk', h⟩
    · cases h
    · cases h
    · injection h with e1 e2 e3; subst e1
      obtain ⟨hil, -, hvS'⟩ := hvF j x hj
      obtain ⟨_, -, hcov⟩ := List.forall₂_getElem_exists hck _ hi
      obtain ⟨k₁, hk₁, l₁⟩ := hcov k' hk'
      exact ⟨k₁, by rw [hvS']; exact hk₁, l₁.trans (e3 ▸ l₀)⟩
  -- the binding, restricted to the rule's variables
  classical
  let τ' : VExpr.Subst := fun x => if x < doms.length then τ x else v x
  let S' : ObSets := fun x => if x < doms.length then S'' x else vS x
  have hτ'1 : ∀ x, x < doms.length → τ' x = τ x := fun x hx => if_pos hx
  have hτ'2 : ∀ x, doms.length ≤ x → τ' x = v x := fun x hx => if_neg (by omega)
  have hbody' : Obs' τ' S' (body.instL m1) o :=
    (Obs.closed_iff hbcl (fun i hi => (hτ'1 i hi).symm) (fun i hi => (if_pos hi).symm)).1 hbody
  have hcov : ∀ x o, S' x o → ∃ o', vS x o' ∧ o' ≼ o := by
    intro x o ho
    by_cases hx : x < doms.length
    · simp only [S', hx, if_true] at ho
      rcases hbind.2 x hx with ⟨i, k, hi, hfirst, hki, -, -, hkS⟩ |
        ⟨-, j, hj, ⟨-, -, -, -, -, hS⟩ | ⟨-, -, hS⟩ | ⟨-, info', hpi', -, hle', -, -, -, hS⟩⟩
      · obtain ⟨o₀, ho₀, l₀⟩ := hkS o ho
        have hil : i < lkeys.length := by
          have := List.Forall₂.length_eq hkeysL
          have := (List.getElem?_eq_some_iff.1 hi).1; simp at *; omega
        obtain ⟨a, ha, -, hsub⟩ := hlead i x hi hx hfirst
        obtain ⟨_, -, hcov⟩ := List.forall₂_getElem_exists hkeysL i hil
        have hk : lkeys[i] = k := (List.getElem?_eq_some_iff.1 hki).2
        rw [hk] at hcov
        obtain ⟨o₁, ho₁, l₁⟩ := hcov o₀ ho₀
        have ha' : recArgs[i]'(by have := List.Forall₂.length_eq hkeysL; omega) = a :=
          (List.getElem?_eq_some_iff.1 ha).2
        rw [ha'] at ho₁
        obtain ⟨o₂, ho₂, l₂⟩ := hsub o₁ ho₁
        exact ⟨o₂, ho₂, l₂.trans (l₁.trans l₀)⟩
      · rw [hS] at ho
        obtain ⟨pre, hpre⟩ := ho
        exact argObOf j x pre o hj hpre
      · rw [hS] at ho; cases ho
      · -- eta: a field observation of the major key
        rw [hS] at ho
        obtain ⟨L, hmem⟩ := ho
        obtain ⟨y, hy, ly⟩ := hKmcov _ hmem
        obtain ⟨L', y₀, rfl, l₀⟩ := ly.fieldOb_inv
        obtain ⟨info'', hpi'', -, a, ha, k', hk', l'⟩ := projctor_spine_inv hcrig hy
        cases henv.ordered.projections_unique hpi' hpi''
        obtain ⟨hil, -, hvS'⟩ := hvF j x hj
        rw [show info'.nparams + (cnp + j - info'.nparams) = cnp + j by omega,
          List.getElem?_eq_getElem hil] at ha
        cases ha
        exact ⟨k', by rw [hvS']; exact hk', l'.trans l₀⟩
    · simp only [S', hx, if_false] at ho
      exact ⟨o, ho, .refl⟩
  obtain ⟨p₁, hp₁, l₁⟩ := hbody'.mono_le hcov
  -- the binding is related to the argument valuation
  have hL := fun x (hx : x < doms.length) => lookup_binderTy (Γ := []) (ls := m1) hx
  have hbcl' : ∀ x, x < doms.length →
      (binderTy doms m1 x).subst τ = (binderTy doms m1 x).subst τ' := fun x hx =>
    (binderTy_closed hdcl hx).subst_congr fun i hi => (hτ'1 i hi).symm
  have Wv' : Ctx.SubstEq env U Δ v v ((doms.map (·.instL m1)).reverse ++ []) := by
    simpa using Wv
  have W' : Ctx.SubstEq env U Δ τ' v ((doms.map (·.instL m1)).reverse ++ []) := by
    refine SubstEq.of_heads_ind Wv' (fun x hx => hτ'2 x (by simpa using hx))
      fun x A hx hLA hW => ?_
    have hx' : x < doms.length := by simpa using hx
    cases hLA.uniq (hL x hx')
    rw [hτ'1 x hx', ← hbcl' x hx']
    have hvx := (Wv'.lookup (hL x hx')).hasType.1
    have hD := SubstEq.entry_typed Wv' hx
    obtain ⟨uD, hDt⟩ := hD
    have hDD := hDt.substDF henv hW.wf hΔ hW
    have eA : (binderTy doms m1 x) =
        ((doms.map (fun d : VExpr => d.instL m1)).reverse[x]'hx).liftN (x+1) := (hL x hx').uniq
          (lookup_append _ x hx)
    have e1 := liftN_subst_shift ((doms.map (fun d : VExpr => d.instL m1)).reverse[x]'hx) τ' x
    have e2 := liftN_subst_shift ((doms.map (fun d : VExpr => d.instL m1)).reverse[x]'hx) v x
    rw [← eA] at e1 e2
    -- the type conversion between the two substitutions
    have hconv : ∀ {a b : VExpr}, env.IsDefEq U Δ a b ((binderTy doms m1 x).subst v) →
        env.IsDefEq U Δ a b ((binderTy doms m1 x).subst τ) := by
      intro a b h
      rw [hbcl' x hx', e1]; rw [e2] at h; exact hDD.symm.defeqDF h
    have hvx' : env.HasType U Δ (v x) ((binderTy doms m1 x).subst τ) := hconv hvx
    rcases hbind.2 x hx' with ⟨i, k, hi, hfirst, hki, hkt, hkm, -⟩ |
      ⟨-, j, hj, ⟨-, cl, hcl, hct, hcm, -⟩ | ⟨⟨X, hX, hτX⟩, ⟨P, hP, hPs⟩, -⟩ |
        ⟨-, info', hpi', hcn', hle', -, hTE, hpc, -⟩⟩
    · have hil : i < lkeys.length := by
        have := List.Forall₂.length_eq hkeysL
        have := (List.getElem?_eq_some_iff.1 hi).1; simp at *; omega
      obtain ⟨a, ha, ⟨X, hX, hav⟩, -⟩ := hlead i x hi hx' hfirst
      obtain ⟨_, hcls, -⟩ := List.forall₂_getElem_exists hkeysL i hil
      have hk : lkeys[i] = k := (List.getElem?_eq_some_iff.1 hki).2
      have ha' : recArgs[i]'(by have := List.Forall₂.length_eq hkeysL; omega) = a :=
        (List.getElem?_eq_some_iff.1 ha).2
      rw [hk, ha'] at hcls
      have hka : k.2.1 (a.subst σ) := by rw [hcls]; exact ElCls.self
      have h1 := hkt.defeq henv hΔ hkm hka
      exact h1.trans (hconv (TyCls.defeq henv hΔ hX hav))
    · exact hct.defeq henv hΔ hcm (argOf j x cl hj hcl)
    · -- proof binding: both are proofs of the proposition `P`
      have hτx : env.HasType U Δ (τ x) ((binderTy doms m1 x).subst τ) :=
        TyCls.defeq henv hΔ hX hτX
      have h1 := TyCls.defeq_rev henv hΔ hP hτx
      have h2 := TyCls.defeq_rev henv hΔ hP hvx'
      exact TyCls.defeq henv hΔ hP (.proofIrrel hPs h1 h2)
    · -- eta binding: the anchor is a projection of the major, whose field is `v x`
      obtain ⟨hil, hvx, -⟩ := hvF j x hj
      refine eta_anchor_defeq henv hΔ hpi' hTE hpc (lsc := lsC)
        (margs := ctorArgs.map (·.subst σ)) (a := v x) ?_ ?_ hvx'
      · rw [show cm = (Dm, cm, Km).2.1 from rfl, hcmM]
        simp only [VExpr.subst_mkApps, VExpr.subst]
        rw [hcn']; exact ElCls.self
      · rw [List.getElem?_map,
          show info'.nparams + (cnp + j - info'.nparams) = cnp + j by omega,
          List.getElem?_eq_getElem hil, hvx]
        rfl
  have hctx := DomsSD.ctxSD (L := []) (Γ := []) hdomsR .nil
  simp only [List.append_nil] at hctx
  have tvv' : TV env U Δ ((doms.map (·.instL m1)).reverse ++ []) v vS := by simpa using tvv
  have tvτ := TV.transfer henv hΔ (by simpa using hctx) W' (fun x hx => hτ'2 x (by simpa using hx))
    tvv'
  obtain ⟨p₂, hp₂, l₂⟩ := (hBs τ' v vS (by simpa using W') (by simpa using tvτ) tvv).1 p₁ hp₁
  -- the β-spine of the reduct
  have hRcl : (VExpr.wrapLams (doms.map (·.instL m1)) (body.instL m1)).ClosedN := by
    rw [← eR]; exact hrcl.instL
  have hal' : argsR.length = (doms.map (·.instL m1)).length := by simp [hal]
  rw [hv] at Wv; rw [hv, hvS] at tvv
  have hβ := (beta_spine_sub henv hΔ hRcl hRH hRS hal' Wv tvv).2 p₂
    ((Obs.subst_argSubst (by rw [hal]; exact hbcl)).2 (by rw [← hv, ← hvS]; exact hp₂))
  exact ⟨p₂, by rw [eR]; exact hβ, l₂.trans l₁⟩


omit henv hΔ in
/-- Choice of one list per argument. -/
theorem exists_lists_of_getElem {α : Type} {args : List VExpr} {P : Nat → VExpr → List α → Prop}
    (h : ∀ i (hi : i < args.length), ∃ K, P i args[i] K) :
    ∃ Ks : List (List α), ∃ hl : Ks.length = args.length,
      ∀ i (hi : i < args.length), P i args[i] (Ks[i]'(hl ▸ hi)) := by
  classical
  refine ⟨List.ofFn fun i : Fin args.length => Classical.choose (h i i.2), by simp, fun i hi => ?_⟩
  simp only [List.getElem_ofFn]
  exact Classical.choose_spec (h i hi)

/-- **The lead binding of an instance** (right to left): the key of a leading argument `a` of
the redex binds a variable whose type class is the domain class of the spine at `a`
(`hTy`) and whose value is equal to `a` (`hdef`), covering the demanded observations. -/
theorem bind_lead_inst {Γ : List VExpr} {hd : VExpr} {recArgs : List VExpr}
    {σ : VExpr.Subst} {S : ObSets} (W : Ctx.SubstEq env U Δ σ σ Γ)
    {infoL : List (Key × VExpr)} (hinfoL : List.Forall₂ (KeyData env U Δ Γ σ S) infoL recArgs)
    (PT : ∀ i (hi : i < infoL.length), ∃ B,
      HTS env U Δ Γ (.mkApps hd (recArgs.take i)) (.forallE (infoL[i]'hi).2 B))
    {Ks : List (List Ob)} (hKsi : List.Forall₂ (fun K (ka : Key × VExpr) => ∀ y ∈ K, y ∈ ka.1.2.2)
      Ks infoL)
    {i : Nat} {a vx A₀ : VExpr} (ha : recArgs[i]? = some a)
    (hTy : ∀ Aq Bq, HTS env U Δ Γ (.mkApps hd (recArgs.take i)) (.forallE Aq Bq) →
      TyCls env U Δ A₀ = TyCls env U Δ (Aq.subst σ))
    (hdef : ∃ X, TyCls env U Δ A₀ X ∧ env.IsDefEq U Δ (a.subst σ) vx X)
    {L : List Ob} (hL : ∀ y ∈ L, ∃ y' ∈ (Ks[i]?).getD [], y' ≼ y) :
    ∃ k : Key, (infoL.map (·.1))[i]? = some k ∧ TypedElCls env U Δ (TyCls env U Δ A₀) k.2.1 ∧
      k.2.1 vx ∧ ∀ o, listSet L o → ∃ o' ∈ k.2.2, o' ≼ o := by
  have hil : i < recArgs.length := (List.getElem?_eq_some_iff.1 ha).1
  have hlen := List.Forall₂.length_eq hinfoL
  have hi' : i < infoL.length := by omega
  have hKl := List.Forall₂.length_eq hKsi
  have ha' : recArgs[i] = a := (List.getElem?_eq_some_iff.1 ha).2
  obtain ⟨_, hkd⟩ := List.forall₂_getElem_exists hinfoL i hi'
  obtain ⟨_, hks⟩ := List.forall₂_getElem_exists hKsi i (by omega)
  rw [ha'] at hkd
  obtain ⟨h1, -, h3, -, hsd, -⟩ := hkd
  obtain ⟨B, hB⟩ := PT i hi'
  have eT := hTy _ _ hB
  have haσ : env.HasType U Δ (a.subst σ) ((infoL[i]).2.subst σ) :=
    hsd.1.defeq.hasType.1.substDF henv W.wf hΔ W
  have eK : (infoL[i]).1.1 = TyCls env U Δ A₀ := by rw [h3, eT]
  refine ⟨(infoL[i]).1, by simp [hi'], ?_, ?_, ?_⟩
  · rw [h1, eK, eT]; exact .of_hasType haσ
  · rw [h1, eK]
    obtain ⟨X, hX, hd⟩ := hdef
    exact .of_link ⟨X, hX, hd⟩
  · intro o ho
    obtain ⟨y', hy', l⟩ := hL o ho
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hy'
    exact ⟨y', hks y' hy', l⟩

/-- **The constructor binding of an instance** (right to left): the constructor class of a
field argument of the major binds a variable whose type class is the domain class of the
constructor spine there (`hTy`). -/
theorem bind_field_inst {Γ : List VExpr} {c : Name} {lsc : List VLevel} {margs : List VExpr}
    {σ : VExpr.Subst} {S : ObSets} (W : Ctx.SubstEq env U Δ σ σ Γ)
    {cinfo : List (Key × VExpr)} (hcinfo : List.Forall₂ (KeyData env U Δ Γ σ S) cinfo margs)
    (PT : ∀ i (hi : i < cinfo.length), ∃ B,
      HTS env U Δ Γ (.mkApps (.const c lsc) (margs.take i)) (.forallE (cinfo[i]'hi).2 B))
    {Ks : List (List Ob)} (hcKs : List.Forall₂ (fun K (ka : Key × VExpr) => ∀ y ∈ K, y ∈ ka.1.2.2)
      Ks cinfo)
    {q : Nat} {ℓs : List (List Nat → Nat)} {A₀ : VExpr} (hq : q < margs.length)
    (hTy : ∀ Aq Bq, HTS env U Δ Γ (.mkApps (.const c lsc) (margs.take q)) (.forallE Aq Bq) →
      TyCls env U Δ A₀ = TyCls env U Δ (Aq.subst σ)) :
    ∃ cl, .ctorArg q cl ∈ ctorObs c ℓs (cinfo.map (·.1)) ∧
      TypedElCls env U Δ (TyCls env U Δ A₀) cl ∧ cl ((margs[q]).subst σ) ∧
      ∀ k ∈ (Ks[q]?).getD [], .ctorArgOb q ((cinfo.map (·.1)).take q) k ∈
        ctorObs c ℓs (cinfo.map (·.1)) := by
  have hlen := List.Forall₂.length_eq hcinfo
  have hq' : q < cinfo.length := by omega
  have hKl := List.Forall₂.length_eq hcKs
  obtain ⟨_, hkd⟩ := List.forall₂_getElem_exists hcinfo q hq'
  obtain ⟨_, hks⟩ := List.forall₂_getElem_exists hcKs q (by omega)
  obtain ⟨h1, -, h3, -, hsd, -⟩ := hkd
  obtain ⟨B, hB⟩ := PT q hq'
  have eT := hTy _ _ hB
  have haσ : env.HasType U Δ ((margs[q]).subst σ) ((cinfo[q]).2.subst σ) :=
    hsd.1.defeq.hasType.1.substDF henv W.wf hΔ W
  have hq'' : q < (cinfo.map (·.1)).length := by simpa using hq'
  refine ⟨(cinfo[q]).1.2.1, ?_, ?_, ?_, fun k hk => ?_⟩
  · have := mem_ctorObs_arg (c := c) (ℓs := ℓs) hq''; simpa using this
  · rw [h1, h3, ← eT]
    rw [eT]; exact .of_hasType haσ
  · rw [h1]; exact ElCls.self
  · rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hk
    have := mem_ctorObs_argOb (c := c) (ℓs := ℓs) hq'' (k := k) (by simpa using hks k hk)
    simpa using this


/-- **Right to left** for an instance of an ι rule. -/
theorem iota_rhs_sub_inst {n ctor : Name} {k nind cnp nf : Nat} {rhs : VExpr} {hc : rhs.Closed}
    {doms : List VExpr} {body : VExpr}
    (hp : env.pats (SimplePattern.iota n (k + nind) ctor (cnp + nf)).toPattern
      (SimplePattern.iotaRHS' n ctor k nind cnp nf rhs hc, .true))
    (hr : rhs = .wrapLams doms body)
    {ci : VConstant} {dsH : List VExpr} {RH : VExpr} {I : Name} {lsI : List VLevel}
    {iargs lead ms : List VExpr}
    (hci : env.constants n = some ci)
    (hstat : IotaStatic ci ctor k nind nf doms dsH RH I lsI iargs lead)
    (hcov : ∀ x < doms.length, VExpr.bvar x ∈ lead ∨ x ∈ iotaFs nf)
    (hIrig : env.Rigid I) (hcf : CtorFam env ctor I) (hcis : IsCtor env ctor)
    {m1 lsC : List VLevel} (hms : ms.length = cnp)
    (hfam : MajorFam env U Δ [] I ctor doms lead ms (iotaFs nf) m1 lsI)
    (hC : ∀ keys : List Key, keys.length = lead.length →
      Obs' .id .empty (ci.type.instL m1) (piCodChain keys
        (.piDomOb (.rigid I ((lsI.map (·.inst m1)).map (·.eval)) iargs.length fun _ => 0))) →
      (∀ (p' : Pattern) (r' : p'.RHS × p'.Check), env.pats p' r' → p'.headConst = n →
        ∃ h : p' = (SimplePattern.iota n (k + nind) ctor (cnp + nf)).toPattern,
          h ▸ r' = (SimplePattern.iotaRHS' n ctor k nind cnp nf rhs hc, .true)) ∧
      ∀ x < doms.length, (∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) →
        ∀ v vS, Ctx.SubstEq env U Δ v v ((doms.map (·.instL m1)).reverse ++ []) →
        TV env U Δ ((doms.map (·.instL m1)).reverse ++ []) v vS →
        (∃ P, TyCls env U Δ ((binderTy doms m1 x).subst v) P ∧
          env.HasType U Δ P (.sort .zero)) ∧
        ∀ τ, Obs' v vS (binderTy doms m1 x) τ → ∃ cv', TypedOb env U Δ cv' τ [.sort fun _ => 0])
    (hlsC : List.Forall₂ (· ≈ ·) lsC (lsI.map (·.inst m1)))
    {recArgs ctorArgs argsR : List VExpr}
    (hrA : recArgs.length = k + nind) (hcA : ctorArgs.length = cnp + nf)
    (hargs : argsR = recArgs.take k ++ ctorArgs.drop cnp)
    {Γ : List VExpr} {A : VExpr}
    (ihe : HTS env U Δ Γ (.mkApps (.const n m1) (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs])) A)
    (ihred : SoundAt env U Δ Γ (.mkApps (rhs.instL m1) argsR) (.mkApps (rhs.instL m1) argsR) A)
    (heqI : env.IsDefEq U Γ (.mkApps (.const n m1) (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs]))
      (.mkApps (rhs.instL m1) argsR) A)
    {T : VExpr} (hRH : HTS env U Δ [] (rhs.instL m1) T)
    (hRS : SoundAt env U Δ [] (rhs.instL m1) (rhs.instL m1) T)
    {σ v : VExpr.Subst} {S vS : ObSets}
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S)
    (hv : v = VExpr.argSubst (argsR.map (·.subst σ))) (hvS : vS = argSets env U Δ σ S argsR)
    (Wv : Ctx.SubstEq env U Δ v v (doms.map (·.instL m1)).reverse)
    (tvv : TV env U Δ (doms.map (·.instL m1)).reverse v vS)
    (hlead : ∀ (i x : Nat), lead[i]? = some (VExpr.bvar x) → x < doms.length →
      (∀ j < i, lead[j]? ≠ some (VExpr.bvar x)) → ∃ a : VExpr, recArgs[i]? = some a ∧
        (∃ X, TyCls env U Δ ((binderTy doms m1 x).subst v) X ∧
          env.IsDefEq U Δ (a.subst σ) (v x) X) ∧
        (∀ Aq Bq, HTS env U Δ Γ (.mkApps (.const n m1) (recArgs.take i)) (.forallE Aq Bq) →
          TyCls env U Δ ((binderTy doms m1 x).subst v) = TyCls env U Δ (Aq.subst σ)) ∧
        Ob.Sub (vS x) (Obs' σ S a))
    (hfield : ∀ j < nf, ∀ Aq Bq,
      HTS env U Δ Γ (.mkApps (.const ctor lsC) (ctorArgs.take (cnp + j))) (.forallE Aq Bq) →
      TyCls env U Δ ((binderTy doms m1 (nf - 1 - j)).subst v) = TyCls env U Δ (Aq.subst σ)) :
    Ob.Sub (Obs' σ S (.mkApps (rhs.instL m1) argsR))
      (Obs' σ S (.mkApps (.const n m1) (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs]))) := by
  have hrcl : rhs.ClosedN := hc
  have hleadl : lead.length = k + nind := hstat.lead_length
  have ⟨hdl, eH, hlenH0, hkH0, _⟩ := hstat
  have hlenH : dsH.length = lead.length + 1 := by rw [hleadl]; exact hlenH0
  have hkH : dsH[lead.length]? = some (.mkApps (.const I lsI) iargs) := by rw [hleadl]; exact hkH0
  have hal : argsR.length = doms.length := by subst hargs; simp; omega
  have hkr : k ≤ recArgs.length := by omega
  -- the reduct template
  have eR : rhs.instL m1 = .wrapLams (doms.map (·.instL m1)) (body.instL m1) := by
    rw [hr, VExpr.instL_wrapLams]
  have hbcl : (body.instL m1).ClosedN doms.length := by
    have := (closedN_wrapLams (hr ▸ hrcl : (VExpr.wrapLams doms body).ClosedN 0)).1
    simpa using this.instL
  have hRcl : (VExpr.wrapLams (doms.map (·.instL m1)) (body.instL m1)).ClosedN := by
    rw [← eR]; exact hrcl.instL
  have hal' : argsR.length = (doms.map (·.instL m1)).length := by simp [hal]
  have hRH' := hRH; have hRS' := hRS
  rw [eR] at hRH' hRS'
  have hβ := beta_spine_sub henv hΔ hRcl hRH' hRS' hal' (hv ▸ Wv) (hv ▸ hvS ▸ tvv)
  have hvF : ∀ j x, (iotaFs nf)[j]? = some x → ∃ h : cnp + j < ctorArgs.length,
      v x = (ctorArgs[cnp + j]'h).subst σ ∧ vS x = Obs' σ S (ctorArgs[cnp + j]'h) := by
    intro j x hj
    obtain ⟨hjn, rfl⟩ := iotaFs_getElem? hj
    refine ⟨by omega, ?_, ?_⟩
    · rw [hv]; exact argSubst_field hargs hkr hcA hjn
    · rw [hvS]; exact argSets_field hargs hkr hcA hjn
  intro o ho
  rw [eR] at ho
  obtain ⟨o₁, ho₁, l₁⟩ := hβ.1 o ho
  suffices hgoal : Obs' σ S (.mkApps (.const n m1)
      (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs])) o₁ from ⟨o₁, hgoal, l₁⟩
  have ho₁r : Obs' σ S (.mkApps (rhs.instL m1) argsR) o₁ := by rw [eR]; exact hβ.2 o₁ ho₁
  have hp₀ : Obs' v vS (body.instL m1) o₁ := by
    rw [hv, hvS]; exact (Obs.subst_argSubst (by rw [hal]; exact hbcl)).1 ho₁
  -- the reduct's observation is typed at the class of the redex
  obtain ⟨τs, hτs, hty⟩ := (ihred σ σ S W tv tv).2.2.1 o₁ ho₁r
  rw [← vcls_defeq henv hΔ W heqI] at hty
  -- finite backed observation sets for the template's variables
  obtain ⟨G, hGl, hGS, hG⟩ := Obs.compact_all hbcl (τs := [o₁])
    (fun τ hτ => by rw [List.mem_singleton] at hτ; subst hτ; exact hp₀)
  have hclo : ∀ m (hm : m < doms.length), ∃ K : List Ob, (∀ y ∈ G[m]'(by omega), y ∈ K) ∧
      (∀ y ∈ K, vS m y) ∧ Backed (· ∈ K) := fun m hm =>
    Backed.close (tvv.1 m) (hGS m (by omega))
  classical
  let Lx : Nat → List Ob := fun m => if h : m < doms.length then (hclo m h).choose else []
  have hLx1 : ∀ m < doms.length, ∀ y ∈ Lx m, vS m y := fun m hm y hy => by
    simp only [Lx, hm, dite_true] at hy; exact (hclo m hm).choose_spec.2.1 y hy
  have hLx2 : ∀ m < doms.length, Backed (· ∈ Lx m) := fun m hm => by
    simp only [Lx, hm, dite_true]; exact (hclo m hm).choose_spec.2.2
  let S₀ : ObSets := fun m => if m < doms.length then listSet (Lx m) else vS m
  have hp₁ : Obs' v S₀ (body.instL m1) o₁ := hG S₀ (fun m hm y hy => by
    have hm' : m < doms.length := by omega
    simp only [S₀, hm', if_true, listSet, Lx, dite_true]
    exact (hclo m hm').choose_spec.1 y hy) o₁ (List.mem_singleton_self _)
  have hS₀b : ∀ x, Backed (S₀ x) := fun x => by
    by_cases hx : x < doms.length
    · simp only [S₀, hx, if_true]; exact hLx2 x hx
    · simp only [S₀, hx, if_false]; exact tvv.1 x
  -- demands on the leading arguments
  have hdem : ∀ i (hi : i < recArgs.length), ∃ K : List Ob,
      (∀ y ∈ K, Obs' σ S recArgs[i] y) ∧
      ∀ x, lead[i]? = some (VExpr.bvar x) → x < doms.length →
        (∀ j < i, lead[j]? ≠ some (VExpr.bvar x)) → ∀ y ∈ Lx x, ∃ y' ∈ K, y' ≼ y := by
    intro i hi
    by_cases hb : ∃ x, lead[i]? = some (VExpr.bvar x) ∧ x < doms.length ∧
        ∀ j < i, lead[j]? ≠ some (VExpr.bvar x)
    · obtain ⟨x, hx1, hx2, hx3⟩ := hb
      obtain ⟨a, ha, -, -, hsub⟩ := hlead i x hx1 hx2 hx3
      have ha' : recArgs[i] = a := (List.getElem?_eq_some_iff.1 ha).2
      obtain ⟨K, hK1, hK2⟩ := exists_list_cover (L := Lx x) (P := Obs' σ S recArgs[i])
        (R := fun y' y => y' ≼ y) fun y hy => by
          obtain ⟨y', hy', l⟩ := hsub y (hLx1 x hx2 y hy)
          exact ⟨y', by rw [ha']; exact hy', l⟩
      refine ⟨K, hK1, fun x' hx1' _ _ y hy => ?_⟩
      rw [hx1] at hx1'
      cases hx1'
      exact hK2 y hy
    · exact ⟨[], nofun, fun x h1 h2 h3 => absurd ⟨x, h1, h2, h3⟩ hb⟩
  obtain ⟨Ks0, hKs0l, hKs0⟩ := exists_lists_of_getElem (args := recArgs)
    (P := fun i a K => (∀ y ∈ K, Obs' σ S a y) ∧
      ∀ x, lead[i]? = some (VExpr.bvar x) → x < doms.length →
        (∀ j < i, lead[j]? ≠ some (VExpr.bvar x)) → ∀ y ∈ Lx x, ∃ y' ∈ K, y' ≼ y) hdem
  have hKs0f : List.Forall₂ (fun K a => ∀ y ∈ K, Obs' σ S a y) Ks0 recArgs :=
    List.forall₂_of_getElem hKs0l fun i hi hi' => (hKs0 i hi').1
  have hKs0c : ∀ (i x : Nat), lead[i]? = some (VExpr.bvar x) → x < doms.length →
      (∀ j < i, lead[j]? ≠ some (VExpr.bvar x)) →
      ∀ y ∈ Lx x, ∃ y' ∈ (Ks0[i]?).getD [], y' ≼ y := by
    intro i x h1 h2 h3 y hy
    have hi : i < recArgs.length := by
      have := (List.getElem?_eq_some_iff.1 h1).1; omega
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact (hKs0 i hi).2 x h1 h2 h3 y hy
  -- facts about the leading arguments
  have firstOcc : ∀ x : Nat, (∃ i : Nat, lead[i]? = some (VExpr.bvar x)) →
      ∃ i : Nat, lead[i]? = some (VExpr.bvar x) ∧ ∀ j < i, lead[j]? ≠ some (VExpr.bvar x) := by
    intro x ⟨i₀, hi₀⟩
    have hmem : VExpr.bvar x ∈ lead := List.mem_of_getElem? hi₀
    obtain ⟨i, hi⟩ : ∃ i, lead.idxOf? (VExpr.bvar x) = some i := by
      cases h : lead.idxOf? (VExpr.bvar x) with
      | none => exact absurd hmem (by simpa using h)
      | some i => exact ⟨i, rfl⟩
    obtain ⟨hil, h1, h2⟩ := List.idxOf?_eq_some_iff.1 hi
    refine ⟨i, List.getElem?_eq_some_iff.2 ⟨hil, h1⟩, fun j hj e => ?_⟩
    obtain ⟨hjl, e⟩ := List.getElem?_eq_some_iff.1 e
    exact h2 j hj e
  have fieldIdx : ∀ x : Nat, x ∈ iotaFs nf → ∃ j : Nat, (iotaFs nf)[j]? = some x := fun x hx => by
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hx
    exact ⟨j, List.getElem?_eq_some_iff.2 ⟨hj, e⟩⟩
  have Wv' : Ctx.SubstEq env U Δ v v ((doms.map (·.instL m1)).reverse ++ []) := by simpa using Wv
  have tvv' : TV env U Δ ((doms.map (·.instL m1)).reverse ++ []) v vS := by simpa using tvv
  -- the lead binding, for keys of the leading arguments
  have leadBind : ∀ (infoL : List (Key × VExpr)), List.Forall₂ (KeyData env U Δ Γ σ S) infoL recArgs →
      (∀ i (hi : i < infoL.length), ∃ B,
        HTS env U Δ Γ (.mkApps (.const n m1) (recArgs.take i)) (.forallE (infoL[i]'hi).2 B)) →
      List.Forall₂ (fun K (ka : Key × VExpr) => ∀ y ∈ K, y ∈ ka.1.2.2) Ks0 infoL →
      ∀ (x i : Nat), x < doms.length → lead[i]? = some (VExpr.bvar x) →
        (∀ j < i, lead[j]? ≠ some (VExpr.bvar x)) →
        ∃ k : Key, (infoL.map (·.1))[i]? = some k ∧
          TypedElCls env U Δ (TyCls env U Δ ((binderTy doms m1 x).subst v)) k.2.1 ∧
          k.2.1 (v x) ∧ ∀ o, S₀ x o → ∃ o' ∈ k.2.2, o' ≼ o := by
    intro infoL hinfoL PTL hKsiL x i hx hi hfirst
    obtain ⟨a, ha, hdef, hTy, -⟩ := hlead i x hi hx hfirst
    obtain ⟨kk, h1, h2, h3, h4⟩ := bind_lead_inst henv hΔ W hinfoL PTL hKsiL ha hTy hdef
      (L := Lx x) (hKs0c i x hi hx hfirst)
    refine ⟨kk, h1, h2, h3, fun o ho => h4 o ?_⟩
    simpa [S₀, hx] using ho
  -- the head spine of the redex, first pass
  have hKs : List.Forall₂ (fun K a => ∀ y ∈ K, Obs' σ S a y) (Ks0 ++ [[]])
      (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs]) :=
    forall₂_append_single hKs0f nofun
  obtain ⟨Th, info, hTh, hThcl, ⟨uH, hHT, -⟩, hinfo, hKsi, P1, -, dP2, PT⟩ :=
    ihe.spineH' henv hΔ rfl ⟨n, m1, rfl⟩ W tv _ hKs τs hτs
  obtain ⟨_, _, ci', e0, hci', hlw, rfl⟩ := hTh
  cases e0
  cases hci.symm.trans hci'
  have W0 : Ctx.SubstEq env U Δ .id .id [] := .nil
  have tv0 : TV env U Δ [] .id .empty := TV.empty
  obtain ⟨infoL, kaM, rfl, hinfoL, hkaM⟩ := List.forall₂_snoc_right hinfo
  obtain ⟨KsL, KsM, eKs, hKsiL, -⟩ := List.forall₂_snoc_right hKsi
  obtain ⟨rfl, -⟩ := List.append_inj' eKs rfl
  obtain ⟨τ₀, hτ₀, hty₀⟩ := P1 o₁ hty
  have hlenL : infoL.length = lead.length := by
    have := List.Forall₂.length_eq hinfoL; omega
  have prefixTy : ∀ (infoL' : List (Key × VExpr)) (kaM' : Key × VExpr),
      List.Forall₂ (KeyData env U Δ Γ σ S) infoL' recArgs →
      (∀ i (hi : i < (infoL' ++ [kaM']).length), ∃ B, HTS env U Δ Γ (.mkApps (.const n m1)
        ((recArgs ++ [VExpr.mkApps (.const ctor lsC) ctorArgs]).take i))
          (.forallE ((infoL' ++ [kaM'])[i]'hi).2 B)) →
      ∀ i (hi : i < infoL'.length), ∃ B,
        HTS env U Δ Γ (.mkApps (.const n m1) (recArgs.take i)) (.forallE (infoL'[i]'hi).2 B) := by
    intro infoL' kaM' h1 h2 i hi
    have hl := List.Forall₂.length_eq h1
    obtain ⟨B, hB⟩ := h2 i (by simp; omega)
    refine ⟨B, ?_⟩
    rw [List.getElem_append_left hi, List.take_append_of_le_length (by omega)] at hB
    exact hB
  obtain ⟨u, hind⟩ := major_indicator_gen (dsH := dsH) (RH := RH) henv hΔ hThcl hHT W0 tv0
    (by rw [eH, VExpr.instL_wrapForalls]) hlenH hkH hIrig
    (keys := (infoL ++ [kaM]).map (·.1)) (by simp [hlenL]) hτ₀ hty₀
  rw [show ((infoL ++ [kaM]).map (·.1)).take lead.length = infoL.map (·.1) by
    simp [List.map_append, hlenL]] at hind
  obtain ⟨xr, hxr, lr⟩ := dP2 infoL kaM [] rfl _ hind
  rw [lr.rigid_inv] at hxr
  -- the common conclusion from a rule clause instance
  have finish : ∀ (infoL' : List (Key × VExpr)) (kaM' : Key × VExpr) (S' : ObSets) (mC : Bool)
      (τ₀' : List Ob),
      List.Forall₂ (KeyData env U Δ Γ σ S) (infoL' ++ [kaM'])
        (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs]) →
      (∀ τ ∈ τ₀', Obs' .id .empty (ci.type.instL m1) τ) →
      TypedOb env U Δ (ElCls env U Δ (TyCls env U Δ (ci.type.instL m1)) (.const n m1))
        (wrap ((infoL' ++ [kaM']).map (·.1)) o₁) τ₀' →
      (mC = true → ∀ (p' : Pattern) (r' : p'.RHS × p'.Check), env.pats p' r' →
        p'.headConst = n →
        ∃ h : p' = (SimplePattern.iota n (k + nind) ctor (cnp + nf)).toPattern,
          h ▸ r' = (SimplePattern.iotaRHS' n ctor k nind cnp nf rhs hc, .true)) →
      (mC = true → Obs' .id .empty (ci.type.instL m1) (piCodChain (infoL'.map (·.1))
        (.piDomOb (.rigid I ((lsI.map (·.inst m1)).map (·.eval)) iargs.length fun _ => 0)))) →
      (mC = false → (∃ ℓs, .ctorHead ctor ℓs (cnp + nf) ∈ kaM'.1.2.2) ∨
        EtaHead env I ctor ci.type (infoL'.map (·.1)).length) →
      RuleBind env U Δ doms m1 lead cnp (iotaFs nf) mC I ctor lsI (infoL'.map (·.1)) kaM'.1.2.1
        kaM'.1.2.2 v S' →
      (∀ x o, S₀ x o → S' x o) →
      Obs' σ S (.mkApps (.const n m1) (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs])) o₁ := by
    intro infoL' kaM' S' mC τ₀' hinfo' hτ₀' hty₀' hsingle hmobs hhdC hbind hS'
    have hlen' : infoL'.length = lead.length := by
      have := List.Forall₂.length_eq hinfo'; simp at this; omega
    have hc' := Obs.pat (σ := σ) (S := S) (Dm := kaM'.1.1) (cm := kaM'.1.2.1) (Km := kaM'.1.2.2)
      (lkeys := infoL'.map (·.1)) hp hr hstat hci hτ₀' (by simpa using hty₀')
      (by simp [hlen', hleadl]) hsingle hmobs hhdC hbind
      (by simpa using KeyData.forall₂_backed hinfo') (hp₁.mono hS')
    exact obs_mkApps_of_wrap (KeyData.forall₂_keys hinfo') (by simpa using hc')
  -- the proof binding of a field not bound by the leading arguments
  have proofBind : ∀ x, x < doms.length → (∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) →
      (∀ τ, Obs' v vS (binderTy doms m1 x) τ → ∃ cv', TypedOb env U Δ cv' τ [.sort fun _ => 0]) →
      S₀ x = fun _ => False := by
    intro x hx hnb hprop
    have hL := lookup_binderTy (Γ := []) (ls := m1) hx
    funext kk; apply propext; constructor
    · intro hk
      have hk' : vS x kk := by
        simp only [S₀, hx, if_true, listSet] at hk; exact hLx1 x hx kk hk
      obtain ⟨τs', hτs', htk⟩ := tvv'.2 x _ hL kk hk'
      exact htk.not_prop fun τ hτ => hprop τ (hτs' τ hτ)
    · nofun
  have leadOr : ∀ x, x < doms.length → (∃ i : Nat, lead[i]? = some (VExpr.bvar x)) ∨
      ((∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) ∧ x ∈ iotaFs nf) := by
    intro x hx
    by_cases hb : ∃ i : Nat, lead[i]? = some (VExpr.bvar x)
    · exact .inl hb
    · refine .inr ⟨fun i h => hb ⟨i, h⟩, (hcov x hx).resolve_left fun h => ?_⟩
      obtain ⟨i, hi, e⟩ := List.getElem_of_mem h
      exact hb ⟨i, List.getElem?_eq_some_iff.2 ⟨hi, e⟩⟩
  by_cases hm : u.eval = fun _ => 0
  · -- mode C: the major is ignored, its only own fields are proofs
    rw [hm] at hind
    obtain ⟨hsingle, hpf⟩ := hC _ (by simp [hlenL]) hind
    refine finish infoL kaM S₀ true τ₀ (forall₂_append_single hinfoL hkaM) hτ₀ hty₀
      (fun _ => hsingle) (fun _ => hind) nofun ⟨hS₀b, ?_⟩ fun _ _ h => h
    intro x hx
    rcases leadOr x hx with hb | ⟨hnb, hxf⟩
    · obtain ⟨i, hi, hfirst⟩ := firstOcc x hb
      obtain ⟨kk, hk1, hk2, hk3, hk4⟩ := leadBind infoL hinfoL (prefixTy infoL kaM hinfoL PT)
        hKsiL x i hx hi hfirst
      exact .inl ⟨i, kk, hi, hfirst, hk1, hk2, hk3, hk4⟩
    · obtain ⟨j, hj⟩ := fieldIdx x hxf
      obtain ⟨hP, hprop⟩ := hpf x hx hnb v vS Wv' tvv'
      have hL := lookup_binderTy (Γ := []) (ls := m1) hx
      exact .inr ⟨hnb, j, hj, .inr (.inl ⟨⟨_, .self, (Wv'.lookup hL).hasType.1⟩, hP,
        proofBind x hx hnb hprop⟩)⟩
  · have hS₀Lx : ∀ x, x < doms.length → ∀ o, S₀ x o → o ∈ Lx x := fun x hx o h => by
      simpa [S₀, hx, listSet] using h
    have hfsj : ∀ x, x ∈ iotaFs nf → (iotaFs nf)[(iotaFs nf).idxOf x]? = some x := fun x hx =>
      List.getElem?_eq_some_iff.2 ⟨List.idxOf_lt_length_of_mem hx, List.getElem_idxOf _⟩
    rcases hfam with ⟨hIP, hcnp⟩ | ⟨info, hpI, hPV, hcn, hfull, hnpj, hnzp⟩
    · -- mode AB: the major's constructor observations
      obtain ⟨-, -, -, hHTSm, -, -⟩ := hkaM
      have hcdem : ∀ q (hq : q < ctorArgs.length), ∃ K : List Ob,
          (∀ y ∈ K, Obs' σ S ctorArgs[q] y) ∧ ∀ j x, q = cnp + j → (iotaFs nf)[j]? = some x →
            x < doms.length → ∀ y ∈ Lx x, y ∈ K := by
        intro q hq
        by_cases hqc : cnp ≤ q
        · have hjn : q - cnp < nf := by omega
          have hj : (iotaFs nf)[q - cnp]? = some (nf - 1 - (q - cnp)) := by
            simp [iotaFs, hjn] <;> omega
          by_cases hxd : nf - 1 - (q - cnp) < doms.length
          · refine ⟨Lx (nf - 1 - (q - cnp)), fun y hy => ?_, fun j x hqj hj' _ y hy => ?_⟩
            · obtain ⟨hil, -, hvS'⟩ := hvF _ _ hj
              have := hLx1 _ hxd y hy
              rw [hvS'] at this
              have e : cnp + (q - cnp) = q := by omega
              simpa [e] using this
            · subst hqj
              simp only [Nat.add_sub_cancel_left] at hj hy ⊢
              rw [hj] at hj'; cases hj'
              exact hy
          · exact ⟨[], nofun, fun j x hqj hj' hx _ _ => by
              subst hqj
              rw [show cnp + j - cnp = j by omega] at hj
              rw [hj] at hj'; cases hj'
              exact absurd hx (by rwa [show cnp + j - cnp = j by omega] at hxd)⟩
        · exact ⟨[], nofun, fun j x hqj _ _ _ _ => by omega⟩
      obtain ⟨Kc, hKcl, hKc⟩ := exists_lists_of_getElem (args := ctorArgs)
        (P := fun q a K => (∀ y ∈ K, Obs' σ S a y) ∧ ∀ j x, q = cnp + j →
          (iotaFs nf)[j]? = some x → x < doms.length → ∀ y ∈ Lx x, y ∈ K) hcdem
      have hKcf : List.Forall₂ (fun K a => ∀ y ∈ K, Obs' σ S a y) Kc ctorArgs :=
        List.forall₂_of_getElem hKcl fun i hi hi' => (hKc i hi').1
      obtain ⟨Thc, cinfo, hThc, -, -, hcinfo, hcKs, cP1, -, -, PTc⟩ :=
        hHTSm.spineH' henv hΔ rfl ⟨ctor, lsC, rfl⟩ W tv _ hKcf
          [.rigid I ((lsI.map (·.inst m1)).map (·.eval)) iargs.length u.eval]
          (fun τ hτ => by rw [List.mem_singleton] at hτ; subst hτ; exact hxr)
      obtain ⟨_, _, cc, ec, hcc, -, rfl⟩ := hThc
      cases ec
      have hCT : CtorTyped env ctor
          [.rigid I ((lsI.map (·.inst m1)).map (·.eval)) iargs.length u.eval] :=
        ⟨I, _, _, _, List.mem_singleton_self _, hcf, hm, hIP⟩
      have hcobs : ∀ r ∈ ctorObs ctor (lsC.map (·.eval)) (cinfo.map (·.1)),
          Obs' σ S (.mkApps (.const ctor lsC) ctorArgs) r := by
        intro r hr
        have hend := ctorObs_end hr
        have hrty : TypedOb env U Δ (vcls env U Δ σ (.mkApps (.const ctor lsC) ctorArgs) kaM.2) r
            [.rigid I ((lsI.map (·.inst m1)).map (·.eval)) iargs.length u.eval] := by
          rcases hend with rfl | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩
          · exact .ctorHead hCT
          · exact .ctorArg hCT
          · exact .ctorArgOb hCT
        obtain ⟨τ₀c, h1, h2⟩ := cP1 r hrty
        exact obs_mkApps_of_wrap (KeyData.forall₂_keys hcinfo)
          (.ctor hcis hcnp hcc h1 h2 hend (KeyData.forall₂_backed hcinfo))
      have hKs2 := forall₂_append_single hKs0f hcobs
      obtain ⟨Th2, info2, hTh2, -, -, hinfo2, hKsi2, P12, -, -, PT2⟩ :=
        ihe.spineH' henv hΔ rfl ⟨n, m1, rfl⟩ W tv _ hKs2 τs hτs
      obtain ⟨_, _, ci2, e2, hci2, -, rfl⟩ := hTh2
      cases e2
      cases hci.symm.trans hci2
      have hbk2 := KeyData.forall₂_backed hinfo2
      obtain ⟨infoL2, kaM2, rfl, hinfoL2, -⟩ := List.forall₂_snoc_right hinfo2
      obtain ⟨KsL2, KsM2, eKs2, hKsiL2, hKsM2⟩ := List.forall₂_snoc_right hKsi2
      obtain ⟨rfl, e2⟩ := List.append_inj' eKs2 rfl
      cases e2
      obtain ⟨τ₀2, hτ₀2, hty₀2⟩ := P12 o₁ hty
      have hclen : (cinfo.map (·.1)).length = cnp + nf := by
        have := List.Forall₂.length_eq hcinfo; simp at this ⊢; omega
      let S' : ObSets := fun x =>
        if x < doms.length ∧ (∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) ∧ x ∈ iotaFs nf then
          fun kk => ∃ pre, .ctorArgOb (cnp + (iotaFs nf).idxOf x) pre kk ∈ kaM2.1.2.2
        else S₀ x
      have hbM : Backed (fun o => o ∈ kaM2.1.2.2) :=
        hbk2 _ (List.mem_map_of_mem (List.mem_append_right _ (List.mem_singleton_self _)))
      refine finish infoL2 kaM2 S' false τ₀2 hinfo2 hτ₀2 hty₀2 nofun nofun
        (fun _ => .inl ⟨_, hKsM2 _ (hclen ▸ mem_ctorObs_head)⟩) ⟨fun x => ?_, ?_⟩ ?_
      · simp only [S']
        split
        · intro kk ⟨pre, hk⟩ w hw
          exact ⟨pre, hbM _ hk _ (by simp only [Ob.wit]; exact List.mem_map_of_mem hw)⟩
        · exact hS₀b x
      · intro x hx
        rcases leadOr x hx with hb | ⟨hnb, hxf⟩
        · obtain ⟨i, hi, hfirst⟩ := firstOcc x hb
          obtain ⟨kk, hk1, hk2, hk3, hk4⟩ := leadBind infoL2 hinfoL2
            (prefixTy infoL2 kaM2 hinfoL2 PT2) hKsiL2 x i hx hi hfirst
          have : S' x = S₀ x := by
            simp only [S']; rw [if_neg]; rintro ⟨-, h, -⟩; exact h i hi
          exact .inl ⟨i, kk, hi, hfirst, hk1, hk2, hk3, by rw [this]; exact hk4⟩
        · obtain ⟨hjl, -⟩ := iotaFs_getElem? (hfsj x hxf)
          obtain ⟨hil, hvx, -⟩ := hvF _ x (hfsj x hxf)
          obtain ⟨cl, hcl, hcty, hcm, -⟩ := bind_field_inst (c := ctor) (lsc := lsC)
            (ℓs := lsC.map (·.eval)) henv hΔ W hcinfo PTc hcKs (q := cnp + (iotaFs nf).idxOf x) hil
            (by
              have := hfield _ hjl
              rwa [show nf - 1 - (iotaFs nf).idxOf x = x by
                obtain ⟨-, e⟩ := iotaFs_getElem? (hfsj x hxf); omega] at this)
          refine .inr ⟨hnb, (iotaFs nf).idxOf x, hfsj x hxf, .inl ⟨rfl, cl, hKsM2 _ hcl, hcty,
            by rw [hvx]; exact hcm, ?_⟩⟩
          simp only [S']; rw [if_pos ⟨hx, hnb, hxf⟩]
      · intro x o ho
        simp only [S']
        split
        · rename_i hMF
          obtain ⟨hx, hnb, hxf⟩ := hMF
          obtain ⟨hjl, -⟩ := iotaFs_getElem? (hfsj x hxf)
          obtain ⟨hil, -, -⟩ := hvF _ x (hfsj x hxf)
          obtain ⟨-, -, -, -, hall⟩ := bind_field_inst (c := ctor) (lsc := lsC)
            (ℓs := lsC.map (·.eval)) henv hΔ W hcinfo PTc hcKs (q := cnp + (iotaFs nf).idxOf x) hil
            (by
              have := hfield _ hjl
              rwa [show nf - 1 - (iotaFs nf).idxOf x = x by
                obtain ⟨-, e⟩ := iotaFs_getElem? (hfsj x hxf); omega] at this)
          have hoK : o ∈ (Kc[cnp + (iotaFs nf).idxOf x]?).getD [] := by
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            exact (hKc _ hil).2 _ x rfl (hfsj x hxf) hx o (hS₀Lx x hx o ho)
          exact ⟨_, hKsM2 _ (hall o hoK)⟩
        · exact ho
    · -- a projection-registered family: the eta binding (never zero) or the proof binding
      have hEH : ∀ kk, kk = lead.length → EtaHead env I ctor ci.type kk := fun kk hk =>
        ⟨info, dsH, RH, lsI, iargs, hpI, hcn, eH, hk ▸ hlenH, hk ▸ hkH⟩
      rcases hnzp with hnz | hpf
      · -- the eta binding: fields read from the field observations of the major key
        obtain ⟨-, -, -, hHTSm, hSDm, -⟩ := hkaM
        subst hcn
        obtain ⟨hlsW, hlsl⟩ := ctor_spine_levels henv hΔ hpI W hSDm
        have hnz' : (info.resultLevel.inst lsC).IsNeverZero :=
          hnz.of_equiv (VLevel.inst_congr (VLevel.equiv_def.2 fun _ => rfl)
            (forall₂_equiv_symm hlsC))
        have hfull' : cnp + nf = info.nparams + info.numFields := by
          rw [← hms]; simpa using hfull
        -- the field observations of the major
        have hfo : ∀ j x kk, (iotaFs nf)[j]? = some x → info.nparams ≤ cnp + j →
            x < doms.length → kk ∈ Lx x → ∃ L, Obs' σ S (.mkApps (.const info.ctorName lsC)
              ctorArgs) (.fieldOb I (cnp + j - info.nparams) L kk) := by
          intro j x kk hj hnp hxd hk
          obtain ⟨hil, -, hvS'⟩ := hvF j x hj
          have H' := hHTSm
          rw [← List.take_append_drop info.nparams ctorArgs] at H'
          have hjd : cnp + j - info.nparams < (ctorArgs.drop info.nparams).length := by
            simp; omega
          have hget : (ctorArgs.drop info.nparams)[cnp + j - info.nparams]'hjd =
              ctorArgs[cnp + j] := by
            rw [List.getElem_drop]; congr 1; omega
          have hkx : Obs' σ S (ctorArgs.drop info.nparams)[cnp + j - info.nparams] kk := by
            rw [hget, ← hvS']; exact hLx1 x hxd kk hk
          have := ctor_field_obs henv hΔ hpI hPV hlsW hlsl hnz' W tv H'
            (by simp; omega) (by simp; omega) hjd hkx
          rwa [List.take_append_drop] at this
        obtain ⟨Kd, hKd, hKdc⟩ := exists_list_witness
          (Q := Obs' σ S (.mkApps (.const info.ctorName lsC) ctorArgs))
          (P := fun (a : Nat × Ob) o => ∃ L, o = .fieldOb I (cnp + a.1 - info.nparams) L a.2)
          (((List.range nf).filter fun j => decide (info.nparams ≤ cnp + j ∧
              (iotaFs nf).getD j 0 < doms.length)).flatMap fun j =>
                (Lx ((iotaFs nf).getD j 0)).map fun kk => (j, kk))
          (by
            intro a ha
            simp only [List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq,
              List.mem_map] at ha
            obtain ⟨j, ⟨hjl, hnp, hxd⟩, kk, hk, rfl⟩ := ha
            have hjl' : j < (iotaFs nf).length := by simp; omega
            have hj : (iotaFs nf)[j]? = some ((iotaFs nf).getD j 0) := by
              rw [← List.getElem_eq_getD 0 (h := hjl'), List.getElem?_eq_getElem hjl']
            obtain ⟨L, hL⟩ := hfo j _ kk hj hnp hxd hk
            exact ⟨_, hL, L, rfl⟩)
        have hKdx : ∀ j x kk, (iotaFs nf)[j]? = some x → info.nparams ≤ cnp + j →
            x < doms.length → kk ∈ Lx x →
            ∃ L, .fieldOb I (cnp + j - info.nparams) L kk ∈ Kd := by
          intro j x kk hj hnp hxd hk
          have hjl : j < (iotaFs nf).length := (List.getElem?_eq_some_iff.1 hj).1
          have hfx : (iotaFs nf).getD j 0 = x := by
            rw [← List.getElem_eq_getD 0 (h := hjl)]; exact (List.getElem?_eq_some_iff.1 hj).2
          obtain ⟨o', ho', L, rfl⟩ := hKdc (j, kk) (by
            simp only [List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq,
              List.mem_map]
            exact ⟨j, ⟨by simpa using hjl, hnp, by rw [hfx]; exact hxd⟩, kk,
              by rw [hfx]; exact hk, rfl⟩)
          exact ⟨L, ho'⟩
        -- the second pass of the head spine, with the field observations of the major
        have hKs2 := forall₂_append_single hKs0f hKd
        obtain ⟨Th2, info2, hTh2, -, -, hinfo2, hKsi2, P12, -, -, PT2⟩ :=
          ihe.spineH' henv hΔ rfl ⟨n, m1, rfl⟩ W tv _ hKs2 τs hτs
        obtain ⟨_, _, ci2, e2, hci2, -, rfl⟩ := hTh2
        cases e2
        cases hci.symm.trans hci2
        have hbk2 := KeyData.forall₂_backed hinfo2
        obtain ⟨infoL2, kaM2, rfl, hinfoL2, hkaM2⟩ := List.forall₂_snoc_right hinfo2
        obtain ⟨KsL2, KsM2, eKs2, hKsiL2, hKsM2⟩ := List.forall₂_snoc_right hKsi2
        obtain ⟨rfl, e2⟩ := List.append_inj' eKs2 rfl
        cases e2
        obtain ⟨τ₀2, hτ₀2, hty₀2⟩ := P12 o₁ hty
        obtain ⟨hcm2, -, hDm2, hHTS2, hSD2, -⟩ := hkaM2
        have hlenL2 : infoL2.length = lead.length := by
          have := List.Forall₂.length_eq hinfoL2; omega
        let S' : ObSets := fun x =>
          if x < doms.length ∧ (∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) ∧ x ∈ iotaFs nf then
            fun kk => ∃ L, .fieldOb I (cnp + (iotaFs nf).idxOf x - info.nparams) L kk ∈ kaM2.1.2.2
          else S₀ x
        have hbM : Backed (fun o => o ∈ kaM2.1.2.2) :=
          hbk2 _ (List.mem_map_of_mem (List.mem_append_right _ (List.mem_singleton_self _)))
        refine finish infoL2 kaM2 S' false τ₀2 hinfo2 hτ₀2 hty₀2 nofun nofun
          (fun _ => .inr (hEH _ (by simp [hlenL2]))) ⟨fun x => ?_, ?_⟩ ?_
        · simp only [S']
          split
          · intro kk ⟨L, hk⟩ w hw
            exact ⟨L, hbM _ hk _ (Ob.mem_wit_fieldOb.2 (.inr ⟨w, hw, rfl⟩))⟩
          · exact hS₀b x
        · intro x hx
          rcases leadOr x hx with hb | ⟨hnb, hxf⟩
          · obtain ⟨i, hi, hfirst⟩ := firstOcc x hb
            obtain ⟨kk, hk1, hk2, hk3, hk4⟩ := leadBind infoL2 hinfoL2
              (prefixTy infoL2 kaM2 hinfoL2 PT2) hKsiL2 x i hx hi hfirst
            have : S' x = S₀ x := by
              simp only [S']; rw [if_neg]; rintro ⟨-, h, -⟩; exact h i hi
            exact .inl ⟨i, kk, hi, hfirst, hk1, hk2, hk3, by rw [this]; exact hk4⟩
          · obtain ⟨hjl, ex⟩ := iotaFs_getElem? (hfsj x hxf)
            obtain ⟨hil, hvx, -⟩ := hvF _ x (hfsj x hxf)
            have hnp := hnpj x _ (hfsj x hxf) hnb
            rw [hms] at hnp
            obtain ⟨E, hvx'⟩ := eta_field_cls_gen henv hΔ hpI hPV W tv hHTS2 hSD2
              (by rw [hcA]; rw [hms] at hfull; simpa using hfull) hnz' (q := cnp + (iotaFs nf).idxOf x)
              hil hnp (A₀ := (binderTy doms m1 x).subst v) (by
                have := hfield _ hjl
                rwa [show nf - 1 - (iotaFs nf).idxOf x = x by omega] at this)
            have ecm : kaM2.1.2.1 = ElCls env U Δ (TyCls env U Δ (kaM2.2.subst σ))
                ((VExpr.mkApps (.const info.ctorName lsC) ctorArgs).subst σ) := by
              rw [hcm2, hDm2]
            refine .inr ⟨hnb, (iotaFs nf).idxOf x, hfsj x hxf,
              .inr (.inr ⟨rfl, info, hpI, rfl, hnp, hnz, ?_, ?_, ?_⟩)⟩
            · rw [ecm, E]; exact TypedElCls.of_hasType hvx'
            · rw [ecm, E, hvx]; exact ElCls.self
            · simp only [S']; rw [if_pos ⟨hx, hnb, hxf⟩]
        · intro x o ho
          simp only [S']
          split
          · rename_i hMF
            obtain ⟨hx, hnb, hxf⟩ := hMF
            have hnp := hnpj x _ (hfsj x hxf) hnb
            rw [hms] at hnp
            obtain ⟨L, hmem⟩ := hKdx _ x o (hfsj x hxf) hnp hx (hS₀Lx x hx o ho)
            exact ⟨L, hKsM2 _ hmem⟩
          · exact ho
      · -- the proof binding for every field not bound by the leading arguments
        refine finish infoL kaM S₀ false τ₀ (forall₂_append_single hinfoL hkaM) hτ₀ hty₀ nofun
          nofun (fun _ => .inr (hEH _ (by simp [hlenL]))) ⟨hS₀b, ?_⟩ fun _ _ h => h
        intro x hx
        rcases leadOr x hx with hb | ⟨hnb, hxf⟩
        · obtain ⟨i, hi, hfirst⟩ := firstOcc x hb
          obtain ⟨kk, hk1, hk2, hk3, hk4⟩ := leadBind infoL hinfoL (prefixTy infoL kaM hinfoL PT)
            hKsiL x i hx hi hfirst
          exact .inl ⟨i, kk, hi, hfirst, hk1, hk2, hk3, hk4⟩
        · obtain ⟨j, hj⟩ := fieldIdx x hxf
          obtain ⟨hP, hprop⟩ := hpf x hx hnb v vS Wv' tvv'
          have hL := lookup_binderTy (Γ := []) (ls := m1) hx
          exact .inr ⟨hnb, j, hj, .inr (.inl ⟨⟨_, .self, (Wv'.lookup hL).hasType.1⟩, hP,
            proofBind x hx hnb hprop⟩)⟩



end

/-- The relation of an instance's arguments to the reduct template, at a valuation `(σ, S)` of
the instance's context: the reduct's arguments `argsR` are typed along the template's binders
at the argument valuation, a leading argument binding a variable is equal to it and has its
type class and its observations up to subsumption, and the domain class of the constructor
spine at a field is the field's binder class. -/
def IotaArgRel (env : VEnv) (U : Nat) (Δ Γ : List VExpr) (n ctor : Name) (m1 lsC : List VLevel)
    (cnp nf : Nat) (doms lead recArgs ctorArgs argsR : List VExpr) (σ : VExpr.Subst)
    (S : ObSets) : Prop :=
  Ctx.SubstEq env U Δ (VExpr.argSubst (argsR.map (·.subst σ)))
    (VExpr.argSubst (argsR.map (·.subst σ))) (doms.map (·.instL m1)).reverse ∧
  TV env U Δ (doms.map (·.instL m1)).reverse (VExpr.argSubst (argsR.map (·.subst σ)))
    (argSets env U Δ σ S argsR) ∧
  (∀ (i x : Nat), lead[i]? = some (VExpr.bvar x) → x < doms.length →
    (∀ j < i, lead[j]? ≠ some (VExpr.bvar x)) → ∃ a : VExpr, recArgs[i]? = some a ∧
      (∃ X, TyCls env U Δ ((binderTy doms m1 x).subst
          (VExpr.argSubst (argsR.map (·.subst σ)))) X ∧
        env.IsDefEq U Δ (a.subst σ) (VExpr.argSubst (argsR.map (·.subst σ)) x) X) ∧
      (∀ Aq Bq, HTS env U Δ Γ (.mkApps (.const n m1) (recArgs.take i)) (.forallE Aq Bq) →
        TyCls env U Δ ((binderTy doms m1 x).subst (VExpr.argSubst (argsR.map (·.subst σ)))) =
          TyCls env U Δ (Aq.subst σ)) ∧
      Ob.Sub (Obs env U Δ σ S a) (argSets env U Δ σ S argsR x) ∧
      Ob.Sub (argSets env U Δ σ S argsR x) (Obs env U Δ σ S a)) ∧
  ∀ j < nf, ∀ Aq Bq,
    HTS env U Δ Γ (.mkApps (.const ctor lsC) (ctorArgs.take (cnp + j))) (.forallE Aq Bq) →
    TyCls env U Δ ((binderTy doms m1 (nf - 1 - j)).subst
        (VExpr.argSubst (argsR.map (·.subst σ)))) = TyCls env U Δ (Aq.subst σ)

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- **Soundness of an instance of an ι rule**, from the static facts of the rule, the
semantic typing of the reduct template, and the relation of the instance's arguments to the
template (`IotaArgRel`) at every typed valuation. -/
theorem iota_inst_sound {n ctor : Name} {k nind cnp nf : Nat} {rhs : VExpr} {hc : rhs.Closed}
    {doms : List VExpr} {body : VExpr}
    (hp : env.pats (SimplePattern.iota n (k + nind) ctor (cnp + nf)).toPattern
      (SimplePattern.iotaRHS' n ctor k nind cnp nf rhs hc, .true))
    (hr : rhs = .wrapLams doms body)
    {ci : VConstant} {dsH : List VExpr} {RH : VExpr} {I : Name} {lsI : List VLevel}
    {iargs lead ms : List VExpr}
    (hci : env.constants n = some ci)
    (hstat : IotaStatic ci ctor k nind nf doms dsH RH I lsI iargs lead)
    (hleadU : LeadUniq ci ctor k nind nf lead)
    (huniq : PatUniq env n ctor k nind cnp nf rhs)
    (hcov : ∀ x < doms.length, VExpr.bvar x ∈ lead ∨ x ∈ iotaFs nf)
    (hIrig : env.Rigid I) (hcf : CtorFam env ctor I) (hcis : IsCtor env ctor)
    (hcrig : env.Rigid ctor) (hctor : ∀ c, IsCtor env c → env.Rigid c)
    (hpctor : ∀ c, IsProjCtor env c → env.Rigid c)
    (hnodf : ∀ df', env.defeqs df' → ∀ ls', df'.lhs.stripLams.getAppFnArgs.1 ≠ .const n ls')
    {m1 lsC : List VLevel} (hms : ms.length = cnp)
    (hfam : MajorFam env U Δ [] I ctor doms lead ms (iotaFs nf) m1 lsI)
    (hC : ∀ keys : List Key, keys.length = lead.length →
      Obs' .id .empty (ci.type.instL m1) (piCodChain keys
        (.piDomOb (.rigid I ((lsI.map (·.inst m1)).map (·.eval)) iargs.length fun _ => 0))) →
      (∀ (p' : Pattern) (r' : p'.RHS × p'.Check), env.pats p' r' → p'.headConst = n →
        ∃ h : p' = (SimplePattern.iota n (k + nind) ctor (cnp + nf)).toPattern,
          h ▸ r' = (SimplePattern.iotaRHS' n ctor k nind cnp nf rhs hc, .true)) ∧
      ∀ x < doms.length, (∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) →
        ∀ v vS, Ctx.SubstEq env U Δ v v ((doms.map (·.instL m1)).reverse ++ []) →
        TV env U Δ ((doms.map (·.instL m1)).reverse ++ []) v vS →
        (∃ P, TyCls env U Δ ((binderTy doms m1 x).subst v) P ∧
          env.HasType U Δ P (.sort .zero)) ∧
        ∀ τ, Obs' v vS (binderTy doms m1 x) τ → ∃ cv', TypedOb env U Δ cv' τ [.sort fun _ => 0])
    {recArgs ctorArgs argsR : List VExpr}
    (hrA : recArgs.length = k + nind) (hcA : ctorArgs.length = cnp + nf)
    (hargs : argsR = recArgs.take k ++ ctorArgs.drop cnp)
    {Γ : List VExpr} {A : VExpr}
    (ihe : SoundAt env U Δ Γ (.mkApps (.const n m1) (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs]))
        (.mkApps (.const n m1) (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs])) A ∧
      HTS env U Δ Γ (.mkApps (.const n m1) (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs])) A)
    (ihred : SoundAt env U Δ Γ (.mkApps (rhs.instL m1) argsR) (.mkApps (rhs.instL m1) argsR) A)
    (heqI : env.IsDefEq U Γ (.mkApps (.const n m1) (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs]))
      (.mkApps (rhs.instL m1) argsR) A)
    {T : VExpr} (hRH : HTS env U Δ [] (rhs.instL m1) T)
    (hRS : SoundAt env U Δ [] (rhs.instL m1) (rhs.instL m1) T)
    (hrel : ∀ σ S, Ctx.SubstEq env U Δ σ σ Γ → TV env U Δ Γ σ S →
      IotaArgRel env U Δ Γ n ctor m1 lsC cnp nf doms lead recArgs ctorArgs argsR σ S ∧
        List.Forall₂ (· ≈ ·) lsC (lsI.map (·.inst m1))) :
    SoundAt env U Δ Γ (.mkApps (.const n m1) (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs]))
      (.mkApps (rhs.instL m1) argsR) A := by
  intro σ σ' S W tv tv'
  have W' := SubstEq.right henv hΔ W
  obtain ⟨⟨Wv, tvv, hlead, hfield⟩, hlsC⟩ := hrel σ' S W' tv'
  have E := ihe.1 σ σ' S W tv tv'
  have hLR := iota_lhs_sub_inst henv hΔ hp hr hci hstat hleadU huniq hcrig hctor hpctor hnodf
    hfam.weak (lsC := lsC) hrA hcA hargs hRH hRS (σ := σ') rfl rfl Wv tvv
    (fun i x h1 h2 h3 => let ⟨a, ha, hd, _, hs, _⟩ := hlead i x h1 h2 h3; ⟨a, ha, hd, hs⟩)
  have hRL := iota_rhs_sub_inst henv hΔ hp hr hci hstat hcov hIrig hcf hcis hms hfam hC hlsC hrA
    hcA hargs ihe.2 ihred heqI hRH hRS W' tv' rfl rfl Wv tvv
    (fun i x h1 h2 h3 => let ⟨a, ha, hd, hT, _, hs⟩ := hlead i x h1 h2 h3; ⟨a, ha, hd, hT, hs⟩)
    hfield
  exact ⟨E.1.trans hLR, hRL.trans E.2.1, (ihe.1 σ σ S W.left tv tv).2.2.1,
    (ihred σ' σ' S W' tv' tv').2.2.1⟩

end

end Model
end VEnv
end Lean4Lean
