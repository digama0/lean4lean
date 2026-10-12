import Lean4Lean.Theory.Typing.HeadInjectivity.Model.FamSort
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.EmptyRule

/-! # Soundness of the generic equation of an ι rule

The generic λ-wrapped equation `L ≡ R` of a registered ι rule (the stored equation of the
block, `L = λ doms. rec lsP (lead ++ [ctor lsC (ms ++ fields)])`, `R = λ doms. body`) is sound
in the model, by the two directions of `Model/RuleSound.lean` at the `pat` clause of `Obs`:

* right to left, `pat_rhs_sub_head` with the head clause `Obs.pat`;
* left to right, `pat_lhs_sub_iota`, the pattern-world form of `pat_lhs_sub`: an observation
  of the left side comes from the `pat` clause of its recursor head, whose data are those of
  the rule (uniqueness of the pattern per head and constructor, `huniq`, and of the lead per
  recursor type, `hleadU`), and the body observation transfers to the right side.

`sound_iota_pat` assembles the two; `sound_iota_pat_empty` handles small elimination (no
observations on the right). -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-- The uniqueness of a registered ι pattern per head and constructor, as the left-to-right
direction reads it off the `pat` clause. -/
def PatUniq (env : VEnv) (n ctor : Name) (k nind cnp nf : Nat) (rhs : VExpr) : Prop :=
  ∀ k' nind' ctor' cnp' nf' rhs' (hc' : rhs'.Closed),
    env.pats (SimplePattern.iota n (k' + nind') ctor' (cnp' + nf')).toPattern
      (SimplePattern.iotaRHS' n ctor' k' nind' cnp' nf' rhs' hc', .true) →
    k' + nind' = k + nind ∧ (ctor' = ctor → k' = k ∧ nind' = nind ∧ cnp' = cnp ∧ nf' = nf ∧ rhs' = rhs)

/-- The uniqueness of the lead read off the recursor type for a constructor. -/
def LeadUniq (ci : VConstant) (ctor : Name) (k nind nf : Nat) (lead : List VExpr) : Prop :=
  ∀ doms' dsH' RH' I' lsI' iargs' lead',
    IotaStatic ci ctor k nind nf doms' dsH' RH' I' lsI' iargs' lead' → lead' = lead

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- **Left to right** for the generic equation of an ι rule: every observation of the left side
is subsumed by one of the right side. -/
theorem pat_lhs_sub_iota {df : VDefEq} {n : Name} {lsP : List VLevel} {doms lead ms : List VExpr}
    {ctor : Name} {lsC : List VLevel} {fs : List Nat} {body : VExpr} {ls : List VLevel}
    {σ : VExpr.Subst} {S : ObSets} {k nind cnp nf : Nat} {hc : df.rhs.Closed}
    (hp : env.pats (SimplePattern.iota n (k + nind) ctor (cnp + nf)).toPattern
      (SimplePattern.iotaRHS' n ctor k nind cnp nf df.rhs hc, .true))
    (hl : df.lhs = .wrapLams doms (.mkApps (.const n lsP)
      (lead ++ [.mkApps (.const ctor lsC) (ms ++ fs.map .bvar)])))
    (hr : df.rhs = .wrapLams doms body)
    (hlsP : lsP.map (·.inst ls) = ls) (hlcl : df.lhs.ClosedN)
    (hms : ms.length = cnp) (hfs : fs = iotaFs nf)
    (hcrig : env.Rigid ctor) (hctor : ∀ c, IsCtor env c → env.Rigid c)
    (hpctor : ∀ c, IsProjCtor env c → env.Rigid c)
    (hnodf : ∀ df', env.defeqs df' → ∀ ls', df'.lhs.stripLams.getAppFnArgs.1 ≠ .const n ls')
    (huniq : PatUniq env n ctor k nind cnp nf df.rhs)
    {ci : VConstant} {dsH : List VExpr} {RH : VExpr} {I : Name} {lsI : List VLevel}
    {iargs : List VExpr}
    (hci : env.constants n = some ci)
    (hstat : IotaStatic ci ctor k nind nf doms dsH RH I lsI iargs lead)
    (hleadU : LeadUniq ci ctor k nind nf lead)
    (hfam : MajorFamEntry env I ctor)
    (hRH : HTS env U Δ Γ (df.rhs.instL ls) (df.type.instL ls))
    (hR : SoundAt env U Δ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls))
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) :
    Ob.Sub (Obs' σ S (df.lhs.instL ls)) (Obs' σ S (df.rhs.instL ls)) := by
  have hrcl : df.rhs.ClosedN := hc
  have hleadl : lead.length = k + nind := hstat.lead_length
  obtain ⟨hdl, eH, hlenH0, hkH0, -⟩ := hstat
  have hlenH : dsH.length = lead.length + 1 := by rw [hleadl]; exact hlenH0
  have hkH : dsH[lead.length]? = some (.mkApps (.const I lsI) iargs) := by rw [hleadl]; exact hkH0
  obtain ⟨eL, eR⟩ := pat_instL hl hr hlsP
  intro o ho
  rw [eL] at ho
  obtain ⟨lk, v, vS, p, hk, rfl, hp'⟩ := Obs.wrapLams_iff.1 ho
  rw [eR] at hRH hR ⊢
  obtain ⟨B, hBs, hdomsR⟩ := HTS.wrapLams_body hRH hR
  obtain ⟨Wv, tvv⟩ := hk.typed henv hΔ hdomsR W tv
  obtain ⟨keys, hkeys, hc'⟩ := wrap_of_obs_mkApps_le hp'
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
    have := List.Forall₂.length_eq hkeys; simpa using this
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
  subst hfs
  -- closedness
  have hbcl : (body.instL ls).ClosedN doms.length := by
    have := (closedN_wrapLams (hr ▸ hrcl : (VExpr.wrapLams doms body).ClosedN 0)).1
    simpa using this.instL
  have hdcl : ∀ i (h : i < doms.length), (doms[i]).ClosedN i := by
    have := (closedN_wrapLams (hl ▸ hlcl :
      (VExpr.wrapLams doms (.mkApps (.const n lsP)
        (lead ++ [.mkApps (.const ctor lsC) (ms ++ (iotaFs nf).map .bvar)]))).ClosedN 0)).2
    simpa using this
  -- the major's arguments
  have hmargs : ∀ j x, (iotaFs nf)[j]? = some x →
      (ms.map (·.instL ls) ++ (iotaFs nf).map VExpr.bvar)[cnp + j]? = some (.bvar x) := by
    intro j x hj
    rw [List.getElem?_append_right (by simp [hms])]
    simp [hj, hms]
  -- facts about the constructor observations of the major
  have argOf : ∀ j x cl, (iotaFs nf)[j]? = some x → .ctorArg (cnp + j) cl ∈ Km → cl (v x) := by
    intro j x cl hj hcl
    obtain ⟨y, hy, ly⟩ := hKmcov _ hcl
    rw [ly.ctorArg_inv] at hy
    obtain ⟨ckeys, hck, hend⟩ := ctor_spine_inv hcrig hy (.inr (.inl ⟨_, _, rfl⟩))
    rcases hend with h | ⟨i, hi, h⟩ | ⟨_, _, _, _, h⟩
    · cases h
    · injection h with e1 e2; subst e1; subst e2
      obtain ⟨_, hci', -⟩ := List.forall₂_getElem_exists hck _ hi
      have := hmargs j x hj
      rw [List.getElem?_eq_some_iff] at this
      obtain ⟨_, ha⟩ := this
      rw [hci', ha]; exact ElCls.self
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
      obtain ⟨_, -, hcov⟩ := List.forall₂_getElem_exists hck _ hi
      have := hmargs j x hj
      rw [List.getElem?_eq_some_iff] at this
      obtain ⟨_, ha⟩ := this
      obtain ⟨k₁, hk₁, l₁⟩ := hcov k' hk'
      rw [ha] at hk₁
      exact ⟨k₁, Obs.bvar_iff.1 hk₁, l₁.trans (e3 ▸ l₀)⟩
  -- the binding, restricted to the rule's variables
  classical
  let τ' : VExpr.Subst := fun x => if x < doms.length then τ x else v x
  let S' : ObSets := fun x => if x < doms.length then S'' x else vS x
  have hτ'1 : ∀ x, x < doms.length → τ' x = τ x := fun x hx => if_pos hx
  have hτ'2 : ∀ x, doms.length ≤ x → τ' x = v x := fun x hx => if_neg (by omega)
  have hbody' : Obs' τ' S' (body.instL ls) p :=
    (Obs.closed_iff hbcl (fun i hi => (hτ'1 i hi).symm) (fun i hi => (if_pos hi).symm)).1 hbody
  have hcov : ∀ x o, S' x o → ∃ o', vS x o' ∧ o' ≼ o := by
    intro x o ho
    by_cases hx : x < doms.length
    · simp only [S', hx, if_true] at ho
      rcases hbind.2 x hx with ⟨i, k, hi, -, hki, -, -, hkS⟩ |
        ⟨-, j, hj, ⟨-, -, -, -, -, hS⟩ | ⟨-, -, hS⟩ | ⟨-, info', hpi', -, hle', -, -, -, hS⟩⟩
      · obtain ⟨o₀, ho₀, l₀⟩ := hkS o ho
        have hil : i < lkeys.length := by
          have := List.Forall₂.length_eq hkeysL
          have := (List.getElem?_eq_some_iff.1 hi).1; simp at *; omega
        obtain ⟨_, -, hcov⟩ := List.forall₂_getElem_exists hkeysL i hil
        have hk : lkeys[i] = k := by
          have := List.getElem?_eq_some_iff.1 hki; exact this.2
        rw [hk] at hcov
        obtain ⟨o', ho', l⟩ := hcov o₀ ho₀
        have ha : (lead.map (·.instL ls))[i]'(by
            have := List.Forall₂.length_eq hkeysL; omega) = .bvar x := by
          simp only [List.getElem_map]
          rw [(List.getElem?_eq_some_iff.1 hi).2]; rfl
        rw [ha] at ho'
        exact ⟨o', Obs.bvar_iff.1 ho', l.trans l₀⟩
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
        rw [show info'.nparams + (cnp + j - info'.nparams) = cnp + j by omega,
          hmargs j x hj] at ha
        cases ha
        exact ⟨k', Obs.bvar_iff.1 hk', l'.trans l₀⟩
    · simp only [S', hx, if_false] at ho
      exact ⟨o, ho, .refl⟩
  obtain ⟨p₁, hp₁, l₁⟩ := hbody'.mono_le hcov
  -- the binding is related to the actual variables
  have hL := fun x (hx : x < doms.length) => lookup_binderTy (Γ := Γ) (ls := ls) hx
  have hbcl' : ∀ x, x < doms.length →
      (binderTy doms ls x).subst τ = (binderTy doms ls x).subst τ' := fun x hx =>
    (binderTy_closed hdcl hx).subst_congr fun i hi => (hτ'1 i hi).symm
  have W' : Ctx.SubstEq env U Δ τ' v ((doms.map (·.instL ls)).reverse ++ Γ) := by
    refine SubstEq.of_heads_ind Wv (fun x hx => hτ'2 x (by simpa using hx))
      fun x A hx hLA hW => ?_
    have hx' : x < doms.length := by simpa using hx
    cases hLA.uniq (hL x hx')
    rw [hτ'1 x hx', ← hbcl' x hx']
    have hvx := (Wv.lookup (hL x hx')).hasType.1
    have hvx' : env.HasType U Δ (v x) ((binderTy doms ls x).subst τ) := by
      have hD := SubstEq.entry_typed Wv hx
      obtain ⟨uD, hDt⟩ := hD
      have hDD := hDt.substDF henv hW.wf hΔ hW
      have eA : (binderTy doms ls x) =
          ((doms.map (fun d : VExpr => d.instL ls)).reverse[x]'hx).liftN (x+1) := (hL x hx').uniq
            (lookup_append _ x hx)
      have e1 := liftN_subst_shift ((doms.map (fun d : VExpr => d.instL ls)).reverse[x]'hx) τ' x
      have e2 := liftN_subst_shift ((doms.map (fun d : VExpr => d.instL ls)).reverse[x]'hx) v x
      rw [← eA] at e1 e2
      rw [hbcl' x hx', e1]; rw [e2] at hvx; exact hDD.symm.defeqDF hvx
    rcases hbind.2 x hx' with ⟨i, k, hi, -, hki, hkt, hkm, -⟩ |
      ⟨-, j, hj, ⟨-, cl, hcl, hct, hcm, -⟩ | ⟨⟨X, hX, hτX⟩, ⟨P, hP, hPs⟩, -⟩ |
        ⟨-, info', hpi', hcn', hle', -, hTE, hpc, -⟩⟩
    · have hil : i < lkeys.length := by
        have := List.Forall₂.length_eq hkeysL
        have := (List.getElem?_eq_some_iff.1 hi).1; simp at *; omega
      obtain ⟨_, hcls, -⟩ := List.forall₂_getElem_exists hkeysL i hil
      have hk : lkeys[i] = k := (List.getElem?_eq_some_iff.1 hki).2
      have ha : (lead.map (·.instL ls))[i]'(by
          have := List.Forall₂.length_eq hkeysL; omega) = .bvar x := by
        simp only [List.getElem_map]
        rw [(List.getElem?_eq_some_iff.1 hi).2]; rfl
      rw [hk, ha] at hcls
      have hvk : k.2.1 (v x) := by rw [hcls]; exact ElCls.self
      exact hkt.defeq henv hΔ hkm hvk
    · exact hct.defeq henv hΔ hcm (argOf j x cl hj hcl)
    · -- proof binding: both are proofs of the proposition `P`
      have hτx : env.HasType U Δ (τ x) ((binderTy doms ls x).subst τ) :=
        TyCls.defeq henv hΔ hX hτX
      have h1 := TyCls.defeq_rev henv hΔ hP hτx
      have h2 := TyCls.defeq_rev henv hΔ hP hvx'
      exact TyCls.defeq henv hΔ hP (.proofIrrel hPs h1 h2)
    · -- eta binding: the anchor is a projection of the major, whose field is `v x`
      refine eta_anchor_defeq henv hΔ hpi' hTE hpc (lsc := lsC.map (·.inst ls))
        (margs := (ms.map (·.instL ls) ++ (iotaFs nf).map VExpr.bvar).map (·.subst v)) ?_ ?_ hvx'
      · rw [show cm = (Dm, cm, Km).2.1 from rfl, hcmM]
        simp only [VExpr.subst_mkApps, VExpr.subst]
        rw [hcn']; exact ElCls.self
      · rw [List.getElem?_map,
          show info'.nparams + (cnp + j - info'.nparams) = cnp + j by omega,
          hmargs j x hj]
        rfl
  have hctx := DomsSD.ctxSD (L := []) (Γ := Γ) hdomsR .nil
  simp only [List.append_nil] at hctx
  have tvτ := TV.transfer henv hΔ hctx W' (fun x hx => hτ'2 x (by simpa using hx)) tvv
  obtain ⟨p₂, hp₂, l₂⟩ := (hBs τ' v vS W' tvτ tvv).1 p₁ hp₁
  exact ⟨wrap lk p₂, Obs.wrapLams_iff.2 ⟨lk, v, vS, p₂, hk, rfl, hp₂⟩, wrap_le (l₂.trans l₁)⟩

/-- **Soundness of the generic equation of an ι rule.** -/
theorem sound_iota_pat {df : VDefEq} {n : Name} {lsP : List VLevel} {doms lead ms : List VExpr}
    {ctor : Name} {fs : List Nat} {body : VExpr} {ls : List VLevel}
    {ci : VConstant} {dsH : List VExpr} {RH : VExpr} {I : Name} {lsI : List VLevel}
    {iargs : List VExpr} {k nind cnp nf : Nat} {hc : df.rhs.Closed}
    (hp : env.pats (SimplePattern.iota n (k + nind) ctor (cnp + nf)).toPattern
      (SimplePattern.iotaRHS' n ctor k nind cnp nf df.rhs hc, .true))
    (hl : df.lhs = .wrapLams doms (.mkApps (.const n lsP)
      (lead ++ [.mkApps (.const ctor lsI) (ms ++ fs.map .bvar)])))
    (hr : df.rhs = .wrapLams doms body)
    (hcov : ∀ x < doms.length, VExpr.bvar x ∈ lead ∨ x ∈ fs)
    (hlsP : lsP.map (·.inst ls) = ls) (hlcl : df.lhs.ClosedN)
    (hms : ms.length = cnp) (hfs : fs = iotaFs nf)
    (hci : env.constants n = some ci)
    (hstat : IotaStatic ci ctor k nind nf doms dsH RH I lsI iargs lead)
    (hleadU : LeadUniq ci ctor k nind nf lead)
    (hIrig : env.Rigid I) (hcf : CtorFam env ctor I) (hcis : IsCtor env ctor)
    (hfam : MajorFam env U Δ Γ I ctor doms lead ms fs ls lsI)
    (hcrig : env.Rigid ctor)
    (hctor : ∀ c, IsCtor env c → env.Rigid c) (hpctor : ∀ c, IsProjCtor env c → env.Rigid c)
    (hnodf : ∀ df', env.defeqs df' → ∀ ls', df'.lhs.stripLams.getAppFnArgs.1 ≠ .const n ls')
    (huniq : PatUniq env n ctor k nind cnp nf df.rhs)
    (hC : ∀ keys : List Key, keys.length = lead.length →
      Obs' .id .empty (ci.type.instL ls) (piCodChain keys
        (.piDomOb (.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length fun _ => 0))) →
      (∀ (p' : Pattern) (r' : p'.RHS × p'.Check), env.pats p' r' → p'.headConst = n →
        ∃ h : p' = (SimplePattern.iota n (k + nind) ctor (cnp + nf)).toPattern,
          h ▸ r' = (SimplePattern.iotaRHS' n ctor k nind cnp nf df.rhs hc, .true)) ∧
      ∀ x < doms.length, (∀ i : Nat, lead[i]? ≠ some (VExpr.bvar x)) →
        ∀ v vS, Ctx.SubstEq env U Δ v v ((doms.map (·.instL ls)).reverse ++ Γ) →
        TV env U Δ ((doms.map (·.instL ls)).reverse ++ Γ) v vS →
        (∃ P, TyCls env U Δ ((binderTy doms ls x).subst v) P ∧
          env.HasType U Δ P (.sort .zero)) ∧
        ∀ τ, Obs' v vS (binderTy doms ls x) τ → ∃ cv', TypedOb env U Δ cv' τ [.sort fun _ => 0])
    (ihL : SoundAt env U Δ Γ (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls) ∧
      HTS env U Δ Γ (df.lhs.instL ls) (df.type.instL ls))
    (ihR : SoundAt env U Δ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) ∧
      HTS env U Δ Γ (df.rhs.instL ls) (df.type.instL ls))
    (heq : env.IsDefEq U Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls)) :
    SoundAt env U Δ Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) := by
  have hleadl : lead.length = k + nind := hstat.lead_length
  have ⟨hdl, eH, hlenH0, hkH0, _⟩ := hstat
  have hlenH : dsH.length = lead.length + 1 := by rw [hleadl]; exact hlenH0
  have hkH : dsH[lead.length]? = some (.mkApps (.const I lsI) iargs) := by rw [hleadl]; exact hkH0
  intro σ σ' S W tv tv'
  have W' := SubstEq.right henv hΔ W
  have hLc := hlcl.instL (ls := ls)
  have hRc : (df.rhs.instL ls).ClosedN := hc.instL
  refine ⟨fun o h => ?_, fun o h => ?_, (ihL.1 σ σ S W.left tv tv).2.2.1,
    (ihR.1 σ' σ' S W' tv' tv').2.2.1⟩
  · obtain ⟨o', h1, l⟩ := pat_lhs_sub_iota henv hΔ hp hl hr hlsP hlcl hms hfs hcrig hctor hpctor
      hnodf huniq hci hstat hleadU hfam.weak ihR.2 ihR.1 W.left tv o h
    exact ⟨o', (Obs.closed_iff_id hRc).2 ((Obs.closed_iff_id hRc).1 h1), l⟩
  · obtain ⟨eL, eR⟩ := pat_instL hl hr hlsP
    obtain ⟨o', h1, l⟩ := pat_rhs_sub_head henv hΔ (hd := .const n ls) (type := ci.type)
      (Single := ∀ (p' : Pattern) (r' : p'.RHS × p'.Check), env.pats p' r' → p'.headConst = n →
        ∃ h : p' = (SimplePattern.iota n (k + nind) ctor (cnp + nf)).toPattern,
          h ▸ r' = (SimplePattern.iotaRHS' n ctor k nind cnp nf df.rhs hc, .true))
      ⟨_, _, rfl⟩ (fun Th ⟨_, _, ci', e, hci', _, he⟩ => by
        cases e; cases hci.symm.trans hci'; exact he) eL eR hcov eH hlenH hkH hIrig hcf hcis hfam
      (fun mC hτ hty hlen hsingle hmobs hhdC hbind hbk hbody => by
        subst hfs
        refine Obs.pat hp hr hstat hci hτ hty (by rw [hlen, hleadl]) hsingle hmobs ?_
          (by simpa [hms] using hbind) hbk hbody
        intro h; rcases hhdC h with ⟨ℓs, hmem⟩ | hEH
        · exact .inl ⟨ℓs, by simpa [hms] using hmem⟩
        · exact .inr hEH)
      hC ihL.2 ihR.1 heq W' tv' o h
    · exact ⟨o', (Obs.closed_iff_id hLc).2 ((Obs.closed_iff_id hLc).1 h1), l⟩

/-- Soundness of the generic equation of an ι rule whose right-hand side has no observations
at typed valuations (small elimination). -/
theorem sound_iota_pat_empty {df : VDefEq} {n : Name} {lsP : List VLevel}
    {doms lead ms : List VExpr} {ctor : Name} {lsC : List VLevel} {fs : List Nat} {body : VExpr}
    {ls : List VLevel} {k nind cnp nf : Nat} {hc : df.rhs.Closed}
    (hp : env.pats (SimplePattern.iota n (k + nind) ctor (cnp + nf)).toPattern
      (SimplePattern.iotaRHS' n ctor k nind cnp nf df.rhs hc, .true))
    (hl : df.lhs = .wrapLams doms (.mkApps (.const n lsP)
      (lead ++ [.mkApps (.const ctor lsC) (ms ++ fs.map .bvar)])))
    (hr : df.rhs = .wrapLams doms body)
    (hlsP : lsP.map (·.inst ls) = ls) (hlcl : df.lhs.ClosedN)
    (hms : ms.length = cnp) (hfs : fs = iotaFs nf)
    (hcrig : env.Rigid ctor) (hctor : ∀ c, IsCtor env c → env.Rigid c)
    (hpctor : ∀ c, IsProjCtor env c → env.Rigid c)
    (hnodf : ∀ df', env.defeqs df' → ∀ ls', df'.lhs.stripLams.getAppFnArgs.1 ≠ .const n ls')
    (huniq : PatUniq env n ctor k nind cnp nf df.rhs)
    {ci : VConstant} {dsH : List VExpr} {RH : VExpr} {I : Name} {lsI : List VLevel}
    {iargs : List VExpr}
    (hci : env.constants n = some ci)
    (hstat : IotaStatic ci ctor k nind nf doms dsH RH I lsI iargs lead)
    (hleadU : LeadUniq ci ctor k nind nf lead)
    (hfam : MajorFamEntry env I ctor)
    (ihL : SoundAt env U Δ Γ (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls))
    (ihR : SoundAt env U Δ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) ∧
      HTS env U Δ Γ (df.rhs.instL ls) (df.type.instL ls))
    (hE : ∀ σ S, Ctx.SubstEq env U Δ σ σ Γ → TV env U Δ Γ σ S → ∀ o,
      ¬ Obs' σ S (df.rhs.instL ls) o) :
    SoundAt env U Δ Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) := by
  intro σ σ' S W tv tv'
  have W' := SubstEq.right henv hΔ W
  refine ⟨fun o h => ?_, fun o h => absurd h (hE σ' S W' tv' o),
    (ihL σ σ S W.left tv tv).2.2.1, (ihR.1 σ' σ' S W' tv' tv').2.2.1⟩
  obtain ⟨o', h1, -⟩ := pat_lhs_sub_iota henv hΔ hp hl hr hlsP hlcl hms hfs hcrig hctor hpctor
    hnodf huniq hci hstat hleadU hfam ihR.2 ihR.1 W.left tv o h
  exact absurd h1 (hE σ S W.left tv o')

end

end Model
end VEnv
end Lean4Lean
