import Lean4Lean.Theory.Typing.HeadInjectivity.Model.EmptyRule

/-! # Soundness of eliminator rules

The analogue of `Model/RuleSound.lean` for generic case equations, whose left-hand sides are
headed by an abstract eliminator `.elim b o ls`: `sound_pat_elim` (mode AB; mode C is excluded
by a hypothesis) and `sound_pat_elim_empty` (a right-hand side without observations). The
head's type is the schema's generic type; its semantic typing derivation lives in the
derivation's context (`HTS.elim`), so the family indicator is read at a typed valuation of
that context (`major_indicator_gen`). -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

omit henv hΔ in
theorem HeadTy.elim_eq {schema : InductiveSignature.CaseSchema}
    {owner : Fin schema.signature.families.size} {Th type : VExpr}
    (hEu : ∀ b s s', env.eliminators b s → env.eliminators b s' → s = s')
    (h : HeadTy env U (.elim b owner.val ls) Th) (hb : env.eliminators b schema)
    (htype : schema.genericType owner = some type) : Th = type.instL ls := by
  rcases h with ⟨_, _, _, e, -⟩ | ⟨b', ls', schema', owner', type', e, hb', ht', -, -, rfl⟩
  · cases e
  · injection e with e1 e2 e3
    subst e1 e3
    cases hEu _ _ _ hb hb'
    cases Fin.ext e2
    cases htype.symm.trans ht'
    rfl

omit henv hΔ in
theorem VExpr.getAppFnArgs_mkApps_elim :
    (VExpr.mkApps (.elim b o ls) as).getAppFnArgs = (.elim b o ls, as) := by
  rw [VExpr.getAppFnArgs, VExpr.getAppFnArgs_go_mkApps]; simp [VExpr.getAppFnArgs.go]

omit henv hΔ in
theorem wrapLams_pat_inj_elim :
    ∀ {ds ds' : List VExpr} {as as' : List VExpr} {a a' : VExpr},
    VExpr.wrapLams ds (.mkApps (.elim b o ls) (as ++ [a])) =
      VExpr.wrapLams ds' (.mkApps (.elim b o ls') (as' ++ [a'])) →
    ds = ds' ∧ ls = ls' ∧ as = as' ∧ a = a'
  | [], [], as, as', a, a', h => by
    simp only [VExpr.wrapLams, List.foldr_nil, VExpr.mkApps_snoc] at h
    injection h with h1 h2
    have := congrArg VExpr.getAppFnArgs h1
    rw [VExpr.getAppFnArgs_mkApps_elim, VExpr.getAppFnArgs_mkApps_elim] at this
    simp only [Prod.mk.injEq, VExpr.elim.injEq] at this
    exact ⟨rfl, this.1.2.2, this.2, h2⟩
  | [], _ :: _, as, as', a, a', h => by
    simp only [VExpr.wrapLams, List.foldr_nil, List.foldr_cons, VExpr.mkApps_snoc] at h; cases h
  | _ :: _, [], as, as', a, a', h => by
    simp only [VExpr.wrapLams, List.foldr_nil, List.foldr_cons, VExpr.mkApps_snoc] at h; cases h
  | d :: ds, d' :: ds', as, as', a, a', h => by
    simp only [VExpr.wrapLams, List.foldr_cons] at h
    injection h with h1 h2
    obtain ⟨rfl, h3⟩ := wrapLams_pat_inj_elim h2
    exact ⟨by rw [h1], h3⟩

omit henv hΔ in
theorem pat_instL_elim {df : VDefEq} {fs : List Nat}
    (hl : df.lhs = .wrapLams doms (.mkApps (.elim b o lsP)
      (lead ++ [.mkApps (.const ctor lsC) (ms ++ fs.map .bvar)])))
    (hr : df.rhs = .wrapLams doms body) (hlsP : lsP.map (·.inst ls) = ls) :
    df.lhs.instL ls = .wrapLams (doms.map (·.instL ls)) (.mkApps (.elim b o ls)
      (lead.map (·.instL ls) ++ [.mkApps (.const ctor (lsC.map (·.inst ls)))
        (ms.map (·.instL ls) ++ fs.map .bvar)])) ∧
    df.rhs.instL ls = .wrapLams (doms.map (·.instL ls)) (body.instL ls) := by
  refine ⟨?_, by rw [hr, instL_wrapLams]⟩
  rw [hl, instL_wrapLams]
  simp only [VExpr.instL_mkApps, VExpr.instL, List.map_append, List.map_cons, List.map_nil,
    List.map_map, Function.comp_def, hlsP]

/-- **Right to left** for an eliminator rule. -/
theorem pat_rhs_sub_elim {df : VDefEq} {b : Name} {schema : InductiveSignature.CaseSchema}
    {owner : Fin schema.signature.families.size} {rules : List VDefEq} {type : VExpr} {lsP : List VLevel} {doms lead ms : List VExpr}
    {ctor : Name} {lsC : List VLevel} {fs : List Nat} {body : VExpr} {ls : List VLevel}
    {σ : VExpr.Subst} {S : ObSets}
    (hEu : ∀ b s s', env.eliminators b s → env.eliminators b s' → s = s')
    (hb : env.eliminators b schema) (hrules : schema.genericEquations b owner = some rules)
    (hmem : df ∈ rules)
    (hl : df.lhs = .wrapLams doms (.mkApps (.elim b owner.val lsP)
      (lead ++ [.mkApps (.const ctor lsC) (ms ++ fs.map .bvar)])))
    (hr : df.rhs = .wrapLams doms body)
    (hcov : ∀ x < doms.length, VExpr.bvar x ∈ lead ∨ x ∈ fs)
    (hlsP : lsP.map (·.inst ls) = ls)
    {dsH : List VExpr} {RH : VExpr} {I : Name} {lsI : List VLevel}
    {iargs : List VExpr}
    (htype : schema.genericType owner = some type) (eH : type = .wrapForalls dsH RH)
    (hlenH : dsH.length = lead.length + 1)
    (hkH : dsH[lead.length]? = some (.mkApps (.const I lsI) iargs)) (hIrig : env.Rigid I)
    (hcf : CtorFam env ctor I)
    (hcis : IsCtor env ctor) (hfam : MajorFam env U Δ Γ I ctor doms lead ms fs ls lsC)
    (hC : ∀ keys : List Key, keys.length = lead.length →
      Obs' .id .empty (type.instL ls) (piCodChain keys
        (.piDomOb (.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length fun _ => 0))) →
      False)
    (hL : HTS env U Δ Γ (df.lhs.instL ls) (df.type.instL ls))
    (hR : SoundAt env U Δ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls))
    (heq : env.IsDefEq U Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls))
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) :
    Ob.Sub (Obs' σ S (df.rhs.instL ls)) (Obs' σ S (df.lhs.instL ls)) := by
  obtain ⟨eL, eR⟩ := pat_instL_elim hl hr hlsP
  refine pat_rhs_sub_head henv hΔ (Single := False) (.inr ⟨_, _, _, rfl⟩)
    (fun _ hTh => HeadTy.elim_eq hEu hTh hb htype) eL eR hcov eH hlenH hkH hIrig hcf hcis hfam
    ?_ (fun keys hk h => (hC keys hk h).elim) hL hR heq W tv
  intro _ _ _ _ _ _ _ _ _ _ mC hτ hty hlen hsingle _ hhd hbind hbk hp
  cases mC
  · exact Obs.elimRule hb hrules hmem hl hr htype hτ hty hlen (hhd rfl) hbind hbk hp
  · exact (hsingle rfl).elim

/-- **Left to right** for an eliminator rule. -/
theorem pat_lhs_sub_elim {df : VDefEq} {b : Name} {schema : InductiveSignature.CaseSchema}
    {owner : Fin schema.signature.families.size} {rules : List VDefEq} {lsP : List VLevel} {doms lead ms : List VExpr}
    {ctor : Name} {lsC : List VLevel} {fs : List Nat} {body : VExpr} {ls : List VLevel}
    {σ : VExpr.Subst} {S : ObSets}
    (hEu : ∀ b s s', env.eliminators b s → env.eliminators b s' → s = s')
    (hb : env.eliminators b schema) (hrules : schema.genericEquations b owner = some rules)
    (hl : df.lhs = .wrapLams doms (.mkApps (.elim b owner.val lsP)
      (lead ++ [.mkApps (.const ctor lsC) (ms ++ fs.map .bvar)])))
    (hr : df.rhs = .wrapLams doms body)
    (hlsP : lsP.map (·.inst ls) = ls) (hlcl : df.lhs.ClosedN) (hrcl : df.rhs.ClosedN)
    (hcrig : env.Rigid ctor)
    (huniq : ∀ (df' : VDefEq) (doms' : List VExpr) (lsP' : List VLevel) (lead' : List VExpr)
      (ctor' : Name) (lsC' : List VLevel) (ms' : List VExpr) (fs' : List Nat) (body' : VExpr),
      df' ∈ rules →
      df'.lhs = .wrapLams doms' (.mkApps (.elim b owner.val lsP')
        (lead' ++ [.mkApps (.const ctor' lsC') (ms' ++ fs'.map .bvar)])) →
      df'.rhs = .wrapLams doms' body' →
      lead'.length = lead.length ∧ (ctor' = ctor → df' = df))
    {type : VExpr} {dsH : List VExpr} {RH : VExpr} {I : Name} {lsI : List VLevel}
    {iargs : List VExpr}
    (htype : schema.genericType owner = some type) (eH : type = .wrapForalls dsH RH)
    (hlenH : dsH.length = lead.length + 1)
    (hkH : dsH[lead.length]? = some (.mkApps (.const I lsI) iargs))
    (hfam : MajorFamEntry env I ctor)
    (hRH : HTS env U Δ Γ (df.rhs.instL ls) (df.type.instL ls))
    (hR : SoundAt env U Δ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls))
    (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) :
    Ob.Sub (Obs' σ S (df.lhs.instL ls)) (Obs' σ S (df.rhs.instL ls)) := by
  obtain ⟨eL, eR⟩ := pat_instL_elim hl hr hlsP
  intro o ho
  rw [eL] at ho
  obtain ⟨lk, v, vS, p, hk, rfl, hp⟩ := Obs.wrapLams_iff.1 ho
  rw [eR] at hRH hR ⊢
  obtain ⟨B, hBs, hdomsR⟩ := HTS.wrapLams_body hRH hR
  obtain ⟨Wv, tvv⟩ := hk.typed henv hΔ hdomsR W tv
  obtain ⟨keys, hkeys, hc⟩ := wrap_of_obs_mkApps_le hp
  obtain ⟨schema'', owner'', rules'', df'', doms'', lsP'', lead'', ctor'', lsC'', ms'', fs'',
    body'', type'', τs, lkeys, Dm, cm, Km, p'', τ, S'', I'', eo, e, hb'', hrules'', hmem'', hl'',
    hr'', htype'', -, -, hlen'', hhd, hbind, -, hbody⟩ := Obs.elim_iff.1 hc
  cases hEu _ _ _ hb hb''
  cases Fin.ext eo
  cases hrules.symm.trans hrules''
  obtain ⟨hleadlen, huq⟩ := huniq df'' doms'' lsP'' lead'' ctor'' lsC'' ms'' fs'' body'' hmem''
    hl'' hr''
  have hklen : keys.length = lead.length + 1 := by
    have := List.Forall₂.length_eq hkeys; simpa using this
  obtain ⟨ekeys, rfl⟩ := wrap_inj_len (by simp [hklen, hlen'', hleadlen]) e
  subst ekeys
  obtain ⟨lkeys', mk, ekl, hkeysL, hkM⟩ := List.forall₂_snoc_right hkeys
  obtain ⟨rfl, emk⟩ := List.append_inj' ekl (by simp)
  cases emk
  obtain ⟨hcmM, hKmcov⟩ := hkM
  -- the clause's rule is the given one
  have hdf_eq : df'' = df := by
    apply huq
    rcases hhd with ⟨ℓs, hmem⟩ | hEH
    · obtain ⟨y, hy, ly⟩ := hKmcov _ hmem
      rw [ly.ctorHead_inv] at hy
      obtain ⟨_, _, hend⟩ := ctor_spine_inv hcrig hy (.inl ⟨_, _, _, rfl⟩)
      rcases hend with h | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩
      · injection h
      · cases h
      · cases h
    · -- the generic type names the family `I`, which is projection-registered
      cases htype.symm.trans htype''
      have hll : lkeys.length = lead.length := hlen''.trans hleadlen
      obtain ⟨rfl, info', hpi', hcn'⟩ :=
        hEH.fam eH (by rw [hll]; exact hlenH) (by rw [hll]; exact hkH)
      rcases hfam with ⟨hnp, -⟩ | ⟨info, hpi, hcn⟩
      · exact absurd hpi' (hnp _)
      · cases henv.projections_unique hpi hpi'
        exact hcn'.symm.trans hcn
  subst hdf_eq
  obtain ⟨rfl, -, rfl, emaj⟩ := wrapLams_pat_inj_elim (hl''.symm.trans hl)
  obtain ⟨rfl, rfl, emargs⟩ := VExpr.mkApps_const_inj emaj
  obtain ⟨-, rfl⟩ := wrapLams_inj_len rfl (hr''.symm.trans hr)
  -- closedness
  have hbcl : (body''.instL ls).ClosedN doms''.length := by
    have := (closedN_wrapLams (hr ▸ hrcl : (VExpr.wrapLams doms'' body'').ClosedN 0)).1
    simpa using this.instL
  have hdcl : ∀ i (h : i < doms''.length), (doms''[i]).ClosedN i := by
    have := (closedN_wrapLams (hl ▸ hlcl :
      (VExpr.wrapLams doms'' (.mkApps (.elim b owner.val lsP)
        (lead'' ++ [.mkApps (.const ctor'' lsC'') (ms ++ fs.map .bvar)]))).ClosedN 0)).2
    simpa using this
  -- the major's arguments
  have hmargs : ∀ j x, fs''[j]? = some x →
      (ms.map (·.instL ls) ++ fs.map VExpr.bvar)[ms''.length + j]? = some (.bvar x) := by
    intro j x hj
    have e1 : ms.map (·.instL ls) ++ fs.map VExpr.bvar =
        (ms'' ++ fs''.map VExpr.bvar).map (·.instL ls) := by
      rw [emargs]; simp [List.map_append, VExpr.instL]
    rw [e1, List.getElem?_map, List.getElem?_append_right (by simp)]
    simp [hj, VExpr.instL]
  -- facts about the constructor observations of the major
  have argOf : ∀ j x cl, fs''[j]? = some x → .ctorArg (ms''.length + j) cl ∈ Km → cl (v x) := by
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
  have argObOf : ∀ j x pre k, fs''[j]? = some x →
      .ctorArgOb (ms''.length + j) pre k ∈ Km → ∃ k', vS x k' ∧ k' ≼ k := by
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
  let τ' : VExpr.Subst := fun x => if x < doms''.length then τ x else v x
  let S' : ObSets := fun x => if x < doms''.length then S'' x else vS x
  have hτ'1 : ∀ x, x < doms''.length → τ' x = τ x := fun x hx => if_pos hx
  have hτ'2 : ∀ x, doms''.length ≤ x → τ' x = v x := fun x hx => if_neg (by omega)
  have hbody' : Obs' τ' S' (body''.instL ls) p :=
    (Obs.closed_iff hbcl (fun i hi => (hτ'1 i hi).symm) (fun i hi => (if_pos hi).symm)).1 hbody
  have hcov : ∀ x o, S' x o → ∃ o', vS x o' ∧ o' ≼ o := by
    intro x o ho
    by_cases hx : x < doms''.length
    · simp only [S', hx, if_true] at ho
      rcases hbind.2 x hx with ⟨i, k, hi, -, hki, -, -, hkS⟩ |
        ⟨-, j, hj, ⟨-, -, -, -, -, hS⟩ | ⟨-, -, hS⟩ | ⟨-, info', hpi', -, hle', -, -, -, hS⟩⟩
      · rw [hkS] at ho
        have hil : i < lkeys.length := by
          have := List.Forall₂.length_eq hkeysL
          have := (List.getElem?_eq_some_iff.1 hi).1; simp at *; omega
        obtain ⟨_, -, hcov⟩ := List.forall₂_getElem_exists hkeysL i hil
        have hk : lkeys[i] = k := by
          have := List.getElem?_eq_some_iff.1 hki; exact this.2
        rw [hk] at hcov
        obtain ⟨o', ho', l⟩ := hcov o ho
        have ha : (lead''.map (·.instL ls))[i]'(by
            have := List.Forall₂.length_eq hkeysL; omega) = .bvar x := by
          simp only [List.getElem_map]
          rw [(List.getElem?_eq_some_iff.1 hi).2]; rfl
        rw [ha] at ho'
        exact ⟨o', Obs.bvar_iff.1 ho', l⟩
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
        cases henv.projections_unique hpi' hpi''
        rw [show info'.nparams + (ms''.length + j - info'.nparams) = ms''.length + j by omega,
          hmargs j x hj] at ha
        cases ha
        exact ⟨k', Obs.bvar_iff.1 hk', l'.trans l₀⟩
    · simp only [S', hx, if_false] at ho
      exact ⟨o, ho, .refl⟩
  obtain ⟨p₁, hp₁, l₁⟩ := hbody'.mono_le hcov
  -- the binding is related to the actual variables
  have hL := fun x (hx : x < doms''.length) => lookup_binderTy (Γ := Γ) (ls := ls) hx
  have hbcl' : ∀ x, x < doms''.length →
      (binderTy doms'' ls x).subst τ = (binderTy doms'' ls x).subst τ' := fun x hx =>
    (binderTy_closed hdcl hx).subst_congr fun i hi => (hτ'1 i hi).symm
  have W' : Ctx.SubstEq env U Δ τ' v ((doms''.map (·.instL ls)).reverse ++ Γ) := by
    refine SubstEq.of_heads_ind Wv (fun x hx => hτ'2 x (by simpa using hx))
      fun x A hx hLA hW => ?_
    have hx' : x < doms''.length := by simpa using hx
    cases hLA.uniq (hL x hx')
    rw [hτ'1 x hx', ← hbcl' x hx']
    have hvx := (Wv.lookup (hL x hx')).hasType.1
    have hvx' : env.HasType U Δ (v x) ((binderTy doms'' ls x).subst τ) := by
      have hD := SubstEq.entry_typed Wv hx
      obtain ⟨uD, hDt⟩ := hD
      have hDD := hDt.substDF henv hW.wf hΔ hW
      have eA : (binderTy doms'' ls x) =
          ((doms''.map (fun d : VExpr => d.instL ls)).reverse[x]'hx).liftN (x+1) := (hL x hx').uniq
            (lookup_append _ x hx)
      have e1 := liftN_subst_shift ((doms''.map (fun d : VExpr => d.instL ls)).reverse[x]'hx) τ' x
      have e2 := liftN_subst_shift ((doms''.map (fun d : VExpr => d.instL ls)).reverse[x]'hx) v x
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
      have ha : (lead''.map (·.instL ls))[i]'(by
          have := List.Forall₂.length_eq hkeysL; omega) = .bvar x := by
        simp only [List.getElem_map]
        rw [(List.getElem?_eq_some_iff.1 hi).2]; rfl
      rw [hk, ha] at hcls
      have hvk : k.2.1 (v x) := by rw [hcls]; exact ElCls.self
      exact hkt.defeq henv hΔ hkm hvk
    · exact hct.defeq henv hΔ hcm (argOf j x cl hj hcl)
    · -- proof binding: both are proofs of the proposition `P`
      have hτx : env.HasType U Δ (τ x) ((binderTy doms'' ls x).subst τ) :=
        TyCls.defeq henv hΔ hX hτX
      have h1 := TyCls.defeq_rev henv hΔ hP hτx
      have h2 := TyCls.defeq_rev henv hΔ hP hvx'
      exact TyCls.defeq henv hΔ hP (.proofIrrel hPs h1 h2)
    · -- eta binding: the anchor is a projection of the major, whose field is `v x`
      refine eta_anchor_defeq henv hΔ hpi' hTE hpc (lsc := lsC''.map (·.inst ls))
        (margs := (ms.map (·.instL ls) ++ fs.map VExpr.bvar).map (·.subst v)) ?_ ?_ hvx'
      · rw [show cm = (Dm, cm, Km).2.1 from rfl, hcmM]
        simp only [VExpr.subst_mkApps, VExpr.subst]
        rw [hcn']; exact ElCls.self
      · rw [List.getElem?_map,
          show info'.nparams + (ms''.length + j - info'.nparams) = ms''.length + j by omega,
          hmargs j x hj]
        rfl
  have hctx := DomsSD.ctxSD (L := []) (Γ := Γ) hdomsR .nil
  simp only [List.append_nil] at hctx
  have tvτ := TV.transfer henv hΔ hctx W' (fun x hx => hτ'2 x (by simpa using hx)) tvv
  obtain ⟨p₂, hp₂, l₂⟩ := (hBs τ' v vS W' tvτ tvv).1 p₁ hp₁
  exact ⟨wrap lk p₂, Obs.wrapLams_iff.2 ⟨lk, v, vS, p₂, hk, rfl, hp₂⟩, wrap_le (l₂.trans l₁)⟩

/-- **Soundness of an eliminator rule** (mode AB; mode C excluded by `hC`). -/
theorem sound_pat_elim {df : VDefEq} {b : Name} {schema : InductiveSignature.CaseSchema}
    {owner : Fin schema.signature.families.size} {rules : List VDefEq} {type : VExpr}
    {lsP : List VLevel} {doms lead ms : List VExpr}
    {ctor : Name} {lsC : List VLevel} {fs : List Nat} {body : VExpr} {ls : List VLevel}
    {dsH : List VExpr} {RH : VExpr} {I : Name} {lsI : List VLevel} {iargs : List VExpr}
    (hEu : ∀ b s s', env.eliminators b s → env.eliminators b s' → s = s')
    (hb : env.eliminators b schema) (hrules : schema.genericEquations b owner = some rules)
    (hmem : df ∈ rules)
    (hl : df.lhs = .wrapLams doms (.mkApps (.elim b owner.val lsP)
      (lead ++ [.mkApps (.const ctor lsC) (ms ++ fs.map .bvar)])))
    (hr : df.rhs = .wrapLams doms body)
    (hcov : ∀ x < doms.length, VExpr.bvar x ∈ lead ∨ x ∈ fs)
    (hlsP : lsP.map (·.inst ls) = ls) (hlcl : df.lhs.ClosedN) (hrcl : df.rhs.ClosedN)
    (htype : schema.genericType owner = some type) (eH : type = .wrapForalls dsH RH)
    (hlenH : dsH.length = lead.length + 1)
    (hkH : dsH[lead.length]? = some (.mkApps (.const I lsI) iargs)) (hIrig : env.Rigid I)
    (hcf : CtorFam env ctor I)
    (hcis : IsCtor env ctor) (hfam : MajorFam env U Δ Γ I ctor doms lead ms fs ls lsC)
   
    (hcrig : env.Rigid ctor)
    (huniq : ∀ (df' : VDefEq) (doms' : List VExpr) (lsP' : List VLevel) (lead' : List VExpr)
      (ctor' : Name) (lsC' : List VLevel) (ms' : List VExpr) (fs' : List Nat) (body' : VExpr),
      df' ∈ rules →
      df'.lhs = .wrapLams doms' (.mkApps (.elim b owner.val lsP')
        (lead' ++ [.mkApps (.const ctor' lsC') (ms' ++ fs'.map .bvar)])) →
      df'.rhs = .wrapLams doms' body' →
      lead'.length = lead.length ∧ (ctor' = ctor → df' = df))
    (hC : ∀ keys : List Key, keys.length = lead.length →
      Obs' .id .empty (type.instL ls) (piCodChain keys
        (.piDomOb (.rigid I ((lsI.map (·.inst ls)).map (·.eval)) iargs.length fun _ => 0))) →
      False)
    (ihL : SoundAt env U Δ Γ (df.lhs.instL ls) (df.lhs.instL ls) (df.type.instL ls) ∧
      HTS env U Δ Γ (df.lhs.instL ls) (df.type.instL ls))
    (ihR : SoundAt env U Δ Γ (df.rhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) ∧
      HTS env U Δ Γ (df.rhs.instL ls) (df.type.instL ls))
    (heq : env.IsDefEq U Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls)) :
    SoundAt env U Δ Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) := by
  intro σ σ' S W tv tv'
  have W' := SubstEq.right henv hΔ W
  have hLc := hlcl.instL (ls := ls)
  have hRc := hrcl.instL (ls := ls)
  refine ⟨fun o h => ?_, fun o h => ?_, (ihL.1 σ σ S W.left tv tv).2.2.1,
    (ihR.1 σ' σ' S W' tv' tv').2.2.1⟩
  · obtain ⟨o', h1, l⟩ := pat_lhs_sub_elim henv hΔ hEu hb hrules hl hr hlsP hlcl hrcl hcrig
      huniq htype eH hlenH hkH hfam.weak ihR.2 ihR.1 W.left tv o h
    exact ⟨o', (Obs.closed_iff_id hRc).2 ((Obs.closed_iff_id hRc).1 h1), l⟩
  · obtain ⟨o', h1, l⟩ := pat_rhs_sub_elim henv hΔ hEu hb hrules hmem hl hr hcov hlsP htype eH
      hlenH hkH hIrig hcf hcis hfam hC ihL.2 ihR.1 heq W' tv' o h
    exact ⟨o', (Obs.closed_iff_id hLc).2 ((Obs.closed_iff_id hLc).1 h1), l⟩

/-- Soundness of an eliminator rule whose right-hand side has no observations. -/
theorem sound_pat_elim_empty {df : VDefEq} {b : Name} {schema : InductiveSignature.CaseSchema}
    {owner : Fin schema.signature.families.size} {rules : List VDefEq}
    {lsP : List VLevel} {doms lead ms : List VExpr}
    {ctor : Name} {lsC : List VLevel} {fs : List Nat} {body : VExpr} {ls : List VLevel}
    (hEu : ∀ b s s', env.eliminators b s → env.eliminators b s' → s = s')
    (hb : env.eliminators b schema) (hrules : schema.genericEquations b owner = some rules)
    (hl : df.lhs = .wrapLams doms (.mkApps (.elim b owner.val lsP)
      (lead ++ [.mkApps (.const ctor lsC) (ms ++ fs.map .bvar)])))
    (hr : df.rhs = .wrapLams doms body)
    (hlsP : lsP.map (·.inst ls) = ls) (hlcl : df.lhs.ClosedN) (hrcl : df.rhs.ClosedN)
    (hcrig : env.Rigid ctor)
    (huniq : ∀ (df' : VDefEq) (doms' : List VExpr) (lsP' : List VLevel) (lead' : List VExpr)
      (ctor' : Name) (lsC' : List VLevel) (ms' : List VExpr) (fs' : List Nat) (body' : VExpr),
      df' ∈ rules →
      df'.lhs = .wrapLams doms' (.mkApps (.elim b owner.val lsP')
        (lead' ++ [.mkApps (.const ctor' lsC') (ms' ++ fs'.map .bvar)])) →
      df'.rhs = .wrapLams doms' body' →
      lead'.length = lead.length ∧ (ctor' = ctor → df' = df))
    {type : VExpr} {dsH : List VExpr} {RH : VExpr} {I : Name} {lsI : List VLevel}
    {iargs : List VExpr}
    (htype : schema.genericType owner = some type) (eH : type = .wrapForalls dsH RH)
    (hlenH : dsH.length = lead.length + 1)
    (hkH : dsH[lead.length]? = some (.mkApps (.const I lsI) iargs))
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
  obtain ⟨o', h1, -⟩ := pat_lhs_sub_elim henv hΔ hEu hb hrules hl hr hlsP hlcl hrcl hcrig
    huniq htype eH hlenH hkH hfam ihR.2 ihR.1 W.left tv o h
  exact absurd h1 (hE σ S W.left tv o')

end

end Model
end VEnv
end Lean4Lean
