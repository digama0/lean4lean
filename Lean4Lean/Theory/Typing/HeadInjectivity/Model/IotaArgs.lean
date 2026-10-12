import Lean4Lean.Theory.Typing.HeadInjectivity.Model.IotaRel

/-! # The arguments of an ι instance of an ordinary rule

`iotaArgRel_of`: for an instance `rec m1 (recArgs ++ [ctor lsC ctorArgs])` of a rule whose
reduct template binds the recursor's parameters, motives and minors (`np + nmm` binders, the
first `np + nmm` domains of the recursor's telescope) and the constructor's fields (the field
domains of the *normalized* constructor type, lifted over the motives and minors), the relation
`IotaArgRel` of the instance's arguments to the template holds at every typed valuation. The
argument valuations are compared along three telescopes:

* the installed constructor type `Dc`, along which the constructor arguments are typed
  (the redex's typing);
* the normalized constructor type `Dn`, soundly equal to the installed one
  (`tele_sound_dom`, `tele_sound_res`), whose field domains are the template's;
* the family's telescope `DI`, along which the recursor's major domain at the recursor
  arguments and the normalized constructor result at the constructor arguments are related
  (`rigid_spines_substEq`): the recursor's parameters equal the constructor's, and an index
  argument equals the field that the normalized index names. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

set_option maxHeartbeats 4000000 in
theorem iotaArgRel_of
    {Γ : List VExpr} {n ctor I : Name} {m1 lsC : List VLevel} {np nmm nind nf : Nat}
    {doms lead recArgs ctorArgs argsR : List VExpr} {A : VExpr}
    -- the recursor, at the instance's levels
    {ci : VConstant} {dsH : List VExpr} {RH : VExpr} {lsI : List VLevel} {iargs : List VExpr}
    (hci : env.constants n = some ci) (eH : ci.type.instL m1 = .wrapForalls dsH RH)
    (hlenH : dsH.length = np + nmm + nind + 1)
    (hkH : dsH[np + nmm + nind]? = some (.mkApps (.const I lsI) iargs))
    (hiargsl : iargs.length = np + nind)
    (hiargsP : ∀ i < np, iargs[i]? = some (.bvar (np + nmm + nind - 1 - i)))
    (hiargsI : ∀ j < nind, iargs[np + j]? = some (.bvar (nind - 1 - j)))
    -- the family's telescope
    {cI : VConstant} {DI : List VExpr} {RI : VExpr}
    (hcI : env.constants I = some cI)
    (hITW : Ob.Sub (Obs' .id .empty (cI.type.instL lsI)) (Obs' .id .empty (.wrapForalls DI RI)))
    (hIpi : PiSD env U Δ [] DI RI) (hDIl : np + nind ≤ DI.length) (hIrig : env.Rigid I)
    -- the installed constructor, at the instance's levels
    {cc : VConstant} {Dc cargs : List VExpr} {lsC' : List VLevel}
    (hcc : env.constants ctor = some cc)
    (eC : cc.type.instL lsC = .wrapForalls Dc (.mkApps (.const I lsC') cargs))
    (hDcl : Dc.length = np + nf)
    -- the normalized constructor type, at the instance's levels
    {Dn nargs : List VExpr} {lsN : List VLevel} {uN : VLevel}
    (hNcl : (VExpr.wrapForalls Dn (.mkApps (.const I lsN) nargs)).ClosedN)
    (hNH : HTS env U Δ [] (.wrapForalls Dn (.mkApps (.const I lsN) nargs)) (.sort uN))
    (hNSD : SD env U Δ [] (.wrapForalls Dn (.mkApps (.const I lsN) nargs))
      (.wrapForalls Dn (.mkApps (.const I lsN) nargs)) (.sort uN))
    {TN : VExpr}
    (hNS : SoundAt env U Δ [] (cc.type.instL lsC) (.wrapForalls Dn (.mkApps (.const I lsN) nargs))
      TN)
    (hDnl : Dn.length = np + nf) (hnargsl : nargs.length = np + nind)
    (hnargsP : ∀ i < np, nargs[i]? = some (.bvar (np + nf - 1 - i)))
    -- the template
    (hdl : doms.length = np + nmm + nf)
    (hDP : List.Forall₂ (· ≈ ·) lsC' lsI →
      ∀ i < np, ∃ d dn, dsH[i]? = some d ∧ Dn[i]? = some dn ∧ LvEq U d dn)
    (hDK : ∀ i < np + nmm, (doms.map (·.instL m1))[i]? = dsH[i]?)
    (hDF : List.Forall₂ (· ≈ ·) lsC' lsI →
      ∀ j < nf, ∃ d dn, (doms.map (·.instL m1))[np + nmm + j]? = some d ∧
      Dn[np + j]? = some dn ∧ LvEq U d (dn.liftN nmm j))
    (hleadK : ∀ i < np + nmm, lead[i]? = some (.bvar (np + nmm - 1 - i + nf)))
    (hleadI : ∀ j x, lead[np + nmm + j]? = some (.bvar x) → x < nf →
      nargs[np + j]? = some (.bvar x))
    (hleadl : lead.length = np + nmm + nind)
    (hdomsSD : DomsSD env U Δ [] (doms.map (·.instL m1)))
    -- the instance
    (hrA : recArgs.length = np + nmm + nind) (hcA : ctorArgs.length = np + nf)
    (hargs : argsR = recArgs.take (np + nmm) ++ ctorArgs.drop np)
    (ihe : HTS env U Δ Γ (.mkApps (.const n m1) (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs])) A)
    {σ : VExpr.Subst} {S : ObSets} (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) :
    IotaArgRel env U Δ Γ n ctor m1 lsC np nf doms lead recArgs ctorArgs argsR σ S ∧
      List.Forall₂ (· ≈ ·) lsC' lsI := by
  -- S1: the typings of the recursor's and the constructor's types
  obtain ⟨ci₁, -, hci₁, hlw, ⟨uT, hT, hTsd⟩, -, -, -, -, -⟩ :=
    ihe.spine henv hΔ rfl W tv ((recArgs ++ [VExpr.mkApps (.const ctor lsC) ctorArgs]).map fun _ => [])
      (forall₂_nil_lists _) [] nofun
  cases hci.symm.trans hci₁
  obtain ⟨Amaj, Bm, hfm, hmaj, -⟩ := HTS.spine_at _ rfl ihe recArgs.length (by simp)
  rw [List.getElem_append_right (by omega)] at hmaj
  simp only [Nat.sub_self, List.getElem_singleton] at hmaj
  obtain ⟨cc₁, -, hcc₁, hlwC, ⟨uC, hTc, hTcsd⟩, -, -, -, -, -⟩ :=
    hmaj.spine henv hΔ rfl W tv (ctorArgs.map fun _ => []) (forall₂_nil_lists _) [] nofun
  cases hcc.symm.trans hcc₁
  -- S2: the two family spines of the redex
  obtain ⟨uR, uI, hIR, hIC, WR, tvR, WC, tvC, subCR, subRC⟩ :=
    redex_major_sub henv hΔ hci eH hT hlenH hkH hcc eC hTc hrA (by omega) ihe W tv
  obtain ⟨-, hlsCI, -⟩ := rigid_spines_rel henv hΔ hIC WC tvC hIR WR tvR hIrig subCR subRC
  replace hDP := hDP hlsCI
  replace hDF := hDF hlsCI
  refine ⟨?_, hlsCI⟩
  -- S3: the telescopes of the installed and the normalized constructor types
  have hCcl : (VExpr.wrapForalls Dc (.mkApps (.const I lsC') cargs)).ClosedN := by
    rw [← eC]; exact (henv.ordered.closedC hcc).instL
  obtain ⟨hCRcl, hCDcl⟩ := closedN_wrapForalls hCcl
  obtain ⟨hNRcl, hNDcl⟩ := closedN_wrapForalls hNcl
  simp only [Nat.zero_add] at hCRcl hCDcl hNRcl hNDcl
  have hTc' : HTS env U Δ [] (.wrapForalls Dc (.mkApps (.const I lsC') cargs)) (.sort uC) := by
    rw [← eC]; exact hTc
  have hTcsd' : SD env U Δ [] (.wrapForalls Dc (.mkApps (.const I lsC') cargs))
      (.wrapForalls Dc (.mkApps (.const I lsC') cargs)) (.sort uC) := by
    rw [← eC]; exact hTcsd
  have hCpi := hTc'.piSD
  have hNpi := hNH.piSD
  obtain ⟨wC, hCbody⟩ := PiSD.body_sd hCpi hTcsd'
  obtain ⟨wN, hNbody⟩ := PiSD.body_sd hNpi hNSD
  rw [List.append_nil] at hCbody hNbody
  obtain ⟨uNb, hNbH⟩ := HTS.wrapForalls_body hNH
  rw [List.append_nil] at hNbH
  have hS : SoundAt env U Δ [] (.wrapForalls Dc (.mkApps (.const I lsC') cargs))
      (.wrapForalls Dn (.mkApps (.const I lsN) nargs)) TN := by
    rw [← eC]; exact hNS
  have hlenCN : Dc.length = Dn.length := by omega
  have hTWc : Ob.Sub (Obs' .id .empty (cc.type.instL lsC))
      (Obs' .id .empty (.wrapForalls Dc (.mkApps (.const I lsC') cargs))) := by
    rw [eC]; exact Ob.Sub.refl
  have hCpre := spine_tele_prefix henv hΔ hmaj W tv hcc hTWc hCpi (by omega)
  -- S5: the constructor arguments along the normalized telescope
  have hQ : ∀ m, m ≤ np + nf →
      Ctx.SubstEq env U Δ (VExpr.argSubst ((ctorArgs.take m).map (·.subst σ)))
        (VExpr.argSubst ((ctorArgs.take m).map (·.subst σ))) (Dn.take m).reverse ∧
      TV env U Δ (Dn.take m).reverse (VExpr.argSubst ((ctorArgs.take m).map (·.subst σ)))
        (argSets env U Δ σ S (ctorArgs.take m)) := by
    intro m
    induction m with
    | zero => intro _; simp; exact ⟨.nil, ⟨fun _ _ h => by simp [argSets] at h,
        fun _ _ h => by cases h⟩⟩
    | succ m ih =>
      intro hm
      obtain ⟨Wm, tvm⟩ := ih (by omega)
      obtain ⟨WCm, tvCm⟩ := hCpre m (by omega)
      obtain ⟨WCm1, tvCm1⟩ := hCpre (m + 1) (by omega)
      have hml : ((ctorArgs.take m).map (·.subst σ)).length = m := by simp; omega
      obtain ⟨eTy, sub12, -⟩ := tele_sound_dom henv hΔ hCDcl hNDcl hS hCpi hNpi hlenCN
        (as := (ctorArgs.take m).map (·.subst σ)) (by rw [hml]; omega)
        (by rw [hml]; exact WCm) (by rw [hml]; exact tvCm)
      simp only [hml] at eTy sub12
      obtain ⟨-, u, hDm⟩ := DomsSD.take_getElem hNpi.doms m (by omega)
      rw [List.append_nil] at hDm
      have htake : ctorArgs.take (m + 1) = ctorArgs.take m ++ [ctorArgs[m]'(by omega)] :=
        List.take_succ_eq_append_getElem (by omega)
      rw [htake, List.map_append, List.map_singleton] at WCm1 tvCm1 ⊢
      rw [argSets_snoc]
      rw [argSets_snoc] at tvCm1
      have hlC : ((ctorArgs.take m).map (·.subst σ)).length < Dc.length := by rw [hml]; omega
      have hlN : ((ctorArgs.take m).map (·.subst σ)).length < Dn.length := by rw [hml]; omega
      -- the new argument is typed at the normalized domain
      have hty : env.HasType U Δ ((ctorArgs[m]'(by omega)).subst σ)
          (Dn[m].subst (VExpr.argSubst ((ctorArgs.take m).map (·.subst σ)))) := by
        have h1 := (substEq_snoc_inv hml (by omega) WCm1).1.hasType.1
        have hm : TyCls env U Δ (Dc[m].subst (VExpr.argSubst ((ctorArgs.take m).map (·.subst σ))))
            (Dn[m].subst (VExpr.argSubst ((ctorArgs.take m).map (·.subst σ)))) := by
          rw [eTy]; exact TyCls.self
        exact TyCls.defeq_rev henv hΔ hm h1
      have hX := TV.snoc_inv hml (by omega) tvCm1
      refine ⟨substEq_argSubst_snoc hml (by omega) Wm hDm.1.defeq.hasType.1 hty,
        tv_argSubst_snoc hml (by omega) tvm
        (fun o h w hw => Obs.backed h tv.1 w hw) fun o ho => ?_⟩
      exact ((hX o ho).congr_cls (by rw [eTy])).mono_le sub12
  obtain ⟨WQ, tvQ⟩ := hQ (np + nf) (Nat.le_refl _)
  have hDnt : Dn.take (np + nf) = Dn := List.take_of_length_le (by omega)
  have hcat : ctorArgs.take (np + nf) = ctorArgs := List.take_of_length_le (by omega)
  rw [hDnt, hcat] at WQ tvQ
  -- S6: the results of the installed and the normalized constructor types
  have hCt : Dc.take ctorArgs.length = Dc := List.take_of_length_le (by omega)
  obtain ⟨WC', tvC'⟩ := hCpre ctorArgs.length (by omega)
  rw [List.take_length, hCt] at WC' tvC'
  obtain ⟨subCN, subNC⟩ := tele_sound_res henv hΔ hCDcl hCRcl hNRcl hS hCpi hNpi
    hCbody hNbody hlenCN (as := ctorArgs.map (·.subst σ)) (by simp; omega) WC' tvC'
  -- S7: the recursor's major domain and the normalized constructor result
  obtain ⟨hlenIN, hlsIN, WIN, hobsIN⟩ := rigid_spines_substEq henv hΔ hcI hITW hIpi hIR WR tvR
    hNbH WQ tvQ hIrig (subRC.trans subCN) (subNC.trans subCR) (by omega)
  -- the levels of the two family spines
  obtain ⟨cI₁, -, hcI₁, hlwI, -, -, -, -, -, -⟩ :=
    hIR.spine henv hΔ rfl WR tvR (iargs.map fun _ => []) (forall₂_nil_lists _) [] nofun
  obtain ⟨cI₂, -, hcI₂, hlwN, -, -, -, -, -, -⟩ :=
    hNbH.spine henv hΔ rfl WQ tvQ (nargs.map fun _ => []) (forall₂_nil_lists _) [] nofun
  cases hcI.symm.trans hcI₁
  cases hcI.symm.trans hcI₂
  have hITWN : Ob.Sub (Obs' .id .empty (cI.type.instL lsN))
      (Obs' .id .empty (.wrapForalls DI RI)) :=
    fun o h => hITW o (Obs.lvEq h (LvEq.instL _ hlwN hlwI (forall₂_equiv_symm hlsIN)))
  -- entries of the relation along the family's telescope
  have WIN' : Ctx.SubstEq env U Δ
      (VExpr.argSubst (iargs.map (·.subst (VExpr.argSubst (recArgs.map (·.subst σ))))))
      (VExpr.argSubst (nargs.map (·.subst (VExpr.argSubst (ctorArgs.map (·.subst σ))))))
      (DI.take (iargs.map (·.subst (VExpr.argSubst (recArgs.map (·.subst σ))))).length).reverse := by
    simpa using WIN
  have hWget : ∀ i (hi : i < np + nind),
      (∃ u, env.HasType U (DI.take i).reverse DI[i] (.sort u)) ∧
      env.IsDefEq U Δ ((iargs[i]'(by omega)).subst (VExpr.argSubst (recArgs.map (·.subst σ))))
        ((nargs[i]'(by omega)).subst (VExpr.argSubst (ctorArgs.map (·.subst σ))))
        (DI[i].subst (VExpr.argSubst
          ((iargs.take i).map (·.subst (VExpr.argSubst (recArgs.map (·.subst σ))))))) := by
    intro i hi
    have := substEq_argSubst_get (D := DI) (by simp; omega) (by simp; omega) WIN' (i := i)
      (by simp; omega)
    simpa [List.map_take] using this
  -- (C1) the family's domains at the two related prefixes
  have hC1 : ∀ i (hi : i < np + nind),
      TyCls env U Δ (DI[i].subst (VExpr.argSubst
          ((iargs.take i).map (·.subst (VExpr.argSubst (recArgs.map (·.subst σ))))))) =
        TyCls env U Δ (DI[i].subst (VExpr.argSubst
          ((nargs.take i).map (·.subst (VExpr.argSubst (ctorArgs.map (·.subst σ))))))) := by
    intro i hi
    obtain ⟨⟨u, hDI⟩, -⟩ := hWget i hi
    have Wi := substEq_take (Ds := DI) _ _ (by simp; omega) (by simp; omega) WIN' i (by simp; omega)
    simp only [List.map_take]
    exact TyCls.eq_of_defeq (by simpa using hDI.substDF henv Wi.wf hΔ Wi)
  -- (C2) the family's domain at a bare variable of the normalized result
  have hC2 : ∀ i y (hi : i < np + nind) (hyl : y < np + nf), nargs[i]? = some (.bvar y) →
      TyCls env U Δ (DI[i].subst (VExpr.argSubst
          ((nargs.take i).map (·.subst (VExpr.argSubst (ctorArgs.map (·.subst σ))))))) =
        TyCls env U Δ ((Dn[np + nf - 1 - y]'(by omega)).subst
          (VExpr.argSubst ((ctorArgs.take (np + nf - 1 - y)).map (·.subst σ)))) := by
    intro i y hi hyl hy
    have hy' : nargs[i]'(by omega) = .bvar y := (List.getElem?_eq_some_iff.1 hy).2
    have hL := lookup_append (Γ := []) Dn.reverse y (by simp; omega)
    rw [List.append_nil] at hL
    have e1 := bvar_arg_dom_cls henv hΔ hcI hITWN hIpi hNbH WQ tvQ (by omega) (by omega) hy' hL
    rw [e1, lift_subst_argSubst Dn (ctorArgs.map (·.subst σ)) (by omega) (by simp; omega)]
    simp [hDnl, List.map_take]
  -- (C3) the family's domain at a bare variable of the recursor's major domain
  have hC3 : ∀ i y (hi : i < np + nind) (hyl : y < np + nmm + nind), iargs[i]? = some (.bvar y) →
      TyCls env U Δ (DI[i].subst (VExpr.argSubst
          ((iargs.take i).map (·.subst (VExpr.argSubst (recArgs.map (·.subst σ))))))) =
        TyCls env U Δ ((dsH[np + nmm + nind - 1 - y]'(by omega)).subst
          (VExpr.argSubst ((recArgs.take (np + nmm + nind - 1 - y)).map (·.subst σ)))) := by
    intro i y hi hyl hy
    have hy' : iargs[i]'(by omega) = .bvar y := (List.getElem?_eq_some_iff.1 hy).2
    have hL := lookup_append (Γ := []) (dsH.take (np + nmm + nind)).reverse y (by simp; omega)
    rw [List.append_nil] at hL
    have e1 := bvar_arg_dom_cls henv hΔ hcI hITW hIpi hIR WR tvR (by omega) (by omega) hy' hL
    rw [e1, lift_subst_argSubst (dsH.take (np + nmm + nind)) (recArgs.map (·.subst σ))
      (by simp; omega) (by simp; omega)]
    simp only [List.length_take, Nat.min_eq_left (show np + nmm + nind ≤ dsH.length by omega),
      List.getElem_take, List.map_take]
  -- the observations of a bare variable at an argument valuation
  have obsBvar : ∀ (L : List VExpr) (y : Nat) (hy : y < L.length),
      Obs' (VExpr.argSubst (L.map (·.subst σ))) (argSets env U Δ σ S L) (.bvar y) =
        Obs' σ S (L[L.length - 1 - y]'(by omega)) := by
    intro L y hy
    funext o; apply propext
    rw [Obs.bvar_iff, argSets_lt hy]
  have substBvar : ∀ (L : List VExpr) (y : Nat) (hy : y < L.length),
      (VExpr.bvar y).subst (VExpr.argSubst (L.map (·.subst σ))) =
        (L[L.length - 1 - y]'(by omega)).subst σ := by
    intro L y hy
    show VExpr.argSubst (L.map (·.subst σ)) y = _
    exact argSubst_map_lt hy
  -- the recursor's and the constructor's parameters
  have hPobs : ∀ l (hl : l < np),
      Ob.Sub (Obs' σ S (ctorArgs[l]'(by omega))) (Obs' σ S (recArgs[l]'(by omega))) ∧
      Ob.Sub (Obs' σ S (recArgs[l]'(by omega))) (Obs' σ S (ctorArgs[l]'(by omega))) := by
    intro l hl
    obtain ⟨h1, h2⟩ := hobsIN l (by omega) (by omega)
    have ei : iargs[l]'(by omega) = .bvar (np + nmm + nind - 1 - l) :=
      (List.getElem?_eq_some_iff.1 (hiargsP l hl)).2
    have en : nargs[l]'(by omega) = .bvar (np + nf - 1 - l) :=
      (List.getElem?_eq_some_iff.1 (hnargsP l hl)).2
    rw [ei, obsBvar recArgs _ (by omega)] at h1 h2
    rw [en, obsBvar ctorArgs _ (by omega)] at h1 h2
    have e3 : recArgs.length - 1 - (np + nmm + nind - 1 - l) = l := by omega
    have e4 : ctorArgs.length - 1 - (np + nf - 1 - l) = l := by omega
    simp only [e3, e4] at h1 h2
    exact ⟨h2, h1⟩
  -- the recursor's telescope along the recursor arguments
  have hT' : HTS env U Δ [] (.wrapForalls dsH RH) (.sort uT) := by rw [← eH]; exact hT
  have hpiH : PiSD env U Δ [] dsH RH := hT'.piSD
  have hTWr : Ob.Sub (Obs' .id .empty (ci.type.instL m1)) (Obs' .id .empty (.wrapForalls dsH RH)) := by
    rw [eH]; exact Ob.Sub.refl
  have hRpre := spine_tele_prefix henv hΔ ihe W tv hci hTWr hpiH (by simp; omega)
  have hRpre' : ∀ m, m ≤ recArgs.length →
      Ctx.SubstEq env U Δ (VExpr.argSubst ((recArgs.take m).map (·.subst σ)))
        (VExpr.argSubst ((recArgs.take m).map (·.subst σ))) (dsH.take m).reverse ∧
      TV env U Δ (dsH.take m).reverse (VExpr.argSubst ((recArgs.take m).map (·.subst σ)))
        (argSets env U Δ σ S (recArgs.take m)) := by
    intro m hm
    have := hRpre m (by simp; omega)
    rwa [List.take_append_of_le_length hm] at this
  -- S8: the template's view of the constructor arguments: the recursor's parameters, then the
  -- constructor's fields, along the normalized telescope
  have hPXt : ∀ m, m ≤ np → (recArgs.take np ++ ctorArgs.drop np).take m = recArgs.take m := by
    intro m hm
    rw [List.take_append_of_le_length (by simp; omega), List.take_take, Nat.min_eq_left hm]
  have hPXget : ∀ m (hm : m < np + nf), (recArgs.take np ++ ctorArgs.drop np)[m]'(by simp; omega) =
      if h : m < np then recArgs[m]'(by omega) else ctorArgs[m]'(by omega) := by
    intro m hm
    split
    · rw [List.getElem_append_left (by simp; omega)]; simp
    · rw [List.getElem_append_right (by simp; omega)]; simp; congr 1; omega
  have hP : ∀ m, m ≤ np + nf →
      Ctx.SubstEq env U Δ (VExpr.argSubst ((ctorArgs.take m).map (·.subst σ)))
        (VExpr.argSubst (((recArgs.take np ++ ctorArgs.drop np).take m).map (·.subst σ)))
        (Dn.take m).reverse ∧
      TV env U Δ (Dn.take m).reverse
        (VExpr.argSubst (((recArgs.take np ++ ctorArgs.drop np).take m).map (·.subst σ)))
        (argSets env U Δ σ S ((recArgs.take np ++ ctorArgs.drop np).take m)) := by
    intro m
    induction m with
    | zero => intro _; simp; exact ⟨.nil, ⟨fun _ _ h => by simp [argSets] at h,
        fun _ _ h => by cases h⟩⟩
    | succ m ih =>
      intro hm
      obtain ⟨Wm, tvm⟩ := ih (by omega)
      obtain ⟨WQm, tvQm⟩ := hQ m (by omega)
      obtain ⟨WQm1, tvQm1⟩ := hQ (m + 1) hm
      obtain ⟨hdTake, u, hDm⟩ := DomsSD.take_getElem hNpi.doms m (by omega)
      rw [List.append_nil] at hDm
      have hml : ((ctorArgs.take m).map (·.subst σ)).length = m := by simp; omega
      have hpl : (((recArgs.take np ++ ctorArgs.drop np).take m).map (·.subst σ)).length = m := by
        simp; omega
      rw [List.take_succ_eq_append_getElem (l := ctorArgs) (by omega), List.map_append,
        List.map_singleton] at WQm1 tvQm1
      rw [argSets_snoc] at tvQm1
      have htyQ := (substEq_snoc_inv hml (by omega) WQm1).1
      have hXQ := TV.snoc_inv hml (by omega) tvQm1
      rw [List.take_succ_eq_append_getElem (l := recArgs.take np ++ ctorArgs.drop np) (by simp; omega),
        List.map_append, List.map_singleton, argSets_snoc, hPXget m (by omega),
        List.take_succ_eq_append_getElem (l := ctorArgs) (by omega), List.map_append,
        List.map_singleton]
      have eDm : TyCls env U Δ (Dn[m].subst (VExpr.argSubst ((ctorArgs.take m).map (·.subst σ)))) =
          TyCls env U Δ (Dn[m].subst (VExpr.argSubst
            (((recArgs.take np ++ ctorArgs.drop np).take m).map (·.subst σ)))) :=
        TyCls.eq_of_defeq (by simpa using hDm.1.defeq.hasType.1.substDF henv Wm.wf hΔ Wm)
      split
      · -- a parameter: the recursor's equals the constructor's
        rename_i hmp
        obtain ⟨-, hd⟩ := hWget m (by omega)
        have ei : iargs[m]'(by omega) = .bvar (np + nmm + nind - 1 - m) :=
          (List.getElem?_eq_some_iff.1 (hiargsP m hmp)).2
        have en : nargs[m]'(by omega) = .bvar (np + nf - 1 - m) :=
          (List.getElem?_eq_some_iff.1 (hnargsP m hmp)).2
        rw [ei, en, substBvar recArgs _ (by omega), substBvar ctorArgs _ (by omega)] at hd
        have e3 : recArgs.length - 1 - (np + nmm + nind - 1 - m) = m := by omega
        have e4 : ctorArgs.length - 1 - (np + nf - 1 - m) = m := by omega
        simp only [e3, e4] at hd
        have hmem : TyCls env U Δ (DI[m].subst (VExpr.argSubst
            ((iargs.take m).map (·.subst (VExpr.argSubst (recArgs.map (·.subst σ)))))))
            (Dn[m].subst (VExpr.argSubst ((ctorArgs.take m).map (·.subst σ)))) := by
          rw [hC1 m (by omega), hC2 m (np + nf - 1 - m) (by omega) (by omega) (hnargsP m hmp)]
          simp only [show np + nf - 1 - (np + nf - 1 - m) = m by omega]
          exact TyCls.self
        have hd' := (TyCls.defeq_rev henv hΔ hmem hd).symm
        rw [hPXt m (by omega)] at Wm tvm ⊢
        refine ⟨substEq_argSubst_snoc hml (by omega) Wm hDm.1.defeq.hasType.1 hd',
          tv_argSubst_snoc (by simp; omega) (by omega) tvm
            (fun o h w hw => Obs.backed h tv.1 w hw) fun o ho => ?_⟩
        obtain ⟨-, tvRm1⟩ := hRpre' (m + 1) (by omega)
        rw [List.take_succ_eq_append_getElem (l := recArgs) (by omega), List.map_append,
          List.map_singleton, argSets_snoc] at tvRm1
        have hXR := TV.snoc_inv (by simp; omega) (by omega) tvRm1 o ho
        obtain ⟨d, dn, hd1, hd2, hlv⟩ := hDP m hmp
        have e5 : dsH[m]'(by omega) = d := (List.getElem?_eq_some_iff.1 hd1).2
        have e6 : Dn[m]'(by omega) = dn := (List.getElem?_eq_some_iff.1 hd2).2
        rw [e5] at hXR; rw [e6]
        have hlv' := hlv.subst (VExpr.argSubst ((recArgs.take m).map (·.subst σ)))
        refine (hXR.congr_cls (by rw [TyCls.eq_of_lvEq hlv'])).mono_le ?_
        exact Ob.Sub.of_imp fun o h => Obs.lvEq h hlv
      · rename_i hmp
        refine ⟨substEq_argSubst_snoc hml (by omega) Wm hDm.1.defeq.hasType.1 htyQ,
          tv_argSubst_snoc hpl (by omega) tvm
            (fun o h w hw => Obs.backed h tv.1 w hw) fun o ho => ?_⟩
        have hctx : CtxSD env U Δ [] (Dn.take m).reverse := by
          simpa using DomsSD.ctxSD (L := []) (Γ := []) (by simpa using hdTake) .nil
        refine ((hXQ o ho).congr_cls (by rw [eDm])).mono_le ?_
        refine SoundAt.sub_sets henv hΔ hDm.2 hctx Wm (fun x hx => ?_) tvQm tvm ?_
        · simp only [List.length_reverse, List.length_take] at hx
          rw [VExpr.argSubst_ge _ (by simp; omega), VExpr.argSubst_ge _ (by simp; omega)]
          simp; omega
        · intro i o' ho'
          have hl1 : min m ctorArgs.length = m := by omega
          have hl2 : min m (recArgs.take np ++ ctorArgs.drop np).length = m := by simp; omega
          have hi : i < m := by
            by_contra h
            simp [argSets, List.length_take, hl1, h] at ho'
          rw [argSets_lt (by simp; omega)] at ho'
          rw [argSets_lt (by simp; omega)]
          simp only [List.getElem_take, List.length_take, hl1, hl2] at ho' ⊢
          rw [hPXget _ (by omega)]
          split
          · rename_i hlt
            exact (hPobs _ hlt).1 o' ho'
          · exact ⟨o', ho', .refl⟩
  -- S9: the template's binders at the argument valuation
  -- the domain classes of the two constructor telescopes, and of the normalized one at the
  -- two prefixes
  have hTS : ∀ m (hm : m < np + nf),
      TyCls env U Δ ((Dc[m]'(by omega)).subst (VExpr.argSubst ((ctorArgs.take m).map (·.subst σ)))) =
        TyCls env U Δ ((Dn[m]'(by omega)).subst
          (VExpr.argSubst ((ctorArgs.take m).map (·.subst σ)))) := by
    intro m hm
    obtain ⟨WCm, tvCm⟩ := hCpre m (by omega)
    have hml : ((ctorArgs.take m).map (·.subst σ)).length = m := by simp; omega
    obtain ⟨eTy, -, -⟩ := tele_sound_dom henv hΔ hCDcl hNDcl hS hCpi hNpi hlenCN
      (as := (ctorArgs.take m).map (·.subst σ)) (by rw [hml]; omega)
      (by rw [hml]; exact WCm) (by rw [hml]; exact tvCm)
    simpa only [hml] using eTy
  have hPQ : ∀ m (hm : m < np + nf),
      TyCls env U Δ ((Dn[m]'(by omega)).subst
          (VExpr.argSubst ((ctorArgs.take m).map (·.subst σ)))) =
        TyCls env U Δ ((Dn[m]'(by omega)).subst (VExpr.argSubst
          (((recArgs.take np ++ ctorArgs.drop np).take m).map (·.subst σ)))) := by
    intro m hm
    obtain ⟨Wm, -⟩ := hP m (by omega)
    obtain ⟨-, u, hDm⟩ := DomsSD.take_getElem hNpi.doms m (by omega)
    rw [List.append_nil] at hDm
    exact TyCls.eq_of_defeq (by simpa using hDm.1.defeq.hasType.1.substDF henv Wm.wf hΔ Wm)
  -- the splits of the reduct's arguments
  have hArgsTake : ∀ j, j ≤ nf → argsR.take (np + nmm + j) =
      recArgs.take np ++ (recArgs.take (np + nmm)).drop np ++ (ctorArgs.drop np).take j := by
    intro j hj
    subst hargs
    rw [List.take_append, List.take_of_length_le (l := recArgs.take (np + nmm)) (by simp; omega)]
    have hl : (recArgs.take (np + nmm)).length = np + nmm := by simp; omega
    rw [hl, show np + nmm + j - (np + nmm) = j by omega]
    conv => lhs; rw [← List.take_append_drop np (recArgs.take (np + nmm))]
    rw [List.take_take, Nat.min_eq_left (by omega)]
  have hPXTake : ∀ j, j ≤ nf → (recArgs.take np ++ ctorArgs.drop np).take (np + j) =
      recArgs.take np ++ (ctorArgs.drop np).take j := by
    intro j hj
    rw [List.take_append, List.take_of_length_le (by simp; omega)]
    simp; omega
  -- (F1) the template's field binders are the normalized field domains at the template's view
  have hF1 : ∀ j (hj : j < nf),
      TyCls env U Δ ((binderTy doms m1 (nf - 1 - j)).subst
          (VExpr.argSubst (argsR.map (·.subst σ)))) =
        TyCls env U Δ ((Dn[np + j]'(by omega)).subst (VExpr.argSubst
          (((recArgs.take np ++ ctorArgs.drop np).take (np + j)).map (·.subst σ)))) ∧
      ∃ d, (doms.map (·.instL m1))[np + nmm + j]? = some d ∧ ∀ o,
        Obs' (VExpr.argSubst ((argsR.take (np + nmm + j)).map (·.subst σ)))
            (argSets env U Δ σ S (argsR.take (np + nmm + j))) d o ↔
          Obs' (VExpr.argSubst (((recArgs.take np ++ ctorArgs.drop np).take (np + j)).map
              (·.subst σ)))
            (argSets env U Δ σ S ((recArgs.take np ++ ctorArgs.drop np).take (np + j)))
            (Dn[np + j]'(by omega)) o := by
    intro j hj
    obtain ⟨d, dn, hd, hdn, hlv⟩ := hDF j hj
    have edn : Dn[np + j]'(by omega) = dn := (List.getElem?_eq_some_iff.1 hdn).2
    have hal : argsR.length = doms.length := by subst hargs; simp; omega
    have hmidl : ((recArgs.take (np + nmm)).drop np).length = nmm := by simp; omega
    have hpostl : ((ctorArgs.drop np).take j).length = j := by simp; omega
    have hdncl : dn.ClosedN (np + j) := by
      have := hNDcl (np + j) (by omega); rwa [edn] at this
    -- the lift skips the motives and minors
    have key : ∀ (f : VExpr → VExpr),
        (dn.liftN nmm j).subst (VExpr.argSubst ((argsR.take (np + nmm + j)).map f)) =
          dn.subst (VExpr.argSubst (((recArgs.take np ++ ctorArgs.drop np).take (np + j)).map f)) := by
      intro f
      rw [hArgsTake j (by omega), hPXTake j (by omega), List.map_append, List.map_append,
        List.map_append]
      have := argSubst_liftN_mid dn ((recArgs.take np).map f)
        (((recArgs.take (np + nmm)).drop np).map f) (((ctorArgs.drop np).take j).map f)
      simp only [List.length_map, hmidl, hpostl] at this
      exact this
    rw [edn]
    refine ⟨?_, d, hd, fun o => ?_⟩
    · rw [binderTy_subst_argSubst (by omega) (by simp [hal])]
      simp only [show doms.length - 1 - (nf - 1 - j) = np + nmm + j by omega]
      have hd' : (doms.map (·.instL m1))[np + nmm + j]'(by simp; omega) = d :=
        (List.getElem?_eq_some_iff.1 hd).2
      rw [hd', ← List.map_take, ← key (·.subst σ)]
      exact TyCls.eq_of_lvEq (hlv.subst _)
    · have hcl1 : (dn.liftN nmm j).ClosedN (argsR.take (np + nmm + j)).length := by
        have := hdncl.liftN (n := nmm) (j := j)
        have hlen : (argsR.take (np + nmm + j)).length = np + nmm + j := by
          simp; omega
        rw [hlen]; simpa [Nat.add_right_comm] using this
      have hcl2 : dn.ClosedN ((recArgs.take np ++ ctorArgs.drop np).take (np + j)).length := by
        have hlen : ((recArgs.take np ++ ctorArgs.drop np).take (np + j)).length = np + j := by
          simp; omega
        rw [hlen]; exact hdncl
      have key0 := key (fun e => e)
      simp only [List.map_id'] at key0
      constructor
      · intro h
        have h1 := (Obs.subst_argSubst hcl1).2 (Obs.lvEq h hlv)
        rw [key0] at h1
        exact (Obs.subst_argSubst hcl2).1 h1
      · intro h
        have h1 := (Obs.subst_argSubst hcl2).2 h
        rw [← key0] at h1
        exact Obs.lvEq ((Obs.subst_argSubst hcl1).1 h1) hlv.symm
  -- the template's domains at the recursor's prefix
  have hDtake : ∀ m, m ≤ np + nmm → (doms.map (·.instL m1)).take m = dsH.take m := by
    intro m hm
    apply List.ext_getElem?
    intro i
    simp only [List.getElem?_take]
    split
    · exact hDK i (by omega)
    · rfl
  have hArgsTakeK : ∀ m, m ≤ np + nmm → argsR.take m = recArgs.take m := by
    intro m hm
    subst hargs
    rw [List.take_append_of_le_length (by simp; omega), List.take_take, Nat.min_eq_left hm]
  -- the typed argument valuation along the template
  have hV : ∀ j, j ≤ nf →
      Ctx.SubstEq env U Δ (VExpr.argSubst ((argsR.take (np + nmm + j)).map (·.subst σ)))
        (VExpr.argSubst ((argsR.take (np + nmm + j)).map (·.subst σ)))
        ((doms.map (·.instL m1)).take (np + nmm + j)).reverse ∧
      TV env U Δ ((doms.map (·.instL m1)).take (np + nmm + j)).reverse
        (VExpr.argSubst ((argsR.take (np + nmm + j)).map (·.subst σ)))
        (argSets env U Δ σ S (argsR.take (np + nmm + j))) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [Nat.add_zero, hDtake _ (Nat.le_refl _), hArgsTakeK _ (Nat.le_refl _)]
      exact hRpre' _ (by omega)
    | succ j ih =>
      intro hj
      obtain ⟨Wj, tvj⟩ := ih (by omega)
      obtain ⟨hF1t, d, hd, hF1o⟩ := hF1 j (by omega)
      have hal : argsR.length = doms.length := by subst hargs; simp; omega
      have hjl : ((argsR.take (np + nmm + j)).map (·.subst σ)).length = np + nmm + j := by
        simp; omega
      have hd' : (doms.map (·.instL m1))[np + nmm + j]'(by simp; omega) = d :=
        (List.getElem?_eq_some_iff.1 hd).2
      -- the class of the template's domain
      have eD : TyCls env U Δ (d.subst (VExpr.argSubst ((argsR.take (np + nmm + j)).map (·.subst σ)))) =
          TyCls env U Δ ((Dn[np + j]'(by omega)).subst (VExpr.argSubst
            (((recArgs.take np ++ ctorArgs.drop np).take (np + j)).map (·.subst σ)))) := by
        rw [← hF1t, binderTy_subst_argSubst (by omega) (by simp [hal])]
        simp only [show doms.length - 1 - (nf - 1 - j) = np + nmm + j by omega, hd', List.map_take]
      -- the new argument
      have hget : argsR[np + nmm + j]'(by omega) = ctorArgs[np + j]'(by omega) := by
        subst hargs
        rw [List.getElem_append_right (by simp; omega)]
        simp; congr 1; omega
      rw [show np + nmm + (j + 1) = np + nmm + j + 1 by omega,
        List.take_succ_eq_append_getElem (l := argsR) (by omega), List.map_append,
        List.map_singleton, argSets_snoc, hget]
      obtain ⟨-, tvQ1⟩ := hQ (np + j + 1) (by omega)
      obtain ⟨WQ1, -⟩ := hQ (np + j + 1) (by omega)
      rw [List.take_succ_eq_append_getElem (l := ctorArgs) (by omega), List.map_append,
        List.map_singleton] at WQ1 tvQ1
      rw [argSets_snoc] at tvQ1
      have hqml : ((ctorArgs.take (np + j)).map (·.subst σ)).length = np + j := by simp; omega
      have htyQ := (substEq_snoc_inv hqml (by omega) WQ1).1.hasType.1
      have hty : env.HasType U Δ ((ctorArgs[np + j]'(by omega)).subst σ)
          (d.subst (VExpr.argSubst ((argsR.take (np + nmm + j)).map (·.subst σ)))) := by
        have hm : TyCls env U Δ ((Dn[np + j]'(by omega)).subst
            (VExpr.argSubst ((ctorArgs.take (np + j)).map (·.subst σ))))
            (d.subst (VExpr.argSubst ((argsR.take (np + nmm + j)).map (·.subst σ)))) := by
          rw [hPQ (np + j) (by omega), ← eD]; exact TyCls.self
        exact TyCls.defeq_rev henv hΔ hm htyQ
      obtain ⟨-, w, hDd⟩ := DomsSD.take_getElem hdomsSD (np + nmm + j) (by simp; omega)
      rw [List.append_nil] at hDd
      simp only [hd'] at hDd
      obtain ⟨-, tvP1⟩ := hP (np + j + 1) (by omega)
      rw [List.take_succ_eq_append_getElem (l := recArgs.take np ++ ctorArgs.drop np)
        (by simp; omega), List.map_append, List.map_singleton, argSets_snoc,
        hPXget _ (by omega), dif_neg (by omega)] at tvP1
      have hpml : (((recArgs.take np ++ ctorArgs.drop np).take (np + j)).map (·.subst σ)).length =
          np + j := by simp; omega
      have hXP := TV.snoc_inv hpml (by omega) tvP1
      have hDdl : (doms.map (·.instL m1))[np + nmm + j]'(by simp; omega) = d := hd'
      refine ⟨?_, ?_⟩
      · have := substEq_argSubst_snoc (D := doms.map (·.instL m1)) hjl (by simp; omega) Wj
          (by rw [hDdl]; exact hDd.1.defeq.hasType.1) (by rw [hDdl]; exact hty)
        exact this
      · refine tv_argSubst_snoc hjl (by simp; omega) tvj
          (fun o h w hw => Obs.backed h tv.1 w hw) fun o ho => ?_
        rw [hDdl]
        refine ((hXP o ho).congr_cls (by rw [eD])).mono_le ?_
        exact Ob.Sub.of_imp fun o h => (hF1o o).2 h
  obtain ⟨Wfull, tvfull⟩ := hV nf (Nat.le_refl _)
  have hal : argsR.length = doms.length := by subst hargs; simp; omega
  have hargsFull : argsR.take (np + nmm + nf) = argsR := List.take_of_length_le (by omega)
  have hDfull : (doms.map (·.instL m1)).take (np + nmm + nf) = doms.map (·.instL m1) :=
    List.take_of_length_le (by simp; omega)
  rw [hargsFull, hDfull] at Wfull tvfull
  have hkr : np + nmm ≤ recArgs.length := by omega
  refine ⟨Wfull, tvfull, fun i x hi hx hfirst => ?_, fun j hj Aq Bq hB => ?_⟩
  · have hil : i < np + nmm + nind := by
      have := (List.getElem?_eq_some_iff.1 hi).1; omega
    by_cases hik : i < np + nmm
    · -- a parameter, motive or minor
      have hxi : x = np + nmm - 1 - i + nf := by
        rw [hleadK i hik] at hi; injection hi with hi; injection hi with hi; omega
      subst hxi
      have eBT : (binderTy doms m1 (np + nmm - 1 - i + nf)).subst
          (VExpr.argSubst (argsR.map (·.subst σ))) =
          (dsH[i]'(by omega)).subst (VExpr.argSubst ((recArgs.take i).map (·.subst σ))) := by
        rw [binderTy_subst_argSubst (by omega) (by simp [hal])]
        simp only [show doms.length - 1 - (np + nmm - 1 - i + nf) = i by omega, ← List.map_take,
          hArgsTakeK i (by omega)]
        have := hDK i hik
        rw [List.getElem?_eq_getElem (by simp; omega), List.getElem?_eq_getElem (by omega)] at this
        rw [Option.some.inj this]
      have hvx : VExpr.argSubst (argsR.map (·.subst σ)) (np + nmm - 1 - i + nf) =
          (recArgs[i]'(by omega)).subst σ := by
        rw [argSubst_map_lt (by omega)]
        subst hargs
        rw [List.getElem_append_left (by simp; omega)]
        simp only [List.getElem_take]; congr 2; simp; omega
      have hvS : argSets env U Δ σ S argsR (np + nmm - 1 - i + nf) = Obs' σ S (recArgs[i]'(by omega)) := by
        rw [argSets_lt (by omega)]
        subst hargs
        rw [List.getElem_append_left (by simp; omega)]
        simp only [List.getElem_take]; congr 2; simp; omega
      obtain ⟨WRi, -⟩ := hRpre' (i + 1) (by omega)
      rw [List.take_succ_eq_append_getElem (by omega), List.map_append, List.map_singleton] at WRi
      have hrml : ((recArgs.take i).map (·.subst σ)).length = i := by simp; omega
      have hty := (substEq_snoc_inv hrml (by omega) WRi).1
      refine ⟨recArgs[i]'(by omega), List.getElem?_eq_getElem _, ⟨_, by rw [eBT]; exact TyCls.self,
        by rw [hvx]; exact hty.hasType.1⟩, fun Aq Bq hB => ?_, by rw [hvS]; exact Ob.Sub.refl,
        by rw [hvS]; exact Ob.Sub.refl⟩
      have e := spine_dom_cls henv hΔ hci hTWr hpiH (pre := recArgs.take i) (by simp; omega) W tv hB
      simp only [List.length_take, Nat.min_eq_left (show i ≤ recArgs.length by omega)] at e
      rw [eBT, e]
    · -- an index: a field named by the constructor's index
      obtain ⟨j, rfl⟩ : ∃ j, i = np + nmm + j := ⟨i - (np + nmm), by omega⟩
      have hjn : j < nind := by omega
      have hxnf : x < nf := by
        by_contra hxnf
        have hi' := hleadK (np + nmm - 1 - (x - nf)) (by omega)
        rw [show np + nmm - 1 - (np + nmm - 1 - (x - nf)) + nf = x by omega] at hi'
        exact hfirst _ (by omega) hi'
      have hn := hleadI j x hi hxnf
      obtain ⟨j', hj', rfl⟩ : ∃ j', j' < nf ∧ x = nf - 1 - j' := ⟨nf - 1 - x, by omega, by omega⟩
      obtain ⟨-, hd⟩ := hWget (np + j) (by omega)
      have ei : iargs[np + j]'(by omega) = .bvar (nind - 1 - j) :=
        (List.getElem?_eq_some_iff.1 (hiargsI j hjn)).2
      have en : nargs[np + j]'(by omega) = .bvar (nf - 1 - j') :=
        (List.getElem?_eq_some_iff.1 hn).2
      rw [ei, en, substBvar recArgs _ (by omega), substBvar ctorArgs _ (by omega)] at hd
      have e3 : recArgs.length - 1 - (nind - 1 - j) = np + nmm + j := by omega
      have e4 : ctorArgs.length - 1 - (nf - 1 - j') = np + j' := by omega
      simp only [e3, e4] at hd
      have hvx : VExpr.argSubst (argsR.map (·.subst σ)) (nf - 1 - j') =
          (ctorArgs[np + j']'(by omega)).subst σ := argSubst_field hargs hkr hcA hj'
      have hvS : argSets env U Δ σ S argsR (nf - 1 - j') = Obs' σ S (ctorArgs[np + j']'(by omega)) :=
        argSets_field hargs hkr hcA hj'
      -- the type classes along the chain
      have eChain : TyCls env U Δ ((binderTy doms m1 (nf - 1 - j')).subst
          (VExpr.argSubst (argsR.map (·.subst σ)))) =
          TyCls env U Δ (DI[np + j].subst (VExpr.argSubst
            ((iargs.take (np + j)).map (·.subst (VExpr.argSubst (recArgs.map (·.subst σ))))))) := by
        rw [(hF1 j' hj').1, ← hPQ (np + j') (by omega), hC1 (np + j) (by omega),
          hC2 (np + j) (nf - 1 - j') (by omega) (by omega) hn]
        simp only [show np + nf - 1 - (nf - 1 - j') = np + j' by omega]
      obtain ⟨hob1, hob2⟩ := hobsIN (np + j) (by omega) (by omega)
      rw [ei, obsBvar recArgs _ (by omega), en, obsBvar ctorArgs _ (by omega)] at hob1 hob2
      simp only [e3, e4] at hob1 hob2
      refine ⟨recArgs[np + nmm + j]'(by omega), List.getElem?_eq_getElem _,
        ⟨_, by rw [eChain]; exact TyCls.self, by rw [hvx]; exact hd⟩, fun Aq Bq hB => ?_,
        by rw [hvS]; exact hob1, by rw [hvS]; exact hob2⟩
      have e := spine_dom_cls henv hΔ hci hTWr hpiH (pre := recArgs.take (np + nmm + j))
        (by simp; omega) W tv hB
      simp only [List.length_take, Nat.min_eq_left (show np + nmm + j ≤ recArgs.length by omega)]
        at e
      rw [eChain, e, hC3 (np + j) (nind - 1 - j) (by omega) (by omega) (hiargsI j hjn)]
      simp only [show np + nmm + nind - 1 - (nind - 1 - j) = np + nmm + j by omega]
  · -- the constructor's field domains
    have e := spine_dom_cls henv hΔ hcc hTWc hCpi (pre := ctorArgs.take (np + j))
      (by simp; omega) W tv hB
    simp only [List.length_take, Nat.min_eq_left (show np + j ≤ ctorArgs.length by omega)] at e
    rw [e, hTS (np + j) (by omega), hPQ (np + j) (by omega), (hF1 j hj).1]

end

end Model
end VEnv
end Lean4Lean
