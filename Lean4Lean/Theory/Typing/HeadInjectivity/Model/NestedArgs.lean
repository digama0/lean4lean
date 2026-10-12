import Lean4Lean.Theory.Typing.HeadInjectivity.Model.IotaArgs

/-! # The arguments of an instance of a container rule

`iotaArgRel_container`: the relation `IotaArgRel` of the arguments of an instance
`rec m1 (recArgs ++ [c lsC ctorArgs])` of an ι rule of a nested block whose major family is a
container family `I` (the rule of an auxiliary recursor, firing on a container constructor `c`)
to the rule's reduct template. Unlike the rules of a block's own families (`iotaArgRel_of`), the
recursor's parameters `P` (`np` of them) are not the constructor's (`cnp` of them): the
recursor's major domain is `I (Ds ++ indices)`, the container family at the specialization
arguments `Ds` (terms over `P`), and the constructor's parameters `Q` are equal to `Ds[P]` only
semantically, by injectivity of `I` (`rigid_spines_substEq`). The argument valuations are
compared along four telescopes:

* the installed constructor type `Dc`, along which `Q ++ fields` are typed (the redex's typing),
  and along which `Ds[P] ++ fields` are typed at the same domain classes (`Q ≡ Ds[P]`);
* the specialized constructor type `B = Π params, (Π fields, I ..)[Ds]`, whose field domains at
  `P ++ fields` are those of `Dc` at `Ds[P] ++ fields` up to level variants;
* the normalized constructor type `Dn` (the restored auxiliary constructor's type), soundly equal
  to `B` (`tele_sound_dom`, `tele_sound_res`), whose field domains are the template's;
* the family's telescope `DI`, along which the recursor's major domain at the recursor arguments
  and the normalized constructor result at `P ++ fields` are related: an index argument equals
  the field that the normalized index names. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ


theorem subst_argSubst_comp {e : VExpr} {ps : List VExpr} (he : e.ClosedN ps.length)
    (σ : VExpr.Subst) :
    (e.subst (VExpr.argSubst ps)).subst σ = e.subst (VExpr.argSubst (ps.map (·.subst σ))) := by
  rw [VExpr.subst_subst]
  apply VExpr.subst_congr_closedN he
  intro i hi
  show (VExpr.argSubst ps i).subst σ = _
  rw [VExpr.argSubst_lt _ hi, VExpr.argSubst_lt _ (by simpa using hi)]
  simp

theorem liftN_subst_argSubst_append (e : VExpr) (pre mid : List VExpr) :
    (e.liftN mid.length).subst (VExpr.argSubst (pre ++ mid)) = e.subst (VExpr.argSubst pre) := by
  have := argSubst_liftN_mid e pre mid []
  simpa using this

section
variable (henv : env.OrderedStrong) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

set_option maxHeartbeats 16000000 in
theorem iotaArgRel_container
    {Γ : List VExpr} {n ctor I : Name} {m1 lsC : List VLevel} {np nmm nind cnp nf : Nat}
    {doms lead recArgs ctorArgs argsR : List VExpr} {A : VExpr}
    -- the recursor, at the instance's levels
    {ci : VConstant} {dsH : List VExpr} {RH : VExpr} {lsI : List VLevel} {iargs Ds : List VExpr}
    (hci : env.constants n = some ci) (eH : ci.type.instL m1 = .wrapForalls dsH RH)
    (hlenH : dsH.length = np + nmm + nind + 1)
    (hkH : dsH[np + nmm + nind]? = some (.mkApps (.const I lsI) iargs))
    (hDsl : Ds.length = cnp) (hDscl : ∀ d ∈ Ds, d.ClosedN np)
    (hiargsl : iargs.length = cnp + nind)
    (hiargsP : ∀ i (hi : i < cnp), iargs[i]? = some ((Ds[i]'(by omega)).liftN (nmm + nind)))
    (hiargsI : ∀ j < nind, iargs[cnp + j]? = some (.bvar (nind - 1 - j)))
    -- the family's telescope
    {cI : VConstant} {DI : List VExpr} {RI : VExpr}
    (hcI : env.constants I = some cI)
    (hITW : Ob.Sub (Obs' .id .empty (cI.type.instL lsI)) (Obs' .id .empty (.wrapForalls DI RI)))
    (hIpi : PiSD env U Δ [] DI RI) (hDIl : cnp + nind ≤ DI.length) (hIrig : env.Rigid I)
    -- the installed constructor, at the instance's levels
    {cc : VConstant} {Dc cargs : List VExpr} {lsC' : List VLevel}
    (hcc : env.constants ctor = some cc)
    (eC : cc.type.instL lsC = .wrapForalls Dc (.mkApps (.const I lsC') cargs))
    (hDcl : Dc.length = cnp + nf)
    (hcargsP : ∀ i < cnp, cargs[i]? = some (.bvar (cnp + nf - 1 - i)))
    -- the specialized constructor type
    {DB : List VExpr} {RB : VExpr} {uB : VLevel}
    (hBcl : (VExpr.wrapForalls DB RB).ClosedN)
    (hBH : HTS env U Δ [] (.wrapForalls DB RB) (.sort uB))
    (hBSD : SD env U Δ [] (.wrapForalls DB RB) (.wrapForalls DB RB) (.sort uB))
    (hDBl : DB.length = np + nf)
    (hDBf : List.Forall₂ (· ≈ ·) lsC' lsI → ∀ j (hj : j < nf) (ps fs : List VExpr),
      ps.length = np → fs.length = j →
      LvEq U ((DB[np + j]'(by omega)).subst (VExpr.argSubst (ps ++ fs)))
        ((Dc[cnp + j]'(by omega)).subst
          (VExpr.argSubst (Ds.map (·.subst (VExpr.argSubst ps)) ++ fs))))
    (hRB : List.Forall₂ (· ≈ ·) lsC' lsI → ∀ (ps fs : List VExpr),
      ps.length = np → fs.length = nf →
      LvEq U (RB.subst (VExpr.argSubst (ps ++ fs)))
        ((VExpr.mkApps (.const I lsC') cargs).subst
          (VExpr.argSubst (Ds.map (·.subst (VExpr.argSubst ps)) ++ fs))))
    -- the normalized constructor type
    {Dn nargs : List VExpr} {lsN : List VLevel} {uN : VLevel}
    (hNcl : (VExpr.wrapForalls Dn (.mkApps (.const I lsN) nargs)).ClosedN)
    (hNH : HTS env U Δ [] (.wrapForalls Dn (.mkApps (.const I lsN) nargs)) (.sort uN))
    (hNSD : SD env U Δ [] (.wrapForalls Dn (.mkApps (.const I lsN) nargs))
      (.wrapForalls Dn (.mkApps (.const I lsN) nargs)) (.sort uN))
    {TN : VExpr}
    (hNS : SoundAt env U Δ [] (.wrapForalls DB RB)
      (.wrapForalls Dn (.mkApps (.const I lsN) nargs)) TN)
    (hDnl : Dn.length = np + nf) (hnargsl : nargs.length = cnp + nind)
    (hnargsP : ∀ i (hi : i < cnp), nargs[i]? = some ((Ds[i]'(by omega)).liftN nf))
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
      nargs[cnp + j]? = some (.bvar x))
    (hleadl : lead.length = np + nmm + nind)
    (hdomsSD : DomsSD env U Δ [] (doms.map (·.instL m1)))
    -- the instance
    (hrA : recArgs.length = np + nmm + nind) (hcA : ctorArgs.length = cnp + nf)
    (hargs : argsR = recArgs.take (np + nmm) ++ ctorArgs.drop cnp)
    (ihe : HTS env U Δ Γ (.mkApps (.const n m1) (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs])) A)
    {σ : VExpr.Subst} {S : ObSets} (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) :
    IotaArgRel env U Δ Γ n ctor m1 lsC cnp nf doms lead recArgs ctorArgs argsR σ S ∧
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
  replace hDBf := hDBf hlsCI
  replace hRB := hRB hlsCI
  refine ⟨?_, hlsCI⟩
  -- S3: the installed constructor's telescope
  have hCcl : (VExpr.wrapForalls Dc (.mkApps (.const I lsC') cargs)).ClosedN := by
    rw [← eC]; exact (henv.ordered.closedC hcc).instL
  obtain ⟨hCRcl, hCDcl⟩ := closedN_wrapForalls hCcl
  obtain ⟨hNRcl, hNDcl⟩ := closedN_wrapForalls hNcl
  obtain ⟨hBRcl, hBDcl⟩ := closedN_wrapForalls hBcl
  simp only [Nat.zero_add] at hCRcl hCDcl hNRcl hNDcl hBRcl hBDcl
  have hTc' : HTS env U Δ [] (.wrapForalls Dc (.mkApps (.const I lsC') cargs)) (.sort uC) := by
    rw [← eC]; exact hTc
  have hTcsd' : SD env U Δ [] (.wrapForalls Dc (.mkApps (.const I lsC') cargs))
      (.wrapForalls Dc (.mkApps (.const I lsC') cargs)) (.sort uC) := by
    rw [← eC]; exact hTcsd
  have hCpi := hTc'.piSD
  have hNpi := hNH.piSD
  have hBpi := hBH.piSD
  obtain ⟨wC, hCbody⟩ := PiSD.body_sd hCpi hTcsd'
  obtain ⟨wN, hNbody⟩ := PiSD.body_sd hNpi hNSD
  obtain ⟨wB, hBbody⟩ := PiSD.body_sd hBpi hBSD
  rw [List.append_nil] at hCbody hNbody hBbody
  obtain ⟨uNb, hNbH⟩ := HTS.wrapForalls_body hNH
  rw [List.append_nil] at hNbH
  have hlenBN : DB.length = Dn.length := by omega
  have hTWc : Ob.Sub (Obs' .id .empty (cc.type.instL lsC))
      (Obs' .id .empty (.wrapForalls Dc (.mkApps (.const I lsC') cargs))) := by
    rw [eC]; exact Ob.Sub.refl
  have hCpre := spine_tele_prefix henv hΔ hmaj W tv hcc hTWc hCpi (by omega)
  -- the levels of the family spines
  obtain ⟨cI₁, -, hcI₁, hlwI, -, -, -, -, -, -⟩ :=
    hIR.spine henv hΔ rfl WR tvR (iargs.map fun _ => []) (forall₂_nil_lists _) [] nofun
  obtain ⟨cI₂, -, hcI₂, hlwC', -, -, -, -, -, -⟩ :=
    hIC.spine henv hΔ rfl WC tvC (cargs.map fun _ => []) (forall₂_nil_lists _) [] nofun
  cases hcI.symm.trans hcI₁
  cases hcI.symm.trans hcI₂
  have hITWC : Ob.Sub (Obs' .id .empty (cI.type.instL lsC'))
      (Obs' .id .empty (.wrapForalls DI RI)) :=
    fun o h => hITW o (Obs.lvEq h (LvEq.instL _ hlwC' hlwI hlsCI))
  -- S4: the major domain against the installed constructor's result, along `I`'s telescope
  obtain ⟨hlenRC, -, WRC, hobsRC⟩ := rigid_spines_substEq henv hΔ hcI hITW hIpi hIR WR tvR
    hIC WC tvC hIrig subRC subCR (by omega)
  have hcargsl : cargs.length = cnp + nind := by omega
  -- the specialization arguments at the recursor's parameters
  have hDsget : ∀ i (hi : i < cnp), (Ds[i]'(by omega)).ClosedN np :=
    fun i hi => hDscl _ (List.getElem_mem _)
  have hPl : (recArgs.take np).length = np := by simp; omega
  have hiargsGet : ∀ i (hi : i < cnp), iargs[i]'(by omega) = (Ds[i]'(by omega)).liftN (nmm + nind) :=
    fun i hi => (List.getElem?_eq_some_iff.1 (hiargsP i hi)).2
  have hsplitR : recArgs = recArgs.take np ++ recArgs.drop np := (List.take_append_drop _ _).symm
  have hdropl : (recArgs.drop np).length = nmm + nind := by simp; omega
  -- `iargs[i]` at the recursor arguments is `Ds[i]` at the recursor's parameters
  have hiargsSubst : ∀ i (hi : i < cnp) (L : List VExpr), L.length = recArgs.length →
      (iargs[i]'(by omega)).subst (VExpr.argSubst L) =
        (Ds[i]'(by omega)).subst (VExpr.argSubst (L.take np)) := by
    intro i hi L hL
    rw [hiargsGet i hi]
    have hsplit : L = L.take np ++ L.drop np := (List.take_append_drop _ _).symm
    have hdl : (L.drop np).length = nmm + nind := by simp; omega
    conv => lhs; rw [hsplit, ← hdl]
    exact liftN_subst_argSubst_append _ _ _
  have hiargsCl : ∀ i (hi : i < cnp), (iargs[i]'(by omega)).ClosedN recArgs.length := by
    intro i hi
    rw [hiargsGet i hi, hrA]
    have := (hDsget i hi).liftN (n := nmm + nind) (j := 0)
    simpa [Nat.add_assoc] using this
  -- the observations of, and the substitution at, a bare variable at an argument valuation
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
  -- the specialization arguments at the recursor's parameters, as terms of `Γ`
  obtain ⟨L2, hL2⟩ : ∃ L2, L2 = Ds.map (·.subst (VExpr.argSubst (recArgs.take np))) := ⟨_, rfl⟩
  have hL2l : L2.length = cnp := by rw [hL2, List.length_map, hDsl]
  have hL2get : ∀ i (hi : i < cnp), L2[i]'(by omega) =
      (Ds[i]'(by omega)).subst (VExpr.argSubst (recArgs.take np)) := by
    intro i hi; subst hL2; simp
  have hL2σ : ∀ i (hi : i < cnp), (L2[i]'(by omega)).subst σ =
      (Ds[i]'(by omega)).subst (VExpr.argSubst ((recArgs.take np).map (·.subst σ))) := by
    intro i hi
    rw [hL2get i hi, subst_argSubst_comp (by rw [hPl]; exact hDsget i hi)]
  have hiargsR : ∀ i (hi : i < cnp),
      (iargs[i]'(by omega)).subst (VExpr.argSubst (recArgs.map (·.subst σ))) =
        (L2[i]'(by omega)).subst σ := by
    intro i hi
    rw [hiargsSubst i hi _ (by simp), hL2σ i hi, List.map_take]
  have hiargsObs : ∀ i (hi : i < cnp),
      Obs' (VExpr.argSubst (recArgs.map (·.subst σ))) (argSets env U Δ σ S recArgs)
        (iargs[i]'(by omega)) = Obs' σ S (L2[i]'(by omega)) := by
    intro i hi
    funext o; apply propext
    rw [← Obs.subst_argSubst (hiargsCl i hi), hiargsSubst i hi _ rfl, hL2get i hi]
  have hcargsGet : ∀ i (hi : i < cnp), cargs[i]'(by omega) = .bvar (cnp + nf - 1 - i) :=
    fun i hi => (List.getElem?_eq_some_iff.1 (hcargsP i hi)).2
  -- (C1) the family's domains at the two related prefixes of the major and the installed result
  have WRC' : Ctx.SubstEq env U Δ
      (VExpr.argSubst (iargs.map (·.subst (VExpr.argSubst (recArgs.map (·.subst σ))))))
      (VExpr.argSubst (cargs.map (·.subst (VExpr.argSubst (ctorArgs.map (·.subst σ))))))
      (DI.take (iargs.map (·.subst (VExpr.argSubst (recArgs.map (·.subst σ))))).length).reverse := by
    simpa using WRC
  have hWRCget : ∀ i (hi : i < cnp + nind),
      (∃ u, env.HasType U (DI.take i).reverse DI[i] (.sort u)) ∧
      env.IsDefEq U Δ ((iargs[i]'(by omega)).subst (VExpr.argSubst (recArgs.map (·.subst σ))))
        ((cargs[i]'(by omega)).subst (VExpr.argSubst (ctorArgs.map (·.subst σ))))
        (DI[i].subst (VExpr.argSubst
          ((iargs.take i).map (·.subst (VExpr.argSubst (recArgs.map (·.subst σ))))))) := by
    intro i hi
    have := substEq_argSubst_get (D := DI) (by simp; omega) (by simp; omega) WRC' (i := i)
      (by simp; omega)
    simpa [List.map_take] using this
  have hRC1 : ∀ i (hi : i < cnp + nind),
      TyCls env U Δ (DI[i].subst (VExpr.argSubst
          ((iargs.take i).map (·.subst (VExpr.argSubst (recArgs.map (·.subst σ))))))) =
        TyCls env U Δ (DI[i].subst (VExpr.argSubst
          ((cargs.take i).map (·.subst (VExpr.argSubst (ctorArgs.map (·.subst σ))))))) := by
    intro i hi
    obtain ⟨⟨u, hDI⟩, -⟩ := hWRCget i hi
    have Wi := substEq_take (Ds := DI) _ _ (by simp; omega) (by simp; omega) WRC' i (by simp; omega)
    simp only [List.map_take]
    exact TyCls.eq_of_defeq (by simpa using hDI.substDF henv Wi.wf hΔ Wi)
  -- (C2') the family's domain at a bare variable of the installed result
  have hRC2 : ∀ i y (hi : i < cnp + nind) (hyl : y < cnp + nf), cargs[i]? = some (.bvar y) →
      TyCls env U Δ (DI[i].subst (VExpr.argSubst
          ((cargs.take i).map (·.subst (VExpr.argSubst (ctorArgs.map (·.subst σ))))))) =
        TyCls env U Δ ((Dc[cnp + nf - 1 - y]'(by omega)).subst
          (VExpr.argSubst ((ctorArgs.take (cnp + nf - 1 - y)).map (·.subst σ)))) := by
    intro i y hi hyl hy
    have hy' : cargs[i]'(by omega) = .bvar y := (List.getElem?_eq_some_iff.1 hy).2
    have hL := lookup_append (Γ := []) Dc.reverse y (by simp; omega)
    rw [List.append_nil] at hL
    have e1 := bvar_arg_dom_cls henv hΔ hcI hITWC hIpi hIC WC tvC (by omega) (by omega) hy' hL
    rw [e1, lift_subst_argSubst Dc (ctorArgs.map (·.subst σ)) (by omega) (by simp; omega)]
    simp [hDcl, List.map_take]
  -- S4': the constructor's parameters are the specialization arguments at the recursor's
  have hQLdef : ∀ i (hi : i < cnp),
      env.IsDefEq U Δ ((ctorArgs[i]'(by omega)).subst σ) ((L2[i]'(by omega)).subst σ)
        ((Dc[i]'(by omega)).subst (VExpr.argSubst ((ctorArgs.take i).map (·.subst σ)))) := by
    intro i hi
    obtain ⟨-, hd⟩ := hWRCget i (by omega)
    rw [hiargsR i hi, hcargsGet i hi, substBvar ctorArgs _ (by omega)] at hd
    have e4 : ctorArgs.length - 1 - (cnp + nf - 1 - i) = i := by omega
    simp only [e4] at hd
    have hmem : TyCls env U Δ (DI[i].subst (VExpr.argSubst
        ((iargs.take i).map (·.subst (VExpr.argSubst (recArgs.map (·.subst σ)))))))
        ((Dc[i]'(by omega)).subst (VExpr.argSubst ((ctorArgs.take i).map (·.subst σ)))) := by
      rw [hRC1 i (by omega), hRC2 i (cnp + nf - 1 - i) (by omega) (by omega) (hcargsP i hi)]
      simp only [show cnp + nf - 1 - (cnp + nf - 1 - i) = i by omega]
      exact TyCls.self
    exact (TyCls.defeq_rev henv hΔ hmem hd).symm
  have hQLobs : ∀ i (hi : i < cnp),
      Ob.Sub (Obs' σ S (ctorArgs[i]'(by omega))) (Obs' σ S (L2[i]'(by omega))) ∧
      Ob.Sub (Obs' σ S (L2[i]'(by omega))) (Obs' σ S (ctorArgs[i]'(by omega))) := by
    intro i hi
    obtain ⟨h1, h2⟩ := hobsRC i (by omega) (by omega)
    rw [hiargsObs i hi, hcargsGet i hi, obsBvar ctorArgs _ (by omega)] at h1 h2
    have e4 : ctorArgs.length - 1 - (cnp + nf - 1 - i) = i := by omega
    simp only [e4] at h1 h2
    exact ⟨h2, h1⟩
  -- S5: the specialized arguments `L2 ++ fields` along the installed constructor's telescope,
  -- related to the constructor's arguments, with the constructor arguments' observation sets
  obtain ⟨cview, hcview⟩ : ∃ cview, cview = L2 ++ ctorArgs.drop cnp := ⟨_, rfl⟩
  have hcvl : cview.length = cnp + nf := by subst hcview; simp; omega
  have hcvget : ∀ m (hm : m < cnp + nf), cview[m]'(by omega) =
      if h : m < cnp then L2[m]'(by omega) else ctorArgs[m]'(by omega) := by
    intro m hm
    subst hcview
    split
    · rw [List.getElem_append_left (by omega)]
    · rw [List.getElem_append_right (by omega)]; simp; congr 1; omega
  have hcvtake : ∀ m, cnp ≤ m → m ≤ cnp + nf →
      cview.take m = L2 ++ (ctorArgs.drop cnp).take (m - cnp) := by
    intro m h1 h2
    subst hcview
    rw [List.take_append, List.take_of_length_le (by omega), hL2l]
  have hCV : ∀ m, m ≤ cnp + nf →
      Ctx.SubstEq env U Δ (VExpr.argSubst ((ctorArgs.take m).map (·.subst σ)))
        (VExpr.argSubst ((cview.take m).map (·.subst σ))) (Dc.take m).reverse ∧
      TV env U Δ (Dc.take m).reverse (VExpr.argSubst ((cview.take m).map (·.subst σ)))
        (argSets env U Δ σ S (ctorArgs.take m)) := by
    intro m
    induction m with
    | zero => intro _; simp; exact ⟨.nil, ⟨fun _ _ h => by simp [argSets] at h,
        fun _ _ h => by cases h⟩⟩
    | succ m ih =>
      intro hm
      obtain ⟨Wm, tvm⟩ := ih (by omega)
      obtain ⟨-, tvCm⟩ := hCpre m (by omega)
      obtain ⟨WCm1, tvCm1⟩ := hCpre (m + 1) (by omega)
      obtain ⟨hdTake, u, hDm⟩ := DomsSD.take_getElem hCpi.doms m (by omega)
      rw [List.append_nil] at hDm
      have hml : ((ctorArgs.take m).map (·.subst σ)).length = m := by simp; omega
      have hcml : ((cview.take m).map (·.subst σ)).length = m := by simp; omega
      rw [List.take_succ_eq_append_getElem (l := ctorArgs) (by omega), List.map_append,
        List.map_singleton] at WCm1 tvCm1
      rw [argSets_snoc] at tvCm1
      have htyQ := (substEq_snoc_inv hml (by omega) WCm1).1
      have hXQ := TV.snoc_inv hml (by omega) tvCm1
      rw [List.take_succ_eq_append_getElem (l := ctorArgs) (by omega),
        List.take_succ_eq_append_getElem (l := cview) (by omega), List.map_append,
        List.map_singleton, List.map_append, List.map_singleton, argSets_snoc]
      have eDm : TyCls env U Δ ((Dc[m]'(by omega)).subst
            (VExpr.argSubst ((ctorArgs.take m).map (·.subst σ)))) =
          TyCls env U Δ ((Dc[m]'(by omega)).subst
            (VExpr.argSubst ((cview.take m).map (·.subst σ)))) :=
        TyCls.eq_of_defeq (by simpa using hDm.1.defeq.hasType.1.substDF henv Wm.wf hΔ Wm)
      -- the new entry: a parameter is related to its specialization argument
      have hab : env.IsDefEq U Δ ((ctorArgs[m]'(by omega)).subst σ) ((cview[m]'(by omega)).subst σ)
          ((Dc[m]'(by omega)).subst (VExpr.argSubst ((ctorArgs.take m).map (·.subst σ)))) := by
        rw [hcvget m (by omega)]
        split
        · exact hQLdef m (by assumption)
        · exact htyQ
      have hctx : CtxSD env U Δ [] (Dc.take m).reverse := by
        simpa using DomsSD.ctxSD (L := []) (Γ := []) (by simpa using hdTake) .nil
      have hsubD : Ob.Sub
          (Obs' (VExpr.argSubst ((ctorArgs.take m).map (·.subst σ)))
            (argSets env U Δ σ S (ctorArgs.take m)) (Dc[m]'(by omega)))
          (Obs' (VExpr.argSubst ((cview.take m).map (·.subst σ)))
            (argSets env U Δ σ S (ctorArgs.take m)) (Dc[m]'(by omega))) := by
        refine SoundAt.sub_sets henv hΔ hDm.2 hctx Wm (fun x hx => ?_) tvCm tvm
          (fun i o h => ⟨o, h, .refl⟩)
        simp only [List.length_reverse, List.length_take] at hx
        rw [VExpr.argSubst_ge _ (by simp; omega), VExpr.argSubst_ge _ (by simp; omega)]
        simp; omega
      refine ⟨substEq_argSubst_snoc hml (by omega) Wm hDm.1.defeq.hasType.1 hab,
        tv_argSubst_snoc hcml (by omega) tvm
          (fun o h w hw => Obs.backed h tv.1 w hw) fun o ho => ?_⟩
      have hcls : ElCls env U Δ (TyCls env U Δ ((Dc[m]'(by omega)).subst
            (VExpr.argSubst ((ctorArgs.take m).map (·.subst σ))))) ((ctorArgs[m]'(by omega)).subst σ) =
          ElCls env U Δ (TyCls env U Δ ((Dc[m]'(by omega)).subst
            (VExpr.argSubst ((cview.take m).map (·.subst σ))))) ((cview[m]'(by omega)).subst σ) := by
        rw [ElCls.eq_of_defeq TyCls.self hab, eDm]
      exact ((hXQ o ho).congr_cls hcls).mono_le hsubD
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
  -- S6: the template's view `P ++ fields` along the specialized and the normalized telescopes
  obtain ⟨view, hview⟩ : ∃ view, view = recArgs.take np ++ ctorArgs.drop cnp := ⟨_, rfl⟩
  have hvl : view.length = np + nf := by subst hview; simp; omega
  have hvtakeP : ∀ m, m ≤ np → view.take m = recArgs.take m := by
    intro m hm
    subst hview
    rw [List.take_append_of_le_length (by simp; omega), List.take_take, Nat.min_eq_left hm]
  have hvtakeF : ∀ j, j ≤ nf → view.take (np + j) = recArgs.take np ++ (ctorArgs.drop cnp).take j := by
    intro j hj
    subst hview
    rw [List.take_append, List.take_of_length_le (by simp; omega)]
    simp; omega
  have hvget : ∀ m (hm : m < np + nf), view[m]'(by omega) =
      if h : m < np then recArgs[m]'(by omega) else ctorArgs[cnp + (m - np)]'(by omega) := by
    intro m hm
    subst hview
    split
    · rw [List.getElem_append_left (by simp; omega)]; simp
    · rw [List.getElem_append_right (by simp; omega)]; simp; congr 1; simp; omega
  -- the specialization arguments at the substituted parameters
  have hDsσ : ∀ (fs : List VExpr), Ds.map (·.subst (VExpr.argSubst
      ((recArgs.take np).map (·.subst σ)))) ++ fs = (L2.map (·.subst σ)) ++ fs := by
    intro fs
    congr 1
    apply List.ext_getElem (by simp [hL2l, hDsl])
    intro i h1 h2
    simp only [List.getElem_map]
    rw [hL2σ i (by simpa [hDsl] using h1)]
  have hVW : ∀ m, m ≤ np + nf →
      (Ctx.SubstEq env U Δ (VExpr.argSubst ((view.take m).map (·.subst σ)))
        (VExpr.argSubst ((view.take m).map (·.subst σ))) (DB.take m).reverse ∧
      TV env U Δ (DB.take m).reverse (VExpr.argSubst ((view.take m).map (·.subst σ)))
        (argSets env U Δ σ S (view.take m))) ∧
      (Ctx.SubstEq env U Δ (VExpr.argSubst ((view.take m).map (·.subst σ)))
        (VExpr.argSubst ((view.take m).map (·.subst σ))) (Dn.take m).reverse ∧
      TV env U Δ (Dn.take m).reverse (VExpr.argSubst ((view.take m).map (·.subst σ)))
        (argSets env U Δ σ S (view.take m))) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [List.take_zero, List.map_nil, List.reverse_nil]
      exact ⟨⟨.nil, ⟨fun _ _ h => by simp [argSets] at h, fun _ _ h => by cases h⟩⟩,
        ⟨.nil, ⟨fun _ _ h => by simp [argSets] at h, fun _ _ h => by cases h⟩⟩⟩
    | succ m ih =>
      intro hm
      obtain ⟨⟨WBm, tvBm⟩, ⟨WNm, tvNm⟩⟩ := ih (by omega)
      have hvml : ((view.take m).map (·.subst σ)).length = m := by simp; omega
      obtain ⟨-, uB', hDBm⟩ := DomsSD.take_getElem hBpi.doms m (by omega)
      obtain ⟨-, uN', hDNm⟩ := DomsSD.take_getElem hNpi.doms m (by omega)
      rw [List.append_nil] at hDBm hDNm
      rw [List.take_succ_eq_append_getElem (l := view) (by omega), List.map_append,
        List.map_singleton, argSets_snoc]
      by_cases hmp : m < np
      · -- a parameter: typed along the recursor's telescope, hence along `Dn`, hence along `DB`
        have hvm : view[m]'(by omega) = recArgs[m]'(by omega) := by rw [hvget m (by omega), dif_pos hmp]
        rw [hvm]
        obtain ⟨WRm1, tvRm1⟩ := hRpre' (m + 1) (by omega)
        rw [List.take_succ_eq_append_getElem (l := recArgs) (by omega), List.map_append,
          List.map_singleton] at WRm1 tvRm1
        rw [argSets_snoc] at tvRm1
        have hrml : ((recArgs.take m).map (·.subst σ)).length = m := by simp; omega
        have htyR := (substEq_snoc_inv hrml (by omega) WRm1).1
        have hXR := TV.snoc_inv hrml (by omega) tvRm1
        obtain ⟨d, dn, hd1, hd2, hlv⟩ := hDP m hmp
        have e5 : dsH[m]'(by omega) = d := (List.getElem?_eq_some_iff.1 hd1).2
        have e6 : Dn[m]'(by omega) = dn := (List.getElem?_eq_some_iff.1 hd2).2
        rw [e5] at htyR hXR
        rw [hvtakeP m (by omega)] at WBm tvBm WNm tvNm ⊢
        have hlv' := hlv.subst (VExpr.argSubst ((recArgs.take m).map (·.subst σ)))
        have eRN : TyCls env U Δ (d.subst (VExpr.argSubst ((recArgs.take m).map (·.subst σ)))) =
            TyCls env U Δ ((Dn[m]'(by omega)).subst
              (VExpr.argSubst ((recArgs.take m).map (·.subst σ)))) := by
          rw [e6]; exact TyCls.eq_of_lvEq hlv'
        have htyN : env.IsDefEq U Δ ((recArgs[m]'(by omega)).subst σ)
            ((recArgs[m]'(by omega)).subst σ) ((Dn[m]'(by omega)).subst
              (VExpr.argSubst ((recArgs.take m).map (·.subst σ)))) :=
          TyCls.defeq_rev henv hΔ (by rw [eRN]; exact TyCls.self) htyR
        have hXN : ∀ o, Obs' σ S (recArgs[m]'(by omega)) o → TypedAt env U Δ
            (ElCls env U Δ (TyCls env U Δ ((Dn[m]'(by omega)).subst
              (VExpr.argSubst ((recArgs.take m).map (·.subst σ))))) ((recArgs[m]'(by omega)).subst σ))
            (VExpr.argSubst ((recArgs.take m).map (·.subst σ))) (argSets env U Δ σ S (recArgs.take m))
            (Dn[m]'(by omega)) o := by
          intro o ho
          refine ((hXR o ho).congr_cls (by rw [eRN])).mono_le ?_
          rw [e6]; exact Ob.Sub.of_imp fun o h => Obs.lvEq h hlv
        -- along `DB`, through the sound equality of the two telescopes
        have hrml' : ((recArgs.take m).map (·.subst σ)).length < Dn.length := by rw [hrml]; omega
        obtain ⟨eNB, subNB, -⟩ := tele_sound_dom henv hΔ hNDcl hBDcl (hNS.symm henv hΔ) hNpi hBpi
          hlenBN.symm (as := (recArgs.take m).map (·.subst σ)) hrml'
          (by rw [hrml]; exact WNm) (by rw [hrml]; exact tvNm)
        simp only [hrml] at eNB subNB
        have htyB : env.IsDefEq U Δ ((recArgs[m]'(by omega)).subst σ)
            ((recArgs[m]'(by omega)).subst σ) ((DB[m]'(by omega)).subst
              (VExpr.argSubst ((recArgs.take m).map (·.subst σ)))) :=
          TyCls.defeq_rev henv hΔ (by rw [eNB]; exact TyCls.self) htyN
        refine ⟨⟨substEq_argSubst_snoc hrml (by omega) WBm hDBm.1.defeq.hasType.1 htyB,
          tv_argSubst_snoc hrml (by omega) tvBm (fun o h w hw => Obs.backed h tv.1 w hw)
            fun o ho => ((hXN o ho).congr_cls (by rw [eNB])).mono_le subNB⟩,
          ⟨substEq_argSubst_snoc hrml (by omega) WNm hDNm.1.defeq.hasType.1 htyN,
          tv_argSubst_snoc hrml (by omega) tvNm (fun o h w hw => Obs.backed h tv.1 w hw) hXN⟩⟩
      · -- a field: typed along the installed constructor's telescope at the specialized
        -- arguments, hence along `DB`, hence along `Dn`
        obtain ⟨j, rfl⟩ : ∃ j, m = np + j := ⟨m - np, by omega⟩
        have hj : j < nf := by omega
        have hvm : view[np + j]'(by omega) = ctorArgs[cnp + j]'(by omega) := by
          rw [hvget _ (by omega), dif_neg hmp]; congr 1; omega
        rw [hvm]
        rw [hvtakeF j (by omega)] at WBm tvBm WNm tvNm hvml ⊢
        obtain ⟨WCj, -⟩ := hCV (cnp + j) (by omega)
        obtain ⟨WCj1, tvCj1⟩ := hCV (cnp + j + 1) (by omega)
        have hcj : ((ctorArgs.take (cnp + j)).map (·.subst σ)).length = cnp + j := by simp; omega
        have hcvj : ((cview.take (cnp + j)).map (·.subst σ)).length = cnp + j := by simp; omega
        rw [List.take_succ_eq_append_getElem (l := ctorArgs) (by omega),
          List.take_succ_eq_append_getElem (l := cview) (by omega), List.map_append,
          List.map_singleton, List.map_append, List.map_singleton] at WCj1
        rw [List.take_succ_eq_append_getElem (l := cview) (by omega),
          List.take_succ_eq_append_getElem (l := ctorArgs) (by omega), List.map_append,
          List.map_singleton, argSets_snoc] at tvCj1
        have hcvm : cview[cnp + j]'(by omega) = ctorArgs[cnp + j]'(by omega) := by
          rw [hcvget _ (by omega), dif_neg (by omega)]
        rw [hcvm] at WCj1 tvCj1
        have htyC := (substEq_snoc_inv hcj (by omega) WCj1).1
        have hXC := TV.snoc_inv hcvj (by omega) tvCj1
        obtain ⟨-, uC', hDCm⟩ := DomsSD.take_getElem hCpi.doms (cnp + j) (by omega)
        rw [List.append_nil] at hDCm
        have eQC : TyCls env U Δ ((Dc[cnp + j]'(by omega)).subst
              (VExpr.argSubst ((ctorArgs.take (cnp + j)).map (·.subst σ)))) =
            TyCls env U Δ ((Dc[cnp + j]'(by omega)).subst
              (VExpr.argSubst ((cview.take (cnp + j)).map (·.subst σ)))) :=
          TyCls.eq_of_defeq (by simpa using hDCm.1.defeq.hasType.1.substDF henv WCj.wf hΔ WCj)
        -- the specialized field domain is the installed one at the specialized arguments
        have hlvB := hDBf j hj ((recArgs.take np).map (·.subst σ))
          (((ctorArgs.drop cnp).take j).map (·.subst σ)) (by simp; omega) (by simp; omega)
        have hcvt : cview.take (cnp + j) = L2 ++ (ctorArgs.drop cnp).take j := by
          rw [hcvtake (cnp + j) (by omega) (by omega), show cnp + j - cnp = j by omega]
        rw [hDsσ, ← List.map_append, ← List.map_append, ← hcvt] at hlvB
        have eCB : TyCls env U Δ ((Dc[cnp + j]'(by omega)).subst
              (VExpr.argSubst ((cview.take (cnp + j)).map (·.subst σ)))) =
            TyCls env U Δ ((DB[np + j]'(by omega)).subst (VExpr.argSubst
              ((recArgs.take np ++ (ctorArgs.drop cnp).take j).map (·.subst σ)))) :=
          (TyCls.eq_of_lvEq hlvB).symm
        have htyB : env.IsDefEq U Δ ((ctorArgs[cnp + j]'(by omega)).subst σ)
            ((ctorArgs[cnp + j]'(by omega)).subst σ) ((DB[np + j]'(by omega)).subst
              (VExpr.argSubst ((recArgs.take np ++ (ctorArgs.drop cnp).take j).map (·.subst σ)))) :=
          TyCls.defeq_rev henv hΔ (by rw [eQC, eCB]; exact TyCls.self) htyC
        -- the observations of the specialized field domain
        have hsubCB : Ob.Sub
            (Obs' (VExpr.argSubst ((cview.take (cnp + j)).map (·.subst σ)))
              (argSets env U Δ σ S (ctorArgs.take (cnp + j))) (Dc[cnp + j]'(by omega)))
            (Obs' (VExpr.argSubst ((recArgs.take np ++ (ctorArgs.drop cnp).take j).map (·.subst σ)))
              (argSets env U Δ σ S (recArgs.take np ++ (ctorArgs.drop cnp).take j))
              (DB[np + j]'(by omega))) := by
          intro o ho
          obtain ⟨o', ho', l⟩ := ho.mono_le (S' := argSets env U Δ σ S (cview.take (cnp + j)))
            (fun i x hx => by
              have hi : i < cnp + j := by
                by_contra h
                rw [argSets, dif_neg (by simp; omega)] at hx
                exact hx
              rw [argSets_lt (by simp; omega)] at hx
              rw [argSets_lt (by simp; omega)]
              simp only [List.getElem_take, List.length_take] at hx ⊢
              have hk1 : min (cnp + j) ctorArgs.length - 1 - i = cnp + j - 1 - i := by omega
              have hk2 : min (cnp + j) cview.length - 1 - i = cnp + j - 1 - i := by omega
              simp only [hk1] at hx
              simp only [hk2]
              by_cases hkc : cnp + j - 1 - i < cnp
              · obtain ⟨x', hx', lx⟩ := (hQLobs _ hkc).1 x hx
                refine ⟨x', ?_, lx⟩
                rw [hcvget _ (by omega), dif_pos hkc]
                exact hx'
              · refine ⟨x, ?_, .refl⟩
                rw [hcvget _ (by omega), dif_neg hkc]
                exact hx)
          have hcl1 : (Dc[cnp + j]'(by omega)).ClosedN (cview.take (cnp + j)).length := by
            have := hCDcl (cnp + j) (by omega); simpa [hcvl, show min (cnp + j) (cnp + nf) = cnp + j by omega] using this
          have hcl2 : (DB[np + j]'(by omega)).ClosedN
              (recArgs.take np ++ (ctorArgs.drop cnp).take j).length := by
            have := hBDcl (np + j) (by omega)
            have hl : (recArgs.take np ++ (ctorArgs.drop cnp).take j).length = np + j := by
              simp; omega
            rw [hl]; exact this
          have h1 := (Obs.subst_argSubst hcl1).2 ho'
          have hlvB0 := hDBf j hj (recArgs.take np) ((ctorArgs.drop cnp).take j) hPl (by simp; omega)
          rw [← hL2, ← hcvt] at hlvB0
          exact ⟨o', (Obs.subst_argSubst hcl2).1 (Obs.lvEq h1 (LvEq.symm hlvB0)), l⟩
        have hXB : ∀ o, Obs' σ S (ctorArgs[cnp + j]'(by omega)) o → TypedAt env U Δ
            (ElCls env U Δ (TyCls env U Δ ((DB[np + j]'(by omega)).subst (VExpr.argSubst
              ((recArgs.take np ++ (ctorArgs.drop cnp).take j).map (·.subst σ)))))
              ((ctorArgs[cnp + j]'(by omega)).subst σ))
            (VExpr.argSubst ((recArgs.take np ++ (ctorArgs.drop cnp).take j).map (·.subst σ)))
            (argSets env U Δ σ S (recArgs.take np ++ (ctorArgs.drop cnp).take j))
            (DB[np + j]'(by omega)) o :=
          fun o ho => ((hXC o ho).congr_cls (by rw [eCB])).mono_le hsubCB
        -- along `Dn`
        have hvml' : ((recArgs.take np ++ (ctorArgs.drop cnp).take j).map (·.subst σ)).length <
            DB.length := by rw [hvml]; omega
        obtain ⟨eBN, subBN, -⟩ := tele_sound_dom henv hΔ hBDcl hNDcl hNS hBpi hNpi hlenBN
          (as := (recArgs.take np ++ (ctorArgs.drop cnp).take j).map (·.subst σ)) hvml'
          (by rw [hvml]; exact WBm) (by rw [hvml]; exact tvBm)
        simp only [hvml] at eBN subBN
        have htyN : env.IsDefEq U Δ ((ctorArgs[cnp + j]'(by omega)).subst σ)
            ((ctorArgs[cnp + j]'(by omega)).subst σ) ((Dn[np + j]'(by omega)).subst
              (VExpr.argSubst ((recArgs.take np ++ (ctorArgs.drop cnp).take j).map (·.subst σ)))) :=
          TyCls.defeq_rev henv hΔ (by rw [eBN]; exact TyCls.self) htyB
        refine ⟨⟨substEq_argSubst_snoc hvml (by omega) WBm hDBm.1.defeq.hasType.1 htyB,
          tv_argSubst_snoc hvml (by omega) tvBm (fun o h w hw => Obs.backed h tv.1 w hw) hXB⟩,
          ⟨substEq_argSubst_snoc hvml (by omega) WNm hDNm.1.defeq.hasType.1 htyN,
          tv_argSubst_snoc hvml (by omega) tvNm (fun o h w hw => Obs.backed h tv.1 w hw)
            fun o ho => ((hXB o ho).congr_cls (by rw [eBN])).mono_le subBN⟩⟩
  -- the full valuations
  obtain ⟨WCV, tvCV⟩ := hCV (cnp + nf) (Nat.le_refl _)
  have hcat : ctorArgs.take (cnp + nf) = ctorArgs := List.take_of_length_le (by omega)
  have hcvt : cview.take (cnp + nf) = cview := List.take_of_length_le (by omega)
  have hDct : Dc.take (cnp + nf) = Dc := List.take_of_length_le (by omega)
  rw [hcat, hcvt, hDct] at WCV tvCV
  obtain ⟨⟨WB, tvB⟩, ⟨WN, tvN⟩⟩ := hVW (np + nf) (Nat.le_refl _)
  have hvt : view.take (np + nf) = view := List.take_of_length_le (by omega)
  have hDBt : DB.take (np + nf) = DB := List.take_of_length_le (by omega)
  have hDnt : Dn.take (np + nf) = Dn := List.take_of_length_le (by omega)
  rw [hvt, hDBt] at WB tvB
  rw [hvt, hDnt] at WN tvN
  -- the field domain classes along the telescopes
  have hFieldCls : ∀ j (hj : j < nf),
      TyCls env U Δ ((Dc[cnp + j]'(by omega)).subst
          (VExpr.argSubst ((ctorArgs.take (cnp + j)).map (·.subst σ)))) =
        TyCls env U Δ ((Dn[np + j]'(by omega)).subst
          (VExpr.argSubst ((view.take (np + j)).map (·.subst σ)))) := by
    intro j hj
    obtain ⟨WCj, -⟩ := hCV (cnp + j) (by omega)
    obtain ⟨⟨WBj, tvBj⟩, -⟩ := hVW (np + j) (by omega)
    obtain ⟨-, uC', hDCm⟩ := DomsSD.take_getElem hCpi.doms (cnp + j) (by omega)
    rw [List.append_nil] at hDCm
    have eQC : TyCls env U Δ ((Dc[cnp + j]'(by omega)).subst
          (VExpr.argSubst ((ctorArgs.take (cnp + j)).map (·.subst σ)))) =
        TyCls env U Δ ((Dc[cnp + j]'(by omega)).subst
          (VExpr.argSubst ((cview.take (cnp + j)).map (·.subst σ)))) :=
      TyCls.eq_of_defeq (by simpa using hDCm.1.defeq.hasType.1.substDF henv WCj.wf hΔ WCj)
    have hcvt' : cview.take (cnp + j) = L2 ++ (ctorArgs.drop cnp).take j := by
      rw [hcvtake (cnp + j) (by omega) (by omega), show cnp + j - cnp = j by omega]
    have hlvB := hDBf j hj ((recArgs.take np).map (·.subst σ))
      (((ctorArgs.drop cnp).take j).map (·.subst σ)) (by simp; omega) (by simp; omega)
    rw [hDsσ, ← List.map_append, ← List.map_append, ← hcvt', ← hvtakeF j (by omega)] at hlvB
    have hvjl : ((view.take (np + j)).map (·.subst σ)).length = np + j := by simp; omega
    obtain ⟨eBN, -, -⟩ := tele_sound_dom henv hΔ hBDcl hNDcl hNS hBpi hNpi hlenBN
      (as := (view.take (np + j)).map (·.subst σ)) (by rw [hvjl]; omega)
      (by rw [hvjl]; exact WBj) (by rw [hvjl]; exact tvBj)
    simp only [hvjl] at eBN
    rw [eQC, ← TyCls.eq_of_lvEq hlvB, eBN]
  -- S7: the major domain against the normalized constructor's result at the view
  have hctxC : CtxSD env U Δ [] Dc.reverse := by
    simpa using DomsSD.ctxSD (L := []) (Γ := []) (by simpa using hCpi.doms) .nil
  have houtC : ∀ x, Dc.reverse.length ≤ x →
      VExpr.argSubst (ctorArgs.map (·.subst σ)) x = VExpr.argSubst (cview.map (·.subst σ)) x := by
    intro x hx
    simp only [List.length_reverse] at hx
    rw [VExpr.argSubst_ge _ (by simp; omega), VExpr.argSubst_ge _ (by simp; omega)]
    simp; omega
  have sub2 := SoundAt.sub_sets henv hΔ hCbody.2 hctxC WCV houtC tvC tvCV
    (fun i o h => ⟨o, h, .refl⟩)
  have sub2' := SoundAt.sub_sets henv hΔ hCbody.2 hctxC (SubstEq.symm henv hΔ WCV)
    (fun x hx => (houtC x hx).symm) tvCV tvC (fun i o h => ⟨o, h, .refl⟩)
  -- switching the parameter sets between the constructor's and the specialization's
  have hsets : ∀ (b : Bool) i o, (if b then argSets env U Δ σ S ctorArgs else
        argSets env U Δ σ S cview) i o →
      ∃ o', (if b then argSets env U Δ σ S cview else argSets env U Δ σ S ctorArgs) i o' ∧
        o' ≼ o := by
    intro b i x hx
    have hi : i < cnp + nf := by
      by_contra h
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hx <;>
        rw [argSets, dif_neg (by omega)] at hx <;> exact hx
    have hk1 : ctorArgs.length - 1 - i = cnp + nf - 1 - i := by omega
    have hk2 : cview.length - 1 - i = cnp + nf - 1 - i := by omega
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hx ⊢ <;>
      rw [argSets_lt (by omega)] at hx <;> rw [argSets_lt (by omega)]
    · simp only [hk1, hk2] at hx ⊢
      by_cases hkc : cnp + nf - 1 - i < cnp
      · rw [hcvget (cnp + nf - 1 - i) (by omega), dif_pos hkc] at hx
        exact (hQLobs _ hkc).2 x hx
      · rw [hcvget (cnp + nf - 1 - i) (by omega), dif_neg hkc] at hx
        exact ⟨x, hx, .refl⟩
    · simp only [hk1, hk2] at hx ⊢
      by_cases hkc : cnp + nf - 1 - i < cnp
      · rw [hcvget (cnp + nf - 1 - i) (by omega), dif_pos hkc]
        exact (hQLobs _ hkc).1 x hx
      · rw [hcvget (cnp + nf - 1 - i) (by omega), dif_neg hkc]
        exact ⟨x, hx, .refl⟩
  have hcl1 : (VExpr.mkApps (.const I lsC') cargs).ClosedN cview.length := by
    rw [hcvl]; simpa [hDcl] using hCRcl
  have hcl2 : RB.ClosedN view.length := by rw [hvl]; simpa [hDBl] using hBRcl
  have hlvR := hRB (recArgs.take np) (ctorArgs.drop cnp) hPl (by simp; omega)
  rw [← hL2, ← hcview, ← hview] at hlvR
  have hBC : ∀ o, Obs' (VExpr.argSubst (cview.map (·.subst σ))) (argSets env U Δ σ S cview)
      (.mkApps (.const I lsC') cargs) o ↔
      Obs' (VExpr.argSubst (view.map (·.subst σ))) (argSets env U Δ σ S view) RB o := by
    intro o
    rw [← Obs.subst_argSubst hcl1, ← Obs.subst_argSubst hcl2]
    exact ⟨fun h => Obs.lvEq h hlvR.symm, fun h => Obs.lvEq h hlvR⟩
  have hvll : (view.map (·.subst σ)).length = DB.length := by simp; omega
  obtain ⟨subBN, subNB⟩ := tele_sound_res henv hΔ hBDcl hBRcl hNRcl hNS hBpi hNpi
    hBbody hNbody hlenBN (as := view.map (·.subst σ)) hvll (by simpa using WB) (by simpa using tvB)
  have subRN : Ob.Sub (Obs' (VExpr.argSubst (recArgs.map (·.subst σ))) (argSets env U Δ σ S recArgs)
        (.mkApps (.const I lsI) iargs))
      (Obs' (VExpr.argSubst (view.map (·.subst σ))) (argSets env U Δ σ S view)
        (.mkApps (.const I lsN) nargs)) := by
    intro o ho
    obtain ⟨o1, h1, l1⟩ := subRC o ho
    obtain ⟨o2, h2, l2⟩ := sub2 o1 h1
    obtain ⟨o3, h3, l3⟩ := h2.mono_le (hsets true)
    obtain ⟨o4, h4, l4⟩ := subBN o3 ((hBC o3).1 h3)
    exact ⟨o4, h4, l4.trans (l3.trans (l2.trans l1))⟩
  have subNR : Ob.Sub (Obs' (VExpr.argSubst (view.map (·.subst σ))) (argSets env U Δ σ S view)
        (.mkApps (.const I lsN) nargs))
      (Obs' (VExpr.argSubst (recArgs.map (·.subst σ))) (argSets env U Δ σ S recArgs)
        (.mkApps (.const I lsI) iargs)) := by
    intro o ho
    obtain ⟨o1, h1, l1⟩ := subNB o ho
    obtain ⟨o2, h2, l2⟩ := ((hBC o1).2 h1).mono_le (hsets false)
    obtain ⟨o3, h3, l3⟩ := sub2' o2 h2
    obtain ⟨o4, h4, l4⟩ := subCR o3 h3
    exact ⟨o4, h4, l4.trans (l3.trans (l2.trans l1))⟩
  obtain ⟨hlenIN, hlsIN, WIN, hobsIN⟩ := rigid_spines_substEq henv hΔ hcI hITW hIpi hIR WR tvR
    hNbH (by simpa using WN) (by simpa using tvN) hIrig subRN subNR (by omega)
  -- S8: entries of the relation along the family's telescope
  obtain ⟨cI₃, -, hcI₃, hlwN, -, -, -, -, -, -⟩ :=
    hNbH.spine henv hΔ rfl (by simpa using WN) (by simpa using tvN) (nargs.map fun _ => [])
      (forall₂_nil_lists _) [] nofun
  cases hcI.symm.trans hcI₃
  have hITWN : Ob.Sub (Obs' .id .empty (cI.type.instL lsN))
      (Obs' .id .empty (.wrapForalls DI RI)) :=
    fun o h => hITW o (Obs.lvEq h (LvEq.instL _ hlwN hlwI (forall₂_equiv_symm hlsIN)))
  have WIN' : Ctx.SubstEq env U Δ
      (VExpr.argSubst (iargs.map (·.subst (VExpr.argSubst (recArgs.map (·.subst σ))))))
      (VExpr.argSubst (nargs.map (·.subst (VExpr.argSubst (view.map (·.subst σ))))))
      (DI.take (iargs.map (·.subst (VExpr.argSubst (recArgs.map (·.subst σ))))).length).reverse := by
    simpa using WIN
  have hWget : ∀ i (hi : i < cnp + nind),
      (∃ u, env.HasType U (DI.take i).reverse DI[i] (.sort u)) ∧
      env.IsDefEq U Δ ((iargs[i]'(by omega)).subst (VExpr.argSubst (recArgs.map (·.subst σ))))
        ((nargs[i]'(by omega)).subst (VExpr.argSubst (view.map (·.subst σ))))
        (DI[i].subst (VExpr.argSubst
          ((iargs.take i).map (·.subst (VExpr.argSubst (recArgs.map (·.subst σ))))))) := by
    intro i hi
    have := substEq_argSubst_get (D := DI) (by simp; omega) (by simp; omega) WIN' (i := i)
      (by simp; omega)
    simpa [List.map_take] using this
  have hC1 : ∀ i (hi : i < cnp + nind),
      TyCls env U Δ (DI[i].subst (VExpr.argSubst
          ((iargs.take i).map (·.subst (VExpr.argSubst (recArgs.map (·.subst σ))))))) =
        TyCls env U Δ (DI[i].subst (VExpr.argSubst
          ((nargs.take i).map (·.subst (VExpr.argSubst (view.map (·.subst σ))))))) := by
    intro i hi
    obtain ⟨⟨u, hDI⟩, -⟩ := hWget i hi
    have Wi := substEq_take (Ds := DI) _ _ (by simp; omega) (by simp; omega) WIN' i (by simp; omega)
    simp only [List.map_take]
    exact TyCls.eq_of_defeq (by simpa using hDI.substDF henv Wi.wf hΔ Wi)
  have hC2 : ∀ i y (hi : i < cnp + nind) (hyl : y < np + nf), nargs[i]? = some (.bvar y) →
      TyCls env U Δ (DI[i].subst (VExpr.argSubst
          ((nargs.take i).map (·.subst (VExpr.argSubst (view.map (·.subst σ))))))) =
        TyCls env U Δ ((Dn[np + nf - 1 - y]'(by omega)).subst
          (VExpr.argSubst ((view.take (np + nf - 1 - y)).map (·.subst σ)))) := by
    intro i y hi hyl hy
    have hy' : nargs[i]'(by omega) = .bvar y := (List.getElem?_eq_some_iff.1 hy).2
    have hL := lookup_append (Γ := []) Dn.reverse y (by simp; omega)
    rw [List.append_nil] at hL
    have e1 := bvar_arg_dom_cls henv hΔ hcI hITWN hIpi hNbH (by simpa using WN)
      (by simpa using tvN) (by omega) (by omega) hy' hL
    rw [e1, lift_subst_argSubst Dn (view.map (·.subst σ)) (by omega) (by simp; omega)]
    simp [hDnl, List.map_take]
  have hC3 : ∀ i y (hi : i < cnp + nind) (hyl : y < np + nmm + nind), iargs[i]? = some (.bvar y) →
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
  -- S9: the template
  have hArgsTake : ∀ j, j ≤ nf → argsR.take (np + nmm + j) =
      recArgs.take np ++ (recArgs.take (np + nmm)).drop np ++ (ctorArgs.drop cnp).take j := by
    intro j hj
    subst hargs
    rw [List.take_append, List.take_of_length_le (l := recArgs.take (np + nmm)) (by simp; omega)]
    have hl : (recArgs.take (np + nmm)).length = np + nmm := by simp; omega
    rw [hl, show np + nmm + j - (np + nmm) = j by omega]
    conv => lhs; rw [← List.take_append_drop np (recArgs.take (np + nmm))]
    rw [List.take_take, Nat.min_eq_left (by omega)]
  have hF1 : ∀ j (hj : j < nf),
      TyCls env U Δ ((binderTy doms m1 (nf - 1 - j)).subst
          (VExpr.argSubst (argsR.map (·.subst σ)))) =
        TyCls env U Δ ((Dn[np + j]'(by omega)).subst (VExpr.argSubst
          ((view.take (np + j)).map (·.subst σ)))) ∧
      ∃ d, (doms.map (·.instL m1))[np + nmm + j]? = some d ∧ ∀ o,
        Obs' (VExpr.argSubst ((argsR.take (np + nmm + j)).map (·.subst σ)))
            (argSets env U Δ σ S (argsR.take (np + nmm + j))) d o ↔
          Obs' (VExpr.argSubst ((view.take (np + j)).map (·.subst σ)))
            (argSets env U Δ σ S (view.take (np + j))) (Dn[np + j]'(by omega)) o := by
    intro j hj
    obtain ⟨d, dn, hd, hdn, hlv⟩ := hDF j hj
    have edn : Dn[np + j]'(by omega) = dn := (List.getElem?_eq_some_iff.1 hdn).2
    have hal : argsR.length = doms.length := by subst hargs; simp; omega
    have hmidl : ((recArgs.take (np + nmm)).drop np).length = nmm := by simp; omega
    have hpostl : ((ctorArgs.drop cnp).take j).length = j := by simp; omega
    have hdncl : dn.ClosedN (np + j) := by
      have := hNDcl (np + j) (by omega); rwa [edn] at this
    have key : ∀ (f : VExpr → VExpr),
        (dn.liftN nmm j).subst (VExpr.argSubst ((argsR.take (np + nmm + j)).map f)) =
          dn.subst (VExpr.argSubst ((view.take (np + j)).map f)) := by
      intro f
      rw [hArgsTake j (by omega), hvtakeF j (by omega), List.map_append, List.map_append,
        List.map_append]
      have := argSubst_liftN_mid dn ((recArgs.take np).map f)
        (((recArgs.take (np + nmm)).drop np).map f) (((ctorArgs.drop cnp).take j).map f)
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
      have hcl2 : dn.ClosedN (view.take (np + j)).length := by
        have hlen : (view.take (np + j)).length = np + j := by simp; omega
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
      have eD : TyCls env U Δ (d.subst (VExpr.argSubst ((argsR.take (np + nmm + j)).map (·.subst σ)))) =
          TyCls env U Δ ((Dn[np + j]'(by omega)).subst (VExpr.argSubst
            ((view.take (np + j)).map (·.subst σ)))) := by
        rw [← hF1t, binderTy_subst_argSubst (by omega) (by simp [hal])]
        simp only [show doms.length - 1 - (nf - 1 - j) = np + nmm + j by omega, hd', List.map_take]
      have hget : argsR[np + nmm + j]'(by omega) = ctorArgs[cnp + j]'(by omega) := by
        subst hargs
        rw [List.getElem_append_right (by simp; omega)]
        simp; congr 1; omega
      rw [show np + nmm + (j + 1) = np + nmm + j + 1 by omega,
        List.take_succ_eq_append_getElem (l := argsR) (by omega), List.map_append,
        List.map_singleton, argSets_snoc, hget]
      obtain ⟨-, ⟨WNj1, tvNj1⟩⟩ := hVW (np + j + 1) (by omega)
      have hvj : view[np + j]'(by omega) = ctorArgs[cnp + j]'(by omega) := by
        rw [hvget _ (by omega), dif_neg (by omega)]; congr 1; omega
      rw [List.take_succ_eq_append_getElem (l := view) (by omega), List.map_append,
        List.map_singleton, hvj] at WNj1 tvNj1
      rw [argSets_snoc] at tvNj1
      have hvjl : ((view.take (np + j)).map (·.subst σ)).length = np + j := by simp; omega
      have htyN := (substEq_snoc_inv hvjl (by omega) WNj1).1.hasType.1
      have hXN := TV.snoc_inv hvjl (by omega) tvNj1
      have hty : env.HasType U Δ ((ctorArgs[cnp + j]'(by omega)).subst σ)
          (d.subst (VExpr.argSubst ((argsR.take (np + nmm + j)).map (·.subst σ)))) := by
        have hm : TyCls env U Δ ((Dn[np + j]'(by omega)).subst
            (VExpr.argSubst ((view.take (np + j)).map (·.subst σ))))
            (d.subst (VExpr.argSubst ((argsR.take (np + nmm + j)).map (·.subst σ)))) := by
          rw [← eD]; exact TyCls.self
        exact TyCls.defeq_rev henv hΔ hm htyN
      obtain ⟨-, w, hDd⟩ := DomsSD.take_getElem hdomsSD (np + nmm + j) (by simp; omega)
      rw [List.append_nil] at hDd
      simp only [hd'] at hDd
      refine ⟨?_, ?_⟩
      · exact substEq_argSubst_snoc (D := doms.map (·.instL m1)) hjl (by simp; omega) Wj
          (by rw [hd']; exact hDd.1.defeq.hasType.1) (by rw [hd']; exact hty)
      · refine tv_argSubst_snoc hjl (by simp; omega) tvj
          (fun o h w hw => Obs.backed h tv.1 w hw) fun o ho => ?_
        rw [hd']
        refine ((hXN o ho).congr_cls (by rw [eD])).mono_le ?_
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
      obtain ⟨-, hd⟩ := hWget (cnp + j) (by omega)
      have ei : iargs[cnp + j]'(by omega) = .bvar (nind - 1 - j) :=
        (List.getElem?_eq_some_iff.1 (hiargsI j hjn)).2
      have en : nargs[cnp + j]'(by omega) = .bvar (nf - 1 - j') :=
        (List.getElem?_eq_some_iff.1 hn).2
      rw [ei, en, substBvar recArgs _ (by omega), substBvar view _ (by omega)] at hd
      have e3 : recArgs.length - 1 - (nind - 1 - j) = np + nmm + j := by omega
      have e4 : view.length - 1 - (nf - 1 - j') = np + j' := by omega
      simp only [e3, e4] at hd
      have hvj : view[np + j']'(by omega) = ctorArgs[cnp + j']'(by omega) := by
        rw [hvget _ (by omega), dif_neg (by omega)]; congr 1; omega
      rw [hvj] at hd
      have hvx : VExpr.argSubst (argsR.map (·.subst σ)) (nf - 1 - j') =
          (ctorArgs[cnp + j']'(by omega)).subst σ := argSubst_field hargs hkr hcA hj'
      have hvS : argSets env U Δ σ S argsR (nf - 1 - j') = Obs' σ S (ctorArgs[cnp + j']'(by omega)) :=
        argSets_field hargs hkr hcA hj'
      have eChain : TyCls env U Δ ((binderTy doms m1 (nf - 1 - j')).subst
          (VExpr.argSubst (argsR.map (·.subst σ)))) =
          TyCls env U Δ (DI[cnp + j].subst (VExpr.argSubst
            ((iargs.take (cnp + j)).map (·.subst (VExpr.argSubst (recArgs.map (·.subst σ))))))) := by
        rw [(hF1 j' hj').1, hC1 (cnp + j) (by omega),
          hC2 (cnp + j) (nf - 1 - j') (by omega) (by omega) hn]
        simp only [show np + nf - 1 - (nf - 1 - j') = np + j' by omega]
      obtain ⟨hob1, hob2⟩ := hobsIN (cnp + j) (by omega) (by omega)
      rw [ei, obsBvar recArgs _ (by omega), en, obsBvar view _ (by omega)] at hob1 hob2
      simp only [e3, e4] at hob1 hob2
      rw [hvj] at hob1 hob2
      refine ⟨recArgs[np + nmm + j]'(by omega), List.getElem?_eq_getElem _,
        ⟨_, by rw [eChain]; exact TyCls.self, by rw [hvx]; exact hd⟩, fun Aq Bq hB => ?_,
        by rw [hvS]; exact hob1, by rw [hvS]; exact hob2⟩
      have e := spine_dom_cls henv hΔ hci hTWr hpiH (pre := recArgs.take (np + nmm + j))
        (by simp; omega) W tv hB
      simp only [List.length_take, Nat.min_eq_left (show np + nmm + j ≤ recArgs.length by omega)]
        at e
      rw [eChain, e, hC3 (cnp + j) (nind - 1 - j) (by omega) (by omega) (hiargsI j hjn)]
      simp only [show np + nmm + nind - 1 - (nind - 1 - j) = np + nmm + j by omega]
  · -- the constructor's field domains
    have e := spine_dom_cls henv hΔ hcc hTWc hCpi (pre := ctorArgs.take (cnp + j))
      (by simp; omega) W tv hB
    simp only [List.length_take, Nat.min_eq_left (show cnp + j ≤ ctorArgs.length by omega)] at e
    rw [e, hFieldCls j hj, (hF1 j hj).1]

/-- `IotaArgRel` of an instance of a rule whose constructor has no fields: the reduct's
arguments are the recursor's parameters, motives and minors. -/
theorem iotaArgRel_nofields
    {Γ : List VExpr} {n ctor : Name} {m1 lsC : List VLevel} {np nmm nind cnp : Nat}
    {doms lead recArgs ctorArgs argsR : List VExpr} {A : VExpr}
    {ci : VConstant} {dsH : List VExpr} {RH : VExpr}
    (hci : env.constants n = some ci) (eH : ci.type.instL m1 = .wrapForalls dsH RH)
    (hlenH : dsH.length = np + nmm + nind + 1)
    (hdl : doms.length = np + nmm)
    (hDK : ∀ i < np + nmm, (doms.map (·.instL m1))[i]? = dsH[i]?)
    (hleadK : ∀ i < np + nmm, lead[i]? = some (.bvar (np + nmm - 1 - i)))
    (hrA : recArgs.length = np + nmm + nind) (hcA : ctorArgs.length = cnp)
    (hargs : argsR = recArgs.take (np + nmm) ++ ctorArgs.drop cnp)
    (ihe : HTS env U Δ Γ (.mkApps (.const n m1) (recArgs ++ [.mkApps (.const ctor lsC) ctorArgs])) A)
    {σ : VExpr.Subst} {S : ObSets} (W : Ctx.SubstEq env U Δ σ σ Γ) (tv : TV env U Δ Γ σ S) :
    IotaArgRel env U Δ Γ n ctor m1 lsC cnp 0 doms lead recArgs ctorArgs argsR σ S := by
  obtain ⟨ci₁, -, hci₁, hlw, ⟨uT, hT, hTsd⟩, -, -, -, -, -⟩ :=
    ihe.spine henv hΔ rfl W tv ((recArgs ++ [VExpr.mkApps (.const ctor lsC) ctorArgs]).map fun _ => [])
      (forall₂_nil_lists _) [] nofun
  cases hci.symm.trans hci₁
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
  have hargsE : argsR = recArgs.take (np + nmm) := by
    rw [hargs, List.drop_eq_nil_of_le (by omega), List.append_nil]
  subst hargsE
  have hDtake : (doms.map (·.instL m1)) = dsH.take (np + nmm) := by
    apply List.ext_getElem? 
    intro i
    simp only [List.getElem?_take]
    split
    · exact hDK i (by omega)
    · exact List.getElem?_eq_none (by simp; omega)
  obtain ⟨Wf, tvf⟩ := hRpre' (np + nmm) (by omega)
  have hal : (recArgs.take (np + nmm)).length = np + nmm := by simp; omega
  refine ⟨by rw [hDtake]; exact Wf, by rw [hDtake]; exact tvf,
    fun i x hi hx hfirst => ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  have hil : i < np + nmm := by
    by_contra hil
    have hxl : x < np + nmm := by omega
    have hi' := hleadK (np + nmm - 1 - x) (by omega)
    rw [show np + nmm - 1 - (np + nmm - 1 - x) = x by omega] at hi'
    exact hfirst _ (by omega) hi'
  have hxi : x = np + nmm - 1 - i := by
    rw [hleadK i hil] at hi; injection hi with hi; injection hi with hi; omega
  subst hxi
  have eBT : (binderTy doms m1 (np + nmm - 1 - i)).subst
      (VExpr.argSubst ((recArgs.take (np + nmm)).map (·.subst σ))) =
      (dsH[i]'(by omega)).subst (VExpr.argSubst ((recArgs.take i).map (·.subst σ))) := by
    rw [binderTy_subst_argSubst (by omega) (by simp [hdl]; omega)]
    simp only [show doms.length - 1 - (np + nmm - 1 - i) = i by omega, ← List.map_take]
    simp only [List.take_take, Nat.min_eq_left (show i ≤ np + nmm by omega)]
    have := hDK i hil
    rw [List.getElem?_eq_getElem (by simp; omega), List.getElem?_eq_getElem (by omega)] at this
    rw [Option.some.inj this]
  have hvx : VExpr.argSubst ((recArgs.take (np + nmm)).map (·.subst σ)) (np + nmm - 1 - i) =
      (recArgs[i]'(by omega)).subst σ := by
    rw [argSubst_map_lt (by omega)]
    simp only [List.getElem_take]
    congr 2; simp; omega
  have hvS : argSets env U Δ σ S (recArgs.take (np + nmm)) (np + nmm - 1 - i) = Obs' σ S (recArgs[i]'(by omega)) := by
    rw [argSets_lt (by omega)]
    simp only [List.getElem_take]
    congr 2; simp; omega
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

end

end Model
end VEnv
end Lean4Lean
