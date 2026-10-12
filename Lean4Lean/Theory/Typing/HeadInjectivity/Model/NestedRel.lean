import Lean4Lean.Theory.Typing.HeadInjectivity.Model.NestedSyntax

/-! # The arguments of the instances of a restored rule

`Model.Nested.nested_rel`: the relation (`IotaArgRel`) of the instances of a rule of a nested
block to its reduct template, from the static data of the rule: the restored recursor, the
family of its major (with its telescope), the installed constructor of the restored equation's
major (a source constructor, or a container constructor), the restored constructor type `Dn`
(the restored normalized constructor type) and the specialized constructor type `B` it is
definitionally equal to (the source constructor's own type, or the container constructor's type
at the specialization). The instances are related by `iotaArgRel_container`, or by
`iotaArgRel_nofields` when the constructor has no fields. -/

namespace Lean4Lean
namespace VEnv
namespace Model
namespace Nested
open InductiveSignature

/-- A closed Π-telescope typed in a strong stage environment valid in the model of `envF` is
soundly typed at a sort. -/
theorem pi_sort_sd {envF envT : VEnv} (henvF : envF.OrderedStrong) (hTs : envT.OrderedStrong)
    (VT : EnvValid envF envT) (hTF : envT ≤ envF) {U : Nat} {Δ : List VExpr}
    (hΔ : OnCtx Δ (envF.IsType U)) {ds : List VExpr} {R X : VExpr} (hne : ds ≠ [])
    (h : envT.HasType U [] (.wrapForalls ds R) X) :
    ∃ u, HTS envF U Δ [] (.wrapForalls ds R) (.sort u) ∧
      SD envF U Δ [] (.wrapForalls ds R) (.wrapForalls ds R) (.sort u) := by
  obtain ⟨A0, ds0, rfl⟩ : ∃ A0 ds0, ds = A0 :: ds0 := by
    cases ds with
    | nil => exact absurd rfl hne
    | cons A0 ds0 => exact ⟨A0, ds0, rfl⟩
  obtain ⟨⟨u1, hA⟩, ⟨v1, hB⟩⟩ := HasType.forallE_inv hTs.ordered h
  have hsort : envT.HasType U [] (.wrapForalls (A0 :: ds0) R) (.sort (.imax u1 v1)) :=
    .forallEDF hA hB
  have st := IsDefEq.strong hTs (Γ := []) trivial hsort
  obtain ⟨S, H, -⟩ := VT.soundAtH henvF hTF U Δ hΔ st
  exact ⟨_, H, st.mono hTF, S⟩

theorem iotaLead_getElem?_lt {k nf i : Nat} {idx : List VExpr} (hi : i < k) :
    (iotaLead k nf idx)[i]? = some (.bvar (k - 1 - i + nf)) := by
  unfold iotaLead
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_map, List.getElem?_reverse (by simpa using hi)]
  simp only [List.length_range]
  rw [List.getElem?_range (by omega)]
  simp only [Option.map_some]

theorem iotaLead_getElem?_ge {k nf j : Nat} {idx : List VExpr} :
    (iotaLead k nf idx)[k + j]? = idx[j]? := by
  unfold iotaLead
  rw [List.getElem?_append_right (by simp)]
  simp

theorem instL_liftN_comm (e : VExpr) (ls : List VLevel) (n k : Nat) :
    (e.liftN n k).instL ls = (e.instL ls).liftN n k := VExpr.instL_liftN


set_option maxHeartbeats 8000000 in
/-- **The relation of the instances of a restored rule to its template.** -/
theorem nested_rel {envF envT envTypes envI : VEnv}
    (henvF : envF.OrderedStrong) (hTs : envT.OrderedStrong) (VT : EnvValid envF envT)
    (hTF : envT ≤ envF) (hET : envTypes ≤ envT)
    (hIs : envI.OrderedStrong) (VI : EnvValid envF envI) (hIF : envI ≤ envF)
    {np nmm nind nf : Nat} {su : Nat}
    -- the recursor
    {n : Name} {ci : VConstant} {dsH' : List VExpr} {RHs : VExpr} {glv lvC0 : List VLevel}
    {I0 : Name} {Ds0 : List VExpr}
    (hci : envF.constants n = some ci) (eH0 : ci.type = .wrapForalls dsH' RHs)
    (hlenH : dsH'.length = np + nmm + nind + 1) (hglv : glv.length = su)
    (hDs0 : ∀ e ∈ Ds0, e.ClosedN np)
    (hkH0 : dsH'[np + nmm + nind]? = some (.mkApps (.const I0 (lvC0.map (·.inst glv)))
      (Ds0.map (fun e => (e.instL glv).liftN (nmm + nind)) ++ vars nind 0)))
    -- the family
    {cI : VConstant} {uI : Nat} {DIr : List VExpr} {RIr XI : VExpr}
    (hcI : envF.constants I0 = some cI)
    (hIdef : envI.IsDefEq uI [] cI.type (.wrapForalls DIr RIr) XI)
    (hDIl : Ds0.length + nind ≤ DIr.length) (hIrig : envF.Rigid I0)
    -- the installed constructor
    {c0 : Name} {cc : VConstant} {cdoms cres : List VExpr}
    (hcc : envF.constants c0 = some cc)
    (hcty : cc.type = .wrapForalls cdoms (.mkApps (.const I0 (VLevel.params cc.uvars)) cres))
    (hcdl : cdoms.length = Ds0.length + nf) (hlvC0 : lvC0.length = cc.uvars)
    (hcresP : ∀ i < Ds0.length, cres[i]? = some (.bvar (Ds0.length + nf - 1 - i)))
    -- the template
    {doms : List VExpr} {P0 Fn0 Idx0 : List VExpr}
    (hdl : doms.length = np + nmm + nf) (hP0l : P0.length = np) (hFn0l : Fn0.length = nf)
    (hIdx0l : Idx0.length = nind)
    (hDK0 : ∀ i < np + nmm, doms[i]? = dsH'[i]?)
    (hDP0 : ∀ i (hi : i < np), dsH'[i]? = some ((P0[i]'(by omega)).instL glv))
    (hDF0 : ∀ j (hj : j < nf), doms[np + nmm + j]? = some (((Fn0[j]'(by omega)).instL glv).liftN nmm j))
    (hdomsT : ∀ (U : Nat) (Δ : List VExpr), OnCtx Δ (envF.IsType U) → ∀ m1 : List VLevel,
      (∀ l ∈ m1, l.WF U) → m1.length = ci.uvars →
      ∃ u T', HTS envF U Δ [] (.wrapForalls (doms.map (·.instL m1)) T') (.sort u))
    -- the restored and the specialized constructor types
    {B0 : VExpr} {PB : List VExpr} (hPBl : PB.length = np)
    (hB0 : ∀ L : List VLevel, L.length = su → B0.instL L = .wrapForalls
      (PB.map (·.instL L) ++ ((cdoms.drop Ds0.length).zipIdx.map fun (d, j) =>
        (d.instL (lvC0.map (·.inst L))).subst ((VExpr.argSubst (Ds0.map (·.instL L))).liftN j)))
      (((VExpr.mkApps (.const I0 (VLevel.params cc.uvars)) cres).instL
        (lvC0.map (·.inst L))).subst ((VExpr.argSubst (Ds0.map (·.instL L))).liftN nf)))
    (hdef : envTypes.IsDefEqU su [] (.wrapForalls (P0 ++ Fn0)
      (.mkApps (.const I0 (lvC0.map (·.inst (VLevel.params su))))
        (Ds0.map (fun e => (e.instL (VLevel.params su)).liftN nf) ++ Idx0))) B0) :
    ∀ (U : Nat) (Δ : List VExpr), OnCtx Δ (envF.IsType U) →
      ∀ (Γ : List VExpr) (m1 lsC : List VLevel) (recArgs ctorArgs : List VExpr) (A : VExpr),
      recArgs.length = np + nmm + nind → ctorArgs.length = Ds0.length + nf →
      HTS envF U Δ Γ (.mkApps (.const n m1) (recArgs ++ [.mkApps (.const c0 lsC) ctorArgs])) A →
      ∀ σ S, Ctx.SubstEq envF U Δ σ σ Γ → TV envF U Δ Γ σ S →
        IotaArgRel envF U Δ Γ n c0 m1 lsC Ds0.length nf doms
          (iotaLead (np + nmm) nf ((Idx0.map (·.instL glv)).map (·.liftN (np + nmm - np) nf)))
          recArgs ctorArgs (recArgs.take (np + nmm) ++ ctorArgs.drop Ds0.length) σ S ∧
        List.Forall₂ (· ≈ ·) lsC ((lvC0.map (·.inst glv)).map (·.inst m1)) := by
  intro U Δ hΔ Γ m1 lsC recArgs ctorArgs A hrA hcA ihe σ S W tv
  -- the levels of the instance
  obtain ⟨ci1, hci1, hm1, hlen1⟩ := HTS.spine_levels ihe
  cases hci.symm.trans hci1
  obtain ⟨Amaj, Bm, -, hmaj, -⟩ := HTS.spine_at _ rfl ihe recArgs.length (by simp)
  rw [List.getElem_append_right (by omega)] at hmaj
  simp only [Nat.sub_self, List.getElem_singleton] at hmaj
  obtain ⟨cc1, hcc1, hlsC, hlenC⟩ := HTS.spine_levels hmaj
  cases hcc.symm.trans hcc1
  obtain ⟨L, hL⟩ : ∃ L, L = glv.map (·.inst m1) := ⟨_, rfl⟩
  have hLw : ∀ l ∈ L, l.WF U := by
    intro l hl; rw [hL] at hl
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    exact VLevel.WF.inst hm1
  have hLl : L.length = su := by rw [hL, List.length_map, hglv]
  have hpL : (VLevel.params su).map (·.inst L) = L := VLevel.inst_map_id hLl
  have hlvL : (lvC0.map (·.inst glv)).map (·.inst m1) = lvC0.map (·.inst L) := by
    rw [hL, List.map_map]
    apply List.map_congr_left
    intro l _
    simp [Function.comp, VLevel.inst_inst]
  have hlvLw : ∀ l ∈ lvC0.map (·.inst L), l.WF U := by
    intro l hl
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    exact VLevel.WF.inst hLw
  have hpC : (VLevel.params cc.uvars).map (·.inst lsC) = lsC := VLevel.inst_map_id hlenC
  -- the recursor and its major domain, at the instance's levels
  have eH : ci.type.instL m1 = .wrapForalls (dsH'.map (·.instL m1)) (RHs.instL m1) := by
    rw [eH0, VExpr.instL_wrapForalls]
  have hlenH' : (dsH'.map (·.instL m1)).length = np + nmm + nind + 1 := by simp [hlenH]
  have hkH : (dsH'.map (·.instL m1))[np + nmm + nind]? = some (.mkApps
      (.const I0 (lvC0.map (·.inst L)))
      ((Ds0.map (·.instL L)).map (·.liftN (nmm + nind)) ++ vars nind 0)) := by
    rw [List.getElem?_map, hkH0]
    simp only [Option.map_some, VExpr.instL_mkApps, VExpr.instL, List.map_append, List.map_map,
      vars_instL, hlvL]
    congr 3
    apply List.map_congr_left
    intro e _
    simp only [Function.comp, VExpr.instL_liftN, VExpr.instL_instL, hL]
  -- the installed constructor, at the instance's levels
  have eC : cc.type.instL lsC = .wrapForalls (cdoms.map (·.instL lsC))
      (.mkApps (.const I0 lsC) (cres.map (·.instL lsC))) := by
    rw [hcty, VExpr.instL_wrapForalls, VExpr.instL_mkApps]
    simp only [VExpr.instL, hpC]
  -- the redex's typings
  obtain ⟨ci₁, -, hci₁, -, ⟨uT, hT, -⟩, -, -, -, -, -⟩ :=
    ihe.spine henvF hΔ rfl W tv ((recArgs ++ [VExpr.mkApps (.const c0 lsC) ctorArgs]).map fun _ => [])
      (forall₂_nil_lists _) [] nofun
  cases hci.symm.trans hci₁
  obtain ⟨cc₁, -, hcc₁, -, ⟨uC, hTc, -⟩, -, -, -, -, -⟩ :=
    hmaj.spine henvF hΔ rfl W tv (ctorArgs.map fun _ => []) (forall₂_nil_lists _) [] nofun
  cases hcc.symm.trans hcc₁
  have hlead : ∀ i < np + nmm,
      (iotaLead (np + nmm) nf ((Idx0.map (·.instL glv)).map (·.liftN (np + nmm - np) nf)))[i]? =
        some (.bvar (np + nmm - 1 - i + nf)) := fun i hi => iotaLead_getElem?_lt hi
  by_cases hnf : nf = 0
  · subst hnf
    obtain ⟨uR, uI, hIR, hIC, WR, tvR, WC, tvC, subCR, subRC⟩ :=
      redex_major_sub henvF hΔ hci eH hT hlenH' hkH hcc eC hTc hrA (by simp; omega) ihe W tv
    obtain ⟨-, hls, -⟩ := rigid_spines_rel henvF hΔ hIC WC tvC hIR WR tvR hIrig subCR subRC
    refine ⟨iotaArgRel_nofields henvF hΔ hci eH hlenH' (by omega) (fun i hi => by
        rw [List.getElem?_map, List.getElem?_map, hDK0 i hi]) (fun i hi => by
        simpa using hlead i hi) hrA hcA rfl ihe W tv, ?_⟩
    rw [hlvL]; exact hls
  have hnf' : 0 < nf := Nat.pos_of_ne_zero hnf
  -- the family's telescope
  have hNi : envI.IsDefEq U [] (cI.type.instL (lvC0.map (·.inst L)))
      ((VExpr.wrapForalls DIr RIr).instL (lvC0.map (·.inst L))) (XI.instL (lvC0.map (·.inst L))) :=
    IsDefEq.instL hlvLw hIdef
  obtain ⟨SN, -, HN⟩ := VI.soundAtH henvF hIF U Δ hΔ (IsDefEq.strong hIs (Γ := []) trivial hNi)
  rw [VExpr.instL_wrapForalls] at SN HN
  have hITW := (SN .id .id .empty .nil TV.empty TV.empty).1
  have hIpi := HTS.piSD HN
  -- the restored and the specialized constructor types, at `L`
  obtain ⟨X, hX⟩ := hdef
  obtain ⟨Ds, hDs⟩ : ∃ Ds, Ds = Ds0.map (·.instL L) := ⟨_, rfl⟩
  have hDsl : Ds.length = Ds0.length := by rw [hDs, List.length_map]
  rw [← hDs] at hkH
  have hDscl : ∀ d ∈ Ds, d.ClosedN np := by
    intro d hd; rw [hDs] at hd
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd
    exact (hDs0 e he).instL
  obtain ⟨DB, hDB⟩ : ∃ DB : List VExpr, DB = PB.map (·.instL L) ++
      ((cdoms.drop Ds0.length).zipIdx.map fun ((d, j) : VExpr × Nat) =>
        (d.instL (lvC0.map (·.inst L))).subst ((VExpr.argSubst Ds).liftN j)) := ⟨_, rfl⟩
  have eB : B0.instL L = .wrapForalls DB
      (((VExpr.mkApps (.const I0 (VLevel.params cc.uvars)) cres).instL
        (lvC0.map (·.inst L))).subst ((VExpr.argSubst Ds).liftN nf)) := by
    rw [hB0 L hLl, hDB, hDs]
  have eN : (VExpr.wrapForalls (P0 ++ Fn0)
      (.mkApps (.const I0 (lvC0.map (·.inst (VLevel.params su))))
        (Ds0.map (fun e => (e.instL (VLevel.params su)).liftN nf) ++ Idx0))).instL L =
      .wrapForalls ((P0 ++ Fn0).map (·.instL L))
        (.mkApps (.const I0 (lvC0.map (·.inst L)))
          (Ds.map (·.liftN nf) ++ Idx0.map (·.instL L))) := by
    rw [VExpr.instL_wrapForalls, VExpr.instL_mkApps]
    simp only [VExpr.instL, List.map_append, List.map_map]
    congr 3
    · apply List.map_congr_left
      intro l _
      simp only [Function.comp, VLevel.inst_inst, hpL]
    · rw [hDs, List.map_map]
      apply List.map_congr_left
      intro e _
      simp only [Function.comp, VExpr.instL_liftN, VExpr.instL_instL, hpL]
  have hXL := (IsDefEq.instL hLw hX).mono hET
  simp only [List.map_nil] at hXL
  rw [eN, eB] at hXL
  have hBcl := (hXL.hasType.2.closedN' hTs.ordered.closed (Γ := []) ⟨⟩).1
  have hNcl := (hXL.hasType.1.closedN' hTs.ordered.closed (Γ := []) ⟨⟩).1
  have hne : ∀ {ds ds' : List VExpr}, ds.length = np → ds'.length = nf → ds ++ ds' ≠ [] := by
    intro ds ds' h1 h2 h
    have := congrArg List.length h
    rw [List.length_append, List.length_nil] at this; omega
  obtain ⟨uB, hBH, hBSD⟩ := pi_sort_sd henvF hTs VT hTF hΔ
    (by rw [hDB]; exact hne (by simp [hPBl]) (by simp [hcdl])) hXL.hasType.2
  obtain ⟨uN, hNH, hNSD⟩ := pi_sort_sd henvF hTs VT hTF hΔ
    (by rw [List.map_append]; exact hne (by simp [hP0l]) (by simp [hFn0l])) hXL.hasType.1
  have hNS := (VT.soundAtH henvF hTF U Δ hΔ
    (IsDefEq.strong hTs (Γ := []) trivial hXL.symm)).1
  -- the installed constructor's telescope is closed
  have hccl : (VExpr.wrapForalls cdoms (.mkApps (.const I0 (VLevel.params cc.uvars)) cres)).ClosedN := by
    rw [← hcty]; exact henvF.ordered.closedC hcc
  obtain ⟨hcRcl, hcDcl⟩ := closedN_wrapForalls hccl
  simp only [Nat.zero_add] at hcRcl hcDcl
  have hlenDB : DB.length = np + nf := by
    rw [hDB]; simp [hPBl, hcdl]
  have hDBget : ∀ j (hj : j < nf), DB[np + j]'(by rw [hlenDB]; omega) =
      ((cdoms[Ds0.length + j]'(by omega)).instL (lvC0.map (·.inst L))).subst
        ((VExpr.argSubst Ds).liftN j) := by
    intro j hj
    subst hDB
    rw [List.getElem_append_right (by simp [hPBl])]
    simp [hPBl]
  obtain ⟨hres, hlsCI⟩ := iotaArgRel_container henvF hΔ (cnp := Ds0.length) (Ds := Ds)
    hci eH hlenH' hkH hDsl hDscl (by simp [hDsl, length_vars])
    (fun i hi => by
      rw [List.getElem?_append_left (by simp [hDsl]; omega), List.getElem?_map,
        List.getElem?_eq_getElem (by omega)]; rfl)
    (fun j hj => by
      rw [List.getElem?_append_right (by simp [hDsl]), List.length_map, hDsl,
        Nat.add_sub_cancel_left, vars_getElem? hj]
      simp)
    hcI hITW hIpi (by simp; omega) hIrig hcc eC (by simp [hcdl])
    (fun i hi => by rw [List.getElem?_map, hcresP i hi]; rfl)
    hBcl hBH hBSD hlenDB
    (fun hls j hj ps fs hps hfs => by
      rw [hDBget j hj, subst_spec_argSubst (by
        rw [hDsl]; exact (hcDcl (Ds0.length + j) (by omega)).instL) hfs]
      simp only [List.getElem_map]
      exact (LvEq.instL _ hlvLw hlsC (forall₂_equiv_symm hls)).subst _)
    (fun hls ps fs hps hfs => by
      rw [subst_spec_argSubst (by
        rw [hDsl]
        have := hcRcl.instL (ls := lvC0.map (·.inst L))
        rwa [hcdl] at this) hfs]
      have : VExpr.mkApps (.const I0 lsC) (cres.map (·.instL lsC)) =
          (VExpr.mkApps (.const I0 (VLevel.params cc.uvars)) cres).instL lsC := by
        rw [VExpr.instL_mkApps]; simp only [VExpr.instL, hpC]
      rw [this]
      exact (LvEq.instL _ hlvLw hlsC (forall₂_equiv_symm hls)).subst _)
    hNcl hNH hNSD hNS (by simp [hP0l, hFn0l]) (by simp [hDsl, hIdx0l])
    (fun i hi => by
      rw [List.getElem?_append_left (by simp [hDsl]; omega), List.getElem?_map,
        List.getElem?_eq_getElem (by omega)]; rfl)
    hdl
    (fun _ i hi => ⟨(P0[i]'(by omega)).instL L, (P0[i]'(by omega)).instL L,
      by rw [List.getElem?_map, hDP0 i hi]; simp [VExpr.instL_instL, hL],
      by rw [List.getElem?_map, List.getElem?_append_left (by omega),
        List.getElem?_eq_getElem (by omega)]; rfl, .refl⟩)
    (fun i hi => by rw [List.getElem?_map, List.getElem?_map, hDK0 i hi])
    (fun _ j hj => ⟨((Fn0[j]'(by omega)).instL L).liftN nmm j, (Fn0[j]'(by omega)).instL L,
      by rw [List.getElem?_map, hDF0 j hj]; simp [VExpr.instL_instL, hL],
      by rw [List.getElem?_map, List.getElem?_append_right (by omega),
        List.getElem?_eq_getElem (by omega)]; simp [hP0l], .refl⟩)
    hlead
    (fun j x hx hxf => by
      rw [iotaLead_getElem?_ge, List.getElem?_map, List.getElem?_map] at hx
      have hj : j < nind := by
        refine Nat.lt_of_not_le fun hj' => ?_
        rw [List.getElem?_eq_none (by omega)] at hx; cases hx
      rw [List.getElem?_eq_getElem (by omega)] at hx
      simp only [Option.map_some, Option.some.injEq] at hx
      have e1 := eq_bvar_of_instL (eq_bvar_of_liftN hx hxf)
      rw [List.getElem?_append_right (by simp [hDsl]), List.length_map, hDsl,
        Nat.add_sub_cancel_left, List.getElem?_map, List.getElem?_eq_getElem (by omega), e1]
      rfl)
    (by simp [hIdx0l])
    (by obtain ⟨u, T', H⟩ := hdomsT U Δ hΔ m1 hm1 hlen1; exact (HTS.piSD H).doms)
    hrA (by omega) rfl ihe W tv
  refine ⟨hres, ?_⟩
  rw [hlvL]; exact hlsCI

end Nested
end Model
end VEnv
end Lean4Lean
