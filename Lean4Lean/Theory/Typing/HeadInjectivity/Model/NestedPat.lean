import Lean4Lean.Theory.Typing.HeadInjectivity.Model.NestedFacts

/-! # Validity of the ι rules of a nested block, from the data of a constructor

`Model.Nested.nested_finish`: a rule of a nested block read off the restored equation of a
generated constructor `index` is valid in the model (`PatValid.of_rule`,
`PatValid.of_rule_empty`), given the data of the constructor that depend on whether it is a
source constructor or the auxiliary constructor of a container (`Model/PatSound.lean` supplies
them): the specialization of its family and constructor (`Spec`), the restoration relating its
normalized type to the specialized type `B0`, the family's telescope and rigidity, the installed
constructor's type, and the projection facts and semantic sort of the family. -/

namespace Lean4Lean
namespace VEnv
namespace Model
namespace Nested
open InductiveSignature

/-- A compilation with container specializations has at least two families. -/
theorem nested_families {base : VEnv} {source expanded : VInductDecl} {s : InductiveSignature}
    {g : Instance s} {aux : List ContainerSpecialization} {block : VInductBlock}
    (C : CompilationData base source expanded s g aux block) (haux : aux ≠ []) :
    2 ≤ s.families.size := by
  obtain ⟨envTypes, direct, _, hdirect, _, hfamilies⟩ := C.correspondence
  have h1 := Lean4Lean.List.Forall₂.length_eq hfamilies
  have h2 := Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hdirect)
  have h3 : source.types ≠ [] := C.sourceWF.1
  simp only [declaration, List.length_map, List.length_zipIdx, Array.length_toList,
    List.length_append] at h1
  have := List.length_pos_iff.2 h3
  have := List.length_pos_iff.2 haux
  omega

set_option maxHeartbeats 8000000 in
/-- **Validity of a rule of a nested block** from the data of its constructor. -/
theorem nested_finish {envF env0 env' : VEnv} {decl : VInductDecl}
    (hF : envF.WF) (h0 : env0.WF) (hdecl : decl.WF env0)
    (hadd : env0.addInduct decl = some env') (hle : env' ≤ envF)
    (V0 : EnvValid envF env0)
    (hprojV : ∀ S info, env'.projections S info → ProjValid envF S info)
    (hpats : ∀ (p : Pattern) (r : p.RHS × p.Check), envF.pats p r →
      (∃ ci, env'.constants p.headConst = some ci) → env'.pats p r)
    (hdefs : ∀ df, envF.defeqs df → ∀ n ls, df.lhs.stripLams.getAppFnArgs.1 = .const n ls →
      (∃ ci, env'.constants n = some ci) → env'.defeqs df)
    (hctor : ∀ c, IsCtor envF c → envF.Rigid c) (hpctor : ∀ c, IsProjCtor envF c → envF.Rigid c)
    {rec : VRecursor} {ru : VRecRule} (hrec : rec ∈ decl.recs) (hru : ru ∈ rec.rules)
    (hc : ru.rhs.Closed)
    {block : VInductBlock} {base : VEnv} {expanded : VInductDecl} {s : InductiveSignature}
    {g : InductiveSignature.Instance s} {aux : List InductiveSignature.ContainerSpecialization}
    (haux : aux ≠ [])
    (hcomp : CompiledInductive env0 decl block)
    (hrecsOf : decl.RecsOf block) (hbwf : block.WF env0) (hbase : base ≤ env0)
    (C : InductiveSignature.CompilationData base decl expanded s g aux block)
    {df : VDefEq} (hdf : df ∈ block.rules) (H : VRecRule.OfEquation rec ru df)
    (index : Fin s.constructors.size)
    (hres : (compilationRestoration decl aux).equation (g.equation index) = some df)
    {envTypes : VEnv} (htypes : base.addConstVals decl.typeConstants = some envTypes)
    {I0 c0 : Name} {lvf : List VLevel → List VLevel} {Ds0 : List VExpr} {lvC0 : List VLevel}
    (hSF : Spec (compilationRestoration decl aux) s.families[s.constructors[index].owner].name
      s.params.length I0 lvf Ds0)
    (hSC : Spec (compilationRestoration decl aux) s.constructors[index].name s.params.length c0
      lvf Ds0)
    (hlvf : ∀ lv : List VLevel, lv.length = s.uvars → lvf lv = lvC0.map (·.inst lv))
    -- the restored and the specialized constructor types
    {B0 : VExpr}
    (hRT : RestoresType (compilationRestoration decl aux) envTypes decl.uvars
      (s.constructorType s.constructors[index]) B0)
    {cc : VConstant} {cdoms cres PB : List VExpr} (hPBl : PB.length = s.params.length)
    (hB0 : ∀ L : List VLevel, L.length = s.uvars → B0.instL L = .wrapForalls
      (PB.map (·.instL L) ++ ((cdoms.drop Ds0.length).zipIdx.map fun ((d, j) : VExpr × Nat) =>
        (d.instL (lvC0.map (·.inst L))).subst ((VExpr.argSubst (Ds0.map (·.instL L))).liftN j)))
      (((VExpr.mkApps (.const I0 (VLevel.params cc.uvars)) cres).instL
        (lvC0.map (·.inst L))).subst ((VExpr.argSubst (Ds0.map (·.instL L))).liftN
          s.constructors[index].fields.length)))
    -- the family
    {cI : VConstant} {uI : Nat} {DIr : List VExpr} {RIr XI : VExpr}
    (hcI : envF.constants I0 = some cI)
    (hIdef : env0.IsDefEq uI [] cI.type (.wrapForalls DIr RIr) XI)
    (hDIl : Ds0.length + s.families[s.constructors[index].owner].indices.length ≤ DIr.length)
    (hIrig : envF.Rigid I0)
    -- the installed constructor
    (hcc : envF.constants c0 = some cc)
    (hcty : cc.type = .wrapForalls cdoms (.mkApps (.const I0 (VLevel.params cc.uvars)) cres))
    (hlvC0 : lvC0.length = cc.uvars)
    (hcresP : ∀ i < Ds0.length,
      cres[i]? = some (.bvar (Ds0.length + s.constructors[index].fields.length - 1 - i)))
    -- the family's projection facts and sort
    {L : VLevel}
    (hpm : ProjMajor envF I0 c0 Ds0.length s.constructors[index].fields.length L)
    (hfs : FamSort envF I0 L)
    (hLz : L.inst (lvC0.map (·.inst g.levels)) ≈
      s.families[s.constructors[index].owner].resultLevel.inst g.levels) :
    PatValid envF
      (SimplePattern.iota rec.name rec.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
      (SimplePattern.iotaRHS rec.name ru.ctor rec.numParams rec.numMotives rec.numMinors
        rec.numIndices ru.ctorParams ru.nfields ru.rhs hc, .true) := by
  have henvF := hF.orderedStrong
  have hp' := hle.pats (addInduct_pat hrec hru hc hadd)
  have hci' := hle.constants (addInduct_rec_find hadd hrec)
  have hglv := (C.admissible.choose_spec.2).levels_length
  have hsu : s.uvars = decl.uvars := C.model.uvars.trans C.uvars
  -- the rule's data
  obtain ⟨hname, hctorN, hrhs, hk, hnI, hcp, hnf, harity⟩ :=
    rule_counts hdecl hrecsOf C hrec hru index hSC hres H
  obtain ⟨ds', ctorIdx, body', args', hds, hcidx, hl, hr, hb, -⟩ :=
    restored_equation C index hSC hres
  obtain ⟨dsH', hdsH, htype, hstat⟩ :=
    restored_iotaStatic C hrecsOf hrec index hSF hSC hname hds hcidx harity
  have hu := patUniq_decl h0 hdecl hadd hpats hrec hru (envF := envF)
  have hci : envF.constants rec.name = some rec.toVConstVal.toVConstant := hci'
  show PatValid envF (SimplePattern.iota rec.name
      (rec.numParams + rec.numMotives + rec.numMinors + rec.numIndices) ru.ctor
      (ru.ctorParams + ru.nfields)).toPattern
    (SimplePattern.iotaRHS' rec.name ru.ctor (rec.numParams + rec.numMotives + rec.numMinors)
      rec.numIndices ru.ctorParams ru.nfields ru.rhs hc, .true)
  change envF.pats (SimplePattern.iota rec.name
      (rec.numParams + rec.numMotives + rec.numMinors + rec.numIndices) ru.ctor
      (ru.ctorParams + ru.nfields)).toPattern
    (SimplePattern.iotaRHS' rec.name ru.ctor (rec.numParams + rec.numMotives + rec.numMinors)
      rec.numIndices ru.ctorParams ru.nfields ru.rhs hc, .true) at hp'
  -- the stage environments
  obtain ⟨envT, envC, envR, sT, sC, sR, sP⟩ := addInduct_stages hadd
  have hTC : decl.addTypesCtors env0 = some envC := by
    unfold VInductDecl.addTypesCtors; rw [sT]; exact sC
  obtain ⟨hTs, hRs⟩ := stages_orderedStrong h0 hdecl sT sC sR
  obtain ⟨VT, VR⟩ := stages_envValid V0 hprojV sT sC sR sP
  have hRF : envR ≤ envF := (addRules_le sP).trans hle
  have hCF : envC ≤ envF := addProjs_le.trans ((addRecs_le sR).trans hRF)
  have hTF : envT ≤ envF := (addCtors_le sC).trans hCF
  have h0F : env0 ≤ envF := (addInduct_le hadd).trans hle
  have hR' : decl.addTypesCtorsProjsRecs env0 = some envR := by
    unfold VInductDecl.addTypesCtorsProjsRecs; rw [addTypesCtorsProjs_eq_some hTC]; exact sR
  have hdfWF := VInductDecl.WF.block_rules_wf hcomp hrecsOf hbwf hR' _ hdf
  have hT' := sT
  rw [VInductDecl.addTypes_eq_addConstVals] at hT'
  have hET : envTypes ≤ envT := addConstVals_mono hbase htypes hT'
  -- the installed constructor's arity
  obtain ⟨ci2, hci2, hsh⟩ := hdecl.rules_ctor envC hTC rec hrec ru hru
  rw [hctorN] at hci2
  cases (hCF.constants hci2).symm.trans hcc
  have hcdl : cdoms.length = ru.ctorParams + ru.nfields := by
    have := hsh.1
    rw [hcty, VExpr.piArity_eq_forallArity, VExpr.forallArity_wrapForalls,
      forallArity_mkApps_const'] at this
    omega
  rw [← hctorN] at hstat hSC hcc hpm
  generalize rec.numParams + rec.numMotives + rec.numMinors = k at hk hp' hu ⊢
  generalize rec.numIndices = nind at hnI hp' hu ⊢
  generalize ru.ctorParams = cnp at hcp hp' hu hcdl ⊢
  generalize ru.nfields = nf at hnf hp' hu hcdl ⊢
  subst hk hnI hcp hnf
  have hr' : ru.rhs = .wrapLams ds' body' := hrhs.trans hr
  have hcis : IsCtor envF ru.ctor := .inr ⟨_, _, rec.name, _, _, hp', rfl⟩
  have hnodf : ∀ df', envF.defeqs df' → ∀ ls',
      df'.lhs.stripLams.getAppFnArgs.1 ≠ .const rec.name ls' := by
    intro df' hdf' ls' hh
    have h1 := hdefs df' hdf' _ _ hh ⟨_, addInduct_rec_find hadd hrec⟩
    rw [addInduct_defeqs hadd] at h1
    obtain ⟨_, hc0⟩ := (h0.ordered.defEqWF h1).1.head_const_lookup h0.orderedStrong (Γ := []) ⟨⟩ hh
    rw [addInduct_rec_fresh hadd hrec] at hc0; cases hc0
  have hcf : CtorFam envF ru.ctor I0 := by
    refine ⟨_, VLevel.params cc.uvars, hcc, ?_⟩
    rw [hcty, VExpr.forallResult_wrapForalls,
      forallResult_of_const_head (c := I0) (ls := VLevel.params cc.uvars)
        (by rw [VExpr.getAppFnArgs_mkApps_const]),
      VExpr.getAppFnArgs_mkApps_const]
  have hcov : ∀ x < ds'.length, VExpr.bvar x ∈
      iotaLead (s.params.length + (s.families.size + s.constructors.size))
        s.constructors[index].fields.length
        (ctorIdx.map (·.liftN (s.params.length + (s.families.size + s.constructors.size) -
          s.params.length) s.constructors[index].fields.length)) ∨
      x ∈ iotaFs s.constructors[index].fields.length := by
    intro x hx
    rw [mapM_length hds, Instance.eqDoms_length] at hx
    by_cases hxf : x < s.constructors[index].fields.length
    · exact .inr (List.mem_reverse.2 (List.mem_range.2 hxf))
    · refine .inl (List.mem_append_left _ (List.mem_map.2 ⟨x - s.constructors[index].fields.length,
        List.mem_reverse.2 (List.mem_range.2 (by omega)), by congr 1; omega⟩))
  -- the restored constructor type
  obtain ⟨restored, hrest, hdefU⟩ := hRT
  obtain ⟨P0, Fn0, Idx0, hP0, hFn0, hIdx0, rfl⟩ :=
    restored_constructorType s.constructors[index] hSF hrest
  have hP0l := mapM_length hP0
  have hFn0l := mapM_length hFn0
  have hIdx0l := mapM_length hIdx0
  simp only [fieldTypes, List.length_map, List.length_zipIdx] at hFn0l
  have hctorIdx : ctorIdx = Idx0.map (·.instL g.levels) := by
    have := mapM_map_of (f := (compilationRestoration decl aux).expr)
      (f' := (compilationRestoration decl aux).expr) (g := (·.instL g.levels))
      (g' := (·.instL g.levels)) (fun x y h => expr_instL_some h g.levels) hIdx0
    exact Option.some.inj (hcidx.symm.trans this)
  subst hctorIdx
  have hlvfg : lvf g.levels = lvC0.map (·.inst g.levels) := hlvf _ hglv
  have hlvfp : lvf (VLevel.params s.uvars) = lvC0.map (·.inst (VLevel.params s.uvars)) :=
    hlvf _ VLevel.params_length
  rw [hlvfg] at hstat
  have hsc : ∀ h ∈ (compilationRestoration decl aux).heads, ∀ e ∈ h.arguments,
      e.ClosedN h.nparams := fun h hh => (C.restorationScoped.2.2.1 h hh).2
  have hDK0 : ∀ i < s.params.length + (s.families.size + s.constructors.size),
      ds'[i]? = dsH'[i]? := by
    intro i hi
    have e : (g.eqDoms index)[i]? = (g.recDoms s.constructors[index].owner)[i]? := by
      rw [← List.getElem?_take_of_lt hi, g.eqDoms_take, ← g.recDoms_take s.constructors[index].owner,
        List.getElem?_take_of_lt hi]
    have hlt : i < (g.eqDoms index).length := by rw [g.eqDoms_length]; omega
    have hx1 := List.getElem?_eq_getElem hlt
    have hx2 := hx1; rw [e] at hx2
    obtain ⟨d1, hd1, e1⟩ := mapM_getElem? hds hx1
    obtain ⟨d2, hd2, e2⟩ := mapM_getElem? hdsH hx2
    rw [e1, e2, ← Option.some.inj (hd1.symm.trans hd2)]
  have hDP0 : ∀ i (hi : i < s.params.length),
      dsH'[i]? = some ((P0[i]'(by omega)).instL g.levels) := by
    intro i hi
    obtain ⟨d, hd, e⟩ := mapM_getElem? hdsH (g.recDoms_param s.constructors[index].owner hi)
    rw [e, ← Option.some.inj ((expr_instL_some (mapM_get hP0 i hi) g.levels).symm.trans hd)]
  have hDF0 : ∀ j (hj : j < s.constructors[index].fields.length),
      ds'[s.params.length + (s.families.size + s.constructors.size) + j]? =
        some (((Fn0[j]'(by omega)).instL g.levels).liftN (s.families.size + s.constructors.size) j) := by
    intro j hj
    obtain ⟨d, hd, e⟩ := mapM_getElem? hds (g.eqDoms_field index hj)
    rw [e]
    have hF := mapM_get hFn0 j (by simp [fieldTypes]; exact hj)
    rw [← Option.some.inj ((expr_liftN_some hsc (expr_instL_some hF g.levels) _ _).symm.trans hd)]
  have hrel := nested_rel henvF hTs VT hTF hET h0.orderedStrong V0 h0F
    (np := s.params.length) (nmm := s.families.size + s.constructors.size)
    (nind := s.families[s.constructors[index].owner].indices.length)
    (nf := s.constructors[index].fields.length) (su := s.uvars)
    hci htype (by rw [mapM_length hdsH, g.recDoms_length]) hglv hSF.closed hstat.2.2.2.1
    hcI hIdef hDIl hIrig hcc hcty hcdl hlvC0 hcresP
    (by rw [mapM_length hds, g.eqDoms_length]) hP0l hFn0l (by rw [hIdx0l, harity])
    hDK0 hDP0 hDF0
    (fun U Δ hΔ m1 hm1 _ => by
      obtain ⟨targs, htyp, -⟩ := restored_equation_type g index hds hres
      obtain ⟨⟨u, hTH⟩, -, -⟩ := eq_rhs_sound henvF hRs hRF VR hdfWF hΔ hm1
      rw [htyp, VExpr.instL_wrapForalls] at hTH
      exact ⟨u, _, hTH⟩)
    hPBl hB0 (by have h := hdefU; rw [← hsu] at h; rw [← hlvfp]; exact h)
  have hpm' : ProjMajor envF I0 ru.ctor Ds0.length
      (iotaFs s.constructors[index].fields.length).length L := by
    rw [iotaFs_length]; exact hpm
  obtain ⟨envE, hE, hadm⟩ := C.admissible
  have hmemF : s.families[s.constructors[index].owner] ∈ s.families.toList :=
    Array.mem_toList_iff.2 (Array.getElem_mem _)
  rcases hadm.elimination with hnz | hsmall | ⟨hsing, -⟩
  · -- families never in `Prop`: mode C is impossible
    have hnz' : (L.inst (lvC0.map (·.inst g.levels))).IsNeverZero :=
      (hnz _ hmemF).of_equiv (Eq.symm hLz)
    refine PatValid.of_rule henvF hp' hr' hci hstat hu hcov hIrig hcf hcis
      (hctor _ hcis) hctor hpctor hnodf (ms := Ds0) rfl ?_ hrel
    intro U Δ hΔ m1 hm1 hlen1
    obtain ⟨-, hRH, hRS⟩ := eq_rhs_sound henvF hRs hRF VR hdfWF hΔ hm1
    refine ⟨hpm'.majorFam (.inl ?_), fun keys hkl hobs => ?_,
      df.type.instL m1, by rw [hrhs]; exact hRH, by rw [hrhs]; exact hRS⟩
    · rw [← VLevel.inst_inst]
      exact hnz'.inst
    · exact (C_absurd_gen hΔ hm1 hstat.2.1 hstat.2.2.1 hstat.2.2.2.1 hIrig hfs
        hnz'.inst (by rw [hkl, hstat.lead_length]) hobs).elim
  · -- small elimination: the reduct has no observations
    refine PatValid.of_rule_empty henvF hp' hr' hci hstat hu (hctor _ hcis) hctor hpctor hnodf
      hpm.weak ?_ hrel
    intro U Δ hΔ m1 hm1 hlen1
    obtain ⟨⟨u, hTH⟩, hRH, hRS⟩ := eq_rhs_sound henvF hRs hRF VR hdfWF hΔ hm1
    refine ⟨⟨_, by rw [hrhs]; exact hRH, by rw [hrhs]; exact hRS⟩, fun o ho => ?_⟩
    obtain ⟨targs, htyp, htl⟩ := restored_equation_type g index hds hres
    obtain ⟨mo, hmo, emo⟩ := mapM_getElem? hds (eqDoms_motive g index)
    obtain ⟨mds0, rfl, hmds0⟩ := restored_motive g _ _ hmo
    have hlenD := mapM_length hds
    rw [g.eqDoms_length] at hlenD
    have hown := s.constructors[index].owner.isLt
    have hget : ds'.reverse[s.constructors[index].fields.length + s.constructors.size +
        (s.families.size - 1 - s.constructors[index].owner.val)]? =
        some (.wrapForalls mds0 (.sort g.targetLevel)) := by
      rw [List.getElem?_reverse (by omega), ← emo]
      congr 1; omega
    obtain ⟨mds, emds, lmds⟩ := binderTy_wrapForalls_sort hget m1
    have hcl : (df.type.instL m1).ClosedN :=
      ((hdfWF.2.closedN' hRs.ordered.closed (Γ := []) ⟨⟩).2.2).instL
    have hlk := lookup_binderTy (Γ := []) (ls := m1) (doms := ds')
      (x := s.constructors[index].fields.length + s.constructors.size +
        (s.families.size - 1 - s.constructors[index].owner.val)) (by omega)
    rw [List.append_nil, emds] at hlk
    rw [hrhs] at ho
    refine rhs_empty_motive henvF hΔ (doms := ds'.map (·.instL m1))
      (by rw [htyp, VExpr.instL_wrapForalls]) (by rw [hr, VExpr.instL_wrapLams])
      hcl hTH (by simp only [VExpr.instL_mkApps, VExpr.instL]; rfl) hlk ?_
      (funext fun v => by
        rw [VLevel.eval_inst]; exact (VLevel.equiv_def.1 hsmall _).trans rfl)
      hRS Ctx.SubstEq.nil TV.empty o ho
    rw [lmds, hmds0, List.length_map, htl, harity]
  · -- singleton elimination does not occur in a nested block
    exact absurd hsing.1 (by have := nested_families C haux; omega)

end Nested
end Model
end VEnv
end Lean4Lean
