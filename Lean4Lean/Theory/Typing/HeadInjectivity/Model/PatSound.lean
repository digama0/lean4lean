import Lean4Lean.Theory.Typing.HeadInjectivity.Model.IotaHistory
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.NestedPat

/-! # Validity of the registered ι rules

A registered ι rule of a well-formed environment is valid in the model (`Model.PatValid`, the
`pat` case of `Model.sound`). Along the declaration history (`Model/EnvValid.lean`) the rule is
an ι rule registered by an inductive step (`addInduct_pats_origin'`), read off a generated
equation of the step's compiled block (`VInductDecl.WF.rule_block`):

* for an ordinary compilation (no container specializations) by `Model.PatValid.ordinary`
  (`Model/IotaHistory.lean`);
* for a nested compilation by `Model.PatValid.nested`, here.

A rule of a nested block is read off the restoration of a generated equation of a constructor
of the expanded signature (`Model.Nested.ctor_cases`): a source constructor, restored to itself,
or the auxiliary constructor of a container specialization, restored to the container's
constructor at the specialization arguments. Both are handled by `Model.Nested.nested_finish`
(`Model/NestedPat.lean`) from the constructor's data: its family's and its own specialization
(`Spec`), the installed constructor's raw shape, the specialized constructor type the restored
normalized type is definitionally equal to, the family's telescope and rigidity, and the
family's projection facts and semantic sort (the source declaration's, or the container's,
`Model/NestedFacts.lean`). -/

namespace Lean4Lean
namespace VEnv
namespace Model
open InductiveSignature Nested

/-- The data of a raw constructor shape: its telescope, its result family spine at the
declaration's universe parameters, and its parameter arguments. -/
theorem rawCtorShape_data {decl : VInductDecl} {t : VInductiveType} {fc : VConstVal}
    (H : decl.RawCtorShape t fc) (hu : fc.uvars = decl.uvars) :
    ∃ cdoms cres, fc.type = .wrapForalls cdoms (.mkApps (.const t.name (VLevel.params fc.uvars)) cres) ∧
      decl.nparams ≤ cdoms.length ∧
      ∀ i < decl.nparams, cres[i]? = some (.bvar (cdoms.length - 1 - i)) := by
  obtain ⟨cdoms, result, hty, hle, hvalid, hhead⟩ := H
  have hres := eq_mkApps_of_getAppFnArgs hhead
  refine ⟨cdoms, result.getAppFnArgs.2, by rw [hty, hu]; exact congrArg _ hres, hle, ?_⟩
  intro i hi
  rcases hga : result.getAppFnArgs with ⟨fn, args⟩
  simp only [VInductDecl.RawIndAppAt, hga] at hvalid
  obtain ⟨_, _, _, _, _, _, hal, htake⟩ := hvalid
  have := congrArg (·[i]?) htake
  simp only [List.getElem?_take, hi, if_true] at this
  rw [this]
  simp only [VInductDecl.paramVars, List.getElem?_map]
  rw [List.getElem?_reverse (by simpa using hi)]
  simp only [List.length_range]
  rw [List.getElem?_range (by omega)]
  simp only [Option.map_some]
  congr 2; omega

set_option maxHeartbeats 8000000 in
/-- **Validity of the ι rules of a nested block.** -/
theorem PatValid.nested {envF env0 env' : VEnv} {decl : VInductDecl}
    (hF : envF.WF) (h0 : env0.WF) (hdecl : decl.WF env0)
    (hadd : env0.addInduct decl = some env') (hle : env' ≤ envF)
    (V0 : EnvValid envF env0)
    (hprojV : ∀ S info, env'.projections S info → ProjValid envF S info)
    (hpats : ∀ (p : Pattern) (r : p.RHS × p.Check), envF.pats p r →
      (∃ ci, env'.constants p.headConst = some ci) → env'.pats p r)
    (hdefs : ∀ df, envF.defeqs df → ∀ n ls, df.lhs.stripLams.getAppFnArgs.1 = .const n ls →
      (∃ ci, env'.constants n = some ci) → env'.defeqs df)
    (hrigT : ∀ t ∈ decl.types, envF.Rigid t.name)
    (hctor : ∀ c, IsCtor envF c → envF.Rigid c) (hpctor : ∀ c, IsProjCtor envF c → envF.Rigid c)
    {rec : VRecursor} {ru : VRecRule} (hrec : rec ∈ decl.recs) (hru : ru ∈ rec.rules)
    (hc : ru.rhs.Closed)
    {block : VInductBlock} {base : VEnv} {expanded : VInductDecl} {s : InductiveSignature}
    {g : InductiveSignature.Instance s} {aux : List InductiveSignature.ContainerSpecialization}
    (haux : aux ≠ [])
    (hcomp : CompiledInductive env0 decl block)
    (hrecsOf : decl.RecsOf block) (hbwf : block.WF env0) (hbase : base ≤ env0)
    (C : InductiveSignature.CompilationData base decl expanded s g aux block)
    (hcont : ContainersInstalled base aux)
    {df : VDefEq} (hdf : df ∈ block.rules) (H : VRecRule.OfEquation rec ru df) :
    PatValid envF
      (SimplePattern.iota rec.name rec.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
      (SimplePattern.iotaRHS rec.name ru.ctor rec.numParams rec.numMotives rec.numMinors
        rec.numIndices ru.ctorParams ru.nfields ru.rhs hc, .true) := by
  have henvF := hF.orderedStrong
  have h0F : env0 ≤ envF := (addInduct_le hadd).trans hle
  have hbF : base ≤ envF := hbase.trans h0F
  -- the generated equation behind the rule
  obtain ⟨geq, hgeq, hres⟩ := Lean4Lean.List.Forall₂.forall_exists_r
    (List.mapM_eq_some.mp C.equations) df hdf
  obtain ⟨index, -, rfl⟩ := List.mem_map.1 hgeq
  have hnp : decl.nparams = s.params.length := (C.model.nparams.trans C.nparams).symm
  have hsu : s.uvars = decl.uvars := C.model.uvars.trans C.uvars
  obtain ⟨hglv⟩ : ∃ _ : g.levels.length = s.uvars, True :=
    ⟨(C.admissible.choose_spec.2).levels_length, trivial⟩
  -- the constructor's stage
  obtain ⟨envT, envC, envR, sT, sC, sR, sP⟩ := addInduct_stages hadd
  have hTC : decl.addTypesCtors env0 = some envC := by
    unfold VInductDecl.addTypesCtors; rw [sT]; exact sC
  have hCF : envC ≤ envF := addProjs_le.trans ((addRecs_le sR).trans ((addRules_le sP).trans hle))
  obtain ⟨ci2, hci2, hsh⟩ := hdecl.rules_ctor envC hTC rec hrec ru hru
  have hsh' : ci2.type.forallArity = ru.ctorParams + ru.nfields := by
    rw [← VExpr.piArity_eq_forallArity]; exact hsh.1
  -- the registered patterns of the declaration's constructors
  have hallpat : ∀ c2 ∈ decl.constructorConstants, IsPatCtor envF c2.name := by
    intro c2 hc2
    obtain ⟨df2, hdf2, hmaj⟩ := hcomp.constructor_equation c2 hc2
    obtain ⟨r2, hr2, ru2, hru2, hof⟩ := hrecsOf.rules_total df2 hdf2
    have hn := hmaj.ofEquation hof
    have hc2' := VEnv.addRules_closed sP r2 hr2 ru2 hru2
    exact ⟨_, _, r2.name, r2.getMajorIdx, ru2.ctorParams + ru2.nfields,
      hle.pats (addInduct_pat hr2 hru2 hc2' hadd), by rw [hn]⟩
  obtain ⟨envTypes, htypes, hcase⟩ := ctor_cases C index
  rcases hcase with ⟨t, ht, fc, hfc, hfn, hcn, hrelF, hRT, hSFt, hSCt⟩ |
      ⟨a, ha, c, hc', T, hfa, hcn, hT, hRT, hLev, hnI, hwf, hSFa, hSCa⟩
  · -- a source constructor
    have hSF : Spec (compilationRestoration decl aux) s.families[s.constructors[index].owner].name
        s.params.length t.name id (vars s.params.length 0) := by rw [hfn]; exact hSFt
    have hSC : Spec (compilationRestoration decl aux) s.constructors[index].name
        s.params.length fc.name id (vars s.params.length 0) := by rw [hcn]; exact hSCt
    obtain ⟨hname, hctorN, -, -, -, hcp, hnf, -⟩ :=
      rule_counts hdecl hrecsOf C hrec hru index hSC hres H
    have hfcu : fc.uvars = decl.uvars := hdecl.source.2.2.2.1 fc (List.mem_flatMap.2 ⟨t, ht, hfc⟩)
    obtain ⟨_, _, _, hshapes, _, hraws⟩ := C.sourceParameters
    obtain ⟨cdoms, cres, hcty, hcle, hcresP⟩ := rawCtorShape_data (hraws t ht fc hfc) hfcu
    have hcc : envF.constants fc.name = some fc.toVConstant :=
      hle.constants (addInduct_ctor_find hadd ht hfc)
    have hcC : envC.constants fc.name = some fc.toVConstant :=
      (addCtors_find sC t ht fc hfc)
    rw [hctorN] at hci2
    cases hcC.symm.trans hci2
    have hcdl : cdoms.length = s.params.length + s.constructors[index].fields.length := by
      have := hsh'
      change fc.type.forallArity = _ at this
      rw [hcty, VExpr.forallArity_wrapForalls, forallArity_mkApps_const', hcp, hnf] at this
      simp [length_vars] at this; omega
    -- the stage environments
    obtain ⟨hTs, -⟩ := stages_orderedStrong h0 hdecl sT sC sR
    obtain ⟨VT, -⟩ := stages_envValid V0 hprojV sT sC sR sP
    have hTF : envT ≤ envF := (addCtors_le sC).trans hCF
    -- the installed constructor's type is closed
    have hccl : (VExpr.wrapForalls cdoms (.mkApps (.const t.name (VLevel.params fc.uvars)) cres)).ClosedN := by
      rw [← hcty]; exact henvF.ordered.closedC hcc
    obtain ⟨hcRcl, hcDcl⟩ := closedN_wrapForalls hccl
    simp only [Nat.zero_add] at hcRcl hcDcl
    have hvl : (vars s.params.length 0).length = s.params.length := length_vars _ _
    have hpL : ∀ L : List VLevel, L.length = s.uvars → (VLevel.params s.uvars).map (·.inst L) = L :=
      fun L h => VLevel.inst_map_id h
    have hB0 : ∀ L : List VLevel, L.length = s.uvars → fc.type.instL L = .wrapForalls
        ((cdoms.take s.params.length).map (·.instL L) ++
          ((cdoms.drop (vars s.params.length 0).length).zipIdx.map fun ((d, j) : VExpr × Nat) =>
            (d.instL ((VLevel.params s.uvars).map (·.inst L))).subst
              ((VExpr.argSubst ((vars s.params.length 0).map (·.instL L))).liftN j)))
        (((VExpr.mkApps (.const t.name (VLevel.params fc.toVConstant.uvars)) cres).instL
          ((VLevel.params s.uvars).map (·.inst L))).subst
            ((VExpr.argSubst ((vars s.params.length 0).map (·.instL L))).liftN
              s.constructors[index].fields.length)) := by
      intro L hL
      rw [hpL L hL, vars_instL, hvl, hcty, VExpr.instL_wrapForalls]
      congr 1
      · conv => lhs; rw [← List.take_append_drop s.params.length cdoms]
        rw [List.map_append]
        congr 1
        apply List.ext_getElem (by simp)
        intro j h1 h2
        simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_drop, Nat.zero_add]
        rw [subst_spec_vars]
        have := hcDcl (s.params.length + j) (by simp at h1; omega)
        exact this.instL
      · rw [subst_spec_vars]
        have := hcRcl.instL (ls := L)
        rwa [hcdl] at this
    -- the family's telescope
    obtain ⟨N, ownP, afterP, idxs, res, X, hN, htf1, htf2, -, -⟩ := hshapes t ht
    obtain ⟨e1, l1⟩ := VExpr.takeForalls_eq_wrapForalls htf1
    obtain ⟨e2, l2⟩ := VExpr.takeForalls_eq_wrapForalls htf2
    subst e1 e2
    rw [← VExpr.wrapForalls_append] at hN
    have hfam := hrelF.indices
    simp only [declarationFamily] at hfam
    refine nested_finish hF h0 hdecl hadd hle V0 hprojV hpats hdefs hctor hpctor hrec hru hc
      haux hcomp hrecsOf hbwf hbase C hdf H index hres htypes hSF hSC
      (lvC0 := VLevel.params s.uvars) (fun lv h => (VLevel.inst_map_id h).symm) hRT
      (cc := fc.toVConstant) (cdoms := cdoms) (cres := cres)
      (by simp only [List.length_take]; omega) hB0 (cI := t.toVConstant)
      (hle.constants (addInduct_type_find hadd ht)) (hN.mono hbase)
      (by simp only [hvl, List.length_append, l1, l2, hnp]; omega) (hrigT t ht) hcc
      (by show fc.type = _; rw [hcty]) (by simp [hfcu, hsu])
      (fun i hi => by
        rw [hvl] at hi ⊢
        rw [hcresP i (by rw [hnp]; exact hi), hcdl])
      (L := t.resultLevel) ?_ ?_ ?_
    · -- the projection facts
      have hfcA : fc.type.forallArity = decl.nparams + s.constructors[index].fields.length := by
        rw [hcty, VExpr.forallArity_wrapForalls, forallArity_mkApps_const', hcdl, hnp]; rfl
      have := projMajor_decl hF hdecl hadd hle hprojV ht hfc
        (fun c2 hc2 => hallpat c2 (List.mem_flatMap.2 ⟨t, ht, hc2⟩)) hfcA
      rw [hvl, ← hnp]; exact this
    · -- the semantic sort
      exact famSort_congr (famSort_decl henvF sT hTs VT hTF hbase htypes ht hrelF)
        hrelF.resultLevel
    · rw [hpL _ hglv]
      exact VLevel.inst_congr_l (Eq.symm hrelF.resultLevel)
  · -- an auxiliary constructor: the container's constructor at the specialization
    have hSF : Spec (compilationRestoration decl aux) s.families[s.constructors[index].owner].name
        s.params.length a.source.name (fun lv => a.levels.map (·.inst lv)) a.arguments := by
      rw [hfa]; exact hSFa
    have hSC : Spec (compilationRestoration decl aux) s.constructors[index].name
        s.params.length c.name (fun lv => a.levels.map (·.inst lv)) a.arguments := by
      rw [hcn]; exact hSCa
    obtain ⟨hname, hctorN, -, -, -, hcp, hnf, -⟩ :=
      rule_counts hdecl hrecsOf C hrec hru index hSC hres H
    -- the container
    obtain ⟨base0, installed, base', block', expanded', s', g', aux', hb', C', -, hadd', hle'⟩ :=
      containers_mem hcont ha
    have hsrc : a.source ∈ a.container.types := List.getElem_mem a.family.isLt
    obtain ⟨_, _, _, hshapes', _, hraws'⟩ := C'.sourceParameters
    have hcu : c.uvars = a.container.uvars :=
      C'.sourceWF.2.2.2.1 c (List.mem_flatMap.2 ⟨a.source, hsrc, hc'⟩)
    obtain ⟨cdoms, cres, hcty, hcle, hcresP⟩ := rawCtorShape_data (hraws' a.source hsrc c hc') hcu
    have hargl : a.arguments.length = a.container.nparams := hwf.1
    have hiE : installed ≤ env0 := hle'.trans hbase
    have hiF : installed ≤ envF := hiE.trans h0F
    have hcc : envF.constants c.name = some c.toVConstant :=
      hiF.constants (addInduct_ctor_find hadd' hsrc hc')
    have h0C : env0 ≤ envC := (addTypes_le sT).trans (addCtors_le sC)
    have hcC : envC.constants c.name = some c.toVConstant :=
      (hiE.trans h0C).constants (addInduct_ctor_find hadd' hsrc hc')
    rw [hctorN] at hci2
    cases hcC.symm.trans hci2
    have hcdl : cdoms.length = a.arguments.length + s.constructors[index].fields.length := by
      have := hsh'
      change c.type.forallArity = _ at this
      rw [hcty, VExpr.forallArity_wrapForalls, forallArity_mkApps_const', hcp, hnf] at this
      omega
    -- the specialized constructor type
    rw [hcty] at hT
    have eT := specializeType_shape (by omega) hT
    have hB0 : ∀ L : List VLevel, L.length = s.uvars → (VExpr.wrapForalls s.params T).instL L =
        .wrapForalls (s.params.map (·.instL L) ++
          ((cdoms.drop a.arguments.length).zipIdx.map fun ((d, j) : VExpr × Nat) =>
            (d.instL (a.levels.map (·.inst L))).subst
              ((VExpr.argSubst (a.arguments.map (·.instL L))).liftN j)))
        (((VExpr.mkApps (.const a.source.name (VLevel.params c.toVConstant.uvars)) cres).instL
          (a.levels.map (·.inst L))).subst
            ((VExpr.argSubst (a.arguments.map (·.instL L))).liftN
              s.constructors[index].fields.length)) := by
      intro L _
      rw [eT, VExpr.instL_wrapForalls, VExpr.instL_wrapForalls, ← VExpr.wrapForalls_append,
        instL_spec, VExpr.instL_instL, show cdoms.length - a.arguments.length =
          s.constructors[index].fields.length by omega]
      congr 2
      rw [List.map_map]
      apply List.map_congr_left
      intro x _
      simp only [Function.comp, instL_spec, VExpr.instL_instL]
    -- the container family's telescope
    obtain ⟨N, ownP, afterP, idxs, res, X, hN, htf1, htf2, -, -⟩ := hshapes' a.source hsrc
    obtain ⟨e1, l1⟩ := VExpr.takeForalls_eq_wrapForalls htf1
    obtain ⟨e2, l2⟩ := VExpr.takeForalls_eq_wrapForalls htf2
    subst e1 e2
    rw [← VExpr.wrapForalls_append] at hN
    -- the container family is rigid
    obtain ⟨dsF, HF⟩ := hF
    have hpc : IsPatCtor envF c.name := by
      obtain ⟨p, r, recN, M, N', hp, hpe⟩ := hcont.constructor_isPatCtor ha hc'
      exact ⟨p, r, recN, M, N', hbF.pats hp, hpe⟩
    have hIrig : envF.Rigid a.source.name := by
      obtain ⟨ci, hci, F, ls, hhead, -, hrig⟩ := patCtor_resultRigid HF hpc
      cases hcc.symm.trans hci
      have := (rawCtorShape_head (hraws' a.source hsrc c hc')).symm.trans hhead
      cases this
      exact hrig
    have hF : envF.WF := ⟨dsF, HF⟩
    have hpat' : ∀ c2 ∈ a.source.ctors, IsPatCtor envF c2.name := by
      intro c2 hc2
      obtain ⟨p, r, recN, M, N', hp, hpe⟩ := hcont.constructor_isPatCtor ha hc2
      exact ⟨p, r, recN, M, N', hbF.pats hp, hpe⟩
    refine nested_finish hF h0 hdecl hadd hle V0 hprojV hpats hdefs hctor hpctor hrec hru hc
      haux hcomp hrecsOf hbwf hbase C hdf H index hres htypes hSF hSC
      (lvC0 := a.levels) (fun lv _ => rfl) hRT
      (cc := c.toVConstant) (cdoms := cdoms) (cres := cres) (PB := s.params)
      rfl hB0 (cI := a.source.toVConstant)
      (hiF.constants (addInduct_type_find hadd' hsrc))
      (hN.mono (hb'.trans ((addInduct_le hadd').trans hiE)))
      (by simp only [List.length_append, l1, l2, hnI, hargl]; omega) hIrig hcc
      (by show c.type = _; rw [hcty]) (by show a.levels.length = c.uvars; rw [hwf.2.2.1, hcu])
      (fun i hi => by rw [hcresP i (by omega), hcdl])
      (L := a.source.resultLevel) ?_
      (famSort_installed henvF h0.orderedStrong h0F V0 hb' C' hadd' hiE hsrc) ?_
    · have hshape : c.type.forallArity = a.container.nparams + s.constructors[index].fields.length := by
        rw [hcty, VExpr.forallArity_wrapForalls, forallArity_mkApps_const', hcdl, hargl]; rfl
      have := projMajor_installed hF (fun t ht c hc => hraws' t ht c hc) hadd' hiF
        (fun S info h => V0.proj S info (hiE.projections h)) hsrc hc' hpat' hshape
      rw [hargl]; exact this
    · rw [← VLevel.inst_inst]
      exact VLevel.inst_congr_l (Eq.symm hLev)

end Model
end VEnv
end Lean4Lean
