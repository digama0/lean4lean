import Lean4Lean.Theory.Typing.ConstructorRigidity
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.Typing.RecursorRegistryInstallation
import Lean4Lean.Theory.Typing.QuotLiftTelescope
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Typing.SignatureArity
import Lean4Lean.Theory.Typing.CaseSourceSort

/-! The major family of a registered recursor owning a constructor is
a rigid constant. The proof uses an installed recursor equation of that
owner, whose constructor returns the family. -/

namespace Lean4Lean
namespace VEnv
open InductiveSignature

theorem RecursorRegistered.family_head_rigid {data : RecursorData} (henv : env.WF)
    (H : RecursorRegistered env data)
    (index : Fin data.schema.signature.constructors.size)
    {owner : Fin data.schema.signature.families.size}
    (hown : data.schema.signature.constructors[index].owner = owner) :
    (∃ ci, env.constants
      (data.schema.restoration.headName data.schema.signature.families[owner].name) =
        some ci) ∧
    env.Rigid (data.schema.restoration.headName data.schema.signature.families[owner].name) := by
  subst hown
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, hprior, hbase, hr, _, _, _, _, hi, he⟩ := H
  have hle : base ≤ env := hbase.trans ((VInductBlock.install_base_le hi).trans he)
  rw [hr]
  rcases hdata.family_head_cases hdata.recursorNamesFresh hprior index with
    ⟨family, hsrc, hfn, hhn, fc, hfc, hcn⟩ |
    ⟨cctor, equation, hdefeq, hmaj, hconst, ls, hres⟩
  · rw [hfn, hhn]
    have hgenerated : g.equation index ∈ g.equations :=
      List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩
    obtain ⟨actual, hmem, hrestore⟩ := Lean4Lean.List.Forall₂.forall_exists_l
      (List.mapM_eq_some.mp hdata.equations) _ hgenerated
    have hmajor := Instance.restored_equation_major hdata index hrestore
    rw [hcn] at hmajor
    have hdf : env.defeqs actual := he.defeqs (VInductBlock.install_rule hi hmem)
    obtain ⟨ci, hci, F, ls', hF, ⟨ciF, hciF⟩, hFr⟩ :=
      henv.installed_constructor_result_rigid hdf hmajor
    have hfcc : fc ∈ source.constructorConstants := List.mem_flatMap.mpr ⟨family, hsrc, hfc⟩
    have hconst : env.constants fc.name = some fc.toVConstant :=
      he.constants (VInductBlock.install_ctor_lookup hi (by rw [hdata.ctors]; exact hfcc))
    rw [hconst] at hci
    cases hci
    obtain ⟨_, _, _, _, _, hraw⟩ := hdata.sourceParameters
    obtain ⟨doms, result, heq, _, _, hhead⟩ := hraw family hsrc fc hfc
    have h2 := hhead
    rw [← VExpr.forallResult_of_head hhead, ← VExpr.forallResult_wrapForalls doms, ← heq] at h2
    obtain rfl := (VExpr.const.inj (hF.symm.trans h2)).1
    exact ⟨⟨ciF, hciF⟩, hFr⟩
  · have hdf : env.defeqs equation := hle.defeqs hdefeq
    obtain ⟨ci, hci, F, ls', hF, ⟨ciF, hciF⟩, hFr⟩ :=
      henv.installed_constructor_result_rigid hdf hmaj
    rw [hle.constants hconst] at hci
    cases hci
    obtain rfl := (VExpr.const.inj (hF.symm.trans hres)).1
    exact ⟨⟨ciF, hciF⟩, hFr⟩

end VEnv
end Lean4Lean

namespace Lean4Lean.InductiveSignature

theorem Restoration.wrapForalls_forall₂ {r : Restoration}
    (H : r.expr (VExpr.wrapForalls domains body) = some output) :
    ∃ domains' body', output = VExpr.wrapForalls domains' body' ∧
      List.Forall₂ (fun d d' => r.expr d = some d') domains domains' ∧ r.expr body = some body' := by
  induction domains generalizing output with
  | nil => exact ⟨[], output, rfl, .nil, H⟩
  | cons domain domains ih =>
    change (do let domain' ← r.expr domain; let body' ← r.expr (VExpr.wrapForalls domains body)
               pure (.forallE domain' body')) = some output at H
    simp only [bind, Option.bind_eq_some_iff] at H
    obtain ⟨domain', hd, out, hout, H⟩ := H
    cases H
    obtain ⟨domains', body', rfl, hrel, hb⟩ := ih hout
    exact ⟨domain' :: domains', body', rfl, .cons hd hrel, hb⟩

end Lean4Lean.InductiveSignature

namespace Lean4Lean.VEnv
open InductiveSignature

/-- The restored recursor type is a telescope whose major domain is an
application of the restored family head of its owner. -/
theorem RecursorData.recursorType_major {data : RecursorData}
    (H : data.recursorType = some type) :
    ∃ domains body args, type = VExpr.wrapForalls domains body ∧
      domains.length = data.majorOffset + 1 ∧
      domains[data.majorOffset]? = some (VExpr.mkApps (.const
        (data.schema.restoration.headName data.schema.signature.families[data.owner].name)
        (data.schema.restoration.headLevels data.schema.signature.families[data.owner].name
          data.levels)) args) := by
  unfold RecursorData.recursorType Instance.recursorType at H
  obtain ⟨domains, body, rfl, hrel, _⟩ := Restoration.wrapForalls_forall₂ H
  obtain ⟨pre', x', rfl, hpre, hx⟩ := List.forall₂_snoc_left hrel
  have hpl := Lean4Lean.List.Forall₂.length_eq hpre
  have hoff : pre'.length = data.majorOffset := by
    rw [← hpl]
    simp [Instance.params, Instance.motives, Instance.minors, insertBinders,
      RecursorData.majorOffset, RecursorData.indexOffset,
      RecursorData.numParams, RecursorData.numIndices, Nat.add_assoc]
  obtain ⟨args, hmajor⟩ := Restoration.const_mkApps_exact hx
  refine ⟨pre' ++ [x'], body, args, rfl, by simp [hoff], ?_⟩
  rw [List.getElem?_append_right (by omega)]
  simp [hoff, hmajor]; rfl

/-- The major of a typed recursor application at its major offset has
an application of the owner's restored family head as type. -/
theorem RecursorRegistered.major_type {data : RecursorData} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (H : RecursorRegistered env data)
    (ht : env.HasType U Γ (.app (VExpr.mkApps (.const data.name ls) vs) M) T)
    (hlen : vs.length = data.majorOffset) :
    (∀ l ∈ ls, l.WF U) ∧ ls.length = data.uvars ∧ ∃ args,
    env.HasType U Γ M (VExpr.mkApps (.const
      (data.schema.restoration.headName data.schema.signature.families[data.owner].name)
      ((data.schema.restoration.headLevels data.schema.signature.families[data.owner].name
        data.levels).map (·.inst ls))) args) := by
  obtain ⟨type, htype⟩ := H.recursorType_exists
  have hconst := H.recursorType htype
  obtain ⟨domains, body, args, rfl, hdl, hdom⟩ :=
    RecursorData.recursorType_major htype
  have happ : VExpr.mkApps (.const data.name ls) (vs ++ [M]) =
      .app (VExpr.mkApps (.const data.name ls) vs) M := by
    simp [VExpr.mkApps, List.foldl_append]
  have hWF : VExpr.WF env U Γ (VExpr.mkApps (.const data.name ls) (vs ++ [M])) :=
    ⟨_, happ ▸ ht⟩
  obtain ⟨_, hc⟩ := VExpr.WF.of_mkApps henv.ordered hΓ hWF
  obtain ⟨ci, hci, hw, hl⟩ := HasType.const_inv henv.ordered hΓ hc
  rw [hconst] at hci
  cases hci
  have hcT : env.HasType U Γ (.const data.name ls) (VExpr.wrapForalls
      (domains.map (·.instL ls)) (body.instL ls)) := by
    rw [← VExpr.instL_wrapForalls]; exact .const hconst hw hl
  have hlen' : (vs ++ [M]).length = (domains.map (·.instL ls)).length := by
    simp [hdl, hlen]
  obtain ⟨hargs, _⟩ := HasType.mkApps_wrapForalls henv hΓ hcT hWF hlen'
  have hM := hargs data.majorOffset (by simp; omega) (by simp; omega)
  have hlt : data.majorOffset < domains.length := by omega
  have hd : domains[data.majorOffset] = _ := (List.getElem?_eq_some_iff.mp hdom).2
  simp only [List.getElem_append_right (show vs.length ≤ data.majorOffset by omega),
    List.getElem_map, hlen, Nat.sub_self, List.getElem_singleton,
    List.take_left' hlen] at hM
  rw [hd, VExpr.instL_mkApps, VExpr.instL, VExpr.instOuter_mkApps, VExpr.instOuter_const] at hM
  exact ⟨hw, hl, _, hM⟩

/-- The major of a typed recursor application at its major offset is
never a function: its type is an application of the owner's family head,
which is rigid when the owner has a constructor. -/
theorem RecursorRegistered.major_not_pi {data : RecursorData} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (H : RecursorRegistered env data)
    (index : Fin data.schema.signature.constructors.size)
    (hown : data.schema.signature.constructors[index].owner = data.owner)
    (ht : env.HasType U Γ (.app (VExpr.mkApps (.const data.name ls) vs) M) T)
    (hlen : vs.length = data.majorOffset) :
    ¬ env.HasType U Γ M (.forallE A B) := by
  intro hpi
  obtain ⟨_, _, _, hM⟩ := H.major_type henv hΓ ht hlen
  have hrigid := (H.family_head_rigid henv index hown).2
  have ⟨_, hsort⟩ := hM.isType henv.ordered hΓ
  exact IsDefEqU.rigidApp_forallE_inv henv hΓ hrigid hsort (hM.uniqU henv hΓ hpi)

theorem QuotRegistered.quot_rigid (henv : env.WF) (hr : QuotRegistered env) :
    env.Rigid ``Quot := by
  have hmk : quotDefEq.HasConstructorMajor ``Quot.mk :=
    ⟨_, [.param 0], [.bvar 5, .bvar 4, .bvar 0], rfl⟩
  obtain ⟨ci, hci, F, ls, hF, _, hFr⟩ := henv.installed_constructor_result_rigid hr.equation hmk
  rw [hr.constructor] at hci
  cases hci
  have : quotMkConst.type.forallResult.getAppFnArgs.1 = .const ``Quot [.param 0] := rfl
  obtain rfl := (VExpr.const.inj (hF.symm.trans this)).1
  exact hFr

set_option maxHeartbeats 1000000 in
theorem QuotRegistered.major_type (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hr : QuotRegistered env) (hu : u.WF U) (hv : v.WF U)
    (H : VExpr.WF env U Γ (VExpr.mkApps (.const ``Quot.lift [u,v])
      [alpha, relation, beta, fn, compat, major])) :
    env.HasType U Γ major (VExpr.mkApps (.const ``Quot [u]) [alpha, relation]) := by
  obtain ⟨result, hw⟩ := quotient_walk henv hΓ hr hu hv H
  cases hw with | cons ha hw =>
    cases hw with | cons hrel hw =>
      cases hw with | cons hbeta hw =>
        cases hw with | cons hf hw =>
          cases hw with | cons hcompat hw =>
            cases hw with | cons hmajor hw =>
              simp [VExpr.instL, VExpr.inst, VLevel.inst, VExpr.inst_lift,
                ← VExpr.lift_instN_lo] at hmajor
              simpa [VExpr.mkApps] using hmajor

/-- The restored recursor type returns its owner's motive applied to
the indices and the major, and that motive's binder is a telescope ending in
the recursor's target sort. -/
theorem RecursorData.recursorType_shape {data : RecursorData}
    (H : data.recursorType = some type) :
    ∃ domains motiveDomains, type = VExpr.wrapForalls domains (VExpr.mkApps
        (.bvar (data.numIndices + 1 + data.schema.signature.constructors.size +
          (data.schema.signature.families.size - 1 - data.owner.val)))
        (vars data.numIndices 1 ++ [.bvar 0])) ∧
      domains.length = data.majorOffset + 1 ∧
      domains[data.numParams + data.owner.val]? =
        some (VExpr.wrapForalls motiveDomains (.sort data.target)) ∧
      motiveDomains.length = data.numIndices + 1 := by
  unfold RecursorData.recursorType Instance.recursorType at H
  obtain ⟨domains, body, rfl, hrel, hbody⟩ := Restoration.wrapForalls_forall₂ H
  have hbodyEq : body = VExpr.mkApps
      (.bvar (data.numIndices + 1 + data.schema.signature.constructors.size +
          (data.schema.signature.families.size - 1 - data.owner.val)))
      (vars data.numIndices 1 ++ [.bvar 0]) := by
    change Restoration.expr.go _ (VExpr.mkApps _ _) [] = _ at hbody
    rw [restoration_mkApps] at hbody
    simp only [List.mapM_append, InductiveSignature.Restoration.mapM_expr_vars, bind, Option.bind_some,
      List.mapM_cons, List.mapM_nil] at hbody
    simpa [Restoration.expr, Restoration.expr.go, VExpr.mkApps, insertBinders,
      RecursorData.numIndices] using hbody.symm
  subst hbodyEq
  have hlen := Lean4Lean.List.Forall₂.length_eq hrel
  have hpos : data.numParams + data.owner.val < domains.length := by
    rw [← hlen]
    simp [Instance.params, Instance.motives, Instance.minors, insertBinders,
      RecursorData.numParams]
    omega
  have hrel' := Lean4Lean.List.Forall₂.getElem_of hrel (data.numParams + data.owner.val)
    (by rw [hlen]; exact hpos) hpos
  have hsrc : (data.recursorInstance.params ++ data.recursorInstance.motives ++
      data.recursorInstance.minors ++ insertBinders (data.schema.signature.families[data.owner].indices.map
        (VExpr.instL data.recursorInstance.levels)) (data.schema.signature.families.size +
          data.schema.signature.constructors.size) ++
      [data.recursorInstance.familyApp data.owner _ _])[data.numParams + data.owner.val]'(by
        rw [hlen]; exact hpos) =
      data.recursorInstance.motive data.schema.signature.families[data.owner] data.owner.val := by
    simp only [List.append_assoc]
    rw [List.getElem_append_right (by simp [Instance.params, RecursorData.numParams])]
    rw [List.getElem_append_left (by simp [Instance.params, Instance.motives,
      RecursorData.numParams])]
    simp [Instance.params, Instance.motives, RecursorData.numParams]
  rw [hsrc] at hrel'
  unfold Instance.motive at hrel'
  obtain ⟨mds, sbody, heqm, hmrel, hsort⟩ := Restoration.wrapForalls_forall₂ hrel'
  simp only [Restoration.expr, Restoration.expr.go, VExpr.mkApps, Option.some.injEq] at hsort
  subst hsort
  refine ⟨domains, mds, rfl, ?_, ?_, ?_⟩
  · rw [← hlen]
    simp [Instance.params, Instance.motives, Instance.minors, insertBinders,
      RecursorData.majorOffset, RecursorData.indexOffset,
      RecursorData.numParams, RecursorData.numIndices, Nat.add_assoc]
  · rw [List.getElem?_eq_getElem hpos, heqm]; rfl
  · have := Lean4Lean.List.Forall₂.length_eq hmrel
    simp [insertBinders, RecursorData.numIndices] at this ⊢
    omega

/-- A saturated recursor application has a type living in the
recursor's target universe. -/
theorem RecursorRegistered.result_sort {data : RecursorData} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (H : RecursorRegistered env data)
    (ht : env.HasType U Γ (VExpr.mkApps (.const data.name ls) args) T)
    (hlen : args.length = data.majorOffset + 1) :
    ∃ T', env.HasType U Γ (VExpr.mkApps (.const data.name ls) args) T' ∧
      env.HasType U Γ T' (.sort (data.target.inst ls)) := by
  obtain ⟨type, htype⟩ := H.recursorType_exists
  have hconst := H.recursorType htype
  obtain ⟨domains, mds, rfl, hdl, hmot, hmdl⟩ := RecursorData.recursorType_shape htype
  obtain ⟨_, hc⟩ := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, ht⟩
  obtain ⟨ci, hci, hw, hl⟩ := HasType.const_inv henv.ordered hΓ hc
  rw [hconst] at hci
  cases hci
  have hcT : env.HasType U Γ (.const data.name ls) (VExpr.wrapForalls
      (domains.map (·.instL ls)) ((VExpr.mkApps
        (.bvar (data.numIndices + 1 + data.schema.signature.constructors.size +
          (data.schema.signature.families.size - 1 - data.owner.val)))
        (vars data.numIndices 1 ++ [.bvar 0])).instL ls)) := by
    rw [← VExpr.instL_wrapForalls]; exact .const hconst hw hl
  have hbodyL : (VExpr.mkApps
        (.bvar (data.numIndices + 1 + data.schema.signature.constructors.size +
          (data.schema.signature.families.size - 1 - data.owner.val)))
        (vars data.numIndices 1 ++ [.bvar 0])).instL ls = VExpr.mkApps
        (.bvar (data.numIndices + 1 + data.schema.signature.constructors.size +
          (data.schema.signature.families.size - 1 - data.owner.val)))
        (vars data.numIndices 1 ++ [.bvar 0]) := by
    have hvars : (vars data.numIndices 1).map (VExpr.instL ls) = vars data.numIndices 1 := by
      simp [vars, List.map_map, VExpr.instL]
    simp only [VExpr.instL_mkApps, VExpr.instL, List.map_append, hvars, List.map_cons,
      List.map_nil]
  rw [hbodyL] at hcT
  have hlenL : args.length = (domains.map (·.instL ls)).length := by simp [hdl, hlen]
  obtain ⟨hargs, hres⟩ := HasType.mkApps_wrapForalls henv hΓ hcT ⟨_, ht⟩ hlenL
  refine ⟨_, hres, ?_⟩
  have ⟨_, hT⟩ := hcT.isType henv.ordered hΓ
  obtain ⟨hctx, lv, hbody⟩ := IsType.wrapForalls_inv henv hΓ ⟨_, hT⟩
  have hpos : data.numParams + data.owner.val < domains.length := by
    have := data.owner.isLt
    simp [hdl, RecursorData.majorOffset, RecursorData.indexOffset]; omega
  have hposL : data.numParams + data.owner.val < (domains.map (·.instL ls)).length := by
    simpa using hpos
  have hvar : env.HasType U ((domains.map (·.instL ls)).reverse ++ Γ)
      (.bvar ((domains.map (·.instL ls)).length - 1 - (data.numParams + data.owner.val)))
      ((domains.map (·.instL ls))[data.numParams + data.owner.val].liftN
        ((domains.map (·.instL ls)).length - (data.numParams + data.owner.val))) :=
    .bvar (Lookup.reverse_append _ Γ _ hposL)
  have hd : (domains.map (·.instL ls))[data.numParams + data.owner.val] =
      VExpr.wrapForalls (mds.map (·.instL ls)) (.sort (data.target.inst ls)) := by
    rw [List.getElem_map, (List.getElem?_eq_some_iff.mp hmot).2, VExpr.instL_wrapForalls]; rfl
  rw [hd] at hvar
  obtain ⟨mds', hm'⟩ := VExpr.liftN_wrapForalls_sort (mds.map (·.instL ls)) (data.target.inst ls)
    ((domains.map (·.instL ls)).length - (data.numParams + data.owner.val)) 0
  rw [hm'] at hvar
  have hidx : (domains.map (·.instL ls)).length - 1 - (data.numParams + data.owner.val) =
      data.numIndices + 1 + data.schema.signature.constructors.size +
        (data.schema.signature.families.size - 1 - data.owner.val) := by
    have := data.owner.isLt
    simp [hdl, RecursorData.majorOffset, RecursorData.indexOffset]; omega
  rw [hidx] at hvar
  have hbody' : env.HasType U ((domains.map (·.instL ls)).reverse ++ Γ)
      (VExpr.mkApps (.bvar (data.numIndices + 1 + data.schema.signature.constructors.size +
          (data.schema.signature.families.size - 1 - data.owner.val)))
        (vars data.numIndices 1 ++ [.bvar 0])) (.sort lv) := hbody
  have hlength := HasType.mkApps_sort_arity henv hctx hvar hbody'
  have hsort := (HasType.mkApps_wrapForalls henv hctx hvar ⟨_, hbody'⟩ hlength).2
  rw [VExpr.instOuter_sort] at hsort
  have hfinal := IsDefEq.instOuter_telescope henv hsort hlenL hargs
  simpa only [VExpr.instOuter_sort, HasType] using hfinal

theorem _root_.Lean4Lean.InductiveSignature.Restoration.headLevels_inst
    (r : InductiveSignature.Restoration) (name : Name) (levels ls : List VLevel) :
    r.headLevels name (levels.map (·.inst ls)) = (r.headLevels name levels).map (·.inst ls) := by
  unfold InductiveSignature.Restoration.headLevels
  split <;> simp [List.map_map, Function.comp_def, VLevel.inst_inst]

/-- A recursor whose source universe is never zero at the occurrence
cannot eliminate a proof. -/
theorem RecursorRegistered.major_not_proof {data : RecursorData} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (H : RecursorRegistered env data)
    (ht : env.HasType U Γ (.app (VExpr.mkApps (.const data.name ls) vs) M) T)
    (hlen : vs.length = data.majorOffset)
    (hnz : ¬ (data.schema.sourceLevel data.owner data.levels).inst ls ≈ .zero)
    (hM : env.HasType U Γ M P) (hP : env.HasType U Γ P (.sort .zero)) : False := by
  obtain ⟨hw, hlw, args, hMt⟩ := H.major_type henv hΓ ht hlen
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, hprior, hbase, hr, _, hu, hl, _, hi, he⟩ := H
  have hle : base ≤ env := hbase.trans ((VInductBlock.install_base_le hi).trans he)
  have hconstants : ∀ family ∈ source.types,
      env.constants family.name = some family.toVConstant := fun family hf =>
    he.constants (VInductBlock.install_type_lookup hi (by
      rw [hdata.types]; exact List.mem_map.mpr ⟨family, hf, rfl⟩))
  obtain ⟨_, _, hadm⟩ := hdata.admissible
  have hlevels' : ∀ l ∈ data.levels.map (·.inst ls), l.WF U := by
    intro l hlm
    obtain ⟨l0, _, rfl⟩ := List.mem_map.mp hlm
    exact VLevel.WF.inst hw
  have hlen' : (data.levels.map (·.inst ls)).length = data.schema.signature.uvars := by
    rw [List.length_map, hl]; exact hadm.levels_length
  obtain ⟨domains, level, hH, hlevel⟩ := hdata.family_head_type hdata.recursorNamesFresh hprior henv hΓ hle hconstants
    data.owner hlevels' hlen'
  rw [Restoration.headLevels_inst, ← hr] at hH
  have ⟨_, hTs⟩ := hMt.isType henv.ordered hΓ
  have hlength := HasType.mkApps_sort_arity henv hΓ hH hTs
  have hsortT := (HasType.mkApps_wrapForalls henv hΓ hH ⟨_, hTs⟩ hlength).2
  rw [VExpr.instOuter_sort] at hsortT
  have heq := hM.uniqU henv hΓ hMt
  have hP' := hP.defeqU_l henv hΓ heq
  have hzero := (hsortT.uniqU henv hΓ hP').sort_inv henv hΓ
  apply hnz
  have : (data.schema.sourceLevel data.owner data.levels).inst ls =
      data.schema.signature.families[data.owner].resultLevel.inst (data.levels.map (·.inst ls)) := by
    simp [InductiveSignature.CaseSchema.sourceLevel, VLevel.inst_inst]
  rw [this]
  exact hlevel.symm.trans hzero

end Lean4Lean.VEnv
