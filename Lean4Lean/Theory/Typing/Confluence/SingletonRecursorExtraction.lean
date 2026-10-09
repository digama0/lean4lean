import Lean4Lean.Theory.Typing.Confluence.SingletonExtractionTyping
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Inductive.SingletonCompilation
import Lean4Lean.Theory.Typing.CaseSourceSort
import Lean4Lean.Theory.Typing.Confluence.GeneratedIotaPatterns
import Lean4Lean.Theory.Typing.Confluence.SingletonRecursorTyping
import Lean4Lean.Theory.Typing.SingletonExtraction.Recursor
import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.InductBlock
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Inductive.Restoration
import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Inductive.CompilationNames
import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.VExpr.Telescope
import Lean4Lean.Theory.Inductive.CaseRuleConstructors
import Lean4Lean.Theory.Inductive.RestorationHead
import Lean4Lean.Theory.Inductive.InstanceSpecialize
import Lean4Lean.Theory.Typing.SingletonExtraction.Basic
import Lean4Lean.Theory.Inductive.Signature
import Lean4Lean.Theory.Typing.SingletonExtraction.TelescopeTyping

/-! # Singleton extraction for a registered recursor

The abstract extraction interface (`PropElim`, `SingletonExtraction.lean`) is
instantiated at a registered recursor of a large-eliminating inductive
proposition: the field and index telescopes come from the generated signature at the
occurrence's source universes, and the eliminator into `Prop` is the recursor
itself with its free elimination universe (`Instance.FreeTarget`) set to zero. -/

namespace Lean4Lean
open VExpr InductiveSignature VEnv

namespace InductiveSignature.RecursorData
variable {env : VEnv}

/-- The family's declared header ends in a sort equivalent to its recorded result level. -/
theorem singleton_familyHead (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel packed ≈ .zero) :
    ∀ {U Γ levels}, env.WF → OnCtx Γ (env.IsType U) → (∀ l ∈ levels, l.WF U) →
    levels.length = data.schema.signature.uvars →
    ∃ domains level, env.HasType U Γ
      (.const data.schema.signature.families[data.owner].name levels)
      (VExpr.wrapForalls domains (.sort level)) ∧
      level ≈ data.schema.signature.families[data.owner].resultLevel.inst levels := by
  have hfam := (singletonSignature H hlarge hzero).families
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, _, hbase, hr, _, hu, hl, ht, hi, he⟩ := H
  have hinst := hi
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hinst
  obtain ⟨e1, he1, e2, he2, e3, he3, rfl⟩ := hinst
  have hle1 : e1 ≤ env := (VEnv.addConstVals_le he2).trans
    (VEnv.addEliminators_addProjections_le.trans ((VEnv.addConstVals_le he3).trans
      (VEnv.addDefEqRules_le.trans he)))
  have hbaseLE : base ≤ env := hbase.trans ((VEnv.addConstVals_le he1).trans hle1)
  intro U Γ levels henv hΓ hlevels hlen
  have hconstants : ∀ family ∈ source.types,
      env.constants family.name = some family.toVConstant := fun family hf =>
    he.constants (VInductBlock.install_type_lookup' hi (by
      rw [hdata.types]; exact List.mem_map.mpr ⟨family, hf, rfl⟩))
  obtain ⟨domains, level, hH, hlevel⟩ :=
    hdata.family_head_type hdata.recursorNamesFresh ‹_› henv hΓ hbaseLE hconstants data.owner hlevels hlen
  rw [hdata.restoration_of_singleton hfam] at hH
  exact ⟨domains, level, by simpa [Restoration.headName, Restoration.headLevels,
    Restoration.recursorName] using hH, hlevel⟩

theorem propElim_wf (henv : env.WF) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel packed ≈ .zero)
    (hpk : ∀ l ∈ packed, l.WF U) (hlen : packed.length = data.uvars)
    (hctor : ∃ i : Fin data.schema.signature.constructors.size,
      data.schema.signature.constructors[i].owner = data.owner) :
    ∃ S E, data.singletonLayout env packed = some S ∧ data.propElim packed = some E ∧
      PropElim.WF S (data.propParams packed) E env U := by
  have F := singletonSignature H hlarge hzero
  obtain ⟨k, hk, hkU, hfree⟩ := F.free
  obtain ⟨i, hi⟩ := hctor
  have hcs : data.schema.signature.constructors.size = 1 := by
    have := F.constructors; have := i.isLt; omega
  have hfam := F.families
  have htp : data.targetParam = some k := by simp [targetParam, hk]
  have hsc : data.singletonCtor = some i := by
    unfold singletonCtor
    have hfr : List.finRange data.schema.signature.constructors.size = [i] := by
      apply List.ext_getElem (by simp [hcs])
      intro n h1 h2
      simp only [List.length_finRange, hcs] at h1
      simp only [List.getElem_finRange, List.getElem_singleton]
      ext; simp; omega
    rw [hfr, List.filter_cons_of_pos (by simpa [Fin.getElem_fin] using hi), List.filter_nil]
  have hls0 : ∀ l ∈ packed.set k .zero, l.WF U := by
    intro l hl
    rcases List.mem_or_eq_of_mem_set hl with h | rfl
    · exact hpk l h
    · simp [VLevel.WF]
  have hlev : data.levels.map (·.inst (packed.set k .zero)) = data.levels.map (·.inst packed) :=
    List.map_congr_left fun l hl => hfree l hl packed .zero
  -- the instance at the occurrence, eliminating into `Prop`
  let gp := data.recursorInstance.specialize U (packed.set k .zero)
  have hgpl : gp.levels = data.levels.map (·.inst packed) := hlev
  have htarget : gp.targetLevel = .zero := by
    show (data.target).inst (packed.set k .zero) = .zero
    rw [hk]
    simp [VLevel.inst, List.getD_eq_getElem?_getD, hlen, hkU]
  have hhead : env.HasType U [] (.const data.name (packed.set k .zero))
      (gp.recursorType data.owner) := by
    have := HasType.const (env := env) (Γ := []) F.recursor hls0 (by simp [hlen])
    rwa [Instance.recursorType_specialize _ U] at this
  obtain ⟨c, hc⟩ : ∃ c, data.schema.signature.constructors[i] = c := ⟨_, rfl⟩
  have hown : c.owner = data.owner := hc ▸ hi
  have hFeq : (data.recursorInstance.fieldsAt c).map (·.instL packed) = gp.fieldsAt c := by
    simp [gp, Instance.fieldsAt, Instance.specialize, recursorInstance, List.map_map,
      Function.comp_def, VExpr.instL_instL, hlev]
  have hIeq : (data.recursorInstance.indicesAt data.owner).map (·.instL packed) =
      gp.indicesAt data.owner := by
    simp [gp, Instance.indicesAt, Instance.specialize, recursorInstance, List.map_map,
      Function.comp_def, VExpr.instL_instL, hlev]
  have hCIeq : (data.recursorInstance.ctorIndicesAt c).map (·.instL packed) = gp.ctorIndicesAt c := by
    simp [gp, Instance.ctorIndicesAt, Instance.specialize, recursorInstance, List.map_map,
      Function.comp_def, VExpr.instL_instL, hlev]
  have hPeq : data.propParams packed = gp.params := by
    simp [gp, propParams, Instance.params, Instance.specialize, recursorInstance, List.map_map,
      Function.comp_def, VExpr.instL_instL, hlev]
  have hS : data.singletonLayout env packed = some (gp.singletonCast data.owner c
      ((data.genericSorts env c).map (·.inst packed))) := by
    simp only [singletonLayout, singletonLayoutGeneric, hsc, hc, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, Option.map_some]
    simp only [SingletonLayout.instL, Instance.singletonCast, Option.some.injEq, SingletonLayout.mk.injEq]
    refine ⟨hFeq, hIeq, ?_, trivial⟩
    rw [← hFeq, ← hCIeq, List.length_map]
    congr 1; funext j; exact (fieldSlot_instL _ _ _ _).symm
  have hE : data.propElim packed = some (gp.singletonElim data.owner c
      (.const data.name (packed.set k .zero))) := by
    simp only [propElim, htp, hsc, hc, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rfl
  refine ⟨_, _, hS, hE, ?_⟩
  rw [hPeq]
  have hmem : c ∈ data.schema.signature.constructors.toList := hc ▸ Array.getElem_mem_toList ..
  have hnf : (gp.fieldsAt c).length = c.fields.length := by
    simp [Instance.fieldsAt, fieldTypes]
  have hnfG : (data.recursorInstance.fieldsAt c).length = c.fields.length := by
    simp [Instance.fieldsAt, fieldTypes]
  have harity : (gp.ctorIndicesAt c).length = (gp.indicesAt data.owner).length := by
    have := F.arity c hmem
    simp [Instance.ctorIndicesAt, Instance.indicesAt, this, hown]
  have hlw : ∀ l ∈ gp.levels, l.WF U := by
    rw [hgpl]
    intro l hl
    obtain ⟨l', _, rfl⟩ := List.mem_map.1 hl
    exact VLevel.WF.inst hpk
  have hfamHead : ∀ {Γ}, OnCtx Γ (env.IsType gp.uvars) → ∃ domains level,
      env.HasType gp.uvars Γ (.const data.schema.signature.families[data.owner].name gp.levels)
        (VExpr.wrapForalls domains (.sort level)) ∧ level ≈ .zero := by
    intro Γ hΓ
    obtain ⟨domains, level, hH, hlv⟩ := singleton_familyHead H hlarge hzero henv hΓ hlw
      (by rw [hgpl, List.length_map]; exact F.uvars)
    refine ⟨domains, level, hH, ?_⟩
    have e : data.schema.signature.families[data.owner].resultLevel.inst gp.levels =
        data.sourceLevel packed := by
      rw [hgpl]
      simp [sourceLevel, CaseSchema.sourceLevel, VLevel.inst_inst]
    rw [e] at hlv
    exact Eq.trans hlv hzero
  -- the generic instance, eliminating into `Prop`, for the choice of the data fields' sorts
  let gG := data.recursorInstance.specialize data.uvars ((VLevel.params data.uvars).set k .zero)
  have hgGl : gG.levels = data.levels := by
    show data.levels.map (·.inst ((VLevel.params data.uvars).set k .zero)) = data.levels
    conv => rhs; rw [← List.map_id data.levels]
    apply List.map_congr_left
    intro l hl
    rw [hfree l hl, VLevel.inst_id (F.levels_wf l hl)]
    rfl
  have hlsG : ∀ l ∈ (VLevel.params data.uvars).set k .zero, l.WF data.uvars := by
    intro l hl
    rcases List.mem_or_eq_of_mem_set hl with h | rfl
    · exact VLevel.params_wf h
    · simp [VLevel.WF]
  have htargetG : gG.targetLevel = .zero := by
    show (data.target).inst ((VLevel.params data.uvars).set k .zero) = .zero
    rw [hk]
    simp [VLevel.inst, List.getD_eq_getElem?_getD, hkU]
  have hheadG : env.HasType gG.uvars [] (.const data.name ((VLevel.params data.uvars).set k .zero))
      (gG.recursorType data.owner) := by
    have := HasType.const (env := env) (Γ := []) F.recursor hlsG (by simp)
    rwa [Instance.recursorType_specialize _ data.uvars] at this
  have hFG : gG.fieldsAt c = data.recursorInstance.fieldsAt c := by
    simp only [Instance.fieldsAt, hgGl]; rfl
  have hPG : gG.params = data.recursorInstance.params := by
    simp only [Instance.params, hgGl]; rfl
  have hctxG := gG.singleton_fieldsCtx henv hfam hcs data.owner i hc hown htargetG hheadG
  rw [hFG, hPG] at hctxG
  have hspec : ∀ j (hj : j < (data.recursorInstance.fieldsAt c).length) k',
      fieldSlot (data.recursorInstance.ctorIndicesAt c) (data.recursorInstance.fieldsAt c).length j =
        some k' →
      env.HasType data.uvars
        (data.recursorInstance.params ++ (data.recursorInstance.fieldsAt c).take j).reverse
        (data.recursorInstance.fieldsAt c)[j] (.sort ((data.genericSorts env c).getD j .zero)) := by
    intro j hj k' hslot
    have hget : (data.genericSorts env c).getD j .zero = Classical.epsilon fun u =>
        env.HasType data.uvars
          (data.recursorInstance.params ++ (data.recursorInstance.fieldsAt c).take j).reverse
          ((data.recursorInstance.fieldsAt c).getD j default) (.sort u) := by
      simp [genericSorts, List.getD_eq_getElem?_getD, List.getElem?_range hj, hslot]
    have hex : ∃ u, env.HasType data.uvars
        (data.recursorInstance.params ++ (data.recursorInstance.fieldsAt c).take j).reverse
        ((data.recursorInstance.fieldsAt c).getD j default) (.sort u) := by
      have := hctxG (j + 1) hj
      rw [List.take_succ_eq_append_getElem hj, ← List.append_assoc, List.reverse_append] at this
      obtain ⟨_, u, hu⟩ := this
      exact ⟨u, by rw [getD_of_lt hj]; exact hu⟩
    have := Classical.epsilon_spec hex
    rw [hget, ← getD_of_lt (d := default) hj]
    exact this
  have hlift : ∀ j (hj : j < (data.recursorInstance.fieldsAt c).length) (u : VLevel),
      env.HasType data.uvars
        (data.recursorInstance.params ++ (data.recursorInstance.fieldsAt c).take j).reverse
        (data.recursorInstance.fieldsAt c)[j] (.sort u) →
      env.HasType U (gp.params ++ (gp.fieldsAt c).take j).reverse
        ((gp.fieldsAt c)[j]'(by rw [hnf]; rw [hnfG] at hj; exact hj)) (.sort (u.inst packed)) := by
    intro j hj u h
    have h' := h.instL hpk
    have e1 : (List.map (VExpr.instL packed)
        (data.recursorInstance.params ++ (data.recursorInstance.fieldsAt c).take j).reverse) =
        (gp.params ++ (gp.fieldsAt c).take j).reverse := by
      rw [← hPeq, ← hFeq]
      simp [propParams, List.map_reverse, List.map_take]
    have e2 : (data.recursorInstance.fieldsAt c)[j].instL packed = (gp.fieldsAt c)[j]'(by
        rw [hnf]; rw [hnfG] at hj; exact hj) := by
      simp only [← hFeq, List.getElem_map]
    rw [e1, e2] at h'
    exact h'
  have hslotEq : ∀ j, fieldSlot (gp.ctorIndicesAt c) (gp.fieldsAt c).length j =
      fieldSlot (data.recursorInstance.ctorIndicesAt c) (data.recursorInstance.fieldsAt c).length j := by
    intro j
    rw [← hCIeq, ← hFeq, List.length_map, fieldSlot_instL]
  have hprop : ∀ j (hj : j < (gp.fieldsAt c).length),
      fieldSlot (gp.ctorIndicesAt c) (gp.fieldsAt c).length j = none →
      env.HasType gp.uvars (gp.params ++ (gp.fieldsAt c).take j).reverse (gp.fieldsAt c)[j]
        (.sort .zero) := by
    intro j hj hnone
    have hjc : j < c.fields.length := hnf ▸ hj
    obtain ⟨envTypes, hle, hsing⟩ := F.singleton
    rcases hsing.2.2 c hmem j hjc with hP | hbv
    · have hG : env.HasType data.uvars
          (data.recursorInstance.params ++ (data.recursorInstance.fieldsAt c).take j).reverse
          ((data.recursorInstance.fieldsAt c)[j]'(hnfG ▸ hjc)) (.sort .zero) := by
        have := hP.mono hle
        simpa [Instance.fieldsAt, Instance.params, recursorInstance, fieldTypes, List.map_take,
          List.reverse_append] using this
      exact hlift j (hnfG ▸ hjc) .zero hG
    · exfalso
      apply fieldSlot_none hnone
      rw [hnf]
      exact List.mem_map.2 ⟨_, hbv, rfl⟩
  have hsorts : ∀ j (hj : j < (gp.fieldsAt c).length) k',
      fieldSlot (gp.ctorIndicesAt c) (gp.fieldsAt c).length j = some k' →
      env.HasType gp.uvars (gp.params ++ (gp.fieldsAt c).take j).reverse (gp.fieldsAt c)[j]
        (.sort (((data.genericSorts env c).map (VLevel.inst packed)).getD j .zero)) := by
    intro j hj k' hslot
    have hjG : j < (data.recursorInstance.fieldsAt c).length := hnfG ▸ hnf ▸ hj
    rw [hslotEq] at hslot
    have := hlift j hjG _ (hspec j hjG k' hslot)
    have e : ((data.genericSorts env c).map (VLevel.inst packed)).getD j .zero =
        ((data.genericSorts env c).getD j .zero).inst packed := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases (data.genericSorts env c)[j]? <;> simp [VLevel.inst]
    rw [e]
    exact this
  have hsortWF : ∀ j, (((data.genericSorts env c).map (VLevel.inst packed)).getD j .zero).WF gp.uvars := by
    intro j
    have e : ((data.genericSorts env c).map (VLevel.inst packed)).getD j .zero =
        ((data.genericSorts env c).getD j .zero).inst packed := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases (data.genericSorts env c)[j]? <;> simp [VLevel.inst]
    rw [e]
    exact VLevel.WF.inst hpk
  exact gp.singletonElim_wf henv hfam hcs data.owner i hc hown htarget hhead harity hfamHead
    hprop hsorts hsortWF

end InductiveSignature.RecursorData
end Lean4Lean
