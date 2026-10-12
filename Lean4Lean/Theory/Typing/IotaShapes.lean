import Lean4Lean.Theory.Typing.IotaSoundnessLemmas
import Lean4Lean.Theory.Typing.FamilyHeadType
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.NestedSyntax
import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.Compiled
import Lean4Lean.Theory.Typing.RecursorRegistration

/-! # The ι shapes of a generated rule

For a rule of a recursor of a declaration installed by `VEnv.addInduct`, read off a restored
generated equation of the declaration's compilation (`CompilationData.iota_shapes`): the
recursor telescope over the restored family head (`VRecursorShape`), the telescope of the
restored constructor (`VConstructorShape`) and the shape of the equation, typed in the
environment (`VIotaRuleTyped`). These are the data of `VIotaRuleTyped.reduct_typed`, which
types the reduct of every instance of the rule (`VEnv.WF.iotaReductTyped`). Ordinary and nested
compilations are handled together: an ordinary compilation restores nothing. -/

namespace Lean4Lean
open InductiveSignature

namespace InductiveSignature

theorem mem_familyNames {types : List VInductiveType} {n : Name} :
    n ∈ familyNames types ↔
      (∃ t ∈ types, t.name = n) ∨ ∃ t ∈ types, ∃ c ∈ t.ctors, c.name = n := by
  unfold familyNames
  simp only [List.mem_flatMap, List.mem_cons, List.mem_map]
  constructor
  · rintro ⟨t, ht, h | ⟨c, hc, rfl⟩⟩
    · exact .inl ⟨t, ht, h.symm⟩
    · exact .inr ⟨t, ht, c, hc, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, c, hc, rfl⟩)
    · exact ⟨t, ht, .inl rfl⟩
    · exact ⟨t, ht, .inr ⟨c, hc, rfl⟩⟩

theorem familyNames_append (l₁ l₂ : List VInductiveType) :
    familyNames (l₁ ++ l₂) = familyNames l₁ ++ familyNames l₂ := by
  simp [familyNames, List.flatMap_append]

/-- Restoration-only names are absent from the environment holding the source
types and constructors. Auxiliary heads are lowered family and constructor
names, fresh by the expanded formation; auxiliary recursor names are fresh
generated recursors. -/
theorem CompilationData.restorableNames_fresh
    {base envTypes envCtors : VEnv} {source expanded : VInductDecl}
    {s : InductiveSignature} {g : Instance s}
    {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (H : CompilationData base source expanded s g auxiliaries block)
    (hadded : base.addConstVals source.typeConstants = some envTypes)
    (hctors : envTypes.addConstVals source.constructorConstants = some envCtors) :
    ∀ n ∈ (compilationRestoration source auxiliaries).restorableNames,
      envCtors.constants n = none := by
  intro n hn
  -- every name of the source block
  have hsrc : ∀ v, envCtors.constants n = some v → base.constants n = some v ∨
      n ∈ familyNames source.types := by
    intro v hv
    rcases VEnv.addConstVals_lookup_cases hctors hv with h | ⟨e, he, hname, _⟩
    · rcases VEnv.addConstVals_lookup_cases hadded h with h | ⟨e, he, hname, _⟩
      · exact .inl h
      · right
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
        exact mem_familyNames.mpr (.inl ⟨t, ht, hname⟩)
    · right
      obtain ⟨t, ht, hc⟩ := List.mem_flatMap.mp he
      exact mem_familyNames.mpr (.inr ⟨t, ht, e, hc, hname⟩)
  -- expanded names
  obtain ⟨envT, direct, _, hdirect, _, hfamilies⟩ := H.correspondence
  have hexpNames : familyNames expanded.types = familyNames source.types ++ familyNames direct := by
    rw [← H.model.familyNames, RestoresFamily.familyNames hfamilies, familyNames_append]
  obtain ⟨envExpT, envExpC, hexpT, hexpC, _⟩ := H.generatedIHsWellTyped
  have hfreshExp : ∀ m ∈ familyNames expanded.types, base.constants m = none := by
    intro m hm
    rcases mem_familyNames.mp hm with ⟨t, ht, rfl⟩ | ⟨t, ht, c, hc, rfl⟩
    · exact VEnv.addConstVals_names_fresh hexpT t.toVConstVal (List.mem_map.mpr ⟨t, ht, rfl⟩)
    · have h := VEnv.addConstVals_names_fresh hexpC c (List.mem_flatMap.mpr ⟨t, ht, hc⟩)
      cases hb : base.constants c.name with
      | none => rfl
      | some v => rw [(VEnv.addConstVals_le hexpT).constants hb] at h; cases h
  cases hv : envCtors.constants n with
  | none => rfl
  | some v =>
  rcases List.mem_append.mp hn with hhead | hrec
  · have hdir : n ∈ familyNames direct := by
      rw [← compilationRestoration_heads_names (H.model.nparams.trans H.nparams) hdirect]
      exact hhead
    rcases hsrc v hv with hb | hs
    · rw [hfreshExp n (by rw [hexpNames]; exact List.mem_append_right _ hdir)] at hb
      cases hb
    · exact (H.source_head_disjoint hs hhead).elim
  · obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hrec
    have hg := H.recursor_source_mem hpair
    rcases hsrc v hv with hb | hs
    · obtain ⟨rc, hrc, hname⟩ := List.mem_map.mp hg
      rw [← hname, H.recursorsFresh rc hrc] at hb
      cases hb
    · exfalso
      have hnd := H.generatedNames
      simp only [List.map_append, List.nodup_append] at hnd
      have hin : pair.1 ∈ (expanded.typeConstants.map (·.name) ++
          expanded.constructorConstants.map (·.name)) := by
        have he : pair.1 ∈ familyNames expanded.types := by
          rw [hexpNames]; exact List.mem_append_left _ hs
        rcases mem_familyNames.mp he with ⟨t, ht, h⟩ | ⟨t, ht, c, hc, h⟩
        · exact List.mem_append_left _ (List.mem_map.mpr ⟨t.toVConstVal,
            List.mem_map.mpr ⟨t, ht, rfl⟩, h⟩)
        · exact List.mem_append_right _ (List.mem_map.mpr ⟨c,
            List.mem_flatMap.mpr ⟨t, ht, hc⟩, h⟩)
      exact hnd.2.2 _ hin _ hg rfl


/-- A recursor of the compiled declaration named after a generated recursor is the
restoration of that generated recursor, installed as a constant of `env`. -/
theorem CompilationData.recursorType_installed {base installBase installed env : VEnv}
    {source expanded : VInductDecl} {s : InductiveSignature} {g : Instance s}
    {aux : List ContainerSpecialization} {block : VInductBlock}
    (C : CompilationData base source expanded s g aux block) (hrecsOf : source.RecsOf block)
    (hadd : installBase.addInduct source = some installed) (hle : installed ≤ env)
    {rec : VRecursor} (hrec : rec ∈ source.recs) (o : Fin s.families.size)
    (hname : rec.name = (compilationRestoration source aux).recursorName (g.recursorName o)) :
    ∃ type, (compilationRestoration source aux).expr (g.recursorType o) = some type ∧
      env.constants ((compilationRestoration source aux).recursorName (g.recursorName o)) =
        some ⟨g.uvars, type⟩ := by
  have hrs := List.mapM_eq_some.mp C.recursors
  obtain ⟨rr, hrr, hr⟩ := Lean4Lean.List.Forall₂.forall_exists_l hrs (g.recursor o)
    (g.recursor_mem o)
  obtain ⟨hn, hu, ht⟩ := VEnv.Model.Nested.recursor_parts hr
  have hmem : rec.toVConstVal ∈ block.recursors := by
    rw [← hrecsOf.recursors]; exact List.mem_map_of_mem hrec
  have hnd : (block.recursors.map (·.name)).Nodup := by
    have := C.names
    simp only [List.map_append] at this
    exact (List.nodup_append.1 this).2.1
  have heq : rec.toVConstVal = rr :=
    VEnv.inj_on_of_nodup_map hnd hmem hrr (hname.trans hn.symm)
  refine ⟨rr.type, ht, ?_⟩
  rw [← hname, hle.constants (VEnv.addInduct_rec_find hadd hrec)]
  show some rec.toVConstVal.toVConstant = _
  rw [heq]
  show some (VConstant.mk rr.uvars rr.type) = _
  rw [hu]
  rfl


set_option maxHeartbeats 4000000 in
/-- **The ι shapes of a restored generated equation** of a declaration installed by
`VEnv.addInduct`: the recursor telescope over the restored family head of the constructor's
owner, the restored constructor's telescope and the typed shape of the equation, in a
well-formed environment containing the installation. -/
theorem CompilationData.iota_shapes {env base installBase installed : VEnv}
    {source expanded : VInductDecl} {s : InductiveSignature} {g : Instance s}
    {aux : List ContainerSpecialization} {block : VInductBlock}
    (henv : env.WF)
    (hdata : CompilationData base source expanded s g aux block)
    (hprior : ContainersInstalled base aux) (hbase : base ≤ installBase)
    (hrecsOf : source.RecsOf block)
    (hadd : installBase.addInduct source = some installed) (hle : installed ≤ env)
    {rec : VRecursor} (hrec : rec ∈ source.recs) (index : Fin s.constructors.size)
    (hname : rec.name = (compilationRestoration source aux).recursorName
      (g.recursorName s.constructors[index].owner))
    {equation : VDefEq}
    (heq : (compilationRestoration source aux).equation (g.equation index) = some equation)
    (hwf : equation.WF env) :
    ∃ (head : RestoredFamilyHead),
      Nonempty (VRecursorShape env rec.name g.uvars s.params.length head.arguments.length
        s.families.size s.constructors.size s.families[s.constructors[index].owner].indices.length
        head.name head.levels head.arguments) ∧
      (∃ fields, Nonempty (VConstructorShape env
        ((compilationRestoration source aux).restoredHeadName s.constructors[index].name)
        head.levels.length head.arguments.length fields
        s.families[s.constructors[index].owner].indices.length head.name)) ∧
      Nonempty (VIotaRuleTyped env rec.name g.uvars s.params.length head.arguments.length
        s.families.size s.constructors.size s.families[s.constructors[index].owner].indices.length
        ((compilationRestoration source aux).restoredHeadName s.constructors[index].name)
        head.levels s.constructors[index].fields.length equation head.arguments) := by
  let r := compilationRestoration source aux
  obtain ⟨-, -, -, -, envTypes, envCtors, hadded, hctorsAdded, -, -⟩ := hdata.sourceWF
  have hfreshC := hdata.restorableNames_fresh hadded hctorsAdded
  have hfreshT : ∀ n ∈ r.restorableNames, envTypes.constants n = none := by
    intro n hn
    cases h : envTypes.constants n with
    | none => rfl
    | some v =>
      have := (VEnv.addConstVals_le hctorsAdded).constants h
      rw [hfreshC n hn] at this; cases this
  have hbaseEnv : base ≤ env := hbase.trans ((VEnv.addInduct_le hadd).trans hle)
  have hleC : envCtors ≤ env := by
    obtain ⟨envT, envC, envR, hT, hC, hR, hP⟩ := VEnv.addInduct_stages hadd
    have hCle : envC ≤ env :=
      ((VEnv.addProjs_le.trans (VEnv.addRecs_le hR)).trans (VEnv.addRules_le hP)).trans hle
    rw [VInductDecl.addTypes_eq_addConstVals] at hT
    rw [VInductDecl.addCtors_eq_addConstVals] at hC
    apply VEnv.addConstVals_le_target (VEnv.addConstVals_le_target hbaseEnv hadded ?_)
      hctorsAdded ?_
    · intro v hv
      exact hCle.constants ((VEnv.addConstVals_le hC).constants (VEnv.addConstVals_get hT hv))
    · intro v hv
      exact hCle.constants (VEnv.addConstVals_get hC hv)
  obtain ⟨head, hhead, _, _, hargs, happ, Hctors⟩ :=
    hdata.restoredFamilyHead_spec hadded hctorsAdded hfreshT hfreshC s.constructors[index].owner
  obtain ⟨-, happC⟩ := Hctors index rfl
  have hindices := hdata.model.constructorArity _
    (Array.getElem_mem_toList (xs := s.constructors) index.isLt)
  have hnotHead : r.heads.find? (fun h => h.auxiliary ==
      g.recursorName s.constructors[index].owner) = none := by
    apply Restoration.heads_find?_eq_none
    intro hm
    obtain ⟨h, hh, he'⟩ := List.mem_map.mp hm
    exact hdata.heads_not_recursors _ h hh he'
  -- the recursor type
  obtain ⟨type, htype', hcst⟩ := hdata.recursorType_installed hrecsOf hadd hle hrec _ hname
  obtain ⟨_, -, Hadm⟩ := hdata.admissible
  obtain ⟨head3, hhead3, RP, RF, hRP, hRF, Hfd⟩ :=
    hdata.restoredConstructorFieldDomains hprior hadded hctorsAdded hfreshT hfreshC hleC henv
      Hadm.levels_wf index _ rfl
  have h33 : head3 = head := Option.some.inj (hhead3.symm.trans hhead)
  rw [h33] at Hfd
  obtain ⟨I⟩ := Restoration.restored_iota_shape g r index heq hwf henv VEnv.LE.rfl
    (fun _ => rfl) ⟨type, htype', hcst⟩ hindices hnotHead happC
    (fun h hh => (hdata.restorationScoped.2.2.1 h hh).2) ⟨RP, RF, hRP, hRF, Hfd⟩
  obtain ⟨head2, hhead2, fields, ⟨hctorShape⟩⟩ := hdata.restoredConstructorShape hprior
    hadded hctorsAdded hfreshT hfreshC hleC index _ rfl
  cases Option.some.inj (hhead2.symm.trans hhead)
  -- the recursor shape
  obtain ⟨pre, major, hpre, hm, rfl⟩ := r.expr_recursorType_eq_some htype'
  have hprelen : pre.length = s.params.length + s.families.size + s.constructors.size +
      s.families[s.constructors[index].owner].indices.length := by
    rw [← (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hpre)),
      g.recursorPrefix_length]
  have hmaj := Option.some.inj (hm.symm.trans happ)
  refine ⟨head, ⟨{
    ctorParams_length := rfl
    ctorParams_closed := hargs
    type := _
    const := hname ▸ hcst
    doms := pre ++ [major]
    result := g.recursorBody s.constructors[index].owner
    type_eq := rfl
    doms_length := by simp [hprelen]
    major_eq := by
      rw [← hprelen, List.getElem?_concat_length, hmaj, vars_eq_bvarRange, Nat.zero_add] }⟩, ⟨fields, ⟨hctorShape⟩⟩, ⟨hname ▸ I⟩⟩

end InductiveSignature

end Lean4Lean
