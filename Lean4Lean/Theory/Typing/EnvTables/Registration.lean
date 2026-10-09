import Lean4Lean.Theory.Typing.EnvTables.DeclarationSteps

/-!
# Preservation of the table invariant by eliminator and projection registration
-/

namespace Lean4Lean.EnvTables
open VEnv InductiveSignature

variable {env env' : VEnv} {T : Tables}

/-! ## Constant occurrences with their universe arity -/

/-! ## Constructor names of a certified schema -/

theorem forall₂_prefix {R : α → β → Prop} {as : List α} {bs cs : List β}
    (h : List.Forall₂ R as (bs ++ cs)) : List.Forall₂ R (as.take bs.length) bs := by
  induction bs generalizing as with
  | nil => simp
  | cons b bs ih =>
    cases h with
    | cons hab hrest => exact .cons hab (ih hrest)

theorem Certified.mem_schemaCtorNames {schema : CaseSchema}
    (H : schema.Certified base source block) :
    n ∈ schemaCtorNames schema ↔ ∃ c ∈ source.constructorConstants, c.name = n := by
  obtain ⟨expanded, aux, hdata, _, _, hnames, _⟩ := H
  obtain ⟨envTypes, direct, _, _, _, hfamilies⟩ := hdata.correspondence
  have hpre := forall₂_prefix hfamilies
  have hlen : schema.sourceFamilies.length = source.types.length := by rw [hnames]; simp
  simp only [schemaCtorNames, hlen, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨nt, hnt, nc, hnc, rfl⟩
    obtain ⟨t, ht, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l hpre nt hnt
    obtain ⟨c, hc, hcrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l hrel.constructors nc hnc
    exact ⟨c, List.mem_flatMap.mpr ⟨t, ht, hc⟩, hcrel.1.symm⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨t, ht, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨nt, hnt, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_r hpre t ht
    obtain ⟨nc, hnc, hcrel⟩ := Lean4Lean.List.Forall₂.forall_exists_r hrel.constructors c hc
    exact ⟨nt, hnt, nc, hnc, hcrel.1⟩

/-! ## Witnesses are present below -/

/-! ## Eliminator registration -/

/-- A family none of whose names (its own and its constructors') is recorded yet. -/
noncomputable def unrecorded (T : Tables) (t : VInductiveType) : Bool := by
  classical
  exact decide (T.fam t.name = none ∧ T.ctor t.name = none ∧
    ∀ c ∈ t.ctors, T.fam c.name = none ∧ T.ctor c.name = none)

/-- `n` is the name of a constructor of a source family of a schema registered in `env`. -/
def SchemaCtorReserved (env : VEnv) (n : Name) : Prop :=
  ∃ key schema, env.eliminators key schema ∧ n ∈ schemaCtorNames schema

/-- A family none of whose names is recorded yet, whose own name is not the name of a constructor
of a registered schema. -/
noncomputable def unrecordedIn (env : VEnv) (T : Tables) (t : VInductiveType) : Bool := by
  classical
  exact unrecorded T t && decide (¬SchemaCtorReserved env t.name)

theorem selFree_of_selFreeIn (h : unrecordedIn env T t = true) : unrecorded T t = true := by
  simp only [unrecordedIn, Bool.and_eq_true] at h; exact h.1

/-- Record the views of a schema's families none of whose names is recorded yet (family by
family: a family of the schema that is not otherwise registered is recorded here, so every
family of a generic equation's major has a recorded sort). A family whose name is a constructor
of an already registered schema is not recorded: once a name is a schema constructor, it is
never recorded as a family afterwards (in a consistent environment no such family exists). -/
noncomputable def Tables.addSchema (T : Tables) (env : VEnv) (source : VInductDecl) : Tables :=
  T.addViews (viewFams source (unrecordedIn env T)) (viewCtors source (unrecordedIn env T))

theorem Tables.Inv.eliminator {base : VEnv} {source : VInductDecl} {block : VInductBlock}
    {schema : CaseSchema} (H : T.Inv env) (hbase : base.WF) (hle : base ≤ env)
    (hcert : schema.Certified base source block)
    (hconsts : ∀ value ∈ block.types ++ block.ctors,
      env.constants value.name = some value.toVConstant)
    (hdf : env.defeqs = base.defeqs) :
    T.Extends (T.addSchema env source) ∧
      (T.addSchema env source).Inv (env.addEliminator key schema) := by
  classical
  have hcert₀ := hcert
  have H' := H.transport (env' := env.addEliminator key schema) VEnv.addEliminator_le rfl rfl
  have hfree : ∀ t ∈ source.types, unrecordedIn env T t = true → T.fam t.name = none ∧
      T.ctor t.name = none ∧ ∀ c ∈ t.ctors, T.fam c.name = none ∧ T.ctor c.name = none := by
    intro t _ ht; simpa [unrecorded] using selFree_of_selFreeIn ht
  unfold Tables.addSchema
  · refine ⟨T.extends_addViews _ _, H'.addViews ?_⟩
    obtain ⟨expanded, aux, hdata, _, _, hnames, _⟩ := hcert
    obtain ⟨_, hnd, hTypeUv, hCtorUv, envTypes, envCtors, htypes, hctors, _⟩ := hdata.sourceWF
    obtain ⟨params, _, _, hTypeShape, _, hraw⟩ := hdata.sourceParameters
    have hle' : base ≤ env.addEliminator key schema := hle.trans VEnv.addEliminator_le
    have htypeConst : ∀ t ∈ source.types,
        (env.addEliminator key schema).constants t.name = some t.toVConstant := by
      intro t ht
      exact hconsts t.toVConstVal (List.mem_append_left _ (by
        rw [hdata.types]; exact List.mem_map.mpr ⟨t, ht, rfl⟩))
    have hctorConst : ∀ t ∈ source.types, ∀ c ∈ t.ctors,
        (env.addEliminator key schema).constants c.name = some c.toVConstant := by
      intro t ht c hc
      exact hconsts c (List.mem_append_right _ (by
        rw [hdata.ctors]; exact List.mem_flatMap.mpr ⟨t, ht, hc⟩))
    have hfreshType : ∀ t ∈ source.types, base.constants t.name = none := fun t ht =>
      VEnv.addConstVals_names_fresh htypes t.toVConstVal (List.mem_map.mpr ⟨t, ht, rfl⟩)
    have hfreshCtor : ∀ t ∈ source.types, ∀ c ∈ t.ctors, base.constants c.name = none :=
      fun t ht c hc => VEnv.LE.constants_eq_none_left (VEnv.addConstVals_le htypes)
        (VEnv.addConstVals_names_fresh hctors c (List.mem_flatMap.mpr ⟨t, ht, hc⟩))
    have hrigid : ∀ n, base.constants n = none → (env.addEliminator key schema).Rigid n := by
      intro n hn
      have := hbase.ordered.rigid_of_absent hn
      simpa only [VEnv.Rigid, VEnv.addEliminator_defeqs, hdf] using this
    have hreg : (env.addEliminator key schema).eliminators key schema := VEnv.addEliminator_self
    apply newViewsWF_decl hnd
    · intro t ht hs; exact hfree t ht hs
    · intro t ht _
      exact famShape_of_typeShape ((hTypeShape t ht).mono hle') (hTypeUv t ht) (htypeConst t ht)
    · intro t ht _ c hc
      exact ⟨hctorConst t ht c hc, hraw t ht c hc, hCtorUv c (List.mem_flatMap.mpr ⟨t, ht, hc⟩)⟩
    · intro t ht _
      exact ⟨hrigid _ (hfreshType t ht), fun c hc => hrigid _ (hfreshCtor t ht c hc)⟩
    · intro t ht _
      refine ⟨.inr <| .inr <| .inr ⟨key, schema, hreg, .inl ?_⟩,
        fun c hc => .inr <| .inr <| .inr ⟨key, schema, hreg, .inr ?_⟩⟩
      · rw [hnames]; exact List.mem_map.mpr ⟨t, ht, rfl⟩
      · exact (Certified.mem_schemaCtorNames hcert₀).mpr
          ⟨c, List.mem_flatMap.mpr ⟨t, ht, hc⟩, rfl⟩

/-- Record the views of a schema that is already registered in `E`: a block installation that
also installs the certified case eliminator of its declaration (`VInductBlock.install`). -/
theorem Tables.Inv.addSchema_registered {base E : VEnv} {source : VInductDecl}
    {block : VInductBlock} {schema : CaseSchema} {key : Name} (H : T.Inv E) (hle : base ≤ E)
    (hcert : schema.Certified base source block) (hreg : E.eliminators key schema)
    (hconsts : ∀ value ∈ block.types ++ block.ctors,
      E.constants value.name = some value.toVConstant)
    (hrigid : ∀ t ∈ source.types, unrecordedIn E T t = true →
      E.Rigid t.name ∧ ∀ c ∈ t.ctors, E.Rigid c.name) :
    T.Extends (T.addSchema E source) ∧ (T.addSchema E source).Inv E := by
  classical
  have hcert₀ := hcert
  have hfree : ∀ t ∈ source.types, unrecordedIn E T t = true → T.fam t.name = none ∧
      T.ctor t.name = none ∧ ∀ c ∈ t.ctors, T.fam c.name = none ∧ T.ctor c.name = none := by
    intro t _ ht; simpa [unrecorded] using selFree_of_selFreeIn ht
  unfold Tables.addSchema
  refine ⟨T.extends_addViews _ _, H.addViews ?_⟩
  obtain ⟨expanded, aux, hdata, _, _, hnames, _⟩ := hcert
  obtain ⟨_, hnd, hTypeUv, hCtorUv, _⟩ := hdata.sourceWF
  obtain ⟨params, _, _, hTypeShape, _, hraw⟩ := hdata.sourceParameters
  have htypeConst : ∀ t ∈ source.types, E.constants t.name = some t.toVConstant := by
    intro t ht
    exact hconsts t.toVConstVal (List.mem_append_left _ (by
      rw [hdata.types]; exact List.mem_map.mpr ⟨t, ht, rfl⟩))
  have hctorConst : ∀ t ∈ source.types, ∀ c ∈ t.ctors,
      E.constants c.name = some c.toVConstant := by
    intro t ht c hc
    exact hconsts c (List.mem_append_right _ (by
      rw [hdata.ctors]; exact List.mem_flatMap.mpr ⟨t, ht, hc⟩))
  apply newViewsWF_decl hnd
  · intro t ht hs; exact hfree t ht hs
  · intro t ht _
    exact famShape_of_typeShape ((hTypeShape t ht).mono hle) (hTypeUv t ht) (htypeConst t ht)
  · intro t ht _ c hc
    exact ⟨hctorConst t ht c hc, hraw t ht c hc, hCtorUv c (List.mem_flatMap.mpr ⟨t, ht, hc⟩)⟩
  · exact hrigid
  · intro t ht _
    refine ⟨.inr <| .inr <| .inr ⟨key, schema, hreg, .inl ?_⟩,
      fun c hc => .inr <| .inr <| .inr ⟨key, schema, hreg, .inr ?_⟩⟩
    · rw [hnames]; exact List.mem_map.mpr ⟨t, ht, rfl⟩
    · exact (Certified.mem_schemaCtorNames hcert₀).mpr
        ⟨c, List.mem_flatMap.mpr ⟨t, ht, hc⟩, rfl⟩

/-- A family whose names are fresh in a well-formed environment is selected by `unrecordedIn` in
every environment with the same schemas. -/
theorem selFreeIn_of_fresh {base E : VEnv} {t : VInductiveType} (H : T.Inv base)
    (hbase : base.WF) (helim : ∀ {k s}, E.eliminators k s → base.eliminators k s)
    (hfresh : base.constants t.name = none)
    (hfreshC : ∀ c ∈ t.ctors, base.constants c.name = none) : unrecordedIn E T t = true := by
  classical
  simp only [unrecordedIn, unrecorded, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨(H.freshT hfresh).1, (H.freshT hfresh).2.1, fun c hc =>
    ⟨(H.freshT (hfreshC c hc)).1, (H.freshT (hfreshC c hc)).2.1⟩⟩, ?_⟩
  rintro ⟨key, schema, hreg, hmem⟩
  obtain ⟨_, _, _, _, _, hcert, _, hconsts⟩ := hbase.eliminator_installed (helim hreg)
  obtain ⟨c, hc, hcn⟩ := (Certified.mem_schemaCtorNames hcert).mp hmem
  have hcb := hconsts c (List.mem_append_right _ (by
    obtain ⟨_, _, hdata, _⟩ := hcert
    rw [hdata.ctors]; exact hc))
  rw [hcn, hfresh] at hcb
  cases hcb

/-- Registered projections whose structure views are recorded preserve the invariant. -/
theorem Tables.Inv.addProjections_viewed {P : List VProjectionEntry} (H : T.Inv env)
    (hP : ∀ entry ∈ P, T.fam entry.typeName = some (projFam entry.info) ∧
      T.ctor entry.info.ctorName = some (projCtor entry.typeName entry.info)) :
    T.Inv (env.addProjections P) where
  defs h := by
    obtain ⟨h1, h2, h3⟩ := H.defs h
    exact ⟨h1, VEnv.addProjections_le.constants h2, VEnv.addProjections_le.defeqs h3⟩
  recursors h := by
    obtain ⟨h1, h2⟩ := H.recursors h
    exact ⟨h1, h2.mono VEnv.addProjections_le .rfl⟩
  quot h := by
    obtain ⟨h1, h2⟩ := H.quot h
    exact ⟨h1.mono VEnv.addProjections_le, h2⟩
  defs_recursors := H.defs_recursors
  views := H.views.transport VEnv.addProjections_le (VEnv.addProjections_defeqs _ _)
  equations h := H.equations (by rwa [VEnv.addProjections_defeqs] at h)
  projections h := by
    rcases VEnv.addProjections_iff.mp h with ⟨entry, hentry, rfl, rfl⟩ | h
    · exact hP entry hentry
    · exact H.projections h

/-- The constructor stage of an inductive declaration. -/
theorem constructorStage_facts {base envTypes envCtors : VEnv} {block : VInductBlock}
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors) :
    base ≤ envCtors ∧ envCtors.defeqs = base.defeqs ∧ envCtors.projections = base.projections ∧
      envCtors.eliminators = base.eliminators ∧
      ∀ value ∈ block.types ++ block.ctors,
        envCtors.constants value.name = some value.toVConstant := by
  refine ⟨(VEnv.addConstVals_le htypes).trans (VEnv.addConstVals_le hctors),
    (VEnv.addConstVals_defeqs hctors).trans (VEnv.addConstVals_defeqs htypes),
    (VEnv.addConstVals_projections hctors).trans (VEnv.addConstVals_projections htypes),
    (VEnv.addConstVals_eliminators hctors).trans (VEnv.addConstVals_eliminators htypes), ?_⟩
  intro value hvalue
  rcases List.mem_append.mp hvalue with hvalue | hvalue
  · exact (VEnv.addConstVals_le hctors).constants (VEnv.addConstVals_get htypes hvalue)
  · exact VEnv.addConstVals_get hctors hvalue

/-- Every family of a certified declaration is selected by `unrecordedIn` at its constructor
stage. -/
theorem selFreeIn_constructorStage {base envTypes envCtors : VEnv} {decl : VInductDecl}
    {block : VInductBlock} {schema : CaseSchema} (H : T.Inv base) (hbase : base.WF)
    (hcert : schema.Certified base decl block)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors)
    {t : VInductiveType} (ht : t ∈ decl.types) : unrecordedIn envCtors T t = true := by
  obtain ⟨_, _, hdata, _⟩ := hcert
  obtain ⟨-, -, -, helimC, -⟩ := constructorStage_facts htypes hctors
  refine selFreeIn_of_fresh H hbase (fun h => by rwa [helimC] at h) ?_ fun c hc => ?_
  · exact VEnv.addConstVals_names_fresh htypes t.toVConstVal (by
      rw [hdata.types]; exact List.mem_map.mpr ⟨t, ht, rfl⟩)
  · exact VEnv.LE.constants_eq_none_left (VEnv.addConstVals_le htypes)
      (VEnv.addConstVals_names_fresh hctors c (by
        rw [hdata.ctors]; exact List.mem_flatMap.mpr ⟨t, ht, hc⟩))

/-- Register the certified case schema of a declaration and then its projections, over the
tables of its base (`VEnv.WF'.inductProjections`: the projections of a declaration are
registered after its case eliminator). The schema records every family of the declaration, so
every structure of the declaration already has its structure view. -/
theorem Tables.Inv.registerCasesProjections {base envTypes envCtors : VEnv}
    {decl : VInductDecl} {block : VInductBlock} {key : Name} {schema : CaseSchema}
    (H : T.Inv base) (hbase : base.WF) (hE : block.eliminators = [(key, schema)])
    (hcert : schema.Certified base decl block)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors) :
    T.Extends (T.addSchema envCtors decl) ∧
      (T.addSchema envCtors decl).Inv
        ((envCtors.addEliminators block.eliminators).addProjections block.projections) := by
  classical
  have hcert₀ := hcert
  obtain ⟨hle1, hdfC, hprojC, -, hconsts⟩ := constructorStage_facts htypes hctors
  obtain ⟨hext, hinv⟩ := (H.transport hle1 hdfC hprojC).eliminator (key := key) hbase hle1
    hcert₀ hconsts hdfC
  refine ⟨hext, ?_⟩
  have hEC : envCtors.addEliminators block.eliminators = envCtors.addEliminator key schema := by
    rw [hE]; rfl
  rw [hEC]
  apply hinv.addProjections_viewed
  obtain ⟨expanded, aux, hdata, _⟩ := hcert
  obtain ⟨_, hnd, _, hCtorUv, _⟩ := hdata.sourceWF
  obtain ⟨_, _, _, _, _, hraw⟩ := hdata.sourceParameters
  have hctorConst : ∀ t ∈ decl.types, ∀ c ∈ t.ctors,
      envCtors.constants c.name = some c.toVConstant := by
    intro t ht c hc
    exact hconsts c (List.mem_append_right _ (by
      rw [hdata.ctors]; exact List.mem_flatMap.mpr ⟨t, ht, hc⟩))
  intro entry hentry
  rw [hdata.projections] at hentry
  obtain ⟨t, ht, c, hctors1, rfl⟩ := VInductDecl.projectionEntries_origin hentry
  have hs := selFreeIn_constructorStage H hbase hcert₀ htypes hctors ht
  have hc : c ∈ t.ctors := by simp [hctors1]
  have hfreshT := (H.freshT (VEnv.addConstVals_names_fresh htypes t.toVConstVal (by
    rw [hdata.types]; exact List.mem_map.mpr ⟨t, ht, rfl⟩)))
  have hfreshC := (H.freshT (VEnv.LE.constants_eq_none_left (VEnv.addConstVals_le htypes)
    (VEnv.addConstVals_names_fresh hctors c (by
      rw [hdata.ctors]; exact List.mem_flatMap.mpr ⟨t, ht, hc⟩))))
  refine ⟨addView_some.mpr (.inr ⟨hfreshT.1, ?_⟩), addView_some.mpr (.inr ⟨hfreshC.2.1, ?_⟩)⟩
  · rw [viewFams_mem hnd ht hs]
    simp [famView, projFam, hctors1]
  · rw [viewCtors_mem ht hs hc
      (ctorView_unique (fun t ht _ c hc => ⟨hctorConst t ht c hc, hraw t ht c hc,
        hCtorUv c (List.mem_flatMap.mpr ⟨t, ht, hc⟩)⟩) t ht hs c hc)]
    rfl

/-! ## Structure registration -/

end Lean4Lean.EnvTables

namespace Lean4Lean.EnvTables
open VEnv InductiveSignature

/-! ## Every history has tables -/

def Tables.empty : Tables := ⟨fun _ => none, fun _ => none, false, fun _ => none, fun _ => none⟩

theorem Tables.empty_inv : Tables.empty.Inv VEnv.empty where
  defs h := by cases h
  recursors h := by cases h
  quot h := by cases h
  defs_recursors h := rfl
  views := {
    fam := fun h => by cases h
    ctor := fun h => by cases h
    fam_ctor := fun _ => rfl
    rigid := fun h => (h.elim (· rfl) (· rfl)).elim
    witness := fun h => (h.elim (· rfl) (· rfl)).elim }
  equations h := by cases h
  projections h := by cases h

end Lean4Lean.EnvTables
