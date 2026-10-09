import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Inductive.SignatureLemmas
import Lean4Lean.Theory.Inductive.CompilationLemmas

/-! Registration of declaration-derived case schemas right after the constructors, and the
registry invariant `VEnv.RegistryInv` of every well-formed environment (section 2.3 of
the design notes). Freshness of a schema follows from the installation history.

Registration also carries the certified fact
`CaseSchema.ProjNamesRegistered` (the schema projects only out of structures
registered at registration time). It is a hypothesis of
`RegistrationCertificate.register_after_constructors`, and it is exposed for every registry entry by
`VEnv.WF.eliminatorsProjNamesRegistered`. -/

namespace Lean4Lean

private theorem definitions_le (env : VEnv) (cis : List VDefVal) :
    env ≤ env.addDefEqs cis := by
  induction cis generalizing env with
  | nil => exact .rfl
  | cons ci cis ih => exact VEnv.addDefEq_le.trans (ih _)

private theorem declaration_le (H : VDecl.WF env decl env') : env ≤ env' := by
  cases H with
  | «axiom» _ h | «opaque» _ h => exact VEnv.addConst_le h
  | «def» _ h => exact (VEnv.addConst_le h).trans VEnv.addDefEq_le
  | «example» => exact .rfl
  | mutualDef _ h _ => exact (VEnv.addConsts_le h).trans (definitions_le ..)
  | quot _ h =>
    simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := h
    exact (VEnv.addConst_le ha).trans <| (VEnv.addConst_le hb).trans <|
      (VEnv.addConst_le hc).trans <| (VEnv.addConst_le hd).trans VEnv.addDefEq_le
  | induct h =>
    cases h with
    | intro _ _ _ _ h => exact VInductBlock.install_base_le h

theorem VDecl.WF.le (H : VDecl.WF env decl env') : env ≤ env' := declaration_le H

namespace VEnv.InductRegistration

theorem le (R : VEnv.InductRegistration env decl key schema env') : env ≤ env' := by
  obtain ⟨_, _, _, _, _, _, hinstall, _⟩ := R
  exact VInductBlock.install_base_le hinstall

/-- The registered block's families and constructors are installed. -/
theorem constants (R : VEnv.InductRegistration env decl key schema env') :
    ∃ block : VInductBlock, schema.RegistrationCertificate env decl block key ∧
      ∀ value ∈ block.types ++ block.ctors, env'.constants value.name = some value.toVConstant := by
  obtain ⟨block, envTypes, envCtors, _, _, _, hinstall, ht, hc, _, hreg, _⟩ := R
  refine ⟨block, hreg, fun value hv => ?_⟩
  have hle := VInductBlock.install_ctors_le hinstall ht hc
  rcases List.mem_append.mp hv with hv | hv
  · exact hle.constants ((VEnv.addConstVals_le hc).constants (VEnv.addConstVals_get ht hv))
  · exact hle.constants (VEnv.addConstVals_get hc hv)

theorem projNames (R : VEnv.InductRegistration env decl key schema env') :
    schema.ProjNamesRegistered env' key := by
  obtain ⟨block, envTypes, envCtors, _, _, _, hinstall, ht, hc, _, _, hprojs⟩ := R
  exact hprojs.mono (VInductBlock.install_ctors_le hinstall ht hc)

end VEnv.InductRegistration

open InductiveSignature

theorem VInductBlock.install_projections_iff {env env' : VEnv} {block : VInductBlock}
    (H : VInductBlock.install env block = some env') :
    env'.projections name info ↔
      (∃ entry ∈ block.projections, name = entry.typeName ∧ info = entry.info) ∨
        env.projections name info := by
  obtain ⟨_, _, _, ht, hc, hr, rfl⟩ := VInductBlock.install_stages H
  rw [VEnv.addDefEqRules_projections, VEnv.addConstVals_projections hr, VEnv.addProjections_iff,
    VEnv.addEliminators_projections, VEnv.addConstVals_projections hc,
    VEnv.addConstVals_projections ht]

/-- A certified eliminator covers each projection entry of its block. -/
private theorem covered_of_certified {decl : VInductDecl} {block : VInductBlock}
    {schema : CaseSchema} {base : VEnv} (hcert : schema.Certified base decl block)
    (hprojections : block.projections = decl.projectionEntries)
    {entry : VProjectionEntry} (hentry : entry ∈ block.projections) :
    entry.typeName ∈ schema.sourceFamilies := by
  rw [hprojections] at hentry
  obtain ⟨type, htype, ctor, _, rfl⟩ := VInductDecl.projectionEntries_origin hentry
  obtain ⟨_, _, _, _, _, hnames, _⟩ := hcert
  rw [hnames]
  exact List.mem_map.mpr ⟨type, htype, rfl⟩

/-- **The registry invariant** of a well-formed environment. Every registered case schema
retains its registration certificate over an earlier well-formed environment and the source
constants it was registered with; it projects only out of registered structures; a key fixes
its schema; and every registered structure is a source family of a registered schema.
All four facts are established by one induction over the history (`VEnv.WF'.registryInv`). -/
structure VEnv.RegistryInv (env : VEnv) : Prop where
  origin : ∀ {key schema}, env.eliminators key schema →
    ∃ (base : VEnv) (source : VInductDecl) (block : VInductBlock), base.WF ∧ base ≤ env ∧
      schema.RegistrationCertificate base source block key ∧
      ∀ value ∈ block.types ++ block.ctors, env.constants value.name = some value.toVConstant
  projNames : ∀ {key schema}, env.eliminators key schema → schema.ProjNamesRegistered env key
  unique : ∀ {key left right}, env.eliminators key left → env.eliminators key right →
    left = right
  projectionsEliminated : ∀ {name info}, env.projections name info →
    ∃ key schema, env.eliminators key schema ∧ name ∈ schema.sourceFamilies

namespace VEnv.RegistryInv

/-- Every source family of a registered schema is a constant of the environment. -/
theorem family_present {env : VEnv} (H : env.RegistryInv)
    (hlookup : env.eliminators key schema) (hname : name ∈ schema.sourceFamilies) :
    ∃ value, env.constants name = some value := by
  obtain ⟨base, source, block, _, _, hreg, hconstants⟩ := H.origin hlookup
  obtain ⟨expanded, auxiliaries, hdata, _, _, hnames, hdisj⟩ := hreg.certified
  rw [hnames] at hname
  obtain ⟨family, hfamily, rfl⟩ := List.mem_map.mp hname
  refine ⟨family.toVConstant, hconstants family.toVConstVal ?_⟩
  apply List.mem_append_left
  rw [hdata.types]
  exact List.mem_map.mpr ⟨family, hfamily, rfl⟩

theorem key_mem {env : VEnv} (H : env.RegistryInv)
    (hlookup : env.eliminators key schema) : key ∈ schema.sourceFamilies := by
  obtain ⟨base, source, block, _, _, hreg, _⟩ := H.origin hlookup
  obtain ⟨expanded, auxiliaries, _, _, _, hnames, hdisj⟩ := hreg.certified
  have hkey := hreg.keyHead
  rw [hnames]
  cases htypes : source.types with
  | nil => simp [htypes] at hkey
  | cons family families =>
    simp only [htypes, List.head?_cons, Option.map_some, Option.some.injEq] at hkey
    simp [← hkey]

end VEnv.RegistryInv

namespace InductiveSignature.CaseSchema

/-- The checked source header installation already guarantees freshness of
the schema's key and source families. Registration asks for no new freshness
certificate from the verifier. -/
theorem Certified.freshOfInv {schema : CaseSchema} {base : VEnv}
    (H : schema.Certified base source block) (hbase : base.RegistryInv)
    (hkey : source.types.head?.map (·.name) = some key) : schema.Fresh base key := by
  obtain ⟨expanded, auxiliaries, hdata, _, _, hnames, hdisj⟩ := H
  obtain ⟨types, ctors, htypes, _, _, _⟩ := hdata.sourceWF.2.2.2.2
  have hnew : ∀ name ∈ schema.sourceFamilies, base.constants name = none := by
    intro name hname
    rw [hnames] at hname
    obtain ⟨family, hfamily, rfl⟩ := List.mem_map.mp hname
    exact VEnv.addConstVals_names_fresh htypes family.toVConstVal
      (List.mem_map.mpr ⟨family, hfamily, rfl⟩)
  have hkeyMem : key ∈ schema.sourceFamilies := by
    rw [hnames]
    cases ht : source.types with
    | nil => simp [ht] at hkey
    | cons family families =>
      simp only [ht, List.head?_cons, Option.map_some, Option.some.injEq] at hkey
      simp [← hkey]
  constructor
  · intro previous hprevious
    obtain ⟨value, hvalue⟩ := hbase.family_present hprevious (hbase.key_mem hprevious)
    rw [hnew key hkeyMem] at hvalue
    contradiction
  · intro previousKey previous hprevious name hleft hright
    obtain ⟨value, hvalue⟩ := hbase.family_present hprevious hright
    rw [hnew name hleft] at hvalue
    contradiction

end InductiveSignature.CaseSchema

namespace VEnv.InductRegistration

theorem freshOfInv (R : VEnv.InductRegistration env decl key schema env')
    (henv : env.RegistryInv) : schema.Fresh env key := by
  obtain ⟨block, _, _, _, _, _, _, _, _, _, hreg, _⟩ := R
  exact hreg.certified.freshOfInv henv hreg.keyHead

/-- One declaration step registers one eliminator. -/
theorem uniqueOfInv (R : VEnv.InductRegistration env decl key schema env')
    (henv : env.RegistryInv) (R' : VEnv.InductRegistration env decl' key' schema' env') :
    key = key' ∧ schema = schema' := by
  have hfresh := R.freshOfInv henv
  obtain ⟨block', _, _, _, _, _, hinstall', _, _, hE', _⟩ := R'
  obtain ⟨block, _, _, _, _, _, hinstall, _, _, hE, _⟩ := R
  have h1 : env'.eliminators key schema := by
    rw [VInductBlock.install_eliminators_iff hinstall, hE]; simp
  rw [VInductBlock.install_eliminators_iff hinstall', hE'] at h1
  rcases h1 with h1 | h1
  · simp only [List.mem_singleton, Prod.mk.injEq] at h1; exact h1
  · exact (hfresh.1 _ h1).elim

end VEnv.InductRegistration

/-- The registry invariant along a history. -/
theorem VEnv.WF'.registryInv {ds : List VDecl} {env : VEnv} (H : env.WF' ds) :
    env.RegistryInv := by
  induction H with
  | empty =>
    exact ⟨fun h => h.elim, fun h => h.elim, fun h => h.elim, fun h => h.elim⟩
  | decl h hds ih =>
    have hle := declaration_le h
    refine ⟨fun hlookup => ?_, fun hlookup => ?_, fun hleft hright => ?_, fun hp => ?_⟩
    · rcases h.eliminators_iff.mp hlookup with ⟨source, -, R⟩ | hlookup
      · obtain ⟨block, hreg, hc⟩ := R.constants
        exact ⟨_, source, block, ⟨_, hds⟩, R.le, hreg, hc⟩
      obtain ⟨base, source, block, hb, hble, hreg, hc⟩ := ih.origin hlookup
      exact ⟨base, source, block, hb, hble.trans hle, hreg,
        fun value hv => hle.constants (hc value hv)⟩
    · rcases h.eliminators_iff.mp hlookup with ⟨source, -, R⟩ | hlookup
      · exact R.projNames
      exact (ih.projNames hlookup).mono hle
    · rcases h.eliminators_iff.mp hleft with ⟨source, rfl, R⟩ | hleft <;>
        rcases h.eliminators_iff.mp hright with ⟨source', hs, R'⟩ | hright
      · cases hs; exact (R.uniqueOfInv ih R').2
      · exact ((R.freshOfInv ih).1 _ hright).elim
      · exact ((R'.freshOfInv ih).1 _ hleft).elim
      · exact ih.unique hleft hright
    · cases h with
      | «axiom» _ hadd | «opaque» _ hadd =>
        rw [VEnv.addConst_projections hadd] at hp
        obtain ⟨k, s, hs, hn⟩ := ih.projectionsEliminated hp
        exact ⟨k, s, hle.eliminators hs, hn⟩
      | «def» _ hadd =>
        obtain ⟨k, s, hs, hn⟩ := ih.projectionsEliminated (by
          have hp' := hp
          simp only [VEnv.addDefEq] at hp'
          rwa [VEnv.addConst_projections hadd] at hp')
        exact ⟨k, s, hle.eliminators hs, hn⟩
      | «example» => exact ih.projectionsEliminated hp
      | mutualDef _ hadd _ =>
        rw [VEnv.addDefEqs_projections, VEnv.addConsts_projections hadd] at hp
        obtain ⟨k, s, hs, hn⟩ := ih.projectionsEliminated hp
        exact ⟨k, s, hle.eliminators hs, hn⟩
      | quot _ hadd =>
        rw [VEnv.addQuot_projections hadd] at hp
        obtain ⟨k, s, hs, hn⟩ := ih.projectionsEliminated hp
        exact ⟨k, s, hle.eliminators hs, hn⟩
      | induct hadd =>
        cases hadd with
        | intro _ hcompile _ helim hinstall =>
          rcases (VInductBlock.install_projections_iff hinstall).mp hp with
            ⟨entry, hentry, rfl, rfl⟩ | hold
          · obtain ⟨_, _, _, _, helim⟩ := helim
            rcases helim with ⟨hT, -⟩ | ⟨key, schema, hE, hreg, _⟩
            · rw [hcompile.projections] at hentry
              simp [VInductDecl.projectionEntries, hT] at hentry
            refine ⟨key, schema, ?_,
              covered_of_certified hreg.certified hcompile.projections hentry⟩
            rw [VInductBlock.install_eliminators_iff hinstall, hE]
            simp
          · obtain ⟨k, s, hs, hn⟩ := ih.projectionsEliminated hold
            exact ⟨k, s, hle.eliminators hs, hn⟩
  | inductProjections _ _ hcovered _ _ _ _ _ _ _ _ hprojections _ _ _ ih =>
    refine ⟨fun hlookup => ?_, fun hlookup => ?_, fun hleft hright => ?_, fun hp => ?_⟩
    · rw [VEnv.addProjections_eliminators] at hlookup
      obtain ⟨base, source, block, hb, hble, hreg, hc⟩ := ih.origin hlookup
      exact ⟨base, source, block, hb, hble.trans VEnv.addProjections_le, hreg,
        fun value hv => VEnv.addProjections_le.constants (hc value hv)⟩
    · rw [VEnv.addProjections_eliminators] at hlookup
      exact (ih.projNames hlookup).mono VEnv.addProjections_le
    · rw [VEnv.addProjections_eliminators] at hleft hright
      exact ih.unique hleft hright
    · rw [VEnv.addProjections_iff] at hp
      rcases hp with ⟨entry, hentry, rfl, rfl⟩ | hold
      · obtain ⟨key, schema, hE, hreg⟩ := hcovered
        refine ⟨key, schema, ?_, covered_of_certified hreg.certified hprojections hentry⟩
        rw [VEnv.addProjections_eliminators, VEnv.addEliminators_iff, hE]
        simp
      · obtain ⟨k, s, hs, hn⟩ := ih.projectionsEliminated hold
        exact ⟨k, s, by rw [VEnv.addProjections_eliminators]; exact hs, hn⟩
  | inductEliminators hb _ hble hreg hc _ hprojs _ hfresh _ _ ih =>
    refine ⟨fun hlookup => ?_, fun hlookup => ?_, fun hleft hright => ?_, fun hp => ?_⟩
    · rcases hlookup with ⟨rfl, rfl⟩ | hlookup
      · exact ⟨_, _, _, ⟨_, hb⟩, hble.trans VEnv.addEliminator_le, hreg, hc⟩
      obtain ⟨base, source, block, hb, hble, hreg, hc⟩ := ih.origin hlookup
      exact ⟨base, source, block, hb, hble.trans VEnv.addEliminator_le, hreg, hc⟩
    · rcases hlookup with ⟨rfl, rfl⟩ | hlookup
      · exact hprojs.mono VEnv.addEliminator_le
      · exact (ih.projNames hlookup).mono VEnv.addEliminator_le
    · rcases hleft with ⟨rfl, rfl⟩ | hleft
      · rcases hright with ⟨_, rfl⟩ | hright
        · rfl
        · exact (hfresh.1 _ hright).elim
      · rcases hright with ⟨rfl, rfl⟩ | hright
        · exact (hfresh.1 _ hleft).elim
        · exact ih.unique hleft hright
    · obtain ⟨k, s, hs, hn⟩ := ih.projectionsEliminated hp
      exact ⟨k, s, .inr hs, hn⟩

theorem VEnv.WF.registryInv {env : VEnv} (H : env.WF) : env.RegistryInv :=
  H.choose_spec.registryInv

/-- Every registry entry retains its independent formation derivation and
the exact source constants justified when it was registered. -/
theorem VEnv.WF.eliminator_installed {env : VEnv} (H : env.WF)
    (hlookup : env.eliminators key schema) :
    ∃ (base : VEnv) (source : VInductDecl) (block : VInductBlock), base.WF ∧ base ≤ env ∧
      schema.Certified base source block ∧
      source.types.head?.map (·.name) = some key ∧
      (∀ value ∈ block.types ++ block.ctors,
        env.constants value.name = some value.toVConstant) :=
  let ⟨base, source, block, hb, hle, hreg, hc⟩ := H.registryInv.origin hlookup
  ⟨base, source, block, hb, hle, hreg.certified, hreg.keyHead, hc⟩

/-- Every registry entry retains the header agreement certified at its registration. -/
theorem VEnv.WF.eliminator_headerAgreement {env : VEnv} (H : env.WF)
    (hlookup : env.eliminators key schema) :
    ∃ (base : VEnv) (source : VInductDecl) (block : VInductBlock), base.WF ∧ base ≤ env ∧
      schema.Certified base source block ∧ schema.HeaderAgreement base source ∧
      (∀ value ∈ block.types ++ block.ctors,
        env.constants value.name = some value.toVConstant) :=
  let ⟨base, source, block, hb, hle, hreg, hc⟩ := H.registryInv.origin hlookup
  ⟨base, source, block, hb, hle, hreg.certified, hreg.headerAgreement, hc⟩

/-- Every source family of a registered schema is a constant of the environment. -/
theorem VEnv.WF.eliminator_family_present {env : VEnv} (H : env.WF)
    (hlookup : env.eliminators key schema) (hname : name ∈ schema.sourceFamilies) :
    ∃ value, env.constants name = some value :=
  H.registryInv.family_present hlookup hname

theorem VEnv.WF.eliminator_key_mem {env : VEnv} (H : env.WF)
    (hlookup : env.eliminators key schema) : key ∈ schema.sourceFamilies :=
  H.registryInv.key_mem hlookup

/-- Every registered case schema projects only out of structures registered in
the environment: the fact certified at registration, transported along the
later extensions. -/
theorem VEnv.WF.eliminatorsProjNamesRegistered {env : VEnv} (H : env.WF) :
    ∀ block schema, env.eliminators block schema → schema.ProjNamesRegistered env block :=
  fun _ _ hlookup => H.registryInv.projNames hlookup

/-- Fresh registration fixes a schema for every abstract block key. -/
theorem VEnv.WF.eliminators_unique (H : VEnv.WF env)
    (hleft : env.eliminators key left) (hright : env.eliminators key right) :
    left = right :=
  H.registryInv.unique hleft hright

/-- **Every registered structure has a registered case eliminator.** Projections are only
registered together with, and after, the certified case eliminator of their declaration. -/
theorem VEnv.WF.projections_eliminated {env : VEnv} (H : env.WF)
    (hp : env.projections name info) :
    ∃ key schema, env.eliminators key schema ∧ name ∈ schema.sourceFamilies :=
  H.registryInv.projectionsEliminated hp

theorem InductiveSignature.CaseSchema.Certified.fresh {schema : InductiveSignature.CaseSchema}
    {base : VEnv} (H : schema.Certified base source block) (hbase : base.WF)
    (hkey : source.types.head?.map (·.name) = some key) : schema.Fresh base key :=
  H.freshOfInv hbase.registryInv hkey

theorem VEnv.InductRegistration.fresh (R : VEnv.InductRegistration env decl key schema env')
    (henv : env.WF) : schema.Fresh env key :=
  R.freshOfInv henv.registryInv

/-- One declaration step registers one eliminator. -/
theorem VEnv.InductRegistration.unique (R : VEnv.InductRegistration env decl key schema env')
    (henv : env.WF) (R' : VEnv.InductRegistration env decl' key' schema' env') :
    key = key' ∧ schema = schema' :=
  R.uniqueOfInv henv.registryInv R'

namespace InductiveSignature.CaseSchema

theorem view_constructor_names (schema : CaseSchema)
    (owner : Fin schema.signature.families.size) :
    (schema.view owner).constructors.toList.map (·.name) =
      (schema.signature.declarationFamily owner).ctors.map (·.name) := by
  simp only [view, List.toList_toArray, declarationFamily, List.map_filterMap]
  apply congrArg (List.filterMap · schema.signature.constructors.toList)
  funext ctor
  by_cases ho : ctor.owner = owner
  · simp [ho, caseConstructor]
  · have hv : ctor.owner.val ≠ owner.val := fun hv => ho (Fin.ext hv)
    simp [ho, hv]

/-- A certified schema is compatible with the structures registered by its own
declaration and by its base: a structure of the declaration has exactly the
declaration's single constructor, and a structure of the base is not a source
family of the schema, since those are fresh in the base. -/
theorem Certified.structCompat {schema : CaseSchema} {base envTypes envCtors : VEnv}
    (H : schema.Certified base source block) (hbase : base.WF)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors) :
    schema.StructCompat (envCtors.addProjections block.projections) := by
  obtain ⟨expanded, auxiliaries, hdata, _, _, hnames, _⟩ := H
  intro s info hproj owner hname
  rw [hnames, List.getElem?_map] at hname
  obtain ⟨family, hfamily, rfl⟩ := Option.map_eq_some_iff.mp hname
  have hmem : family ∈ source.types := List.mem_of_getElem? hfamily
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hfamily
  rcases VEnv.addProjections_iff.mp hproj with ⟨entry, hentry, hentryName, rfl⟩ | hold
  · rw [hdata.projections] at hentry
    obtain ⟨type, htype, ctor, hctorsType, rfl⟩ := VInductDecl.projectionEntries_origin hentry
    have heq : family = type :=
      VInductDecl.type_eq_of_mem_name hdata.sourceWF.2.1 hmem htype hentryName
    subst heq
    obtain ⟨_, direct, _, _, _, hfamilies⟩ := hdata.correspondence
    have hlen := Lean4Lean.List.Forall₂.length_eq hfamilies
    have hdecl : owner.val < schema.signature.declaration.types.length := by
      simp [declaration]
    have hrel := Lean4Lean.List.Forall₂.getElem_of hfamilies owner.val hdecl
      (by rw [← hlen]; exact hdecl)
    have hfam : schema.signature.declaration.types[owner.val] =
        schema.signature.declarationFamily owner := by
      simp [declaration, declarationFamily]
    rw [hfam, List.getElem_append_left hlt, hget] at hrel
    rw [view_constructor_names, ctorNames_eq_of_forall₂ hrel.constructors (fun _ _ h => h.1),
      hctorsType]
    rfl
  · exfalso
    rw [VEnv.addConstVals_projections hctors, VEnv.addConstVals_projections htypes] at hold
    obtain ⟨c, hc⟩ := hbase.ordered.projectionConstant hold
    have hfresh := VEnv.addConstVals_names_fresh htypes family.toVConstVal (by
      rw [hdata.types]
      exact List.mem_map.mpr ⟨family, hmem, rfl⟩)
    have hfresh' : base.constants family.name = none := hfresh
    rw [hfresh'] at hc
    contradiction

/-- Constant checking preserves the registry, so freshness transports to
the constructor environment, where the case schemas become available. -/
theorem Fresh.of_registry_eq {schema : CaseSchema} {base env : VEnv}
    (H : schema.Fresh base key) (heq : env.eliminators = base.eliminators) :
    schema.Fresh env key := by
  unfold Fresh at *
  rw [heq]
  exact H

/-- Register all case schemas immediately after source headers and
constructors. The case certificate suffices; the generated
recursors and their equations are neither installed nor assumed correct. -/
theorem RegistrationCertificate.register_after_constructors {schema : CaseSchema}
    {base envTypes envCtors : VEnv}
    (R : schema.RegistrationCertificate base source block key) (hbase : base.WF)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors)
    (hprojs : schema.ProjNamesRegistered envCtors key) :
    (envCtors.addEliminator key schema).WF := by
  have H := R.certified
  have hkey := R.keyHead
  have hcompat : schema.StructCompat envCtors :=
    StructCompat.of_projections (H.structCompat hbase htypes hctors)
      VEnv.addProjections_le.projections
  have hctorsWF : envCtors.WF := by
    obtain ⟨expanded, auxiliaries, hdata, _, _⟩ := H
    obtain ⟨types, ctors, ht, hc, htypesWF, hctorsWF⟩ := hdata.sourceWF.2.2.2.2
    rw [hdata.types] at htypes
    rw [htypes] at ht
    cases ht
    rw [hdata.ctors] at hctors
    apply VEnv.WF.addConstVals (cis := source.constructorConstants) _ hctorsWF hctors
    apply VEnv.WF.addConstVals hbase _ htypes
    intro value hvalue
    obtain ⟨family, hfamily, rfl⟩ := List.mem_map.mp hvalue
    exact htypesWF family hfamily
  have hfresh := (H.fresh hbase hkey).of_registry_eq
    ((VEnv.addConstVals_eliminators hctors).trans (VEnv.addConstVals_eliminators htypes))
  have hcoherent : source.ProjectionsCoherent envCtors := by
    intro type htype info hinfo
    exfalso
    rw [VEnv.addConstVals_projections hctors, VEnv.addConstVals_projections htypes] at hinfo
    obtain ⟨ci, hci⟩ := hbase.ordered.projectionConstant hinfo
    obtain ⟨expanded, auxiliaries, hdata, _, _⟩ := H
    have hmem : type.toVConstVal ∈ block.types := by
      rw [hdata.types]; exact List.mem_map.mpr ⟨type, htype, rfl⟩
    have hfresh := VEnv.addConstVals_names_fresh htypes _ hmem
    change base.constants type.name = none at hfresh
    rw [hfresh] at hci
    cases hci
  apply hbase.inductEliminators hctorsWF
    ((VEnv.addConstVals_le htypes).trans (VEnv.addConstVals_le hctors)) R _
    ((VEnv.addConstVals_defeqs hctors).trans (VEnv.addConstVals_defeqs htypes)) hprojs
    hcoherent hfresh hcompat
  intro value hvalue
  rcases List.mem_append.mp hvalue with hvalue | hvalue
  · exact (VEnv.addConstVals_le hctors).constants (VEnv.addConstVals_get htypes hvalue)
  · exact VEnv.addConstVals_get hctors hvalue

end InductiveSignature.CaseSchema

namespace VInductBlock
open InductiveSignature

/-- The constructor environment of a declaration installed from its checked source is well
formed. -/
theorem _root_.Lean4Lean.VInductDecl.SourceWF.ctorsWF {base envTypes envCtors : VEnv}
    {decl : VInductDecl} (hsource : decl.SourceWF base) (hbase : base.WF)
    (htypes : base.addConstVals decl.typeConstants = some envTypes)
    (hctors : envTypes.addConstVals decl.constructorConstants = some envCtors) :
    envCtors.WF := by
  obtain ⟨types, ctors, ht, hc, htypesWF, hctorsWF⟩ := hsource.2.2.2.2
  rw [htypes] at ht
  cases ht
  apply VEnv.WF.addConstVals (cis := decl.constructorConstants) _ hctorsWF hctors
  apply VEnv.WF.addConstVals hbase _ htypes
  intro value hvalue
  obtain ⟨family, hfamily, rfl⟩ := List.mem_map.mp hvalue
  exact htypesWF family hfamily

/-- The constructor environment of a block, extended by its certified eliminators, is well
formed. -/
theorem EliminatorsWF.elimWF {base envTypes envCtors : VEnv} {decl : VInductDecl}
    {block : VInductBlock} (H : VInductBlock.EliminatorsWF base decl block) (hbase : base.WF)
    (hsource : decl.SourceWF base) (htypesSource : block.types = decl.typeConstants)
    (hctorsSource : block.ctors = decl.constructorConstants)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors) :
    (envCtors.addEliminators block.eliminators).WF := by
  obtain ⟨envTypes', envCtors', ht', hc', H⟩ := H
  cases htypes.symm.trans ht'
  cases hctors.symm.trans hc'
  rcases H with ⟨-, hE⟩ | ⟨key, schema, hE, hreg, hprojs⟩
  · rw [hE]
    exact hsource.ctorsWF hbase (htypesSource ▸ htypes) (hctorsSource ▸ hctors)
  · rw [hE]
    exact hreg.register_after_constructors hbase htypes hctors hprojs

end VInductBlock
end Lean4Lean
