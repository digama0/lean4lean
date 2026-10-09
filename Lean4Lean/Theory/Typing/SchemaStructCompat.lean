import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Inductive.CaseRegistration

/-!
# Compatibility of eliminator schemas with registered structures

`VEnv.WF'.inductEliminators` requires each new schema to be compatible with the
structures already registered over its source families
(`CaseSchema.StructCompat`). Without this premise a schema can add constructors to a
registered structure, and the environment is inconsistent: register
`structure Unit : Type` with constructor `Unit.mk`, add an axiom `other : Unit`, and register a
schema (compiled in the empty base) for `inductive Unit : Type | mk | other`. Then
`elim C a b Unit.mk ≡ a` and `elim C a b other ≡ b` (generic equations), while `unitLike` gives
`Unit.mk ≡ other`; with `C := fun _ => Type`, `a := Prop`, `b := Prop → Prop` this derives
`Prop ≡ (Prop → Prop)`.

`SchemaStructCompat env`: for every registered schema and every registered structure `s` that is
a source family of the schema (at source slot `owner`), the schema's constructors of that slot
are exactly the structure's constructor. It holds in every well-formed environment: the premise
gives it for the projections present when a schema is registered, and every later projection
names a constant that is fresh at its registration, whereas the source families of a registered
schema are installed constants (`VEnv.WF.eliminator_family_present`).
-/

namespace Lean4Lean

/-- Every registered structure that is a source family of a registered schema has, in the
schema, exactly its registered constructor. -/
def SchemaStructCompat (env : VEnv) : Prop :=
  ∀ {key : Name} {schema : InductiveSignature.CaseSchema} {s : Name} {info : VProjectionInfo},
    env.eliminators key schema → env.projections s info →
    ∀ owner : Fin schema.signature.families.size,
      schema.sourceFamilies[owner.val]? = some s →
      (schema.view owner).constructors.toList.map (·.name) = [info.ctorName]

/-- Projections registered by the entries of one inductive declaration name its
families, which are fresh in the environment the families are added to. -/
private theorem projectionEntries_fresh {base envTypes : VEnv} {decl : VInductDecl}
    {block : VInductBlock} (htypesSource : block.types = decl.typeConstants)
    (hprojections : block.projections = decl.projectionEntries)
    (htypes : base.addConstVals block.types = some envTypes)
    {entry : VProjectionEntry} (hentry : entry ∈ block.projections) :
    base.constants entry.typeName = none := by
  rw [hprojections] at hentry
  obtain ⟨type, htype, _, _, rfl⟩ := VInductDecl.projectionEntries_origin hentry
  exact VEnv.addConstVals_names_fresh htypes type.toVConstVal (by
    rw [htypesSource]
    exact List.mem_map.mpr ⟨type, htype, rfl⟩)

/-- A declaration step registers projections only for names that are fresh before it. -/
private theorem VDecl.WF.projections_fresh (H : VDecl.WF env decl env')
    (hproj : env'.projections s info) : env.projections s info ∨ env.constants s = none := by
  cases H with
  | «axiom» _ h | «opaque» _ h => exact .inl (by rwa [VEnv.addConst_projections h] at hproj)
  | «def» _ h => exact .inl (by rw [← VEnv.addConst_projections h]; exact hproj)
  | «example» => exact .inl hproj
  | mutualDef _ h _ =>
    exact .inl (by rwa [VEnv.addDefEqs_projections, VEnv.addConsts_projections h] at hproj)
  | quot _ h => exact .inl (by rwa [VEnv.addQuot_projections h] at hproj)
  | induct h =>
    cases h with
    | intro _ hcompile _ _ h =>
      obtain ⟨types, ctors, recs, ht, hc, hr, rfl⟩ := VInductBlock.install_stages h
      rw [VEnv.addDefEqRules_projections, VEnv.addConstVals_projections hr,
        VEnv.addProjections_iff, VEnv.addEliminators_projections, VEnv.addConstVals_projections hc,
        VEnv.addConstVals_projections ht] at hproj
      rcases hproj with ⟨entry, hentry, rfl, _⟩ | hold
      · exact .inr (projectionEntries_fresh hcompile.types hcompile.projections ht hentry)
      · exact .inl hold

/-- The projections of an installed block are those of its constructor stage extended by the
block's own projection entries. -/
private theorem install_projections {env env' envTypes envCtors : VEnv} {block : VInductBlock}
    (H : VInductBlock.install env block = some env')
    (ht : env.addConstVals block.types = some envTypes)
    (hc : envTypes.addConstVals block.ctors = some envCtors)
    (hproj : env'.projections s info) :
    (envCtors.addProjections block.projections).projections s info := by
  obtain ⟨types, ctors, recs, ht', hc', hr, rfl⟩ := VInductBlock.install_stages H
  cases ht.symm.trans ht'
  cases hc.symm.trans hc'
  rw [VEnv.addDefEqRules_projections, VEnv.addConstVals_projections hr,
    VEnv.addProjections_iff, VEnv.addEliminators_projections] at hproj
  exact VEnv.addProjections_iff.mpr hproj

/-- A projection that is new at some step names a constant that was fresh before the step, so it
is not a source family of a schema registered before the step. -/
private theorem fresh_not_family {env : VEnv} (H : env.WF)
    (hlookup : env.eliminators key schema) (hfresh : env.constants s = none)
    {owner : Nat} (hname : schema.sourceFamilies[owner]? = some s) : False := by
  obtain ⟨value, hvalue⟩ := H.eliminator_family_present hlookup (List.mem_of_getElem? hname)
  rw [hfresh] at hvalue
  contradiction

/-- Every well-formed history satisfies `SchemaStructCompat`. -/
theorem VEnv.WF'.schemaStructCompat {ds : List VDecl} {env : VEnv} (H : env.WF' ds) :
    SchemaStructCompat env := by
  induction H with
  | empty => intro _ _ _ _ hlookup; cases hlookup
  | @decl env' d env ds h henv ih =>
    intro key schema s info hlookup hproj owner hname
    rcases h.eliminators_iff.mp hlookup with
      ⟨source, -, block, envTypes, envCtors, -, -, -, hinstall, ht, hc, -, hreg, -⟩ | hlookup
    · exact hreg.certified.structCompat ⟨_, henv⟩ ht hc (install_projections hinstall ht hc hproj) owner hname
    rcases h.projections_fresh hproj with hold | hfresh
    · exact ih hlookup hold owner hname
    · exact (fresh_not_family ⟨_, henv⟩ hlookup hfresh hname).elim
  | inductProjections hbase _ hcovered _ _ _ _ _ _ htypesSource hctorsSource hprojections htypes
      hctors _ ih =>
    intro key schema s info hlookup hproj owner hname
    simp only [VEnv.addProjections_eliminators] at hlookup
    rcases VEnv.addProjections_iff.mp hproj with ⟨entry, hentry, rfl, hinfo⟩ | hold
    · rcases VEnv.addEliminators_iff.mp hlookup with hmem | hlookup
      · obtain ⟨key', schema', hE, hreg⟩ := hcovered
        rw [hE, List.mem_singleton, Prod.mk.injEq] at hmem
        obtain ⟨rfl, rfl⟩ := hmem
        exact hreg.certified.structCompat ⟨_, hbase⟩ htypes hctors
          (VEnv.addProjections_iff.mpr (.inl ⟨entry, hentry, rfl, hinfo⟩)) owner hname
      rw [VEnv.addConstVals_eliminators hctors, VEnv.addConstVals_eliminators htypes] at hlookup
      exact (fresh_not_family ⟨_, hbase⟩ hlookup
        (projectionEntries_fresh htypesSource hprojections htypes hentry) hname).elim
    · exact ih hlookup hold owner hname
  | inductEliminators _ _ _ _ _ _ _ _ _ hcompat _ ih =>
    intro key schema s info hlookup hproj owner hname
    rcases hlookup with ⟨rfl, rfl⟩ | hlookup
    · exact hcompat hproj owner hname
    · exact ih hlookup hproj owner hname

theorem VEnv.WF.schemaStructCompat {env : VEnv} (H : env.WF) : SchemaStructCompat env :=
  VEnv.WF'.schemaStructCompat H.choose_spec

end Lean4Lean
