import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceConstructors
import Lean4Lean.Verify.Inductive.Nested.Restoration.TableAgreement

/-! Restoration of the lowered constructor types of the source families of a
validated nested run (the `loweredConstructors` field of
`LoweredConstructorsRestore`).

`NestedRun.restorationTablesRestoring` expands every source
constructor type into the corresponding lowered constructor type by leaves
that `compilationRestoration` inverts (`Restoration.RestoringLeaf`), so
restoration maps each lowered constructor type syntactically back to its
source constructor type (`VExpr.NestedExprExpansion.restore`), given that

* the source constructor types avoid the restorable names (they are typed in
  the source header environment, where these names are fresh), and
* every restoration head occurs in the lowered constructor types at the
  declaration's own universe parameters (`VExpr.ConstLevelsAt`).

The second fact is a premise here; it is discharged by
`NestedRun.loweredConstructorLevels_heads` (in
`Nested/Lowering/Levels.lean`): the executable lowering emits each auxiliary
occurrence at `state.lvls`, which is initialised to the declaration's level
parameters and never modified, as recorded by the relations describing the lowering run
(`NestedAuxLE`, `ConstructorLowering.Resolved.lvls`, `NestedLowering.lvls`).
-/

namespace Lean4Lean

open InductiveSignature

namespace VerifyInductive

open Lean hiding Environment Exception
open Kernel

/-- The restorable names of the compilation restoration of a validated nested
run (the auxiliary family and constructor names, and the auxiliary recursor
names) are fresh in the source header environment. -/
theorem NestedRun.restorableNames_fresh
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (SpecializationGenerates
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.lowered.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.lowered.loweredDecl.types ++
      E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup) :
    ∀ name ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      envTypes.constants name = none := by
  have hinit : E.lowered.initialEnv =
      ves.venv (if isUnsafe then .unsafe else .safe) := E.lowered_initialEnv
  have hloweredTypes : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      E.lowered.loweredDecl.typeConstants =
        some E.lowered.constructors.toConstructorCheck.headerVEnv :=
    Eq.mp (congrArg (fun env : VEnv => env.addConstVals
        E.lowered.loweredDecl.typeConstants =
          some E.lowered.constructors.toConstructorCheck.headerVEnv) hinit)
      E.lowered.constructors.toConstructorCheck.core.typesAdded
  have hloweredCtors := E.lowered.constructors.toConstructorCheck.core.ctorsAdded
  have Hsource := E.sourceCore.core
  rw [E.sourceCoreDecl_eq] at Hsource
  have hsourceLength : sourceDecl.types.length = sourceTypes.length :=
    (TrInductDeclCore.types_length Hsource).symm
  have hprefix : sourceDecl.typeConstants =
      E.lowered.loweredDecl.typeConstants.take sourceDecl.types.length := by
    have h := E.sourceCore.sourceTypeValues
    rw [E.sourceCoreDecl_eq] at h
    rw [h, VInductDecl.typeConstants, List.map_take, hsourceLength]
  have hsourceTypesEq : sourceDecl.types.map VInductiveType.toVConstVal =
      (E.lowered.loweredDecl.types.take sourceDecl.types.length).map
        VInductiveType.toVConstVal := by
    have := hprefix
    simp only [VInductDecl.typeConstants] at this
    rw [this, List.map_take]
  have Hmodels : E.lowered.signature.Models
      (ves.venv (if isUnsafe then .unsafe else .safe)) E.lowered.loweredDecl := by
    have h := E.lowered.recursorConstruction.generator.models
    change E.lowered.signature.Models E.lowered.initialEnv
      E.lowered.loweredDecl at h
    rwa [hinit] at h
  have hfamNodup : (familyNames (E.lowered.loweredDecl.types.take sourceDecl.types.length) ++
      familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length)).Nodup := by
    have h := (List.nodup_append.mp hnodup).1
    rw [← List.take_append_drop sourceDecl.types.length E.lowered.loweredDecl.types] at h
    simpa only [familyNames, List.flatMap_append] using h
  have hsourceEntry : ∀ entry ∈ sourceDecl.typeConstants, ∃ t ∈
      E.lowered.loweredDecl.types.take sourceDecl.types.length,
        entry = t.toVConstVal := by
    intro entry hentry
    rw [VInductDecl.typeConstants, hsourceTypesEq] at hentry
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hentry
    exact ⟨t, ht, rfl⟩
  have hbaseLE : (ves.venv (if isUnsafe then .unsafe else .safe)) ≤
      E.lowered.constructors.toConstructorCheck.headerVEnv := VEnv.addConstVals_le hloweredTypes
  have hbaseFresh : ∀ name ∈ familyNames
      (E.lowered.loweredDecl.types.drop sourceDecl.types.length),
      (ves.venv (if isUnsafe then .unsafe else .safe)).constants name = none := by
    intro name hname
    obtain ⟨t, ht, rfl | ⟨c, hc, rfl⟩⟩ := mem_familyNames.mp hname
    · exact (VEnv.addConstVals_names_fresh hloweredTypes).2 t.toVConstVal
        (List.mem_map.mpr ⟨t, List.mem_of_mem_drop ht, rfl⟩)
    · have hmem : c ∈ E.lowered.loweredDecl.constructorConstants :=
        List.mem_flatMap.mpr ⟨t, List.mem_of_mem_drop ht, hc⟩
      exact VEnv.LE.constants_eq_none_left hbaseLE
        ((VEnv.addConstVals_names_fresh hloweredCtors).2 c hmem)
  have hheadNames : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length) := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have hfresh : ∀ name ∈ (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary),
      envTypes.constants name = none := by
    rw [hheadNames]
    intro name hname
    cases hc : envTypes.constants name with
    | none => rfl
    | some ci =>
      exfalso
      rcases VEnv.addConstVals_lookup_cases hadded hc with hbase | ⟨entry, hentry, hn, -⟩
      · rw [hbaseFresh name hname] at hbase; cases hbase
      · obtain ⟨t, ht, rfl⟩ := hsourceEntry entry hentry
        have h1 : name ∈ familyNames
            (E.lowered.loweredDecl.types.take sourceDecl.types.length) :=
          mem_familyNames.mpr ⟨t, ht, .inl hn.symm⟩
        exact (List.nodup_append.mp hfamNodup).2.2 _ h1 _ hname rfl
  have hrecursorsAdded := E.lowered.recursors.installed.abstract
  have hrecursorValues : E.lowered.recursors.entries.map Prod.snd =
      E.lowered.generatedInstance.recursors :=
    E.lowered.recursors.recursors
  rw [hrecursorValues, E.lowered.constructors.toConstructorCheck.contextVEnv]
    at hrecursorsAdded
  have hrecursorsFresh := VEnv.addConstVals_names_fresh hrecursorsAdded
  simp only [VEnv.addEliminators_constants, VEnv.addProjections_constants] at hrecursorsFresh
  have hctorFresh : ∀ recursor ∈ E.lowered.generatedInstance.recursors,
      E.lowered.constructors.toConstructorCheck.ctorVEnv.constants recursor.name = none :=
    hrecursorsFresh.2
  have hbaseCtorLE : (ves.venv (if isUnsafe then .unsafe else .safe)) ≤
      E.lowered.constructors.toConstructorCheck.ctorVEnv :=
    hbaseLE.trans (VEnv.addConstVals_le hloweredCtors)
  have hrecBase : ∀ t ∈ E.lowered.loweredDecl.types,
      (ves.venv (if isUnsafe then .unsafe else .safe)).constants (t.name.str "rec") = none := by
    intro t ht
    obtain ⟨d, hd, hdname, -⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_r Hmodels.families t ht
    simp only [InductiveSignature.declaration, List.mem_map] at hd
    obtain ⟨⟨f, i⟩, hfi, rfl⟩ := hd
    have hf : f ∈ E.lowered.signature.families.toList :=
      List.fst_mem_of_mem_zipIdx hfi
    obtain ⟨j, hj, hjf⟩ := List.getElem_of_mem hf
    let owner : Fin E.lowered.signature.families.size :=
      ⟨j, by simpa using hj⟩
    have hname : E.lowered.generatedInstance.recursorName owner = t.name.str "rec" := by
      have h := E.lowered.recursorConstruction.generator.names owner
      change E.lowered.generatedInstance.recursorName owner =
        E.lowered.signature.families[owner].name.str "rec" at h
      rw [h, ← hdname]
      simp only [owner, ← hjf, Array.getElem_toList, Fin.getElem_fin]
    have hmem : E.lowered.generatedInstance.recursor owner ∈
        E.lowered.generatedInstance.recursors :=
      List.mem_map.mpr ⟨owner, List.mem_finRange owner, rfl⟩
    have := hctorFresh _ hmem
    change E.lowered.constructors.toConstructorCheck.ctorVEnv.constants
      (E.lowered.generatedInstance.recursorName owner) = none at this
    rw [hname] at this
    exact VEnv.LE.constants_eq_none_left hbaseCtorLE this
  have hrecFresh : ∀ p ∈ (compilationRestoration sourceDecl auxiliaries).recursors,
      envTypes.constants p.1 = none := by
    intro p hp
    have hp1 : p.1 ∈ auxiliaries.map (fun a => a.auxiliary.str "rec") := by
      rw [← compilationRestoration_recursors_fst]
      exact List.mem_map_of_mem hp
    obtain ⟨a, ha, hpa⟩ := List.mem_map.mp hp1
    have haux : a.auxiliary ∈
        (E.lowered.loweredDecl.types.drop sourceDecl.types.length).map (·.name) := by
      rw [← auxiliarySpecializations_names Haux Hexpansion]
      exact List.mem_map_of_mem ha
    obtain ⟨t, ht, hta⟩ := List.mem_map.mp haux
    rw [← hpa, ← hta]
    cases hc : envTypes.constants (t.name.str "rec") with
    | none => rfl
    | some ci =>
      exfalso
      rcases VEnv.addConstVals_lookup_cases hadded hc with hbase | ⟨entry, hentry, hn, -⟩
      · rw [hrecBase t (List.mem_of_mem_drop ht)] at hbase; cases hbase
      · obtain ⟨t', ht', rfl⟩ := hsourceEntry entry hentry
        have h1 : t'.name ∈ familyNames E.lowered.loweredDecl.types :=
          mem_familyNames.mpr ⟨t', List.mem_of_mem_take ht', .inl rfl⟩
        have h2 : t.name.str "rec" ∈ E.lowered.loweredDecl.types.map
            (fun t => t.name.str "rec") :=
          List.mem_map_of_mem (f := fun t : VInductiveType => t.name.str "rec")
            (List.mem_of_mem_drop ht)
        exact (List.nodup_append.mp hnodup).2.2 _ h1 _ h2 hn
  intro name hname
  rcases List.mem_append.mp hname with h | h
  · exact hfresh name h
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    exact hrecFresh p hp

end VerifyInductive

end Lean4Lean
