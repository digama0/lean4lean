import Lean4Lean.Verify.Inductive.Nested.Restoration.Base
import Lean4Lean.Verify.Inductive.Nested.Restoration.KernelData
import Lean4Lean.Verify.Environment.Blocks
import Lean4Lean.Verify.Inductive.Nested.Restoration.RecursorTranslations
import Lean4Lean.Verify.Inductive.Nested.Restoration.Recursors
import Lean4Lean.Verify.Inductive.Nested.Restoration.RecursorShape
import Lean4Lean.Verify.Inductive.Nested.Restoration.TableAgreement
import Lean4Lean.Verify.Inductive.Nested.Restoration.ContainerSpecializations
import Lean4Lean.Verify.Inductive.Nested.Restoration.CompilationDataConstructors
import Lean4Lean.Verify.Inductive.Nested.Restoration.RuleConstructors
import Lean4Lean.Verify.Inductive.Nested.Restoration.RecursorRenaming
import Lean4Lean.Verify.Inductive.Install.RecursorShapesOf

/-! # The telescopes of the restored recursors

`RecursorShapesAt` of every restored kernel recursor in the recursor stage of a restored block
base, read by `NestedRun.assemblyRecursors` (`AssemblyRecursors.lean`) for
`RestoredBlock.recShapes`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-- The restored recursors of a run are the restoration steps at the recursor names (the
`rvals_steps` of `AssemblyRecursors.lean`, restated here below it). -/
private theorem rvals_steps_aux {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceEnv : Environment} {auxRec : NameMap Name} {allIndNames : List Name}
    {types : List InductiveType} {auxRecNames : List Name} {out : Unit × Environment}
    (H : NestedRestorationFolds result loweredEnv sourceEnv auxRec allIndNames types auxRecNames
      out) :
    List.Forall₂ (fun (n : Name) (rv : RecursorVal) => ∃ (s t : Environment)
        (Hs : RestoredRecursorStep result loweredEnv auxRec allIndNames n s t),
        Hs.restored.newInfo = rv)
      (types.map (fun t => Lean.mkRecName t.name) ++ auxRecNames) H.rvals := by
  have h1 : ∀ {types : List InductiveType} {sourceEnv targetEnv : Environment}
      (H : FoldSteps (RestoredInductiveStep result loweredEnv auxRec allIndNames) types
        sourceEnv targetEnv),
      List.Forall₂ (fun (n : Name) (rv : RecursorVal) => ∃ (s t : Environment)
          (Hs : RestoredRecursorStep result loweredEnv auxRec allIndNames n s t),
          Hs.restored.newInfo = rv)
        (types.map (fun t => Lean.mkRecName t.name)) H.inductiveRecs := by
    intro types sourceEnv targetEnv H
    induction H with
    | nil => exact .nil
    | cons h t ih => exact .cons ⟨_, _, h.restored.recursor, rfl⟩ ih
  have h2 : ∀ {names : List Name} {sourceEnv targetEnv : Environment}
      (H : FoldSteps (RestoredRecursorStep result loweredEnv auxRec allIndNames) names
        sourceEnv targetEnv),
      List.Forall₂ (fun (n : Name) (rv : RecursorVal) => ∃ (s t : Environment)
          (Hs : RestoredRecursorStep result loweredEnv auxRec allIndNames n s t),
          Hs.restored.newInfo = rv)
        names H.recursorInfos := by
    intro names sourceEnv targetEnv H
    induction H with
    | nil => exact .nil
    | cons h t ih => exact .cons ⟨_, _, h, rfl⟩ ih
  exact Lean4Lean.List.Forall₂.append (h1 H.inductives) (h2 H.auxiliaries)

/-- Every restored recursor of a run is the restoration step at the recursor name of a
generated owner. -/
theorem NestedRun.rval_step
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv L)
    (hnonempty : sourceTypes ≠ []) {rv : RecursorVal} (hrv : rv ∈ E.restoration.rvals) :
    ∃ (owner : Fin E.lowered.recursors.generationSignature.families.size) (s t : Environment)
      (Hs : RestoredRecursorStep result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 (sourceTypes.map (·.name))
        (E.lowered.recursors.canonicalGeneration.recursorName owner) s t),
      Hs.restored.newInfo = rv := by
  have hsteps := rvals_steps_aux E.restoration
  rw [← E.recursorNames_order hnonempty, Lean4Lean.List.forall₂_map_left_iff] at hsteps
  obtain ⟨owner, -, s, t, Hs, h⟩ := Lean4Lean.List.Forall₂.forall_exists_r hsteps rv hrv
  exact ⟨owner, s, t, Hs, h⟩

/-- **The recursor shape of every restored recursor**, without its rules, in the recursor
stage of the base (`RestoredRecursorShape`, whose `k` clause is the premise `hk`). -/
theorem NestedRun.restoredRecursorShapeOf
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    (C : RestoredBlockBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.loweredDecl = E.lowered.loweredDecl)
    (hk : ∀ rv ∈ E.restoration.rvals, rv.k = false) :
    ∃ auxiliaries : List ContainerSpecialization, ∀ rv ∈ E.restoration.rvals,
      ∃ owner, RestoredRecursorShape E.lowered.generatedInstance
        (compilationRestoration sourceDecl auxiliaries) C.recursorVEnv owner rv := by
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, auxiliaries, hadded, henvTypes, Haux, Hexpansion,
      hparamsSize, D, Hrestoring, HauxRestoring, -⟩
  have hnodup :
      (familyNames E.lowered.loweredDecl.types ++
        E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  obtain ⟨-, -, -, -, -, -, -, hscoped, -, -, -, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D True.intro
  have hrecs := E.restoredRecursorList_of_paramUniform C hC wf Hsources hadded Haux Hexpansion
    hnodup hparamsSize D hscoped
  have hrecTypes : ∀ owner, ∃ t, (compilationRestoration sourceDecl auxiliaries).expr
      (E.lowered.generatedInstance.recursorType owner) = some t := by
    intro owner
    have Hm := List.mapM_eq_some.mp hrecs
    obtain ⟨v, -, hv⟩ := Lean4Lean.List.Forall₂.forall_exists_l Hm _
      (List.mem_map_of_mem (List.mem_finRange owner))
    simp only [Restoration.recursor, Option.bind_eq_bind, Option.pure_def] at hv
    cases ht : (compilationRestoration sourceDecl auxiliaries).expr
        (E.lowered.generatedInstance.recursor owner).type with
    | none => simp [ht] at hv
    | some t => exact ⟨t, ht⟩
  obtain ⟨rules, hrulesEq⟩ := E.lowered.generatedInstance.restoredEquations_isSome _
    hrecTypes (fun owner => E.recursorName_not_head Haux Hexpansion hnodup owner)
  have hequations : E.lowered.generatedInstance.restoredEquations
      (compilationRestoration sourceDecl auxiliaries) = some (rules ++ []) := by
    rw [List.append_nil]; exact hrulesEq
  obtain ⟨-, ⟨Hdata⟩⟩ := E.compilationData_of_tables wf Hsources C hC rules []
    hadded henvTypes Haux Hexpansion hparamsSize D Hrestoring HauxRestoring hequations
  have htypesEq : C.install.venvTypes = envTypes := by
    have h := C.install.abstract_types
    rw [C.typeValues, hadded] at h
    exact (Option.some.inj h).symm
  have hctorsAdded : envTypes.addConstVals sourceDecl.constructorConstants =
      some C.install.venvCtors := by
    have h := C.install.abstract_ctors
    rwa [C.constructorValues, htypesEq] at h
  have hsourceCtorNames := C.sourceConstructorNames
  rw [hC] at hsourceCtorNames
  have hfresh := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hfreshCtors := E.restorableNames_fresh_ctors hadded Haux Hexpansion hnodup
    hsourceCtorNames hctorsAdded
  refine ⟨auxiliaries, fun rv hrv => ?_⟩
  obtain ⟨owner, s, t, Hs, rfl⟩ := E.rval_step C.sourceNonempty hrv
  obtain ⟨htype, hnp, hni, hnm, hnmin⟩ := E.restoredRecursorShapeFields C hC wf Hsources hadded
    Haux Hexpansion hnodup hparamsSize D hscoped owner Hs
  obtain ⟨head, -, hheadName, -, hargs, happ, -⟩ :=
    Hdata.restoredFamilyHead_spec hadded hctorsAdded hfresh hfreshCtors owner
  refine ⟨owner, {
    type := htype
    numParams := hnp
    numIndices := hni
    numMotives := hnm
    numMinors := hnmin
    k := hk _ hrv
    specialization := ⟨head, ?_, hargs, happ⟩ }⟩
  rw [E.restoredMajorInduct wf Hsources Haux Hexpansion hnodup hparamsSize D hscoped
    owner Hs, hheadName]

/-- **The rule-free telescope shapes of the restored recursors** in the recursor stage of the
base, as `NestedRun.strippedValid` reads them. -/
theorem NestedRun.restoredRecursorTelescopes
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    (C : RestoredBlockBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.loweredDecl = E.lowered.loweredDecl)
    (hk : ∀ rv ∈ E.restoration.rvals, rv.k = false) :
    ∀ r ∈ E.restoration.rvals, ∃ cnparams indLevels ctorParams,
      Nonempty (VRecursorShape C.recursorVEnv r.name r.levelParams.length r.numParams
        cnparams r.numMotives r.numMinors r.numIndices r.getMajorInduct indLevels ctorParams) := by
  obtain ⟨auxiliaries, H⟩ := E.restoredRecursorShapeOf wf Hsources C hC hk
  intro r hr
  obtain ⟨owner, S⟩ := H r hr
  obtain ⟨head, -, hshape⟩ := S.shape
  exact ⟨_, _, _, hshape⟩

/-- The constructor and field count of every restored rule of a restored recursor (the `ctor`
and `nfields` clauses of `NestedRun.trRestoredRules`, which need no rule translation). -/
theorem NestedRun.restoredRuleCtorFields
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv L)
    {auxiliaries : List ContainerSpecialization} {venv : VEnv}
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hctorNames : ∀ a ∈ auxiliaries, ∀ ctor ∈ a.source.ctors,
      result.restoreCtorName E.loweredEnv (a.constructorName ctor) =
        (compilationRestoration sourceDecl auxiliaries).restoredHeadName
          (a.constructorName ctor))
    (hrecNames : ∀ owner, E.lowered.generatedInstance.recursorName owner =
      E.lowered.signature.families[owner].name.str "rec")
    (hheadsNotRec : ∀ owner, ∀ head ∈ (compilationRestoration sourceDecl auxiliaries).heads,
      head.auxiliary ≠ E.lowered.generatedInstance.recursorName owner)
    {X : List Name}
    (hfreshFinal : ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      n ∉ X → venv.constants n = none)
    (hauxRec : ∀ a ∈ auxiliaries, a.auxiliary.str "rec" ∉ X)
    (owner : Fin E.lowered.signature.families.size)
    {s t : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name))
      (E.lowered.generatedInstance.recursorName owner) s t)
    (hinstalled : venv.constants Hstep.restored.newInfo.name ≠ none)
    (head : RestoredFamilyHead)
    (Hctor : ∀ index : Fin E.lowered.signature.constructors.size,
      E.lowered.signature.constructors[index].owner = owner →
        (((compilationRestoration sourceDecl auxiliaries).heads.find?
            (fun h => h.auxiliary ==
              E.lowered.signature.families[owner].name) = none ∧
          (compilationRestoration sourceDecl auxiliaries).restoredHeadName
            E.lowered.signature.constructors[index].name =
              E.lowered.signature.constructors[index].name) ∨
          ∃ a ∈ auxiliaries, E.lowered.signature.families[owner].name =
              a.auxiliary ∧
            ∃ ctor ∈ a.source.ctors, E.lowered.signature.constructors[index].name =
              a.constructorName ctor) ∧
        (compilationRestoration sourceDecl auxiliaries).expr
          (E.lowered.generatedInstance.constructorApp
            E.lowered.signature.constructors[index]
            (E.lowered.signature.families.size +
              E.lowered.signature.constructors.size) 0) =
          some (VExpr.mkApps (.const ((compilationRestoration sourceDecl auxiliaries).restoredHeadName
              E.lowered.signature.constructors[index].name) head.levels)
            (head.arguments.map (fun arg => arg.liftN
              (E.lowered.signature.families.size +
                E.lowered.signature.constructors.size +
                E.lowered.signature.constructors[index].fields.length)) ++
              vars E.lowered.signature.constructors[index].fields.length 0))) :
    List.Forall₂ (fun (index : Fin E.lowered.signature.constructors.size)
        (rule : Lean.RecursorRule) =>
        rule.ctor = (compilationRestoration sourceDecl auxiliaries).restoredHeadName
          E.lowered.signature.constructors[index].name ∧
        rule.nfields = E.lowered.signature.constructors[index].fields.length)
      (E.lowered.signature.ownedConstructors owner)
      Hstep.restored.newInfo.rules := by
  let P := E.lowered.recursors
  obtain ⟨hi, hinfo⟩ := E.generatedEntryOfStep owner Hstep
  have RR := P.trRules P.ruleRhsTranslations owner hi
  rw [hinfo] at RR
  have hmap := P.ownedConstructors_map_val owner hi
  rw [hinfo] at hmap
  have R := Hstep.restored.restoration
  have hlenNew : Hstep.restored.newInfo.rules.length = Hstep.oldInfo.rules.length :=
    R.rules.length
  have hlenOwned : (E.lowered.signature.ownedConstructors owner).length =
      Hstep.oldInfo.rules.length := by
    have h2 : (P.generationSignature.ownedConstructors owner).length =
        Hstep.oldInfo.rules.length := by
      simpa using congrArg List.length hmap
    exact h2
  apply Lean4Lean.List.forall₂_of_getElem (hlenOwned.trans hlenNew.symm)
  intro j hj hjNew
  have hjOld : j < Hstep.oldInfo.rules.length := hlenOwned ▸ hj
  have hval := RuleAssembly.getElem_of_map_val_eq hmap j hj
  let index := (E.lowered.signature.ownedConstructors owner)[j]
  have hindexOwner : E.lowered.signature.constructors[index].owner = owner := by
    have hmem : index ∈ E.lowered.signature.ownedConstructors owner :=
      List.getElem_mem hj
    simp only [InductiveSignature.ownedConstructors, List.mem_filter, beq_iff_eq] at hmem
    exact hmem.2
  have RRj := Lean4Lean.List.forall₂_getElem RR j hj hjOld
  have Rj := R.rules.entry j hjOld hjNew
  obtain ⟨hclass, happ⟩ := Hctor index hindexOwner
  -- the restored constructor name
  have hrecMem : ∀ a ∈ auxiliaries, a.auxiliary.str "rec" ∈
      (compilationRestoration sourceDecl auxiliaries).recursors.map Prod.fst := by
    intro a ha
    obtain ⟨i, hi⟩ := InductiveSignature.mem_zipIdx_of_mem ha
    exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨(a, i), hi, rfl⟩, rfl⟩
  -- the restored constructor name
  have hctor : (Hstep.restored.newInfo.rules[j]'hjNew).ctor =
      (compilationRestoration sourceDecl auxiliaries).restoredHeadName
        E.lowered.signature.constructors[index].name := by
    rw [Rj.ctor, RRj.ctor]
    rcases hclass with ⟨hfind, hheadId⟩ | ⟨a, ha, hfam, ctor, hctor, hcName⟩
    · have hnotRec : E.lowered.generatedInstance.recursorName owner ∉
          (compilationRestoration sourceDecl auxiliaries).recursors.map Prod.fst := by
        intro hmem
        obtain ⟨pair, hpair, hpairName⟩ := List.mem_map.mp hmem
        obtain ⟨⟨a, i⟩, hai, rfl⟩ := List.mem_map.mp hpair
        have ha : a ∈ auxiliaries := List.fst_mem_of_mem_zipIdx hai
        have hfamName : E.lowered.signature.families[owner].name =
            a.auxiliary := by
          have h := hpairName.trans (hrecNames owner)
          exact (Name.str.inj h).1.symm
        have hmemHead : (⟨a.auxiliary, sourceDecl.uvars, sourceDecl.nparams, a.source.name,
            a.levels, a.arguments⟩ : HeadSpecialization) ∈
              (compilationRestoration sourceDecl auxiliaries).heads :=
          List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
        have := List.find?_eq_none.mp hfind _ hmemHead
        simp only [beq_iff_eq] at this
        exact this (by simpa using hfamName.symm)
      have hsame : Hstep.restored.newRecName =
          E.lowered.generatedInstance.recursorName owner := by
        rw [Hstep.restored.mappedName, nameMap_getD_eq, ← D.recursorName]
        exact Restoration.recursorName_of_not_mem hnotRec
      simp only [hsame, beq_self_eq_true, if_true]
      exact hheadId.symm
    · have hold : E.lowered.generatedInstance.recursorName owner =
          a.auxiliary.str "rec" := by
        rw [hrecNames owner, hfam]
      have hfreshOld : venv.constants (E.lowered.generatedInstance.recursorName owner) =
          none := by
        rw [hold]
        exact hfreshFinal _ (List.mem_append_right _ (hrecMem a ha)) (hauxRec a ha)
      have hne : (Hstep.restored.newRecName ==
          E.lowered.generatedInstance.recursorName owner) = false := by
        have : Hstep.restored.newRecName ≠
            E.lowered.generatedInstance.recursorName owner := by
          intro h
          apply hinstalled
          rw [R.name, h]
          exact hfreshOld
        simpa using this
      simp only [hne, Bool.false_eq_true, if_false]
      show result.restoreCtorName E.loweredEnv
          E.lowered.signature.constructors[index].name = _
      rw [hcName]
      exact hctorNames a ha ctor hctor
  exact ⟨hctor, Rj.nfields.trans RRj.nfields⟩

/-- The recursor shape of a restored recursor at a given restored family head (the proof of
`RestoredRecursorShape.shape` with the head fixed). -/
theorem restoredRecursorVShape {s : InductiveSignature} {g : Instance s}
    {r : Restoration} {venv : VEnv} {owner : Fin s.families.size}
    {rec : Lean.RecursorVal}
    (htype : ∃ type, r.expr (g.recursorType owner) = some type ∧
      venv.constants rec.name = some ⟨rec.levelParams.length, type⟩)
    (hnp : rec.numParams = s.params.length)
    (hni : rec.numIndices = s.families[owner].indices.length)
    (hnm : rec.numMotives = s.families.size)
    (hnmin : rec.numMinors = s.constructors.size)
    (head : RestoredFamilyHead) (hmajor : rec.getMajorInduct = head.name)
    (hargs : ∀ arg ∈ head.arguments, arg.ClosedN s.params.length)
    (happ : r.expr (g.familyApp owner
      (vars s.params.length
        (s.families.size + s.constructors.size + s.families[owner].indices.length))
      (vars s.families[owner].indices.length 0)) =
      some (VExpr.mkApps (.const head.name head.levels)
        (head.arguments.map (fun arg => arg.liftN
          (s.families.size + s.constructors.size + s.families[owner].indices.length)) ++
          vars s.families[owner].indices.length 0))) :
    Nonempty (VRecursorShape venv rec.name rec.levelParams.length rec.numParams
      head.arguments.length rec.numMotives rec.numMinors rec.numIndices
      rec.getMajorInduct head.levels head.arguments) := by
  rcases htype with ⟨type, htype, hconst⟩
  rcases r.expr_recursorType_eq_some htype with ⟨pre, major, hpre, hm, rfl⟩
  have hprelen : pre.length = s.params.length + s.families.size +
      s.constructors.size + s.families[owner].indices.length := by
    rw [← g.recursorPrefix_length owner]
    exact (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hpre)).symm
  have hmaj : major = VExpr.mkApps (.const head.name head.levels)
      (head.arguments.map (fun arg => arg.liftN
        (s.families.size + s.constructors.size + s.families[owner].indices.length)) ++
        vars s.families[owner].indices.length 0) := by
    have := hm.symm.trans happ
    exact Option.some.inj this
  refine ⟨{
    ctorParams_length := rfl
    ctorParams_closed := by rw [hnp]; exact hargs
    type := _
    const := hconst
    doms := pre ++ [major]
    result := g.recursorBody owner
    type_eq := rfl
    doms_length := by
      simp [hprelen, hnp, hnm, hnmin, hni]
    major_eq := ?_ }⟩
  rw [hnp, hnm, hnmin, hni, ← hprelen,
    List.getElem?_concat_length, hmaj, ← hmajor, InductiveSignature.vars_eq_bvarRange_add, Nat.add_zero]

/-- **The recursor and constructor telescopes of every restored kernel recursor** in the
recursor stage of the base (`RecursorShapesAt`, with its rules): the recursor telescope at the
restored family head, and for each rule the `VConstructorShape` of its restored constructor
(`CompilationData.restoredConstructorShape`), whose kernel `ctorInfo` has the head's argument
count as parameter count (`restoredRuleConstructors`). -/
theorem NestedRun.restoredRecursorShapes
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    (C : RestoredBlockBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.loweredDecl = E.lowered.loweredDecl)
    (hkernel : List.Perm
      ((C.typeEntries ++ C.constructorEntries ++ C.recursorEntries).map Prod.fst)
      E.restoration.entries) :
    ∀ rv ∈ E.restoration.rvals, RecursorShapesAt outEnv.constants C.recursorVEnv rv := by
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, auxiliaries, hadded, henvTypes, Haux, Hexpansion,
      hparamsSize, D, Hrestoring, HauxRestoring, Hkernel⟩
  have hnodup :
      (familyNames E.lowered.loweredDecl.types ++
        E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  obtain ⟨-, -, -, -, -, -, -, hscoped, -, hctorNames, -, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D True.intro
  have hrecs := E.restoredRecursorList_of_paramUniform C hC wf Hsources hadded Haux Hexpansion
    hnodup hparamsSize D hscoped
  have hrecTypes : ∀ owner, ∃ t, (compilationRestoration sourceDecl auxiliaries).expr
      (E.lowered.generatedInstance.recursorType owner) = some t := by
    intro owner
    have Hm := List.mapM_eq_some.mp hrecs
    obtain ⟨v, -, hv⟩ := Lean4Lean.List.Forall₂.forall_exists_l Hm _
      (List.mem_map_of_mem (List.mem_finRange owner))
    simp only [Restoration.recursor, Option.bind_eq_bind, Option.pure_def] at hv
    cases ht : (compilationRestoration sourceDecl auxiliaries).expr
        (E.lowered.generatedInstance.recursor owner).type with
    | none => simp [ht] at hv
    | some t => exact ⟨t, ht⟩
  obtain ⟨rules, hrulesEq⟩ := E.lowered.generatedInstance.restoredEquations_isSome _
    hrecTypes (fun owner => E.recursorName_not_head Haux Hexpansion hnodup owner)
  have hequations : E.lowered.generatedInstance.restoredEquations
      (compilationRestoration sourceDecl auxiliaries) = some (rules ++ []) := by
    rw [List.append_nil]; exact hrulesEq
  obtain ⟨Hcert, ⟨Hdata⟩⟩ := E.compilationData_of_tables wf Hsources C hC rules []
    hadded henvTypes Haux Hexpansion hparamsSize D Hrestoring HauxRestoring hequations
  have htypesEq : C.install.venvTypes = envTypes := by
    have h := C.install.abstract_types
    rw [C.typeValues, hadded] at h
    exact (Option.some.inj h).symm
  have hctorsAdded : envTypes.addConstVals sourceDecl.constructorConstants =
      some C.install.venvCtors := by
    have h := C.install.abstract_ctors
    rwa [C.constructorValues, htypesEq] at h
  have hsourceCtorNames := C.sourceConstructorNames
  rw [hC] at hsourceCtorNames
  have hfresh := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hfreshCtors := E.restorableNames_fresh_ctors hadded Haux Hexpansion hnodup
    hsourceCtorNames hctorsAdded
  have hle : C.install.venvCtors ≤ C.recursorVEnv :=
    VEnv.addProjections_le.trans C.install.recursorsAdded.le
  have hcoreEnvs : E.sourceCore.envCtors = C.install.venvCtors := by
    have Hcore := E.sourceCore.core
    rw [E.sourceCoreDecl_eq] at Hcore
    have hT : E.sourceCore.envTypes = envTypes :=
      Option.some.inj (Hcore.typesAdded.symm.trans hadded)
    have hc := Hcore.ctorsAdded
    rw [hT] at hc
    exact Option.some.inj (hc.symm.trans hctorsAdded)
  have hfreshFinal := E.recursorVEnv_restorableNames_fresh_of_not_renamed wf Hsources C hC
    hkernel D
  have hfreshF : ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      n ∉ ((compilationRestoration sourceDecl auxiliaries).recursors.map Prod.snd).filter
        (· ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames) →
      C.recursorVEnv.constants n = none := by
    intro n hn hnot
    exact hfreshFinal n hn (fun hm => hnot (List.mem_filter.mpr ⟨hm, by simpa using hn⟩))
  intro rv hrv
  obtain ⟨owner, s, t, Hs, rfl⟩ := E.rval_step C.sourceNonempty hrv
  obtain ⟨htype, hnp, hni, hnm, hnmin⟩ := E.restoredRecursorShapeFields C hC wf Hsources hadded
    Haux Hexpansion hnodup hparamsSize D hscoped owner Hs
  obtain ⟨head, hhead, hheadName, -, hargs, happ, Hctor⟩ :=
    Hdata.restoredFamilyHead_spec hadded hctorsAdded hfresh hfreshCtors owner
  have hmajor : Hs.restored.newInfo.getMajorInduct = head.name := by
    rw [E.restoredMajorInduct wf Hsources Haux Hexpansion hnodup hparamsSize D hscoped
      owner Hs, hheadName]
  have hinstalled : C.recursorVEnv.constants Hs.restored.newInfo.name ≠ none := by
    obtain ⟨_, _, h⟩ := htype; rw [h]; simp
  have Hrc := E.restoredRuleCtorFields D hctorNames Hdata.recursorNames
    Hdata.heads_not_recursors hfreshF
    (fun a ha hm => E.auxRecName_not_renamed wf Hsources D a ha (List.mem_filter.mp hm).1)
    owner Hs hinstalled head Hctor
  have hrules : ∀ rule ∈ Hs.restored.newInfo.rules,
      (∃ cval, outEnv.constants.find? rule.ctor = some (.ctorInfo cval) ∧
        cval.numParams = head.arguments.length) ∧
      Nonempty (VConstructorShape C.recursorVEnv rule.ctor head.levels.length
        head.arguments.length rule.nfields Hs.restored.newInfo.numIndices
        Hs.restored.newInfo.getMajorInduct) := by
    intro rule hrule
    obtain ⟨index, hindexMem, hct, hnf⟩ := Lean4Lean.List.Forall₂.forall_exists_r Hrc rule hrule
    have hown : E.lowered.signature.constructors[index].owner = owner := by
      simp only [InductiveSignature.ownedConstructors, List.mem_filter] at hindexMem
      exact eq_of_beq hindexMem.2
    obtain ⟨⟨cval, hcval, hcnp⟩, ⟨ci, hci, hshape⟩, -⟩ :=
      E.restoredRuleConstructors wf Hsources D Hcert Hdata (E.constructorArityPrefix C hC) Haux
        Hexpansion Hkernel owner hhead index hown
    refine ⟨⟨cval, hct ▸ hcval, hcnp⟩, ?_⟩
    obtain ⟨head', hhead', fields, ⟨S⟩⟩ := Hdata.restoredConstructorShape Hcert hadded
      hctorsAdded hfresh hfreshCtors hle index owner hown
    have hh : head' = head := Option.some.inj (hhead'.symm.trans hhead)
    subst hh
    rw [hcoreEnvs] at hci
    have hci' := hle.constants hci
    rw [S.const] at hci'
    have hty : ci.type = S.type := by
      cases Option.some.inj hci'; rfl
    have hpi := hshape.1
    rw [hty, S.type_eq, VExpr.piArity_wrapForalls_mkApps_const, S.doms_length] at hpi
    have hfields : fields = rule.nfields := by rw [hnf]; omega
    subst hfields
    rw [hct, hni, hmajor]
    exact ⟨S⟩
  refine ⟨⟨head.arguments.length, head.levels, head.arguments,
    restoredRecursorVShape htype hnp hni hnm hnmin head hmajor hargs happ, ?_⟩, ?_⟩
  · intro rule hrule
    obtain ⟨⟨cval, hcval, hcnp⟩, hS⟩ := hrules rule hrule
    refine ⟨head.levels.length, rfl, hS, fun cval' h => ?_⟩
    rw [hcval] at h
    cases h; exact hcnp
  · intro rule hrule
    obtain ⟨⟨cval, hcval, -⟩, -⟩ := hrules rule hrule
    exact ⟨cval, hcval⟩

end VerifyInductive
end Lean4Lean
