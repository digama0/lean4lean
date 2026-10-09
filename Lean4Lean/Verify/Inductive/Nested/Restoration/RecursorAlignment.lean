import Lean4Lean.Verify.Inductive.Nested.Restoration.LoweredRuleAvoidance
import Lean4Lean.Theory.Typing.IotaSoundnessLemmas
import Lean4Lean.Verify.Inductive.Nested.Restoration.HeaderRenaming

/-! Recursor alignment of a validated nested run: every recursor of the output is
aligned with its abstract translation (`NewRecursorsAligned`).

`NestedRun.recursorsAligned_of` discharges the `Hprovenance`
hypothesis of `NestedRun.assemblyOfRun_of_run`.

The hypothesis quantifies over an arbitrary specialization list carrying
`RestorationTablesAgree`. The restoration `compilationRestoration decl auxiliaries`
is determined by the table data (`RestorationTablesAgree.expr_eq`,
`Nested/Restoration/HeaderRenaming.lean`), so the specialization list of
`restorationTablesRestoringAll`, for which all the formation facts are
available, may be used instead. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

open private Lean.Kernel.Environment.add from Lean.Environment


end VerifyInductive

/-! ### Shapes of restored recursors and their rules -/

namespace InductiveSignature


/-- The recursor shape of a restored recursor at the specialization head of
its translation (`TrRestoredRecursorVal`). -/
theorem TrRestoredRecursorVal.shape_of_head {s : InductiveSignature} {g : Instance s}
    {r : Restoration} {sourceNames : List Name} {venv : VEnv}
    {owner : Fin s.families.size} {rec : Lean.RecursorVal}
    (H : TrRestoredRecursorVal g r sourceNames venv owner rec)
    (hconst : ∃ type, r.expr (g.recursorType owner) = some type ∧
      venv.constants rec.name = some ⟨rec.levelParams.length, type⟩)
    {head : RestoredFamilyHead}
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
      head.name head.levels head.arguments) := by
  rcases hconst with ⟨type, htype, hconst⟩
  rcases r.expr_recursorType_eq_some htype with ⟨pre, major, hpre, hm, rfl⟩
  have hprelen : pre.length = s.params.length + s.families.size +
      s.constructors.size + s.families[owner].indices.length := by
    rw [← g.recursorPrefix_length owner]
    exact (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hpre)).symm
  have hmaj : major = VExpr.mkApps (.const head.name head.levels)
      (head.arguments.map (fun arg => arg.liftN
        (s.families.size + s.constructors.size + s.families[owner].indices.length)) ++
        vars s.families[owner].indices.length 0) :=
    Option.some.inj (hm.symm.trans happ)
  refine ⟨{
    ctorParams_length := rfl
    ctorParams_closed := by rw [H.numParams]; exact hargs
    type := _
    const := hconst
    doms := pre ++ [major]
    result := g.recursorBody owner
    type_eq := rfl
    doms_length := by
      simp [hprelen, H.numParams, H.numMotives, H.numMinors, H.numIndices]
    major_eq := ?_ }⟩
  rw [H.numParams, H.numMotives, H.numMinors, H.numIndices, ← hprelen,
    List.getElem?_concat_length, hmaj, vars_eq_bvarRange, Nat.add_zero]




end InductiveSignature

/-! ### Constructor shapes of certified containers -/



namespace InductiveSignature


end InductiveSignature

namespace VerifyInductive

open private Lean.Kernel.Environment.add from Lean.Environment

private theorem Restoration.recursor_name {r : Restoration} {v w : VConstVal}
    (h : r.recursor v = some w) : w.name = r.recursorName v.name := by
  simp only [Restoration.recursor, Option.bind_eq_bind, Option.pure_def] at h
  cases ht : r.expr v.type with
  | none => simp [ht] at h
  | some type =>
    simp only [ht, Option.bind_some, Option.some.injEq] at h
    rw [← h]

/-- **The major inductive of a restored recursor is an inductive type of the
output environment**: a restored source family header, or the container
family of the nested occurrence recorded by lowering. -/
theorem NestedRun.restoredMajorFound
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
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
      E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (owner : Fin E.lowered.signature.families.size)
    {s t : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name))
      (E.lowered.generatedInstance.recursorName owner) s t) :
    ∃ info, outEnv.constants.find? Hstep.restored.newInfo.getMajorInduct =
      some (.inductInfo info) := by
  let r := compilationRestoration sourceDecl auxiliaries
  have hheads : r.heads.map (·.auxiliary) = E.auxHeads := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have hfamNodup : (familyNames (E.lowered.loweredDecl.types.take sourceDecl.types.length) ++
      familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length)).Nodup := by
    have h := (List.nodup_append.mp hnodup).1
    rw [← List.take_append_drop sourceDecl.types.length E.lowered.loweredDecl.types] at h
    simpa only [familyNames, List.flatMap_append] using h
  have hfamRec : ∀ hi, (E.lowered.loweredDecl.types[owner.val]'hi).name ∉
      r.recursors.map Prod.fst := by
    intro hi hmem
    rw [compilationRestoration_recursors_fst] at hmem
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp hmem
    have haux : a.auxiliary ∈
        (E.lowered.loweredDecl.types.drop sourceDecl.types.length).map (·.name) := by
      rw [← auxiliarySpecializations_names Haux Hexpansion]
      exact List.mem_map_of_mem ha
    obtain ⟨t, ht, hta⟩ := List.mem_map.mp haux
    have h1 : (E.lowered.loweredDecl.types[owner.val]'hi).name ∈
        familyNames E.lowered.loweredDecl.types :=
      mem_familyNames_of_type (List.getElem_mem hi)
    have h2 : (E.lowered.loweredDecl.types[owner.val]'hi).name ∈
        E.lowered.loweredDecl.types.map (fun t => t.name.str "rec") := by
      rw [← heq, ← hta]
      exact List.mem_map_of_mem (f := fun t : VInductiveType => t.name.str "rec")
        (List.mem_of_mem_drop ht)
    exact (List.nodup_append.mp hnodup).2.2 _ h1 _ h2 rfl
  have hfamKey : ∀ hi, (E.lowered.loweredDecl.types[owner.val]'hi).name ∈
      r.heads.map (·.auxiliary) →
      ∃ nested, result.aux2nested.find?
        (E.lowered.loweredDecl.types[owner.val]'hi).name = some nested := by
    intro hi hmem
    rw [hheads] at hmem
    by_cases hlt : owner.val < sourceDecl.types.length
    · exfalso
      have htake : E.lowered.loweredDecl.types[owner.val]'hi ∈
          E.lowered.loweredDecl.types.take sourceDecl.types.length :=
        List.mem_iff_getElem.mpr ⟨owner.val, by simp; omega, by simp⟩
      exact (List.nodup_append.mp hfamNodup).2.2 _ (mem_familyNames_of_type htake) _ hmem rfl
    · have hdrop : E.lowered.loweredDecl.types[owner.val]'hi ∈
          E.lowered.loweredDecl.types.drop sourceDecl.types.length :=
        List.mem_iff_getElem.mpr ⟨owner.val - sourceDecl.types.length, by simp; omega, by
          simp only [List.getElem_drop]; congr 1; omega⟩
      have hname := List.mem_map_of_mem (f := (·.name)) hdrop
      rw [← auxiliarySpecializations_names Haux Hexpansion] at hname
      obtain ⟨a, ha, haeq⟩ := List.mem_map.mp hname
      obtain ⟨nested, hnested⟩ := D.familyLookup a ha
      exact ⟨nested, haeq ▸ hnested⟩
  have hnestedHead : ∀ name nested, result.aux2nested.find? name = some nested →
      ∃ c ls, nested.getAppFn = .const c ls := by
    intro name nested h
    obtain ⟨I, ls, -, h1, -⟩ := E.auxNestedHead wf Hsources h
    exact ⟨I, ls, h1⟩
  obtain ⟨hi', domain, c, ls, Hbinder, hc, hdisj⟩ := E.restoredMajorHead wf Hsources
    (D.agreement VEnv.empty lparams) hheads hparamsSize D.paramsFVars hnestedHead owner Hstep
    hfamRec hfamKey
  have hmi : Hstep.restored.newInfo.getMajorInduct = c := by
    rw [RecursorVal.getMajorInduct_of_binderAt _ Hbinder, hc]
    rfl
  have hwf : sourceProdEnv.constants.WF := (wf.tr (safety := .safe)).map_wf
  obtain ⟨entries, Htrace, -, hheaders⟩ := E.restoration.freshExtensionRecursorSteps hwf
  have houtWF : outEnv.constants.WF := Htrace.targetWF hwf
  rw [hmi]
  rcases hdisj with ⟨hnot, hceq⟩ | ⟨nested, ls', hfindN, hfn⟩
  · have hsourceLength : sourceTypes.length = sourceDecl.types.length := by
      have Hcore := E.sourceCore.core
      rw [E.sourceCoreDecl_eq] at Hcore
      exact Lean4Lean.List.Forall₂.length_eq Hcore.types
    have hlt : owner.val < sourceDecl.types.length := by
      by_contra hge
      apply hnot
      rw [compilationRestoration_heads_auxiliary,
        auxiliarySpecializations_headNames Haux Hexpansion]
      apply mem_familyNames_of_type
      exact List.mem_iff_getElem.mpr ⟨owner.val - sourceDecl.types.length, by simp; omega, by
        simp only [List.getElem_drop]; congr 1; omega⟩
    have hmemNames : (E.lowered.loweredDecl.types[owner.val]'hi').name ∈
        sourceTypes.map (·.name) := by
      rw [E.sourceNames_eq]
      exact List.mem_map_of_mem
        (List.mem_iff_getElem.mpr ⟨owner.val, by simp; omega, by simp⟩)
    obtain ⟨t0, ht0, ht0name⟩ := List.mem_map.mp hmemNames
    obtain ⟨s1, t1, Hind, hmemH⟩ := hheaders t0 ht0
    have hfindH := Htrace.findEntry hwf hmemH
    have hhname : (ConstantInfo.inductInfo Hind.restored.header.newInfo).name = t0.name := by
      change Hind.restored.header.newInfo.name = t0.name
      rw [Hind.restored.header.restored]
      exact (E.loweredSourceKeyed ht0 Hind.lookup : Hind.oldInfo.name = t0.name)
    rw [hhname, Kernel.Environment.find?_eq_constants houtWF] at hfindH
    rw [hceq, ← ht0name]
    exact ⟨_, hfindH⟩
  · obtain ⟨I0, ls0, info0, hfn0, hfind0⟩ := E.auxNestedHead wf Hsources hfindN
    rw [hfn] at hfn0
    simp only [Expr.const.injEq] at hfn0
    rw [hfn0.1]
    rw [Kernel.Environment.find?_eq_constants hwf] at hfind0
    exact ⟨_, Htrace.preservesSourceMapFind hwf hfind0⟩

/-- **Recursor alignment of a validated nested run**: the `Hprovenance`
hypothesis of `NestedRun.assemblyOfRun_of_run`, given that
lowering recorded a nested occurrence (`hnested`, the condition under which
the run restores at all; it makes the expanded block mutual, so no restored
recursor is K-like). The freshness premise (restorable names outside the
renamed recursor names) is not needed: it holds for every
`RestoredBlockDerivation` (`recursorVEnv_restorableNames_fresh_of_not_renamed`). -/
theorem NestedRun.recursorsAligned_of
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (hnested : result.aux2nested.size ≠ 0) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ C : RestoredBlockDerivation E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.lowered = E.lowered →
        (∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
          n ∉ (compilationRestoration sourceDecl auxiliaries).recursors.map Prod.snd →
          C.recursorVEnv.constants n = none) →
        List.Forall₂
          (E.TrRestoredRecursorRule (compilationRestoration sourceDecl auxiliaries)
            C.recursorVEnv)
          (List.finRange E.lowered.signature.constructors.size)
          (C.sourceRules ++ C.auxiliaryRules) →
        NewRecursorsAligned .unsafe sourceProdEnv.constants
          (ves.venv (if isUnsafe then .unsafe else .safe)) outEnv.constants
          (C.recursorVEnv.addDefEqRules (C.sourceRules ++ C.auxiliaryRules)) := by
  intro aux₁ D₁ C hC _ HCrules₁
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, auxiliaries, hadded, henvTypes, Haux, Hexpansion,
      hparamsSize, D, Hrestoring, HauxRestoring⟩
  -- transfer the hypotheses to the specialization list of the tables
  have hexpr : ∀ e, (compilationRestoration sourceDecl auxiliaries).expr e =
      (compilationRestoration sourceDecl aux₁).expr e := D.expr_eq D₁
  have hfreshFinal := E.recursorVEnv_restorableNames_fresh_of_not_renamed wf Hsources C hC D
  have HCrules : List.Forall₂
      (E.TrRestoredRecursorRule (compilationRestoration sourceDecl auxiliaries)
        C.recursorVEnv)
      (List.finRange E.lowered.signature.constructors.size)
      (C.sourceRules ++ C.auxiliaryRules) := by
    refine Lean4Lean.List.Forall₂.imp (fun k rule h => ?_) HCrules₁
    obtain ⟨owner, j, s, t, Hstep, hj, hk, hu, ht, hl, hty⟩ := h
    exact ⟨owner, j, s, t, Hstep, hj, hk, hu, ht, (hexpr _).trans hl, (hexpr _).trans hty⟩
  -- the compilation data (as in `assemblyOfRun_of_run`)
  have hnodup :
      (familyNames E.lowered.loweredDecl.types ++
        E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  obtain ⟨-, -, -, -, -, -, -, hscoped, -, hctorNames, -, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D True.intro
  have hheads : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      E.auxHeads := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have HL := E.loweredRulesAvoid_renamed wf Hsources Haux Hexpansion D
  rw [← hheads] at HL
  have hequations := E.restoredEquations_of_trModulo wf Hsources hheads hparamsSize
    D hscoped HL
    (TrRestoredRulesModulo.filter_restorable ⟨C.recursorVEnv, hfreshFinal, HCrules⟩)
  obtain ⟨Hcertified, ⟨Hdata⟩⟩ := E.compilationData_of_tables wf Hsources C hC hadded
    henvTypes Haux Hexpansion hparamsSize D Hrestoring HauxRestoring hequations
  have hwf : sourceProdEnv.constants.WF := (wf.tr (safety := .safe)).map_wf
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
  have hrecAdded := C.install.recursorsAdded.abstract
  have hle : (C.install.venvCtors.addEliminators C.install.eliminators).addProjections sourceDecl.projectionEntries ≤
      C.recursorVEnv := VEnv.addConstVals_le hrecAdded
  have hleCtors : C.install.venvCtors ≤ C.recursorVEnv := VEnv.addEliminators_addProjections_le.trans hle
  have hnames : sourceTypes.map (·.name) = sourceDecl.types.map (·.name) := by
    have Hcore := E.sourceCore.core
    rw [E.sourceCoreDecl_eq] at Hcore
    exact (forall₂_trInductiveType_names Hcore.types).symm
  have hinfos := E.restoredRecursorEntryInfos C hC wf Hsources hadded Haux Hexpansion hnodup
    hparamsSize D hscoped hwf
  -- the translation of the restored recursor of an entry
  have Hreal : ∀ (owner : Fin E.lowered.signature.families.size)
      (entry : ConstantInfo × VConstVal), entry ∈ C.recursorEntries →
      ∀ (s t : Environment) (Hstep : RestoredRecursorStep result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
        (sourceTypes.map (·.name))
        (E.lowered.generatedInstance.recursorName owner) s t),
      (compilationRestoration sourceDecl auxiliaries).recursor
        (E.lowered.generatedInstance.recursor owner) = some entry.2 →
      RecursorRestorationStepValue
        ((C.install.venvCtors.addEliminators C.install.eliminators).addProjections sourceDecl.projectionEntries) Hstep entry.2 →
      TrRestoredRecursorVal E.lowered.generatedInstance
        (compilationRestoration sourceDecl auxiliaries)
        (sourceDecl.types.map (·.name)) C.recursorVEnv owner Hstep.restored.newInfo := by
    intro owner entry hentry s t Hstep hrec Hw
    obtain ⟨head, hhead, hheadName, hlevels, hargs, happ, Hctor⟩ :=
      Hdata.restoredFamilyHead_spec hadded hctorsAdded hfresh hfreshCtors owner
    have hinstalled : C.recursorVEnv.constants Hstep.restored.newInfo.name ≠ none := by
      have hget := VEnv.addConstVals_get hrecAdded (List.mem_map_of_mem hentry)
      have hname : entry.2.name = Hstep.restored.newInfo.name :=
        Hw.1.trans Hstep.restored.restoration.name.symm
      rw [← hname, hget]
      simp
    have Hrules' := E.trRestoredRules D hctorNames Hdata.recursorNames
      Hdata.heads_not_recursors hfreshFinal (E.auxRecName_not_renamed wf Hsources D)
      Hdata.equations HCrules owner Hstep hinstalled head Hctor
    refine E.trRestoredRecursorVal_of_step D hnames owner Hstep hle hrec Hw
      ⟨head, hhead, ?_, hlevels, hargs, happ, Hrules'⟩
    rw [E.restoredMajorInduct wf Hsources Haux Hexpansion hnodup hparamsSize D hscoped
      owner Hstep, hheadName]
  -- the source environment and the recursor environment
  have Hvalid : CheckingEnv.Valid (if isUnsafe then .unsafe else .safe) sourceProdEnv
      (ves.venv (if isUnsafe then .unsafe else .safe)) :=
    wf.toCheckingValid (if isUnsafe then .unsafe else .safe)
  have hheadsSrc := Hvalid.recursors.heads
  have hsrcWF : sourceProdEnv.constants.WF := Hvalid.tr.map_wf
  have hfinalWF : C.recursorVEnv.WF := (C.install.validCore Hvalid.toValidCore).tr.wf
  have hrulesWF : ∀ df ∈ C.sourceRules ++ C.auxiliaryRules, df.WF C.recursorVEnv := by
    intro df hdf
    rcases List.mem_append.mp hdf with hp | ha
    · exact C.sourceIota.rulesWF df hp
    · exact C.auxiliaryWF.rulesWF (by simp) df ha
  obtain ⟨entries, Htrace, hsteps, -⟩ := E.restoration.freshExtensionRecursorSteps hsrcWF
  have houtWF : outEnv.constants.WF := Htrace.targetWF hsrcWF
  -- every inductive type of the output environment is rigid in the recursor environment
  have hrigid : ∀ n info, outEnv.constants.find? n = some (.inductInfo info) →
      C.recursorVEnv.Rigid n := by
    intro n info h
    have h' : outEnv.find? n = some (.inductInfo info) := by
      rw [Kernel.Environment.find?_eq_constants houtWF]; exact h
    have hsrc : (ves.venv (if isUnsafe then .unsafe else .safe)).Rigid n := by
      rcases Htrace.entryOrigin hsrcWF h' with hold | ⟨entry, hentry, hname, -⟩
      · rw [Kernel.Environment.find?_eq_constants hsrcWF] at hold
        exact hheadsSrc.rigid hold
      · have hnone := Htrace.sourceFresh hsrcWF hentry
        rw [← hname, Kernel.Environment.find?_eq_constants hsrcWF] at hnone
        exact hheadsSrc.rigid_of_fresh hnone
    intro df hdf ls
    exact hsrc df (C.install.defeqs df hdf) ls
  -- the equation list
  have Heqs := List.mapM_eq_some.mp Hdata.equations
  -- the alignment of one restored recursor
  have Hcore : ∀ (owner : Fin E.lowered.signature.families.size)
      (entry : ConstantInfo × VConstVal), entry ∈ C.recursorEntries →
      ∀ rec : Lean.RecursorVal,
      (compilationRestoration sourceDecl auxiliaries).recursor
        (E.lowered.generatedInstance.recursor owner) = some entry.2 →
      TrRestoredRecursorVal E.lowered.generatedInstance
        (compilationRestoration sourceDecl auxiliaries)
        (sourceDecl.types.map (·.name)) C.recursorVEnv owner rec →
      (∃ info, outEnv.constants.find? rec.getMajorInduct = some (.inductInfo info)) →
      RecursorAlignmentCore
        (C.recursorVEnv.addDefEqRules (C.sourceRules ++ C.auxiliaryRules)) rec := by
    intro owner entry hentry rec hrec R hmajorFound
    have hconst := restoredRecursor_constant hrec
      (VEnv.addConstVals_get hrecAdded (List.mem_map_of_mem hentry)) R.name R.uvars
    obtain ⟨head, hhead, hmajor, -, hargs, happ, hrules⟩ := R.specialization
    obtain ⟨hshape⟩ := R.shape_of_head hconst hargs happ
    have hrigidHead : C.recursorVEnv.Rigid head.name := by
      obtain ⟨info, hinfo⟩ := hmajorFound
      rw [hmajor] at hinfo
      exact hrigid _ info hinfo
    refine ⟨head.arguments.length, head.levels, head.arguments,
      ⟨by rw [hmajor]; exact hshape.mono VEnv.addDefEqRules_le⟩, ?_⟩
    intro rule hmem
    obtain ⟨index, hindex, RR⟩ := Lean4Lean.List.Forall₂.forall_exists_r hrules rule hmem
    have howner : E.lowered.signature.constructors[index].owner = owner := by
      simpa only [beq_iff_eq] using (List.mem_filter.mp hindex).2
    obtain ⟨df, heq, -, htr⟩ := RR.equation
    have hdfMem : df ∈ C.sourceRules ++ C.auxiliaryRules := by
      obtain ⟨d, hd, hdeq⟩ := Lean4Lean.List.Forall₂.forall_exists_l Heqs
        (E.lowered.generatedInstance.equation index)
        (List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩)
      rw [heq] at hdeq
      cases hdeq
      exact hd
    have hdef : (C.recursorVEnv.addDefEqRules (C.sourceRules ++ C.auxiliaryRules)).defeqs df :=
      VEnv.addDefEqRules_defeqs_iff.mpr (.inr hdfMem)
    have hindices := Hdata.model.constructorArity _
      (Array.getElem_mem_toList (xs := E.lowered.signature.constructors) index.isLt)
    have hnotHead : (compilationRestoration sourceDecl auxiliaries).heads.find?
        (fun h => h.auxiliary == E.lowered.generatedInstance.recursorName
          E.lowered.signature.constructors[index].owner) = none := by
      apply Restoration.heads_find?_eq_none
      intro hm
      obtain ⟨h, hh, he⟩ := List.mem_map.mp hm
      exact Hdata.heads_not_recursors _ h hh he
    have hrecType : ∃ type, (compilationRestoration sourceDecl auxiliaries).expr
        (E.lowered.generatedInstance.recursorType
          E.lowered.signature.constructors[index].owner) = some type ∧
        C.recursorVEnv.constants ((compilationRestoration sourceDecl auxiliaries).recursorName
          (E.lowered.generatedInstance.recursorName
            E.lowered.signature.constructors[index].owner)) =
          some ⟨E.lowered.generatedInstance.uvars, type⟩ := by
      subst howner; rw [← R.name, ← R.uvars]; exact hconst
    have Hrec : VRecursorShape C.recursorVEnv
        ((compilationRestoration sourceDecl auxiliaries).recursorName
          (E.lowered.generatedInstance.recursorName
            E.lowered.signature.constructors[index].owner))
        E.lowered.generatedInstance.uvars
        E.lowered.signature.params.length head.arguments.length
        E.lowered.signature.families.size
        E.lowered.signature.constructors.size
        E.lowered.signature.families[
          E.lowered.signature.constructors[index].owner].indices.length
        head.name head.levels head.arguments := by
      have h := hshape
      rw [R.name, R.uvars, R.numParams, R.numMotives, R.numMinors, R.numIndices] at h
      subst howner; exact h
    obtain ⟨_, -, Hadm⟩ := Hdata.admissible
    obtain ⟨head3, hhead3, RP, RF, hRP, hRF, Hfd⟩ :=
      Hdata.restoredConstructorFieldDomains Hcertified hadded hctorsAdded hfresh hfreshCtors
        hleCtors hfinalWF Hadm.levels_wf index owner howner
    have h33 : head3 = head := Option.some.inj (hhead3.symm.trans hhead)
    rw [h33, ← RR.ctor] at Hfd
    obtain ⟨I⟩ := Restoration.restored_iota_shape E.lowered.generatedInstance
      (compilationRestoration sourceDecl auxiliaries) index heq hdef hfinalWF
      VEnv.addDefEqRules_le (fun _ => by simp) hrecType
      hindices hnotHead RR.constructorApplication
      (fun h hh => (Hdata.restorationScoped.2.2.1 h hh).2) ⟨RP, RF, hRP, hRF, Hfd⟩
    obtain ⟨head2, hhead2, fields, ⟨hctorShape⟩⟩ := Hdata.restoredConstructorShape Hcertified
      hadded hctorsAdded hfresh hfreshCtors hleCtors index owner howner
    have hhh : head2 = head := Option.some.inj (hhead2.symm.trans hhead)
    subst hhh
    rw [← RR.ctor] at hctorShape
    subst howner
    have I' : VIotaRuleShape (C.recursorVEnv.addDefEqRules (C.sourceRules ++ C.auxiliaryRules))
        rec.name rec.levelParams.length rec.numParams head2.arguments.length rec.numMotives
        rec.numMinors rec.numIndices rule.ctor head2.levels rule.nfields df
        head2.arguments := by
      rw [R.name, R.uvars, R.numParams, R.numMotives, R.numMinors, R.numIndices, RR.nfields]
      exact I
    have hfields := VIotaRuleShape.fieldCount hfinalWF I' (hrulesWF df hdfMem) hshape
      hctorShape hrigidHead
    subst hfields
    refine ⟨df, { shape := ⟨I'⟩, rhs := htr.mono VEnv.addDefEqRules_le, ctor := ?_ }⟩
    refine ⟨head2.levels.length, rfl, ?_⟩
    rw [R.numIndices, hmajor]
    exact ⟨hctorShape.mono VEnv.addDefEqRules_le⟩
  refine { recursor := ?_, defeq := ?_ }
  · intro name rec hfind
    have hfind' : outEnv.find? name = some (.recInfo rec) := by
      rw [Kernel.Environment.find?_eq_constants houtWF]; exact hfind
    rcases Htrace.entryOrigin hsrcWF hfind' with hold | ⟨entry, hentry, hname, hfound⟩
    · left
      rwa [Kernel.Environment.find?_eq_constants hsrcWF] at hold
    right
    intro _
    obtain ⟨oldRecName, hold, s, t, Hstep, hreq⟩ := hsteps entry hentry rec hfound.symm
    subst hreq
    rw [← E.recursorNames_order C.sourceNonempty] at hold
    obtain ⟨owner, -, rfl⟩ := List.mem_map.mp hold
    obtain ⟨entry', hentry', s', t', Hstep', hentry1, hrec, Hw⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_l hinfos owner (List.mem_finRange owner)
    have hnew : Hstep'.restored.newInfo = Hstep.restored.newInfo := (Hstep'.info_eq Hstep).2
    have R := Hreal owner entry' hentry' s' t' Hstep' hrec Hw
    rw [hnew] at R
    have hmajorFound := E.restoredMajorFound wf Hsources Haux Hexpansion hnodup hparamsSize D
      owner Hstep
    refine ⟨Hcore owner entry' hentry' _ hrec R hmajorFound, ?_, hmajorFound⟩
    intro hk
    rw [R.k_eq_false (E.one_lt_familiesSize hnested)] at hk
    cases hk
  · intro df hdf
    rcases VEnv.addDefEqRules_defeqs_iff.mp hdf with hold | hnew
    · exact .inl (C.install.defeqs df hold)
    right
    obtain ⟨e, he, hedf⟩ := Lean4Lean.List.Forall₂.forall_exists_r Heqs df hnew
    obtain ⟨index, -, rfl⟩ := List.mem_map.mp he
    have hleft : (compilationRestoration sourceDecl auxiliaries).expr
        (E.lowered.generatedInstance.equation index).lhs = some df.lhs := by
      simp only [Restoration.equation, Option.bind_eq_bind, Option.pure_def] at hedf
      cases hl : (compilationRestoration sourceDecl auxiliaries).expr
          (E.lowered.generatedInstance.equation index).lhs with
      | none => simp [hl] at hedf
      | some lhs =>
        simp only [hl, Option.bind_some] at hedf
        cases hr : (compilationRestoration sourceDecl auxiliaries).expr
            (E.lowered.generatedInstance.equation index).rhs with
        | none => simp [hr] at hedf
        | some rhs =>
          simp only [hr, Option.bind_some] at hedf
          cases hty : (compilationRestoration sourceDecl auxiliaries).expr
              (E.lowered.generatedInstance.equation index).type with
          | none => simp [hty] at hedf
          | some ty =>
            simp only [hty, Option.bind_some, Option.some.injEq] at hedf
            rw [← hedf]
    have hhead := Restoration.wrapLams_head_const
      (Hdata.heads_not_recursors E.lowered.signature.constructors[index].owner)
      (VExpr.getAppFnArgs_mkApps_head _ _) hleft
    obtain ⟨entry, hentry, s, t, Hstep, hentry1, hrec, -⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_l hinfos
        E.lowered.signature.constructors[index].owner (List.mem_finRange _)
    have hfindE := C.find_recursorEntry hwf entry hentry
    rw [Restoration.recursor_name hrec, hentry1,
      Kernel.Environment.find?_eq_constants houtWF] at hfindE
    exact ⟨_, _, _, hhead, hfindE⟩

end VerifyInductive

end Lean4Lean
