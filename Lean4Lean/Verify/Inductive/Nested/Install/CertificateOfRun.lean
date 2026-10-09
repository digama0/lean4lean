import Lean4Lean.Verify.Inductive.Nested.Restoration.RecursorAlignment
import Lean4Lean.Verify.Inductive.Nested.Restoration.Equations.RestoredRulesBase
import Lean4Lean.Verify.Inductive.Nested.Restoration.AuxiliaryProjections

/-! # The rule hypothesis and the restored block certificate of a validated nested run

* `NestedRun.hrules_of`: the rule hypothesis `Hrules` of
  `assemblyOfRun_of_run` from the rule-shape hypothesis `HruleShape` alone;
  freshness is derived for the restorable names that are not renamed
  auxiliary recursor names `Main.rec_k` (a renamed name may coincide with an
  auxiliary constructor name, see `Nested/Restoration/RecursorRenaming.lean`).
* `NestedRun.assemblyOfRun_of_run`: the restored block
  certificate from `Hrules` and the recursor alignment hypothesis `Hprovenance`
  (`recursorsAligned_of`), using the input-side avoidance of the renamed names by
  the lowered rules (`loweredRulesAvoid_renamed`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-- **The rule hypothesis `Hrules` of `assemblyOfRun_of_run`**, from the
rule-translation hypothesis `HruleShape`: some restored block derivation of the
run has rule lists translating the executable restored rules in its recursor
environment. The freshness conjunct (restorable names other than
the renamed recursor names) is derived for that shape. -/
theorem NestedRun.hrules_of
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (HruleShape : ∀ auxiliaries : List ContainerSpecialization,
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∃ C : RestoredBlockDerivation E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.lowered = E.lowered ∧
        List.Forall₂
          (E.TrRestoredRecursorRule (compilationRestoration sourceDecl auxiliaries)
            C.recursorVEnv)
          (List.finRange E.lowered.signature.constructors.size)
          (C.sourceRules ++ C.auxiliaryRules)) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∃ C : RestoredBlockDerivation E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.lowered = E.lowered ∧
        (∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
          n ∉ (compilationRestoration sourceDecl auxiliaries).recursors.map Prod.snd →
          C.recursorVEnv.constants n = none) ∧
        List.Forall₂
          (E.TrRestoredRecursorRule (compilationRestoration sourceDecl auxiliaries)
            C.recursorVEnv)
          (List.finRange E.lowered.signature.constructors.size)
          (C.sourceRules ++ C.auxiliaryRules) :=
  E.hrules_of_modulo wf Hsources HruleShape

/-- **Restored block certificate of a validated nested run**, modulo the rule
hypothesis `Hrules` (discharged by `hrules_of` from the rule-shape hypothesis)
and the recursor alignment hypothesis `Hprovenance` (discharged by
`recursorsAligned_of`).  Freshness of the restorable names in the derivation's
recursor environment is only
asked outside the renamed auxiliary recursor names `Main.rec_k`, which is
what holds without any naming hypothesis
(`recursorVEnv_restorableNames_fresh_of_not_renamed`); the input-side
avoidance of the renamed names by the lowered rules is
`loweredRulesAvoid_renamed`. -/
theorem NestedRun.assemblyOfRun_of_run
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (Hrules : ∀ auxiliaries : List ContainerSpecialization,
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∃ C : RestoredBlockDerivation E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.lowered = E.lowered ∧
        (∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
          n ∉ (compilationRestoration sourceDecl auxiliaries).recursors.map Prod.snd →
          C.recursorVEnv.constants n = none) ∧
        List.Forall₂
          (E.TrRestoredRecursorRule (compilationRestoration sourceDecl auxiliaries)
            C.recursorVEnv)
          (List.finRange E.lowered.signature.constructors.size)
          (C.sourceRules ++ C.auxiliaryRules))
    (Hprovenance : ∀ auxiliaries : List ContainerSpecialization,
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
          (C.recursorVEnv.addDefEqRules (C.sourceRules ++ C.auxiliaryRules))) :
    Nonempty { C : RestoredBlockCertificate E.restoration
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
        nparams isUnsafe (if isUnsafe then .unsafe else .safe) //
      C.lowered = E.lowered } := by
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, auxiliaries, hadded, henvTypes, Haux, Hexpansion,
      hparamsSize, D, Hrestoring, HauxRestoring⟩
  obtain ⟨C, hC, hfreshFinal, HCrules⟩ := Hrules auxiliaries D
  have Hprov := Hprovenance auxiliaries D C hC hfreshFinal HCrules
  have hnodup :
      (familyNames E.lowered.loweredDecl.types ++
        E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  obtain ⟨-, -, -, -, -, -, -, hscoped, -, hctorNames, -, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D True.intro
  -- the restored equations, modulo the renamed recursor names
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
  -- the constructor environment of the derivation
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
  have hnames : sourceTypes.map (·.name) = sourceDecl.types.map (·.name) := by
    have Hcore := E.sourceCore.core
    rw [E.sourceCoreDecl_eq] at Hcore
    exact (forall₂_trInductiveType_names Hcore.types).symm
  have hinfos := E.restoredRecursorEntryInfos C hC wf Hsources hadded Haux Hexpansion hnodup
    hparamsSize D hscoped hwf
  have Hentries : List.Forall₂
      (TrRestoredRecursorEntry E.lowered.generatedInstance
        (compilationRestoration sourceDecl auxiliaries)
        (sourceDecl.types.map (·.name)) C.recursorVEnv)
      (List.finRange E.lowered.signature.families.size)
      C.recursorEntries := by
    refine forall₂_imp_mem_right hinfos ?_
    rintro owner entry hentry ⟨s, t, Hstep, hentry1, hrec, Hw⟩
    refine ⟨Hstep.restored.newInfo, hentry1, hrec, ?_⟩
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
  exact ⟨⟨{ toRestoredBlockDerivation := C
            trCompilation := ⟨⟨_, _, _, _, Hdata, Hcertified, Hentries⟩⟩
            recursorsAligned := Hprov }, hC⟩⟩

end VerifyInductive
end Lean4Lean

/-! # The restored block certificate of a validated nested run

* `NestedRun.assemblyOfRun_of_restoredWF`: the restored block
  certificate of a nested run, modulo only the well-formedness `HrestoredWF`
  of the restored generated equations in the recursor environment of a
  restored block base. It composes `hruleShape_of_base`, `hrules_of`,
  `recursorsAligned_of` and `assemblyOfRun_of_run`.
* `NestedRun.assemblyOfRun`: the same certificate with no
  hypothesis beyond the run being nested, from `hrestoredWF_of`; this is used
  by `Nested/Install/Result.lean`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-- The restored block certificate of a nested validated run, from the
well-formedness `HrestoredWF` of the restored generated equations (the
hypothesis of `hruleShape_of_base`, verbatim). -/
theorem NestedRun.assemblyOfRun_of_restoredWF
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (hnested : result.aux2nested.size ≠ 0)
    (HrestoredWF : ∀ auxiliaries : List ContainerSpecialization,
      RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ B : RestoredBlockBase E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        B.lowered = E.lowered →
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) B.recursorVEnv →
        ∀ (k : Fin E.lowered.recursors.generationSignature.constructors.size)
          (rule : VDefEq),
          (compilationRestoration sourceDecl auxiliaries).equation
              (E.lowered.recursors.canonicalGeneration.equation k) =
            some rule →
          rule.WF B.recursorVEnv) :
    Nonempty { C : RestoredBlockCertificate E.restoration
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
        nparams isUnsafe (if isUnsafe then .unsafe else .safe) //
      C.lowered = E.lowered } :=
  E.assemblyOfRun_of_run wf Hsources
    (E.hrules_of wf Hsources (E.hruleShape_of_base wf Hsources hnested HrestoredWF))
    (E.recursorsAligned_of wf Hsources hnested)

/-- The restored equations and the concrete recursor alignment are selected
from this complete successful run. This theorem does not accept arbitrary
rule batches or a caller-supplied compilation callback. The
restored-equation well-formedness `HrestoredWF` of
`assemblyOfRun_of_restoredWF` is `NestedRun.hrestoredWF_of`
(`Nested/Restoration/AuxiliaryProjections.lean`). -/
theorem NestedRun.assemblyOfRun
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (hnested : result.aux2nested.size ≠ 0) :
    Nonempty { C : RestoredBlockCertificate E.restoration
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
        nparams isUnsafe (if isUnsafe then .unsafe else .safe) //
      C.lowered = E.lowered } :=
  E.assemblyOfRun_of_restoredWF wf Hsources hnested (E.hrestoredWF_of wf Hsources)

end VerifyInductive

end Lean4Lean
