import Lean4Lean.Verify.Inductive.Nested.Restoration.Base
import Lean4Lean.Verify.Inductive.Nested.Restoration.RunOfRestoration
import Lean4Lean.Verify.Inductive.Nested.Restoration.SideEnvironment.ConstructorEnvironment
import Lean4Lean.Verify.Inductive.Nested.Lowering.Expansion.Data
import Lean4Lean.Verify.Inductive.Nested.Restoration.KernelData

/-! # The rule-free restored block of a nested run

`NestedRun.assemblyBase` builds the `RestoredBlockBase` of a nested run. The restored
constants are replayed in dependency order (`RestorationInDependencyOrder`) and installed in
the abstract stages `BlockStages`. The restored recursor types are translated by the recursor-type
validation pass in the constructor side environment, a checker environment of the projection
stage (`ValidationEnvironment.validProjected`, `CheckerEnv.ofSideExtension`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-! ### The recursor-type validation pass, per recursor -/

/-- The recursor-type pass translates the restored type of a source recursor to a type. -/
theorem validateRestoredRecursorTypes.translation_of_run
    {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    (C : CheckerEnv safety env venv) {loweredEnv : Environment} {fuel : FuelConfig}
    {result : ElimNestedInductive.Result} {recNameMap : NameMap Name} {allIndNames : List Name}
    {types : List InductiveType} {auxRecNames : List Name} {indType : InductiveType}
    {oldInfo : RecursorVal}
    (hrun : Lean4Lean.validateRestoredRecursorTypes.run env loweredEnv
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (htype : indType ∈ types)
    (hlookup : loweredEnv.find? (Lean.mkRecName indType.name) =
      some (.recInfo oldInfo)) :
    let newRecName := recNameMap.getD (Lean.mkRecName indType.name)
      (Lean.mkRecName indType.name)
    let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
      (Lean.mkRecName indType.name) newRecName oldInfo
    ∃ target, TrExprS venv restored.levelParams [] restored.type target ∧
      venv.IsType restored.levelParams.length [] target := by
  have hcheck := validateRestoredRecursorTypes.run.WF C loweredEnv fuel result recNameMap
    allIndNames types auxRecNames hrun (Lean.mkRecName indType.name)
    (List.mem_append_left _ (List.mem_map.mpr ⟨indType, htype, rfl⟩))
  obtain ⟨recInfo, hfind, T, hT, hty⟩ := validateRestoredRecursorTypes.check.WF C loweredEnv
    fuel result recNameMap allIndNames _ hcheck
  cases ConstantInfo.recInfo.inj (Option.some.inj (hfind.symm.trans hlookup))
  exact ⟨T, hT, hty⟩

/-- The recursor-type pass translates the restored type of an auxiliary recursor to a type. -/
theorem validateRestoredRecursorTypes.auxiliaryTranslation_of_run
    {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    (C : CheckerEnv safety env venv) {loweredEnv : Environment} {fuel : FuelConfig}
    {result : ElimNestedInductive.Result} {recNameMap : NameMap Name} {allIndNames : List Name}
    {types : List InductiveType} {auxRecNames : List Name} {recName : Name}
    {oldInfo : RecursorVal}
    (hrun : Lean4Lean.validateRestoredRecursorTypes.run env loweredEnv
      safety fuel result recNameMap allIndNames types auxRecNames = .ok ())
    (hrec : recName ∈ auxRecNames)
    (hlookup : loweredEnv.find? recName = some (.recInfo oldInfo)) :
    let newRecName := recNameMap.getD recName recName
    let restored := result.restoreRecursor loweredEnv recNameMap allIndNames
      recName newRecName oldInfo
    ∃ target, TrExprS venv restored.levelParams [] restored.type target ∧
      venv.IsType restored.levelParams.length [] target := by
  have hcheck := validateRestoredRecursorTypes.run.WF C loweredEnv fuel result recNameMap
    allIndNames types auxRecNames hrun recName (List.mem_append_right _ hrec)
  obtain ⟨recInfo, hfind, T, hT, hty⟩ := validateRestoredRecursorTypes.check.WF C loweredEnv
    fuel result recNameMap allIndNames _ hcheck
  cases ConstantInfo.recInfo.inj (Option.some.inj (hfind.symm.trans hlookup))
  exact ⟨T, hT, hty⟩

/-- Telescope-translation form of the pointwise source recursor translation (the source
branch's `restoredSourceTelescopeAtFreshOfValidation`). -/
theorem NestedLoweringOutputClosed.restoredSourceTelescopeAtFreshOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envCtors : VEnv} {ctorEnv loweredEnv validationEnv : Environment}
    {result : ElimNestedInductive.Result} {sourceTypes : List InductiveType}
    {loweredSourceEnv : Environment} {fuel : Nat} {auxRecNames : List Name}
    {validationSafety : DefinitionSafety} {validationFuel : FuelConfig}
    {R : ConstructorCheck c stats loweredDecl nparams isUnsafe depth sourceVEnv
      result.types.toArray ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorInstallation R loweredEnv)
    (Hvalid : CheckerEnv validationSafety validationEnv envCtors)
    (Hrun : Lean4Lean.validateRestoredRecursorTypes.run validationEnv
      loweredEnv validationSafety validationFuel result
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) sourceTypes auxRecNames = .ok ())
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (hentry : familyIdx < Hprod.entries.length)
    {stepSource stepTarget : Environment}
    (Hstep : RestoredInductiveStep result loweredEnv
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) sourceTypes[familyIdx]
        stepSource stepTarget) :
    ∃ targetType, Expr.ForallTelescopeTypeTranslation envCtors
      Hstep.restored.recursor.oldInfo.levelParams []
      Hstep.restored.recursor.restored.newInfo.type
      (result.nparams + (Hprod.recInfos.map (·.motive)).size +
        (Hprod.recInfos.flatMap (·.minors)).size +
        Hprod.recInfos[familyIdx]!.indices.size + 1)
      targetType := by
  have holdRecName : Lean.mkRecName sourceTypes[familyIdx].name =
      Lean.mkRecName result.types.toArray[familyIdx]!.name := by
    rcases H.sourceResolvedMappingAtFreshAligned hempty hfamily with
      ⟨_fvars, _stepState, mappedTarget, _loweredState, _hparams, _hnodup,
        _hsize, Hmapping, hmappedTarget⟩
    obtain ⟨hresult, hmappedEq⟩ := _root_.getElem?_eq_some_iff.mp hmappedTarget
    have harray : result.types.toArray[familyIdx]! = mappedTarget := by
      simp [hresult, hmappedEq]
    rw [harray, Hmapping.name]
  rcases Hprod.restoredSourceTelescopeAlignment familyIdx hentry
      Hstep.restored.recursor holdRecName H.toResult.resultNParams H.resultParamsSize with
    ⟨Hrecursor⟩
  have Htel := Hrecursor.restoredForallTelescope
  rcases validateRestoredRecursorTypes.translation_of_run Hvalid Hrun
      (List.getElem_mem hfamily)
      Hstep.restored.recursor.lookup with ⟨targetType, Htr, Htype⟩
  rw [← Hstep.restored.recursor.restored.produced] at Htr Htype
  rw [Hstep.restored.recursor.restored.restoration.levelParams] at Htr Htype
  exact ⟨targetType, by
    simpa only [Nat.add_assoc] using
      Expr.ForallTelescopeTypeTranslation.ofTrExprS Htel Htr Htype⟩

/-- The recursor-type pass translates the auxiliary recursor of one restoration step. -/
theorem AuxiliaryRecursorGeneratedAlignment.recursorStepOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envCtors : VEnv} {indTypes : Array InductiveType}
    {ctorEnv loweredEnv validationEnv stepSource stepTarget : Environment}
    {result : ElimNestedInductive.Result} {auxRec : NameMap Name} {allIndNames : List Name}
    {oldRecName : Name} {validationFuel : FuelConfig} {validationTypes : List InductiveType}
    {auxRecNames : List Name}
    {R : ConstructorCheck c stats loweredDecl nparams isUnsafe depth sourceVEnv indTypes ctorEnv}
    {Hprod : RecursorInstallation R loweredEnv}
    {Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName stepSource stepTarget}
    (A : AuxiliaryRecursorGeneratedAlignment Hprod Hstep)
    (Hvalid : CheckerEnv c.safety validationEnv envCtors)
    (Hrun : Lean4Lean.validateRestoredRecursorTypes.run validationEnv
      loweredEnv c.safety validationFuel result auxRec
      allIndNames validationTypes auxRecNames = .ok ())
    (hrec : oldRecName ∈ auxRecNames) :
    Nonempty (AuxiliaryRecursorTranslation c.safety envCtors envCtors Hstep) := by
  rcases validateRestoredRecursorTypes.auxiliaryTranslation_of_run Hvalid Hrun
      hrec Hstep.lookup with ⟨targetType, Htranslation, Htype⟩
  rw [← Hstep.restored.produced] at Htranslation Htype
  have Hmetadata := Hprod.restoredSourceRecursorMetadata A.ownerIdx
    A.entry_lt Hstep A.oldRecName_eq
  have Hsafety : c.safety ≤
      (ConstantInfo.recInfo Hstep.restored.newInfo).safety := by
    simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
      ConstantInfo.isPartial, Hstep.restored.restoration.isUnsafe] using
        Hmetadata.1
  exact ⟨AuxiliaryRecursorTranslation.ofTypeTranslation targetType Hsafety
    Htranslation Htype⟩

/-- Fold the recursor-type validation over the auxiliary restoration fold (the source
branch's `AuxiliaryRecursorGeneratedAlignments.recursorTraceOfValidation`). -/
theorem AuxiliaryRecursorGeneratedAlignments.recursorTraceOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envCtors : VEnv} {indTypes : Array InductiveType}
    {ctorEnv loweredEnv validationEnv sourceProdEnv targetProdEnv : Environment}
    {result : ElimNestedInductive.Result} {auxRec : NameMap Name} {allIndNames : List Name}
    {names : List Name} {validationFuel : FuelConfig} {validationTypes : List InductiveType}
    {auxRecNames : List Name}
    {R : ConstructorCheck c stats loweredDecl nparams isUnsafe depth sourceVEnv indTypes ctorEnv}
    {Hprod : RecursorInstallation R loweredEnv}
    {Htrace : FoldSteps
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceProdEnv targetProdEnv}
    (H : AuxiliaryRecursorGeneratedAlignments Hprod Htrace)
    (Hvalid : CheckerEnv c.safety validationEnv envCtors)
    (Hrun : Lean4Lean.validateRestoredRecursorTypes.run validationEnv
      loweredEnv c.safety validationFuel result auxRec
      allIndNames validationTypes auxRecNames = .ok ())
    (Hnames : ∀ name ∈ names, name ∈ auxRecNames)
    (priorRecursors : List VConstVal) :
    ∃ finalRecursors, AuxiliaryRecursorTranslations c.safety envCtors
      envCtors Htrace priorRecursors finalRecursors := by
  induction H generalizing priorRecursors with
  | nil sourceEnv => exact ⟨priorRecursors, .nil sourceEnv priorRecursors⟩
  | @cons oldRecName stepSource middleEnv tail targetEnv Hstep Htail A Hrest ih =>
      rcases A.recursorStepOfValidation Hvalid Hrun
          (Hnames oldRecName (by simp)) with ⟨Hhead⟩
      have HtailNames : ∀ name ∈ tail, name ∈ auxRecNames := by
        intro name hname
        exact Hnames name (by simp [hname])
      rcases ih HtailNames (priorRecursors ++ [Hhead.recursor]) with
        ⟨finalRecursors, Hfinal⟩
      exact ⟨finalRecursors,
        AuxiliaryRecursorTranslations.cons Hstep Htail Hhead Hfinal⟩

/-- The abstract stages of a dependency-order replay: the headers and constructors are the
declaration's, and the recursors are added to the projection stage. -/
theorem RestorationInDependencyOrder.existsBlockStages
    {safety : DefinitionSafety} {sourceProdEnv outProdEnv : Environment}
    {sourceVEnv envTypes envCtors : VEnv} {owners : List VInductiveType}
    {primaryRecursors auxiliaryRecursors : List VConstVal}
    {primitiveEntries nondeltaEntries : List ConstantInfo}
    (projections : List VProjectionEntry)
    (H : RestorationInDependencyOrder safety sourceProdEnv outProdEnv
      sourceVEnv envTypes (envCtors.addProjections projections) owners
        primaryRecursors auxiliaryRecursors)
    (Hchecking : CheckingEnv safety sourceProdEnv sourceVEnv)
    (HprojectedWF : (envCtors.addProjections projections).WF)
    (Hprimitive : FreshNonprimitiveExtension false sourceProdEnv
      primitiveEntries outProdEnv)
    (Hnondelta : FreshExtension sourceProdEnv nondeltaEntries outProdEnv)
    (hnondelta : ∀ entry ∈ nondeltaEntries, entry.deltaValue? = none)
    (htypesAbstract : sourceVEnv.addConstVals
      (H.typeEntries.map Prod.snd) = some envTypes)
    (hconstructorsAbstract : envTypes.addConstVals
      (H.constructorEntries.map Prod.snd) = some envCtors) :
    ∃ recursorVEnv, ∃ S : BlockStages sourceVEnv H.typeEntries H.constructorEntries
      H.recursorEntries projections recursorVEnv,
      S.venvTypes = envTypes ∧ S.venvCtors = envCtors := by
  rcases H.existsCanonicalFresh Hchecking.map_wf with
    ⟨canonicalProdEnv, HcanonicalFresh, -⟩
  have HcanonicalFresh' : FreshExtension sourceProdEnv
      (H.typeEntries.map Prod.fst ++ (H.constructorEntries.map Prod.fst ++
        H.recursorEntries.map Prod.fst)) canonicalProdEnv := by
    simpa [List.map_append, List.append_assoc] using HcanonicalFresh
  rcases HcanonicalFresh'.split_append with
    ⟨prodTypes, HtypesFresh, HafterTypes⟩
  rcases HafterTypes.split_append with
    ⟨prodCtors, HconstructorsFresh, HrecursorsFresh⟩
  have hnonprimitive := H.canonicalNonprimitive Hprimitive Hchecking.map_wf
  have hnondeltaCanonical := H.canonicalNondelta Hnondelta
    Hchecking.map_wf hnondelta
  have HtypesAdded : AddConstants safety sourceProdEnv sourceVEnv
      H.typeEntries prodTypes envTypes := by
    apply AddConstants.ofFreshAbstract HtypesFresh
      (fun entry hentry => (H.types entry hentry).1)
      (fun entry hentry => (H.types entry hentry).2)
    · intro entry hentry
      exact hnonprimitive entry (by simp [hentry])
    · intro entry hentry
      exact hnondeltaCanonical entry (by simp [hentry])
    · exact htypesAbstract
    · exact VEnv.LE.rfl
  have HcheckingTypes : CheckingEnv safety prodTypes envTypes :=
    HtypesAdded.checking Hchecking
  have HconstructorsAdded : AddConstants safety prodTypes envTypes
      H.constructorEntries prodCtors envCtors := by
    apply AddConstants.ofFreshAbstract HconstructorsFresh
      (fun entry hentry => (H.constructors entry hentry).1)
      (fun entry hentry => (H.constructors entry hentry).2)
    · intro entry hentry
      exact hnonprimitive entry (by simp [hentry])
    · intro entry hentry
      exact hnondeltaCanonical entry (by simp [hentry])
    · exact hconstructorsAbstract
    · exact VEnv.LE.rfl
  have HcheckingProjected : CheckingEnv safety prodCtors
      (envCtors.addProjections projections) :=
    (HconstructorsAdded.checking HcheckingTypes).addProjections HprojectedWF
  rcases AddConstants.exists_ofFresh HrecursorsFresh
      (fun entry hentry => (H.recursors entry hentry).1)
      (fun entry hentry => (H.recursors entry hentry).2)
      (fun entry hentry => hnonprimitive entry (by simp [hentry]))
      (fun entry hentry => hnondeltaCanonical entry (by simp [hentry]))
      HcheckingProjected VEnv.LE.rfl with ⟨recursorVEnv, HrecursorsAdded⟩
  exact ⟨recursorVEnv, {
    venvTypes := envTypes
    venvCtors := envCtors
    abstract_types := htypesAbstract
    abstract_ctors := hconstructorsAbstract
    recursorsAdded := {
      abstract := HrecursorsAdded.abstract
      name_eq := fun entry hentry => (H.recursors entry hentry).1.2 } }, rfl, rfl⟩

/-! ### The restored block base -/

private theorem nodup_of_map_nodup {l : List α} (f : α → β) (H : (l.map f).Nodup) :
    l.Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons] at H ⊢
    exact ⟨fun ha => H.1 (List.mem_map_of_mem ha), ih H.2⟩

/-- A fresh extension between fixed endpoints has a unique payload up to order. -/
theorem FreshExtension.permOfSameTarget {source target : Environment}
    {leftEntries rightEntries : List ConstantInfo}
    (Hleft : FreshExtension source leftEntries target)
    (Hright : FreshExtension source rightEntries target)
    (hsourceWF : source.constants.WF) : leftEntries ~ rightEntries := by
  have leftNodup : leftEntries.Nodup :=
    nodup_of_map_nodup ConstantInfo.name (Hleft.namesNodup hsourceWF)
  have rightNodup : rightEntries.Nodup :=
    nodup_of_map_nodup ConstantInfo.name (Hright.namesNodup hsourceWF)
  apply List.Subperm.antisymm
  · apply List.subperm_of_subset leftNodup
    intro ci hci
    have hfind := Hleft.findEntry hsourceWF hci
    rcases Hright.entryOrigin hsourceWF hfind with hsource |
      ⟨entry, hentry, _hname, hfound⟩
    · rw [Hleft.sourceFresh hsourceWF hci] at hsource
      contradiction
    · simpa [hfound] using hentry
  · apply List.subperm_of_subset rightNodup
    intro ci hci
    have hfind := Hright.findEntry hsourceWF hci
    rcases Hleft.entryOrigin hsourceWF hfind with hsource |
      ⟨entry, hentry, _hname, hfound⟩
    · rw [Hright.sourceFresh hsourceWF hci] at hsource
      contradiction
    · simpa [hfound] using hentry

/-- **The rule-free restored block of a nested run.** The stripped environment's validity is
read off the rule-free stage `RuleFreeStage`. Source parameter formation `Hparameters` is a
premise. -/
theorem NestedRun.assemblyBase {res : ElimNestedInductive.Result} {sourceProdEnv : Environment}
    {sourceTypes : List InductiveType} {sourceVEnv : VEnv} {decl : VInductDecl}
    {lparams : List Name} {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams res.types.toArray loweredEnv₀}
    (E : NestedRun res sourceProdEnv sourceTypes sourceVEnv decl lparams nparams isUnsafe
      safety outEnv L)
    {ves : VEnvs} (wf : ves.WF sourceProdEnv) (hsourceVEnv : sourceVEnv = ves.venv safety)
    (Hsources : SourceSyntaxChecks sourceProdEnv sourceTypes)
    (Hparameters : decl.SourceParameterWF sourceVEnv)
    (hvisible : safety ≤ (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    Nonempty { B : RestoredBlockBase E.restoration sourceVEnv decl lparams nparams isUnsafe
      safety // B.loweredDecl = E.lowered.loweredDecl ∧
        ((B.typeEntries ++ B.constructorEntries ++ B.recursorEntries).map Prod.fst).Perm
          E.restoration.entries } := by
  obtain ⟨context_env, context_lparams, context_safety, lowered_isUnsafe_source,
    lowered_initialEnv, validationFuel, lowering,
    restoration, primitiveSafe, validationEnv, validationEnvironment, recursorTypeValidation,
    -, auxiliaryHeaderEnv, headerValidationEnvironment, auxiliaryVEnv,
    auxiliarySelection, auxiliaryTranslations, sourceCore, sourceCoreDecl_eq,
    auxiliaryVEnv_eq_sourceCore, -⟩ := E
  obtain ⟨c, stats, Hc, phase, loweredDecl, ctorEnv, R, check⟩ := L
  dsimp only at *
  subst context_env context_lparams context_safety lowered_initialEnv
    lowered_isUnsafe_source sourceCoreDecl_eq auxiliaryVEnv_eq_sourceCore
  have HcChecker : CheckerEnv c.safety c.env Hc.venv := Hc.checkerEnv
  let Hprod := check
  have hsourceWF : c.env.constants.WF := Hc.map_wf
  have hempty : ({ lvls := c.lparams.map .param, newTypes := #[] } :
      ElimNestedInductive.State).nestedAux = #[] := rfl
  have Hlower : NestedLoweringOutputClosed c.env validationFuel.inductiveFuel nparams
      sourceTypes { ({ lvls := c.lparams.map .param, newTypes := #[] } :
        ElimNestedInductive.State) with newTypes := sourceTypes.toArray } res := lowering
  have Hchecked : SourceSyntaxChecked sourceTypes :=
    checkInductiveSources_refines c.env sourceTypes () Hsources
  have Hcore := sourceCore.core
  have Hmetadata := sourceCore.checked
  -- the header side environment
  have Caux := ValidationHeaderEnvironment.checkerEnvOfLowering HcChecker
    headerValidationEnvironment sourceCore.sourceAdded sourceCore.headerValidationValid
  -- formation
  obtain ⟨D, hD⟩ := R.nestedExpansionData wf hsourceVEnv Hc Hlower Hsources Hcore Hmetadata
    sourceCore.sourceHeaders sourceCore.sourceAdded Caux.wf auxiliarySelection
    auxiliaryTranslations Hparameters
  have Harity : sourceCore.sourceDecl.ConstructorArityPrefix loweredDecl := by
    have h := D.constructorArityPrefix
    rw [hD] at h
    exact h
  -- the projection stage and the constructor side environment
  have hprojectedWF : (sourceCore.envCtors.addProjections
      sourceCore.sourceDecl.projectionEntries).WF :=
    VEnv.WF.inductProjections (block := ⟨sourceCore.sourceDecl.typeConstants,
        sourceCore.sourceDecl.constructorConstants, [], [],
        sourceCore.sourceDecl.projectionEntries⟩)
      HcChecker.wf sourceCore.validationValid.tr.wf
      (TrInductDeclCore.sourceNames_nodup Hcore)
      (TrInductDeclCore.typeHeadersWF Hcore) (TrInductDeclCore.constructorUvars Hcore)
      (TrInductDeclCore.constructorsWF Hcore) Hparameters Hparameters.rawCtorShape
      rfl rfl rfl Hcore.typesAdded Hcore.ctorsAdded
  have HtypeValid := validationEnvironment.validProjected Hlower Hc Hprod Hcore Hmetadata
    Hchecked Harity hempty restoration sourceCore.validationValid HcChecker.toValid hprojectedWF
  have hle : Hc.venv ≤ sourceCore.envCtors.addProjections
      sourceCore.sourceDecl.projectionEntries :=
    (VEnv.addConstVals_le Hcore.typesAdded).trans
      ((VEnv.addConstVals_le Hcore.ctorsAdded).trans VEnv.addProjections_le)
  have HtypeChecker : CheckerEnv c.safety validationEnv
      (sourceCore.envCtors.addProjections sourceCore.sourceDecl.projectionEntries) :=
    CheckerEnv.ofSideExtension HcChecker HtypeValid
      (fun h => validationEnvironment.preservesSourceFind hsourceWF h)
      (fun h => by
        rcases validationEnvironment.findCases hsourceWF h with hold |
            ⟨_, _, _, _, _, he⟩ | ⟨_, _, _, _, _, _, _, _, _, he⟩
        · exact hold
        · cases he
        · cases he)
      hle
  -- the source families
  have Hfamilies : ∀ name nested, res.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true := by
    rcases Hlower with ⟨_finalState, Hrun, _Hcache, _Hparams⟩
    exact Hrun.resultFamilyNamesReservedFresh hempty
  have Hconstructors := Hlower.restoreAuxConstructorsFreshAtTypes Hc Hprod Hcore
    Hc.checking.constructorOwners hempty
  obtain ⟨primaryRecursors, Hsource⟩ :=
    Hlower.sourceTraceAtFreshOfTelescopeTranslations Hc Hprod Hchecked Hcore Hmetadata
      Hfamilies Hconstructors hempty restoration (by
        intro familyIdx hfamily _hdecl hentry stepSource stepTarget Hstep
        exact Hlower.restoredSourceTelescopeAtFreshOfValidation Hprod HtypeChecker
          recursorTypeValidation hempty familyIdx hfamily hentry Hstep)
  -- the auxiliary recursors
  have hsourceNonempty : sourceTypes ≠ [] := by
    rcases Hlower with ⟨_finalState, Hrun, _Hcache, _Hparams⟩
    rcases Hrun.source with ⟨first, rest, _, _, _, _, htypes, _⟩
    rw [htypes]; simp
  obtain ⟨main, rest, rfl⟩ : ∃ main rest, sourceTypes = main :: rest := by
    cases sourceTypes with
    | nil => exact (hsourceNonempty rfl).elim
    | cons main rest => exact ⟨main, rest, rfl⟩
  have Halignment := restoration.generatedAlignmentTraceOfKernel Hlower Hc Hprod hempty
  obtain ⟨auxiliaryRecursors, Hauxiliary⟩ := Halignment.recursorTraceOfValidation HtypeChecker
    recursorTypeValidation (fun _ h => h) []
  -- the dependency-order replay and its abstract stages
  obtain ⟨nondeltaEntries, Hnondelta, hnondelta⟩ := restoration.freshExtensionNondelta hsourceWF
  obtain ⟨typeEntries, constructorEntries, primaryRecursorEntries, primaryActualEntries,
    Hprimary⟩ := Hsource.existsExactCanonicalSourceReplay Hlower Hprod hempty hvisible hsourceWF
  have hprimaryWF := Hprimary.fresh.targetWF hsourceWF
  obtain ⟨auxiliaryEntries, HauxReplay⟩ := Hauxiliary.existsInDependencyOrder hprimaryWF
  let replay := Hprimary.appendAuxiliaryRecursors HauxReplay
  have htypesAbstract : Hc.venv.addConstVals (replay.typeEntries.map Prod.snd) =
      some sourceCore.envTypes := by
    rw [replay.typeValues]
    simpa [VInductDecl.typeConstants] using Hcore.typesAdded
  have hconstructorsAbstract : sourceCore.envTypes.addConstVals
      (replay.constructorEntries.map Prod.snd) = some sourceCore.envCtors := by
    rw [replay.constructorValues]
    simpa [VInductDecl.constructorConstants] using Hcore.ctorsAdded
  obtain ⟨primitiveEntries, Hprimitive⟩ := primitiveSafe
  obtain ⟨recursorVEnv, S, hT, hC⟩ := replay.existsBlockStages
    sourceCore.sourceDecl.projectionEntries HcChecker.toValid.tr hprojectedWF Hprimitive
    Hnondelta hnondelta htypesAbstract hconstructorsAbstract
  have hownersNonempty : sourceCore.sourceDecl.types ≠ [] :=
    TrInductDeclCore.nonempty Hcore (by simp)
  obtain ⟨mainT, restT, htypesSource⟩ : ∃ m r, sourceCore.sourceDecl.types = m :: r := by
    cases h : sourceCore.sourceDecl.types with
    | nil => exact (hownersNonempty h).elim
    | cons m r => exact ⟨m, r, rfl⟩
  have Hsource' : SourceFamilyTranslations sourceCore.sourceDecl c.lparams c.safety Hc.venv
      S.venvTypes (S.venvCtors.addProjections sourceCore.sourceDecl.projectionEntries)
      restoration.inductives (mainT :: restT) primaryRecursors := by
    rw [hT, hC, ← htypesSource]; exact Hsource
  have Hauxiliary' : AuxiliaryRecursorTranslations c.safety
      (S.venvCtors.addProjections sourceCore.sourceDecl.projectionEntries)
      (S.venvCtors.addProjections sourceCore.sourceDecl.projectionEntries)
      restoration.auxiliaries [] auxiliaryRecursors := by
    rw [hC]; exact Hauxiliary
  exact ⟨⟨{
    loweredDecl := loweredDecl
    typeEntries := replay.typeEntries
    constructorEntries := replay.constructorEntries
    recursorEntries := replay.recursorEntries
    recursorVEnv := recursorVEnv
    install := S
    main := mainT
    rest := restT
    typesSource := htypesSource
    sourceRecursors := primaryRecursors
    auxiliaryRecursors := auxiliaryRecursors
    sourceTranslations := Hsource'
    auxiliaryRecursorTrace := Hauxiliary'
    typeValues := replay.typeValues
    constructorValues := replay.constructorValues
    recursorValues := replay.recursorValues
    formationAssembly := D
    formationExpanded := hD
    checked := Hmetadata
    uvars := Hcore.uvars
    numParams := Hcore.nparams
    unsafeEq := Hcore.isUnsafe
    sourceNonempty := by simp }, rfl,
    replay.kernelOrder.symm.trans
      (replay.fresh.permOfSameTarget (restoration.freshExtensionExact hsourceWF) hsourceWF)⟩⟩

end VerifyInductive
end Lean4Lean
