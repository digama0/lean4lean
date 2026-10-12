import Lean4Lean.Verify.Inductive.Nested.Restoration.LoweringRestoration
import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceValidation
import Lean4Lean.Verify.Inductive.Nested.Lowering.OccurrenceTyping
import Lean4Lean.Verify.Inductive.Nested.Lowering.Output
import Lean4Lean.Verify.Inductive.Nested.Lowering.Queue
import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.Checks
import Lean4Lean.Verify.Inductive.Nested.Restoration.Steps
import Lean4Lean.Verify.Inductive.Recursor.Binders.MinorAlignment
import Lean4Lean.Verify.Inductive.Recursor.Context.ForallTelescope
import Lean4Lean.Verify.Typing.EnvironmentRestriction
import Lean4Lean.Verify.Inductive.Recursor.Binders.MotivesAndIndices
import Lean4Lean.Verify.Inductive.Formation
import Lean4Lean.Verify.Inductive.Install.Ordinary

/-! Source translations of a nested declaration: the lowering run (`NestedLoweringRun`,
`NestedLoweringOutputClosed`) maps each source family to its lowered family, and the
restoration folds are interpreted as the source family translations
(`SourceFamilyTranslations`) of the submitted declaration, with headers, constructors and
source recursors. The file ends with `Environment.addInductive.checkedLoweringClosedWF`,
which runs the source checks and lowering of `Environment.addInductive` before
dispatch. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Source family headers need no restoration: lowering preserves them
verbatim, so the positional translation proved for the lowered block is
already the checked translation of the corresponding source header. The list
position is the one fixed by lowering; the owner is not recovered by name. -/
theorem NestedLoweringOutputClosed.sourceHeaderTranslationAtFresh
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[])
    (Hcore : TrInductDeclCore sourceVEnv lparams nparams result.types
      isUnsafe decl envTypes envCtors)
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length) :
    ∃ hdecl : familyIdx < decl.types.length,
      TrSourceConst sourceVEnv lparams sourceTypes[familyIdx].name
        sourceTypes[familyIdx].type
        (decl.types[familyIdx]'hdecl).toVConstVal := by
  rcases H.sourceResolvedMappingAtFreshAligned hempty hfamily with
    ⟨_fvars, _stepState, target, _loweredState, _hparams, _hnodup,
      _hsize, Hmapping, htarget⟩
  obtain ⟨hsourceCore, htargetEq⟩ :=
    _root_.getElem?_eq_some_iff.mp htarget
  have hdecl : familyIdx < decl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hcore]
    exact hsourceCore
  have Hheader :=
    (Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hcore familyIdx
      hsourceCore hdecl).header
  refine ⟨hdecl, ?_⟩
  rw [← Hmapping.name, ← Hmapping.type]
  simpa [htargetEq] using Hheader

/-- The constructor freshness required by source-expression restoration is not a
per-family premise. When lowering and the ordinary run start from the same
kernel environment, it follows from the freshness of the auxiliary families, the
block installation, and the kernel metadata invariant for base constructors. -/
theorem NestedLoweringOutputClosed.restoreAuxConstructorsFreshAtBase
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {ctorEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceVEnv result.types.toArray ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorInstallation R loweredEnv)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[]) :
    RestoreAuxConstructorsFresh result loweredEnv sourceVEnv := by
  rcases H with ⟨finalState, Hrun, _Hcache, _Hparams⟩
  exact Hprod.restoreAuxConstructorsFreshOfInstalled Howners
    (Hrun.resultFamilyNamesFreshOfEmpty Hc.checking.tr.map_wf hempty)

/-- Lift auxiliary-constructor freshness through the source-header prefix
reconstructed from lowering, without source constructors or a source
declaration. -/
theorem NestedLoweringOutputClosed.restoreAuxConstructorsFreshAtHeaderPrefix
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv sourceTypesVEnv : VEnv}
    {ctorEnv : Environment}
    {R : ConstructorCheck c stats loweredDecl nparams isUnsafe depth sourceVEnv result.types.toArray ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorInstallation R loweredEnv)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst sourceVEnv c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (loweredDecl.types.take sourceTypes.length))
    (HsourceAdded : sourceVEnv.addConstVals
      ((loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some sourceTypesVEnv) :
    RestoreAuxConstructorsFresh result loweredEnv sourceTypesVEnv := by
  intro name nested auxFamily hrecognized
  have Hbase := H.restoreAuxConstructorsFreshAtBase Hc Hprod Howners hempty
  have hbase : sourceVEnv.constants name = none :=
    Hbase name nested auxFamily hrecognized
  rcases H with ⟨finalState, Hrun, _Hcache, _Hparams⟩
  have hnames : ∀ ci ∈
      (loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal, ci.name ≠ name := by
    intro ci hci
    rcases List.mem_map.mp hci with ⟨targetType, htargetType, rfl⟩
    rcases Lean4Lean.List.Forall₂.forall_exists_r HsourceHeaders targetType
        htargetType with ⟨sourceType, hsourceType, Htype⟩
    rcases Hrun.preservesInitialTypeName
        ⟨sourceType, by simpa using hsourceType, rfl⟩ with
      ⟨loweredType, hloweredType, hloweredName⟩
    rcases Hprod.findSourceHeader Hc (by simpa using hloweredType) with
      ⟨info, hheader, _hctors, _hall⟩
    intro htargetName
    have hsourceName : sourceType.name = name :=
      Htype.name.symm.trans (by simpa using htargetName)
    have hloweredName' : loweredType.name = name :=
      hloweredName.trans hsourceName
    rw [hloweredName'] at hheader
    rcases getNestedIfAuxCtor_refines result loweredEnv name nested auxFamily
        hrecognized with ⟨⟨ctorInfo, hconstructor, _hfamily, _hmap⟩⟩
    rw [hheader] at hconstructor
    cases hconstructor
  rw [VEnv.addConstVals_constants_of_forall_ne HsourceAdded hnames]
  exact hbase

/-- Alignment of one source family's lowering with the executable
constructor-restoration fold. All executable `oldInfo.type = lowered.type`
facts are consequences of the verified lowered installation; the result keeps
only the translation of the source constructors, proved by the callers. -/
theorem NestedLoweringOutputClosed.sourceConstructorRestorationTraceAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {ctorEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceVEnv result.types.toArray ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorInstallation R loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv) :
    ∃ fvars : List FVarId, ∃ stepState target loweredState,
      result.params = (fvars.map Expr.fvar).toArray ∧
      fvars.Nodup ∧
      result.params.size = nparams ∧
      result.types[familyIdx]? = some target ∧
      Hstep.oldInfo.ctors = target.ctors.map (fun ctor => ctor.name) ∧
      ∃ _Hmappings : ConstructorLowerings.Resolved loweredSourceEnv result.params
          nparams result sourceTypes[familyIdx].ctors stepState
            (target.ctors, loweredState),
        ∃ _Htrace : FoldSteps
          (RestoredConstructorStep result loweredEnv)
          (target.ctors.map (fun ctor => ctor.name))
          Hstep.restored.headerEnv Hstep.restored.constructorEnv,
          LoweredRestoredConstructors result loweredSourceEnv loweredEnv
            result.params nparams c.safety c.lparams
              sourceTypes[familyIdx].ctors stepState target.ctors loweredState
              Hstep.restored.headerEnv Hstep.restored.constructorEnv := by
  rcases H.sourceResolvedMappingAtFreshAligned hempty hfamily with
    ⟨fvars, stepState, target, loweredState, hparams, hnodup, hsize,
      Hmapping, htarget⟩
  have htargetMem : target ∈ result.types.toArray.toList := by
    simpa using List.mem_of_getElem? htarget
  have hctorNames : Hstep.oldInfo.ctors =
      target.ctors.map (fun ctor => ctor.name) :=
    Hstep.oldConstructors_eq_ofInstalled Hc Hprod htargetMem
      Hmapping.name.symm
  have Htrace : FoldSteps
      (RestoredConstructorStep result loweredEnv)
      (target.ctors.map (fun ctor => ctor.name)) Hstep.restored.headerEnv
        Hstep.restored.constructorEnv := by
    rw [← hctorNames]
    exact Hstep.restored.constructors
  have Haligned := LoweredRestoredConstructors.ofInstalled Hprod
    htargetMem Hmapping.constructors Htrace (by
      intro targetCtor htargetCtor
      exact htargetCtor)
  exact ⟨fvars, stepState, target, loweredState, hparams, hnodup, hsize,
    htarget, hctorNames, Hmapping.constructors, Htrace, Haligned⟩

/-- Executable restoration never renames the source recursor of a source
mutual-family member. Source families occupy positions strictly
before the auxiliary suffix from which `mkAuxRecNameMap` is built, and the
installed mutual-family metadata proves that these positions are distinct. -/
theorem NestedLoweringOutputClosed.sourceRecursorUnmappedAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {ctorEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceVEnv result.types.toArray ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorInstallation R loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length) :
    (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2.find?
      (Lean.mkRecName sourceTypes[familyIdx].name) = none := by
  rcases H with ⟨finalState, Hrun, Hcache, Hparams⟩
  rcases Hrun.source with
    ⟨main, rest, tail, paramsState, lctx, params, hsource, Hopening,
      hinitial, hinitialAux, hinitialNext, _hprefix, Hctx, Hselection, Hqueue⟩
  subst sourceTypes
  have Hclosed : NestedLoweringOutputClosed loweredSourceEnv fuel nparams
      (main :: rest)
      { initialState with newTypes := (main :: rest).toArray } result :=
    ⟨finalState, Hrun, Hcache, Hparams⟩
  rcases Hclosed.sourceResolvedMappingAtFreshAligned hempty (j := 0) (by simp) with
    ⟨_mainFVars, _mainState, mainTarget, _mainLoweredState, _mainParams,
      _mainNodup, _mainSize, Hmain, hmainTarget⟩
  have hmainMem : mainTarget ∈ result.types.toArray.toList := by
    simpa using List.mem_of_getElem? hmainTarget
  rcases Hprod.findSourceHeader Hc hmainMem with
    ⟨mainInfo, hmainFind, _hmainCtors, hall⟩
  have hmainFind' :
      loweredEnv.find? main.name = some (.inductInfo mainInfo) := by
    have hmainName : mainTarget.name = main.name := by
      simpa using Hmain.name
    rw [← hmainName]
    exact hmainFind
  apply mkAuxRecNameMap_recMap_find_none main rest loweredEnv mainInfo
    hmainFind'
  intro hquery
  rcases List.mem_map.mp hquery with ⟨suffixName, hsuffix, hrecName⟩
  have hsuffixName : suffixName = (main :: rest)[familyIdx].name :=
    mkRecName_injective (hrecName.trans rfl)
  rcases List.mem_drop_iff_getElem.mp hsuffix with
    ⟨suffixIdx, hsuffixBound, hsuffixGet⟩
  rcases Hclosed.sourceResolvedMappingAtFreshAligned hempty hfamily with
    ⟨_familyFVars, _familyState, familyTarget, _familyLoweredState,
      _familyParams, _familyNodup, _familySize, Hfamily, hfamilyTarget⟩
  have hfamilyInfo : mainInfo.all[familyIdx]? =
      some (main :: rest)[familyIdx].name := by
    rw [hall]
    rw [List.getElem?_map, hfamilyTarget]
    simp only [Option.map_some, Option.some.injEq]
    exact Hfamily.name
  have hsuffixInfo :
      mainInfo.all[(main :: rest).length + suffixIdx]? =
        some (main :: rest)[familyIdx].name := by
    exact _root_.getElem?_eq_some_iff.mpr
      ⟨by omega, hsuffixGet.trans hsuffixName⟩
  have hfamilyResultBound : familyIdx < result.types.length :=
    (_root_.getElem?_eq_some_iff.mp hfamilyTarget).1
  have hindexEq : familyIdx = (main :: rest).length + suffixIdx :=
    (List.getElem?_inj (l := mainInfo.all)
      (i := familyIdx) (j := (main :: rest).length + suffixIdx)
      (by simpa [hall] using hfamilyResultBound)
      (Hprod.closed main.name mainInfo hmainFind').names).mp
      (hfamilyInfo.trans hsuffixInfo.symm)
  omega

/-- Interpret one source family's constructor-restoration fold using the
checked source constructor translations. Freshness of the auxiliary names turns
the syntactic no-auxiliary condition into the disjointness required by the
lowering/restoration inverse. -/
theorem NestedLoweringOutputClosed.sourceConstructorTypingAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv canonicalEnv : VEnv} {ctorEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceVEnv result.types.toArray ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorInstallation R loweredEnv)
    (Hsources : SourceSyntaxChecked sourceTypes)
    (hfamily : familyIdx < sourceTypes.length)
    (Htranslations : List.Forall₂ (fun source constructor =>
      TrSourceConst canonicalEnv c.lparams source.name source.type constructor)
      sourceTypes[familyIdx].ctors constructors)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv canonicalEnv)
    (hempty : initialState.nestedAux = #[])
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv) :
    RestoredConstructorTranslations result loweredEnv c.lparams c.safety canonicalEnv
      Hstep.oldInfo.ctors Hstep.restored.headerEnv
        Hstep.restored.constructorEnv sourceTypes[familyIdx].ctors
          constructors := by
  rcases H.sourceConstructorRestorationTraceAtFresh Hc Hprod hempty
      familyIdx hfamily Hstep with
    ⟨fvars, stepState, target, loweredState, hparams, hnodup, _hsize,
      htarget, hctorNames, Hmappings, Htrace, Haligned⟩
  have Hsyntax := (Hsources.getElem familyIdx hfamily).constructors
  have Hsemantic := Haligned.sourceTyping Htranslations Hsyntax (by
    intro source hsource
    have HsourceTranslation :=
      Lean4Lean.List.Forall₂.forall_exists_l Htranslations source hsource
    rcases HsourceTranslation with ⟨constructor, _hconstructor, Hsource⟩
    exact (Hsyntax.of_mem hsource).noNestedAux
      |>.restoreSourceDisjointOfFresh Hsource.type.constantsDefined Hfamilies
        Hconstructors) rfl fvars hparams hnodup H.toResult.resultNParams
      (H.resultParamsSize.trans H.toResult.resultNParams)
  simpa [hctorNames] using Hsemantic

/-- Source-constructor translations for one restored family. The constructor
list comes from the successful header-only executable validation; the
lowering/restoration mapping supplies the installed translations. -/
theorem NestedLoweringOutputClosed.sourceConstructorTypingAtFreshOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv sourceTypesVEnv : VEnv} {ctorEnv : Environment}
    {R : ConstructorCheck c stats loweredDecl nparams isUnsafe depth sourceVEnv result.types.toArray ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorInstallation R loweredEnv)
    (Hsources : SourceSyntaxChecked sourceTypes)
    (Howners : ConstructorOwnersPresent c.env)
    (HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst sourceVEnv c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (loweredDecl.types.take sourceTypes.length))
    (HsourceAdded : sourceVEnv.addConstVals
      ((loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some sourceTypesVEnv)
    (HvalidationValid : CheckerEnv c.safety validationEnv sourceTypesVEnv)
    (hclosed : ∀ type ∈ sourceTypes, ∀ ctor ∈ type.ctors,
      ctor.type.FVarsIn fun _ => False)
    (HparameterRun :
      Lean4Lean.validateSourceConstructorTypes.run validationEnv
        c.lparams c.safety validationFuel sourceTypes = .ok ())
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv) :
    ∃ constructors : List VConstVal,
      RestoredConstructorTranslations result loweredEnv c.lparams c.safety
        sourceTypesVEnv Hstep.oldInfo.ctors Hstep.restored.headerEnv
          Hstep.restored.constructorEnv sourceTypes[familyIdx].ctors
            constructors := by
  rcases validateSourceConstructorTypes.sourceConsts_of_run
      HvalidationValid hclosed HparameterRun (List.getElem_mem hfamily) with
    ⟨constructors, Htranslations⟩
  have Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true := by
    rcases H with ⟨_finalState, Hrun, _Hcache, _Hparams⟩
    exact Hrun.resultFamilyNamesReservedFresh hempty
  have Hconstructors : RestoreAuxConstructorsFresh result loweredEnv
      sourceTypesVEnv :=
    H.restoreAuxConstructorsFreshAtHeaderPrefix Hc Hprod Howners hempty
      HsourceHeaders HsourceAdded
  exact ⟨constructors, H.sourceConstructorTypingAtFresh Hc Hprod
    Hsources hfamily Htranslations Hfamilies Hconstructors hempty Hstep⟩

/-- `TrSourceRecursor` for one restored source recursor, from the translation of
its restored executable type in the source environment. The source translation,
the shared metadata, lowering, and the generated recursor entry determine every
remaining name, universe, and telescope-length premise. -/
theorem NestedLoweringOutputClosed.trSourceRecursorAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors recEnv : VEnv}
    {ctorEnv : Environment}
    {R : ConstructorCheck c stats loweredDecl nparams isUnsafe depth sourceVEnv result.types.toArray ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorInstallation R loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (hdecl : familyIdx < sourceDecl.types.length)
    (hentry : familyIdx < Hprod.entries.length)
    (Hstep : RestoredInductiveStep result loweredEnv
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv)
    (targetType : VExpr)
    (Htype : TrExprS recEnv Hstep.restored.recursor.oldInfo.levelParams []
      Hstep.restored.recursor.restored.newInfo.type targetType) :
    ∃ recursor, Nonempty (TrSourceRecursor sourceDecl
      (sourceDecl.types[familyIdx]'hdecl) Hstep.restored.recursor recEnv
      recursor) := by
  rcases H.sourceResolvedMappingAtFreshAligned hempty hfamily with
    ⟨_fvars, _stepState, target, _loweredState, _hparams, _hnodup,
      _hsize, Hmapping, htarget⟩
  obtain ⟨hresultIdx, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp htarget
  have howner : familyIdx < result.types.toArray.size := by
    simpa using hresultIdx
  have hrecInfo : familyIdx < Hprod.recInfos.size := by
    simpa [Hprod.generated.length] using hentry
  have hloweredDecl : familyIdx < loweredDecl.types.length := by
    simpa [Hprod.cardinality.records] using hrecInfo
  have hdeclLength : sourceDecl.types.length ≤ loweredDecl.types.length := by
    calc
      sourceDecl.types.length = sourceTypes.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource).symm
      _ ≤ result.types.length := H.toResult.sourceTypes_length_le
      _ = loweredDecl.types.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
  have hindices : (sourceDecl.types[familyIdx]'hdecl).numIndices =
      Hprod.recInfos[familyIdx]!.indices.size := by
    exact (Hmetadata.numIndices hdeclLength familyIdx hdecl hloweredDecl).trans
      (Hprod.cardinality.indices familyIdx hrecInfo).symm
  have hsourceName : result.types.toArray[familyIdx]!.name =
      sourceTypes[familyIdx].name := by
    have harray : result.types.toArray[familyIdx]! = target := by
      simp [hresultIdx,
        htargetEq]
    rw [harray, Hmapping.name]
  have holdRecName : Lean.mkRecName sourceTypes[familyIdx].name =
      Lean.mkRecName result.types.toArray[familyIdx]!.name :=
    congrArg Lean.mkRecName hsourceName.symm
  let recursor : VConstVal := {
    name := sourceDecl.recursorName (sourceDecl.types[familyIdx]'hdecl)
    uvars := Hstep.restored.recursor.oldInfo.levelParams.length
    type := targetType }
  have huvars : recursor.uvars = sourceDecl.uvars ∨
      recursor.uvars = sourceDecl.uvars + 1 := by
    exact Hprod.restoredSourceRecursorUvars familyIdx hentry
      Hstep.restored.recursor holdRecName sourceDecl Hsource.uvars
  have hmotives : sourceDecl.types.length ≤
      (Hprod.recInfos.map (·.motive)).size := by
    calc
      sourceDecl.types.length = sourceTypes.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource).symm
      _ ≤ result.types.length := H.toResult.sourceTypes_length_le
      _ = loweredDecl.types.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
      _ = Hprod.recInfos.size := Hprod.cardinality.records.symm
      _ = (Hprod.recInfos.map (·.motive)).size := by simp
  have hminors : sourceDecl.ownedConstructors.length ≤
      (Hprod.recInfos.flatMap (·.minors)).size := by
    calc
      sourceDecl.ownedConstructors.length =
          (Lean4Lean.VerifyInductive.ownedConstructors sourceTypes).length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length
          Hsource).symm
      _ ≤ (Lean4Lean.VerifyInductive.ownedConstructors result.types).length :=
        H.toResult.sourceOwnedConstructors_length_le hempty
      _ = loweredDecl.ownedConstructors.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length
          R.core
      _ = (Hprod.recInfos.flatMap (·.minors)).size :=
        Hprod.cardinality.minors.symm
  refine ⟨recursor, ⟨Hprod.restoredTrSourceRecursor
    familyIdx hentry Hstep.restored.recursor holdRecName sourceDecl hdecl
    recursor recEnv rfl huvars rfl H.toResult.resultNParams
    (Hsource.nparams.trans H.toResult.resultNParams.symm) hmotives hminors
    hindices ?_⟩⟩
  simpa [recursor] using Htype

/-- Binder-explicit form of `trSourceRecursorAtFresh`: the caller provides the
typed restored telescope, rather than a translation of the whole expression. -/
theorem NestedLoweringOutputClosed.trSourceRecursorAtFreshOfTelescope
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors recEnv : VEnv}
    {ctorEnv : Environment}
    {R : ConstructorCheck c stats loweredDecl nparams isUnsafe depth sourceVEnv result.types.toArray ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorInstallation R loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (hdecl : familyIdx < sourceDecl.types.length)
    (hentry : familyIdx < Hprod.entries.length)
    (Hstep : RestoredInductiveStep result loweredEnv
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv)
    (targetType : VExpr)
    (Htype : Expr.ForallTelescopeTypeTranslation recEnv
      Hstep.restored.recursor.oldInfo.levelParams []
      Hstep.restored.recursor.restored.newInfo.type
      (result.nparams + (Hprod.recInfos.map (·.motive)).size +
        (Hprod.recInfos.flatMap (·.minors)).size +
        Hprod.recInfos[familyIdx]!.indices.size + 1)
      targetType) :
    ∃ recursor, Nonempty (TrSourceRecursor sourceDecl
      (sourceDecl.types[familyIdx]'hdecl) Hstep.restored.recursor recEnv
      recursor) :=
  H.trSourceRecursorAtFresh Hprod Hsource Hmetadata hempty
    familyIdx hfamily hdecl hentry Hstep targetType Htype.translation

/-- The `SourceFamilyTranslation` of one source family, as used by the fold over
the mutual block. Header and constructor translations come from the source
translation. The source recursor is indexed by the source declaration, while
the installed expanded declaration is used only for the kernel safety metadata
and name preservation. -/
theorem NestedLoweringOutputClosed.sourceInductiveTypingAtFreshExactOwner
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {ctorEnv : Environment}
    {R : ConstructorCheck c stats loweredDecl nparams isUnsafe depth sourceVEnv result.types.toArray ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorInstallation R loweredEnv)
    (Hsources : SourceSyntaxChecked sourceTypes)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (hdecl : familyIdx < sourceDecl.types.length)
    (hentry : familyIdx < Hprod.entries.length)
    (Hsource : TrInductiveType sourceVEnv envTypes c.lparams
      sourceTypes[familyIdx] (sourceDecl.types[familyIdx]'hdecl))
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv envTypes)
    (Hstep : RestoredInductiveStep result loweredEnv
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv)
    (HsourceRec : SourceRecursorSpec sourceDecl
      (sourceDecl.types[familyIdx]'hdecl) envCtors)
    (Hrefine : SourceRecursorRefinement Hstep.restored.recursor
      envCtors HsourceRec.recursor) :
    Nonempty { S : SourceFamilyTranslation sourceDecl c.lparams
        c.safety sourceVEnv envTypes envCtors Hstep //
      S.owner = sourceDecl.types[familyIdx]'hdecl } := by
  rcases H.sourceResolvedMappingAtFreshAligned hempty hfamily with
    ⟨_fvars, _stepState, target, _loweredState, _hparams, _hnodup,
      _hsize, Hmapping, htarget⟩
  obtain ⟨hresultIdx, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp htarget
  have howner : familyIdx < result.types.toArray.size := by simpa using hresultIdx
  have hsourceName : result.types.toArray[familyIdx]!.name =
      sourceTypes[familyIdx].name := by
    have harray : result.types.toArray[familyIdx]! = target := by
      simp [hresultIdx,
        htargetEq]
    rw [harray, Hmapping.name]
  have HctorSemantics := H.sourceConstructorTypingAtFresh Hc Hprod
    Hsources hfamily Hsource.ctors Hfamilies Hconstructors hempty Hstep
  have hrestoredName : Hstep.restored.recursor.restored.newRecName =
      Lean.mkRecName sourceTypes[familyIdx].name := by
    have hunmapped := H.sourceRecursorUnmappedAtFresh Hc Hprod hempty
      familyIdx hfamily
    rw [Hstep.restored.recursor.restored.mappedName]
    apply Std.TreeMap.getD_eq_fallback_of_contains_eq_false
    change Std.TreeMap.contains
      (show Std.TreeMap Name Name Name.quickCmp from
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2)
        (Lean.mkRecName sourceTypes[familyIdx].name) = false
    rw [Std.TreeMap.contains_eq_isSome_getElem?]
    change ((Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2.find?
      (Lean.mkRecName sourceTypes[familyIdx].name)).isSome = false
    rw [hunmapped]
    rfl
  have Hmetadata := Hprod.restoredSourceRecursorMetadata familyIdx hentry
    Hstep.restored.recursor (congrArg Lean.mkRecName hsourceName.symm)
  have hownerName : (sourceDecl.types[familyIdx]'hdecl).name =
      sourceTypes[familyIdx].name := by
    simpa using Hsource.header.name
  have HrecName : HsourceRec.recursor.name =
      Hstep.restored.recursor.restored.newRecName := by
    exact HsourceRec.name.trans <| by
      simpa only [VInductDecl.recursorName_eq_mkRecName] using
        (congrArg Lean.mkRecName hownerName).trans hrestoredName.symm
  have HrecWF : HsourceRec.recursor.toVConstant.WF envCtors := by
    exact HsourceRec.isType
  have HrecSemantics : SourceRecursorTranslation sourceDecl
      (sourceDecl.types[familyIdx]'hdecl) c.safety
      Hstep.restored.recursor envCtors := {
    recursor := HsourceRec.recursor
    safety_le := Hmetadata.1
    uvars := Hrefine.uvars
    type := Hrefine.type
    name := HrecName
    wf := HrecWF
    shape := HsourceRec.shape }
  exact ⟨⟨{
    owner := sourceDecl.types[familyIdx]'hdecl
    header := Hsource.header
    constructors := HctorSemantics
    recursor := HrecSemantics }, rfl⟩⟩

/-- Fold the per-family translations over the restoration fold, in lockstep
with the source declaration's `Forall₂` alignment. The resulting owner list is
therefore the source declaration's literal type list, rather than an
existential list identified later. -/
theorem FoldSteps.sourceInductiveTraceExactOwners
    {decl : VInductDecl} {lparams : List Name}
    {safety : DefinitionSafety} {sourceVEnv envTypes envCtors : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name}
    {sourceTypes : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    {owners : List VInductiveType}
    (Htrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv targetProdEnv)
    (Htypes : List.Forall₂
      (TrInductiveType sourceVEnv envTypes lparams) sourceTypes owners)
    (Hsemantics : ∀ i
      (hsource : i < sourceTypes.length) (howner : i < owners.length)
      stepSource stepTarget
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        sourceTypes[i] stepSource stepTarget)
      (_Htype : TrInductiveType sourceVEnv envTypes lparams
        sourceTypes[i] owners[i]),
      Nonempty { S : SourceFamilyTranslation decl lparams safety
          sourceVEnv envTypes envCtors Hstep // S.owner = owners[i] }) :
    ∃ recursors,
      SourceFamilyTranslations decl lparams safety sourceVEnv
        envTypes envCtors Htrace owners recursors := by
  induction Htrace generalizing owners with
  | nil =>
    cases Htypes
    exact ⟨[], .nil _⟩
  | @cons head source middle tail target Hstep Htail ih =>
    cases Htypes with
    | @cons _ owner _ tailOwners HheadTypes HtailTypes =>
      rcases Hsemantics 0 (by simp) (by simp) source middle (by
          simpa using Hstep) (by simpa using HheadTypes) with
        ⟨⟨Hhead, hheadOwner⟩⟩
      have hheadOwner' : Hhead.owner = owner := by
        simpa using hheadOwner
      rcases ih HtailTypes (fun i hsource howner stepSource stepTarget
          HtailStep HtailType => by
        have hsource' : i + 1 < (head :: tail).length := by
          simpa using hsource
        have howner' : i + 1 < (owner :: tailOwners).length := by
          simpa using howner
        rcases Hsemantics (i + 1) hsource' howner' stepSource stepTarget
            (by simpa using HtailStep) (by simpa using HtailType) with
          ⟨⟨S, hS⟩⟩
        exact ⟨⟨S, by simpa using hS⟩⟩) with
        ⟨tailRecursors, Hrest⟩
      cases hheadOwner'
      exact ⟨Hhead.recursor.recursor :: tailRecursors,
        .cons Hstep Htail Hhead.header Hhead.constructors Hhead.recursor
          Hrest⟩

/-- `SourceFamilyTranslations` for the whole mutual block, from telescope
translations of the restored source recursor types. The per-family premise is
decomposed at every forall binder and includes typehood of every domain and of
the result. The fold is indexed by the literal source declaration types, so the
nested installation never chooses an existential owner list. -/
theorem NestedLoweringOutputClosed.sourceTraceAtFreshOfTelescopeTranslations
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors recEnv : VEnv}
    {ctorEnv : Environment}
    {R : ConstructorCheck c stats loweredDecl nparams isUnsafe depth sourceVEnv result.types.toArray ctorEnv}
    {auxRecNames : List Name}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorInstallation R loweredEnv)
    (Hsources : SourceSyntaxChecked sourceTypes)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv envTypes)
    (hempty : initialState.nestedAux = #[])
    (Hrestored : NestedRestorationFolds result loweredEnv
      loweredSourceEnv (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      allIndNames sourceTypes auxRecNames out)
    (HtelescopeTypes : ∀ familyIdx
      (hfamily : familyIdx < sourceTypes.length)
      (hdecl : familyIdx < sourceDecl.types.length)
      (hentry : familyIdx < Hprod.entries.length)
      (stepSource stepTarget : Environment)
      (Hstep : RestoredInductiveStep result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
        sourceTypes[familyIdx] stepSource stepTarget),
      ∃ targetType, Expr.ForallTelescopeTypeTranslation recEnv
        Hstep.restored.recursor.oldInfo.levelParams []
        Hstep.restored.recursor.restored.newInfo.type
        (result.nparams + (Hprod.recInfos.map (·.motive)).size +
          (Hprod.recInfos.flatMap (·.minors)).size +
          Hprod.recInfos[familyIdx]!.indices.size + 1)
        targetType) :
    ∃ recursors,
      SourceFamilyTranslations sourceDecl c.lparams c.safety
        sourceVEnv envTypes recEnv Hrestored.inductives sourceDecl.types
          recursors := by
  apply Hrestored.inductives.sourceInductiveTraceExactOwners
    Hsource.types
  intro familyIdx hfamily hdecl stepSource stepTarget Hstep Htype
  rcases H.toResult.sourceResolvedMappingAtFresh hempty hfamily with
    ⟨_mappingParams, _mappingState, _mappingTarget, _mappingLowered,
      _mappingSize, _mapping, htarget⟩
  have hresult : familyIdx < result.types.length :=
    (_root_.getElem?_eq_some_iff.mp htarget).1
  have hentry : familyIdx < Hprod.entries.length := by
    rw [Hprod.generated.length, Hprod.cardinality.records,
      ← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]
    simpa using hresult
  rcases HtelescopeTypes familyIdx hfamily hdecl hentry stepSource stepTarget
      Hstep with ⟨targetType, Htelescope⟩
  rcases H.trSourceRecursorAtFreshOfTelescope Hprod Hsource
      Hmetadata hempty familyIdx hfamily hdecl hentry Hstep targetType
        Htelescope with
    ⟨recursor, ⟨Hrealization⟩⟩
  have Hrefinement := Hrealization.refinement
  rw [← Hrealization.recursor_eq] at Hrefinement
  exact H.sourceInductiveTypingAtFreshExactOwner Hc Hprod Hsources hempty
    familyIdx hfamily hdecl hentry Htype Hfamilies Hconstructors Hstep
      Hrealization.source Hrefinement

/-- Lift automatically derived auxiliary-constructor freshness through the
source mutual-header environment used to translate source constructors.
An auxiliary constructor cannot share a name with a source header: lowering
preserves every source header in the installed block, where the two names
would otherwise resolve to incompatible kernel metadata. -/
theorem NestedLoweringOutputClosed.restoreAuxConstructorsFreshAtTypes
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {ctorEnv : Environment}
    {R : ConstructorCheck c stats loweredDecl nparams isUnsafe depth sourceVEnv result.types.toArray ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorInstallation R loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[]) :
    RestoreAuxConstructorsFresh result loweredEnv envTypes := by
  intro name nested auxFamily hrecognized
  have Hbase := H.restoreAuxConstructorsFreshAtBase Hc Hprod Howners hempty
  have hbase : sourceVEnv.constants name = none :=
    Hbase name nested auxFamily hrecognized
  have hnames : ∀ ci ∈ sourceDecl.typeConstants, ci.name ≠ name := by
    intro ci hci
    simp only [VInductDecl.typeConstants] at hci
    rcases List.mem_map.mp hci with ⟨targetType, htargetType, rfl⟩
    rcases Lean4Lean.List.Forall₂.forall_exists_r Hsource.types targetType
        htargetType with ⟨sourceType, hsourceType, Htype⟩
    rcases H.toResult.sourceTypeName hsourceType with
      ⟨loweredType, hloweredType, hloweredName⟩
    rcases Hprod.findSourceHeader Hc (by simpa using hloweredType) with
      ⟨info, hheader, _hctors, _hall⟩
    intro htargetName
    have hsourceName : sourceType.name = name :=
      Htype.header.name.symm.trans (by simpa using htargetName)
    have hloweredName' : loweredType.name = name :=
      hloweredName.trans hsourceName
    rw [hloweredName'] at hheader
    rcases getNestedIfAuxCtor_refines result loweredEnv name nested auxFamily
        hrecognized with ⟨⟨ctorInfo, hconstructor, _hfamily, _hmap⟩⟩
    rw [hheader] at hconstructor
    cases hconstructor
  rw [VEnv.addConstVals_constants_of_forall_ne Hsource.typesAdded hnames]
  exact hbase

/-- Specialize `restorationSources` from the installed lowered family list
back to each source family, using the lowering run for name
preservation and target constructor telescopes. -/
theorem RecursorInstallation.restorationSourcesOfLowering
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {res : Lean4Lean.ElimNestedInductive.Result}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv res.types.toArray ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hc : ContextWF c) (H : RecursorInstallation R outEnv)
    (Hlower : NestedLoweringRun prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } res) :
    ∀ owner, owner ∈ sourceTypes →
      ∃ oldInfo : InductiveVal,
        outEnv.find? owner.name = some (.inductInfo oldInfo) ∧
        (∀ ctorName, ctorName ∈ oldInfo.ctors →
          ∃ ctorInfo : ConstructorVal,
            outEnv.find? ctorName = some (.ctorInfo ctorInfo) ∧
            RestoreTelescope ctorInfo.type nparams) ∧
        ∃ recInfo : RecursorVal,
          outEnv.find? (Lean.mkRecName owner.name) = some (.recInfo recInfo) ∧
          RestoreTelescope recInfo.type nparams ∧
          ∀ rule ∈ recInfo.rules,
            RestoreTelescope rule.rhs nparams := by
  have Hlowered := H.restorationSources Hc (by
    intro lowered hlowered ctor hctor
    apply Hlower.resultRestorable lowered (by simpa using hlowered)
    exact hctor)
  intro owner howner
  rcases Hlower.sourceTypeName howner with
    ⟨lowered, hlowered, hname⟩
  simpa [hname] using Hlowered lowered (by simpa using hlowered)

/-- Every auxiliary recursor selected by the executable restoration map is
the installed recursor of one of the auxiliary lowered families.
Consequently its type and every rule RHS satisfy the telescope discipline
required by restoration. -/
theorem RecursorInstallation.auxRestorationSourcesOfLowering
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {res : Lean4Lean.ElimNestedInductive.Result}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv res.types.toArray ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hc : ContextWF c) (H : RecursorInstallation R outEnv)
    (Hlower : NestedLoweringRun prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } res) :
    ∀ recName,
      recName ∈ (Lean4Lean.mkAuxRecNameMap outEnv sourceTypes).1 →
      ∃ oldInfo : RecursorVal,
        outEnv.find? recName = some (.recInfo oldInfo) ∧
        RestoreTelescope oldInfo.type nparams ∧
        ∀ rule ∈ oldInfo.rules,
          RestoreTelescope rule.rhs nparams := by
  rcases Hlower with ⟨finalState, Hrun⟩
  rcases Hrun.source with
    ⟨main, rest, tail, paramsState, lctx, params, hsource, Hopening,
      hinitial, _hinitialAux, _hinitialNext, _hprefix, _Hctx, _Hselection, Hqueue⟩
  subst sourceTypes
  have Hrestorable := H.restorationSources Hc (by
    intro lowered hlowered ctor hctor
    apply Hrun.resultRestorable lowered (by simpa using hlowered)
    exact hctor)
  have hmainPresent :
      NewTypeNamePresent
        { initialState with newTypes := (main :: rest).toArray } main.name :=
    ⟨main, by simp, rfl⟩
  rcases Hrun.preservesInitialTypeName hmainPresent with
    ⟨loweredMain, hloweredMain, hmainName⟩
  rcases H.findSourceHeader Hc (by simpa using hloweredMain) with
    ⟨mainInfo, hmainFind, _hctors, hall⟩
  have hmainFind' :
      outEnv.find? main.name = some (.inductInfo mainInfo) := by
    simpa [hmainName] using hmainFind
  have hall' :
      mainInfo.all = res.types.map (fun type => type.name) := by
    simpa using hall
  intro recName hrecName
  rcases mkAuxRecNameMap_recNames_mem main rest outEnv mainInfo hmainFind'
      hrecName with ⟨familyName, hfamilyName, rfl⟩
  rw [hall'] at hfamilyName
  rcases List.mem_map.mp hfamilyName with
    ⟨family, hfamily, rfl⟩
  rcases Hrestorable family (by simpa using hfamily) with
    ⟨_oldIndInfo, _hindFind, _hctors, recInfo, hrecFind, hrecType,
      hrecRules⟩
  exact ⟨recInfo, hrecFind, hrecType, hrecRules⟩

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Run premises for the non-primitive nested path

The nested branch runs `AddInductive` with primitive declarations disabled.
Consequently all three freshness fields of `PrimitiveNamesFresh` are vacuous.
-/

/-- The safety selected by the public inductive entry point is never the
partial-definition mode rejected by recursor generation. -/
theorem inductiveSafety_notPartial (isUnsafe : Bool) :
    (if isUnsafe then DefinitionSafety.unsafe else .safe) ≠
      DefinitionSafety.partial := by
  cases isUnsafe <;> decide

end VerifyInductive
end Lean4Lean
