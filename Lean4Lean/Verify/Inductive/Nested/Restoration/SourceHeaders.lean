import Lean4Lean.Verify.Inductive.Nested.Install.DependencyOrder
import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.Environment
import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.ConstructorEnvironment

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-! # Source headers of nested declarations

The source family headers of a nested declaration are the literal prefix of the lowered block,
so the source header environment and its translation are read off the ordinary header phase of
the lowered run, and the header-only environment of the restoration validation models that
prefix (section 3.3 of the design notes). -/

/-- The source mutual headers form the literal prefix of the lowered
abstract block.  Splitting ordinary header installation at that queue
boundary constructs the source-shaped abstract header environment and the
complete positional source translation without choosing a source declaration
or translating any constructor. -/
theorem NestedLoweringOutputClosed.sourceHeaderPrefix
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Htarget : TrInductDeclCore sourceVEnv lparams nparams result.types
      isUnsafe loweredDecl targetEnvTypes targetEnvCtors)
    (hempty : initialState.nestedAux = #[]) :
    ∃ sourceEnvTypes,
      sourceVEnv.addConstVals
          ((loweredDecl.types.take sourceTypes.length).map
            VInductiveType.toVConstVal) = some sourceEnvTypes ∧
      List.Forall₂
        (fun source target => TrSourceConst sourceVEnv lparams source.name
          source.type target.toVConstVal)
        sourceTypes (loweredDecl.types.take sourceTypes.length) := by
  have hsourceLE : sourceTypes.length ≤ result.types.length :=
    H.toResult.sourceTypes_length_le
  have hloweredLength : loweredDecl.types.length = result.types.length :=
    (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Htarget).symm
  have hprefixLength :
      (loweredDecl.types.take sourceTypes.length).length =
        sourceTypes.length := by
    simp [hloweredLength, hsourceLE]
  have htypeConstants : loweredDecl.typeConstants =
      (loweredDecl.types.take sourceTypes.length).map
          VInductiveType.toVConstVal ++
        (loweredDecl.types.drop sourceTypes.length).map
          VInductiveType.toVConstVal := by
    simp only [VInductDecl.typeConstants, ← List.map_append,
      List.take_append_drop]
  have htypesAdded := Htarget.typesAdded
  rw [htypeConstants] at htypesAdded
  rcases VEnv.addConstVals_append_inv htypesAdded with
    ⟨sourceEnvTypes, HsourceAdded, _HgeneratedAdded⟩
  refine ⟨sourceEnvTypes, HsourceAdded, ?_⟩
  apply List.forall₂_of_getElem hprefixLength.symm
  intro familyIdx hsource htarget
  have hfamily : familyIdx < sourceTypes.length := hsource
  rcases H.sourceHeaderTranslationAtFresh hempty Htarget familyIdx hfamily with
    ⟨hdecl, Hheader⟩
  have hdeclEq : hdecl =
      Nat.lt_of_lt_of_le hsource (by simpa [hloweredLength] using hsourceLE) :=
    Subsingleton.elim _ _
  subst hdecl
  simpa only [List.getElem_take] using Hheader

/-- The source environment's lookups survive the complete lowered installation. -/
theorem RecursorCheck.preservesBaseFind
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    (Hc : ContextWF c)
    (H : RecursorCheck R.toConstructorCheck outEnv)
    (hfind : c.env.find? name = some found) :
    outEnv.find? name = some found := by
  have hheader := Hheaders.installed.preservesSourceFind Hc.checking.tr.map_wf hfind
  have hctor := R.declared.installed.preservesFind
    Hheaders.context.checking.tr.map_wf hheader
  have hlocalWF : H.localContext.env.constants.WF := by
    rw [H.localExtends.env_eq]
    exact R.declared.context.checking.tr.map_wf
  apply H.installed.preservesFind hlocalWF
  rwa [H.localExtends.env_eq]

/-- Every listed constructor of the complete lowered installation is coherent. -/
theorem RecursorCheck.listedConstructors
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    (Hc : ContextWF c)
    (H : RecursorCheck R.toConstructorCheck outEnv) :
    ListedConstructorsCoherent outEnv := by
  have hlocalWF : H.localContext.env.constants.WF := by
    rw [H.localExtends.env_eq]
    exact R.declared.context.checking.tr.map_wf
  exact ListedConstructorsCoherent.ofInductInfosFromDecl Hc.checking.tr.map_wf
    (H.installed.targetMapWF hlocalWF) Hc.checking.listedConstructors
    Hheaders.sourcePresent (H.preservesBaseFind Hc) H.inductInfosFromDecl

/-- Every constant of the complete lowered installation is stored under its own name. -/
theorem RecursorCheck.find?_name
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) (hfind : outEnv.find? name = some found) :
    found.name = name := by
  have hchecking : CheckingEnv H.localContext.safety H.localContext.env R.context.venv := by
    rw [H.localExtends.env_eq, H.localExtends.safety_eq]
    exact R.context.checking.tr
  exact (H.installed.checking hchecking).find?_name hfind

/-- Each source header restored into a header-only side environment was absent from the
environment the side environment extends. -/
theorem FoldSteps.headerFresh
    {loweredEnv : Environment} {allIndNames : List Name}
    {types : List InductiveType} {sourceEnv targetEnv : Environment}
    (H : FoldSteps
      (fun indType source target => ValidationHeaderStep loweredEnv
        allIndNames indType.name source target) types sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) (hmem : indType ∈ types)
    (hlookup : loweredEnv.find? indType.name = some (.inductInfo oldInfo)) :
    sourceEnv.find? oldInfo.name = none := by
  induction H with
  | nil => simp at hmem
  | @cons head source middle tail target Hstep Htail ih =>
    let ci : ConstantInfo := .inductInfo { Hstep.oldInfo with all := allIndNames }
    have hfresh : source.find? ci.name = none :=
      find?_none_of_contains_false hwf
        (by simpa [ci, ConstantInfo.name, ConstantInfo.toConstantVal] using
          Hstep.fresh)
    have hmiddle : middle = source.add ci := Hstep.output
    have hmiddleWF : middle.constants.WF := by
      rw [hmiddle]
      exact constantsWF_add_checked hwf hfresh
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · cases ConstantInfo.inductInfo.inj (Option.some.inj (hlookup.symm.trans Hstep.lookup))
      simpa [ci, ConstantInfo.name, ConstantInfo.toConstantVal] using hfresh
    · have hmid := ih hmiddleWF hmem
      cases hsrc : source.find? oldInfo.name with
      | none => rfl
      | some found =>
        rw [hmiddle, findAddFresh_of_find hwf ci hfresh hsrc] at hmid
        cases hmid

private theorem restoredHeaderValidationValidAux
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    {remainingSources : List InductiveType}
    {remainingTargets : List VInductiveType}
    {currentProdEnv targetProdEnv : Environment}
    {currentVEnv targetVEnv : VEnv}
    (Hvalidation : FoldSteps
      (fun indType source target => ValidationHeaderStep loweredEnv
        (sourceTypes.map (fun type => type.name)) indType.name source target)
      remainingSources currentProdEnv targetProdEnv)
    (Htranslations : List.Forall₂
      (fun source target => TrSourceConst sourceVEnv c.lparams source.name
        source.type target.toVConstVal)
      remainingSources remainingTargets)
    (HsourceMem : ∀ source ∈ remainingSources, source ∈ sourceTypes)
    (HtargetMem : ∀ target ∈ remainingTargets,
      target ∈ loweredDecl.types)
    (Hvalid : CheckingEnv.Valid c.safety currentProdEnv currentVEnv)
    (Hle : sourceVEnv ≤ currentVEnv)
    (Hadded : currentVEnv.addConstVals
      (remainingTargets.map VInductiveType.toVConstVal) = some targetVEnv)
    (Hlisted : ListedConstructorsCoherent targetProdEnv) :
    CheckingEnv.Valid c.safety targetProdEnv targetVEnv := by
  induction Htranslations generalizing currentProdEnv currentVEnv
      targetProdEnv with
  | nil =>
      cases Hvalidation
      have heq : currentVEnv = targetVEnv := by
        simpa [VEnv.addConstVals] using Option.some.inj Hadded
      exact heq ▸ Hvalid
  | @cons source target sources targets Hheader Htail ih =>
      cases Hvalidation with
      | cons HvalidationHead HvalidationTail =>
          have hsourceGlobal : source ∈ sourceTypes :=
            HsourceMem source (by simp)
          rcases List.mem_iff_getElem.mp hsourceGlobal with
            ⟨familyIdx, hfamily, heq⟩
          rcases Hlower.sourceResolvedMappingAtFreshAligned hempty hfamily with
            ⟨_fvars, _mappingState, loweredTarget, _loweredState, _hparams,
              _hnodup, _hsize, Hmapping, htarget⟩
          obtain ⟨hresultFamily, htargetEq⟩ :=
            _root_.getElem?_eq_some_iff.mp htarget
          have hresultArray : familyIdx < result.types.toArray.size := by
            simpa using hresultFamily
          rcases Hprod.findSourceHeaderAt familyIdx hresultArray with
            ⟨installedInfo, hinstalledLookup, hinstalledName, hinstalledType,
              _hinstalledCtors, _hinstalledAll, hinstalledLevels,
              _hinstalledParams, hinstalledUnsafe⟩
          have hinstalledLookup' : loweredEnv.find? source.name =
              some (.inductInfo installedInfo) := by
            subst source
            rw [← Hmapping.name]
            simpa [htargetEq] using hinstalledLookup
          have holdInfo : HvalidationHead.oldInfo = installedInfo :=
            ConstantInfo.inductInfo.inj
              (Option.some.inj
                (HvalidationHead.lookup.symm.trans hinstalledLookup'))
          have HheadTr : TrConstVal c.safety sourceVEnv
              (.inductInfo { HvalidationHead.oldInfo with
                all := sourceTypes.map (fun type => type.name) })
              target.toVConstVal := by
            subst source
            apply Lean4Lean.VerifyInductive.TrSourceConst.inductInfo Hheader
            · simpa [holdInfo] using hinstalledLevels
            · calc
                HvalidationHead.oldInfo.name = installedInfo.name := by
                  rw [holdInfo]
                _ = loweredTarget.name := by
                  simpa [htargetEq] using hinstalledName
                _ = sourceTypes[familyIdx].name := Hmapping.name
            · calc
                HvalidationHead.oldInfo.type = installedInfo.type := by
                  rw [holdInfo]
                _ = loweredTarget.type := by
                  simpa [htargetEq] using hinstalledType
                _ = sourceTypes[familyIdx].type := Hmapping.type
            · have holdUnsafe : HvalidationHead.oldInfo.isUnsafe =
                  isUnsafe := by
                calc
                  HvalidationHead.oldInfo.isUnsafe =
                      installedInfo.isUnsafe := by rw [holdInfo]
                  _ = isUnsafe := hinstalledUnsafe
              simpa [holdUnsafe] using hvisible
          have hname : HvalidationHead.oldInfo.name =
              target.name := by
            exact HheadTr.2
          simp only [List.map_cons, VEnv.addConstVals] at Hadded
          cases hadd : currentVEnv.addConst target.name
              target.toVConstVal.toVConstant with
          | none => simp [hadd] at Hadded
          | some nextVEnv =>
            simp only [hadd] at Hadded
            have hfresh : currentProdEnv.find?
                HvalidationHead.oldInfo.name = none :=
              find?_none_of_contains_false Hvalid.tr.map_wf
                HvalidationHead.fresh
            have HheadTr' := HheadTr.mono Hle
            have hnprim : ¬ Kernel.Environment.primitives.contains
                HvalidationHead.oldInfo.name := by
              rw [hname]
              apply Hheaders.installed.valueNonprimitive
              rw [Hheaders.values]
              simp only [VInductDecl.typeConstants]
              exact List.mem_map.mpr
                ⟨target, HtargetMem target (by simp), rfl⟩
            rw [HvalidationHead.output] at HvalidationTail
            have hnextWF := constantsWF_add_checked (ci := .inductInfo
              { HvalidationHead.oldInfo with all := sourceTypes.map (fun type => type.name) })
              Hvalid.tr.map_wf hfresh
            have HnextListed : ListedConstructorsCoherent (currentProdEnv.add
                (.inductInfo { HvalidationHead.oldInfo with
                  all := sourceTypes.map (fun type => type.name) })) := by
              rcases HvalidationTail.headersFreshExtension hnextWF with ⟨_, Hfresh⟩
              exact Hlisted.ofSub fun h => Hfresh.preservesSourceFind hnextWF h
            have HvalidNext : CheckingEnv.Valid c.safety
                (currentProdEnv.add
                  (.inductInfo { HvalidationHead.oldInfo with
                    all := sourceTypes.map (fun type => type.name) }))
                  nextVEnv :=
              Hvalid.add (ci := .inductInfo { HvalidationHead.oldInfo with
                  all := sourceTypes.map (fun type => type.name) })
                (ci' := target.toVConstVal.toVConstant) hfresh hnprim
                HheadTr'.1 (Hheader.wf.mono Hle)
                (by simpa [HheadTr'.2] using hadd) rfl nofun nofun HnextListed
            apply ih HvalidationTail
            · intro nextSource hmem
              exact HsourceMem nextSource (by simp [hmem])
            · intro nextTarget hmem
              exact HtargetMem nextTarget (by simp [hmem])
            · exact HvalidNext
            · exact Hle.trans (VEnv.addConst_le hadd)
            · exact Hadded
            · exact Hlisted

/-- The header-only side environment lists no present constant beyond those its source
environment already lists coherently: the restored headers list the lowered constructors,
which are absent there. -/
theorem ValidationHeaderEnvironment.listedOfLowering
    {result : Lean4Lean.ElimNestedInductive.Result} {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    (Hvalidation : ValidationHeaderEnvironment loweredEnv c.env
      (sourceTypes.map (fun type => type.name)) sourceTypes validationEnv)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv) :
    ListedConstructorsCoherent validationEnv := by
  have hsourceWF := Hc.checking.tr.map_wf
  have hsub : ∀ {name found}, c.env.find? name = some found →
      validationEnv.find? name = some found := by
    intro name found h
    rcases Hvalidation.headers.headersFreshExtension hsourceWF with ⟨_, Hfresh⟩
    exact Hfresh.preservesSourceFind hsourceWF h
  have Hlowered := Hprod.listedConstructors Hc
  intro familyName familyInfo hfamily name hname found hfound
  rcases Hvalidation.headers.headerFindCases hsourceWF hfamily with hold |
      ⟨indType, hmem, oldInfo, hlookup, hfamilyName, hfamilyInfo⟩
  · rcases Hheaders.sourcePresent familyName familyInfo hold name hname with ⟨old, hold'⟩
    rw [hsub hold'] at hfound
    cases hfound
    exact Hc.checking.listedConstructors familyName familyInfo hold name hname _ hold'
  · cases hfamilyInfo
    have hname' : name ∈ oldInfo.ctors := hname
    have hheaderName : oldInfo.name = indType.name := Hprod.find?_name hlookup
    rcases Hvalidation.headers.headerFindCases hsourceWF hfound with hfoundOld |
        ⟨indType', _, oldInfo', hlookup', hfoundName, hfoundInfo⟩
    · rcases Hlowered indType.name oldInfo hlookup name hname' found
          (Hprod.preservesBaseFind Hc hfoundOld) with ⟨info, rfl, hinduct, -⟩
      rcases Hc.checking.constructorOwners name info hfoundOld with ⟨owner, howner, -⟩
      have hfresh := Hvalidation.headers.headerFresh hsourceWF hmem hlookup
      rw [hheaderName, ← hinduct, howner] at hfresh
      cases hfresh
    · have hname'' : oldInfo'.name = indType'.name := Hprod.find?_name hlookup'
      rw [hfoundName, hname''] at hname'
      rcases Hlowered indType.name oldInfo hlookup indType'.name hname' _ hlookup' with
        ⟨_, hctor, -⟩
      cases hctor

/-- The executable header-only side environment used by nested auxiliary
validation models exactly the abstract source-header prefix selected by the
lowering queue. It is obtained from lowering, the ordinary run on the lowered
declaration, and its header installation; no restoration fact or nested
installation certificate is involved. -/
theorem ValidationHeaderEnvironment.validOfLowering
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (Hvalidation : ValidationHeaderEnvironment loweredEnv c.env
      (sourceTypes.map (fun type => type.name)) sourceTypes validationEnv)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    ∃ sourceEnvTypes,
      sourceVEnv.addConstVals
          ((loweredDecl.types.take sourceTypes.length).map
            VInductiveType.toVConstVal) = some sourceEnvTypes ∧
      CheckingEnv.Valid c.safety validationEnv sourceEnvTypes := by
  rcases Hlower.sourceHeaderPrefix R.core hempty with
    ⟨sourceEnvTypes, Hadded, Htranslations⟩
  refine ⟨sourceEnvTypes, Hadded, ?_⟩
  apply restoredHeaderValidationValidAux Hlower Hprod hempty hvisible
    Hvalidation.headers Htranslations
  · intro source hsource
    exact hsource
  · intro target htarget
    exact List.mem_of_mem_take htarget
  · have Hbase : CheckingEnv.Valid c.safety c.env sourceVEnv := by
      rw [← Hheaders.sourceContextVEnv]
      exact Hheaders.sourceContext.checking
    exact Hbase
  · exact VEnv.LE.rfl
  · exact Hadded
  · exact Hvalidation.listedOfLowering Hc Hprod

end VerifyInductive
end Lean4Lean
