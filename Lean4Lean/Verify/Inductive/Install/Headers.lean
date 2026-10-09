import Lean4Lean.Verify.Inductive.Header.Installation
import Lean4Lean.Verify.Inductive.Header.Declaration
import Lean4Lean.Verify.Inductive.Header.CheckedHeaders
import Lean4Lean.Verify.Inductive.Constructor.Translation
import Lean4Lean.Verify.Inductive.Install.LiteralNames

/-! Skeleton-free header installation: the installed header fold and the
constructor-type fold yield a `HeaderEnvironment` for the declaration they
synthesize, with the primitive-name and literal-name side conditions needed by
the positivity check. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A successfully installed skeleton-free family cannot use a
kernel-reserved primitive name. -/
theorem InstalledHeaders.familyNamesExcludePrimitive
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {nparams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    {Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList}
    {outEnv : Environment}
    (H : InstalledHeaders c Hc stats nparams indTypes numNested
      isUnsafe commonParams commonLevel Hsemantic outEnv)
    (hprimitive : Kernel.Environment.primitives.contains name) :
    name ∉ (Hsemantic.headerDecl isUnsafe).types.map (·.name) := by
  intro hmem
  have hvalue : name ∈ Hsemantic.headers.targets.map VConstVal.name := by
    rw [← Hsemantic.headerDecl_typeConstants]
    simpa [VInductDecl.typeConstants, VInductiveType.toVConstVal,
      Function.comp_def] using hmem
  have hentryValue : name ∈
      ((List.zip
        ((AddInductive.inductiveTypeInfos stats nparams indTypes numNested
          isUnsafe c.lparams).toList.map
            (fun info => ConstantInfo.inductInfo info))
        Hsemantic.headers.targets).map Prod.snd).map VConstVal.name := by
    rw [H.values]
    exact hvalue
  exact H.installed.valueNamesNonprimitive name hentryValue hprimitive

/-- Primitive support visible after skeleton-free header installation was
already present in the source model. -/
theorem InstalledHeaders.sourceContainsOfTargetContainsPrimitive
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {nparams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    {Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList}
    {outEnv : Environment}
    (H : InstalledHeaders c Hc stats nparams indTypes numNested
      isUnsafe commonParams commonLevel Hsemantic outEnv)
    (hprimitive : Kernel.Environment.primitives.contains name)
    (htarget : H.context.venv.contains name) : Hc.venv.contains name := by
  rw [H.contextVEnv] at htarget
  exact H.installed.sourceContainsOfTargetContainsPrimitive
    hprimitive htarget

/-- Source freshness from the skeleton-free header installer excludes the
three literal expansion names not reserved by the kernel's primitive
table whenever those names are already present. -/
theorem InstalledHeaders.unreservedLiteralNamesDisjointOfSourceContains
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {nparams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    {Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList}
    {outEnv : Environment}
    (H : InstalledHeaders c Hc stats nparams indTypes numNested
      isUnsafe commonParams commonLevel Hsemantic outEnv)
    (hpresent : ∀ name ∈
      checkPositivityStep.unreservedLiteralConstructorNames,
      Hc.venv.contains name) :
    checkPositivityStep.UnreservedLiteralConstructorNamesDisjoint
      ((Hsemantic.headerDecl isUnsafe).types.map (·.name)) := by
  have hfresh := (VEnv.addConstVals_names_fresh H.installed.abstract).2
  intro name hname
  have hnotMem :
      name ∉ (Hsemantic.headerDecl isUnsafe).types.map (·.name) := by
    intro hmem
    rcases hpresent name hname with ⟨ci, hlookup⟩
    have hvalue : ∃ value ∈ Hsemantic.headers.targets,
        value.name = name := by
      have hconstant : ∃ value ∈
          (Hsemantic.headerDecl isUnsafe).typeConstants,
          value.name = name := by
        rcases List.mem_map.mp hmem with ⟨type, htype, htypeName⟩
        exact ⟨type.toVConstVal, List.mem_map.mpr ⟨type, htype, rfl⟩,
          by simpa using htypeName⟩
      simpa using hconstant
    rcases hvalue with ⟨value, hvalue, hvalueName⟩
    have hentryValue : value ∈
        (List.zip
          ((AddInductive.inductiveTypeInfos stats nparams indTypes numNested
            isUnsafe c.lparams).toList.map
              (fun info => ConstantInfo.inductInfo info))
          Hsemantic.headers.targets).map Prod.snd := by
      rw [H.values]
      exact hvalue
    have habsent := hfresh value hentryValue
    rw [hvalueName, hlookup] at habsent
    contradiction
  simpa using hnotMem

/-- The installed header result itself supplies positivity's
environment-indexed literal side condition; no caller disjointness premise
is needed. -/
theorem InstalledHeaders.checkedAvailableLiteralDisjoint
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {nparams depth : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    {Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList}
    {outEnv : Environment}
    (H : InstalledHeaders c Hc stats nparams indTypes numNested
      isUnsafe commonParams commonLevel Hsemantic outEnv)
    (Hmaterialized : checkInductiveTypes.loopInd.HeaderStatsWF
      Hc.venv c.lparams Hc.mlctx.vlctx stats
        (Hsemantic.headerDecl isUnsafe) depth) :
    checkPositivityStep.AvailableLiteralDisjoint
      H.context.venv stats.indConsts := by
  have hle : Hc.venv ≤ H.context.venv := by
    rw [H.contextVEnv]
    exact H.installed.le
  let Hmono := Hmaterialized.mono hle
  have hscope : Hc.mlctx.vlctx = H.context.mlctx.vlctx :=
    congrArg TypeChecker.MLCtx.vlctx H.contextMLCtx.symm
  let Hmaterialized' := Hmono.retargetScope hscope
  intro literal havailable
  cases literal with
  | natVal n =>
      exact Hmaterialized'.natLiteralDisjoint
        (H.familyNamesExcludePrimitive (by
          simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList]))
        (H.familyNamesExcludePrimitive (by
          simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])) n
  | strVal s =>
      have hsourceString : Hc.venv.contains ``String.ofList :=
        H.sourceContainsOfTargetContainsPrimitive (by
          simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
          havailable.2
      have hunreserved : ∀ name ∈
          checkPositivityStep.unreservedLiteralConstructorNames,
          Hc.venv.contains name :=
        unreservedLiteralConstructorsOfStringOfList
          Hc.checking.hasPrimitives Hc.checking.tr.wf hsourceString
      have hdisjoint :=
        H.unreservedLiteralNamesDisjointOfSourceContains hunreserved
      have hliteral : checkPositivityStep.LiteralConstructorNamesDisjoint
          ((Hsemantic.headerDecl isUnsafe).types.map (·.name)) := by
        intro name hname
        simp only [checkPositivityStep.literalConstructorNames,
          List.mem_cons, List.not_mem_nil, or_false] at hname
        rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · simpa using H.familyNamesExcludePrimitive (by
            simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
        · simpa using H.familyNamesExcludePrimitive (by
            simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
        · simpa using H.familyNamesExcludePrimitive (by
            simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
        · exact hdisjoint ``Char (by
            simp [checkPositivityStep.unreservedLiteralConstructorNames])
        · exact hdisjoint ``List.nil (by
            simp [checkPositivityStep.unreservedLiteralConstructorNames])
        · exact hdisjoint ``List.cons (by
            simp [checkPositivityStep.unreservedLiteralConstructorNames])
        · simpa using H.familyNamesExcludePrimitive (by
            simp [Kernel.Environment.primitives, NameSet.contains, NameSet.ofList])
      exact Hmaterialized'.literalDisjoint hliteral (.strVal s)

/-- Package the installed header fold and the constructor target assembly as a
`HeaderEnvironment`.  The declaration,
translation and header certificate are all synthesized; the remaining inputs
are exactly the executable statistics and scope invariants retained by the
outer header fold. -/
def HeaderDeclaration.toHeaderEnvironment
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth nparams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    {Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList}
    {outEnv : Environment}
    (Hinstalled : InstalledHeaders c Hc stats nparams indTypes
      numNested isUnsafe commonParams commonLevel Hsemantic outEnv)
    (H : HeaderDeclaration Hc.venv Hinstalled.context.venv
      c.lparams nparams indTypes.toList isUnsafe commonParams commonLevel
      Hsemantic)
    (hlevels : stats.levels.length = c.lparams.length)
    (hlevelParams : stats.levels = c.lparams.map .param)
    (hindices : stats.nindices.toList = H.metadata.map Prod.fst)
    (hconsts : stats.indConsts =
      (indTypes.toList.map fun source =>
        .const source.name stats.levels).toArray)
    (hparams : stats.params.size = nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc commonParams depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (hnotzero : stats.isNotZero = stats.resultLevel.isNeverZero) :
    HeaderEnvironment c stats H.decl nparams isUnsafe depth Hc.venv
      indTypes outEnv := by
  let infos := AddInductive.inductiveTypeInfos stats nparams indTypes
    numNested isUnsafe c.lparams
  let entries : List (ConstantInfo × VConstVal) :=
    List.zip
      (infos.toList.map fun info => .inductInfo info)
      Hsemantic.headers.targets
  have hmetadataLength : H.metadata.length = indTypes.toList.length := by
    calc
      H.metadata.length = H.skeleton.types.length :=
        VInductDeclSkeleton.withMetadata_length H.checked
      _ = H.decl.types.length :=
        (VInductDeclSkeleton.withMetadata_fields H.checked).2.2.2.symm
      _ = indTypes.toList.length :=
        (List.Forall₂.length_eq H.translation.types).symm
  have hindicesSize : stats.nindices.size = indTypes.size := by
    calc
      stats.nindices.size = stats.nindices.toList.length := by simp
      _ = (H.metadata.map Prod.fst).length :=
        congrArg List.length hindices
      _ = H.metadata.length := by simp
      _ = indTypes.toList.length := hmetadataLength
      _ = indTypes.size := by simp
  have hsourceLength : indTypes.toList.length =
      Hsemantic.headers.targets.length :=
    List.Forall₂.length_eq
      Hsemantic.headers.translations
  have hinfosLength : infos.toList.length =
      Hsemantic.headers.targets.length := by
    calc
      infos.toList.length = indTypes.size := by
        simp [infos, AddInductive.inductiveTypeInfos, hindicesSize]
      _ = indTypes.toList.length := by simp
      _ = Hsemantic.headers.targets.length := hsourceLength
  have hentriesFst : entries.map Prod.fst =
      infos.toList.map (fun info => ConstantInfo.inductInfo info) := by
    apply List.map_fst_zip
    simpa using Nat.le_of_eq hinfosLength
  have hentriesSnd : entries.map Prod.snd =
      Hsemantic.headers.targets := by
    apply List.map_snd_zip
    simpa using Nat.le_of_eq hinfosLength.symm
  let sourceMaterialized :=
    H.checkedResult hlevels hlevelParams
      hindices hconsts hparams Hcache Hsuffix Hambient hcommon hnotzero
  have hsourceHeaders : sourceMaterialized.headers = H.headers := by
    change H.formations.complete H.checked = H.headers
    exact H.headers_eq.symm
  have hle : Hc.venv ≤ Hinstalled.context.venv := by
    rw [Hinstalled.contextVEnv]
    exact Hinstalled.installed.le
  let materializedMono := sourceMaterialized.mono hle
  have hscope : Hc.mlctx.vlctx = Hinstalled.context.mlctx.vlctx :=
    congrArg TypeChecker.MLCtx.vlctx Hinstalled.contextMLCtx.symm
  let materialized := materializedMono.retargetScope hscope
  exact {
    entries := entries
    infos := ⟨numNested, by simpa [infos] using hentriesFst⟩
    sourceAligned := ⟨numNested, by
      change InductiveHeaderEntries infos.toList entries
      exact InductiveHeaderEntries.ofZip hinfosLength⟩
    values := hentriesSnd.trans H.typeConstants.symm
    context := Hinstalled.context
    headers := H.headers
    translation := H.translation
    installed := by
      simpa only [entries, infos, Hinstalled.contextVEnv] using
        Hinstalled.installed
    sourceContext := Hc
    sourcePresent := Hinstalled.sourcePresent
    sourceContextVEnv := rfl
    sourceStatsWF := sourceMaterialized
    sourceHeaderParams := congrArg (fun headers => headers.params) hsourceHeaders
    statsWF := materialized
    headerParams := by
      calc
        materialized.headers.params = materializedMono.headers.params := by
          simp [materialized]
        _ = sourceMaterialized.headers.params :=
          checkInductiveTypes.loopInd.HeaderStatsWF.mono_headers_params
            sourceMaterialized hle
        _ = H.headers.params := congrArg (fun headers => headers.params)
          hsourceHeaders
    parameterScopeEq := by
      calc
        materialized.parameterScope = materializedMono.parameterScope := by
          simp [materialized]
        _ = sourceMaterialized.parameterScope := by
          simp [materializedMono] }

/-- Execute the header installation and constructor-type fold of the
executable, then return the `HeaderEnvironment` of the declaration those
checks themselves synthesize.  Unlike `declareInductiveTypes.headersWF`, the
declaration is not chosen in advance. -/
theorem AddInductive.declareInductiveTypes.constructorsWF
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth nparams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    (Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList)
    (hlevels : stats.levels.length = c.lparams.length)
    (hlevelParams : stats.levels = c.lparams.map .param)
    (hindicesSize : stats.nindices.size = indTypes.size)
    (hindices : stats.nindices.toList = Hsemantic.metadata.map Prod.fst)
    (hconsts : stats.indConsts =
      (indTypes.toList.map fun source =>
        .const source.name stats.levels).toArray)
    (hparams : stats.params.size = nparams)
    (hcommonParams : commonParams.length = nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc commonParams depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (hnotzero : stats.isNotZero = stats.resultLevel.isNeverZero)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : c.allowPrimitive = true → ∀ info ∈
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
        isUnsafe c.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlparams : c.lparams.Nodup)
    (hpresent : ListedConstructorsPresent c.env) :
    (AddInductive.declareInductiveTypes stats nparams indTypes numNested
      isUnsafe c).WF fun headerEnv => headerEnv.constants.WF ∧
        (ConstructorNamesAbsent indTypes headerEnv →
        (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0
          { headerCheckContext c stats with env := headerEnv }).WF fun _ =>
            ∃ decl, Nonempty (HeaderEnvironment c stats decl nparams
              isUnsafe depth Hc.venv indTypes headerEnv)) := by
  let HheaderMaterialized := Hsemantic.checkedResult
    (isUnsafe := isUnsafe) hlevels hlevelParams hindices hconsts hparams
      hcommonParams Hcache Hsuffix Hambient hcommon hnotzero
  have hheaderParams : HheaderMaterialized.headers.params =
      commonParams := by
    simp [HheaderMaterialized,
      checkInductiveTypes.loopType.CheckedHeaders.checkedResult,
      checkInductiveTypes.loopType.CheckedHeaders.headerCertificate]
  have Hdeclare :=
    AddInductive.declareInductiveTypes.headersWF Hc Hsemantic
      hindicesSize hvisible hnprim hpresent
  exact Hdeclare.mono fun headerEnv ⟨hheaderWF, Hinstalled⟩ => by
    refine ⟨hheaderWF, fun habsent => ?_⟩
    rcases Hinstalled habsent with ⟨Hinstalled⟩
    have htypesAdded : Hc.venv.addConstVals
        (Hsemantic.headerDecl isUnsafe).typeConstants =
          some Hinstalled.context.venv := by
      simpa only [Hinstalled.contextVEnv] using Hinstalled.typesAdded
    have hlitInstalled : checkPositivityStep.AvailableLiteralDisjoint
        Hinstalled.context.venv stats.indConsts :=
      Hinstalled.checkedAvailableLiteralDisjoint HheaderMaterialized
    have hjL : depth ≤ Hinstalled.context.mlctx.length := by
      rw [Hinstalled.contextMLCtx]; exact Hsuffix.depth_le
    have hdropL : Hinstalled.context.mlctx.dropN depth hjL =
        Hc.mlctx.dropN depth Hsuffix.depth_le := by
      have key : ∀ (m m' : TypeChecker.MLCtx) (_ : m = m') (h : depth ≤ m.length)
          (h' : depth ≤ m'.length), m.dropN depth h = m'.dropN depth h' := by
        intro m m' hm h h'; subst hm; rfl
      exact key _ _ Hinstalled.contextMLCtx _ _
    let HcL := Hinstalled.context.paramCheck stats stats.params.size depth hjL
      (by rw [hdropL]; exact Hsuffix.headerFVars)
    have hlitL : checkPositivityStep.AvailableLiteralDisjoint
        HcL.venv stats.indConsts := hlitInstalled
    have htypesAddedL : Hc.venv.addConstVals
        (Hsemantic.headerDecl isUnsafe).typeConstants = some HcL.venv :=
      htypesAdded
    have halignL : VLCtx.IsDefEq HcL.venv c.lparams.length
        HheaderMaterialized.parameterScope HcL.chk.vlctx := by
      have hchk : HcL.chk.vlctx = Hsuffix.parameterDecls := by
        change (Hinstalled.context.mlctx.dropN depth hjL).vlctx = _
        rw [hdropL]; exact Hsuffix.headerVLCtx
      have hwf := HcL.check.wf.tr.wf
      rw [hchk] at hwf
      rw [hchk]
      exact .refl HcL.checking.tr.wf hwf
    have Hconstructors :=
      checkConstructors.loopTypes.assemblesHeadersExact
        (c := headerCheckContext c stats) (Hc := Hsuffix.headerCheck)
        HcL Hinstalled.contextMLCtx htypesAddedL
        HheaderMaterialized hheaderParams halignL hcommonParams hconsume hlitL
    exact (Hconstructors hlparams).mono fun _ Hassembled => by
      rcases Hassembled with ⟨Hassembled⟩
      have hindicesAssembled : stats.nindices.toList =
          Hassembled.metadata.map Prod.fst := by
        rw [Hassembled.metadata_eq]
        exact hindices
      refine ⟨Hassembled.decl, ⟨?_⟩⟩
      exact Hassembled.toHeaderEnvironment Hinstalled hlevels hlevelParams
        hindicesAssembled hconsts hparams Hcache Hsuffix Hambient hcommon hnotzero

end VerifyInductive
end Lean4Lean
