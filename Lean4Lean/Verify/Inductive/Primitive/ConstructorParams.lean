import Lean4Lean.Verify.Inductive.Primitive.ConstructorCheck
import Lean4Lean.Verify.Inductive.Nested.Restoration.Translations
import Lean4Lean.Verify.Inductive.Install.Lookups
import Lean4Lean.Verify.Inductive.Rules.RuleTranslations
import Lean4Lean.Verify.Inductive.Constructor.LiteralDisjoint

/-!
# The primitive constructor check

The primitive constructor check `PrimitiveConstructorCheck`, established by the executable
constructor phase (`AddInductive.primitiveConstructorPhases.WF`), and the invariants of the
kernel environment that the shared recursor phase needs, derived from it: lookup of the
installed families (`PrimitiveConstructorCheck.inductInfosFromDecl`) and constructor-parameter
agreement (`PrimitiveConstructorCheck.constructorParameterAlignment`).  It embeds into the
shared checked formation and constructor check (`PrimitiveConstructorCheck.toCheckedFormation`,
`PrimitiveConstructorCheck.toConstructorCheck`).
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The primitive constructor check: the same semantic data needed by recursor
generation as the ordinary constructor check, with the atomic installation
kept separate.  The kernel-environment lookup (`PrimitiveConstructorCheck.inductInfosFromDecl`)
and constructor-parameter agreement (`PrimitiveConstructorCheck.constructorParameterAlignment`)
are derived from these fields, and `PrimitiveConstructorCheck.toCheckedFormation` turns it
into the shared checked formation without a valid header-only context. -/
structure PrimitiveConstructorCheck
    (H : PrimitiveHeaderEnvironment c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv)
    (outEnv : Environment) where
  checked : CheckedConstructorCertificate sourceEnv decl H.context.venv
    H.headers.params
  parameterPrefixes : ConstructorParameterPrefixes stats indTypes
  /-- The field classifications returned by the executable constructor check. -/
  classes : List (List (List Bool))
  constructorTails : ConstructorTails H.context.venv c.lparams
    H.statsWF.parameterScope stats decl indTypes classes
  ownerNormalForms : ConstructorOwnerNormalForms stats indTypes
  telescopes : SourceCtorsCertified H.context.venv c.lparams indTypes.toList
  declared : PrimitiveConstructorEnvironment H outEnv
  formation : FormationCertificate sourceEnv decl
  core : TrInductDeclCore sourceEnv c.lparams nparams indTypes.toList
    isUnsafe decl H.context.venv declared.venvCtors

/-- Select one constructor installed by the primitive atomic batch and recover
its family's kernel entry and constructor-parameter agreement
(`ConstructorParameterAlignmentAt`).  This is the primitive counterpart of
`OrdinaryConstructorCheck.installedConstructorCoherenceAt`; it never asserts a
valid header-only context. -/
theorem PrimitiveConstructorCheck.installedConstructorCoherenceAt
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : PrimitiveHeaderEnvironment c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    (R : PrimitiveConstructorCheck H outEnv)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length) :
    ∃ familyInfo : InductiveVal,
      ∃ hi : ctorIdx < familyInfo.ctors.length,
        familyInfo.name = indTypes[familyIdx].name ∧
        familyInfo.ctors = indTypes[familyIdx].ctors.map (fun ctor => ctor.name) ∧
        outEnv.find? familyInfo.name = some (.inductInfo familyInfo) ∧
        Nonempty (ConstructorParameterAlignmentAt
          outEnv R.declared.venvCtors familyInfo.name familyInfo ctorIdx hi) := by
  rcases H.sourceAligned with ⟨numNested, Haligned⟩
  let infos := AddInductive.inductiveTypeInfos stats nparams indTypes
    numNested isUnsafe c.lparams
  have hindicesSize : stats.nindices.size = indTypes.size := by
    calc
      stats.nindices.size = decl.types.length := by
        rw [Array.size_eq_length_toList, H.statsWF.indices,
          List.length_map]
      _ = indTypes.toList.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core).symm
      _ = indTypes.size := by simp
  have hinfosSize : infos.size = indTypes.size := by
    simp [infos, AddInductive.inductiveTypeInfos, hindicesSize]
  have hinfoIdx : familyIdx < infos.size := by simpa [hinfosSize] using hfamily
  let familyInfo := infos[familyIdx]
  have hfamilyInfoMem : familyInfo ∈ infos.toList := by
    apply Array.mem_toList_iff.mpr
    simp [familyInfo]
  have hfamilyName : familyInfo.name = indTypes[familyIdx].name := by
    simp [familyInfo, infos, AddInductive.inductiveTypeInfos]
  have hfamilyCtors : familyInfo.ctors =
      indTypes[familyIdx].ctors.map (fun ctor => ctor.name) := by
    simp [familyInfo, infos, AddInductive.inductiveTypeInfos]
  have hi : ctorIdx < familyInfo.ctors.length := by
    simpa [hfamilyCtors] using hctor
  rcases Haligned.findInfo hfamilyInfoMem with ⟨familyValue, hfamilyEntry⟩
  have hfamilyHeader :
      headerEnv.find? familyInfo.name = some (.inductInfo familyInfo) :=
    H.installed.findEntry H.sourceContext.checking.tr.map_wf hfamilyEntry
  have hfamilyLookup :
      outEnv.find? familyInfo.name = some (.inductInfo familyInfo) :=
    R.declared.installed.preservesSourceFind H.context.checking.map_wf
      hfamilyHeader
  let sourceFamily := indTypes[familyIdx]
  let sourceCtor := sourceFamily.ctors[ctorIdx]
  let ctorInfo := AddInductive.constructorInfo stats c.lparams isUnsafe
    sourceFamily ctorIdx sourceCtor
  rcases R.declared.sourceAligned.findAt
      (owner := sourceFamily) (List.getElem_mem hfamily)
      ctorIdx hctor with ⟨ctorValue, hctorEntry⟩
  have hctorLookupExact :
      outEnv.find? ctorInfo.name = some (.ctorInfo ctorInfo) :=
    R.declared.installed.findEntry H.context.checking.map_wf hctorEntry
  have hctorLookup :
      outEnv.find? familyInfo.ctors[ctorIdx] = some (.ctorInfo ctorInfo) := by
    simpa [ctorInfo, sourceCtor, sourceFamily, hfamilyCtors,
      AddInductive.constructorInfo] using hctorLookupExact
  have htargetFamily : familyIdx < decl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]
    simpa using hfamily
  have Htype := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt R.core
    familyIdx (by simpa using hfamily) htargetFamily
  have htargetCtor : ctorIdx < decl.types[familyIdx].ctors.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Htype]
    simpa [sourceFamily] using hctor
  have Hctor := Lean4Lean.VerifyInductive.TrInductiveType.ctorAt Htype
    ctorIdx (by simpa [sourceFamily] using hctor) htargetCtor
  have hfamilyTargetLookup : R.declared.venvCtors.constants familyInfo.name =
      some decl.types[familyIdx].toVConstant := by
    have hlookup : H.context.venv.constants decl.types[familyIdx].name =
        some decl.types[familyIdx].toVConstant := by
      apply VEnv.addConstVals_get R.core.typesAdded
      exact List.mem_map.mpr
        ⟨decl.types[familyIdx], List.getElem_mem htargetFamily, rfl⟩
    simpa [hfamilyName, Htype.header.name] using
      (VEnv.addConstVals_le R.core.ctorsAdded).constants hlookup
  have hctorTargetLookup : R.declared.venvCtors.constants
      familyInfo.ctors[ctorIdx] =
      some decl.types[familyIdx].ctors[ctorIdx].toVConstant := by
    have hlookup := VEnv.addConstVals_get R.core.ctorsAdded
      (ci := decl.types[familyIdx].ctors[ctorIdx]) (by
        simp only [VInductDecl.constructorConstants]
        apply List.mem_flatMap.mpr
        exact ⟨decl.types[familyIdx], List.getElem_mem htargetFamily,
          List.getElem_mem htargetCtor⟩)
    simpa [hfamilyCtors, sourceFamily, Hctor.name] using hlookup
  have hfinalWF : R.declared.venvCtors.WF := by
    rw [← R.declared.contextVEnv]
    exact R.declared.context.checking.wf
  have hparamsSize : stats.params.size = decl.nparams := by
    have hlength := List.Forall₂.length_eq
      H.statsWF.params
    simpa [VInductDecl.paramVars] using hlength
  let C : CtorInfoCoherentAt outEnv familyInfo.name familyInfo
      ctorIdx hi := {
    info := ctorInfo
    lookup := hctorLookup
    induct := by
      simp [ctorInfo, sourceFamily, AddInductive.constructorInfo, hfamilyName]
    cidx := by simp [ctorInfo, AddInductive.constructorInfo]
    numParams := by
      simp [ctorInfo, familyInfo, infos, AddInductive.inductiveTypeInfos,
        AddInductive.constructorInfo, hparamsSize, R.core.nparams]
    levelParams := by
      simp [ctorInfo, familyInfo, infos, AddInductive.inductiveTypeInfos,
        AddInductive.constructorInfo]
    isUnsafe := by
      simp [ctorInfo, familyInfo, infos, AddInductive.inductiveTypeInfos,
        AddInductive.constructorInfo] }
  refine ⟨familyInfo, hi, hfamilyName, hfamilyCtors, hfamilyLookup, ?_⟩
  apply ConstructorParameterAlignmentAt.ofShapes C hfinalWF
    decl.types[familyIdx] decl.types[familyIdx].ctors[ctorIdx]
    hfamilyTargetLookup hctorTargetLookup
  · exact Htype.header.uvars.trans R.core.uvars.symm
  · exact Hctor.uvars.trans R.core.uvars.symm
  · simp [familyInfo, infos, AddInductive.inductiveTypeInfos,
      R.core.uvars]
  · simp [familyInfo, infos, AddInductive.inductiveTypeInfos,
      R.core.nparams]
  · exact H.headers.typeShapes _ (List.getElem_mem htargetFamily)
  · exact R.checked.formation.ctorShape
      (List.getElem_mem htargetFamily) (List.getElem_mem htargetCtor)
  · exact H.installed.le.trans R.declared.installed.le
  · exact R.declared.installed.le

/-- The two atomic primitive installation stages identify every newly visible
inductive family of the kernel environment with its exact source declaration position. -/
theorem PrimitiveConstructorCheck.inductInfosFromDecl
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : PrimitiveHeaderEnvironment c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    (R : PrimitiveConstructorCheck H outEnv) :
    InductInfosFromDecl c.env.constants outEnv.constants decl := by
  intro familyName familyInfo hfamily
  have hsourceWF := H.sourceContext.checking.tr.map_wf
  have hheaderWF := H.context.checking.map_wf
  have houtWF := R.declared.installed.targetMapWF hheaderWF
  have hfamilyEnv : outEnv.find? familyName =
      some (.inductInfo familyInfo) := by
    rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?]
    exact hfamily
  rcases R.declared.installed.entryOrigin hheaderWF hfamilyEnv with
      hheader | hctorOrigin
  · rcases H.installed.entryOrigin hsourceWF hheader with hold | hnew
    · left
      rwa [Lean.Kernel.Environment.find?, hsourceWF.find?'_eq_find?] at hold
    · right
      rcases hnew with ⟨entry, hentry, hentryName, hentryValue⟩
      rcases H.sourceAligned with ⟨numNested, Haligned⟩
      rcases Haligned.originInfo hentry with ⟨info, hinfo, hentryInfo⟩
      have hinfoEq : familyInfo = info := by
        have heq : ConstantInfo.inductInfo familyInfo = .inductInfo info :=
          hentryValue.trans hentryInfo
        cases heq
        rfl
      subst info
      rcases List.mem_iff_getElem.mp hinfo with
        ⟨familyIdx, hfamilyInfo, hfamilyInfoEq⟩
      let infos := AddInductive.inductiveTypeInfos stats nparams indTypes
        numNested isUnsafe c.lparams
      have hindicesSize : stats.nindices.size = indTypes.size := by
        calc
          stats.nindices.size = decl.types.length := by
            rw [Array.size_eq_length_toList, H.statsWF.indices,
              List.length_map]
          _ = indTypes.toList.length :=
            (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
              R.core).symm
          _ = indTypes.size := by simp
      have hparamsSize : stats.params.size = decl.nparams := by
        have hlength := List.Forall₂.length_eq
          H.statsWF.params
        simpa [VInductDecl.paramVars] using hlength
      have hinfosSize : infos.size = indTypes.size := by
        simp [infos, AddInductive.inductiveTypeInfos, hindicesSize]
      have hfamilyIdx : familyIdx < indTypes.size := by
        have : familyIdx < infos.toList.length := by
          simpa [infos] using hfamilyInfo
        simpa [hinfosSize] using this
      have htargetIdx : familyIdx < decl.types.length := by
        rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]
        simpa using hfamilyIdx
      have Htype := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt R.core
        familyIdx (by simpa using hfamilyIdx) htargetIdx
      have hfamilyInfoExact : familyInfo = infos[familyIdx] := by
        rw [← hfamilyInfoEq]
        exact Array.getElem_toList (by simpa [infos] using hfamilyInfo)
      have hfamilyNameEq : familyName = familyInfo.name := by
        have hentryFamilyName : entry.1.name = familyInfo.name := by
          have heq := congrArg ConstantInfo.name hentryValue
          dsimp only [ConstantInfo.name] at heq
          exact heq.symm
        exact hentryName.trans hentryFamilyName
      refine ⟨familyIdx, hfamilyNameEq, ⟨{
        familyIdx_lt := htargetIdx
        name := ?_
        lookup := by simpa [← hfamilyNameEq] using hfamily
        all := ?_
        levelParams := ?_
        numParams := ?_
        numIndices := ?_
        constructors := ?_
        isUnsafe := ?_
        constructor := ?_ }⟩⟩
      · calc
          familyInfo.name = indTypes[familyIdx].name := by
            simp [hfamilyInfoExact, infos,
              AddInductive.inductiveTypeInfos]
          _ = decl.types[familyIdx].name := Htype.header.name.symm
      · calc
          familyInfo.all = indTypes.toList.map (fun type => type.name) := by
            simp [hfamilyInfoExact, infos,
              AddInductive.inductiveTypeInfos]
          _ = decl.types.map (fun type => type.name) := by
            apply List.ext_getElem
            · simpa using
                Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
            · intro i hsource htarget
              simp only [List.getElem_map]
              exact (Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt R.core
                i (by simpa using hsource) (by simpa using htarget)).header.name.symm
      · simp [hfamilyInfoExact, infos,
          AddInductive.inductiveTypeInfos, R.core.uvars]
      · simp [hfamilyInfoExact, infos,
          AddInductive.inductiveTypeInfos, R.core.nparams]
      · have hindex : stats.nindices[familyIdx]? =
            some decl.types[familyIdx].numIndices := by
          rw [← Array.getElem?_toList, H.statsWF.indices]
          simp [htargetIdx]
        have hstats : familyIdx < stats.nindices.size := by
          simpa [hindicesSize] using hfamilyIdx
        have hindexExact : stats.nindices[familyIdx] =
            decl.types[familyIdx].numIndices := by
          rw [Array.getElem?_eq_getElem hstats] at hindex
          exact Option.some.inj hindex
        calc
          familyInfo.numIndices = stats.nindices[familyIdx] := by
            simp [hfamilyInfoExact, infos,
              AddInductive.inductiveTypeInfos]
          _ = decl.types[familyIdx].numIndices := hindexExact
      · simpa [hfamilyInfoExact, infos,
          AddInductive.inductiveTypeInfos] using
          Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Htype
      · simp [hfamilyInfoExact, infos,
          AddInductive.inductiveTypeInfos, R.core.isUnsafe]
      · intro ctorIdx htargetCtor
        have hsourceCtor : ctorIdx < indTypes[familyIdx].ctors.length := by
          have hbound := htargetCtor
          rw [← Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Htype] at hbound
          simpa using hbound
        have Hctor := Lean4Lean.VerifyInductive.TrInductiveType.ctorAt Htype
          ctorIdx hsourceCtor htargetCtor
        rcases R.installedConstructorCoherenceAt familyIdx hfamilyIdx
            ctorIdx hsourceCtor with
          ⟨installedInfo, hi, hinstalledName, hinstalledCtors,
            hinstalledLookup, ⟨C⟩⟩
        have hsourceName : familyName = indTypes[familyIdx].name := by
          calc
            familyName = familyInfo.name := hfamilyNameEq
            _ = indTypes[familyIdx].name := by
              simp [hfamilyInfoExact, infos,
                AddInductive.inductiveTypeInfos]
        have hsameLookup : outEnv.find? familyName =
            some (.inductInfo installedInfo) := by
          simpa [hinstalledName, hsourceName] using hinstalledLookup
        have hinstalledEq : installedInfo = familyInfo := by
          rw [hfamilyEnv] at hsameLookup
          cases Option.some.inj hsameLookup
          rfl
        subst installedInfo
        have hctorLookup : outEnv.constants.find? familyInfo.ctors[ctorIdx] =
            some (.ctorInfo C.info) := by
          have hlookup := C.lookup
          rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at hlookup
          exact hlookup
        let sourceFamily := indTypes[familyIdx]
        let sourceCtor := sourceFamily.ctors[ctorIdx]
        let ctorInfo := AddInductive.constructorInfo stats c.lparams isUnsafe
          sourceFamily ctorIdx sourceCtor
        rcases R.declared.sourceAligned.findAt
            (owner := sourceFamily) (List.getElem_mem hfamilyIdx)
            ctorIdx (by simpa [sourceFamily] using hsourceCtor) with
          ⟨ctorValue, hctorEntry⟩
        have hctorLookupExact :
            outEnv.find? ctorInfo.name = some (.ctorInfo ctorInfo) :=
          R.declared.installed.findEntry H.context.checking.map_wf hctorEntry
        have hctorNameExact :
            familyInfo.ctors[ctorIdx] = ctorInfo.name := by
          simp [ctorInfo, sourceCtor, sourceFamily, hinstalledCtors,
            AddInductive.constructorInfo]
        have hctorLookupExact' :
            outEnv.constants.find? familyInfo.ctors[ctorIdx] =
              some (.ctorInfo ctorInfo) := by
          have hlookup := hctorLookupExact
          rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at hlookup
          simpa [hctorNameExact] using hlookup
        have hctorInfoExact : C.info = ctorInfo := by
          have heq : (ConstantInfo.ctorInfo C.info) = .ctorInfo ctorInfo := by
            exact Option.some.inj (hctorLookup.symm.trans hctorLookupExact')
          exact ConstantInfo.ctorInfo.inj heq
        exact ⟨{
          familyIdx_lt := htargetIdx
          ctorIdx_lt := htargetCtor
          familyInfo_ctorIdx_lt := hi
          info := C.info
          name := by
            calc
              familyInfo.ctors[ctorIdx] =
                  indTypes[familyIdx].ctors[ctorIdx].name := by
                simp [hinstalledCtors]
              _ = decl.types[familyIdx].ctors[ctorIdx].name :=
                Hctor.name.symm
          lookup := hctorLookup
          induct := by simpa [hfamilyNameEq] using C.induct
          cidx := C.cidx
          numParams := by
            calc
              C.info.numParams = familyInfo.numParams := C.numParams
              _ = decl.nparams := by
                simp [hfamilyInfoExact, infos,
                  AddInductive.inductiveTypeInfos, R.core.nparams]
          numFields := by
            rw [hctorInfoExact]
            calc
              ctorInfo.numFields =
                  AddInductive.constructorArity sourceCtor.type -
                    stats.params.size :=
                AddInductive.constructorInfo_numFields stats c.lparams
                  isUnsafe sourceFamily ctorIdx sourceCtor
              _ = AddInductive.constructorArity ctorInfo.type -
                    decl.nparams := by
                rw [hparamsSize]
                rfl
          numFields_forallArity := by
            rw [hctorInfoExact]
            rcases R.parameterPrefixes.spines familyIdx hfamilyIdx ctorIdx
              hsourceCtor with ⟨k, hspine⟩
            calc
              ctorInfo.numFields =
                  AddInductive.constructorArity sourceCtor.type -
                    stats.params.size :=
                AddInductive.constructorInfo_numFields stats c.lparams
                  isUnsafe sourceFamily ctorIdx sourceCtor
              _ = k - decl.nparams := by
                rw [hspine.constructorArity, hparamsSize]
              _ = (decl.types[familyIdx].ctors[ctorIdx]).type.forallArity -
                    decl.nparams := by
                rw [checkPositivityStep.TrExprS.forallArity_of_spine hspine
                  Hctor.type]
          levelParamsExact := C.levelParams
          levelParams := by
            calc
              C.info.levelParams.length = familyInfo.levelParams.length :=
                congrArg List.length C.levelParams
              _ = decl.uvars := by
                simp [hfamilyInfoExact, infos,
                  AddInductive.inductiveTypeInfos, R.core.uvars]
          isUnsafe := by
            calc
              C.info.isUnsafe = familyInfo.isUnsafe := C.isUnsafe
              _ = decl.isUnsafe := by
                simp [hfamilyInfoExact, infos,
                  AddInductive.inductiveTypeInfos, R.core.isUnsafe] }⟩
  · rcases hctorOrigin with ⟨entry, hentry, _hname, hvalue⟩
    exact False.elim (R.declared.nonInductive entry hentry familyInfo
      hvalue.symm)

/-- Atomic primitive header and constructor installation preserves
constructor-parameter agreement (`ConstructorParameterAlignment`) for the base families and
establishes it positionally for the newly installed canonical family. -/
theorem PrimitiveConstructorCheck.constructorParameterAlignment
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : PrimitiveHeaderEnvironment c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    (R : PrimitiveConstructorCheck H outEnv)
    (Hsource : ConstructorParameterAlignment
      safety c.env sourceEnv) :
    ConstructorParameterAlignment
      safety outEnv R.declared.venvCtors := by
  intro familyName familyInfo hfamily hvisible ctorIdx hctor
  rcases R.declared.installed.entryOrigin H.context.checking.map_wf
      hfamily with hheader | hctorOrigin
  · rcases H.installed.entryOrigin H.sourceContext.checking.tr.map_wf
        hheader with hold | hnew
    · rcases Hsource familyName familyInfo hold hvisible ctorIdx hctor with ⟨C⟩
      have hctorHeader := H.installed.preservesSourceFind
        H.sourceContext.checking.tr.map_wf C.lookup
      have hctorFinal := R.declared.installed.preservesSourceFind
        H.context.checking.map_wf hctorHeader
      exact ⟨C.rebaseKernel hctorFinal
        (H.installed.le.trans R.declared.installed.le)⟩
    · rcases hnew with ⟨entry, hentry, hentryName, hentryValue⟩
      rcases H.sourceAligned with ⟨numNested, Haligned⟩
      rcases Haligned.originInfo hentry with ⟨info, hinfo, hentryInfo⟩
      have hinfoEq : familyInfo = info := by
        have heq : ConstantInfo.inductInfo familyInfo = .inductInfo info :=
          hentryValue.trans hentryInfo
        cases heq
        rfl
      subst info
      rcases List.mem_iff_getElem.mp hinfo with
        ⟨familyIdx, hfamilyInfo, hfamilyInfoEq⟩
      let infos := AddInductive.inductiveTypeInfos stats nparams indTypes
        numNested isUnsafe c.lparams
      have hindicesSize : stats.nindices.size = indTypes.size := by
        calc
          stats.nindices.size = decl.types.length := by
            rw [Array.size_eq_length_toList, H.statsWF.indices,
              List.length_map]
          _ = indTypes.toList.length :=
            (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
              R.core).symm
          _ = indTypes.size := by simp
      have hinfosSize : infos.size = indTypes.size := by
        simp [infos, AddInductive.inductiveTypeInfos, hindicesSize]
      have hfamilyIdx : familyIdx < indTypes.size := by
        have : familyIdx < infos.toList.length := by
          simpa [infos] using hfamilyInfo
        simpa [hinfosSize] using this
      have hfamilyInfoExact : familyInfo = infos[familyIdx] := by
        rw [← hfamilyInfoEq]
        exact Array.getElem_toList (by simpa [infos] using hfamilyInfo)
      have hsourceCtor : ctorIdx < indTypes[familyIdx].ctors.length := by
        simpa [hfamilyInfoExact, infos, AddInductive.inductiveTypeInfos]
          using hctor
      rcases R.installedConstructorCoherenceAt familyIdx hfamilyIdx
          ctorIdx hsourceCtor with
        ⟨installedInfo, hi, hinstalledName, hinstalledCtors,
          hinstalledLookup, ⟨C⟩⟩
      have hentryFamilyName : entry.1.name = familyInfo.name := by
        have heq := congrArg ConstantInfo.name hentryValue
        dsimp only [ConstantInfo.name] at heq
        exact heq.symm
      have hsourceName : familyName = indTypes[familyIdx].name := by
        calc
          familyName = entry.1.name := hentryName
          _ = familyInfo.name := hentryFamilyName
          _ = indTypes[familyIdx].name := by
            simp [hfamilyInfoExact, infos,
              AddInductive.inductiveTypeInfos]
      have hfamilyNameEq : familyName = familyInfo.name := by
        exact hentryName.trans hentryFamilyName
      have hsameLookup : outEnv.find? familyName =
          some (.inductInfo installedInfo) := by
        simpa [hinstalledName, hsourceName] using hinstalledLookup
      have hinstalledEq : installedInfo = familyInfo := by
        rw [hfamily] at hsameLookup
        cases Option.some.inj hsameLookup
        rfl
      subst installedInfo
      rw [hfamilyNameEq]
      exact ⟨by simpa only [Subsingleton.elim hi hctor] using C⟩
  · rcases hctorOrigin with ⟨entry, hentry, _hname, hvalue⟩
    exact False.elim (R.declared.nonInductive entry hentry familyInfo
      hvalue.symm)

/-- The successful executable check is followed by the exact atomic
constructor fold.  Validity is regained only at the end of the fold, once the
Bool/Nat batch is complete. -/
theorem AddInductive.primitiveConstructorPhases.WF
    (H : PrimitiveHeaderEnvironment c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      isUnsafe)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    ((AddInductive.checkConstructors indTypes stats isUnsafe >>= fun positivity =>
      AddInductive.declareConstructors stats indTypes isUnsafe >>= fun ctorEnv =>
        pure (ctorEnv, positivity))
      { c with env := headerEnv }).WF fun out =>
        ∃ R : PrimitiveConstructorCheck H out.1, R.classes = out.2 := by
  exact (AddInductive.checkConstructors.primitiveCoreWF H Hshape).bind
    fun positivity Hchecked =>
      (AddInductive.declareConstructors.primitiveWF H Hshape
        Hchecked.1.checked hvisible).bind fun outEnv Hdeclared => Except.WF.pure <| by
          rcases Hdeclared with ⟨Hdeclared, _⟩
          let Hformation : FormationCertificate sourceEnv decl := {
            headers := H.headers
            envTypes := H.context.venv
            typesInstalled := H.translation.typesAdded
            constructorParameters := Hchecked.1.parameterShapes
              H.context.checking.wf H.translation.types
              (H.statsWF.parameterEmbedding.scopeWF H.context.checking.wf)
              (checkPositivityStep.ValidAppStatsWF.ofHeaderStatsScoped
                H.statsWF).params_size
              H.statsWF.uvars.symm (by
                rw [← H.headerParams]
                exact H.statsWF.paramsContext)
            constructors := Hchecked.1.checked.formation
            rawShapes := Hchecked.1.rawShapes H.context.checking.wf
              H.translation.types
              (H.statsWF.parameterEmbedding.scopeWF H.context.checking.wf)
              (checkPositivityStep.ValidAppStatsWF.ofHeaderStatsScoped
                H.statsWF).params_size }
          exact ⟨{
            checked := Hchecked.1.checked
            parameterPrefixes := Hchecked.1.parameterPrefixes
            classes := positivity
            constructorTails := Hchecked.1.constructorTails
            ownerNormalForms := Hchecked.2
            telescopes := SourceCtorsCertified.ofPrimitiveShape Hshape
              (Hchecked.1.checked.translated H.translation)
            declared := Hdeclared
            formation := Hformation
            core := Lean4Lean.VerifyInductive.TrInductDeclCore.ofPhases
              H.translation Hdeclared.translation }, rfl⟩

/-- The checked formation of a primitive formation run. -/
noncomputable def PrimitiveConstructorCheck.toCheckedFormation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv : Environment}
    {H : PrimitiveHeaderEnvironment c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    (R : PrimitiveConstructorCheck H ctorEnv) :
    CheckedFormation c stats decl nparams isUnsafe depth sourceEnv indTypes where
  headerVEnv := H.context.venv
  sourceContext := H.sourceContext
  sourceContextVEnv := H.sourceContextVEnv
  sourceStatsWF := H.sourceStatsWF
  headerMLCtx := H.context.mlctx
  headers := H.headers
  params := H.headers.params
  headerParams := rfl
  sourceHeaderParams := H.sourceHeaderParams
  parameterScope := H.statsWF.parameterScope
  sourceParameterScope := H.parameterScopeEq.symm
  statsWF := H.statsWF
  checkedParams := H.headerParams
  checkedParameterScope := rfl
  classes := R.classes
  constructorTails := R.constructorTails
  ctorVEnv := R.declared.venvCtors
  formation := R.formation
  core := R.core

/-- The primitive constructor context, with the declaration's case eliminators and
projections. -/
theorem PrimitiveConstructorCheck.projectedChecking
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv : Environment}
    {H : PrimitiveHeaderEnvironment c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    (R : PrimitiveConstructorCheck H ctorEnv) :
    CheckingEnv.Valid c.safety ctorEnv
      ((R.declared.venvCtors.addEliminators R.toCheckedFormation.caseEliminators).addProjections
        decl.projectionEntries) := by
  let B := R.toCheckedFormation
  have hsourceMapWF := H.sourceContext.checking.tr.map_wf
  have Hcombined := H.installed.append R.declared.installed
  have hcore' := (R.declared.validCore.addEliminators B.casesWF).addProjections B.projectedWF
  have hle : R.declared.venvCtors ≤
      (R.declared.venvCtors.addEliminators B.caseEliminators).addProjections
        decl.projectionEntries := VEnv.addEliminators_addProjections_le
  have hsourceBlocks : InstalledBlocks c.safety c.env sourceEnv .headers := by
    rw [← H.sourceContextVEnv]; exact H.sourceContext.checking.blocks
  have htelsCtors : CtorTelescopes c.safety ctorEnv R.declared.venvCtors := by
    rw [← R.declared.contextVEnv]; exact R.declared.context.ctorTelescopes
  obtain ⟨numNested, Hheaders⟩ := H.sourceAligned
  refine hcore'.toValid (hsourceBlocks.addCtorStage H.sourcePresent hsourceMapWF hcore'.tr
    (fun h => Hcombined.preservesSourceFind hsourceMapWF h) (Hcombined.le.trans hle)
    R.inductInfosFromDecl ?_ ?_ R.declared.owners [] ?_ (by simp) (by simp) (by simp)
    B.caseEliminators ?_ ?_ (htelsCtors.mono hle))
    (R.declared.equationHeads.mono id fun df hdf => by simpa using hdf)
    (fun hq => (R.declared.quot hq).extend id hle
      (R.declared.equationHeads.mono id fun df hdf => by simpa using hdf))
  · intro T hT
    have hmem : T.toVConstVal ∈ H.entries.map Prod.snd := by
      rw [H.values]; exact List.mem_map_of_mem hT
    obtain ⟨⟨ci, val⟩, he, hval⟩ := List.mem_map.mp hmem
    obtain ⟨info, -, hci⟩ := Hheaders.originInfo he
    simp only at hci hval
    subst hci
    have hname : info.name = T.name := by
      have := H.installed.entryNames he
      simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at this
      rw [this, hval]
    refine ⟨info, ?_, ?_⟩
    · rw [← hname]; exact Hcombined.findEntry hsourceMapWF (List.mem_append_left _ he)
    · rw [← hname]; exact H.installed.entryFresh hsourceMapWF he
  · have := VEnv.addConstVals_names_nodup R.core.typesAdded
    simpa [VInductDecl.typeConstants, Function.comp_def] using this
  · intro n r hf hnone
    rcases Hcombined.entryOrigin hsourceMapWF hf with hold | ⟨entry, hentry, -, hvalue⟩
    · rw [hold] at hnone; cases hnone
    · rcases List.mem_append.mp hentry with hheader | hctor
      · obtain ⟨info, -, hinfo⟩ := Hheaders.originInfo hheader
        rw [hinfo] at hvalue; cases hvalue
      · obtain ⟨info, hinfo⟩ := R.declared.infos entry hctor
        rw [hinfo] at hvalue; cases hvalue
  · exact {
      typeUvars := by
        intro T hT
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hT
        have hsource : i < indTypes.toList.length := by
          rw [Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]; exact hi
        exact (Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt R.core i hsource
          hi).header.uvars.trans R.core.uvars.symm
      constructorUvars := Lean4Lean.VerifyInductive.TrInductDeclCore.constructorUvars R.core
      family := fun i hi => ((VEnv.addConstVals_le R.core.ctorsAdded).trans hle).constants
        (VEnv.addConstVals_get R.core.typesAdded
          (List.mem_map.mpr ⟨decl.types[i], List.getElem_mem hi, rfl⟩))
      ctor := fun i k hi hk => hle.constants
        (VEnv.addConstVals_get R.core.ctorsAdded (by
          simp only [VInductDecl.constructorConstants, List.mem_flatMap]
          exact ⟨_, List.getElem_mem hi, List.getElem_mem hk⟩))
      projections := fun e he =>
        VEnv.addProjections_iff.mpr (.inl ⟨e, he, rfl, rfl⟩)
      eliminators := fun e he => VEnv.addProjections_le.eliminators
        (VEnv.addEliminators_iff.mpr (.inl he)) }
  · intro S info hp
    rcases VEnv.addProjections_iff.mp hp with ⟨e, he, rfl, rfl⟩ | hold
    · exact .inr he
    · left
      rw [VEnv.addEliminators_projections, VEnv.addConstVals_projections R.core.ctorsAdded,
        VEnv.addConstVals_projections R.core.typesAdded] at hold
      exact hold

/-- The primitive constructor check, with its atomic formation batch, embeds
into the same `ConstructorCheck`. -/
noncomputable def PrimitiveConstructorCheck.toConstructorCheck
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv : Environment}
    {H : PrimitiveHeaderEnvironment c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    (R : PrimitiveConstructorCheck H ctorEnv) :
    ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv
      indTypes ctorEnv where
  headerEnv := headerEnv
  headerVEnv := H.context.venv
  headerEntries := H.entries
  constructorEntries := R.declared.entries
  headerValues := H.values
  constructorValues := R.declared.values
  sourceContext := H.sourceContext
  sourceContextVEnv := H.sourceContextVEnv
  sourceStatsWF := H.sourceStatsWF
  context := (R.declared.context.withEnv R.projectedChecking.tr (by
    rw [R.declared.contextVEnv]
    exact VEnv.addEliminators_addProjections_le)
    (R.projectedChecking.ctorTelescopes)).toContextWF R.projectedChecking
  headerMLCtx := H.context.mlctx
  contextMLCtx := R.declared.contextMLCtx
  headers := H.headers
  params := H.headers.params
  headerParams := rfl
  sourceHeaderParams := H.sourceHeaderParams
  parameterScope := H.statsWF.parameterScope
  sourceParameterScope := H.parameterScopeEq.symm
  statsWF := H.statsWF
  checkedParams := H.headerParams
  checkedParameterScope := rfl
  checked := R.checked
  parameterPrefixes := R.parameterPrefixes
  classes := R.classes
  constructorTails := R.constructorTails
  ownerNormalForms := R.ownerNormalForms
  telescopes := R.telescopes
  headerSourceAligned := H.sourceAligned
  constructorSourceAligned := R.declared.sourceAligned
  constructorKernel := R.declared.infos
  constructorNonInductive := R.declared.nonInductive
  ctorVEnv := R.declared.venvCtors
  eliminators := R.toCheckedFormation.caseEliminators
  eliminatorsWF := R.toCheckedFormation.caseEliminatorsWF
  eliminatorsCertified := R.toCheckedFormation.caseEliminatorsCertified
  eliminatorsOwn := R.toCheckedFormation.caseEliminatorsOwn
  eliminatorsBoundary := ⟨R.toCheckedFormation, rfl, rfl, rfl⟩
  contextVEnv := rfl
  installation := .primitive H.installed R.declared.installed
    (by simpa [H.values, R.declared.values] using R.declared.primitiveConstants)
    R.declared.safeEntries
  formation := R.formation
  core := R.core
  inductInfosFromDecl := R.inductInfosFromDecl
  constructorParameterAlignment := fun Hsource => R.constructorParameterAlignment Hsource

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The non-inductive constructor half of a complete primitive batch
preserves closure of every mutual family visible after the header half. -/
theorem PrimitiveConstructorEnvironment.closesMutuals
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv outEnv : Environment}
    {H : PrimitiveHeaderEnvironment c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    (R : PrimitiveConstructorEnvironment H outEnv)
    (hclosed : MutualInductivesClosed headerEnv) :
    MutualInductivesClosed outEnv :=
  R.installed.closesMutuals H.context.checking.map_wf hclosed
    R.nonInductive

end VerifyInductive
end Lean4Lean
