import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceHeaders
import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceTranslations

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-! # The source declaration of a nested run

The abstract source declaration of a nested declaration (`NestedSourceDeclaration`),
with its header and constructor environments and their translation `TrInductDeclCore`,
is reconstructed from the lowering, restoration and validation runs; neither the
declaration nor its constructor translations are supplied by the caller (section 3.3 of
the design notes). -/

/-- Two runs of the deterministic header-validation fold (`ValidationHeaderStep`)
have the same endpoint. -/
theorem FoldSteps.headerTarget_eq
    (Hleft : FoldSteps
      (fun indType : InductiveType => fun source target =>
        ValidationHeaderStep loweredEnv
        allIndNames indType.name source target)
      types sourceEnv leftTarget)
    (Hright : FoldSteps
      (fun indType : InductiveType => fun source target =>
        ValidationHeaderStep loweredEnv
        allIndNames indType.name source target)
      types sourceEnv rightTarget) :
    leftTarget = rightTarget := by
  induction Hleft generalizing rightTarget with
  | nil =>
    cases Hright
    rfl
  | @cons head tail sourceEnv middleEnv leftTarget Hhead Htail ih =>
    cases Hright with
    | @cons _ _ _ rightMiddle rightTarget HrightHead HrightTail =>
      have holdInfo : HrightHead.oldInfo = Hhead.oldInfo := by
        have hci := Option.some.inj
          (HrightHead.lookup.symm.trans Hhead.lookup)
        exact ConstantInfo.inductInfo.inj hci
      rw [HrightHead.output, holdInfo, ← Hhead.output] at HrightTail
      exact ih HrightTail

private theorem installRestoredSourceConstructors
    (Hvalid : CheckingEnv.ValidCore safety currentProdEnv currentVEnv)
    (Hle : canonicalEnv ≤ currentVEnv)
    (Hsource : RestoredConstructorTranslations result loweredEnv lparams safety
      canonicalEnv names traceProdEnv traceTargetEnv sources constructors)
    (Hvalidation : FoldSteps
      (ValidationConstructorStep result loweredEnv false)
      names currentProdEnv targetProdEnv) :
    ∃ targetVEnv,
      currentVEnv.addConstVals constructors = some targetVEnv ∧
      CheckingEnv.ValidCore safety targetProdEnv targetVEnv := by
  induction Hsource generalizing currentProdEnv currentVEnv targetProdEnv with
  | nil =>
    cases Hvalidation
    exact ⟨currentVEnv, by simp [VEnv.addConstVals], Hvalid⟩
  | cons Hstep Hsemantic Hrest ih =>
    cases Hvalidation with
    | cons HvalidationHead HvalidationTail =>
      have holdInfo : HvalidationHead.oldInfo = Hstep.oldInfo := by
        have hci := Option.some.inj
          (HvalidationHead.lookup.symm.trans Hstep.lookup)
        exact ConstantInfo.ctorInfo.inj hci
      have hinfo :
          { HvalidationHead.oldInfo with type :=
              (result.restoreNested loweredEnv
                HvalidationHead.oldInfo.type) } =
            Hstep.restored.newInfo := by
        rw [Hstep.restored.newInfo_eq, holdInfo]
      have hname : HvalidationHead.oldInfo.name =
          Hstep.restored.newInfo.name := by
        simpa using congrArg (fun info : ConstructorVal => info.name) hinfo
      have hconstructorName : Hstep.restored.newInfo.name =
          Hsemantic.constructor.name := by
        simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using
          Hsemantic.restoredTranslation.2
      have hfreshRestored : currentProdEnv.find?
          Hstep.restored.newInfo.name = none :=
        find?_none_of_contains_false Hvalid.tr.map_wf
          (by simpa [hname] using HvalidationHead.fresh)
      have hfreshProd : currentProdEnv.find?
          Hsemantic.constructor.name = none := by
        simpa [← hconstructorName] using hfreshRestored
      have habstractFresh :
          currentVEnv.constants Hsemantic.constructor.name = none := by
        cases hfind : currentVEnv.constants Hsemantic.constructor.name with
        | none => rfl
        | some value =>
          rcases Hvalid.tr.find?_iff.mpr ⟨value, hfind⟩ with
            ⟨info, hinfoFind, _hvisible⟩
          rw [hfreshProd] at hinfoFind
          contradiction
      rcases VEnv.addConst_eq_none
          (ci := Hsemantic.constructor.toVConstant) habstractFresh with
        ⟨nextVEnv, hadd⟩
      have HheadTr := Hsemantic.restoredTranslation.mono Hle
      have hnprim : ¬ Kernel.Environment.primitives.contains
          Hstep.restored.newInfo.name := by
        simpa [← hname] using HvalidationHead.notPrimitive rfl
      have HvalidNext : CheckingEnv.ValidCore safety
          (currentProdEnv.add (.ctorInfo Hstep.restored.newInfo)) nextVEnv :=
        Hvalid.add (ci := .ctorInfo Hstep.restored.newInfo)
          (ci' := Hsemantic.constructor.toVConstant)
          hfreshRestored hnprim
          HheadTr.1 (Hsemantic.sourceTranslation.wf.mono Hle)
          (by simpa [ConstantInfo.name, ConstantInfo.toConstantVal,
            hconstructorName] using hadd) rfl
      rw [HvalidationHead.output, hinfo] at HvalidationTail
      rcases ih HvalidNext (Hle.trans (VEnv.addConst_le hadd))
          HvalidationTail with ⟨targetVEnv, Hadded, HtargetValid⟩
      exact ⟨targetVEnv, by
        simp [VEnv.addConstVals, hadd, Hadded], HtargetValid⟩

private theorem installRestoredSourceFamilies
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv sourceTypesVEnv : VEnv}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Howners : ConstructorOwnersPresent c.env)
    (HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst sourceVEnv c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (loweredDecl.types.take sourceTypes.length))
    (HsourceAdded : sourceVEnv.addConstVals
      ((loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some sourceTypesVEnv)
    (HvalidationValid : CheckingEnv.Valid c.safety auxiliaryHeaderEnv
      sourceTypesVEnv)
    (hmode : validationFuel.cacheMode.Sound sourceTypesVEnv)
    (HparameterRun :
      Lean4Lean.validateSourceConstructorTypes.run auxiliaryHeaderEnv
        c.lparams c.safety validationFuel sourceTypes = .ok ())
    (hempty : initialState.nestedAux = #[])
    (Hrestoration : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      remainingSources restorationSource restorationTarget)
    (Hvalidation : FoldSteps
      (ValidationFamilyStep result loweredEnv false)
      remainingSources currentProdEnv targetProdEnv)
    (HremainingHeaders : List.Forall₂
      (fun source target => TrSourceConst sourceVEnv c.lparams source.name
        source.type target.toVConstVal)
      remainingSources remainingTargets)
    (HsourceMem : ∀ source ∈ remainingSources, source ∈ sourceTypes)
    (Hvalid : CheckingEnv.ValidCore c.safety currentProdEnv currentVEnv)
    (Hle : sourceTypesVEnv ≤ currentVEnv) :
    ∃ owners targetVEnv,
      owners.map VInductiveTypeSkeleton.toVConstVal =
        remainingTargets.map VInductiveType.toVConstVal ∧
      currentVEnv.addConstVals
        (owners.flatMap VInductiveTypeSkeleton.ctors) = some targetVEnv ∧
      CheckingEnv.ValidCore c.safety targetProdEnv targetVEnv ∧
      List.Forall₂ (fun source owner => ∀ numIndices resultLevel,
          TrInductiveType sourceVEnv sourceTypesVEnv c.lparams source
            (owner.toVInductiveType numIndices resultLevel))
        remainingSources owners := by
  induction Hrestoration generalizing currentProdEnv currentVEnv
      targetProdEnv remainingTargets with
  | nil =>
      cases Hvalidation
      cases HremainingHeaders
      exact ⟨[], currentVEnv, rfl, by simp [VEnv.addConstVals], Hvalid,
        .nil⟩
  | cons Hstep HrestorationTail ih =>
      cases Hvalidation with
      | cons HvalidationHead HvalidationTail =>
        cases HremainingHeaders with
        | @cons source target sources targets Hheader HheadersTail =>
          have hsourceGlobal : _ ∈ sourceTypes :=
            HsourceMem _ List.mem_cons_self
          rcases List.mem_iff_getElem.mp hsourceGlobal with
            ⟨familyIdx, hfamily, hsourceEq⟩
          cases hsourceEq
          rcases Hlower.sourceConstructorTypingAtFreshOfValidation Hc
              Hprod Hsources Howners HsourceHeaders HsourceAdded
              HvalidationValid hmode HparameterRun hempty familyIdx hfamily
              Hstep with ⟨constructors, Hconstructors⟩
          have holdInfo : HvalidationHead.oldInfo = Hstep.oldInfo := by
            have hci := Option.some.inj
              (HvalidationHead.lookup.symm.trans Hstep.lookup)
            exact ConstantInfo.inductInfo.inj hci
          have HvalidationConstructors := HvalidationHead.constructors
          rw [holdInfo] at HvalidationConstructors
          rcases installRestoredSourceConstructors Hvalid Hle Hconstructors
              HvalidationConstructors with
            ⟨middleVEnv, HconstructorsAdded, HmiddleValid⟩
          rcases ih HvalidationTail HheadersTail (fun source hsource =>
              HsourceMem source (by simp [hsource])) HmiddleValid
              (Hle.trans (VEnv.addConstVals_le HconstructorsAdded)) with
            ⟨owners, targetVEnv, HownerHeaders, HrestAdded, HtargetValid,
              Htypes⟩
          let owner' : VInductiveTypeSkeleton := {
            toVConstVal := target.toVConstVal
            ctors := constructors }
          have Howner : ∀ numIndices resultLevel,
              TrInductiveType sourceVEnv sourceTypesVEnv c.lparams
                sourceTypes[familyIdx]
                (owner'.toVInductiveType numIndices resultLevel) :=
            fun _ _ => ⟨Hheader, Hconstructors.forall₂⟩
          refine ⟨owner' :: owners, targetVEnv, ?_, ?_, HtargetValid,
            .cons Howner Htypes⟩
          · simp [owner', HownerHeaders]
          · simpa [owner', VEnv.addConstVals_append] using
              VEnv.addConstVals_append HconstructorsAdded HrestAdded

/-- The source declaration with its header and constructor environments,
obtained from the lowering, restoration, and validation runs. -/
structure NestedSourceDeclaration
    (sourceVEnv : VEnv) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (loweredDecl : VInductDecl) (safety : DefinitionSafety)
    (validationEnv auxiliaryHeaderEnv : Environment) where
  sourceDecl : VInductDecl
  envTypes : VEnv
  envCtors : VEnv
  sourceHeaders : List.Forall₂
    (fun source target => TrSourceConst sourceVEnv lparams source.name
      source.type target.toVConstVal)
    sourceTypes (loweredDecl.types.take sourceTypes.length)
  sourceAdded : sourceVEnv.addConstVals
    ((loweredDecl.types.take sourceTypes.length).map
      VInductiveType.toVConstVal) = some envTypes
  sourceTypeValues : sourceDecl.typeConstants =
    (loweredDecl.types.take sourceTypes.length).map
      VInductiveType.toVConstVal
  core : TrInductDeclCore sourceVEnv lparams nparams sourceTypes isUnsafe
    sourceDecl envTypes envCtors
  checked : SourcePrefixOfLowered sourceDecl loweredDecl
  headerValidationValid : CheckingEnv.Valid safety auxiliaryHeaderEnv envTypes
  validationValid : CheckingEnv.ValidCore safety validationEnv envCtors

/-- The source declaration used by nested verification, reconstructed from the
ordinary run on the lowered declaration and the validation runs. In particular,
neither the declaration nor its constructor translations are supplied by a caller. -/
theorem NestedLoweringOutputClosed.sourceCore
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
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (Hrestoration : NestedRestorationFolds result loweredEnv c.env
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) sourceTypes
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 ((), outEnv))
    (HconstructorValidation : ValidationEnvironment result
      loweredEnv c.env (sourceTypes.map (·.name)) false sourceTypes
      constructorValidationEnv)
    (HheaderValidation : ValidationHeaderEnvironment loweredEnv c.env
      (sourceTypes.map (·.name)) sourceTypes auxiliaryHeaderEnv)
    (HparameterRun :
      Lean4Lean.validateSourceConstructorTypes.run auxiliaryHeaderEnv
        c.lparams c.safety validationFuel sourceTypes = .ok ())
    (hmode : validationFuel.cacheMode.Sound sourceVEnv)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    Nonempty (NestedSourceDeclaration sourceVEnv c.lparams nparams
      sourceTypes isUnsafe loweredDecl c.safety constructorValidationEnv
        auxiliaryHeaderEnv) := by
  rcases Hlower.sourceHeaderPrefix R.core hempty with
    ⟨sourceTypesVEnv, HsourceAdded, HsourceHeaders⟩
  rcases HheaderValidation.validOfLowering Hlower Hc Hprod hempty
      hvisible with
    ⟨headerVEnv, HheaderAdded, HheaderValid⟩
  have hheaderVEnv : headerVEnv = sourceTypesVEnv := by
    exact Option.some.inj (HheaderAdded.symm.trans HsourceAdded)
  subst headerVEnv
  have hheaderProdEnv : HconstructorValidation.headerEnv = auxiliaryHeaderEnv :=
    HconstructorValidation.headers.headerTarget_eq HheaderValidation.headers
  have HconstructorTrace := HconstructorValidation.constructors
  rw [hheaderProdEnv] at HconstructorTrace
  rcases installRestoredSourceFamilies Hlower Hc Hprod Hsources Howners
      HsourceHeaders HsourceAdded HheaderValid (hmode.mono (VEnv.addConstVals_le HsourceAdded)) HparameterRun hempty
      Hrestoration.inductives HconstructorTrace
      HsourceHeaders (fun source hsource => hsource) HheaderValid.toValidCore
      VEnv.LE.rfl with
    ⟨owners, envCtors, HownerHeaders, HconstructorsAdded,
      HvalidationValid, Htypes⟩
  let skeleton : VInductDeclSkeleton := {
    uvars := c.lparams.length
    nparams := nparams
    types := owners
    isUnsafe := isUnsafe }
  have hsourceLength : skeleton.types.length ≤ loweredDecl.types.length := by
    have hownersLength : owners.length = sourceTypes.length :=
      (Lean4Lean.List.Forall₂.length_eq Htypes).symm
    rw [show skeleton.types.length = owners.length by rfl, hownersLength]
    calc
      sourceTypes.length ≤ result.types.length :=
        Hlower.toResult.sourceTypes_length_le
      _ = loweredDecl.types.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
  rcases VInductDeclSkeleton.withMetadataExpandedPrefix skeleton loweredDecl
      hsourceLength with ⟨sourceDecl, Hmaterialize, Hmaterialized⟩
  have hsourceTypeValues : sourceDecl.typeConstants =
      (loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal := by
    calc
      sourceDecl.typeConstants = skeleton.typeConstants := by
        rw [← VInductDecl.toSkeleton_typeConstants sourceDecl,
          VInductDeclSkeleton.withMetadata_toSkeleton Hmaterialize]
      _ = owners.map VInductiveTypeSkeleton.toVConstVal := rfl
      _ = _ := HownerHeaders
  have hfields := VInductDeclSkeleton.withMetadata_fields Hmaterialize
  have HsourceCore : TrInductDeclCore sourceVEnv c.lparams nparams
      sourceTypes isUnsafe sourceDecl sourceTypesVEnv envCtors := {
    uvars := hfields.1
    nparams := hfields.2.1
    isUnsafe := hfields.2.2.1
    typesAdded := by rw [hsourceTypeValues]; exact HsourceAdded
    ctorsAdded := by
      rw [← VInductDecl.toSkeleton_constructorConstants sourceDecl,
        VInductDeclSkeleton.withMetadata_toSkeleton Hmaterialize]
      simpa [skeleton, VInductDeclSkeleton.constructorConstants] using
        HconstructorsAdded
    types := VInductDeclSkeleton.withMetadata_forall₂ Hmaterialize Htypes }
  exact ⟨{
    sourceDecl := sourceDecl
    envTypes := sourceTypesVEnv
    envCtors := envCtors
    sourceHeaders := HsourceHeaders
    sourceAdded := HsourceAdded
    sourceTypeValues := hsourceTypeValues
    core := HsourceCore
    checked := Hmaterialized
    headerValidationValid := HheaderValid
    validationValid := HvalidationValid }⟩

end VerifyInductive
end Lean4Lean
