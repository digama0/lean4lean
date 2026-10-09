import Lean4Lean.Verify.Inductive.Constructor.Check
import Lean4Lean.Verify.Inductive.SourceAlignment

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

theorem ConstructorCheck.checkedRecursorConstructorTailAt
    (R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length) :
    CheckedConstructorTailAt R.headerVEnv c.lparams
      R.parameterScope stats decl
      (decl.types[familyIdx]'(by
        rw [← R.constructorTails.size_eq]
        exact hfamily))
      indTypes[familyIdx].ctors[ctorIdx] R.classes[familyIdx]![ctorIdx]! :=
  R.constructorTails.replay familyIdx hfamily ctorIdx hctor

/-- The motive-pass header of one family of the block, read off the constructor check: its
translation and checked header, transported through either ordinary or atomic installation. -/
def ConstructorCheck.motivePassHeaderAt
    (R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (hlparams : c.lparams.Nodup) :
    mkRecInfos.loopArgs1.MotivePassHeaderAt R.context stats decl depth
      indTypes[familyIdx] familyIdx := by
  have family := Lean4Lean.VerifyInductive.TrInductDeclCore.familyAlignmentFromSource
    R.core familyIdx hfamily
  have htarget := family.target_lt
  have Htype := family.translation
  have hsourceLE : sourceEnv <= R.context.venv :=
    R.installation.headerLE.trans (R.installation.constructorLE.trans R.ctorLE)
  have Hsource := Htype.header.mono hsourceLE
  have HsourceUses :=
    (Htype.header.type.avoids_of_constants
      (fun {_name _ci} hlookup =>
        Lean4Lean.VerifyInductive.TrInductDeclCore.headerBaseAvoidsSourceNames
          R.core hlookup)).mono hsourceLE
  have HrecursorSource : ∀ elimLevel
      (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel),
      ∃ targetType,
        ∃ translation : TrExprS R.context.venv
          (AddInductive.getRecLevelParams elimLevel c.lparams) []
          indTypes[familyIdx].type targetType,
        translation.Avoids (fun name => name ∈ decl.sourceNames) ∧
          targetType =
            (mkRecInfos.loopArgs1.recursorTargetSkeletonOf
              decl.types[familyIdx] c.lparams elimLevel Helim).type := by
    intro elimLevel Helim
    cases elimLevel with
    | zero =>
        exact ⟨decl.types[familyIdx].type, Hsource.type, HsourceUses, rfl⟩
    | param fresh =>
        have hsourceWF : sourceEnv.WF := by
          simpa only [R.sourceContextVEnv] using
            R.sourceContext.checking.tr.wf
        have Hshifted := Htype.header.type.prependLevelParam hsourceWF
          (by trivial) Helim
        have HshiftedUses := Hshifted.avoids_of_constants
          (fun {_name _ci} hlookup =>
            Lean4Lean.VerifyInductive.TrInductDeclCore.headerBaseAvoidsSourceNames
              R.core hlookup)
        exact ⟨decl.types[familyIdx].type.instL
            (VLevel.prependShift c.lparams.length),
          Hshifted.mono hsourceLE, HshiftedUses.mono hsourceLE, rfl⟩
    | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
        simp [AddInductive.AdmissibleElimLevel] at Helim
  refine {
    target := decl.types[familyIdx]
    targetAt := by simp [htarget]
    checked := R.recursorHeaders
    sourceTranslation := Hsource
    sourceTranslationUses := HsourceUses
    recursorSourceTranslationRestricted := HrecursorSource
    targetLookup := ?_
    lparamsNodup := hlparams }
  have hheaderLookup : R.headerVEnv.constants decl.types[familyIdx].name =
      some decl.types[familyIdx].toVConstant := by
    apply VEnv.addConstVals_get R.installation.headerAbstract
    rw [R.headerValues]
    exact List.mem_map.mpr
      ⟨decl.types[familyIdx], List.getElem_mem htarget, rfl⟩
  exact (R.installation.constructorLE.trans R.ctorLE).constants hheaderLookup

/-- The constructor check supplies a typed constructor application prefix, whether its
constants were installed ordinarily or as an atomic primitive batch. -/
theorem ConstructorCheck.checkedConstructorPrefixAt
    (R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    (hlparams : c.lparams.Nodup)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length) :
    let Hbase := R.context
    let Rbase := Hbase.toAdmissibleRecursorContextWF Helim
    let Hmaterialized := R.recursorHeaders
    let Hsuffix := Hmaterialized.parameterSuffix.toRecursorContext Helim
    exists ctorVal tail tailTarget introTarget,
      ctorVal ∈ (decl.types[familyIdx]'(by
        rw [← R.constructorTails.size_eq]
        exact hfamily)).ctors ∧
      ctorVal.name = indTypes[familyIdx].ctors[ctorIdx].name ∧
      ParameterPrefix stats 0
        indTypes[familyIdx].ctors[ctorIdx].type tail ∧
      TrExprS Rbase.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Hsuffix.parameterDecls tail tailTarget ∧
      Rbase.venv.IsType
        (AddInductive.getRecLevelParams elimLevel c.lparams).length
        Hsuffix.parameterDecls.toCtx tailTarget ∧
      TrExprS Rbase.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Hsuffix.parameterDecls
        (mkAppN
          (.const indTypes[familyIdx].ctors[ctorIdx].name stats.levels)
          stats.params) introTarget ∧
      introTarget = VExpr.mkApps
        (.const indTypes[familyIdx].ctors[ctorIdx].name
          (recursorDeclarationAbstractLevels c.lparams Helim))
        (bvarSpine stats.params.size) ∧
      Rbase.venv.HasType
        (AddInductive.getRecLevelParams elimLevel c.lparams).length
        Hsuffix.parameterDecls.toCtx introTarget tailTarget ∧
      Nonempty
        (checkInductiveTypes.loopType.ScopedHeaderTelescope
          Rbase.venv
          (AddInductive.getRecLevelParams elimLevel c.lparams)
          (recursorConstructorTelescopeTarget ctorVal Helim)
          Hsuffix.parameterDecls tailTarget stats.params.size 0) := by
  let Hbase := R.context
  let Rbase := Hbase.toAdmissibleRecursorContextWF Helim
  let Hmaterialized := R.recursorHeaders
  let Hsuffix := Hmaterialized.parameterSuffix.toRecursorContext Helim
  have hheaderLE : R.headerVEnv <= Hbase.venv := by
    change R.headerVEnv <= R.context.venv
    exact R.installation.constructorLE.trans R.ctorLE
  have Hreplay := R.checkedRecursorConstructorTailAt
    familyIdx hfamily ctorIdx hctor
  have Hreplay' : CheckedConstructorTailAt R.headerVEnv c.lparams
      Hmaterialized.parameterScope stats decl
      (decl.types[familyIdx]'(by
        rw [← R.constructorTails.size_eq]
        exact hfamily))
      indTypes[familyIdx].ctors[ctorIdx] R.classes[familyIdx]![ctorIdx]! := by
    rw [R.recursorHeaders_parameterScope]
    exact Hreplay
  have Hrebased := Hreplay'.toRecursorContext
    Hmaterialized hheaderLE Helim
  change exists ctorVal tail tailTarget introTarget, _
  rcases Hrebased with
    ⟨ctorVal, tail, tailTarget, hctorMem, hctorName, hctorUvars,
      Hprefix, Htail, HtailType, ⟨Hsynthesis⟩⟩
  have hfamilyDecl : familyIdx < decl.types.length := by
    rw [← R.constructorTails.size_eq]
    exact hfamily
  have hctorConstantMem : ctorVal ∈ decl.constructorConstants := by
    simp only [VInductDecl.constructorConstants]
    apply List.mem_flatMap.mpr
    exact ⟨decl.types[familyIdx], List.getElem_mem hfamilyDecl, hctorMem⟩
  have hctorWFHeader : ctorVal.toVConstant.WF R.headerVEnv := by
    simpa [VConstant.WF, hctorUvars, R.statsWF.uvars,
      R.checkedParams, R.headerParams] using
      R.checked.types ctorVal hctorConstantMem
  have hctorWF : ctorVal.toVConstant.WF Rbase.venv := by
    simpa [Rbase, Hbase] using hctorWFHeader.mono hheaderLE
  have hctorLookup : Rbase.venv.constants ctorVal.name =
      some ctorVal.toVConstant := by
    have hlookup : Hbase.venv.constants ctorVal.name =
        some ctorVal.toVConstant := by
      change R.context.venv.constants ctorVal.name =
        some ctorVal.toVConstant
      have hctor : R.ctorVEnv.constants ctorVal.name =
          some ctorVal.toVConstant := by
        apply VEnv.addConstVals_get R.installation.constructorAbstract
        rw [R.constructorValues]
        exact hctorConstantMem
      exact R.ctorLE.constants hctor
    simpa [Rbase] using hlookup
  let levels := recursorDeclarationAbstractLevels c.lparams Helim
  have hlevelsWF : ∀ level ∈ levels,
      level.WF (AddInductive.getRecLevelParams
        elimLevel c.lparams).length :=
    recursorDeclarationAbstractLevels_wf Helim
  have hlevelsLength : levels.length = ctorVal.uvars := by
    rw [recursorDeclarationAbstractLevels_length Helim, hctorUvars]
  have hsourceLevelsLength : stats.levels.length = ctorVal.uvars := by
    calc
      stats.levels.length = decl.uvars := Hmaterialized.levels
      _ = c.lparams.length := Hmaterialized.uvars.symm
      _ = ctorVal.uvars := hctorUvars.symm
  have htargetType : ctorVal.type.instL levels =
      (recursorConstructorTelescopeTarget ctorVal Helim).type :=
    VConstVal.type_instL_recursorDeclarationAbstractLevels
      hctorWF hctorUvars Helim
  have HintroType := Hsynthesis.canonicalApplication Rbase.checking.tr.wf
    hctorLookup hlevelsWF hlevelsLength htargetType
  have Hhead : TrExprS Rbase.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      Hsuffix.parameterDecls
      (.const ctorVal.name stats.levels) (.const ctorVal.name levels) := by
    exact TrExprS.const hctorLookup
      (Hmaterialized.recursorLevelTranslation hlparams Helim)
      hsourceLevelsLength
  have hcanonical :
      checkInductiveTypes.loopType.cachedParamVars stats.params.size 0 =
        bvarSpine Hsynthesis.params.length := by
    rw [checkInductiveTypes.loopType.cachedParamVars_zero_eq_bvarSpine,
      Hsynthesis.parameterCount]
  have Hargs : List.Forall₂
      (TrExprS Rbase.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Hsuffix.parameterDecls)
      stats.params.toList
      (bvarSpine Hsynthesis.params.length) := by
    rw [← hcanonical]
    exact Hsuffix.suffixParams
  have Hintro : TrExprS Rbase.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      Hsuffix.parameterDecls
      (Expr.mkAppList (.const ctorVal.name stats.levels)
        stats.params.toList)
      (VExpr.mkApps (.const ctorVal.name levels)
        (bvarSpine Hsynthesis.params.length)) :=
    checkPositivityStep.TrExprS.mkAppList Rbase.checking.tr.wf.ordered
      Hsynthesis.scopeWF.toCtx Hhead Hargs ⟨tailTarget, HintroType⟩
  refine ⟨ctorVal, tail, tailTarget,
    VExpr.mkApps (.const ctorVal.name levels)
      (bvarSpine Hsynthesis.params.length),
    hctorMem, hctorName, Hprefix, Htail, HtailType, ?_, ?_, HintroType,
    ⟨Hsynthesis⟩⟩
  · simpa [Expr.mkAppN_eq_mkAppList, hctorName, Rbase, Hbase,
      Hmaterialized, Hsuffix] using Hintro
  · simp [levels, hctorName, Hsynthesis.parameterCount]

/-- The checked constructor prefix of `checkedConstructorPrefixAt`, reinterpreted in any
later recursor context with the same parameter suffix. -/
theorem ConstructorCheck.checkedConstructorPrefixInRecursorContextAt
    (R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (elimLevel : Level)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    (hlparams : c.lparams.Nodup)
    {current : AddInductive.Context}
    (Rcurrent : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    (henvCurrent : Rcurrent.venv = R.context.venv)
    {runtimeDepth : Nat}
    (HsuffixCurrent : RecursorParameterContextSuffix Rcurrent stats
      runtimeDepth)
    (hparameterDecls : HsuffixCurrent.parameterDecls =
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        Helim).parameterDecls)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length) :
    exists tail tailTarget introTarget,
      ParameterPrefix stats 0
        indTypes[familyIdx].ctors[ctorIdx].type tail ∧
      Nonempty (ConstructorOwnerNormalForm stats familyIdx tail) ∧
      tail.FVarsIn (· ∈ ExprArrayFVarIds stats.params) ∧
      TrExprS Rcurrent.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Rcurrent.mlctx.vlctx tail tailTarget ∧
      Rcurrent.venv.IsType
        (AddInductive.getRecLevelParams elimLevel c.lparams).length
        Rcurrent.mlctx.vlctx.toCtx tailTarget ∧
      TrExprS Rcurrent.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Rcurrent.mlctx.vlctx
        (mkAppN
          (.const indTypes[familyIdx].ctors[ctorIdx].name stats.levels)
          stats.params) introTarget ∧
      Rcurrent.venv.HasType
        (AddInductive.getRecLevelParams elimLevel c.lparams).length
        Rcurrent.mlctx.vlctx.toCtx introTarget tailTarget ∧
      ∃ tailTarget₀, TrExprS Rcurrent.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        HsuffixCurrent.parameterDecls tail tailTarget₀ ∧
        Rcurrent.venv.IsType
          (AddInductive.getRecLevelParams elimLevel c.lparams).length
          HsuffixCurrent.parameterDecls.toCtx tailTarget₀ := by
  let Hbase := R.context
  let Rbase := Hbase.toAdmissibleRecursorContextWF Helim
  let HsuffixBase := R.recursorHeaders.parameterSuffix.toRecursorContext Helim
  rcases R.checkedConstructorPrefixAt Helim hlparams familyIdx hfamily
      ctorIdx hctor with
    ⟨_ctorVal, tail, tailNarrow, introNarrow, _hmem, _hname,
      Hprefix, Htail, HtailType, Hintro, _HintroShape,
      HintroType, _Hsynthesis⟩
  rcases R.ownerNormalForms.replay familyIdx hfamily ctorIdx hctor with
    ⟨normalTail, HnormalPrefix, Hnormal⟩
  have htailEq : normalTail = tail := HnormalPrefix.tail_eq Hprefix
  subst normalTail
  have HtailCurrent : TrExprS Rcurrent.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      HsuffixCurrent.parameterDecls tail tailNarrow := by
    rw [henvCurrent, hparameterDecls]
    simpa [Rbase, Hbase, HsuffixBase] using Htail
  have HtailTypeCurrent : Rcurrent.venv.IsType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      HsuffixCurrent.parameterDecls.toCtx tailNarrow := by
    rw [henvCurrent, hparameterDecls]
    simpa [Rbase, Hbase, HsuffixBase] using HtailType
  have HtailParams : tail.FVarsIn
      (· ∈ ExprArrayFVarIds stats.params) := by
    exact HtailCurrent.fvarsIn.mono fun fv hfv => by
      rw [HsuffixCurrent.parameterDecls_fvars] at hfv
      simpa using hfv
  have HintroCurrent : TrExprS Rcurrent.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      HsuffixCurrent.parameterDecls
      (mkAppN
        (.const indTypes[familyIdx].ctors[ctorIdx].name stats.levels)
        stats.params) introNarrow := by
    rw [henvCurrent, hparameterDecls]
    simpa [Rbase, Hbase, HsuffixBase] using Hintro
  have HintroTypeCurrent : Rcurrent.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      HsuffixCurrent.parameterDecls.toCtx introNarrow tailNarrow := by
    rw [henvCurrent, hparameterDecls]
    simpa [Rbase, Hbase, HsuffixBase] using HintroType
  rcases HsuffixCurrent.parameterEmbedding.transportTypedTerm
      Rcurrent.checking.tr.wf HintroCurrent HtailCurrent
      HintroTypeCurrent HtailTypeCurrent with
    ⟨introTarget, tailTarget, HintroRuntime, HtailRuntime,
      HintroTypeRuntime, HtailTypeRuntime⟩
  exact ⟨tail, tailTarget, introTarget, Hprefix, Hnormal, HtailParams,
    HtailRuntime, HtailTypeRuntime, HintroRuntime, HintroTypeRuntime,
    tailNarrow, HtailCurrent, HtailTypeCurrent⟩

/-- Enter the motive pass (`mkRecInfos.loopInd1`) from a constructor check. -/
theorem ConstructorCheck.loopInd1WF
    {alpha : Type} {Q : alpha -> Prop}
    (R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (elimLevel : Level)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    (hlparams : c.lparams.Nodup)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (k : Array AddInductive.RecInfo -> AddInductive.M alpha)
    (Hk : forall {cOut : AddInductive.Context} {outDepth : Nat}
      (recInfos : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF cOut
        (AddInductive.getRecLevelParams elimLevel c.lparams))
      (_henvOut : Rout.venv = R.context.venv)
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth)
      (_hparameterDeclsOut : HsuffixOut.parameterDecls =
        (R.recursorHeaders.parameterSuffix.toRecursorContext
          Helim).parameterDecls)
      (_HstatsOut : RecursorValidAppStatsWF Rout.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Rout.mlctx.vlctx stats decl outDepth)
      (Hbindings : RecInfoBindings cOut recInfos)
      (Horigins : RecInfoBinderTypes cOut recInfos),
      TrBinderTypes Rout Horigins.majorTypes ->
      MajorPremiseTypes stats recInfos Horigins.majorTypes
        cOut.env.isTypeAnnotationWrapper ->
      TrBinderTypes Rout Horigins.motiveTypes ->
      MotiveTypes cOut recInfos Horigins.motiveTypes elimLevel ->
      RecInfoMotiveTelescopes Rout stats decl
        (R.recursorHeaders.parameterSuffix.toRecursorContext
          Helim).parameterDecls.toCtx recInfos elimLevel ->
      TrBinderTypesPerFamily Rout Horigins.indexTypes ->
      (Hparams : FVarArrayIn cOut stats.params) ->
      RecInfoBindings.NoAlias stats.params recInfos ->
      RecInfoOuterOrder Rout Hparams Hbindings ->
      RecInfoArities stats recInfos ->
      RecInfoMinorsEmpty recInfos ->
      RecInfoTemplateCounts recInfos ->
      BindingContextLE { c with
        env := ctorEnv
        typeCheckerLParams := some <|
          AddInductive.getRecLevelParams elimLevel c.lparams } cOut ->
      recInfos.size = indTypes.size ->
      IndexTelescopeRuns stats indTypes cOut recInfos ->
      (k recInfos cOut).WF Q) :
    (AddInductive.mkRecInfos.loopInd1 stats indTypes elimLevel 0 #[] k
      { c with
        env := ctorEnv
        typeCheckerLParams := some <|
          AddInductive.getRecLevelParams elimLevel c.lparams }).WF Q := by
  let Hbase := R.context
  let Rbase := Hbase.toAdmissibleRecursorContextWF Helim
  let Hmaterialized := R.recursorHeaders
  let Hsuffix := Hmaterialized.parameterSuffix.toRecursorContext Helim
  let HstatsOrdinary :=
    checkPositivityStep.ValidAppStatsWF.ofHeaderStats Hmaterialized
  let Hstats := HstatsOrdinary.toRecursorContext Helim
  let Hheaders : forall i (hi : i < indTypes.size),
      mkRecInfos.loopArgs1.MotivePassHeaderAt Hbase stats decl depth
        indTypes[i] i := fun i hi =>
    R.motivePassHeaderAt i hi hlparams
  have HparamsCtx : forall i (hi : i < indTypes.size),
      VEnv.IsDefEqCtx Rbase.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams).length []
        ((Hheaders i hi).recursorParams Helim).reverse
        Hsuffix.parameterDecls.toCtx := by
    intro i hi
    have hmaterialized : (Hheaders i hi).checked = Hmaterialized := rfl
    change VEnv.IsDefEqCtx Rbase.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams).length []
      ((Hheaders i hi).recursorParams Helim).reverse
      (Hmaterialized.parameterSuffix.toRecursorContext
        Helim).parameterDecls.toCtx
    rw [← hmaterialized]
    exact (Hheaders i hi).recursorParamsContext Helim
  let HparamsBase : FVarArrayIn { c with env := ctorEnv } stats.params :=
    Hmaterialized.parameterSuffix.paramsBound
  let Hparams : FVarArrayIn { c with
      env := ctorEnv
      typeCheckerLParams := some <|
        AddInductive.getRecLevelParams elimLevel c.lparams } stats.params :=
    HparamsBase.monoFVars (by intro fv; exact id)
  have hparamsNodup : Hparams.fvars.Nodup := by
    change HparamsBase.fvars.Nodup
    exact Hmaterialized.parameterSuffix.paramsBound_nodup
  refine mkRecInfos.loopInd1.resultTyping Hbase stats indTypes elimLevel
    Helim Hheaders hconsume 0 #[] k Rbase (by simp [Rbase, Hbase])
    Hsuffix HparamsCtx
    Hstats (RecInfoBindings.empty _) (RecInfoBinderTypes.empty _)
    (TrBinderTypes.empty Rbase)
    (MajorPremiseTypes.empty stats _)
    (TrBinderTypes.empty Rbase)
    (MotiveTypes.empty _ elimLevel)
    (RecInfoMotiveTelescopes.empty Rbase stats decl
      Hsuffix.parameterDecls.toCtx elimLevel)
    (TrBinderTypesPerFamily.empty Rbase) Hparams
    (RecInfoBindings.empty_noAlias _ Hparams hparamsNodup)
    (RecInfoOuterOrder.empty Hsuffix Hparams)
    (BindingContextLE.rebaseTypeCheckerLParams
      (BindingContextLE.refl { c with env := ctorEnv })
      c.typeCheckerLParams
      (some <| AddInductive.getRecLevelParams elimLevel c.lparams))
    rfl (RecInfoArities.empty stats)
    RecInfoMinorsEmpty.empty RecInfoTemplateCounts.empty
    (ParameterUniverseSupport.of_contextWF (root := { c with
        env := ctorEnv
        typeCheckerLParams := some <|
          AddInductive.getRecLevelParams elimLevel c.lparams })
      Hbase HparamsBase rfl rfl (BindingContextLE.refl _)) IndexTelescopeRuns.empty ?_
  intro cOut outDepth recInfos Rout henvOut HsuffixOut hparameterDeclsOut
    HstatsOut Hbindings Horigins HmajorTypes HmajorShapes HmotiveTypes
    HmotiveShapes Htelescopes HindexRows HparamsOut HnoAlias Horder Harities
    Hempty Hblueprints Hroot hsize HindexTraces
  have Hroot' : BindingContextLE { c with
      env := ctorEnv
      typeCheckerLParams := some <|
        AddInductive.getRecLevelParams elimLevel c.lparams } cOut := by
    simpa using Hroot.rebaseTypeCheckerLParams
      (some <| AddInductive.getRecLevelParams elimLevel c.lparams)
      cOut.typeCheckerLParams
  apply Hk recInfos Rout henvOut HsuffixOut hparameterDeclsOut HstatsOut
    Hbindings Horigins HmajorTypes HmajorShapes HmotiveTypes HmotiveShapes (by
      simpa [hparameterDeclsOut] using Htelescopes) HindexRows HparamsOut
    HnoAlias Horder Harities Hempty Hblueprints Hroot' ?_ HindexTraces
  simpa using hsize

theorem ConstructorCheck.mkRecInfosWF
    {alpha : Type} {Q : alpha -> Prop}
    (R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (elimLevel : Level)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    (hlparams : c.lparams.Nodup)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.context.venv stats.indConsts)
    (k : Array AddInductive.RecInfo -> AddInductive.M alpha)
    (Hk : forall {cOut : AddInductive.Context} {outDepth : Nat}
      (recInfos : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF cOut
        (AddInductive.getRecLevelParams elimLevel c.lparams)),
      Rout.venv = R.context.venv ->
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth) ->
      HsuffixOut.parameterDecls =
        (R.recursorHeaders.parameterSuffix.toRecursorContext
          Helim).parameterDecls ->
      RecursorValidAppStatsWF Rout.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Rout.mlctx.vlctx stats decl outDepth ->
      VLCtx.NoIndConsts (decl.types.map (·.name)) Rout.mlctx.vlctx ->
      (Hbindings : RecInfoBindings cOut recInfos) ->
      (Horigins : RecInfoBinderTypes cOut recInfos) ->
      RuleTemplatesMatch stats recInfos Horigins ->
      TypedRuleTemplates Rout decl stats recInfos elimLevel
        HsuffixOut.parameterDecls Horigins ->
      MinorsAndIndicesMatchSource stats indTypes Horigins ->
      TypedMinors Rout Horigins
        HsuffixOut.parameterDecls ->
      TrBinderTypes Rout Horigins.majorTypes ->
      MajorPremiseTypes stats recInfos Horigins.majorTypes
        cOut.env.isTypeAnnotationWrapper ->
      TrBinderTypes Rout Horigins.motiveTypes ->
      MotiveTypes cOut recInfos Horigins.motiveTypes elimLevel ->
      RecInfoMotiveTelescopes Rout stats decl
        (R.recursorHeaders.parameterSuffix.toRecursorContext
          Helim).parameterDecls.toCtx recInfos elimLevel ->
      TrBinderTypesPerFamily Rout Horigins.indexTypes ->
      (Hparams : FVarArrayIn cOut stats.params) ->
      RecInfoBindings.NoAlias stats.params recInfos ->
      RecInfoOuterOrder Rout Hparams Hbindings ->
      RecInfoArities stats recInfos ->
      (forall i, i < recInfos.size ->
        recInfos[i]!.minors.size = indTypes[i]!.ctors.length) ->
      RecursorCounts stats recInfos decl ->
      BindingContextLE { c with
        env := ctorEnv
        typeCheckerLParams := some <|
          AddInductive.getRecLevelParams elimLevel c.lparams } cOut ->
      (k recInfos cOut).WF Q) :
    (AddInductive.mkRecInfos stats indTypes elimLevel k
      { c with
        env := ctorEnv
        typeCheckerLParams := some <|
          AddInductive.getRecLevelParams elimLevel c.lparams }).WF Q := by
  unfold AddInductive.mkRecInfos
  refine R.loopInd1WF elimLevel Helim hlparams hconsume
    (fun recInfos =>
      AddInductive.mkRecInfos.loopInd2 stats indTypes 0 recInfos k) ?_
  intro cFrames frameDepth recInfos Rframes henvFrames HsuffixFrames
    hparameterDeclsFrames HstatsFrames HbindingsFrames HoriginsFrames
    HmajorTypesFrames HmajorShapesFrames HmotiveTypesFrames
    HmotiveShapesFrames HtelescopesFrames HindexRowsFrames HparamsFrames
    HnoAliasFrames HorderFrames HaritiesFrames HemptyFrames
    HblueprintCountsFrames HrootFrames hsizeFrames HindexTracesFrames
  have hrecordsFrames : recInfos.size = stats.indConsts.size := by
    calc
      recInfos.size = indTypes.size := hsizeFrames
      _ = indTypes.toList.length := by simp
      _ = decl.types.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
      _ = stats.indConsts.size := HstatsFrames.types_size.symm
  refine mkRecInfos.loopInd2.resultTyping
    (root := { c with
      env := ctorEnv
      typeCheckerLParams := some <|
        AddInductive.getRecLevelParams elimLevel c.lparams }) (Q := Q)
    stats indTypes 0 recInfos k Rframes HsuffixFrames
    HstatsFrames hconsume (by simpa only [henvFrames] using hlit)
    (checkInductiveTypes.loopType.MLCtxOnlyLams.noIndConsts
      Rframes.onlyLams)
    HbindingsFrames HoriginsFrames
    (RuleTemplatesMatch.ofEmpty HoriginsFrames HemptyFrames
      HblueprintCountsFrames)
    (TypedRuleTemplates.ofEmpty Rframes decl HoriginsFrames
      HemptyFrames HblueprintCountsFrames elimLevel)
    (MinorsAndIndicesMatchSource.ofEmpty HoriginsFrames HemptyFrames
      HindexTracesFrames)
    (TypedMinors.ofEmpty
      (parameterDecls := HsuffixFrames.parameterDecls)
      Rframes HoriginsFrames HemptyFrames)
    HmajorTypesFrames HmajorShapesFrames HmotiveTypesFrames
    HmotiveShapesFrames HtelescopesFrames HindexRowsFrames HparamsFrames
    HnoAliasFrames HorderFrames HrootFrames
    (ParameterUniverseSupport.of_contextWF (root := { c with
        env := ctorEnv
        typeCheckerLParams := some <|
          AddInductive.getRecLevelParams elimLevel c.lparams })
      R.context
      (R.recursorHeaders.parameterSuffix (Hc := R.context)).paramsBound
      rfl rfl HrootFrames)
    (fun familyIdx hfamily ctor hctor tail Hprefix => by
      rw [HrootFrames.lparams_eq]
      exact R.constructorTails.levelParamsIn familyIdx hfamily ctor hctor tail
        Hprefix)
    hsizeFrames hrecordsFrames
    HaritiesFrames ?_ ?_ ?_ ?_
  · intro i hi
    omega
  · intro i _ hi
    exact HemptyFrames i hi
  · intro current currentDepth Rcurrent henvCurrent HsuffixCurrent
      hparameterDeclsCurrent familyIdx hfamily ctor hctor
    rcases List.mem_iff_getElem.mp hctor with ⟨ctorIdx, hctorIdx, rfl⟩
    rcases R.checkedConstructorPrefixInRecursorContextAt elimLevel Helim hlparams
        Rcurrent (henvCurrent.trans henvFrames) HsuffixCurrent
        (hparameterDeclsCurrent.trans hparameterDeclsFrames) familyIdx
        hfamily ctorIdx hctorIdx with
      ⟨tail, tailTarget, introTarget, Hprefix, Hnormal, HtailFVars,
        Htail, HtailType, Hintro, HintroType, tailTarget₀, Htail₀⟩
    exact ⟨tail, tailTarget, introTarget, Hprefix, Hnormal, HtailFVars,
      Htail, HtailType, Hintro, HintroType, tailTarget₀, Htail₀⟩
  · intro cOut outDepth out Rout henvOut HsuffixOut hparameterDeclsOut
      HstatsOut hctxOut HbindingsOut HoriginsOut HblueprintsOut
      HblueprintSemanticsOut HminorSourcesOut HminorSemanticsOut houtSize houtCounts
      HmajorTypesOut HmajorShapesOut
      HmotiveTypesOut HmotiveShapesOut HtelescopesOut HindexRowsOut
      HparamsOut HnoAliasOut HorderOut HaritiesOut HrootOut
    exact Hk out Rout (henvOut.trans henvFrames) HsuffixOut
      (hparameterDeclsOut.trans hparameterDeclsFrames) HstatsOut hctxOut
      HbindingsOut HoriginsOut HblueprintsOut HblueprintSemanticsOut HminorSourcesOut
      HminorSemanticsOut
      HmajorTypesOut HmajorShapesOut HmotiveTypesOut HmotiveShapesOut
      HtelescopesOut HindexRowsOut HparamsOut HnoAliasOut HorderOut
      HaritiesOut houtCounts
      (RecursorCounts.ofResult R.core R.statsWF
        houtSize houtCounts HaritiesOut)
      HrootOut

/-- The `getElimLevel` and `mkRecInfos` part of the recursor phase, run after a constructor
check. -/
theorem ConstructorCheck.getElimLevelMkRecInfosWF
    {alpha : Type} {Q : alpha -> Prop}
    (R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (hlparams : c.lparams.Nodup)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.context.venv stats.indConsts)
    (k : Level -> Bool -> Array AddInductive.RecInfo -> AddInductive.M alpha)
    (Hk : forall elimLevel,
      (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) ->
      AddInductive.getElimLevel stats indTypes { c with env := ctorEnv } =
        .ok elimLevel ->
      forall kTarget, KEligible stats indTypes kTarget ->
      forall {cOut : AddInductive.Context} {outDepth : Nat}
      (recInfos : Array AddInductive.RecInfo)
      (Rout : RecursorContextWF cOut
        (AddInductive.getRecLevelParams elimLevel c.lparams)),
      Rout.venv = R.context.venv ->
      (HsuffixOut : RecursorParameterContextSuffix Rout stats outDepth) ->
      HsuffixOut.parameterDecls =
        (R.recursorHeaders.parameterSuffix.toRecursorContext
          Helim).parameterDecls ->
      RecursorValidAppStatsWF Rout.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Rout.mlctx.vlctx stats decl outDepth ->
      VLCtx.NoIndConsts (decl.types.map (·.name)) Rout.mlctx.vlctx ->
      (Hbindings : RecInfoBindings cOut recInfos) ->
      (Horigins : RecInfoBinderTypes cOut recInfos) ->
      RuleTemplatesMatch stats recInfos Horigins ->
      TypedRuleTemplates Rout decl stats recInfos elimLevel
        HsuffixOut.parameterDecls Horigins ->
      MinorsAndIndicesMatchSource stats indTypes Horigins ->
      TypedMinors Rout Horigins
        HsuffixOut.parameterDecls ->
      TrBinderTypes Rout Horigins.majorTypes ->
      MajorPremiseTypes stats recInfos Horigins.majorTypes
        cOut.env.isTypeAnnotationWrapper ->
      TrBinderTypes Rout Horigins.motiveTypes ->
      MotiveTypes cOut recInfos Horigins.motiveTypes elimLevel ->
      RecInfoMotiveTelescopes Rout stats decl
        (R.recursorHeaders.parameterSuffix.toRecursorContext
          Helim).parameterDecls.toCtx recInfos elimLevel ->
      TrBinderTypesPerFamily Rout Horigins.indexTypes ->
      (Hparams : FVarArrayIn cOut stats.params) ->
      RecInfoBindings.NoAlias stats.params recInfos ->
      RecInfoOuterOrder Rout Hparams Hbindings ->
      RecInfoArities stats recInfos ->
      (forall i, i < recInfos.size ->
        recInfos[i]!.minors.size = indTypes[i]!.ctors.length) ->
      RecursorCounts stats recInfos decl ->
      BindingContextLE { c with
        env := ctorEnv
        typeCheckerLParams := some <|
          AddInductive.getRecLevelParams elimLevel c.lparams } cOut ->
      (k elimLevel kTarget recInfos cOut).WF Q) :
    ((AddInductive.getElimLevel stats indTypes >>= fun elimLevel =>
      AddInductive.withTypeCheckerLParams
        (AddInductive.getRecLevelParams elimLevel c.lparams) do
        let kTarget ← AddInductive.isKTarget stats indTypes
        AddInductive.mkRecInfos stats indTypes elimLevel
          (k elimLevel kTarget)) { c with env := ctorEnv }).WF Q := by
  have Helim : (AddInductive.getElimLevel stats indTypes
      { c with env := ctorEnv }).WF (fun level =>
        AddInductive.AdmissibleElimLevel c.lparams level ∧
        AddInductive.getElimLevel stats indTypes { c with env := ctorEnv } =
          .ok level) := by
    intro level hrun
    exact ⟨AddInductive.getElimLevel.WF stats indTypes { c with env := ctorEnv } level hrun, hrun⟩
  exact Helim.bind fun elimLevel ⟨hElim, hElimRun⟩ => by
    simp only [AddInductive.withTypeCheckerLParams, withReader]
    exact (show (AddInductive.isKTarget stats indTypes
      { c with
        env := ctorEnv
        typeCheckerLParams := some <|
          AddInductive.getRecLevelParams elimLevel c.lparams }).WF
        (KEligible stats indTypes) from
          AddInductive.isKTarget.checkedWF stats indTypes _).bind fun kTarget hk =>
      R.mkRecInfosWF elimLevel hElim hlparams hconsume hlit
        (k elimLevel kTarget) (Hk elimLevel hElim hElimRun kTarget hk)

end VerifyInductive
end Lean4Lean
