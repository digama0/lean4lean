import Lean4Lean.Verify.Inductive.Rules.EquationTranslation

/-! Translation and typing of one recursive-call body in the fixed equation context: the
recursive major at the selected family, the recursor head applied to the common prefix, and
`RecursorCheck.RuleAlignment.RecursiveCallFrame.recursiveCallBodyWF`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- The translated recursive major has the independently specified selected
mutual family at the exact recursive-index targets.  The exposed executable
spine is first identified at canonical parameters, then its merely
convertible index suffix is transported pointwise. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveCallFrame.insertedMajorTyping
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.RuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (B : A.FieldFrame :=
      Classical.choice A.fieldFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let parameterDecls := H.parameterSuffix.parameterDecls
    ∃ C : ClosedMotiveTelescope H.outVEnv Us stats decl
          selectedOwner H.recInfos[selectedOwner]! H.elimLevel,
      ∃ (equationDomains fieldDomains localDomains added frontDomains
          exactIndexTargets : List VExpr)
          (majorTarget ownerTarget : VExpr),
        equationDomains ++ localDomains =
            parameterDecls.toCtx.reverse ++ added ∧
          equationDomains =
            parameterDecls.toCtx.reverse ++ T.motives ++ T.minors ++
              fieldDomains ∧
          added = T.motives ++ T.minors ++ frontDomains ∧
          frontDomains = fieldDomains ++ localDomains ∧
          fieldDomains.length = A.rule.allArgs.size ∧
          fieldDomains =
            (liftContextPrefix (T.motives ++ T.minors).length
              B.fieldDomains.reverse).reverse ∧
          localDomains.length = F.semantic.generated.localArgs.size ∧
          ownerTarget = .bvar
            (frontDomains.length +
              (F.telescope.motives.drop (selectedOwner + 1) ++
                F.telescope.minors).length) ∧
          OnCtx
            (abstractForallContext
              (equationDomains ++ localDomains) []).toCtx
            (H.outVEnv.IsType Us.length) ∧
          TrExprS H.outVEnv Us
            (abstractForallContext equationDomains [])
            ((F.semantic.generated.current.lctx.mkForall
              F.semantic.generated.localArgs (.sort .zero)).abstractList
                A.rule.binders)
            (VExpr.wrapForalls localDomains (.sort .zero)) ∧
          VEnv.IsDefEqCtx H.outVEnv Us.length []
            C.params.reverse parameterDecls.toCtx ∧
          exactIndexTargets.length = C.indices.length ∧
          List.Forall₂
            (TrExprS H.outVEnv Us
              (abstractForallContext
                (equationDomains ++ localDomains) []))
            (((F.semantic.generated.exposedType.getAppArgs[
              stats.params.size:]).toList.map fun index =>
                (index.abstractList
                  F.semantic.generated.arguments_bound.fvars).abstractList
                    A.rule.binders
                    F.semantic.generated.localArgs.size))
            exactIndexTargets ∧
          TrExprS H.outVEnv Us
            (abstractForallContext
              (equationDomains ++ localDomains) [])
            (F.semantic.generated.outerAbstractedMajor A.rule.binders)
            majorTarget ∧
          H.outVEnv.HasType Us.length
            (abstractForallContext
              (equationDomains ++ localDomains) []).toCtx
            majorTarget
            (VExpr.mkApps (C.family.liftN added.length 0)
              exactIndexTargets) ∧
          H.outVEnv.HasType Us.length
            (abstractForallContext
              (equationDomains ++ localDomains) []).toCtx
            (.app (VExpr.mkApps ownerTarget exactIndexTargets) majorTarget)
            (.sort C.resultLevel) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let parameterDecls := H.parameterSuffix.parameterDecls
  rcases F.insertedExposedSpine T (B := B) with
    ⟨equationDomains, fieldDomains, localDomains, added, frontDomains,
      exactIndexTargets, majorTarget, exposedTarget, hdecomposition,
      hequation, hadded, hfront, hfields, hfixedFields, hlocal,
      hequationLength, Hctx,
      HlocalTemplate, Htyping, Hindices, Hmajor, hexactLength,
      levels, parameterTargets,
      spineIndexTargets, hspine, hlevels, _HparameterTranslation,
      hparameterTargets, HindexDefEq⟩
  rcases F.ownerMotiveDomain with
    ⟨S, HselectedSource, HmotiveDomain₀⟩
  have henvLe : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.constructorVEnv_le
  let C := S.canonical.mono henvLe
  have HcanonicalSource : VEnv.IsDefEqCtx H.outVEnv Us.length []
      C.params.reverse S.motiveSourceScope.toCtx := by
    simpa [C, ClosedMotiveTelescope.mono] using
      S.motiveSourceAlignment.mono henvLe
  have HselectedCanonical : VEnv.IsDefEqCtx H.outVEnv Us.length []
      F.telescope.params.reverse C.params.reverse :=
    VEnv.IsDefEqCtx.trans_empty H.outVEnvWF
      HselectedSource (HcanonicalSource.symm H.outVEnvWF.ordered)
  rcases H.installedRecursorParameterContextAt selectedOwner F.entry_lt with
    ⟨Tselected, HselectedCached⟩
  rcases Tselected.groupsResult_eq F.telescope with
    ⟨hselectedParams, _hselectedMotives, _hselectedMinors,
      _hselectedIndices, _hselectedMajor, _hselectedResult⟩
  rw [hselectedParams] at HselectedCached
  have HselectedCached' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      F.telescope.params.reverse parameterDecls.toCtx := by
    simpa [parameterDecls, H.parameterDecls, Us] using HselectedCached
  have HcanonicalCached : VEnv.IsDefEqCtx H.outVEnv Us.length []
      C.params.reverse parameterDecls.toCtx :=
    VEnv.IsDefEqCtx.trans_empty H.outVEnvWF
      (HselectedCanonical.symm H.outVEnvWF.ordered) HselectedCached'
  have hparameterLength : parameterDecls.toCtx.length = stats.params.size := by
    calc
      parameterDecls.toCtx.length = parameterDecls.length := by
        simpa [parameterDecls] using
          checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
            H.parameterSuffix.cached
      _ = stats.params.size := by
        simpa [parameterDecls] using H.parameterSuffix.parameterDecls_length
  have haddedLength : A.rule.binders.length + localDomains.length =
      stats.params.size + added.length := by
    have hlengths := congrArg List.length hdecomposition
    simp only [List.length_append, List.length_reverse] at hlengths
    rw [hequationLength, hparameterLength] at hlengths
    exact hlengths
  have hparameterBound : stats.params.size ≤ A.rule.binders.length := by
    have hparams : A.rule.params_bound.fvars.length = stats.params.size := by
      have h := congrArg Array.size A.rule.params_bound.expressions
      simpa using h.symm
    unfold RecursorRuleSyntax.binders
    simp only [List.length_append]
    omega
  have hparameterTargetsLifted : parameterTargets =
      (bvarSpine stats.params.size).map
        (fun target => target.liftN added.length 0) := by
    rw [hparameterTargets,
      bvarSpine_liftN_zero_eq_ofFn]
    apply List.ext_getElem
    · simp
    · intro k hleft hright
      have hk : k < stats.params.size := by simpa using hright
      simp only [List.getElem_map, List.getElem_ofFn]
      simp [VExpr.liftN, liftVar]
      congr 1
      omega
  let familyTarget := VExpr.mkApps
    (.const (decl.types[selectedOwner]'F.semantic.validated.target_lt).name
      levels) parameterTargets
  have hcanonicalLevels : C.levels = levels := by
    exact Option.some.inj (C.levels_translation.symm.trans hlevels)
  have hfamilyTargetCanonical :
      familyTarget = C.family.liftN added.length 0 := by
    dsimp only [familyTarget]
    rw [C.family_eq]
    simp only [C.params_length, VExpr.liftN_mkApps]
    rw [hcanonicalLevels, hparameterTargetsLifted]
    simp [selectedOwner, VExpr.liftN]
  have hexposedApplication : exposedTarget =
      VExpr.mkApps familyTarget spineIndexTargets := by
    have hrebuild := VExpr.mkApps_getAppFnArgs exposedTarget
    rw [hspine] at hrebuild
    simpa [familyTarget, VExpr.mkApps_append] using hrebuild.symm
  have HmajorSpine : H.outVEnv.HasType Us.length
      (abstractForallContext
        (equationDomains ++ localDomains) []).toCtx
      majorTarget
      (VExpr.mkApps (C.family.liftN added.length 0) spineIndexTargets) := by
    rw [← hfamilyTargetCanonical, ← hexposedApplication]
    exact Htyping
  have HspineWF : VExpr.WF H.outVEnv Us.length
      (abstractForallContext
        (equationDomains ++ localDomains) []).toCtx
      (VExpr.mkApps (C.family.liftN added.length 0)
        spineIndexTargets) := by
    rcases HmajorSpine.isType H.outVEnvWF Hctx with ⟨level, Htype⟩
    exact ⟨.sort level, Htype⟩
  have HfamilyWF := VExpr.WF.mkApps_fn H.outVEnvWF.ordered Hctx HspineWF
  have HappDefEq := VEnv.IsDefEqU.mkApps H.outVEnvWF Hctx
    (VEnv.IsDefEqU.refl HfamilyWF) HspineWF HindexDefEq
  have HmajorExact : H.outVEnv.HasType Us.length
      (abstractForallContext
        (equationDomains ++ localDomains) []).toCtx
      majorTarget
      (VExpr.mkApps (C.family.liftN added.length 0)
        exactIndexTargets) :=
    HmajorSpine.defeqU_r H.outVEnvWF Hctx HappDefEq
  have hindexCanonical : exactIndexTargets.length = C.indices.length := by
    calc
      exactIndexTargets.length = F.telescope.indices.length := hexactLength
      _ = H.recInfos[selectedOwner]!.indices.size :=
        F.telescope.indices_length
      _ = C.indices.length := C.indices_length.symm
  let inserted := T.motives ++ T.minors
  let cachedFull := frontDomains.reverse ++ inserted.reverse ++
    parameterDecls.toCtx
  let Touter := T.params ++ T.motives ++ T.minors
  let selectedOuter := F.telescope.params ++ F.telescope.motives ++
    F.telescope.minors
  have htoCtx : ∀ types : List VExpr,
      VLCtx.toCtx (types.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) = types := by
    intro types
    induction types with
    | nil => rfl
    | cons type types ih => simp [VLCtx.toCtx, ih]
  have hcallCtx :
      (abstractForallContext
        (equationDomains ++ localDomains) []).toCtx =
        (equationDomains ++ localDomains).reverse := by
    simpa [abstractForallContext] using
      htoCtx (equationDomains ++ localDomains).reverse
  have HctxPlain : OnCtx (equationDomains ++ localDomains).reverse
      (H.outVEnv.IsType Us.length) := by
    simpa only [hcallCtx] using Hctx
  have HcachedFull : OnCtx cachedFull (H.outVEnv.IsType Us.length) := by
    rw [hdecomposition, hadded] at HctxPlain
    simpa [cachedFull, inserted, List.reverse_append,
      List.append_assoc] using HctxPlain
  rcases A.installedRecursorParameterContext with ⟨T₀, HparamsT⟩
  rcases T₀.groupsResult_eq T with
    ⟨hparamsT, _hmotivesT, _hminorsT, _hindicesT,
      _hmajorT, _hresultT⟩
  rw [hparamsT] at HparamsT
  have HparamsT' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      T.params.reverse parameterDecls.toCtx := by
    simpa [parameterDecls, H.parameterDecls, Us] using HparamsT
  have HcachedToT₀ :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      (HparamsT'.symm H.outVEnvWF.ordered) HcachedFull
  have HcachedToT : VEnv.IsDefEqCtx H.outVEnv Us.length []
      cachedFull (frontDomains.reverse ++ Touter.reverse) := by
    simpa [cachedFull, inserted, Touter, List.reverse_append,
      List.append_assoc] using HcachedToT₀
  have HTFull : OnCtx (frontDomains.reverse ++ Touter.reverse)
      (H.outVEnv.IsType Us.length) :=
    (HcachedToT.symm H.outVEnvWF.ordered).isType
  have Hcommon := H.installedRecursorCommonPrefixContextAt
    owner howner selectedOwner F.entry_lt T F.telescope
  have HTToSelected :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      Hcommon HTFull
  have HselectedToCached : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (frontDomains.reverse ++ selectedOuter.reverse) cachedFull :=
    VEnv.IsDefEqCtx.trans_empty H.outVEnvWF
      (by simpa [Touter, selectedOuter] using
        HTToSelected.symm H.outVEnvWF.ordered)
      (HcachedToT.symm H.outVEnvWF.ordered)
  have hownerRecInfo : selectedOwner < H.recInfos.size := by
    simpa [H.generated.length] using F.entry_lt
  have hownerMotive : selectedOwner < F.telescope.motives.length := by
    rw [F.telescope.motives_length]
    simpa using hownerRecInfo
  let later := F.telescope.motives.drop (selectedOwner + 1) ++
    F.telescope.minors
  let newer := F.telescope.motives.drop selectedOwner ++
    F.telescope.minors ++ frontDomains
  let ownerTarget : VExpr := .bvar (frontDomains.length + later.length)
  have HownerOuter := F.telescope.ownerMotiveOuterBvarTyping hownerMotive
  have Wfront : Ctx.LiftN frontDomains.length 0 selectedOuter.reverse
      (frontDomains.reverse ++ selectedOuter.reverse) := by
    exact .zero frontDomains.reverse (by simp)
  have HownerSelected₀ := HownerOuter.weakN H.outVEnvWF.ordered Wfront
  have HownerSelected : H.outVEnv.HasType Us.length
      (frontDomains.reverse ++ selectedOuter.reverse) ownerTarget
      (F.telescope.motives[selectedOwner]!.liftN newer.length 0) := by
    have hownerTargetEq :
        (VExpr.bvar later.length).liftN frontDomains.length 0 =
          ownerTarget := by
      simp [ownerTarget, VExpr.liftN, Nat.add_comm]
    have hownerGet :
        F.telescope.motives[selectedOwner]'hownerMotive =
          F.telescope.motives[selectedOwner]! :=
      (getElem!_pos F.telescope.motives selectedOwner hownerMotive).symm
    have hownerTypeEq :
        ((F.telescope.motives[selectedOwner]'hownerMotive).liftN
            (later.length + 1) 0).liftN frontDomains.length 0 =
          F.telescope.motives[selectedOwner]!.liftN newer.length 0 := by
      rw [hownerGet, VExpr.liftN_liftN]
      have hlength : later.length + 1 + frontDomains.length =
          newer.length := by
        dsimp only [later, newer]
        simp only [List.length_append, List.length_drop]
        omega
      rw [hlength]
    rw [hownerTargetEq, hownerTypeEq] at HownerSelected₀
    exact HownerSelected₀
  have HmotiveDomain : H.outVEnv.IsDefEqU Us.length
      (abstractForallContext
        (F.telescope.params ++
          F.telescope.motives.take selectedOwner) []).toCtx
      F.telescope.motives[selectedOwner]!
      (C.motiveType.liftN
        (F.telescope.motives.take selectedOwner).length 0) := by
    simpa [C, ClosedMotiveTelescope.mono] using HmotiveDomain₀
  have hearlierCtx :
      (abstractForallContext
        (F.telescope.params ++
          F.telescope.motives.take selectedOwner) []).toCtx =
        (F.telescope.params ++
          F.telescope.motives.take selectedOwner).reverse := by
    simpa [abstractForallContext] using htoCtx
      ((F.telescope.params ++
        F.telescope.motives.take selectedOwner).reverse)
  have hselectedSplit : selectedOuter.reverse =
      (F.telescope.motives.drop selectedOwner ++
        F.telescope.minors).reverse ++
        (F.telescope.params ++
          F.telescope.motives.take selectedOwner).reverse := by
    dsimp only [selectedOuter]
    have hmotives : F.telescope.motives =
        F.telescope.motives.take selectedOwner ++
          F.telescope.motives.drop selectedOwner :=
      (List.take_append_drop selectedOwner F.telescope.motives).symm
    have hmotivesReverse : F.telescope.motives.reverse =
        (F.telescope.motives.drop selectedOwner).reverse ++
          (F.telescope.motives.take selectedOwner).reverse := by
      calc
        F.telescope.motives.reverse =
            (F.telescope.motives.take selectedOwner ++
              F.telescope.motives.drop selectedOwner).reverse :=
          congrArg List.reverse hmotives
        _ = (F.telescope.motives.drop selectedOwner).reverse ++
            (F.telescope.motives.take selectedOwner).reverse := by
          simp only [List.reverse_append]
    simp only [List.reverse_append]
    rw [hmotivesReverse]
    simp only [List.append_assoc]
  have Wmotive : Ctx.LiftN newer.length 0
      (abstractForallContext
        (F.telescope.params ++
          F.telescope.motives.take selectedOwner) []).toCtx
      (frontDomains.reverse ++ selectedOuter.reverse) := by
    rw [hearlierCtx]
    have hfullSplit : frontDomains.reverse ++ selectedOuter.reverse =
        newer.reverse ++
          (F.telescope.params ++
            F.telescope.motives.take selectedOwner).reverse := by
      rw [hselectedSplit]
      simp [newer, List.reverse_append, List.append_assoc]
    rw [hfullSplit]
    exact .zero newer.reverse (by simp)
  have HmotiveDomainFull := HmotiveDomain.weakN
    H.outVEnvWF.ordered Wmotive
  have hcanonicalLift :
      (F.telescope.motives.take selectedOwner).length + newer.length =
        added.length := by
    have haddedLength' := congrArg List.length hadded
    simp only [List.length_append] at haddedLength'
    have htakeDrop := congrArg List.length
      (List.take_append_drop selectedOwner F.telescope.motives)
    simp only [List.length_append] at htakeDrop
    calc
      (F.telescope.motives.take selectedOwner).length + newer.length =
          F.telescope.motives.length + F.telescope.minors.length +
            frontDomains.length := by
        dsimp only [newer]
        simp only [List.length_append]
        omega
      _ = T.motives.length + T.minors.length + frontDomains.length := by
        rw [F.telescope.motives_length, T.motives_length,
          F.telescope.minors_length, T.minors_length]
      _ = added.length := by omega
  have HmotiveDomainSelected : H.outVEnv.IsDefEqU Us.length
      (frontDomains.reverse ++ selectedOuter.reverse)
      (F.telescope.motives[selectedOwner]!.liftN newer.length 0)
      (C.motiveType.liftN added.length 0) := by
    simpa only [VExpr.liftN_liftN, hcanonicalLift] using HmotiveDomainFull
  have HownerCached := HownerSelected.defeqDFC
    H.outVEnvWF.ordered HselectedToCached
  have HmotiveDomainCached := HmotiveDomainSelected.defeqDFC
    H.outVEnvWF.ordered HselectedToCached
  have HmotiveCanonical : H.outVEnv.HasType Us.length cachedFull
      ownerTarget (C.motiveType.liftN added.length 0) :=
    HownerCached.defeqU_r H.outVEnvWF HcachedFull HmotiveDomainCached
  have HctxApply : OnCtx (added.reverse ++ parameterDecls.toCtx)
      (H.outVEnv.IsType Us.length) := by
    simpa [cachedFull, inserted, hadded, List.reverse_append,
      List.append_assoc] using HcachedFull
  have HmajorApply : H.outVEnv.HasType Us.length
      (added.reverse ++ parameterDecls.toCtx) majorTarget
      (VExpr.mkApps (C.family.liftN added.length 0)
        exactIndexTargets) := by
    have HmajorPlain : H.outVEnv.HasType Us.length
        (equationDomains ++ localDomains).reverse majorTarget
        (VExpr.mkApps (C.family.liftN added.length 0)
          exactIndexTargets) := by
      simpa only [hcallCtx] using HmajorExact
    rw [hdecomposition] at HmajorPlain
    simpa [parameterDecls, List.reverse_append,
      List.append_assoc] using HmajorPlain
  have HmotiveApply : H.outVEnv.HasType Us.length
      (added.reverse ++ parameterDecls.toCtx) ownerTarget
      (C.motiveType.liftN added.length 0) := by
    simpa [cachedFull, inserted, hadded, List.reverse_append,
      List.append_assoc] using HmotiveCanonical
  have Happly := C.applyMajorTypedAfterDefEq H.outVEnvWF
    parameterDecls.toCtx added HcanonicalCached HctxApply
    exactIndexTargets hindexCanonical ownerTarget majorTarget
    HmotiveApply HmajorApply
  have Happly' : H.outVEnv.HasType Us.length
      (abstractForallContext
        (equationDomains ++ localDomains) []).toCtx
      (.app (VExpr.mkApps ownerTarget exactIndexTargets) majorTarget)
      (.sort C.resultLevel) := by
    rw [hcallCtx, hdecomposition]
    simpa [parameterDecls, List.reverse_append,
      List.append_assoc] using Happly
  exact ⟨C, equationDomains, fieldDomains, localDomains, added, frontDomains,
    exactIndexTargets, majorTarget, ownerTarget, hdecomposition,
    (by simpa [List.append_assoc] using hequation),
    hadded, hfront, hfields, hfixedFields, hlocal, rfl, Hctx,
    HlocalTemplate, HcanonicalCached,
    hindexCanonical, Hindices, Hmajor, HmajorExact, Happly'⟩

/-- Assemble the call-selected recursor head with the rule's common
parameter/motive/minor variables in an arbitrary canonical equation
telescope.  The sole non-structural premise is the selected prefix typing in
that context; all concrete argument translations are forced by the retained
rule binders. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveCallFrame.selectedPrefixResidualTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.RuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (Hctx : OnCtx
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length))
    (Hprefix :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let selectedOwner := F.semantic.generated.ownerIdx
      let recursor := (H.entries[selectedOwner]'F.entry_lt).2
      H.outVEnv.HasType Us.length
        (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
        ((VExpr.mkApps
            ((VExpr.const recursor.name
              (VLevel.params Us.length)).liftN
              (T.params ++ T.motives ++ T.minors).length 0)
            (bvarSpine
              (T.params ++ T.motives ++ T.minors).length)).liftN
          fieldDomains.length 0)
        prefixType) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let recursor := (H.entries[selectedOwner]'F.entry_lt).2
    let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
    TrExprS H.outVEnv Us (abstractForallContext domains [])
      (mkAppN
        (mkAppN
          (mkAppN
            (.const F.semantic.generated.recursorName
              (AddInductive.getRecLevels H.elimLevel stats.levels))
            (stats.params.map fun arg =>
              arg.abstractList A.rule.binders))
          ((H.recInfos.map (·.motive)).map fun arg =>
            arg.abstractList A.rule.binders))
        ((H.recInfos.flatMap (·.minors)).map fun arg =>
          arg.abstractList A.rule.binders))
      ((VExpr.mkApps
          ((VExpr.const recursor.name
            (VLevel.params Us.length)).liftN
            (T.params ++ T.motives ++ T.minors).length 0)
          (bvarSpine
            (T.params ++ T.motives ++ T.minors).length)).liftN
        fieldDomains.length 0) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let recursor := (H.entries[selectedOwner]'F.entry_lt).2
  let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  dsimp only
  have Hhead := F.headTranslation (abstractForallContext domains [])
  have Hargs := A.recursorPrefixTranslation T fieldDomains hfields
  have htoCtx : ∀ types : List VExpr,
      VLCtx.toCtx (types.map fun type => (none, .vlam type)) = types := by
    intro types
    induction types with
    | nil => rfl
    | cons type types ih => simp [VLCtx.toCtx, ih]
  have htoCtxReverse : ∀ types : List VExpr,
      VLCtx.toCtx (types.map fun type => (none, .vlam type)).reverse =
        types.reverse := by
    intro types
    rw [← List.map_reverse]
    exact htoCtx types.reverse
  have Hctx' : OnCtx (abstractForallContext domains []).toCtx
      (H.outVEnv.IsType Us.length) := by
    simpa [abstractForallContext, htoCtx, htoCtxReverse, domains] using Hctx
  have Hwf : VExpr.WF H.outVEnv Us.length
      (abstractForallContext domains []).toCtx
      (VExpr.mkApps
        (.const recursor.name (VLevel.params Us.length))
        ((bvarSpine
          (T.params ++ T.motives ++ T.minors).length).map fun arg =>
            arg.liftN fieldDomains.length 0)) := by
    exact ⟨prefixType, by
      change H.outVEnv.HasType Us.length
        (abstractForallContext domains []).toCtx
        (VExpr.mkApps
          (.const recursor.name (VLevel.params Us.length))
          ((bvarSpine
            (T.params ++ T.motives ++ T.minors).length).map fun arg =>
              arg.liftN fieldDomains.length 0)) prefixType
      simpa [abstractForallContext, htoCtx, htoCtxReverse, domains,
        VExpr.liftN_mkApps, VExpr.liftN] using Hprefix⟩
  have Htr := checkPositivityStep.TrExprS.mkAppList
    H.outVEnvWF.ordered Hctx' Hhead Hargs Hwf
  simpa [Expr.mkAppN_eq_mkAppList, Expr.mkAppList_append,
    VExpr.liftN_mkApps, VExpr.liftN, domains,
    List.append_assoc] using Htr

/-- Premise-free form of `selectedPrefixResidualTranslation`: mutual-prefix
context conversion and weakening under the constructor fields are recovered
from the two retained recursor telescopes. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveCallFrame.prefixResidualTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.RuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (Hctx : OnCtx
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let recursor := (H.entries[selectedOwner]'F.entry_lt).2
    let domains := (T.params ++ T.motives ++ T.minors) ++ fieldDomains
    TrExprS H.outVEnv Us (abstractForallContext domains [])
      (mkAppN
        (mkAppN
          (mkAppN
            (.const F.semantic.generated.recursorName
              (AddInductive.getRecLevels H.elimLevel stats.levels))
            (stats.params.map fun arg =>
              arg.abstractList A.rule.binders))
          ((H.recInfos.map (·.motive)).map fun arg =>
            arg.abstractList A.rule.binders))
        ((H.recInfos.flatMap (·.minors)).map fun arg =>
          arg.abstractList A.rule.binders))
      ((VExpr.mkApps
          ((VExpr.const recursor.name
            (VLevel.params Us.length)).liftN
            (T.params ++ T.motives ++ T.minors).length 0)
          (bvarSpine
            (T.params ++ T.motives ++ T.minors).length)).liftN
        fieldDomains.length 0) := by
  exact F.selectedPrefixResidualTranslation T fieldDomains hfields Hctx
    (F.prefixTypingInEquationContext T fieldDomains Hctx)

/-- Cached-parameter form of the call-selected mutual recursor prefix.
Translation uniqueness preserves the exact canonical target while the
dependent context conversion replaces executable parameter domains by the
independently cached parameter suffix. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveCallFrame.cachedPrefixResidualTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.RuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (Hctx :
      let parameterDecls := H.parameterSuffix.parameterDecls
      OnCtx
        (((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
          fieldDomains).reverse)
        (H.outVEnv.IsType
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let selectedOwner := F.semantic.generated.ownerIdx
    let recursor := (H.entries[selectedOwner]'F.entry_lt).2
    let parameterDecls := H.parameterSuffix.parameterDecls
    let cachedDomains :=
      (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++ fieldDomains
    TrExprS H.outVEnv Us (abstractForallContext cachedDomains [])
      (mkAppN
        (mkAppN
          (mkAppN
            (.const F.semantic.generated.recursorName
              (AddInductive.getRecLevels H.elimLevel stats.levels))
            (stats.params.map fun arg => arg.abstractList A.rule.binders))
          ((H.recInfos.map (·.motive)).map fun arg =>
            arg.abstractList A.rule.binders))
        ((H.recInfos.flatMap (·.minors)).map fun arg =>
          arg.abstractList A.rule.binders))
      ((VExpr.mkApps
          ((VExpr.const recursor.name
            (VLevel.params Us.length)).liftN
            (T.params ++ T.motives ++ T.minors).length 0)
          (bvarSpine
            (T.params ++ T.motives ++ T.minors).length)).liftN
        fieldDomains.length 0) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let recursor := (H.entries[selectedOwner]'F.entry_lt).2
  let parameterDecls := H.parameterSuffix.parameterDecls
  let canonicalDomains :=
    (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  let cachedDomains :=
    (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++ fieldDomains
  rcases A.installedRecursorParameterContext with ⟨T₀, hparams₀⟩
  rcases T₀.groupsResult_eq T with
    ⟨hparamsT, _hmotives, _hminors, _hindices, _hmajor, _hresult⟩
  rw [hparamsT] at hparams₀
  have hparams : VEnv.IsDefEqCtx H.outVEnv Us.length []
      T.params.reverse parameterDecls.toCtx := by
    simpa [parameterDecls, H.parameterDecls, Us] using hparams₀
  let commonPrefix :=
    fieldDomains.reverse ++ T.minors.reverse ++ T.motives.reverse
  have Hctx' : OnCtx (commonPrefix ++ parameterDecls.toCtx)
      (H.outVEnv.IsType Us.length) := by
    simpa [cachedDomains, commonPrefix, List.reverse_append,
      List.append_assoc] using Hctx
  have HcachedCanonical :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      (hparams.symm H.outVEnvWF.ordered) Hctx'
  have Hfull : VEnv.IsDefEqCtx H.outVEnv Us.length []
      canonicalDomains.reverse cachedDomains.reverse := by
    have := HcachedCanonical.symm H.outVEnvWF.ordered
    simpa [canonicalDomains, cachedDomains, commonPrefix,
      List.reverse_append, List.append_assoc] using this
  have HcanonicalCtx : OnCtx canonicalDomains.reverse
      (H.outVEnv.IsType Us.length) := Hfull.isType
  have Hcanonical := F.prefixResidualTranslation
    T fieldDomains hfields (by
      simpa [canonicalDomains] using HcanonicalCtx)
  have Hvlctx := abstractForallContext.isDefEq Hfull
  rcases Hcanonical.defeqDFC H.outVEnvWF Hvlctx with
    ⟨target', Hcached⟩
  let source :=
    mkAppN
      (mkAppN
        (mkAppN
          (.const F.semantic.generated.recursorName
            (AddInductive.getRecLevels H.elimLevel stats.levels))
          (stats.params.map fun arg => arg.abstractList A.rule.binders))
        ((H.recInfos.map (·.motive)).map fun arg =>
          arg.abstractList A.rule.binders))
      ((H.recInfos.flatMap (·.minors)).map fun arg =>
        arg.abstractList A.rule.binders)
  have hlength : canonicalDomains.length = cachedDomains.length := by
    simpa using Hfull.length_eq
  have HuniqueCtx := abstractForallContext.isUniqueCtx hlength
  have htarget := TrExprS.uniqueCtx (e := source) HuniqueCtx
    (by simpa [source, canonicalDomains] using Hcanonical)
    (by simpa [source, cachedDomains] using Hcached)
  rw [← htarget] at Hcached
  simpa [source, cachedDomains] using Hcached

/-- Complete recursive-call body translation and well-formedness, with the
selected motive application discharged from the independent canonical
inductive specification. -/
theorem
    RecursorCheck.RuleAlignment.RecursiveCallFrame.recursiveCallBodyWF
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.RuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallFrame j hj)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (B : A.FieldFrame :=
      Classical.choice A.fieldFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ (equationDomains localDomains : List VExpr)
        (prefixTarget : VExpr) (indexTargets : List VExpr)
        (majorTarget ownerTarget : VExpr),
      localDomains.length = F.semantic.generated.localArgs.size ∧
      equationDomains =
        H.parameterSuffix.parameterDecls.toCtx.reverse ++
          T.motives ++ T.minors ++
            (liftContextPrefix (T.motives ++ T.minors).length
              B.fieldDomains.reverse).reverse ∧
      equationDomains.length = A.rule.binders.length ∧
      OnCtx
        (abstractForallContext (equationDomains ++ localDomains) []).toCtx
        (H.outVEnv.IsType Us.length) ∧
      TrExprS H.outVEnv Us
        (abstractForallContext equationDomains [])
        ((F.semantic.generated.current.lctx.mkForall
          F.semantic.generated.localArgs (.sort .zero)).abstractList
            A.rule.binders)
        (VExpr.wrapForalls localDomains (.sort .zero)) ∧
      let args := indexTargets ++ [majorTarget]
      TrExprS H.outVEnv Us
          (abstractForallContext (equationDomains ++ localDomains) [])
          (F.semantic.generated.body.abstractList
        A.rule.binders F.semantic.generated.localArgs.size)
          (VExpr.mkApps prefixTarget args) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext (equationDomains ++ localDomains) [])
          (F.semantic.generated.outerAbstractedMajor A.rule.binders)
          majorTarget ∧
        TrExprS H.outVEnv Us
          (abstractForallContext (equationDomains ++ localDomains) [])
          (F.semantic.generated.outerAbstractedMotiveApp A.rule.binders)
          (VExpr.mkApps ownerTarget args) ∧
        H.outVEnv.HasType Us.length
          (abstractForallContext
            (equationDomains ++ localDomains) []).toCtx
          (VExpr.mkApps prefixTarget args)
          (VExpr.mkApps ownerTarget args) ∧
        H.outVEnv.HasType Us.length
          (abstractForallContext equationDomains []).toCtx
          (VExpr.wrapLams localDomains
            (VExpr.mkApps prefixTarget args))
          (VExpr.wrapForalls localDomains
            (VExpr.mkApps ownerTarget args)) ∧
        VExpr.WF H.outVEnv Us.length
          (abstractForallContext
            (equationDomains ++ localDomains) []).toCtx
          (VExpr.mkApps prefixTarget args) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let selectedOwner := F.semantic.generated.ownerIdx
  let parameterDecls := H.parameterSuffix.parameterDecls
  let sourceIndices :=
    (F.semantic.generated.exposedType.getAppArgs[stats.params.size:]).toList
  let localPrefix :=
    mkAppN
      (mkAppN
        (mkAppN
          (.const F.semantic.generated.recursorName
            (AddInductive.getRecLevels H.elimLevel stats.levels))
          stats.params)
        (H.recInfos.map (·.motive)))
      (H.recInfos.flatMap (·.minors))
  rcases F.insertedMajorTyping T (B := B) with
    ⟨C, equationDomains, fieldDomains, localDomains, added, frontDomains,
      indexTargets, majorTarget, ownerTarget, hdecomposition, hequation,
      hadded, hfront, hfields, hfixedFields, hlocal, hownerTarget, Hctx,
      HlocalTemplate, _HcanonicalCached, hindexCanonical, Hindices, Hmajor,
      _HmajorTyping, Hright⟩
  let recursor := (H.entries[selectedOwner]'F.entry_lt).2
  let outer := T.params ++ T.motives ++ T.minors
  let prefixBase :=
    (VExpr.mkApps
      ((VExpr.const recursor.name (VLevel.params Us.length)).liftN
        outer.length 0)
      (bvarSpine outer.length)).liftN fieldDomains.length 0
  let prefixTarget := prefixBase.liftN localDomains.length 0
  have hcallCtx :
      (abstractForallContext
        (equationDomains ++ localDomains) []).toCtx =
        (equationDomains ++ localDomains).reverse := by
    simpa [abstractForallContext] using
      VLCtx.toCtx_map_anonymousLams
        (equationDomains ++ localDomains).reverse
  have HctxPlain : OnCtx (equationDomains ++ localDomains).reverse
      (H.outVEnv.IsType Us.length) := by
    simpa only [hcallCtx] using Hctx
  have hequationLength : equationDomains.length = A.rule.binders.length := by
    have hcached := A.cachedEquationDomains_length T fieldDomains hfields
    simpa [hequation, H.parameterDecls, parameterDecls,
      List.append_assoc] using hcached
  have hequationFixed : equationDomains =
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse := by
    rw [hequation, hfixedFields]
  have HfieldCtx₀ := HctxPlain.drop localDomains.length
  have HfieldCtx : OnCtx
      (((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
        fieldDomains).reverse)
      (H.outVEnv.IsType Us.length) := by
    have HfieldCtx' : OnCtx equationDomains.reverse
        (H.outVEnv.IsType Us.length) := by
      simpa [List.reverse_append, List.drop_append,
        List.length_reverse] using HfieldCtx₀
    simpa [hequation, List.append_assoc] using HfieldCtx'
  have HprefixBase := F.cachedPrefixResidualTranslation
    T fieldDomains hfields HfieldCtx
  have HprefixBase' : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (mkAppN
        (mkAppN
          (mkAppN
            (.const F.semantic.generated.recursorName
              (AddInductive.getRecLevels H.elimLevel stats.levels))
            (stats.params.map fun arg =>
              arg.abstractList A.rule.binders))
          ((H.recInfos.map (·.motive)).map fun arg =>
            arg.abstractList A.rule.binders))
        ((H.recInfos.flatMap (·.minors)).map fun arg =>
          arg.abstractList A.rule.binders))
      prefixBase := by
    simpa [hequation, parameterDecls, outer, prefixBase,
      List.append_assoc] using HprefixBase
  have HprefixWeak := HprefixBase'.weakBV H.outVEnvWF.ordered
    (abstractForallContext.bvLift localDomains
      (abstractForallContext equationDomains []))
  have hprefixSource := F.outerAbstractedCommonPrefix_eq_lift
  dsimp only at hprefixSource
  have Hprefix : TrExprS H.outVEnv Us
      (abstractForallContext (equationDomains ++ localDomains) [])
      (localPrefix.abstractList A.rule.binders
        F.semantic.generated.localArgs.size) prefixTarget := by
    rw [hprefixSource]
    simpa [localPrefix, prefixTarget, prefixBase, outer, hlocal,
      abstractForallContext, List.reverse_append,
      List.append_assoc] using HprefixWeak
  let inserted := T.motives ++ T.minors
  let cachedBase := inserted.reverse ++ parameterDecls.toCtx
  have HcachedFull : OnCtx (frontDomains.reverse ++ cachedBase)
      (H.outVEnv.IsType Us.length) := by
    have Hctx' := HctxPlain
    rw [hdecomposition, hadded] at Hctx'
    simpa [cachedBase, inserted, List.reverse_append,
      List.append_assoc] using Hctx'
  rcases A.installedRecursorParameterContext with ⟨T₀, Hparams⟩
  rcases T₀.groupsResult_eq T with
    ⟨hparamsT, _hmotivesT, _hminorsT, _hindicesT,
      _hmajorT, _hresultT⟩
  rw [hparamsT] at Hparams
  have Hparams' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      T.params.reverse parameterDecls.toCtx := by
    simpa [parameterDecls, H.parameterDecls, Us] using Hparams
  have HcachedOuter : OnCtx cachedBase
      (H.outVEnv.IsType Us.length) := by
    have Hdropped := HcachedFull.drop frontDomains.length
    simpa [cachedBase, List.drop_append,
      List.length_reverse] using Hdropped
  have HcachedToTOuter :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      (Hparams'.symm H.outVEnvWF.ordered) HcachedOuter
  have HcachedToTFull :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      HcachedToTOuter HcachedFull
  have HcachedToT : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (frontDomains.reverse ++ cachedBase)
      (frontDomains.reverse ++ outer.reverse) := by
    simpa [cachedBase, inserted, outer, List.reverse_append,
      List.append_assoc] using HcachedToTFull
  have HTFull : OnCtx (frontDomains.reverse ++ outer.reverse)
      (H.outVEnv.IsType Us.length) :=
    (HcachedToT.symm H.outVEnvWF.ordered).isType
  let selectedOuter := F.telescope.params ++ F.telescope.motives ++
    F.telescope.minors
  have Hcommon := H.installedRecursorCommonPrefixContextAt
    owner howner selectedOwner F.entry_lt T F.telescope
  have HTToSelected :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      Hcommon HTFull
  have HselectedToCached : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (frontDomains.reverse ++ selectedOuter.reverse)
      (frontDomains.reverse ++ cachedBase) :=
    VEnv.IsDefEqCtx.trans_empty H.outVEnvWF
      (by simpa [outer, selectedOuter] using
        HTToSelected.symm H.outVEnvWF.ordered)
      (HcachedToT.symm H.outVEnvWF.ordered)
  let suffix := F.telescope.indices ++ F.telescope.major
  have HprefixT := F.prefixTypingInEquationContext T frontDomains (by
    simpa [outer, List.reverse_append, List.append_assoc] using HTFull)
  have HprefixT' : H.outVEnv.HasType Us.length
      (frontDomains.reverse ++ outer.reverse) prefixTarget
      ((VExpr.wrapForalls suffix F.telescope.result).liftN
        frontDomains.length 0) := by
    simpa [prefixTarget, prefixBase, outer, suffix, hfront,
      VExpr.liftN_liftN, List.length_append, Nat.add_comm,
      List.reverse_append, List.append_assoc] using HprefixT
  have HprefixSelected := HprefixT'.defeqDFC H.outVEnvWF.ordered
    HTToSelected
  rcases F.cachedPrefixOwnerTelescopeUnderFront
      frontDomains cachedBase prefixTarget HselectedToCached
      (by simpa [suffix, selectedOuter] using HprefixSelected) with
    ⟨motiveDomains, resultLevel, hdomainLength, _hmotive,
      HprefixExpected, HownerExpected, Hsame⟩
  let later := F.telescope.motives.drop (selectedOwner + 1) ++
    F.telescope.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  let expectedDomains :=
    (liftContextPrefix frontDomains.length expected.reverse).reverse
  have hexpectedLength : expectedDomains.length = indexTargets.length + 1 := by
    simp only [expectedDomains, List.length_reverse, liftContextPrefix_length,
      expected, liftContextPrefixAt_length, hdomainLength]
    have hcanonicalLength := C.indices_length
    omega
  have HprefixExpected' : H.outVEnv.HasType Us.length
      (abstractForallContext
        (equationDomains ++ localDomains) []).toCtx prefixTarget
      (VExpr.wrapForalls expectedDomains
        (F.telescope.result.liftN frontDomains.length suffix.length)) := by
    rw [hcallCtx, hdecomposition, hadded]
    simpa [cachedBase, inserted, expectedDomains, expected, later,
      suffix, List.reverse_append, List.append_assoc] using HprefixExpected
  have HownerExpected' : H.outVEnv.HasType Us.length
      (abstractForallContext
        (equationDomains ++ localDomains) []).toCtx ownerTarget
      (VExpr.wrapForalls expectedDomains (.sort resultLevel)) := by
    rw [hcallCtx, hdecomposition, hadded]
    rw [hownerTarget]
    simpa [cachedBase, inserted, expectedDomains, expected, later,
      suffix, List.reverse_append, List.append_assoc] using HownerExpected
  have Hsame' : SameTelescopeDomains expectedDomains.length
      (VExpr.wrapForalls expectedDomains
        (F.telescope.result.liftN frontDomains.length suffix.length))
      (VExpr.wrapForalls expectedDomains (.sort resultLevel)) := by
    simpa [expectedDomains, expected, later, suffix] using Hsame
  let args := indexTargets ++ [majorTarget]
  have hargsLength : args.length = expectedDomains.length := by
    simp [args, hexpectedLength]
  have HrightWF : VExpr.WF H.outVEnv Us.length
      (abstractForallContext
        (equationDomains ++ localDomains) []).toCtx
      (VExpr.mkApps ownerTarget args) := by
    refine ⟨.sort C.resultLevel, ?_⟩
    change H.outVEnv.HasType Us.length
      (abstractForallContext
        (equationDomains ++ localDomains) []).toCtx
      (VExpr.mkApps ownerTarget args) (.sort C.resultLevel)
    simpa [args, VExpr.mkApps_append, VExpr.mkApps] using Hright
  have hselectedMotiveBound :
      selectedOwner < (H.recInfos.map (·.motive)).size := by
    simpa [H.generated.length] using F.entry_lt
  have hselectedRecInfoBound : selectedOwner < H.recInfos.size := by
    simpa using hselectedMotiveBound
  have HcanonicalMotives := A.rule.abstractedMotivesTranslation
    (env := H.outVEnv) (Us := Us) equationDomains [] hequationLength
  have HmotiveBase :=
    List.forall₂_getElem HcanonicalMotives
      selectedOwner (by simpa using hselectedMotiveBound)
        (by simpa using hselectedMotiveBound)
  have HmotiveBase' : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (((H.recInfos.map
        (fun info : AddInductive.RecInfo => info.motive))[selectedOwner]!
          ).abstractList A.rule.binders)
      (.bvar (A.rule.binders.length - 1 -
        (A.rule.params_bound.fvars.length + selectedOwner))) := by
    have hmapMotive :
        (H.recInfos.map
          (fun info : AddInductive.RecInfo => info.motive))[selectedOwner]! =
          H.recInfos[selectedOwner].motive := by
      rw [getElem!_pos
        (H.recInfos.map
          (fun info : AddInductive.RecInfo => info.motive))
        selectedOwner hselectedMotiveBound]
      simp
    rw [hmapMotive]
    simpa using HmotiveBase
  have HmotiveWeak := HmotiveBase'.weakBV H.outVEnvWF.ordered
    (abstractForallContext.bvLift localDomains
      (abstractForallContext equationDomains []))
  rcases A.rule.motives_bound.getElem_eq_fvar
      selectedOwner hselectedMotiveBound with
    ⟨hselectedMotiveFVars, hselectedMotiveExpr⟩
  let motiveFVar := A.rule.motives_bound.fvars[selectedOwner]
  have hselectedRecInfo : selectedOwner < H.recInfos.size := by
    simpa using hselectedMotiveBound
  have hselectedMotiveValue :
      H.recInfos[selectedOwner].motive = .fvar motiveFVar := by
    simpa [motiveFVar] using hselectedMotiveExpr
  have hselectedMappedMotive :
      (H.recInfos.map (fun info : AddInductive.RecInfo => info.motive))[
        selectedOwner]! = .fvar motiveFVar := by
    rw [getElem!_pos
      (H.recInfos.map (fun info : AddInductive.RecInfo => info.motive))
      selectedOwner hselectedMotiveBound]
    simpa using hselectedMotiveValue
  have hselectedMotiveRuleRoot :
      motiveFVar ∈ A.rule.root.lctx.fvars := by
    rcases F.motiveLookup.rootBinding selectedOwner hselectedRecInfo with
      ⟨Hbinding⟩
    have hscope := Hbinding.motive.fvarsIn
    rw [getElem!_pos H.recInfos selectedOwner hselectedRecInfo,
      hselectedMotiveValue] at hscope
    change motiveFVar ∈ A.typing.context.mlctx.vlctx.fvars at hscope
    rw [← A.typing.context.lctx_eq,
      A.typing.context.mlctx_wf.tr.fvars_eq]
    exact hscope
  have hselectedMotiveRoot : motiveFVar ∈ F.originRoot.lctx.fvars :=
    F.originExtension.contextLE.fvars hselectedMotiveRuleRoot
  have hsourceMotiveHead :=
    F.semantic.generated.outerAbstractedRootFVar_eq_lift
      hselectedMotiveRoot A.rule.binders_nodup
  have hsourceMotiveHead' :
      (F.semantic.generated.replayTrace A.rule.binders).motive =
        (((H.recInfos.map
          (fun info : AddInductive.RecInfo => info.motive))[selectedOwner]!
            ).abstractList A.rule.binders).liftLooseBVars' 0
            F.semantic.generated.localArgs.size := by
    simpa [RecursiveCall.replayTrace,
      selectedOwner, hselectedMappedMotive,
      RecursorRuleSyntax.binders,
      List.append_assoc] using hsourceMotiveHead
  have hfrontLength : frontDomains.length =
      fieldDomains.length + localDomains.length := by
    rw [hfront]
    simp
  have hownerIndex :
      A.rule.binders.length - 1 -
          (A.rule.params_bound.fvars.length + selectedOwner) +
            localDomains.length =
        frontDomains.length +
          (F.telescope.motives.drop (selectedOwner + 1) ++
            F.telescope.minors).length := by
    have hparamsLength := A.rule.params_bound.length_fvars
    have hmotivesLength := A.rule.motives_bound.length_fvars
    have hminorsLength := A.rule.minors_bound.length_fvars
    have hfieldsLength := A.rule.all_args_bound.length_fvars
    unfold RecursorRuleSyntax.binders
    simp only [List.length_append, List.length_drop]
    rw [hmotivesLength, hminorsLength, hfieldsLength, hfrontLength, hfields,
      F.telescope.motives_length, F.telescope.minors_length]
    omega
  have htargetMotiveHead :
      (VExpr.bvar (A.rule.binders.length - 1 -
        (A.rule.params_bound.fvars.length + selectedOwner))).liftN
          localDomains.length 0 = ownerTarget := by
    rw [hownerTarget]
    simp only [VExpr.liftN, liftVar_base]
    congr 1
    simpa [Nat.add_comm] using hownerIndex
  have HmotiveHead : TrExprS H.outVEnv Us
      (abstractForallContext (equationDomains ++ localDomains) [])
      (F.semantic.generated.replayTrace A.rule.binders).motive
      ownerTarget := by
    rw [hsourceMotiveHead', ← htargetMotiveHead]
    simpa [hlocal, abstractForallContext, List.reverse_append,
      List.append_assoc] using HmotiveWeak
  have HmotiveArgs := List.Forall₂.append'
    Hindices (List.Forall₂.cons Hmajor List.Forall₂.nil)
  have HmotiveApplication₀ := checkPositivityStep.TrExprS.mkAppList
    H.outVEnvWF.ordered Hctx HmotiveHead HmotiveArgs HrightWF
  have HmotiveApplication : TrExprS H.outVEnv Us
      (abstractForallContext (equationDomains ++ localDomains) [])
      (F.semantic.generated.outerAbstractedMotiveApp A.rule.binders)
      (VExpr.mkApps ownerTarget args) := by
    have hreplayIndices :
        (F.semantic.generated.replayTrace A.rule.binders).indices.toList =
          sourceIndices.map fun index =>
            (index.abstractList
              F.semantic.generated.arguments_bound.fvars).abstractList
                A.rule.binders F.semantic.generated.localArgs.size := by
      simp [RecursiveCall.replayTrace, sourceIndices]
    unfold RecursiveCall.outerAbstractedMotiveApp
    rw [Expr.mkAppN_eq_mkAppList, hreplayIndices]
    simpa [Expr.mkAppList_append, args,
      VExpr.mkApps_append, VExpr.mkApps] using HmotiveApplication₀
  have HsameArgs : SameTelescopeDomains args.length
      (VExpr.wrapForalls expectedDomains
        (F.telescope.result.liftN frontDomains.length suffix.length))
      (VExpr.wrapForalls expectedDomains (.sort resultLevel)) := by
    simpa [hargsLength] using Hsame'
  have Hleft := VEnv.HasType.mkApps_sameTelescopeDomains_exact
    H.outVEnvWF Hctx HsameArgs HprefixExpected' HownerExpected' HrightWF
  have hselectedRecInfo : selectedOwner < H.recInfos.size := by
    simpa [H.generated.length] using F.entry_lt
  have hselectedMotive :
      selectedOwner < (H.recInfos.map (·.motive)).size := by
    simpa using hselectedRecInfo
  have hsuffixLength : suffix.length = expectedDomains.length := by
    simp only [suffix, expectedDomains, expected, List.length_append,
      List.length_reverse, liftContextPrefix_length,
      liftContextPrefixAt_length, F.telescope.indices_length,
      F.telescope.major_length, hdomainLength]
  have hexpectedArity :
      expectedDomains.length =
        H.recInfos[selectedOwner]!.indices.size + 1 := by
    rw [← hsuffixLength]
    simp [selectedOwner, suffix, F.telescope.indices_length,
      F.telescope.major_length]
  have hresultCanonical :
      F.telescope.result.liftN frontDomains.length suffix.length =
        VExpr.mkApps (ownerTarget.liftN expectedDomains.length 0)
          (bvarSpine expectedDomains.length) := by
    rw [F.telescope.resultShape hselectedMotive,
      concreteRecursorResultArgs_eq_bvarSpine]
    rw [VExpr.liftN_mkApps]
    rw [hsuffixLength]
    congr 1
    · rw [hownerTarget]
      simp only [VExpr.liftN]
      congr 1
      have hcut : expectedDomains.length ≤
          1 + H.recInfos[selectedOwner]!.indices.size +
            (H.recInfos.flatMap (·.minors)).size +
            ((H.recInfos.map (·.motive)).size - 1 - selectedOwner) := by
        rw [← hsuffixLength]
        simp only [suffix, List.length_append,
          F.telescope.indices_length, F.telescope.major_length]
        dsimp only [selectedOwner]
        omega
      rw [liftVar_le hcut]
      rw [liftVar_base]
      simp only [
        List.length_append, List.length_drop,
        F.telescope.minors_length, F.telescope.motives_length]
      omega
    · rw [hexpectedArity]
      exact bvarSpine_liftN_at_length _ _
  rw [hresultCanonical] at Hleft
  have htypeResult := VExpr.applyForallType_wrapForalls_bvarSpine
    expectedDomains args ownerTarget hargsLength
  rw [htypeResult] at Hleft
  have HleftWF : VExpr.WF H.outVEnv Us.length
      (abstractForallContext
        (equationDomains ++ localDomains) []).toCtx
      (VExpr.mkApps prefixTarget args) :=
    ⟨VExpr.mkApps ownerTarget args, Hleft⟩
  have Hclosed : H.outVEnv.HasType Us.length equationDomains.reverse
      (VExpr.wrapLams localDomains
        (VExpr.mkApps prefixTarget args))
      (VExpr.wrapForalls localDomains
        (VExpr.mkApps ownerTarget args)) := by
    apply VEnv.HasType.wrapLams
    · simpa [List.reverse_append] using HctxPlain
    · simpa [hcallCtx, List.reverse_append] using Hleft
  have Hclosed' : H.outVEnv.HasType Us.length
      (abstractForallContext equationDomains []).toCtx
      (VExpr.wrapLams localDomains
        (VExpr.mkApps prefixTarget args))
      (VExpr.wrapForalls localDomains
        (VExpr.mkApps ownerTarget args)) := by
    have hequationCtx :
        (abstractForallContext equationDomains []).toCtx =
          equationDomains.reverse := by
      simpa [abstractForallContext] using
        VLCtx.toCtx_map_anonymousLams equationDomains.reverse
    rw [hequationCtx]
    exact Hclosed
  have Hargs := List.Forall₂.append'
    Hindices (List.Forall₂.cons Hmajor List.Forall₂.nil)
  have Hcall := checkPositivityStep.TrExprS.mkAppList
    H.outVEnvWF.ordered Hctx Hprefix Hargs HleftWF
  have Hcall' : TrExprS H.outVEnv Us
      (abstractForallContext (equationDomains ++ localDomains) [])
      (F.semantic.generated.body.abstractList
        A.rule.binders F.semantic.generated.localArgs.size)
      (VExpr.mkApps prefixTarget args) := by
    have hrecursorShape :
        F.semantic.generated.outerAbstractedRecursor A.rule.binders =
          Expr.mkAppList
            (localPrefix.abstractList A.rule.binders
              F.semantic.generated.localArgs.size)
            (sourceIndices.map fun index =>
              (index.abstractList
                F.semantic.generated.arguments_bound.fvars).abstractList
                A.rule.binders
                  F.semantic.generated.localArgs.size) := by
      simpa [localPrefix, sourceIndices] using
        F.outerAbstractedRecursor_eq
    rw [F.semantic.generated.outerAbstractedBody_eq_named, hrecursorShape]
    have hsource : Expr.mkAppList
        (localPrefix.abstractList A.rule.binders
          F.semantic.generated.localArgs.size)
        ((sourceIndices.map fun index =>
          (index.abstractList
            F.semantic.generated.arguments_bound.fvars).abstractList
              A.rule.binders F.semantic.generated.localArgs.size) ++
          [F.semantic.generated.outerAbstractedMajor A.rule.binders]) =
        (Expr.mkAppList
          (localPrefix.abstractList A.rule.binders
            F.semantic.generated.localArgs.size)
          (sourceIndices.map fun index =>
            (index.abstractList
              F.semantic.generated.arguments_bound.fvars).abstractList
                A.rule.binders F.semantic.generated.localArgs.size)).app
          (F.semantic.generated.outerAbstractedMajor A.rule.binders) := by
      simp [Expr.mkAppList_append]
    rw [← hsource]
    simpa only [args] using Hcall
  exact ⟨equationDomains, localDomains, prefixTarget, indexTargets,
    majorTarget, ownerTarget, hlocal, hequationFixed, hequationLength,
    Hctx, HlocalTemplate, Hcall', Hmajor, HmotiveApplication, Hleft,
    Hclosed',
    HleftWF⟩

end VerifyInductive
end Lean4Lean
