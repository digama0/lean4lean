import Lean4Lean.Verify.Inductive.Rules.Rhs

/-! The left-hand side of a rule: the recursor applied to the parameter/motive/minor prefix, the
constructor indices and the constructor major, translated and typed in the cached equation
context and transported to the equation context of the right-hand side. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Canonical equation frame with the source recursor prefix translated and
the matching abstract prefix and constructor major already typed.  All
components share the same telescope witnesses, which is the handoff point
for consuming the target indices and major premise. -/
theorem
    RecursorInstallation.RuleAlignment.installedRecursorPrefixFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let recursor := H.entries[owner].2
    let parameterDecls :=
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type recursor.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ (originalDomains fieldDomains : List VExpr)
          (fieldResult introTarget : VExpr),
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          T.params.reverse parameterDecls.toCtx ∧
        originalDomains.length = A.rule.allArgs.size ∧
        fieldDomains =
          (liftContextPrefix (T.motives ++ T.minors).length
            originalDomains.reverse).reverse ∧
        TrExprS H.outVEnv Us parameterDecls
          A.typing.parameterTail
          (VExpr.wrapForalls originalDomains fieldResult) ∧
        OnCtx (originalDomains.reverse ++ T.params.reverse)
          (H.outVEnv.IsType Us.length) ∧
        fieldDomains.length = A.rule.allArgs.size ∧
        OnCtx
          (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
          (H.outVEnv.IsType Us.length) ∧
        H.outVEnv.HasType Us.length
          (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
          ((VExpr.mkApps
              (introTarget.liftN A.rule.allArgs.size 0)
              (bvarSpine A.rule.allArgs.size)).liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size)
          (fieldResult.liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size) ∧
        H.outVEnv.HasType Us.length
          (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
          ((VExpr.mkApps
              ((VExpr.const recursor.name
                (VLevel.params Us.length)).liftN
                (T.params ++ T.motives ++ T.minors).length 0)
              (bvarSpine
                (T.params ++ T.motives ++ T.minors).length)).liftN
            fieldDomains.length 0)
          ((VExpr.wrapForalls (T.indices ++ T.major) T.result).liftN
            fieldDomains.length 0) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
              fieldDomains) [])
          (A.rule.target.abstractList A.rule.binders)
          (fieldResult.liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size) ∧
        introTarget = VExpr.mkApps
          (.const
            ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
            (recursorDeclarationAbstractLevels c.lparams
              H.elimLevelAdmissible))
          (bvarSpine stats.params.size) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            ((T.params ++ T.motives ++ T.minors) ++ fieldDomains) [])
          (mkAppN
            (mkAppN
              (mkAppN
                (.const (Lean.mkRecName indTypes[owner]!.name)
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
            fieldDomains.length 0) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            ((T.params ++ T.motives ++ T.minors) ++ fieldDomains) [])
          (mkAppN
            (mkAppN
              (.const
                ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
                stats.levels)
              (stats.params.map fun arg =>
                arg.abstractList A.rule.binders))
            (A.rule.allArgs.map fun arg =>
              arg.abstractList A.rule.binders))
          ((VExpr.mkApps
              (introTarget.liftN A.rule.allArgs.size 0)
              (bvarSpine A.rule.allArgs.size)).liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let recursor := H.entries[owner].2
  let parameterDecls :=
    (R.recursorHeaders.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.installedRecursorPrefixEquationContextWithFrame with
    ⟨T, originalDomains, fieldDomains, fieldResult, introTarget,
      hparams, horiginal, hlifted, Htail, HoriginalCtx, hfields, Hctx, Hmajor, Hprefix,
      Htarget, HintroShape⟩
  have Htr := A.recursorPrefixResidualTranslation
    T fieldDomains hfields Hctx Hprefix
  have HmajorTr := A.constructorMajorResidualTranslation
    T fieldDomains fieldResult introTarget hfields Hctx Hmajor HintroShape
  exact ⟨T, originalDomains, fieldDomains, fieldResult, introTarget,
    hparams, horiginal, hlifted, Htail, HoriginalCtx, hfields, Hctx, Hmajor, Hprefix,
    Htarget, HintroShape, Htr, HmajorTr⟩

/-- Move the canonical recursor/constructor frame to the independently
cached parameter context.  Context conversion can in general choose a new
translation target; uniqueness of the closed rule binders shows that both
applications retain the exact abstract terms already typed by the recursor
and constructor phases. -/
theorem
    RecursorInstallation.RuleAlignment.installedCachedRecursorPrefixFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let recursor := H.entries[owner].2
    let parameterDecls :=
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type recursor.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ C : ClosedMotiveTelescope H.outVEnv Us stats decl
          owner H.recInfos[owner]! H.elimLevel,
      ∃ (originalDomains fieldDomains : List VExpr)
          (fieldResult introTarget : VExpr),
        let canonicalDomains :=
          (T.params ++ T.motives ++ T.minors) ++ fieldDomains
        let cachedDomains :=
          (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
            fieldDomains
        let added := T.motives ++ T.minors ++ fieldDomains
        let prefixSource :=
          mkAppN
            (mkAppN
              (mkAppN
                (.const (Lean.mkRecName indTypes[owner]!.name)
                  (AddInductive.getRecLevels H.elimLevel stats.levels))
                (stats.params.map fun arg =>
                  arg.abstractList A.rule.binders))
              ((H.recInfos.map (·.motive)).map fun arg =>
                arg.abstractList A.rule.binders))
            ((H.recInfos.flatMap (·.minors)).map fun arg =>
              arg.abstractList A.rule.binders)
        let prefixTarget :=
          (VExpr.mkApps
              ((VExpr.const recursor.name
                (VLevel.params Us.length)).liftN
                (T.params ++ T.motives ++ T.minors).length 0)
              (bvarSpine
                (T.params ++ T.motives ++ T.minors).length)).liftN
            fieldDomains.length 0
        let majorSource :=
          mkAppN
            (mkAppN
              (.const
                ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
                stats.levels)
              (stats.params.map fun arg =>
                arg.abstractList A.rule.binders))
            (A.rule.allArgs.map fun arg =>
              arg.abstractList A.rule.binders)
        let majorTarget :=
          (VExpr.mkApps
              (introTarget.liftN A.rule.allArgs.size 0)
              (bvarSpine A.rule.allArgs.size)).liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size
        ∃ (levels : List VLevel) (parameterTargets indexTargets : List VExpr),
          VEnv.IsDefEqCtx H.outVEnv Us.length []
            T.params.reverse parameterDecls.toCtx ∧
          VEnv.IsDefEqCtx H.outVEnv Us.length []
            C.params.reverse parameterDecls.toCtx ∧
          originalDomains.length = A.rule.allArgs.size ∧
          fieldDomains =
            (liftContextPrefix (T.motives ++ T.minors).length
              originalDomains.reverse).reverse ∧
          TrExprS H.outVEnv Us parameterDecls
            A.typing.parameterTail
            (VExpr.wrapForalls originalDomains fieldResult) ∧
          OnCtx (originalDomains.reverse ++ T.params.reverse)
            (H.outVEnv.IsType Us.length) ∧
          fieldDomains.length = A.rule.allArgs.size ∧
          VEnv.IsDefEqCtx H.outVEnv Us.length []
            canonicalDomains.reverse cachedDomains.reverse ∧
          OnCtx cachedDomains.reverse (H.outVEnv.IsType Us.length) ∧
          H.outVEnv.HasType Us.length cachedDomains.reverse majorTarget
            (fieldResult.liftN
              (T.motives ++ T.minors).length A.rule.allArgs.size) ∧
          H.outVEnv.HasType Us.length cachedDomains.reverse majorTarget
            (VExpr.mkApps (C.family.liftN added.length 0) indexTargets) ∧
          H.outVEnv.HasType Us.length cachedDomains.reverse prefixTarget
            ((VExpr.wrapForalls (T.indices ++ T.major) T.result).liftN
              fieldDomains.length 0) ∧
          TrExprS H.outVEnv Us (abstractForallContext cachedDomains [])
            (A.rule.target.abstractList A.rule.binders)
            (fieldResult.liftN
              (T.motives ++ T.minors).length A.rule.allArgs.size) ∧
          introTarget = VExpr.mkApps
            (.const
              ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
              (recursorDeclarationAbstractLevels c.lparams
                H.elimLevelAdmissible))
            (bvarSpine stats.params.size) ∧
          TrExprS H.outVEnv Us (abstractForallContext cachedDomains [])
            prefixSource prefixTarget ∧
          TrExprS H.outVEnv Us (abstractForallContext cachedDomains [])
            majorSource majorTarget ∧
          TrExprS H.outVEnv Us (abstractForallContext cachedDomains [])
            (H.recInfos[owner]!.motive.abstractList A.rule.binders)
            (.bvar (fieldDomains.length +
              (T.motives.drop (owner + 1) ++ T.minors).length)) ∧
          (fieldResult.liftN
              (T.motives ++ T.minors).length
              A.rule.allArgs.size).getAppFnArgs =
            (.const (decl.types[owner]'A.abstractOwner_lt).name levels,
              parameterTargets ++ indexTargets) ∧
          stats.levels.mapM (VLevel.ofLevel Us) = some levels ∧
          levels = recursorDeclarationAbstractLevels c.lparams
            H.elimLevelAdmissible ∧
          List.Forall₂
            (TrExprS H.outVEnv Us
              (abstractForallContext cachedDomains []))
            ((stats.params.map fun arg =>
              arg.abstractList A.rule.binders).toList)
            parameterTargets ∧
          parameterTargets =
            (List.ofFn fun i : Fin stats.params.size =>
              VExpr.bvar (A.rule.binders.length - 1 - i)) ∧
          (let familyTarget :=
              VExpr.mkApps
                (.const (decl.types[owner]'A.abstractOwner_lt).name levels)
                parameterTargets
            let added := T.motives ++ T.minors ++ fieldDomains
            ∃ familyType,
              familyTarget = C.family.liftN added.length 0 ∧
              (fieldResult.liftN
                  (T.motives ++ T.minors).length
                  A.rule.allArgs.size) =
                VExpr.mkApps familyTarget indexTargets ∧
              H.outVEnv.HasType Us.length cachedDomains.reverse
                familyTarget familyType) ∧
          indexTargets.length = T.indices.length ∧
          indexTargets.length = C.indices.length ∧
          (let ownerTarget := .bvar
             (fieldDomains.length +
               (T.motives.drop (owner + 1) ++ T.minors).length)
           H.outVEnv.HasType Us.length cachedDomains.reverse
              (.app (VExpr.mkApps ownerTarget indexTargets) majorTarget)
              (.sort C.resultLevel)) ∧
          List.Forall₂
            (TrExprS H.outVEnv Us
              (abstractForallContext cachedDomains []))
            (((AddInductive.getIIndices stats A.rule.target).2.map fun arg =>
              arg.abstractList A.rule.binders).toList)
            indexTargets := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let recursor := H.entries[owner].2
  let parameterDecls :=
    (R.recursorHeaders.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.installedRecursorPrefixFrame with
    ⟨T, originalDomains, fieldDomains, fieldResult, introTarget,
      hparams, horiginal, hlifted, Htail, HoriginalCtx, hfields, Hctx, Hmajor, Hprefix,
      Htarget, HintroShape, HprefixTr, HmajorTr⟩
  rcases H.installedOwnerMotiveDomainAt owner howner with
    ⟨T₀, S, hgeneratedSource, HmotiveDomain₀⟩
  rcases T₀.groupsResult_eq T with
    ⟨hparams₀, hmotives₀, _hminors₀, _hindices₀, _hmajor₀, _hresult₀⟩
  rw [hparams₀] at hgeneratedSource
  rw [hparams₀, hmotives₀] at HmotiveDomain₀
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  let C := S.canonical.mono hbase
  have hcanonicalSource : VEnv.IsDefEqCtx H.outVEnv Us.length []
      C.params.reverse S.motiveSourceScope.toCtx := by
    simpa [C, ClosedMotiveTelescope.mono] using
      S.motiveSourceAlignment.mono hbase
  have hcanonicalGenerated : VEnv.IsDefEqCtx H.outVEnv Us.length []
      C.params.reverse T.params.reverse :=
    VEnv.IsDefEqCtx.trans_empty H.outVEnvWF
      hcanonicalSource
      (hgeneratedSource.symm H.outVEnvWF.ordered)
  have hcanonicalParams : VEnv.IsDefEqCtx H.outVEnv Us.length []
      C.params.reverse parameterDecls.toCtx :=
    VEnv.IsDefEqCtx.trans_empty H.outVEnvWF
      hcanonicalGenerated hparams
  have HmotiveDomain : H.outVEnv.IsDefEqU Us.length
      (abstractForallContext
        (T.params ++ T.motives.take owner) []).toCtx
      T.motives[owner]!
      (C.motiveType.liftN (T.motives.take owner).length 0) := by
    simpa [C, ClosedMotiveTelescope.mono] using HmotiveDomain₀
  let canonicalDomains :=
    (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  let cachedDomains :=
    (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
      fieldDomains
  let commonPrefix :=
    fieldDomains.reverse ++ T.minors.reverse ++ T.motives.reverse
  have Hctx' : OnCtx (commonPrefix ++ T.params.reverse)
      (H.outVEnv.IsType Us.length) := by
    simpa [canonicalDomains, commonPrefix, List.reverse_append,
      List.append_assoc] using Hctx
  have Hfull₀ :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      hparams Hctx'
  have Hfull : VEnv.IsDefEqCtx H.outVEnv Us.length []
      canonicalDomains.reverse cachedDomains.reverse := by
    simpa [canonicalDomains, cachedDomains, commonPrefix,
      List.reverse_append, List.append_assoc] using Hfull₀
  have HcachedCtx : OnCtx cachedDomains.reverse
      (H.outVEnv.IsType Us.length) :=
    (Hfull.symm H.outVEnvWF.ordered).isType
  have HmajorCached := Hmajor.defeqDFC H.outVEnvWF.ordered Hfull
  have HprefixCached := Hprefix.defeqDFC H.outVEnvWF.ordered Hfull
  have Hvlctx := abstractForallContext.isDefEq Hfull
  have hdomainLengths : canonicalDomains.length = cachedDomains.length := by
    simpa using Hfull.length_eq
  have HuniqueCtx := abstractForallContext.isUniqueCtx hdomainLengths
  let prefixSource :=
    mkAppN
      (mkAppN
        (mkAppN
          (.const (Lean.mkRecName indTypes[owner]!.name)
            (AddInductive.getRecLevels H.elimLevel stats.levels))
          (stats.params.map fun arg =>
            arg.abstractList A.rule.binders))
        ((H.recInfos.map (·.motive)).map fun arg =>
          arg.abstractList A.rule.binders))
      ((H.recInfos.flatMap (·.minors)).map fun arg =>
        arg.abstractList A.rule.binders)
  let prefixTarget :=
    (VExpr.mkApps
        ((VExpr.const recursor.name
          (VLevel.params Us.length)).liftN
          (T.params ++ T.motives ++ T.minors).length 0)
        (bvarSpine
          (T.params ++ T.motives ++ T.minors).length)).liftN
      fieldDomains.length 0
  rcases HprefixTr.defeqDFC H.outVEnvWF Hvlctx with
    ⟨prefixTarget', HprefixTr'⟩
  have hprefixTarget : prefixTarget = prefixTarget' :=
    HprefixTr.uniqueCtx HuniqueCtx HprefixTr'
  rw [← hprefixTarget] at HprefixTr'
  let majorSource :=
    mkAppN
      (mkAppN
        (.const
          ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
          stats.levels)
        (stats.params.map fun arg =>
          arg.abstractList A.rule.binders))
      (A.rule.allArgs.map fun arg =>
        arg.abstractList A.rule.binders)
  let majorTarget :=
    (VExpr.mkApps
        (introTarget.liftN A.rule.allArgs.size 0)
        (bvarSpine A.rule.allArgs.size)).liftN
      (T.motives ++ T.minors).length A.rule.allArgs.size
  rcases HmajorTr.defeqDFC H.outVEnvWF Hvlctx with
    ⟨majorTarget', HmajorTr'⟩
  have hmajorTarget : majorTarget = majorTarget' :=
    HmajorTr.uniqueCtx HuniqueCtx HmajorTr'
  rw [← hmajorTarget] at HmajorTr'
  rcases A.cachedConstructorIndexSpineOfTarget
      T fieldDomains fieldResult Htarget with
    ⟨levels, parameterTargets, indexTargets, hspine, hlevels,
      HparameterTargets, hindexLength, HindexTargets⟩
  have hcanonicalLevels := R.recursorHeaders.recursorLevelTranslation
    H.lparamsNodup H.elimLevelAdmissible
  have hlevelsCanonical : levels =
      recursorDeclarationAbstractLevels c.lparams
        H.elimLevelAdmissible := by
    exact Option.some.inj (hlevels.symm.trans hcanonicalLevels)
  rcases A.equationBinderTranslations T fieldDomains hfields with
    ⟨HcanonicalParameters, HcanonicalMotives, _HcanonicalMinors,
      _HcanonicalFields⟩
  have hownerRecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hownerMotive : owner < (H.recInfos.map (·.motive)).size := by
    simpa using hownerRecInfo
  have hownerBang : H.recInfos[owner]! = H.recInfos[owner] := by
    simp [hownerRecInfo]
  have HownerMotive :=
    List.forall₂_getElem HcanonicalMotives owner
      (by simpa using hownerMotive) (by simpa using hownerMotive)
  have HownerMotiveCanonical : TrExprS H.outVEnv Us
      (abstractForallContext canonicalDomains [])
      (H.recInfos[owner]!.motive.abstractList A.rule.binders)
      (.bvar (A.rule.binders.length - 1 -
        (A.rule.params_bound.fvars.length + owner))) := by
    simpa [canonicalDomains, List.append_assoc, hownerBang] using
      HownerMotive
  rcases HownerMotiveCanonical.defeqDFC H.outVEnvWF Hvlctx with
    ⟨ownerMotiveTarget, HownerMotiveCached⟩
  have hownerMotiveTarget :
      VExpr.bvar (A.rule.binders.length - 1 -
          (A.rule.params_bound.fvars.length + owner)) =
        ownerMotiveTarget :=
    HownerMotiveCanonical.uniqueCtx HuniqueCtx HownerMotiveCached
  rw [← hownerMotiveTarget] at HownerMotiveCached
  rw [A.ownerMotiveBvarIndex T fieldDomains hfields] at HownerMotiveCached
  have HownerMotive' : TrExprS H.outVEnv Us
      (abstractForallContext cachedDomains [])
      (H.recInfos[owner]!.motive.abstractList A.rule.binders)
      (.bvar (fieldDomains.length +
        (T.motives.drop (owner + 1) ++ T.minors).length)) := by
    exact HownerMotiveCached
  have hparameterTargets : parameterTargets =
      (List.ofFn fun i : Fin stats.params.size =>
        VExpr.bvar (A.rule.binders.length - 1 - i)) := by
    exact (Lean4Lean.VerifyInductive.TrExprS.forall₂_unique HuniqueCtx
      HcanonicalParameters
      HparameterTargets).symm
  let familyTarget := VExpr.mkApps
    (.const (decl.types[owner]'A.abstractOwner_lt).name levels)
    parameterTargets
  let added := T.motives ++ T.minors ++ fieldDomains
  have hcanonicalFamilyLevels : C.levels = levels := by
    exact Option.some.inj (C.levels_translation.symm.trans hlevels)
  have hbindersLength : A.rule.binders.length =
      stats.params.size + added.length := by
    have hdomains := A.canonicalEquationDomains_length
      T fieldDomains hfields
    simp only [added, List.length_append,
      T.params_length] at hdomains ⊢
    omega
  have hparameterTargetsLifted : parameterTargets =
      (bvarSpine stats.params.size).map
        (fun arg => arg.liftN added.length 0) := by
    rw [hparameterTargets,
      bvarSpine_liftN_zero_eq_ofFn]
    apply List.ext_getElem
    · simp
    · intro j hleft hright
      have hj : j < stats.params.size := by simpa using hright
      simp only [List.getElem_ofFn]
      congr 1
      omega
  have hfamilyTargetCanonical :
      familyTarget = C.family.liftN added.length 0 := by
    dsimp only [familyTarget]
    rw [C.family_eq]
    simp only [C.params_length, VExpr.liftN_mkApps]
    rw [hcanonicalFamilyLevels, hparameterTargetsLifted]
    simp [VExpr.liftN]
  have hfamilyApplication :
      (fieldResult.liftN
          (T.motives ++ T.minors).length A.rule.allArgs.size) =
        VExpr.mkApps familyTarget indexTargets := by
    have hrebuild := VExpr.mkApps_getAppFnArgs
      (fieldResult.liftN
        (T.motives ++ T.minors).length A.rule.allArgs.size)
    rw [hspine] at hrebuild
    simpa [familyTarget, VExpr.mkApps_append] using hrebuild.symm
  have HmajorCanonical : H.outVEnv.HasType Us.length cachedDomains.reverse
      majorTarget
      (VExpr.mkApps (C.family.liftN added.length 0) indexTargets) := by
    rw [← hfamilyTargetCanonical, ← hfamilyApplication]
    exact HmajorCached
  have hindexCanonical : indexTargets.length = C.indices.length := by
    rw [hindexLength, T.indices_length, C.indices_length]
  let ownerTarget : VExpr := .bvar
    (fieldDomains.length +
      (T.motives.drop (owner + 1) ++ T.minors).length)
  let newer := T.motives.drop owner ++ T.minors ++ fieldDomains
  have hownerT : owner < T.motives.length := by
    rw [T.motives_length]
    simpa using hownerMotive
  have htoCtx : ∀ types : List VExpr,
      VLCtx.toCtx (types.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) = types := by
    intro types
    induction types with
    | nil => rfl
    | cons type types ih => simp [VLCtx.toCtx, ih]
  have hearlierCtx :
      (abstractForallContext
        (T.params ++ T.motives.take owner) []).toCtx =
        (T.params ++ T.motives.take owner).reverse := by
    simpa [abstractForallContext] using
      htoCtx ((T.params ++ T.motives.take owner).reverse)
  have hcanonicalSplit : canonicalDomains.reverse =
      newer.reverse ++
        (T.params ++ T.motives.take owner).reverse := by
    dsimp only [canonicalDomains, newer]
    have hmotives : T.motives =
        T.motives.take owner ++ T.motives.drop owner :=
      (List.take_append_drop owner T.motives).symm
    have hmotivesReverse : T.motives.reverse =
        (T.motives.drop owner).reverse ++
          (T.motives.take owner).reverse := by
      calc
        T.motives.reverse =
            (T.motives.take owner ++ T.motives.drop owner).reverse :=
          congrArg List.reverse hmotives
        _ = (T.motives.drop owner).reverse ++
            (T.motives.take owner).reverse :=
          by simp only [List.reverse_append]
    simp only [List.reverse_append]
    rw [hmotivesReverse]
    simp only [List.append_assoc]
  have Wmotive : Ctx.LiftN newer.length 0
      (abstractForallContext
        (T.params ++ T.motives.take owner) []).toCtx
      canonicalDomains.reverse := by
    rw [hearlierCtx, hcanonicalSplit]
    exact .zero newer.reverse (by simp)
  have HmotiveDomainFull := HmotiveDomain.weakN
    H.outVEnvWF.ordered Wmotive
  have hcanonicalLift :
      (T.motives.take owner).length + newer.length = added.length := by
    simp only [newer, added, List.length_append, List.length_take,
      List.length_drop]
    omega
  have HmotiveDomainCanonical : H.outVEnv.IsDefEqU Us.length
      canonicalDomains.reverse
      (T.motives[owner]!.liftN newer.length 0)
      (C.motiveType.liftN added.length 0) := by
    simpa only [VExpr.liftN_liftN, hcanonicalLift] using
      HmotiveDomainFull
  have HownerOuter := T.ownerMotiveOuterBvarTyping hownerT
  have Wfields : Ctx.LiftN fieldDomains.length 0
      (T.params ++ T.motives ++ T.minors).reverse
      canonicalDomains.reverse := by
    have hcanonicalFields : canonicalDomains.reverse =
        fieldDomains.reverse ++
          (T.params ++ T.motives ++ T.minors).reverse := by
      simp [canonicalDomains, List.reverse_append, List.append_assoc]
    rw [hcanonicalFields]
    exact Ctx.LiftN.zero (n := fieldDomains.length)
      (Γ := (T.params ++ T.motives ++ T.minors).reverse)
      fieldDomains.reverse (by simp)
  have HownerCanonical := HownerOuter.weakN H.outVEnvWF.ordered Wfields
  have HownerCanonical' : H.outVEnv.HasType Us.length
      canonicalDomains.reverse ownerTarget
      (T.motives[owner]!.liftN newer.length 0) := by
    let later := T.motives.drop (owner + 1) ++ T.minors
    have hownerTargetEq :
        (VExpr.bvar later.length).liftN fieldDomains.length 0 =
          ownerTarget := by
      simp only [ownerTarget, later, VExpr.liftN, liftVar_base,
        List.length_append]
    have hownerGet : T.motives[owner]'hownerT = T.motives[owner]! :=
      (getElem!_pos T.motives owner hownerT).symm
    have hownerTypeEq :
        ((T.motives[owner]'hownerT).liftN (later.length + 1) 0).liftN
            fieldDomains.length 0 =
          T.motives[owner]!.liftN newer.length 0 := by
      rw [hownerGet, VExpr.liftN_liftN]
      have hlength : later.length + 1 + fieldDomains.length =
          newer.length := by
        dsimp only [later, newer]
        simp only [List.length_append, List.length_drop]
        omega
      rw [hlength]
    rw [hownerTargetEq, hownerTypeEq] at HownerCanonical
    exact HownerCanonical
  have HownerCached := HownerCanonical'.defeqDFC
    H.outVEnvWF.ordered Hfull
  have HmotiveDomainCached := HmotiveDomainCanonical.defeqDFC
    H.outVEnvWF.ordered Hfull
  have HmotiveCanonical : H.outVEnv.HasType Us.length
      cachedDomains.reverse ownerTarget
      (C.motiveType.liftN added.length 0) :=
    HownerCached.defeqU_r H.outVEnvWF HcachedCtx HmotiveDomainCached
  have HapplyCanonical : H.outVEnv.HasType Us.length cachedDomains.reverse
      (.app (VExpr.mkApps ownerTarget indexTargets) majorTarget)
      (.sort C.resultLevel) := by
    have Happ := C.applyMajorTypedAfterDefEq H.outVEnvWF
      parameterDecls.toCtx added hcanonicalParams
      (by simpa [cachedDomains, added, List.reverse_append,
        List.append_assoc] using HcachedCtx)
      indexTargets hindexCanonical ownerTarget majorTarget
      (by simpa [cachedDomains, added, List.reverse_append,
        List.append_assoc] using HmotiveCanonical)
      (by simpa [cachedDomains, added, List.reverse_append,
        List.append_assoc] using HmajorCanonical)
    simpa [cachedDomains, added, List.reverse_append,
      List.append_assoc] using Happ
  have HfieldResultType := HmajorCached.isType H.outVEnvWF HcachedCtx
  have HfieldResultWF : VExpr.WF H.outVEnv Us.length cachedDomains.reverse
      (fieldResult.liftN
        (T.motives ++ T.minors).length A.rule.allArgs.size) := by
    rcases HfieldResultType with ⟨fieldLevel, HfieldResultType⟩
    exact ⟨.sort fieldLevel, HfieldResultType⟩
  rw [hfamilyApplication] at HfieldResultWF
  rcases VExpr.WF.mkApps_fn H.outVEnvWF.orderedStrong HcachedCtx
      HfieldResultWF with ⟨familyType, Hfamily⟩
  exact ⟨T, C, originalDomains, fieldDomains, fieldResult, introTarget,
    levels, parameterTargets, indexTargets, hparams, hcanonicalParams,
    horiginal, hlifted, Htail, HoriginalCtx, hfields,
    Hfull, HcachedCtx,
    HmajorCached, HmajorCanonical, HprefixCached, Htarget, HintroShape,
    HprefixTr',
    HmajorTr', HownerMotive', hspine, hlevels, hlevelsCanonical,
    HparameterTargets, hparameterTargets,
    (by exact ⟨familyType, hfamilyTargetCanonical,
      hfamilyApplication, Hfamily⟩),
    hindexLength, hindexCanonical, HapplyCanonical, HindexTargets⟩

/-- Complete cached equation left-hand side.  The translated recursor prefix
is applied to the independently recovered constructor indices and major;
canonical-result instantiation identifies its exact type with the parallel
owner-motive application. -/
theorem
    RecursorInstallation.RuleAlignment.installedCachedLhsBodyWithFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ originalDomains fieldDomains fieldResult lhsBody typeBody,
        let cachedDomains :=
          (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
            fieldDomains
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          T.params.reverse parameterDecls.toCtx ∧
        originalDomains.length = A.rule.allArgs.size ∧
        fieldDomains =
          (liftContextPrefix (T.motives ++ T.minors).length
            originalDomains.reverse).reverse ∧
        TrExprS H.outVEnv Us parameterDecls
          A.typing.parameterTail
          (VExpr.wrapForalls originalDomains fieldResult) ∧
        OnCtx (originalDomains.reverse ++ T.params.reverse)
          (H.outVEnv.IsType Us.length) ∧
        fieldDomains.length = A.rule.allArgs.size ∧
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
          cachedDomains.reverse ∧
        OnCtx cachedDomains.reverse (H.outVEnv.IsType Us.length) ∧
        TrExprS H.outVEnv Us (abstractForallContext cachedDomains [])
          (A.rule.sourceLhsBody.abstractList A.rule.binders) lhsBody ∧
        H.outVEnv.HasType Us.length cachedDomains.reverse lhsBody typeBody ∧
        H.outVEnv.IsType Us.length cachedDomains.reverse typeBody ∧
        TrExprS H.outVEnv Us (abstractForallContext cachedDomains [])
          ((Expr.app
            (mkAppN H.recInfos[owner]!.motive
              (AddInductive.getIIndices stats A.rule.target).2)
            A.rule.sourceConstructorMajor).abstractList A.rule.binders)
          typeBody := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.recursorHeaders.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.installedCachedRecursorPrefixFrame with
    ⟨T, C, originalDomains, fieldDomains, fieldResult, introTarget,
      levels, parameterTargets, indexTargets, hparams, hcanonicalParams,
      horiginal, hlifted, Htail, HoriginalCtx, hfields, Hfull, HcachedCtx,
      HmajorCached, HmajorCanonical, HprefixCached,
      Htarget, HintroShape, HprefixTr, HmajorTr, HownerMotiveTr, hspine,
      hlevels, hlevelsCanonical, HparameterTargets, hparameterTargets,
      Hfamily, hindexLength, hindexCanonical, HapplyCanonical,
      HindexTargets⟩
  let cachedDomains :=
    (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
      fieldDomains
  let prefixSource :=
    mkAppN
      (mkAppN
        (mkAppN
          (.const (Lean.mkRecName indTypes[owner]!.name)
            (AddInductive.getRecLevels H.elimLevel stats.levels))
          (stats.params.map fun arg =>
            arg.abstractList A.rule.binders))
        ((H.recInfos.map (·.motive)).map fun arg =>
          arg.abstractList A.rule.binders))
      ((H.recInfos.flatMap (·.minors)).map fun arg =>
        arg.abstractList A.rule.binders)
  let prefixTarget :=
    (VExpr.mkApps
        ((VExpr.const H.entries[owner].2.name
          (VLevel.params Us.length)).liftN
          (T.params ++ T.motives ++ T.minors).length 0)
        (bvarSpine
          (T.params ++ T.motives ++ T.minors).length)).liftN
      fieldDomains.length 0
  let majorSource :=
    mkAppN
      (mkAppN
        (.const
          ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
          stats.levels)
        (stats.params.map fun arg =>
          arg.abstractList A.rule.binders))
      (A.rule.allArgs.map fun arg =>
        arg.abstractList A.rule.binders)
  let majorTarget :=
    (VExpr.mkApps
        (introTarget.liftN A.rule.allArgs.size 0)
        (bvarSpine A.rule.allArgs.size)).liftN
      (T.motives ++ T.minors).length A.rule.allArgs.size
  let ownerTarget : VExpr := .bvar
    (fieldDomains.length +
      (T.motives.drop (owner + 1) ++ T.minors).length)
  let args := indexTargets ++ [majorTarget]
  let lhsBody := VExpr.mkApps prefixTarget args
  let typeBody := VExpr.mkApps ownerTarget args
  rcases RecursorInstallation.RuleAlignment.installedCachedPrefixOwnerTelescope
    (H := H) T fieldDomains prefixTarget
      Hfull HcachedCtx HprefixCached with
    ⟨motiveDomains, resultLevel, hdomainLength, hmotive,
      HprefixExpected, HownerExpected, Hsame⟩
  let suffix := T.indices ++ T.major
  let later := T.motives.drop (owner + 1) ++ T.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  let expectedDomains :=
    (liftContextPrefix fieldDomains.length expected.reverse).reverse
  have hargsLength : args.length = expectedDomains.length := by
    simp only [args, expectedDomains, expected, List.length_append,
      List.length_singleton, List.length_reverse, liftContextPrefix_length,
      liftContextPrefixAt_length, hindexLength, T.indices_length,
      hdomainLength]
  have Hsame' : SameTelescopeDomains args.length
      (VExpr.wrapForalls expectedDomains
        (T.result.liftN fieldDomains.length suffix.length))
      (VExpr.wrapForalls expectedDomains (.sort resultLevel)) := by
    simpa [suffix, later, expected, expectedDomains, hargsLength] using Hsame
  have HrightWF : VExpr.WF H.outVEnv Us.length cachedDomains.reverse
      (VExpr.mkApps ownerTarget args) := by
    refine ⟨.sort C.resultLevel, ?_⟩
    change H.outVEnv.HasType Us.length cachedDomains.reverse
      (VExpr.mkApps ownerTarget args) (.sort C.resultLevel)
    have hshape : VExpr.mkApps ownerTarget args =
        .app (VExpr.mkApps ownerTarget indexTargets) majorTarget := by
      simp [args, VExpr.mkApps]
    rw [hshape]
    simpa only [Us, cachedDomains, parameterDecls, ownerTarget,
      majorTarget, List.reverse_append, List.reverse_reverse,
      List.append_assoc] using HapplyCanonical
  have Hlhs := VEnv.HasType.mkApps_sameTelescopeDomains_exact
    H.outVEnvWF HcachedCtx Hsame' HprefixExpected HownerExpected HrightWF
  have hownerRecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hownerMotive : owner < (H.recInfos.map (·.motive)).size := by
    simpa using hownerRecInfo
  have hsuffixLength : suffix.length = expectedDomains.length := by
    simp only [suffix, expectedDomains, expected, List.length_append,
      List.length_reverse, liftContextPrefix_length,
      liftContextPrefixAt_length, T.indices_length, T.major_length,
      hdomainLength]
  have hexpectedArity :
      expectedDomains.length = H.recInfos[owner]!.indices.size + 1 := by
    rw [← hsuffixLength]
    simp [suffix, T.indices_length, T.major_length]
  have hresultCanonical : T.result.liftN fieldDomains.length suffix.length =
      VExpr.mkApps (ownerTarget.liftN expectedDomains.length 0)
        (bvarSpine expectedDomains.length) := by
    rw [T.resultShape hownerMotive,
      concreteRecursorResultArgs_eq_bvarSpine]
    rw [VExpr.liftN_mkApps]
    rw [hsuffixLength]
    congr 1
    · simp only [ownerTarget, VExpr.liftN]
      congr 1
      have hcut : expectedDomains.length ≤
          1 + H.recInfos[owner]!.indices.size +
            (H.recInfos.flatMap (·.minors)).size +
            ((H.recInfos.map (·.motive)).size - 1 - owner) := by
        rw [← hsuffixLength]
        simp only [suffix, List.length_append, T.indices_length,
          T.major_length]
        omega
      rw [liftVar_le hcut]
      rw [liftVar_base]
      simp only [
        List.length_append, List.length_drop,
        T.minors_length, T.motives_length]
      omega
    · rw [hexpectedArity]
      exact bvarSpine_liftN_at_length _ _
  rw [hresultCanonical] at Hlhs
  have htypeResult := VExpr.applyForallType_wrapForalls_bvarSpine
    expectedDomains args ownerTarget hargsLength
  rw [htypeResult] at Hlhs
  have Hlhs' : H.outVEnv.HasType Us.length cachedDomains.reverse
      lhsBody typeBody := by
    simpa only [Us, cachedDomains, parameterDecls, lhsBody, typeBody,
      List.reverse_append, List.append_assoc] using Hlhs
  have HtypeBody : H.outVEnv.IsType Us.length cachedDomains.reverse
      typeBody := by
    refine ⟨C.resultLevel, ?_⟩
    change H.outVEnv.HasType Us.length cachedDomains.reverse
      typeBody (.sort C.resultLevel)
    have hshape : typeBody =
        .app (VExpr.mkApps ownerTarget indexTargets) majorTarget := by
      simp [typeBody, args, VExpr.mkApps_append, VExpr.mkApps]
    rw [hshape]
    simpa only [Us, cachedDomains, parameterDecls, ownerTarget,
      majorTarget, List.reverse_append, List.reverse_reverse,
      List.append_assoc] using HapplyCanonical
  have HargsTr := List.Forall₂.append'
    HindexTargets (List.Forall₂.cons HmajorTr List.Forall₂.nil)
  have HlhsWF : VExpr.WF H.outVEnv Us.length cachedDomains.reverse
      lhsBody := ⟨typeBody, Hlhs'⟩
  have htoCtx : ∀ types : List VExpr,
      VLCtx.toCtx (types.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) = types := by
    intro types
    induction types with
    | nil => rfl
    | cons type types ih => simp [VLCtx.toCtx, ih]
  have HabstractCtx : OnCtx
      (abstractForallContext cachedDomains []).toCtx
      (H.outVEnv.IsType Us.length) := by
    have habstractToCtx :
        (abstractForallContext cachedDomains []).toCtx =
          cachedDomains.reverse := by
      simpa [abstractForallContext] using htoCtx cachedDomains.reverse
    rw [habstractToCtx]
    exact HcachedCtx
  have HlhsWF' : VExpr.WF H.outVEnv Us.length
      (abstractForallContext cachedDomains []).toCtx lhsBody := by
    have habstractToCtx :
        (abstractForallContext cachedDomains []).toCtx =
          cachedDomains.reverse := by
      simpa [abstractForallContext] using htoCtx cachedDomains.reverse
    rw [habstractToCtx]
    exact HlhsWF
  have HrightWF' : VExpr.WF H.outVEnv Us.length
      (abstractForallContext cachedDomains []).toCtx
      (VExpr.mkApps ownerTarget args) := by
    have habstractToCtx :
        (abstractForallContext cachedDomains []).toCtx =
          cachedDomains.reverse := by
      simpa [abstractForallContext] using htoCtx cachedDomains.reverse
    rw [habstractToCtx]
    exact HrightWF
  have HlhsTr := checkPositivityStep.TrExprS.mkAppList
    H.outVEnvWF.orderedStrong HabstractCtx HprefixTr HargsTr (by
      simpa only [lhsBody, args, prefixTarget, majorTarget,
        List.length_append] using HlhsWF')
  have HlhsResidual : TrExprS H.outVEnv Us
      (abstractForallContext cachedDomains [])
      (A.rule.sourceLhsBody.abstractList A.rule.binders) lhsBody := by
    have hsourceShape := A.rule.abstractedSourceLhs
    rcases htarget : AddInductive.getIIndices stats A.rule.target with
      ⟨selectedOwner, sourceIndices⟩
    have hselectedOwner : selectedOwner = owner := by
      have hfirst := checkPositivityStep.getIIndices.fst_eq_of_valid
        A.typing.target_valid
      rw [htarget] at hfirst
      exact hfirst.trans A.typing_owner
    subst selectedOwner
    rw [htarget] at hsourceShape HlhsTr
    rw [hsourceShape]
    simpa [prefixSource, majorSource, lhsBody, args,
      prefixTarget, majorTarget,
      Expr.mkAppN_eq_mkAppList, VExpr.mkApps_append,
      getElem!_pos indTypes owner A.sourceOwner_lt] using HlhsTr
  have HtypeTranslation₀ := checkPositivityStep.TrExprS.mkAppList
    H.outVEnvWF.orderedStrong HabstractCtx HownerMotiveTr HargsTr HrightWF'
  have HtypeTranslation : TrExprS H.outVEnv Us
      (abstractForallContext cachedDomains [])
      ((Expr.app
        (mkAppN H.recInfos[owner]!.motive
          (AddInductive.getIIndices stats A.rule.target).2)
        A.rule.sourceConstructorMajor).abstractList A.rule.binders)
      typeBody := by
    unfold RecursorRuleSyntax.sourceConstructorMajor
    simp only [Expr.abstractList_app, Expr.abstractList_mkAppN]
    simpa [typeBody, ownerTarget, args, majorSource, majorTarget,
      Expr.abstractList_app, Expr.abstractList_mkAppN,
      Expr.mkAppN_eq_mkAppList, VExpr.mkApps_append,
      VExpr.liftN_mkApps, bvarSpine_liftN_at_length,
      getElem!_pos indTypes owner A.sourceOwner_lt] using
      HtypeTranslation₀
  exact ⟨T, originalDomains, fieldDomains, fieldResult, lhsBody, typeBody,
    hparams, horiginal, hlifted, Htail, HoriginalCtx, hfields, Hfull,
    HcachedCtx, HlhsResidual, Hlhs', HtypeBody, HtypeTranslation⟩

/-- Telescope-fixed framed form of `installedCachedLhsBodyWithFrame`.
Besides fixing the recursor telescope, this retains the checked constructor
tail needed to compare the LHS context with the independently dependency-selected RHS
context. -/
theorem
    RecursorInstallation.RuleAlignment.installedCachedLhsBodyWithFrameFor
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ originalDomains fieldDomains fieldResult lhsBody typeBody,
      let cachedDomains :=
        (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
          fieldDomains
      VEnv.IsDefEqCtx H.outVEnv Us.length []
          T.params.reverse parameterDecls.toCtx ∧
        originalDomains.length = A.rule.allArgs.size ∧
        fieldDomains =
          (liftContextPrefix (T.motives ++ T.minors).length
            originalDomains.reverse).reverse ∧
        TrExprS H.outVEnv Us parameterDecls
          A.typing.parameterTail
          (VExpr.wrapForalls originalDomains fieldResult) ∧
        OnCtx (originalDomains.reverse ++ T.params.reverse)
          (H.outVEnv.IsType Us.length) ∧
        fieldDomains.length = A.rule.allArgs.size ∧
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
          cachedDomains.reverse ∧
        OnCtx cachedDomains.reverse (H.outVEnv.IsType Us.length) ∧
        TrExprS H.outVEnv Us (abstractForallContext cachedDomains [])
          (A.rule.sourceLhsBody.abstractList A.rule.binders) lhsBody ∧
        H.outVEnv.HasType Us.length cachedDomains.reverse lhsBody typeBody ∧
        H.outVEnv.IsType Us.length cachedDomains.reverse typeBody ∧
        TrExprS H.outVEnv Us (abstractForallContext cachedDomains [])
          ((Expr.app
            (mkAppN H.recInfos[owner]!.motive
              (AddInductive.getIIndices stats A.rule.target).2)
            A.rule.sourceConstructorMajor).abstractList A.rule.binders)
          typeBody := by
  dsimp only
  rcases A.installedCachedLhsBodyWithFrame with
    ⟨T₀, originalDomains, fieldDomains, fieldResult, lhsBody, typeBody,
      Hparams, horiginal, hlifted, Htail, HoriginalCtx, hfields, Hfull,
      Hctx, Htranslation, Htyping, Htype, HtypeTranslation⟩
  rcases T₀.groupsResult_eq T with
    ⟨hparams, hmotives, hminors, _hindices, _hmajor, _hresult⟩
  rw [hparams] at Hparams HoriginalCtx Hfull
  rw [hmotives, hminors] at hlifted Hfull Hctx Htranslation Htyping Htype HtypeTranslation
  exact ⟨originalDomains, fieldDomains, fieldResult, lhsBody, typeBody,
    Hparams, horiginal, hlifted, Htail, HoriginalCtx, hfields, Hfull, Hctx,
    Htranslation, Htyping, Htype, HtypeTranslation⟩

/-- Transport the independently reconstructed LHS into the exact fixed
equation context used by the canonical RHS.  Projection translation need not
be syntactically unique, so the transported strict targets are retained and
their typing is recovered through semantic translation uniqueness. -/
theorem
    RecursorInstallation.RuleAlignment.installedFixedLhsBodyFor
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorInstallation R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (B : A.FieldFrame)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    let inserted := T.motives ++ T.minors
    let equationFields :=
      (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
    let equationDomains :=
      parameterDecls.toCtx.reverse ++ inserted ++ equationFields
    ∃ lhsBody typeBody,
      OnCtx equationDomains.reverse (H.outVEnv.IsType Us.length) ∧
      TrExprS H.outVEnv Us (abstractForallContext equationDomains [])
        (A.rule.sourceLhsBody.abstractList A.rule.binders) lhsBody ∧
      H.outVEnv.HasType Us.length equationDomains.reverse lhsBody typeBody ∧
      H.outVEnv.IsType Us.length equationDomains.reverse typeBody ∧
      TrExprS H.outVEnv Us (abstractForallContext equationDomains [])
        ((Expr.app
          (mkAppN H.recInfos[owner]!.motive
            (AddInductive.getIIndices stats A.rule.target).2)
          A.rule.sourceConstructorMajor).abstractList A.rule.binders)
        typeBody := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.recursorHeaders.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  let inserted := T.motives ++ T.minors
  let equationFields :=
    (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
  let equationDomains :=
    parameterDecls.toCtx.reverse ++ inserted ++ equationFields
  rcases A.installedCachedLhsBodyWithFrameFor T with
    ⟨originalDomains, fieldDomains, fieldResult, cachedLhs, cachedType,
      Hparams, horiginal, hlifted, Htail, HoriginalCtx, _hfields, Hfull,
      HcachedCtx, HlhsTranslation, HlhsTyping, HcachedType,
      HtypeTranslation⟩
  have Hparams' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      T.params.reverse H.parameterSuffix.parameterDecls.toCtx := by
    simpa only [← H.parameterDecls] using Hparams
  have Htail' : TrExprS H.outVEnv Us
      H.parameterSuffix.parameterDecls A.typing.parameterTail
      (VExpr.wrapForalls originalDomains fieldResult) := by
    simpa only [← H.parameterDecls] using Htail
  rcases A.installedCheckedScopedEquationContextAlignmentFromFrameFor B T
      originalDomains fieldResult Hparams' horiginal Htail' HoriginalCtx with
    ⟨alignedFields, halignedFields, Haligned⟩
  have hfields : alignedFields = fieldDomains :=
    halignedFields.trans hlifted.symm
  rw [hfields] at Haligned
  have HcanonicalFixed : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      equationDomains.reverse := by
    simpa [equationDomains, equationFields, inserted, parameterDecls,
      ← H.parameterDecls, List.reverse_append, List.append_assoc] using
      Haligned
  have HcachedFixed : VEnv.IsDefEqCtx H.outVEnv Us.length []
      ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors ++
        fieldDomains).reverse) equationDomains.reverse :=
    VEnv.IsDefEqCtx.trans_empty H.outVEnvWF
      (Hfull.symm H.outVEnvWF.ordered) HcanonicalFixed
  have HfixedCtx : OnCtx equationDomains.reverse
      (H.outVEnv.IsType Us.length) :=
    (HcachedFixed.symm H.outVEnvWF.ordered).isType
  have Hvlctx : VLCtx.IsDefEq H.outVEnv Us.length
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors ++
          fieldDomains) [])
      (abstractForallContext equationDomains []) :=
    abstractForallContext.isDefEq HcachedFixed
  rcases HlhsTranslation.defeqDFC H.outVEnvWF Hvlctx with
    ⟨lhsBody, HlhsTranslation'⟩
  rcases HtypeTranslation.defeqDFC H.outVEnvWF Hvlctx with
    ⟨typeBody, HtypeTranslation'⟩
  have HlhsTypingFixed := HlhsTyping.defeqDFC
    H.outVEnvWF.ordered HcachedFixed
  have HcachedTypeFixed := HcachedType.defeqDFC
    H.outVEnvWF.ordered HcachedFixed
  have HlhsEq₀ := HlhsTranslation'.uniq H.outVEnvWF
    (Hvlctx.symm H.outVEnvWF) HlhsTranslation
  have HlhsEq : H.outVEnv.IsDefEqU Us.length equationDomains.reverse
      lhsBody cachedLhs := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HlhsEq₀
  have HtypeEq₀ := HtypeTranslation'.uniq H.outVEnvWF
    (Hvlctx.symm H.outVEnvWF) HtypeTranslation
  have HtypeEq : H.outVEnv.IsDefEqU Us.length equationDomains.reverse
      typeBody cachedType := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HtypeEq₀
  have HlhsTypingOld : H.outVEnv.HasType Us.length equationDomains.reverse
      lhsBody cachedType :=
    VEnv.HasType.defeqU_l H.outVEnvWF HfixedCtx HlhsEq.symm
      HlhsTypingFixed
  have HlhsTyping' : H.outVEnv.HasType Us.length equationDomains.reverse
      lhsBody typeBody :=
    HlhsTypingOld.defeqU_r H.outVEnvWF HfixedCtx HtypeEq.symm
  have HtypeBody : H.outVEnv.IsType Us.length equationDomains.reverse
      typeBody :=
    VEnv.IsType.defeqU_l H.outVEnvWF HfixedCtx HtypeEq.symm
      HcachedTypeFixed
  exact ⟨lhsBody, typeBody, HfixedCtx, HlhsTranslation', HlhsTyping',
    HtypeBody, HtypeTranslation'⟩

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Applying a complete telescope to as many arguments as it has domains
undoes a weakening of the residual by those binders.  The domain values may
be dependent; they disappear from the conclusion because the weakened
residual does not depend on any of the newly inserted variables. -/
theorem VExpr.applyForallType_wrapForalls_liftN
    (domains args : List VExpr) (result : VExpr)
    (hlength : args.length = domains.length) :
    VExpr.applyForallType
        (VExpr.wrapForalls domains (result.liftN domains.length 0)) args =
      result := by
  induction args generalizing domains result with
  | nil =>
      have hdomains : domains = [] :=
        List.eq_nil_of_length_eq_zero hlength.symm
      subst domains
      simp [VExpr.applyForallType, VExpr.wrapForalls]
  | cons arg args ih =>
      cases domains with
      | nil => simp at hlength
      | cons domain domains =>
          have htail : args.length = domains.length := by
            simpa using Nat.succ.inj hlength
          change VExpr.applyForallType
            ((VExpr.wrapForalls domains
              (result.liftN (domains.length + 1) 0)).inst arg) args = result
          rw [VExpr.inst_wrapForalls]
          simp only [Nat.zero_add]
          rw [VExpr.inst_liftN_lo]
          simpa only [VExpr.instForallDomains_length] using
            ih (VExpr.instForallDomains domains arg 0) result (by
              simpa using htail)

end VerifyInductive
end Lean4Lean
