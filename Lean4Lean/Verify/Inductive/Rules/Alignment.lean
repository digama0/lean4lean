import Lean4Lean.Verify.Inductive.Install.Lookups
import Lean4Lean.Verify.Inductive.SourceAlignment

/-! Rule alignment, the entry point of the typing of the iota rules (`Rules/`,
section 3.2 of the design notes). For each rule emitted by the recursor construction,
`RecursorCheck.RuleAlignment` fixes in one record the executable family in `indTypes`, the
abstract family and constructor of `decl`, and the rule's syntax and typing facts
(`RecursorRuleSyntax`, `RecursorRuleSyntax.Semantics`); `RecursorCheck.ruleAlignment` produces
it from the recursor check. The file then reads the translated telescope of each installed
recursor off the recursor check and relates its parameter domains to the cached parameter
declarations of the constructor check. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Pointwise projection used by abstract iota reconstruction.  It exposes
the exact generated source rule together with its `Semantics` record from the
same executable constructor iteration. -/
theorem RecursorCheck.generatedRule
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    (i : Nat) (hctor : i < indTypes[owner]!.ctors.length)
    (hrule : i < (H.generated.entry owner howner).info.rules.length) :
      ∃ Hrule : RecursorRuleSyntax indTypes stats
        (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
        (AddInductive.getRecLevels H.elimLevel stats.levels)
        indTypes[owner]!.ctors[i]
        (recursorMinorOffset indTypes owner + i)
        (H.generated.entry owner howner).info.rules[i],
      ∃ S : Hrule.Semantics H.recursorWF decl owner,
        Nonempty (Hrule.MinorAt S H.recInfos H.elimLevel
          H.origins owner i) ∧
        S.parameterDecls = H.parameterSuffix.parameterDecls := by
  rcases H.ruleTyping.entry owner howner with
    ⟨info, hsource, _Hsemantic, _Hmotive, Horigins⟩
  let E := H.generated.entry owner howner
  have hinfo : info = E.info := by
    have heq : ConstantInfo.recInfo info = .recInfo E.info :=
      hsource.symm.trans E.source_eq
    injection heq
  subst info
  dsimp [E] at Horigins ⊢
  have hzero : 0 + owner = owner := Nat.zero_add owner
  rw [hzero] at Horigins
  exact Horigins i hctor hrule

/-- The family selected from the generated residual is exactly the outer
owner whose constructor batch is being traversed. -/
theorem RecursorCheck.generatedRuleOwner
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    (i : Nat) (hctor : i < indTypes[owner]!.ctors.length)
    (hrule : i < (H.generated.entry owner howner).info.rules.length) :
    ∃ Hrule : RecursorRuleSyntax indTypes stats
        (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
        (AddInductive.getRecLevels H.elimLevel stats.levels)
        indTypes[owner]!.ctors[i]
        (recursorMinorOffset indTypes owner + i)
        (H.generated.entry owner howner).info.rules[i],
      ∃ Hsemantic : Hrule.Semantics
          H.recursorWF decl owner,
        Nonempty (Hrule.MinorAt Hsemantic H.recInfos
          H.elimLevel H.origins owner i) ∧
        Hsemantic.parameterDecls = H.parameterSuffix.parameterDecls ∧
        Hsemantic.ownerIdx = owner := by
  rcases H.generatedRule owner howner i hctor hrule with
    ⟨Hrule, Hsemantic, Horigin, hparameterDecls⟩
  have htypeNames : (decl.types.map (·.name)).Nodup := by
    have hprefix := (List.nodup_append.mp
      (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup
        R.core)).1
    simpa [VInductDecl.sourceNames, VInductDecl.typeConstants,
      VInductiveType.toVConstVal, Function.comp_def] using hprefix
  exact ⟨Hrule, Hsemantic, Horigin, hparameterDecls,
    Hsemantic.owner_eq Hrule htypeNames⟩

/-- Complete source alignment for one rule emitted by the mutual recursor
loop.  The entry index selects the same concrete family in `indTypes`, the
same abstract family in `decl.types`, and the same abstract constructor in
that family's constructor list.  The semantic target selected while building
the rule is additionally identified with this owner.  Keeping these facts in
one dependent record prevents later iota reconstruction from silently mixing
the three independent indexing conventions. -/
structure RecursorCheck.RuleAlignment
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    (i : Nat) (hctor : i < indTypes[owner]!.ctors.length) where
  sourceOwner_lt : owner < indTypes.size
  sourceCtor_lt : i < indTypes[owner].ctors.length
  abstractOwner_lt : owner < decl.types.length
  abstractCtor_lt : i < decl.types[owner].ctors.length
  ownerTranslation : TrInductiveType sourceEnv R.headerVEnv
    c.lparams indTypes[owner] decl.types[owner]
  ctorTranslation : TrSourceConst R.headerVEnv c.lparams
    indTypes[owner].ctors[i].name indTypes[owner].ctors[i].type
    decl.types[owner].ctors[i]
  sourceRule_lt : i < (H.generated.entry owner howner).info.rules.length
  rule : RecursorRuleSyntax indTypes stats
    (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
    (AddInductive.getRecLevels H.elimLevel stats.levels)
    indTypes[owner]!.ctors[i]
    (recursorMinorOffset indTypes owner + i)
    (H.generated.entry owner howner).info.rules[i]
  typing : rule.Semantics
    H.recursorWF decl owner
  parameterDecls_eq : typing.parameterSuffix.parameterDecls =
    H.parameterSuffix.parameterDecls
  motiveOrigins : Nonempty (rule.MotiveAt typing
    H.recInfos H.elimLevel)
  minorOrigins : Nonempty (rule.MinorAt typing
    H.recInfos H.elimLevel H.origins owner i)
  typing_owner : typing.ownerIdx = owner

noncomputable def RecursorCheck.RuleAlignment.minorOrigin
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor) :
    A.rule.MinorAt A.typing H.recInfos H.elimLevel
      H.origins owner i :=
  Classical.choice A.minorOrigins

noncomputable def RecursorCheck.RuleAlignment.minorShape
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor) :
    MinorPremiseType :=
  A.minorOrigin.producer.minorShape

noncomputable def RecursorCheck.RuleAlignment.minorReplayAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size) :
    A.rule.CallAt (recInfos := H.recInfos) A.typing
      A.minorShape j hj :=
  Classical.choice (A.minorOrigin.producer.replay j hj)

/-- Select the fully aligned pointwise rule package directly from the
recursor check.  All bounds not supplied by the caller follow from
the generated-recursors cardinality and the source-declaration translation. -/
theorem RecursorCheck.ruleAlignment
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    (i : Nat) (hctor : i < indTypes[owner]!.ctors.length) :
    Nonempty (H.RuleAlignment owner howner i hctor) := by
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have habstractOwner : owner < decl.types.length := by
    simpa [H.cardinality.records] using hrecInfo
  have family := Lean4Lean.VerifyInductive.TrInductDeclCore.familyAlignmentFromTarget
    R.core owner habstractOwner
  have hsourceOwner := family.source_lt
  have hsourceCtor : i < indTypes[owner].ctors.length := by
    simpa [Array.getElem!_eq_getD, Array.getD, hsourceOwner] using hctor
  have constructor := family.constructorAt i hsourceCtor
  let E := H.generated.entry owner howner
  have hsourceRule : i < E.info.rules.length := by
    rw [E.rules.length]
    exact hctor
  rcases H.generatedRuleOwner owner howner i hctor hsourceRule with
    ⟨Hrule, Hsemantic, ⟨Horigin⟩, hparameterDecls, hsemanticOwner⟩
  let Hmotive : Nonempty (Hrule.MotiveAt Hsemantic H.recInfos
      H.elimLevel) := ⟨Horigin.producer⟩
  exact ⟨{
    sourceOwner_lt := hsourceOwner
    sourceCtor_lt := hsourceCtor
    abstractOwner_lt := habstractOwner
    abstractCtor_lt := constructor.target_lt
    ownerTranslation := family.translation
    ctorTranslation := constructor.translation
    sourceRule_lt := hsourceRule
    rule := Hrule
    typing := Hsemantic
    parameterDecls_eq := Hsemantic.parameterDecls_eq.trans hparameterDecls
    motiveOrigins := Hmotive
    minorOrigins := ⟨Horigin⟩
    typing_owner := hsemanticOwner }⟩

/-- The recursor selected by a generated rule carries the exact five-part,
binder-typed telescope recovered from the executable's `.recInfo`.  This is
the canonical source of the parameter, motive, and minor domains used when
typing the corresponding equation; it does not reconstruct those domains
from the rule RHS. -/
theorem RecursorCheck.recursorTelescopeTranslationAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    Nonempty (RecursorTypeTelescope
      R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner) := by
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  let E := H.generated.entry owner howner
  rcases H.generatedTelescopeTranslations owner howner with
    ⟨info, hinfo, ⟨T⟩⟩
  have hinfoEq : info = E.info := by
    have heq : ConstantInfo.recInfo info = .recInfo E.info :=
      hinfo.symm.trans E.source_eq
    injection heq
  subst info
  refine ⟨?_⟩
  simpa [E.levels, H.localExtends.lparams_eq] using T

theorem RecursorCheck.installedRecursorTelescopeTranslationAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    Nonempty (RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner) := by
  rcases H.recursorTelescopeTranslationAt owner howner with ⟨T⟩
  exact ⟨T.mono H.installed.le⟩

/-- The translated common prefixes of any two installed mutual recursors
are definitionally equal.  The proof is deliberately factored through the
concrete generated source binders, so it does not assume that independently
translated abstract domain lists are syntactically identical. -/
theorem RecursorCheck.installedRecursorCommonPrefixContextAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner₁ : Nat) (howner₁ : owner₁ < H.entries.length)
    (owner₂ : Nat) (howner₂ : owner₂ < H.entries.length)
    (T₁ : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner₁ howner₁).info.type
      H.entries[owner₁].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner₁]!.indices.size owner₁)
    (T₂ : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner₂ howner₂).info.type
      H.entries[owner₂].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner₂]!.indices.size owner₂) :
    VEnv.IsDefEqCtx H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
      (T₁.params ++ T₁.motives ++ T₁.minors).reverse
      (T₂.params ++ T₂.motives ++ T₂.minors).reverse := by
  apply T₁.commonPrefixDefEqCtx H.outVEnvWF T₂
  intro i hi _hi₁ _hi₂ domain₁ domain₂ Hbinder₁ Hbinder₂
  exact H.generatedRecursorCommonPrefixBinderDomainAt
    owner₁ howner₁ owner₂ howner₂ i hi Hbinder₁ Hbinder₂

/-- The parameter domains recovered from the installed generated recursor
are definitionally equal to the independently checked cached parameter
scope.  This is the connecting lemma for the equation context: it compares contexts,
not syntax, and is derived from translation of the same concrete `mkForall`
prefix on both sides. -/
theorem
    RecursorCheck.installedRecursorParameterContextAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        T.params.reverse parameterDecls.toCtx := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.recursorHeaders.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases H.installedRecursorTelescopeTranslationAt owner howner with ⟨T⟩
  let E := H.generated.entry owner howner
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  let selections := H.bindings.toRecursorBinderGroups H.localWF H.params
    owner hrecInfo
  have hselectionNoAlias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner hrecInfo
  let inner : Expr :=
    H.localContext.lctx.mkForall (H.recInfos.map (·.motive)) <|
    H.localContext.lctx.mkForall (H.recInfos.flatMap (·.minors)) <|
    H.localContext.lctx.mkForall H.recInfos[owner]!.indices <|
    H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
      (.app (mkAppN H.recInfos[owner]!.motive
        H.recInfos[owner]!.indices) H.recInfos[owner]!.major)
  have Hraw : TrExprS H.outVEnv Us []
      (H.localContext.lctx.mkForall stats.params inner)
      H.entries[owner].2.type := by
    have Htranslated := T.typed.translation
    rw [E.type] at Htranslated
    simpa [E.levels, H.localExtends.lparams_eq, inner, Us] using
      TrExprS.of_inferImplicit Htranslated
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  have Hsort : TrExprS H.outVEnv Us []
      (H.localContext.lctx.mkForall stats.params
        (.sort (.zero : Level)))
      (VExpr.wrapForalls H.parameterSuffix.parameterDecls.toCtx.reverse
        (.sort (.zero : VLevel))) := by
    have HsortBase := H.parameterSuffix.closedSortTranslation
    rw [H.recursorWF.lctx_eq] at HsortBase
    exact HsortBase.mono hbase
  have Hsame : Expr.SameForallPrefix stats.params.size
      (H.localContext.lctx.mkForall stats.params inner)
      (H.localContext.lctx.mkForall stats.params
        (.sort (.zero : Level))) := by
    exact selections.params.sameForallPrefix
      hselectionNoAlias.parts.params inner (.sort (.zero : Level))
  have hnil : VLCtx.IsDefEq H.outVEnv Us.length ([] : VLCtx) [] :=
    .refl H.outVEnvWF.ordered (by trivial)
  rcases Hsame.translatedContexts H.outVEnvWF hnil Hraw Hsort with
    ⟨leftDomains, leftResidual, rightDomains, rightResidual,
      hleftLength, hrightLength, hleftTarget, hrightTarget, hcontexts⟩
  have hleftEq : leftDomains = T.params := by
    apply VExpr.wrapForalls_prefix_domains_eq hleftLength T.params_length
    calc
      VExpr.wrapForalls leftDomains leftResidual = H.entries[owner].2.type :=
        hleftTarget.symm
      _ = VExpr.wrapForalls
          (T.params ++ (T.motives ++ T.minors ++ T.indices ++ T.major))
          T.result := by
        simpa [List.append_assoc] using T.target_eq
  have hparameterCtxLength : H.parameterSuffix.parameterDecls.toCtx.length =
      stats.params.size := by
    calc
      H.parameterSuffix.parameterDecls.toCtx.length =
          H.parameterSuffix.parameterDecls.length :=
        checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
          H.parameterSuffix.cached
      _ = stats.params.size := H.parameterSuffix.parameterDecls_length
  have hrightEq : rightDomains =
      H.parameterSuffix.parameterDecls.toCtx.reverse := by
    apply VExpr.wrapForalls_prefix_domains_eq hrightLength
      (by simpa using hparameterCtxLength)
    calc
      VExpr.wrapForalls rightDomains rightResidual =
          VExpr.wrapForalls H.parameterSuffix.parameterDecls.toCtx.reverse
            (.sort (.zero : VLevel)) := hrightTarget.symm
      _ = VExpr.wrapForalls
          (H.parameterSuffix.parameterDecls.toCtx.reverse ++ [])
          (.sort (.zero : VLevel)) := by simp
  refine ⟨T, ?_⟩
  simpa only [hleftEq, hrightEq, parameterDecls, ← H.parameterDecls,
    VLCtx.toCtx, List.append_nil, List.reverse_reverse] using hcontexts

/-- Rule-local specialization of `installedRecursorParameterContextAt`. -/
theorem
    RecursorCheck.RuleAlignment.installedRecursorParameterContext
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (_A : H.RuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        T.params.reverse parameterDecls.toCtx := by
  exact H.installedRecursorParameterContextAt owner howner

/-- Every retained translation of the installed generated recursor has the
same canonical parameter context.  The existential witness selected by
`installedRecursorParameterContextAt` is immaterial because the five retained
telescope groups are uniquely determined by the common source and target. -/
theorem
    RecursorCheck.installedRecursorParameterContextFor
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv)
    {owner : Nat} (howner : owner < H.entries.length)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner) :
    VEnv.IsDefEqCtx H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
      T.params.reverse
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls.toCtx := by
  rcases H.installedRecursorParameterContextAt owner howner with
    ⟨T₀, Hparams⟩
  have hparams : T.params = T₀.params :=
    (T.groupsResult_eq T₀).1
  simpa only [hparams] using Hparams

/-- Decompose the independently checked constructor tail along the genuine
field telescope retained by rule generation.  This joins the constructor
checker and recursor generator only through their common source tail; the
abstract parameter contexts are related by conversion, not by syntactic
equality. -/
theorem
    RecursorCheck.RuleAlignment.installedCheckedConstructorFieldFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
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
      ∃ (fieldDomains : List VExpr) (fieldResult introTarget : VExpr),
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          T.params.reverse parameterDecls.toCtx ∧
        fieldDomains.length = A.rule.allArgs.size ∧
        TrExprS H.outVEnv Us parameterDecls
          A.typing.parameterTail
          (VExpr.wrapForalls fieldDomains fieldResult) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext fieldDomains parameterDecls)
          (A.rule.target.abstractList A.typing.fieldOpening.fvars)
          fieldResult ∧
        H.outVEnv.IsType Us.length parameterDecls.toCtx
          (VExpr.wrapForalls fieldDomains fieldResult) ∧
        H.outVEnv.IsType Us.length T.params.reverse
          (VExpr.wrapForalls fieldDomains fieldResult) ∧
        OnCtx (fieldDomains.reverse ++ T.params.reverse)
          (H.outVEnv.IsType Us.length) ∧
        H.outVEnv.HasType Us.length T.params.reverse introTarget
          (VExpr.wrapForalls fieldDomains fieldResult) ∧
        TrExprS H.outVEnv Us parameterDecls
          (mkAppN
            (.const
              ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
              stats.levels)
            stats.params) introTarget ∧
        introTarget = VExpr.mkApps
          (.const
            ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
            (recursorDeclarationAbstractLevels c.lparams
              H.elimLevelAdmissible))
          (bvarSpine stats.params.size) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.recursorHeaders.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.installedRecursorParameterContext with ⟨T, hparams⟩
  rcases R.checkedConstructorPrefixAt H.elimLevelAdmissible
      H.lparamsNodup owner A.sourceOwner_lt i A.sourceCtor_lt with
    ⟨_ctorVal, tail, tailTarget, introTarget, _hctorMem, _hctorName,
      Hprefix, Htail, HtailType, Hintro, HintroShape,
      HintroType, _Hsynthesis⟩
  have HsemanticPrefix : ParameterPrefix stats 0
      ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).type
      A.typing.parameterTail := by
    simpa [Array.getElem!_eq_getD, Array.getD, A.sourceOwner_lt] using
      A.typing.parameterPrefix
  have htail : tail = A.typing.parameterTail :=
    Hprefix.tail_eq HsemanticPrefix
  subst tail
  have hbaseLE :
      (R.context.toAdmissibleRecursorContextWF
        H.elimLevelAdmissible).venv ≤ H.outVEnv := by
    simpa only [ContextWF.toAdmissibleRecursorContextWF_venv] using
      H.installed.le
  have Htail' : TrExprS H.outVEnv Us parameterDecls
      A.typing.parameterTail tailTarget := by
    simpa [Us, parameterDecls] using Htail.mono hbaseLE
  have HtailType' : H.outVEnv.IsType Us.length parameterDecls.toCtx
      tailTarget := by
    simpa [Us, parameterDecls] using HtailType.mono hbaseLE
  have Hintro' : TrExprS H.outVEnv Us parameterDecls
      (mkAppN
        (.const
          ((indTypes[owner]'A.sourceOwner_lt).ctors[i]'A.sourceCtor_lt).name
          stats.levels)
        stats.params) introTarget := by
    simpa [Us, parameterDecls] using Hintro.mono hbaseLE
  have HintroType' : H.outVEnv.HasType Us.length T.params.reverse
      introTarget tailTarget := by
    have Htyped : H.outVEnv.HasType Us.length parameterDecls.toCtx
        introTarget tailTarget := by
      simpa [Us, parameterDecls] using HintroType.mono hbaseLE
    exact Htyped.defeqDFC H.outVEnvWF.ordered
      (hparams.symm H.outVEnvWF.ordered)
  have Hfields := Expr.ForallTelescopeTypeTranslation.ofTrExprS
    A.typing.fieldOpening.telescope Htail' HtailType'
  rcases Hfields.toWrapForalls with
    ⟨fieldDomains, sourceResidual, fieldResult, hfields,
      HsourceTelescope, htarget, Hresult, _HresultType⟩
  have hsourceResidual :
      sourceResidual = A.typing.fieldOpening.residual :=
    HsourceTelescope.residual_eq A.typing.fieldOpening.telescope
  have HfieldResidual : TrExprS H.outVEnv Us
      (abstractForallContext fieldDomains parameterDecls)
      (A.rule.target.abstractList A.typing.fieldOpening.fvars)
      fieldResult := by
    rw [A.typing.fieldOpening.closed, ← hsourceResidual]
    exact Hresult
  subst tailTarget
  have HtailTypeT : H.outVEnv.IsType Us.length T.params.reverse
      (VExpr.wrapForalls fieldDomains fieldResult) :=
    HtailType'.defeqDFC H.outVEnvWF.ordered
      (hparams.symm H.outVEnvWF.ordered)
  have HfieldContext : OnCtx
      (fieldDomains.reverse ++ T.params.reverse)
      (H.outVEnv.IsType Us.length) :=
    (VEnv.IsType.wrapForalls_inv H.outVEnvWF.ordered
      hparams.isType HtailTypeT).1
  exact ⟨T, fieldDomains, fieldResult, introTarget, hparams, hfields,
    Htail', HfieldResidual, HtailType', HtailTypeT, HfieldContext,
    HintroType', Hintro', HintroShape⟩

/-- Close the cached common parameters around a constructor result already
translated below its genuine field telescope.  Keeping this lemma
parameterized by the field-frame witnesses lets later equation proofs retain
the very same recursor telescope witness. -/
theorem
    RecursorCheck.RuleAlignment.cachedConstructorTargetOfFieldFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (fieldDomains : List VExpr) (fieldResult : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (HfieldResidual : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext fieldDomains
        (R.recursorHeaders.parameterSuffix.toRecursorContext
          H.elimLevelAdmissible).parameterDecls)
      (A.rule.target.abstractList A.typing.fieldOpening.fvars)
      fieldResult) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    TrExprS H.outVEnv Us
      (abstractForallContext
        (parameterDecls.toCtx.reverse ++ fieldDomains) [])
      (A.rule.target.abstractList
        (A.rule.params_bound.fvars ++
          A.typing.fieldOpening.fvars))
      fieldResult := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.recursorHeaders.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  dsimp only
  have hparamExprs : stats.params.toList.reverse =
      (A.rule.params_bound.fvars.reverse.map Expr.fvar) := by
    have h := congrArg Array.toList A.rule.params_bound.expressions
    simpa [List.map_reverse] using congrArg List.reverse h
  have Hcached : List.Forall₂
      checkInductiveTypes.loopType.CachedParameterDecl
      (A.rule.params_bound.fvars.reverse.map Expr.fvar) parameterDecls := by
    have Hbase := H.parameterSuffix.cached
    rw [hparamExprs] at Hbase
    simpa [parameterDecls, H.parameterDecls] using Hbase
  have Hdecls : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type))
      A.rule.params_bound.fvars.reverse parameterDecls := by
    rw [List.forall₂_map_left_iff] at Hcached
    exact Lean4Lean.List.Forall₂.imp (fun fv entry hentry => by
      rcases hentry with ⟨actual, deps, type, hparam, hentry⟩
      cases Expr.fvar.inj hparam
      exact ⟨deps, type, hentry⟩) Hcached
  have hparamsNodup : A.rule.params_bound.fvars.reverse.Nodup :=
    List.nodup_reverse.mpr <|
      (List.nodup_append.mp
        (List.nodup_append.mp A.rule.outer_binders_nodup).1).1
  have Hclosed :=
    Lean4Lean.VerifyInductive.TrExprS.abstractFVarLambdaSuffix
      Hdecls hparamsNodup HfieldResidual
  have hparamsFields :
      (A.rule.params_bound.fvars ++
        A.typing.fieldOpening.fvars).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨List.nodup_reverse.mp hparamsNodup,
      A.typing.fieldOpening.nodup, ?_⟩
    intro param hparam field hfield heq
    subst field
    rw [A.typing.fieldOpening.fvars_eq_bound
      A.rule.all_args_bound] at hfield
    exact A.rule.all_args_outer_fresh param hfield
      (List.mem_append_left _ (List.mem_append_left _ hparam))
  have hfieldLength : A.typing.fieldOpening.fvars.length =
      fieldDomains.length := by
    rw [A.typing.fieldOpening.fvars_eq_bound
      A.rule.all_args_bound, hfields]
    have h := congrArg Array.size A.rule.all_args_bound.expressions
    simpa using h.symm
  have hsource := Expr.abstractList_after_inner
    (e := A.rule.target) (outer := A.rule.params_bound.fvars)
    (inner := A.typing.fieldOpening.fvars) (k := 0) hparamsFields
  have hsource' :
      ((A.rule.target.abstractList A.typing.fieldOpening.fvars).abstractList
          A.rule.params_bound.fvars fieldDomains.length) =
        A.rule.target.abstractList
          (A.rule.params_bound.fvars ++
            A.typing.fieldOpening.fvars) := by
    simpa [hfieldLength] using hsource
  simp only [List.reverse_reverse] at Hclosed
  rw [hsource'] at Hclosed
  simpa [parameterDecls, List.reverse_reverse] using Hclosed

/-- The lift introduced between parameters and fields is exactly simultaneous
abstraction over the rule's complete parameter/motive/minor/field binder list.
This follows from strict-translation scoping: the constructor result can only
mention parameters and genuine fields, hence motives and minors merely shift
the already abstracted parameter variables. -/
theorem
    RecursorCheck.RuleAlignment.targetBinderLift_eq
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr) (fieldResult : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (Htarget : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (((R.recursorHeaders.parameterSuffix.toRecursorContext
            H.elimLevelAdmissible).parameterDecls.toCtx.reverse) ++
          fieldDomains) [])
      (A.rule.target.abstractList
        (A.rule.params_bound.fvars ++
          A.typing.fieldOpening.fvars))
      fieldResult) :
    ((A.rule.target.abstractList
        (A.rule.params_bound.fvars ++
          A.typing.fieldOpening.fvars)).liftLooseBVars'
      A.rule.allArgs.size (T.motives ++ T.minors).length) =
      A.rule.target.abstractList A.rule.binders := by
  let params := A.rule.params_bound.fvars
  let motives := A.rule.motives_bound.fvars
  let minors := A.rule.minors_bound.fvars
  let fields := A.typing.fieldOpening.fvars
  let middle := motives ++ minors
  let parameterDecls :=
    (R.recursorHeaders.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  have hparamsLength : params.length = stats.params.size := by
    have h := congrArg Array.size A.rule.params_bound.expressions
    simpa [params] using h.symm
  have hfieldsLength : fields.length = A.rule.allArgs.size := by
    change A.typing.fieldOpening.fvars.length = A.rule.allArgs.size
    rw [A.typing.fieldOpening.fvars_eq_bound
      A.rule.all_args_bound]
    have h := congrArg Array.size A.rule.all_args_bound.expressions
    simpa using h.symm
  have hparameterDeclsLength : parameterDecls.toCtx.length =
      stats.params.size := by
    have hcached := H.parameterSuffix.cached
    have h :=
      checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
        hcached
    calc
      parameterDecls.toCtx.length = parameterDecls.length := by
        simpa [parameterDecls, H.parameterDecls] using h
      _ = stats.params.size := by
        simpa [parameterDecls, H.parameterDecls] using
          H.parameterSuffix.parameterDecls_length
  have hparamsFields : (params ++ fields).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨(List.nodup_append.mp
        (List.nodup_append.mp A.rule.outer_binders_nodup).1).1,
      A.typing.fieldOpening.nodup, ?_⟩
    intro param hparam field hfield heq
    subst field
    have hfield' : param ∈ A.rule.all_args_bound.fvars := by
      simpa [fields, A.typing.fieldOpening.fvars_eq_bound
        A.rule.all_args_bound] using hfield
    exact A.rule.all_args_outer_fresh param hfield'
      (List.mem_append_left _ (List.mem_append_left _ hparam))
  have hsourceClosed : Closed
      (A.rule.target.abstractList (params ++ fields))
      (params ++ fields).length := by
    have hclosed := Htarget.closed
    simpa [params, fields, VLCtx.bvars,
      parameterDecls, hparamsLength, hfieldsLength, hfields,
      hparameterDeclsLength] using hclosed
  have htargetClosed : Closed A.rule.target 0 :=
    Expr.closed_of_abstractList (e := A.rule.target)
      (fvars := params ++ fields) (depth := 0) (by
        simpa using hsourceClosed)
  have hsourceFVars :
      (A.rule.target.abstractList (params ++ fields)).FVarsIn
        (fun _ => False) := by
    have hfvars := Htarget.fvarsIn
    simpa [abstractForallContext, VLCtx.fvars, params, fields,
      parameterDecls] using hfvars
  have htargetFVars : A.rule.target.FVarsIn
      (fun fv => fv ∈ params ++ fields) := by
    exact (FVarsIn.of_abstractList hsourceFVars).mono fun fv h => by
      simpa using h
  have houterSplit := List.nodup_append.mp A.rule.outer_binders_nodup
  have hparamsMotivesSplit :=
    List.nodup_append.mp houterSplit.1
  have htargetAvoidsMiddle : A.rule.target.FVarsIn
      (fun fv => fv ∉ middle) := by
    apply htargetFVars.mono
    intro fv hfv hmiddle
    rcases List.mem_append.mp hfv with hparam | hfield
    · rcases List.mem_append.mp hmiddle with hmotive | hminor
      · exact hparamsMotivesSplit.2.2 fv hparam fv hmotive rfl
      · exact houterSplit.2.2 fv
          (List.mem_append_left _ hparam) fv hminor rfl
    · have hfield' : fv ∈ A.rule.all_args_bound.fvars := by
        simpa [fields, A.typing.fieldOpening.fvars_eq_bound
          A.rule.all_args_bound] using hfield
      apply A.rule.all_args_outer_fresh fv hfield'
      rcases List.mem_append.mp hmiddle with hmotive | hminor
      · exact List.mem_append_left _
          (List.mem_append_right _ hmotive)
      · exact List.mem_append_right _ hminor
  have hmiddleAbstract : A.rule.target.abstractList middle = A.rule.target :=
    htargetAvoidsMiddle.abstractList_eq_self htargetClosed
  let targetFields := A.rule.target.abstractList fields
  have hparamsFieldsShape :
      targetFields.abstractList params fields.length =
        A.rule.target.abstractList (params ++ fields) := by
    simpa [targetFields] using Expr.abstractList_after_inner
      (e := A.rule.target) (outer := params) (inner := fields) (k := 0)
      hparamsFields
  have htargetFieldsClosed : Closed targetFields fields.length := by
    apply Expr.closed_of_abstractList
    rw [hparamsFieldsShape]
    simpa [List.length_append, Nat.add_comm] using hsourceClosed
  have hshift := Expr.abstractList_add_eq_liftLooseBVars
    (e := targetFields) (fvars := params) (depth := fields.length)
    (extra := middle.length) htargetFieldsClosed
    (List.nodup_append.mp
      (List.nodup_append.mp A.rule.outer_binders_nodup).1).1
  have hfullShape := Expr.abstractList_after_inner
    (e := A.rule.target) (outer := params)
    (inner := middle ++ fields) (k := 0) (by
      simpa [params, motives, minors, fields, middle,
        A.typing.fieldOpening.fvars_eq_bound A.rule.all_args_bound,
        RecursorRuleSyntax.binders, List.append_assoc] using
        A.rule.binders_nodup)
  rw [Expr.abstractList_append, hmiddleAbstract] at hfullShape
  have hmiddleLength : middle.length =
      (T.motives ++ T.minors).length := by
    have hm : motives.length = (H.recInfos.map (·.motive)).size := by
      have h := congrArg Array.size A.rule.motives_bound.expressions
      simpa [motives] using h.symm
    have hmi : minors.length =
        (H.recInfos.flatMap (·.minors)).size := by
      have h := congrArg Array.size A.rule.minors_bound.expressions
      simpa [minors] using h.symm
    simp [middle, hm, hmi, T.motives_length, T.minors_length]
  have hfullShape' :
      targetFields.abstractList params (fields.length + middle.length) =
        A.rule.target.abstractList (params ++ (middle ++ fields)) := by
    simpa [targetFields, List.length_append, Nat.add_comm,
      List.append_assoc] using hfullShape
  calc
    (A.rule.target.abstractList (params ++ fields)).liftLooseBVars'
        A.rule.allArgs.size (T.motives ++ T.minors).length =
        (targetFields.abstractList params fields.length).liftLooseBVars'
          fields.length middle.length := by
            rw [hparamsFieldsShape, hfieldsLength, hmiddleLength]
    _ = targetFields.abstractList params (fields.length + middle.length) :=
      hshift.symm
    _ = A.rule.target.abstractList (params ++ (middle ++ fields)) :=
      hfullShape'
    _ = A.rule.target.abstractList A.rule.binders := by
      simp [RecursorRuleSyntax.binders, params, motives, minors,
        fields, middle,
        A.typing.fieldOpening.fvars_eq_bound A.rule.all_args_bound,
        List.append_assoc]

/-- Invert a cached constructor target belonging to a fixed recursor
telescope.  Keeping `T` explicit is essential when the resulting index spine
is used by the matching recursor suffix. -/
theorem
    RecursorCheck.RuleAlignment.cachedConstructorIndexSpineOfTarget
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.RuleAlignment owner howner i hctor)
    (T : RecursorTypeTelescope H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr) (fieldResult : VExpr)
    (Htarget :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let parameterDecls :=
        (R.recursorHeaders.parameterSuffix.toRecursorContext
          H.elimLevelAdmissible).parameterDecls
      TrExprS H.outVEnv Us
        (abstractForallContext
          ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
            fieldDomains) [])
        (A.rule.target.abstractList A.rule.binders)
        (fieldResult.liftN
          (T.motives ++ T.minors).length A.rule.allArgs.size)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ (levels : List VLevel) (parameterTargets indexTargets : List VExpr),
        (fieldResult.liftN
            (T.motives ++ T.minors).length A.rule.allArgs.size).getAppFnArgs =
          (.const (decl.types[owner]'A.abstractOwner_lt).name levels,
            parameterTargets ++ indexTargets) ∧
        stats.levels.mapM (VLevel.ofLevel Us) = some levels ∧
        List.Forall₂
          (TrExprS H.outVEnv Us
            (abstractForallContext
              ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
                fieldDomains) []))
          ((stats.params.map fun arg =>
            arg.abstractList A.rule.binders).toList)
          parameterTargets ∧
        indexTargets.length = T.indices.length ∧
        List.Forall₂
          (TrExprS H.outVEnv Us
            (abstractForallContext
              ((parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
                fieldDomains) []))
          (((AddInductive.getIIndices stats A.rule.target).2.map fun arg =>
            arg.abstractList A.rule.binders).toList)
          indexTargets := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.recursorHeaders.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  dsimp only at Htarget
  have hvalid : AddInductive.isValidIndAppIdx stats A.rule.target owner =
      true := by
    have h := (checkPositivityStep.isValidIndApp?_some
      A.typing.target_valid).2
    simpa [A.typing_owner] using h
  have hconst := A.typing.validStats.indConstAt A.abstractOwner_lt
  have hhead : A.rule.target.getAppFn =
      .const (decl.types[owner]'A.abstractOwner_lt).name stats.levels :=
    checkPositivityStep.isValidIndAppIdx.constHead hvalid hconst
  have hheadAbstract :
      (A.rule.target.abstractList A.rule.binders).getAppFn =
        .const (decl.types[owner]'A.abstractOwner_lt).name stats.levels := by
    rw [Expr.getAppFn_abstractList, hhead]
    induction A.rule.binders <;> simp_all [Expr.abstractList, Expr.abstract1]
  rcases checkPositivityStep.TrExprS.constAppSpine Htarget hheadAbstract with
    ⟨levels, translatedArgs, hspine, hlevels, Hargs⟩
  let indices := (AddInductive.getIIndices stats A.rule.target).2
  have hsourcePrefix := A.typing.validStats.sourceParameterPrefix hvalid
  have hsourceArgs :
      (A.rule.target.abstractList A.rule.binders).getAppArgsList =
        (stats.params.map fun arg =>
            arg.abstractList A.rule.binders).toList ++
          (indices.map fun arg =>
            arg.abstractList A.rule.binders).toList := by
    rw [Expr.getAppArgsList_abstractList]
    have hsplit : A.rule.target.getAppArgsList =
        stats.params.toList ++ indices.toList := by
      calc
        A.rule.target.getAppArgsList =
            A.rule.target.getAppArgsList.take stats.params.size ++
              A.rule.target.getAppArgsList.drop stats.params.size :=
          (List.take_append_drop _ _).symm
        _ = stats.params.toList ++ indices.toList := by
          rw [hsourcePrefix]
          congr 1
          have hsuffix :
              (A.rule.target.getAppArgs[stats.params.size:]).toList =
                A.rule.target.getAppArgs.toList.drop stats.params.size := by
            rw [List.drop_eq_drop_min]
            simp only [Subarray.toList_eq, Array.array_toSubarray,
              Array.start_toSubarray, Array.stop_toSubarray, Nat.min_self,
              Array.toList_extract, List.extract_eq_take_drop,
              Array.length_toList]
            apply List.take_of_length_le
            simp
          simpa [indices, AddInductive.getIIndices,
            Expr.getAppArgs_toList] using hsuffix.symm
    rw [hsplit]
    simp
  rw [hsourceArgs] at Hargs
  rcases checkPositivityStep.List.Forall₂.split_left Hargs with
    ⟨parameterTargets, indexTargets, htranslatedArgs,
      HparameterTargets, HindexTargets⟩
  have hindicesLength : indices.size = stats.nindices[owner]! := by
    exact checkPositivityStep.getIIndices.index_arity
      A.typing.target_valid |>.trans (by simp [A.typing_owner])
  have hindexTargetsLength : indexTargets.length = T.indices.length := by
    have htranslated :=
      List.Forall₂.length_eq HindexTargets
    have harity := H.arities owner (by
      simpa [H.generated.length] using howner)
    rw [T.indices_length, harity, ← hindicesLength]
    simpa [indices] using htranslated.symm
  refine ⟨levels, parameterTargets, indexTargets, ?_, hlevels,
    HparameterTargets, hindexTargetsLength, ?_⟩
  · simpa [htranslatedArgs] using hspine
  · simpa [indices] using HindexTargets

/-- Insert the generated motive/minor block beneath the genuine constructor
fields.  `fieldDomains` is rebuilt from the lifted context prefix, so the
resulting canonical equation context remains valid for dependent fields. -/
theorem
    RecursorCheck.RuleAlignment.installedCheckedConstructorEquationContextWithFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : RecursorCheck R outEnv}
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
          (bvarSpine stats.params.size) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.recursorHeaders.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  rcases A.installedCheckedConstructorFieldFrame with
    ⟨T, originalDomains, fieldResult, introTarget, hparams, hfields,
      Htail, HfieldResidual, _HtailType, HtailTypeT, HfieldContext,
      HintroType, _Hintro, HintroShape⟩
  have HcachedTarget := A.cachedConstructorTargetOfFieldFrame
    originalDomains fieldResult hfields HfieldResidual
  let inserted := T.motives ++ T.minors
  have Wtarget := abstractForallContext.bvInsertBeforeInner
    parameterDecls.toCtx.reverse inserted originalDomains
  have HtargetWeak := HcachedTarget.weakBV H.outVEnvWF.ordered Wtarget
  have hsource := A.targetBinderLift_eq
    T originalDomains fieldResult hfields HcachedTarget
  have hsource' :
      ((A.rule.target.abstractList
          (A.rule.params_bound.fvars ++
            A.typing.fieldOpening.fvars)).liftLooseBVars'
        originalDomains.length inserted.length) =
        A.rule.target.abstractList A.rule.binders := by
    simpa [inserted, hfields] using hsource
  rw [hsource'] at HtargetWeak
  have Happ := VEnv.HasType.mkApps_wrapForalls_bvarSpine
    H.outVEnvWF.ordered HintroType
  let added := inserted.reverse
  let liftedPrefix := liftContextPrefix inserted.length originalDomains.reverse
  let fieldDomains := liftedPrefix.reverse
  have W : Ctx.LiftN inserted.length originalDomains.reverse.length
      (originalDomains.reverse ++ T.params.reverse)
      (liftedPrefix ++ added ++ T.params.reverse) := by
    simpa [liftedPrefix, added] using
      Ctx.LiftN.insertAfterPrefix originalDomains.reverse added T.params.reverse
  have Hweak := Happ.weakN H.outVEnvWF.ordered W
  have W0 : Ctx.LiftN inserted.length 0 T.params.reverse
      (added ++ T.params.reverse) := by
    exact .zero added (by simp [added])
  have HliftedType := HtailTypeT.weakN H.outVEnvWF.ordered W0
  rw [VExpr.liftN_wrapForalls] at HliftedType
  have hbase : OnCtx (added ++ T.params.reverse)
      (H.outVEnv.IsType Us.length) := by
    simpa [added, inserted, List.reverse_append, List.append_assoc] using
      T.prefixContext H.outVEnvWF.ordered
  have Hcontext : OnCtx
      (liftedPrefix ++ added ++ T.params.reverse)
      (H.outVEnv.IsType Us.length) := by
    have Hopened := VEnv.IsType.wrapForalls_inv H.outVEnvWF.ordered
      hbase HliftedType
    simpa [liftedPrefix, liftContextPrefix] using Hopened.1
  have hfieldDomains : fieldDomains.length = A.rule.allArgs.size := by
    simp [fieldDomains, liftedPrefix, hfields]
  refine ⟨T, originalDomains, fieldDomains, fieldResult, introTarget,
    hparams, hfields, ?_, Htail, HfieldContext, hfieldDomains, ?_, ?_, ?_,
    HintroShape⟩
  · simp [fieldDomains, liftedPrefix, inserted]
  · simpa [fieldDomains, liftedPrefix, added, inserted, List.reverse_append,
      List.append_assoc] using Hcontext
  · simpa [fieldDomains, liftedPrefix, added, inserted, hfields, List.reverse_append,
      List.append_assoc, Nat.add_comm, bvarSpine] using Hweak
  · simpa [parameterDecls, inserted, fieldDomains, liftedPrefix, added,
      hfields, List.append_assoc] using HtargetWeak

end VerifyInductive
end Lean4Lean
