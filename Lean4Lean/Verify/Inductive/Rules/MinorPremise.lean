import Lean4Lean.Verify.Inductive.Rules.MinorContext

/-! The selected minor premise of a rule: its source construction in the minor pass, the
constructor tail it shares with the constructor check, its typed telescope split into
constructor fields and induction hypotheses, and the alignment of its residual with the
constructor-motive application of the rule's left-hand side. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

open checkInductiveTypes.loopType

/-- Recover the exact source construction behind this rule's flattened minor
domain.  In particular, the retained second-pass shape names the same source
family and constructor slot as rule generation, rather than merely occupying
the same flattened minor position. -/
theorem
    RecursorCheck.RuleAlignment.installedSelectedMinorShape
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
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ D : FVarDeclAt H.localContext
          (H.recInfos.flatMap (·.minors)) minorIdx,
        ∃ _O : H.origins.FlatMinorBinderType D,
          ∃ S : MinorPremiseType,
            S.origin = D.type ∧
            S.localIndex = i ∧
            S.sourceConstructors = indTypes[owner]!.ctors ∧
            S.constructor = indTypes[owner]!.ctors[i] ∧
            S.fields.size = A.rule.allArgs.size ∧
            Nonempty (TypedMinorTraversalAt H.recursorWF S
              H.parameterSuffix.parameterDecls) ∧
            ∃ hypothesisOrigins,
              S.hypothesis_type_origins = some hypothesisOrigins ∧
              hypothesisOrigins.stats = stats ∧
              hypothesisOrigins.recInfos.map (·.motive) =
                H.recInfos.map (·.motive) ∧
              ∃ traversal : ConstructorFieldTraversal,
                S.traversal = some traversal ∧
                traversal.constructor = S.constructor ∧
                traversal.fields = S.fields ∧
                traversal.recursiveFields = S.recursiveFields ∧
                traversal.stats = stats ∧
                AddInductive.isValidIndApp? stats traversal.terminal = some
                  (AddInductive.getIIndices stats traversal.terminal).1 ∧
                S.motiveApp = (
                  let (motiveOwner, indices) :=
                    AddInductive.getIIndices stats traversal.terminal
                  Expr.app
                    (mkAppN H.recInfos[motiveOwner]!.motive indices)
                    (mkAppN
                      (mkAppN (.const S.constructor.name stats.levels)
                        stats.params)
                      S.fields)) ∧
                BindingContextLE traversal.rootContext H.localContext ∧
                BindingContextLE traversal.terminalContext H.localContext ∧
                BindingContextLE S.sourceFullContext H.localContext ∧
                traversal.recursivePositions =
                  A.typing.recursivePositions ∧
                A.minorShape = S ∧
                let sourceBinders := H.params.fvars ++
                  H.bindings.motives.fvars ++
                    H.bindings.flatMinors.fvars.take minorIdx
                TrExprS H.outVEnv Us
                    (abstractForallContext
                      (T.params ++ T.motives ++ T.minors.take minorIdx) [])
                    (D.type.abstractList sourceBinders) T.minors[minorIdx]! ∧
                  H.outVEnv.IsType Us.length
                    (abstractForallContext
                      (T.params ++ T.motives ++
                        T.minors.take minorIdx) []).toCtx
                    T.minors[minorIdx]! := by
  dsimp only
  rcases A.installedSelectedMinorDomain with
    ⟨T, D, O, _discardedShape, Hdomain, HdomainType⟩
  have hposition := RecursorCheck.RuleAlignment.selectedMinorOriginPosition
    (H := H) (howner := howner) (hctor := hctor) O
  have hsourceOwner : O.owner < indTypes.size := by
    rw [hposition.1]
    exact A.sourceOwner_lt
  have hshapeBound : O.localIndex <
      H.origins.minorTypes[O.owner]!.size := by
    rw [(H.origins.minors O.owner O.owner_lt).size_eq]
    simpa [getElem!_pos H.recInfos O.owner O.owner_lt] using O.local_lt
  let S := H.origins.minorShapes O.owner O.owner_lt O.localIndex hshapeBound
  have Hsource : S.origin =
        H.origins.minorTypes[O.owner]![O.localIndex]! ∧
      S.localIndex = O.localIndex ∧
      S.sourceConstructors = indTypes[O.owner]!.ctors ∧
      S.HasInductionHypothesisTypes stats H.recInfos ∧
        ∃ traversal, S.traversal = some traversal ∧
          traversal.constructor = S.constructor ∧
          traversal.fields = S.fields ∧
          traversal.recursiveFields = S.recursiveFields ∧
          traversal.stats = stats ∧
          AddInductive.isValidIndApp? stats traversal.terminal = some
            (AddInductive.getIIndices stats traversal.terminal).1 ∧
          S.motiveApp = (
            let (motiveOwner, indices) :=
              AddInductive.getIIndices stats traversal.terminal
            Expr.app
              (mkAppN H.recInfos[motiveOwner]!.motive indices)
              (mkAppN
                (mkAppN (.const S.constructor.name stats.levels)
                  stats.params)
                S.fields)) ∧
          BindingContextLE traversal.rootContext H.localContext ∧
          BindingContextLE traversal.terminalContext H.localContext ∧
          BindingContextLE S.sourceFullContext H.localContext := by
    simpa [S] using H.minorSources.rows O.owner O.owner_lt hsourceOwner
      O.localIndex hshapeBound
  have horigin : S.origin = D.type :=
    Hsource.1.trans O.originType_eq.symm
  have hlocal : S.localIndex = i := Hsource.2.1.trans hposition.2
  have hconstructorsAtOrigin :
      S.sourceConstructors = indTypes[O.owner]!.ctors := by
    simpa [S] using Hsource.2.2.1
  have hconstructors :
      S.sourceConstructors = indTypes[owner]!.ctors := by
    simpa [hposition.1] using hconstructorsAtOrigin
  rcases Hsource.2.2.2 with
    ⟨HhypothesisOrigins, traversal, htraversal, htraversalConstructor,
      htraversalFields, htraversalRecursiveFields, hstats, hvalid,
      hmotiveApp,
      hrootContext, hterminalContext, hsourceContext⟩
  rcases S.hypothesisTypeOrigins_exists stats H.recInfos
      HhypothesisOrigins with
    ⟨hypothesisOrigins, hhypothesisOrigins, hhypothesisStats,
      hhypothesisRecInfos⟩
  have hconstructor : S.constructor = indTypes[owner]!.ctors[i] := by
    have hsourceConstructor := S.sourceConstructor
    rw [hconstructors, hlocal] at hsourceConstructor
    simpa [hctor] using hsourceConstructor.symm
  have hprefixTraversal := traversal.parameterPrefix
  rw [hstats, htraversalConstructor, hconstructor] at hprefixTraversal
  have hparameterTail :
      traversal.parameterTail = A.typing.parameterTail :=
    hprefixTraversal.tail_eq A.typing.parameterPrefix
  have hsemanticResidual :
      A.typing.fieldOpening.residual.isForall = false := by
    rw [← A.typing.fieldOpening.closed, Expr.abstractList_isForall]
    exact A.typing.target_not_forall
  have hfieldCount : S.fields.size = A.rule.allArgs.size := by
    have HtraversalTelescope := traversal.fieldTelescope
    rw [htraversalFields, hparameterTail] at HtraversalTelescope
    exact (HtraversalTelescope.eq_of_residual_not_forall
      A.typing.fieldOpening.telescope
      traversal.fieldResidual_not_forall hsemanticResidual).1
  have Hsemantic :
      Nonempty (TypedMinorTraversalAt H.recursorWF S
        H.parameterSuffix.parameterDecls) := by
    simpa [S] using
      H.minorTyping O.owner O.owner_lt O.localIndex hshapeBound
  let P := A.minorOrigin
  have hshapeCanonical :
      H.origins.minorShapes O.owner O.owner_lt O.localIndex hshapeBound =
        H.origins.minorShapes owner P.owner_lt i P.local_lt := by
    exact H.origins.minorShapes_congr hposition.1 O.owner_lt P.owner_lt
      hposition.2 hshapeBound P.local_lt
  have hproducerShape : P.producer.minorShape = S :=
    P.shape_eq.trans hshapeCanonical.symm
  have hproducerTraversal := P.producer.minorTraversal_eq
  rw [hproducerShape] at hproducerTraversal
  have hminorTraversal : P.producer.minorTraversal = traversal :=
    Option.some.inj (hproducerTraversal.symm.trans htraversal)
  have hpositions : traversal.recursivePositions =
      A.typing.recursivePositions := by
    rw [← hminorTraversal]
    exact P.producer.decisionPositions_eq
  exact ⟨T, D, O, S, horigin, hlocal, hconstructors, hconstructor,
    hfieldCount, Hsemantic, hypothesisOrigins, hhypothesisOrigins,
    hhypothesisStats,
    hhypothesisRecInfos,
    traversal, htraversal, htraversalConstructor,
    htraversalFields, htraversalRecursiveFields, hstats, hvalid,
    hmotiveApp,
    hrootContext,
    hterminalContext, hsourceContext, hpositions, hproducerShape,
    Hdomain, HdomainType⟩

/-- Recover the exact translation-side context in which the selected minor
source was built, together with its executable extension into the rule's
recursor context.  This is the semantic strengthening of the structural
`BindingContextLE` returned by `installedSelectedMinorShape`. -/
theorem
    RecursorCheck.RuleAlignment.installedSelectedMinorSource
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
    ∃ S : MinorPremiseType,
      ∃ HS : TypedMinorTraversalAt H.recursorWF S
          H.parameterSuffix.parameterDecls,
        S.localIndex = i ∧
        HS.semantic.traversal.parameterTail =
          A.typing.parameterTail := by
  rcases A.installedSelectedMinorDomain with
    ⟨_T, _D, O, _discardedShape, _Hdomain, _HdomainType⟩
  have hposition := RecursorCheck.RuleAlignment.selectedMinorOriginPosition
    (H := H) (howner := howner) (hctor := hctor) O
  have hsourceOwner : O.owner < indTypes.size := by
    rw [hposition.1]
    exact A.sourceOwner_lt
  have hshapeBound : O.localIndex <
      H.origins.minorTypes[O.owner]!.size := by
    rw [(H.origins.minors O.owner O.owner_lt).size_eq]
    simpa [getElem!_pos H.recInfos O.owner O.owner_lt] using O.local_lt
  let S := H.origins.minorShapes O.owner O.owner_lt O.localIndex hshapeBound
  have Hsource := H.minorSources.rows O.owner O.owner_lt hsourceOwner
    O.localIndex hshapeBound
  have hlocal : S.localIndex = i := Hsource.2.1.trans hposition.2
  have hconstructorsAtOrigin :
      S.sourceConstructors = indTypes[O.owner]!.ctors := by
    simpa [S] using Hsource.2.2.1
  have hconstructors :
      S.sourceConstructors = indTypes[owner]!.ctors := by
    simpa [hposition.1] using hconstructorsAtOrigin
  have hconstructor : S.constructor = indTypes[owner]!.ctors[i] := by
    have hsourceConstructor := S.sourceConstructor
    rw [hconstructors, hlocal] at hsourceConstructor
    simpa [hctor] using hsourceConstructor.symm
  rcases Hsource.2.2.2.2 with
    ⟨traversal, htraversal, htraversalConstructor, _htraversalFields,
      _htraversalRecursiveFields, hstats, _hrootContext,
      _hterminalContext, _hsourceContext⟩
  rcases H.minorTyping O.owner O.owner_lt O.localIndex hshapeBound with
    ⟨HS⟩
  have hsemanticTraversal : HS.semantic.traversal = traversal :=
    Option.some.inj (HS.semantic.traversal_eq.symm.trans htraversal)
  have hprefixTraversal := traversal.parameterPrefix
  rw [hstats, htraversalConstructor, hconstructor] at hprefixTraversal
  have hparameterTail :
      traversal.parameterTail = A.typing.parameterTail :=
    hprefixTraversal.tail_eq A.typing.parameterPrefix
  exact ⟨S, HS, hlocal, hsemanticTraversal.symm ▸ hparameterTail⟩

/-- Transport the shared constructor tail retained by the first minor pass
into the exact parameter context and environment used by rule
generation.  This is the first semantic join between the two executable
passes; the source expression is identified structurally, while its target
is preserved from the first pass. -/
theorem
    RecursorCheck.RuleAlignment.installedSelectedMinorSharedTail
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
    ∃ S : MinorPremiseType,
      ∃ HS : TypedMinorTraversalAt H.recursorWF S
          H.parameterSuffix.parameterDecls,
        ∃ target,
          S.localIndex = i ∧
          HS.semantic.traversal.parameterTail =
            A.typing.parameterTail ∧
          TrExprS H.outVEnv Us parameterDecls
            A.typing.parameterTail target := by
  dsimp only
  rcases A.installedSelectedMinorSource with
    ⟨S, HS, hlocal, htail⟩
  rcases HS.semantic.parameterTranslationAtSuffix with
    ⟨target, Htarget⟩
  have hrootLE : HS.semantic.rootWF.venv ≤ H.outVEnv := by
    rw [← HS.semantic.fieldsRecent.contextExtension.venv_eq,
      ← HS.semantic.hypothesesRecent.contextExtension.venv_eq,
      ← HS.semantic.extension.venv_eq, H.recursorEnv]
    exact H.installed.le
  have Htarget' := Htarget.mono hrootLE
  have HtargetAtParameters : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      H.parameterSuffix.parameterDecls A.typing.parameterTail target := by
    simpa only [HS.parameterDecls_eq, htail] using Htarget'
  have HtargetFinal : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
      A.typing.parameterTail target := by
    simpa only [← H.parameterDecls] using HtargetAtParameters
  exact ⟨S, HS, target, hlocal, htail, HtargetFinal⟩

/-- The target retained from first-pass minor construction and the field
telescope reconstructed during rule generation are definitionally
equal, because they translate the same constructor tail in the same exact
parameter context. -/
theorem
    RecursorCheck.RuleAlignment.installedSelectedMinorSharedTailDefEq
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
    ∃ S : MinorPremiseType,
      ∃ HS : TypedMinorTraversalAt H.recursorWF S
          H.parameterSuffix.parameterDecls,
        ∃ target fieldDomains fieldResult,
          S.localIndex = i ∧
          HS.semantic.traversal.parameterTail =
            A.typing.parameterTail ∧
          fieldDomains.length = A.rule.allArgs.size ∧
          TrExprS H.outVEnv Us parameterDecls
            A.typing.parameterTail target ∧
          TrExprS H.outVEnv Us parameterDecls
            A.typing.parameterTail
            (VExpr.wrapForalls fieldDomains fieldResult) ∧
          H.outVEnv.IsDefEqU Us.length parameterDecls.toCtx target
            (VExpr.wrapForalls fieldDomains fieldResult) := by
  dsimp only
  rcases A.installedSelectedMinorSharedTail with
    ⟨S, HS, target, hlocal, htail, Htarget⟩
  rcases A.installedCheckedConstructorFieldFrame with
    ⟨_T, fieldDomains, fieldResult, _introTarget, _hparams, hfields,
      Hfields, _HfieldResidual, _HtailType, _HtailTypeT,
      _HfieldContext, _HintroType, _Hintro, _HintroShape⟩
  have hbaseLE :
      (R.context.toAdmissibleRecursorContextWF
        H.elimLevelAdmissible).venv ≤ H.outVEnv := by
    simpa only [ContextWF.toAdmissibleRecursorContextWF_venv] using
      H.installed.le
  have HparameterWF : VLCtx.WF H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls :=
    (R.recursorHeaders.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterWF.mono hbaseLE
  have Hsame := Htarget.uniq H.outVEnvWF
    (.refl H.outVEnvWF HparameterWF) Hfields
  exact ⟨S, HS, target, fieldDomains, fieldResult, hlocal, htail,
    hfields, Htarget, Hfields, Hsame⟩

/-- Binder-by-binder form of the shared-tail equality.  It is deliberately a
context conversion rather than list equality: the first minor pass and the
later constructor check may translate unannotated domains to
different, convertible representatives. -/
theorem
    RecursorCheck.RuleAlignment.installedSelectedMinorSharedFieldContext
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
    ∃ S : MinorPremiseType,
      ∃ HS : TypedMinorTraversalAt H.recursorWF S
          H.parameterSuffix.parameterDecls,
        ∃ minorFieldDomains minorFieldResult checkedFieldDomains
            checkedFieldResult,
          S.localIndex = i ∧
          HS.semantic.traversal.parameterTail =
            A.typing.parameterTail ∧
          minorFieldDomains.length = A.rule.allArgs.size ∧
          checkedFieldDomains.length = A.rule.allArgs.size ∧
          TrExprS H.outVEnv Us parameterDecls
            A.typing.parameterTail
            (VExpr.wrapForalls minorFieldDomains minorFieldResult) ∧
          TrExprS H.outVEnv Us parameterDecls
            A.typing.parameterTail
            (VExpr.wrapForalls checkedFieldDomains checkedFieldResult) ∧
          VEnv.IsDefEqCtx H.outVEnv Us.length []
            (minorFieldDomains.reverse ++ parameterDecls.toCtx)
            (checkedFieldDomains.reverse ++ parameterDecls.toCtx) := by
  dsimp only
  rcases A.installedSelectedMinorSharedTailDefEq with
    ⟨S, HS, target, checkedFieldDomains, checkedFieldResult, hlocal,
      htail, hcheckedLength, Hminor, Hchecked, Hsame⟩
  rcases TrExprS.forallTelescope_shape A.typing.fieldOpening.telescope
      Hminor with
    ⟨minorFieldDomains, minorFieldResult, hminorLength, htarget⟩
  have Hsame' : H.outVEnv.IsDefEqU
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls.toCtx
      (VExpr.wrapForalls minorFieldDomains minorFieldResult)
      (VExpr.wrapForalls checkedFieldDomains checkedFieldResult) := by
    rw [← htarget]
    exact Hsame
  have hbaseLE :
      (R.context.toAdmissibleRecursorContextWF
        H.elimLevelAdmissible).venv ≤ H.outVEnv := by
    simpa only [ContextWF.toAdmissibleRecursorContextWF_venv] using
      H.installed.le
  have HparameterWF : VLCtx.WF H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls :=
    (R.recursorHeaders.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterWF.mono hbaseLE
  have Hbase : VEnv.IsDefEqCtx H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls.toCtx
      (R.recursorHeaders.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls.toCtx :=
    .refl HparameterWF.toCtx
  have Hfields := VEnv.IsDefEqU.wrapForalls_context H.outVEnvWF Hbase
    (hminorLength.trans hcheckedLength.symm) Hsame'
  exact ⟨S, HS, minorFieldDomains, minorFieldResult,
    checkedFieldDomains, checkedFieldResult, hlocal, htail,
    hminorLength, hcheckedLength, by simpa [htarget] using Hminor,
    Hchecked, Hfields⟩

/-- Binder-by-binder strengthening of the selected minor arity result.  The
complete source telescope is retained together with the translation
and typehood of every abstract domain, so later applications can compare a
particular field or recursive-hypothesis domain rather than only their
cardinalities. -/
theorem
    RecursorCheck.RuleAlignment.installedSelectedMinorTypedTelescope
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
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : MinorPremiseType,
        ∃ hypothesisOrigins : MinorInductionHypothesisTypes
            S.sourceFullContext S.recursiveFields S.hypotheses,
        ∃ traversal : ConstructorFieldTraversal,
        S.hypothesis_type_origins = some hypothesisOrigins ∧
        hypothesisOrigins.stats = stats ∧
        hypothesisOrigins.recInfos.map (·.motive) =
          H.recInfos.map (·.motive) ∧
        S.traversal = some traversal ∧
        traversal.fields = S.fields ∧
        traversal.recursiveFields = S.recursiveFields ∧
        traversal.stats = stats ∧
        traversal.parameterTail = A.typing.parameterTail ∧
        traversal.recursivePositions = A.typing.recursivePositions ∧
        S.localIndex = i ∧
        S.fields.size = A.rule.allArgs.size ∧
        S.hypotheses.size = A.rule.recursiveArgs.size ∧
        BindingContextLE S.sourceFullContext H.localContext ∧
        Nonempty (TypedMinorTraversalAt H.recursorWF S
          H.parameterSuffix.parameterDecls) ∧
        A.minorShape = S ∧
        let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
          H.bindings.flatMinors.fvars.take minorIdx
        Expr.ForallTelescopeTypeTranslation H.outVEnv Us
          (abstractForallContext
            (T.params ++ T.motives ++ T.minors.take minorIdx) [])
          (S.origin.abstractList sourceBinders)
          (A.rule.allArgs.size + A.rule.recursiveArgs.size)
          T.minors[minorIdx]! := by
  dsimp only
  rcases A.installedSelectedMinorShape with
    ⟨T, D, _O, S, horigin, hlocal, _hconstructors, hconstructor,
      hfieldCount, Hsemantic, hypothesisOrigins, hhypothesisOrigins,
      hhypothesisStats, hhypothesisRecInfos, traversal, htraversal,
      htraversalConstructor,
      htraversalFields, htraversalRecursiveFields, hstats, _hvalid,
      _hmotiveApp,
      _hrootContext,
      hterminalContext, hsourceContext, hpositions, hproducerShape,
      Hdomain, HdomainType⟩
  rcases Hsemantic with ⟨HS⟩
  have hsemanticTraversal : HS.semantic.traversal = traversal := by
    exact Option.some.inj (HS.semantic.traversal_eq.symm.trans htraversal)
  have hprefixTraversal := traversal.parameterPrefix
  rw [hstats, htraversalConstructor, hconstructor] at hprefixTraversal
  have hparameterTail :
      traversal.parameterTail = A.typing.parameterTail :=
    hprefixTraversal.tail_eq A.typing.parameterPrefix
  have hhypotheses : S.hypotheses.size = A.rule.recursiveArgs.size :=
    S.hypotheses_size_eq_rule traversal A.typing
      htraversalRecursiveFields hpositions
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take
      (recursorMinorOffset indTypes owner + i)
  rcases S.originTelescope with ⟨sourceResidual, Hsource⟩
  have Habstract := Hsource.abstractList sourceBinders
  rw [hfieldCount, hhypotheses] at Habstract
  have Hdomain' : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (T.params ++ T.motives ++
          T.minors.take (recursorMinorOffset indTypes owner + i)) [])
      (S.origin.abstractList sourceBinders)
      T.minors[recursorMinorOffset indTypes owner + i]! := by
    rw [horigin]
    exact Hdomain
  exact ⟨T, S, hypothesisOrigins, traversal, hhypothesisOrigins,
    hhypothesisStats, hhypothesisRecInfos, htraversal, htraversalFields,
    htraversalRecursiveFields, hstats, hparameterTail, hpositions,
    hlocal, hfieldCount, hhypotheses, hsourceContext, ⟨HS⟩,
    hproducerShape,
    Expr.ForallTelescopeTypeTranslation.ofTrExprS
      Habstract Hdomain' HdomainType⟩
/-- Independently replay the complete selected-minor telescope in the exact
non-contiguous source scope, and close that scope around the source
declaration.  The two certificates expose the same dependency-selected target both as a
body below the selected outer prefix and as a completely closed telescope.
This is the comparison frame used to relate the installed minor domains to
the semantic field and recursive-result domains. -/
theorem
    RecursorCheck.RuleAlignment.installedSelectedMinorExactClosedTelescope
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
    (hpositive : 0 < A.rule.allArgs.size + A.rule.recursiveArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : MinorPremiseType,
      ∃ HS : TypedMinorTraversalAt H.recursorWF S
          H.parameterSuffix.parameterDecls,
      ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.ScopeEmbedding
          H.outVEnv Us scope H.recursorWF.mlctx.vlctx,
      ∃ narrowTarget,
      ∃ fullTarget,
        fullTarget = HS.semantic.unannotatedTarget.lift'
          (HS.semantic.extension.shift.consN 0) ∧
        S.fields.size = A.rule.allArgs.size ∧
        S.hypotheses.size = A.rule.recursiveArgs.size ∧
        HS.semantic.traversal.parameterTail = A.typing.parameterTail ∧
        scope.fvars = sourceBinders.reverse ∧
        Hscope.shift = fvarSelectionLift H.recursorWF.mlctx.vlctx.fvars
          (· ∈ sourceBinders) ∧
        TrExprS H.outVEnv Us H.recursorWF.mlctx.vlctx
          S.origin fullTarget ∧
        H.outVEnv.IsDefEqU Us.length H.recursorWF.mlctx.vlctx.toCtx
          fullTarget (narrowTarget.lift' Hscope.shift) ∧
        Hscope.sourceTelescope.closeSource S.origin =
          H.localContext.lctx.mkForall
            (sourceBinders.map Expr.fvar).toArray S.origin ∧
        VEnv.IsDefEqCtx H.outVEnv Us.length [] scope.toCtx
          (T.params ++ T.motives ++ T.minors.take minorIdx).reverse ∧
        Expr.ForallTelescopeTypeTranslation H.outVEnv Us
          (abstractForallContext scope.toCtx.reverse [])
          (S.origin.abstractList sourceBinders)
          (A.rule.allArgs.size + A.rule.recursiveArgs.size)
          narrowTarget ∧
        Expr.ForallTelescopeTypeTranslation H.outVEnv Us []
          (H.localContext.lctx.mkForall
            (sourceBinders.map Expr.fvar).toArray S.origin)
          scope.length
          (VExpr.wrapForalls scope.toCtx.reverse narrowTarget) ∧
        Expr.ForallTelescopeTypeTranslation H.outVEnv Us
          (abstractForallContext
            (T.params ++ T.motives ++ T.minors.take minorIdx) [])
          (S.origin.abstractList sourceBinders)
          (A.rule.allArgs.size + A.rule.recursiveArgs.size)
          T.minors[minorIdx]! := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  rcases A.installedSelectedMinorTypedTelescope with
    ⟨T, S, _hypothesisOrigins, traversal,
      _hhypothesisOrigins, _hhypothesisStats, _hhypothesisRecInfos,
      htraversal, _htraversalFields, _htraversalRecursiveFields,
      _htraversalStats, hparameterTail, _hpositions, _hlocal,
      hfields, hhypotheses, _hsourceContext, Hsemantic, _hproducerShape,
      Hinstalled⟩
  rcases Hsemantic with ⟨HS⟩
  have hsemanticTraversal : HS.semantic.traversal = traversal :=
    Option.some.inj (HS.semantic.traversal_eq.symm.trans htraversal)
  have hsemanticParameterTail :
      HS.semantic.traversal.parameterTail = A.typing.parameterTail :=
    (congrArg ConstructorFieldTraversal.parameterTail
      hsemanticTraversal).trans hparameterTail
  rcases A.installedSelectedMinorPrefixDefEqCtx with
    ⟨T₀, scope, Hscope, hscope, hscopeShift, hscopeSource, Hprefix₀⟩
  rcases T₀.groupsResult_eq T with
    ⟨hparams, hmotives, hminors, _hindices, _hmajor, _hresult⟩
  rw [hparams, hmotives, hminors] at Hprefix₀
  have Hprefix : VEnv.IsDefEqCtx H.outVEnv Us.length [] scope.toCtx
      (T.params ++ T.motives ++ T.minors.take minorIdx).reverse := by
    simpa using Hprefix₀
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  have hscopeSourceOut : Hscope.sourceTelescope.closeSource S.origin =
      H.localContext.lctx.mkForall
        (sourceBinders.map Expr.fvar).toArray S.origin := by
    exact hscopeSource S.origin
  have HsourceOrigin : TrExprS HS.semantic.sourceWF.venv Us
      HS.semantic.sourceWF.mlctx.vlctx S.origin
      HS.semantic.unannotatedTarget := by
    rw [← S.unannotated_eq]
    simpa only [HS.semantic.extension.venv_eq] using
      HS.semantic.consumption.unannotated
  have Hfull₀ := HS.semantic.extension.weakTrExprS HsourceOrigin
  let fullTarget := HS.semantic.unannotatedTarget.lift'
    (HS.semantic.extension.shift.consN 0)
  have Hfull : TrExprS H.outVEnv Us H.recursorWF.mlctx.vlctx S.origin
      fullTarget :=
    Hfull₀.mono hbase
  have HinstalledTr := Hinstalled.translation
  have HabstractCtx : VLCtx.IsDefEq H.outVEnv Us.length
      (abstractForallContext (T.params ++ T.motives ++ T.minors.take minorIdx) [])
      (abstractForallContext scope.toCtx.reverse []) := by
    have h := VLCtx.IsDefEq.ofDefEqCtxAnonymous (Hprefix.symm H.outVEnvWF.ordered)
    simpa [abstractForallContext] using h
  obtain ⟨narrowTarget, HnarrowAbs⟩ :=
    HinstalledTr.defeqDFC H.outVEnvWF HabstractCtx
  have hsourceBinders : sourceBinders = scope.fvars.reverse := by
    rw [hscope, List.reverse_reverse]
  have Hnarrow : TrExprS H.outVEnv Us scope S.origin narrowTarget := by
    apply Hscope.instantiateAll H.outVEnvWF
    rw [← hsourceBinders]
    exact HnarrowAbs
  have HfullEq : H.outVEnv.IsDefEqU Us.length H.recursorWF.mlctx.vlctx.toCtx
      fullTarget (narrowTarget.lift' Hscope.shift) :=
    (Hscope.fullTargetEq H.outVEnvWF Hnarrow
      (Hfull.trExpr H.outVEnvWF
        (Hscope.context.symm H.outVEnvWF.ordered).wf)).symm
  rcases S.originTelescope with ⟨sourceResidual, HsourceTelescope⟩
  have HsourceTelescope' : Expr.ForallTelescope S.origin
      (A.rule.allArgs.size + A.rule.recursiveArgs.size) sourceResidual := by
    simpa [hfields, hhypotheses] using HsourceTelescope
  have HnarrowType : H.outVEnv.IsType Us.length scope.toCtx narrowTarget :=
    TrExprS.isType_of_forallTelescope HsourceTelescope' hpositive Hnarrow
  have HabstractTelescope :=
    HsourceTelescope'.abstractList sourceBinders
  have HabstractTranslation := Hscope.abstractAll H.outVEnvWF Hnarrow
  rw [hscope, List.reverse_reverse] at HabstractTranslation
  have HabstractType : H.outVEnv.IsType Us.length
      (abstractForallContext scope.toCtx.reverse []).toCtx narrowTarget := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HnarrowType
  have HabstractTyped :=
    Expr.ForallTelescopeTypeTranslation.ofTrExprS
      HabstractTelescope HabstractTranslation HabstractType
  have HclosedTyped := Hscope.closeTypedTelescope H.outVEnvWF
    Hnarrow HnarrowType
  rw [hscopeSourceOut] at HclosedTyped
  exact ⟨T, S, HS, scope, Hscope, narrowTarget, fullTarget,
    rfl, hfields, hhypotheses, hsemanticParameterTail, hscope, hscopeShift,
    Hfull, HfullEq, hscopeSourceOut, Hprefix, HabstractTyped,
    HclosedTyped, Hinstalled⟩

/-- Expose the typed selected-minor telescope in the two semantic blocks used
by its eventual application: genuine constructor fields followed by recursive
hypotheses.  It retains the
binder-by-binder source/target translation certificate. -/
theorem
    RecursorCheck.RuleAlignment.installedSelectedMinorTypedSplit
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
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : MinorPremiseType,
        ∃ hypothesisOrigins : MinorInductionHypothesisTypes
            S.sourceFullContext S.recursiveFields S.hypotheses,
        ∃ traversal : ConstructorFieldTraversal,
        ∃ fieldDomains hypothesisDomains sourceResidual targetResidual,
          S.hypothesis_type_origins = some hypothesisOrigins ∧
          hypothesisOrigins.stats = stats ∧
          hypothesisOrigins.recInfos.map (·.motive) =
            H.recInfos.map (·.motive) ∧
          S.traversal = some traversal ∧
          traversal.fields = S.fields ∧
          traversal.recursiveFields = S.recursiveFields ∧
          traversal.stats = stats ∧
          traversal.parameterTail = A.typing.parameterTail ∧
          traversal.recursivePositions = A.typing.recursivePositions ∧
          S.localIndex = i ∧
          S.fields.size = A.rule.allArgs.size ∧
          S.hypotheses.size = A.rule.recursiveArgs.size ∧
          BindingContextLE S.sourceFullContext H.localContext ∧
          Nonempty (TypedMinorTraversalAt H.recursorWF S
            H.parameterSuffix.parameterDecls) ∧
          A.minorShape = S ∧
          fieldDomains.length = A.rule.allArgs.size ∧
          hypothesisDomains.length = A.rule.recursiveArgs.size ∧
          T.minors[minorIdx]! = VExpr.wrapForalls
            (fieldDomains ++ hypothesisDomains) targetResidual ∧
          let sourceBinders := H.params.fvars ++
            H.bindings.motives.fvars ++
              H.bindings.flatMinors.fvars.take minorIdx
          Expr.ForallTelescope
            (S.origin.abstractList sourceBinders)
            (A.rule.allArgs.size + A.rule.recursiveArgs.size)
            sourceResidual ∧
          TrExprS H.outVEnv Us
            (abstractForallContext (fieldDomains ++ hypothesisDomains)
              (abstractForallContext
                (T.params ++ T.motives ++ T.minors.take minorIdx) []))
            sourceResidual targetResidual ∧
          H.outVEnv.IsType Us.length
            (abstractForallContext (fieldDomains ++ hypothesisDomains)
              (abstractForallContext
                (T.params ++ T.motives ++ T.minors.take minorIdx) [])).toCtx
            targetResidual ∧
          Expr.ForallTelescopeTypeTranslation H.outVEnv Us
            (abstractForallContext
              (T.params ++ T.motives ++ T.minors.take minorIdx) [])
            (S.origin.abstractList sourceBinders)
            (A.rule.allArgs.size + A.rule.recursiveArgs.size)
            T.minors[minorIdx]! := by
  dsimp only
  rcases A.installedSelectedMinorTypedTelescope with
    ⟨T, S, hypothesisOrigins, traversal,
      hhypothesisOrigins, hhypothesisStats, hhypothesisRecInfos, htraversal,
      htraversalFields, htraversalRecursiveFields, htraversalStats,
      hparameterTail, hpositions,
      hlocal, hsourceFields, hsourceHypotheses, hsourceContext,
      HminorSemantic, hproducerShape, Htyped⟩
  rcases Htyped.toWrapForalls with
    ⟨domains, sourceResidual, targetResidual, hlength,
      Hsource, htarget, Hresidual, HresidualType⟩
  let fieldDomains := domains.take A.rule.allArgs.size
  let hypothesisDomains := domains.drop A.rule.allArgs.size
  have hfieldsLE : A.rule.allArgs.size ≤ domains.length := by omega
  have hfields : fieldDomains.length = A.rule.allArgs.size := by
    simp [fieldDomains, List.length_take, Nat.min_eq_left hfieldsLE]
  have hhypotheses : hypothesisDomains.length =
      A.rule.recursiveArgs.size := by
    simp [hypothesisDomains, List.length_drop, hlength]
  have hdomains : domains = fieldDomains ++ hypothesisDomains := by
    exact (List.take_append_drop A.rule.allArgs.size domains).symm
  rw [hdomains] at htarget Hresidual HresidualType
  exact ⟨T, S, hypothesisOrigins, traversal, fieldDomains,
    hypothesisDomains, sourceResidual, targetResidual,
    hhypothesisOrigins, hhypothesisStats, hhypothesisRecInfos, htraversal,
    htraversalFields, htraversalRecursiveFields, htraversalStats,
    hparameterTail, hpositions,
    hlocal, hsourceFields, hsourceHypotheses, hsourceContext, HminorSemantic,
    hproducerShape, hfields, hhypotheses, htarget, Hsource, Hresidual,
    HresidualType, Htyped⟩

/-- Positive-arity selected-minor residual with all source-shape facts
retained on one witness.  The ordinary residual endpoint hides
the first-pass constructor shape; the equation type comparison needs
that shape to identify the residual motive application with the independently
reconstructed constructor motive on the LHS. -/
theorem
    RecursorCheck.RuleAlignment.installedSelectedMinorAlignedResidual
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
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : MinorPremiseType,
      ∃ traversal : ConstructorFieldTraversal,
      ∃ _HS : TypedMinorTraversalAt H.recursorWF S
          H.parameterSuffix.parameterDecls,
      ∃ hypothesisOrigins : MinorInductionHypothesisTypes
          S.sourceFullContext S.recursiveFields S.hypotheses,
      ∃ fieldDomains hypothesisDomains targetResidual,
        hypothesisOrigins.stats = stats ∧
        hypothesisOrigins.recInfos.map (·.motive) =
          H.recInfos.map (·.motive) ∧
        S.constructor = indTypes[owner]!.ctors[i] ∧
        traversal.fields = S.fields ∧
        traversal.fieldFVars = S.fields_bound.fvars ∧
        traversal.terminal.abstractList S.fields_bound.fvars =
          A.rule.target.abstractList A.typing.fieldOpening.fvars ∧
        (AddInductive.getIIndices stats traversal.terminal).1 = owner ∧
        AddInductive.isValidIndApp? stats traversal.terminal = some owner ∧
        S.motiveApp =
          Expr.app
            (mkAppN H.recInfos[owner]!.motive
              (AddInductive.getIIndices stats traversal.terminal).2)
            (mkAppN
              (mkAppN (.const S.constructor.name stats.levels) stats.params)
              S.fields) ∧
        S.fields.size = A.rule.allArgs.size ∧
        S.hypotheses.size = A.rule.recursiveArgs.size ∧
        fieldDomains.length = A.rule.allArgs.size ∧
        hypothesisDomains.length = A.rule.recursiveArgs.size ∧
        T.minors[minorIdx]! = VExpr.wrapForalls
          (fieldDomains ++ hypothesisDomains) targetResidual ∧
        TrExprS H.outVEnv Us
          (abstractForallContext (fieldDomains ++ hypothesisDomains)
            (abstractForallContext
              (T.params ++ T.motives ++ T.minors.take minorIdx) []))
          (((S.motiveApp.abstractList S.hypotheses_bound.fvars).abstractList
            S.fields_bound.fvars S.hypotheses.size).abstractList
              sourceBinders
              (A.rule.allArgs.size + A.rule.recursiveArgs.size))
          targetResidual ∧
        H.outVEnv.IsType Us.length
          (abstractForallContext (fieldDomains ++ hypothesisDomains)
            (abstractForallContext
              (T.params ++ T.motives ++ T.minors.take minorIdx) [])).toCtx
          targetResidual := by
  dsimp only
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  rcases A.installedSelectedMinorShape with
    ⟨T, D, _O, S, horigin, _hlocal, _hconstructors, hconstructor,
      hsourceFields, ⟨HS⟩, hypothesisOrigins,
      _hhypothesisOrigins, hhypothesisStats, hhypothesisRecInfos,
      traversal, htraversal, htraversalConstructor, htraversalFields,
      htraversalRecursiveFields, htraversalStats, hvalid, hmotiveApp,
      _hrootContext, hterminalContext, _hsourceContext, hpositions,
      _hproducerShape, Hdomain, HdomainType⟩
  have hprefixTraversal := traversal.parameterPrefix
  rw [htraversalStats, htraversalConstructor, hconstructor] at hprefixTraversal
  have hparameterTail :
      traversal.parameterTail = A.typing.parameterTail :=
    hprefixTraversal.tail_eq A.typing.parameterPrefix
  have hsourceHypotheses : S.hypotheses.size =
      A.rule.recursiveArgs.size :=
    S.hypotheses_size_eq_rule traversal A.typing
      htraversalRecursiveFields hpositions
  rcases S.originTelescope with ⟨sourceResidual, Hsource⟩
  have Habstract := Hsource.abstractList sourceBinders
  rw [hsourceFields, hsourceHypotheses] at Habstract
  have Hdomain' : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (T.params ++ T.motives ++ T.minors.take minorIdx) [])
      (S.origin.abstractList sourceBinders) T.minors[minorIdx]! := by
    rw [horigin]
    exact Hdomain
  have Htyped := Expr.ForallTelescopeTypeTranslation.ofTrExprS
    Habstract Hdomain' HdomainType
  rcases Htyped.toWrapForalls with
    ⟨domains, splitResidual, targetResidual, hdomainsLength,
      HsplitSource, htarget, Hresidual, HresidualType⟩
  let fieldDomains := domains.take A.rule.allArgs.size
  let hypothesisDomains := domains.drop A.rule.allArgs.size
  have hfieldsLE : A.rule.allArgs.size ≤ domains.length := by omega
  have hfields : fieldDomains.length = A.rule.allArgs.size := by
    simp [fieldDomains, List.length_take, Nat.min_eq_left hfieldsLE]
  have hhypotheses : hypothesisDomains.length =
      A.rule.recursiveArgs.size := by
    simp [hypothesisDomains, List.length_drop, hdomainsLength]
  have hdomains : domains = fieldDomains ++ hypothesisDomains :=
    (List.take_append_drop A.rule.allArgs.size domains).symm
  rw [hdomains] at htarget Hresidual HresidualType
  have hconsume := HS.semantic.sourceType_consumeTypeAnnotations_eq_self
    (ok := S.sourceFullContext.env.isTypeAnnotationWrapper)
  have hsourceType : S.origin = S.sourceType :=
    S.unannotated_eq.symm.trans hconsume
  have hmotiveClosed : Closed S.motiveApp := by
    have h := HS.semantic.motivePreTranslation.closed
    simpa [HS.semantic.terminalWF.mlctx.noBV] using h
  have Hexpected := (S.sourceTelescopeList hmotiveClosed).abstractList sourceBinders
  rw [← hsourceType] at Hexpected
  have hresidualShape : splitResidual =
      (((S.motiveApp.abstractList S.hypotheses_bound.fvars).abstractList
        S.fields_bound.fvars S.hypotheses.size).abstractList
          sourceBinders
          (A.rule.allArgs.size + A.rule.recursiveArgs.size)) := by
    apply HsplitSource.residual_eq
    simpa [sourceBinders, hsourceFields, hsourceHypotheses,
      List.append_assoc] using Hexpected
  rw [hresidualShape] at Hresidual
  have hfieldFVars : traversal.fieldFVars =
      S.fields_bound.fvars := by
    have harrays : (traversal.fieldFVars.map Expr.fvar).toArray =
        (S.fields_bound.fvars.map Expr.fvar).toArray :=
      traversal.fields_eq.symm.trans <|
        htraversalFields.trans S.fields_bound.expressions
    have hlists : traversal.fieldFVars.map Expr.fvar =
        S.fields_bound.fvars.map Expr.fvar := by
      simpa using congrArg Array.toList harrays
    exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hlists
  have hterminalClosed :
      traversal.terminal.abstractList S.fields_bound.fvars =
        traversal.fieldResidual := by
    rw [← hfieldFVars]
    exact traversal.fieldClosed
  have HtraversalTelescope := traversal.fieldTelescope
  rw [htraversalFields, hparameterTail] at HtraversalTelescope
  have hsemanticResidual :
      A.typing.fieldOpening.residual.isForall = false := by
    rw [← A.typing.fieldOpening.closed, Expr.abstractList_isForall]
    exact A.typing.target_not_forall
  have hfieldResidual : traversal.fieldResidual =
      A.typing.fieldOpening.residual :=
    (HtraversalTelescope.eq_of_residual_not_forall
      A.typing.fieldOpening.telescope
      traversal.fieldResidual_not_forall hsemanticResidual).2
  have hclosedTargets :
      traversal.terminal.abstractList S.fields_bound.fvars =
        A.rule.target.abstractList A.typing.fieldOpening.fvars := by
    rw [hterminalClosed, A.typing.fieldOpening.closed, hfieldResidual]
  let selectedOwner :=
    (AddInductive.getIIndices stats traversal.terminal).1
  have hselectedValid : AddInductive.isValidIndApp? stats
      traversal.terminal = some selectedOwner := by
    simpa [selectedOwner] using hvalid
  have hselectedDecl : selectedOwner < decl.types.length := by
    have hselectedStats :=
      (checkPositivityStep.isValidIndApp?_some hselectedValid).1
    rw [A.typing.validStats.types_size] at hselectedStats
    exact hselectedStats
  have hselectedHead : traversal.terminal.getAppFn =
      .const (decl.types[selectedOwner]'hselectedDecl).name stats.levels :=
    checkPositivityStep.isValidIndAppIdx.constHead
      (checkPositivityStep.isValidIndApp?_some hselectedValid).2
      (A.typing.validStats.indConstAt hselectedDecl)
  have htargetValid : AddInductive.isValidIndAppIdx stats A.rule.target
      owner = true := by
    have h := (checkPositivityStep.isValidIndApp?_some
      A.typing.target_valid).2
    simpa [A.typing_owner] using h
  have htargetHead : A.rule.target.getAppFn =
      .const (decl.types[owner]'A.abstractOwner_lt).name stats.levels :=
    checkPositivityStep.isValidIndAppIdx.constHead htargetValid
      (A.typing.validStats.indConstAt A.abstractOwner_lt)
  have hname : (decl.types[selectedOwner]'hselectedDecl).name =
      (decl.types[owner]'A.abstractOwner_lt).name := by
    have heq := congrArg Expr.getAppFn hclosedTargets
    rw [Expr.getAppFn_abstractList, hselectedHead,
      Expr.getAppFn_abstractList, htargetHead] at heq
    simp at heq
    exact heq
  have htypeNames : (decl.types.map (fun type => type.name)).Nodup := by
    have hprefix := (List.nodup_append.mp
      (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup
        R.core)).1
    simpa [VInductDecl.sourceNames, VInductDecl.typeConstants,
      VInductiveType.toVConstVal, Function.comp_def] using hprefix
  have hselectedOwner : selectedOwner = owner := by
    have hleft : selectedOwner <
        (decl.types.map (fun type => type.name)).length := by simpa
    have hright : owner <
        (decl.types.map (fun type => type.name)).length := by
      simpa using A.abstractOwner_lt
    apply (List.getElem_inj (h₀ := hleft) (h₁ := hright)
      htypeNames).mp
    simpa only [List.getElem_map] using hname
  have hselectedOwner' :
      (AddInductive.getIIndices stats traversal.terminal).1 = owner := by
    simpa [selectedOwner] using hselectedOwner
  have hmotiveApp' : S.motiveApp =
      Expr.app
        (mkAppN H.recInfos[owner]!.motive
          (AddInductive.getIIndices stats traversal.terminal).2)
        (mkAppN
          (mkAppN (.const S.constructor.name stats.levels) stats.params)
          S.fields) := by
    rw [hmotiveApp]
    rcases hindices : AddInductive.getIIndices stats traversal.terminal with
      ⟨motiveOwner, indices⟩
    have : motiveOwner = owner := by
      simpa [hindices] using hselectedOwner'
    subst motiveOwner
    rfl
  exact ⟨T, S, traversal, HS, hypothesisOrigins,
    fieldDomains, hypothesisDomains, targetResidual,
    hhypothesisStats, hhypothesisRecInfos,
    hconstructor, htraversalFields, hfieldFVars, hclosedTargets,
    hselectedOwner', by simpa [hselectedOwner'] using hvalid,
    hmotiveApp', hsourceFields, hsourceHypotheses,
    hfields, hhypotheses, htarget, Hresidual, HresidualType⟩

/-- After each constructor pass closes its own fresh field identifiers, the
minor result retained by the minor pass of `mkRecInfos` is literally the constructor-motive
application reconstructed for the generated iota rule.  The proof compares
parameter and index spines through the alpha-closed inductive targets and
normalizes both field arrays to the same de Bruijn sequence. -/
theorem
    RecursorCheck.RuleAlignment.alignedMotiveAppFieldClosure
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
    (S : MinorPremiseType) (traversal : ConstructorFieldTraversal)
    (hconstructor : S.constructor = indTypes[owner]!.ctors[i])
    (hclosedTargets :
      traversal.terminal.abstractList S.fields_bound.fvars =
        A.rule.target.abstractList A.typing.fieldOpening.fvars)
    (hvalid : AddInductive.isValidIndApp? stats traversal.terminal =
      some owner)
    (hmotiveApp : S.motiveApp =
      Expr.app
        (mkAppN H.recInfos[owner]!.motive
          (AddInductive.getIIndices stats traversal.terminal).2)
        (mkAppN
          (mkAppN (.const S.constructor.name stats.levels) stats.params)
          S.fields))
    (hfields : S.fields.size = A.rule.allArgs.size) :
    S.motiveApp.abstractList S.fields_bound.fvars =
      Expr.app
        (mkAppN
          (H.recInfos[owner]!.motive.abstractList S.fields_bound.fvars)
          ((AddInductive.getIIndices stats A.rule.target).2.map fun index =>
            index.abstractList A.rule.all_args_bound.fvars))
        (A.rule.sourceConstructorMajor.abstractList
          A.rule.all_args_bound.fvars) := by
  have hruleFieldFVars : A.typing.fieldOpening.fvars =
      A.rule.all_args_bound.fvars :=
    A.typing.fieldOpening.fvars_eq_bound A.rule.all_args_bound
  have hindices := congrArg
    (fun target => (AddInductive.getIIndices stats target).2)
    hclosedTargets
  rw [checkPositivityStep.getIIndices.snd_abstractList,
    checkPositivityStep.getIIndices.snd_abstractList,
    hruleFieldFVars] at hindices
  have htraversalValid : AddInductive.isValidIndAppIdx stats
      traversal.terminal owner = true :=
    (checkPositivityStep.isValidIndApp?_some hvalid).2
  have hruleValid : AddInductive.isValidIndAppIdx stats A.rule.target
      owner = true := by
    have h := (checkPositivityStep.isValidIndApp?_some
      A.typing.target_valid).2
    simpa [A.typing_owner] using h
  have htraversalPrefix :=
    A.typing.validStats.sourceParameterPrefix htraversalValid
  have hrulePrefix := A.typing.validStats.sourceParameterPrefix hruleValid
  have hargs := congrArg Expr.getAppArgs hclosedTargets
  rw [Expr.getAppArgs_abstractList, Expr.getAppArgs_abstractList] at hargs
  have hparams :
      stats.params.map (fun arg =>
        arg.abstractList S.fields_bound.fvars) =
      stats.params.map (fun arg =>
        arg.abstractList A.rule.all_args_bound.fvars) := by
    apply Array.toList_inj.mp
    have htake := congrArg (List.take stats.params.size)
      (congrArg Array.toList hargs)
    simp only [Array.toList_map] at htake
    have htake' :
        List.map (fun arg => arg.abstractList S.fields_bound.fvars)
            (List.take stats.params.size
              traversal.terminal.getAppArgsList) =
          List.map (fun arg =>
            arg.abstractList A.typing.fieldOpening.fvars)
            (List.take stats.params.size A.rule.target.getAppArgsList) := by
      simpa only [List.map_take, Expr.getAppArgs_toList] using htake
    rw [htraversalPrefix, hrulePrefix, hruleFieldFVars] at htake'
    simpa only [Array.toList_map] using htake'
  have hsourceFields :
      S.fields.map (fun arg => arg.abstractList S.fields_bound.fvars) =
      A.rule.allArgs.map (fun arg =>
        arg.abstractList A.rule.all_args_bound.fvars) := by
    have hleft := congrArg
      (Array.map fun arg => arg.abstractList S.fields_bound.fvars)
      S.fields_bound.expressions
    have hright := congrArg
      (Array.map fun arg =>
        arg.abstractList A.rule.all_args_bound.fvars)
      A.rule.all_args_bound.expressions
    have hleftCanonical := Expr.abstractList_fvarArray
      S.fields_bound.fvars 0 S.fields_nodup
    have hrightCanonical := Expr.abstractList_fvarArray
      A.rule.all_args_bound.fvars 0 A.rule.all_args_nodup
    rw [hleftCanonical] at hleft
    rw [hrightCanonical] at hright
    have hlength : S.fields_bound.fvars.length =
        A.rule.all_args_bound.fvars.length :=
      S.fields_bound.length_fvars.trans <|
        hfields.trans A.rule.all_args_bound.length_fvars.symm
    rw [hlength] at hleft
    exact hleft.trans hright.symm
  rw [hmotiveApp, hconstructor]
  unfold RecursorRuleSyntax.sourceConstructorMajor
  simp only [Expr.abstractList_app, Expr.abstractList_mkAppN,
    Expr.abstractList_const]
  rw [hindices, hparams, hsourceFields]

/-- Once the selected constructor fields are closed, the aligned motive
application can mention only the common parameter and motive binders.  In
particular it is independent of every minor binder which is inserted after
the selected minor type has been generated. -/
theorem
    RecursorCheck.RuleAlignment.alignedMotiveAppFieldClosureScope
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
    (S : MinorPremiseType)
    (hfieldClosure :
      S.motiveApp.abstractList S.fields_bound.fvars =
        Expr.app
          (mkAppN
            (H.recInfos[owner]!.motive.abstractList S.fields_bound.fvars)
            ((AddInductive.getIIndices stats A.rule.target).2.map fun index =>
              index.abstractList A.rule.all_args_bound.fvars))
          (A.rule.sourceConstructorMajor.abstractList
            A.rule.all_args_bound.fvars)) :
    (S.motiveApp.abstractList S.fields_bound.fvars).FVarsIn fun fv =>
      fv ∈ A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars := by
  let outer := A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars
  let fieldFVars := A.rule.all_args_bound.fvars
  let P := fun fv => fv ∈ outer
  have hownerRecInfos : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hownerMotive : owner < (H.recInfos.map (·.motive)).size := by
    simpa using hownerRecInfos
  rcases A.rule.motives_bound.getElem_eq_fvar owner hownerMotive with
    ⟨hownerMotiveFVars, hownerMotiveSource⟩
  let motiveFVar := A.rule.motives_bound.fvars[owner]
  have hmotive : H.recInfos[owner]!.motive = .fvar motiveFVar := by
    rw [getElem!_pos H.recInfos owner hownerRecInfos]
    simpa [motiveFVar] using hownerMotiveSource
  have Hmotive :
      (H.recInfos[owner]!.motive.abstractList
        S.fields_bound.fvars).FVarsIn P := by
    apply FVarsIn.abstractList_of
    rw [hmotive]
    change motiveFVar ∈ S.fields_bound.fvars ∨ P motiveFVar
    exact Or.inr <| List.mem_append_right _
      (List.getElem_mem hownerMotiveFVars)
  have hsemanticFields : A.typing.fieldsRecent.fvars = fieldFVars :=
    FVarArrayIn.fvars_eq
      A.typing.fieldsRecent.toFVarArrayAfter.toFVarArrayIn
      A.rule.all_args_bound rfl
  have hparameterFVars : ExprArrayFVarIds stats.params =
      A.rule.params_bound.fvars := by
    exact A.rule.params_bound.exprArrayFVarIds
  have Htarget : A.rule.target.FVarsIn fun fv =>
      fv ∈ fieldFVars ∨ P fv := by
    apply A.typing.targetFVarsIn.mono
    intro fv hfv
    rcases hfv with hfield | hparam
    · rw [hsemanticFields] at hfield
      exact Or.inl hfield
    · rw [hparameterFVars] at hparam
      exact Or.inr <| List.mem_append_left _ hparam
  have Hindices : ∀ index ∈
      (AddInductive.getIIndices stats A.rule.target).2,
      (index.abstractList fieldFVars).FVarsIn P := by
    intro index hindex
    have hindexArgs : index ∈ A.rule.target.getAppArgsList := by
      have hsuffix :
          (AddInductive.getIIndices stats A.rule.target).2.toList =
            A.rule.target.getAppArgs.toList.drop stats.params.size := by
        change (A.rule.target.getAppArgs[stats.params.size:]).toList = _
        rw [List.drop_eq_drop_min]
        simp only [Subarray.toList_eq, Array.array_toSubarray,
          Array.start_toSubarray, Array.stop_toSubarray, Nat.min_self,
          Array.toList_extract, List.extract_eq_take_drop,
          Array.length_toList]
        apply List.take_of_length_le
        simp
      have hdrop : index ∈
          A.rule.target.getAppArgs.toList.drop stats.params.size := by
        rw [← hsuffix]
        exact Array.mem_toList_iff.mpr hindex
      simpa [Expr.getAppArgs_toList] using List.mem_of_mem_drop hdrop
    apply FVarsIn.abstractList_of
    exact (Htarget.getAppArgsList hindexArgs).mono fun fv hfv =>
      hfv
  have Hmajor :
      (A.rule.sourceConstructorMajor.abstractList fieldFVars).FVarsIn P := by
    have HconstructorScope := A.typing.constructor_translation.fvarsIn
    unfold RecursorRuleSyntax.sourceConstructorMajor at HconstructorScope
    rw [Expr.mkAppN_eq_mkAppList, Expr.mkAppN_eq_mkAppList] at HconstructorScope
    have HconstContext :=
      (FVarsIn.mkAppList.mp (FVarsIn.mkAppList.mp HconstructorScope).1).1
    have Hconst : (Expr.const indTypes[owner]!.ctors[i].name stats.levels).FVarsIn
        (fun fv => fv ∈ fieldFVars ∨ P fv) := by
      change ∀ level ∈ stats.levels, level.hasMVar' = false
      change ∀ level ∈ stats.levels, level.hasMVar' = false at HconstContext
      exact HconstContext
    apply FVarsIn.abstractList_of
    unfold RecursorRuleSyntax.sourceConstructorMajor
    rw [Expr.mkAppN_eq_mkAppList, Expr.mkAppN_eq_mkAppList]
    apply FVarsIn.mkAppList.mpr
    constructor
    · apply FVarsIn.mkAppList.mpr
      constructor
      · exact Hconst
      · intro param hparam
        have hparam' : param ∈
            A.rule.params_bound.fvars.map Expr.fvar := by
          simpa [A.rule.params_bound.expressions] using hparam
        rcases List.mem_map.mp hparam' with ⟨fv, hfv, rfl⟩
        exact Or.inr <| List.mem_append_left _ hfv
    · intro field hfield
      have hfield' : field ∈ fieldFVars.map Expr.fvar := by
        simpa [fieldFVars, A.rule.all_args_bound.expressions] using hfield
      rcases List.mem_map.mp hfield' with ⟨fv, hfv, rfl⟩
      exact Or.inl hfv
  rw [hfieldClosure]
  change FVarsIn P (Expr.app _ _)
  constructor
  · rw [Expr.mkAppN_eq_mkAppList]
    apply FVarsIn.mkAppList.mpr
    constructor
    · exact Hmotive
    · intro index hindex
      rw [Array.toList_map] at hindex
      rcases List.mem_map.mp hindex with ⟨source, hsource, rfl⟩
      exact Hindices source (Array.mem_toList_iff.mp hsource)
  · simpa [fieldFVars] using Hmajor

/-- The selected motive is an outer binder and therefore is unaffected by
closing the fresh constructor fields used to assemble its application. -/
theorem
    RecursorCheck.RuleAlignment.alignedOwnerMotiveFieldClosure
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
    (S : MinorPremiseType)
    (HS : TypedMinorTraversalAt H.recursorWF S
      H.parameterSuffix.parameterDecls)
    (indices : Array Expr) (major : Expr)
    (hmotiveApp : S.motiveApp =
      Expr.app (mkAppN H.recInfos[owner]!.motive indices) major) :
    H.recInfos[owner]!.motive.abstractList S.fields_bound.fvars =
      H.recInfos[owner]!.motive := by
  have hownerRecInfos : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hownerMotive : owner < (H.recInfos.map (·.motive)).size := by
    simpa using hownerRecInfos
  rcases A.rule.motives_bound.getElem_eq_fvar owner hownerMotive with
    ⟨hownerMotiveFVars, hownerMotiveSource⟩
  let motiveFVar := A.rule.motives_bound.fvars[owner]
  have hmotive : H.recInfos[owner]!.motive = .fvar motiveFVar := by
    rw [getElem!_pos H.recInfos owner hownerRecInfos]
    simpa [motiveFVar] using hownerMotiveSource
  rcases HS.semantic.motiveHeadRoot with ⟨headFVar, hhead, hheadRoot⟩
  have hheadEq := congrArg Expr.getAppFn hmotiveApp
  rw [hhead] at hheadEq
  have hheadFVar : headFVar = motiveFVar := by
    simpa [Expr.getAppFn, Expr.getAppFn_mkAppN, hmotive] using hheadEq
  subst headFVar
  have hheadRoot' : motiveFVar ∈
      HS.semantic.traversal.rootContext.lctx.fvars := by
    rw [← HS.semantic.rootWF.lctx_eq,
      HS.semantic.rootWF.mlctx_wf.tr.fvars_eq]
    exact hheadRoot
  have hfieldFVars : HS.semantic.fieldsRecent.fvars =
      S.fields_bound.fvars :=
    FVarArrayIn.fvars_eq_of_array_eq
      HS.semantic.fieldsRecent.toFVarArrayAfter.toFVarArrayIn
      S.fields_bound rfl
  have hnotField : motiveFVar ∉ S.fields_bound.fvars := by
    intro hfield
    rw [← hfieldFVars] at hfield
    exact HS.semantic.fieldsRecent.fresh motiveFVar hfield hheadRoot'
  rw [hmotive, Expr.abstractList_fvar_of_not_mem hnotField]

/-- Insert the selected and later minor binders into the positive-arity
residual source.  After the recursive-hypothesis holes are left open, the
result is exactly the independently reconstructed constructor-motive type
under the complete executable rule binder list. -/
theorem
    RecursorCheck.RuleAlignment.alignedPositiveResidualSource
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
    (S : MinorPremiseType)
    (HS : TypedMinorTraversalAt H.recursorWF S
      H.parameterSuffix.parameterDecls)
    (traversal : ConstructorFieldTraversal)
    (hmotiveApp : S.motiveApp =
      Expr.app
        (mkAppN H.recInfos[owner]!.motive
          (AddInductive.getIIndices stats traversal.terminal).2)
        (mkAppN
          (mkAppN (.const S.constructor.name stats.levels) stats.params)
          S.fields))
    (hfieldClosure :
      S.motiveApp.abstractList S.fields_bound.fvars =
        Expr.app
          (mkAppN
            (H.recInfos[owner]!.motive.abstractList S.fields_bound.fvars)
            ((AddInductive.getIIndices stats A.rule.target).2.map fun index =>
              index.abstractList A.rule.all_args_bound.fvars))
          (A.rule.sourceConstructorMajor.abstractList
            A.rule.all_args_bound.fvars))
    (hfields : S.fields.size = A.rule.allArgs.size)
    (hhypotheses : S.hypotheses.size = A.rule.recursiveArgs.size) :
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    let remainingMinorFVars := A.rule.minors_bound.fvars.drop minorIdx
    let arity := A.rule.allArgs.size + A.rule.recursiveArgs.size
    let expected := Expr.app
      (mkAppN H.recInfos[owner]!.motive
        (AddInductive.getIIndices stats A.rule.target).2)
      A.rule.sourceConstructorMajor
    (((S.motiveApp.abstractList S.hypotheses_bound.fvars).abstractList
      S.fields_bound.fvars S.hypotheses.size).abstractList
        sourceBinders arity).liftLooseBVars'
          arity remainingMinorFVars.length =
      (expected.abstractList A.rule.binders).liftLooseBVars' 0
        A.rule.recursiveArgs.size := by
  dsimp only
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  let outer := A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars
  let generatedPrefix := outer ++ A.rule.minors_bound.fvars.take minorIdx
  let remainingMinorFVars := A.rule.minors_bound.fvars.drop minorIdx
  let fieldClosed := S.motiveApp.abstractList S.fields_bound.fvars
  let expected := Expr.app
    (mkAppN H.recInfos[owner]!.motive
      (AddInductive.getIIndices stats A.rule.target).2)
    A.rule.sourceConstructorMajor
  have hsourceParams : H.params.fvars = A.rule.params_bound.fvars :=
    FVarArrayIn.fvars_eq_of_array_eq H.params A.rule.params_bound rfl
  have hsourceMotives : H.bindings.motives.fvars =
      A.rule.motives_bound.fvars :=
    FVarArrayIn.fvars_eq_of_array_eq H.bindings.motives
      A.rule.motives_bound rfl
  have hsourceMinors : H.bindings.flatMinors.fvars =
      A.rule.minors_bound.fvars :=
    FVarArrayIn.fvars_eq_of_array_eq H.bindings.flatMinors
      A.rule.minors_bound rfl
  have hsourceBinders : sourceBinders = generatedPrefix := by
    simp only [sourceBinders, generatedPrefix, outer]
    rw [hsourceParams, hsourceMotives, hsourceMinors]
  have hfieldsLength : S.fields_bound.fvars.length =
      A.rule.allArgs.size :=
    S.fields_bound.length_fvars.trans hfields
  have hhypothesesLength : S.hypotheses_bound.fvars.length =
      A.rule.recursiveArgs.size :=
    S.hypotheses_bound.length_fvars.trans hhypotheses
  have HmotiveClosed : Closed S.motiveApp 0 := by
    have Hclosed := HS.semantic.motivePreTranslation.closed
    rw [HS.semantic.terminalWF.mlctx.noBV] at Hclosed
    simpa using Hclosed
  have HfieldClosed : Closed fieldClosed A.rule.allArgs.size := by
    have Hclosed := Closed.abstractList_at
      (e := S.motiveApp) (fvars := S.fields_bound.fvars)
      (depth := 0) (outer := 0) HmotiveClosed
    simpa [fieldClosed, hfieldsLength] using Hclosed
  have hcloseHypotheses := HS.semantic.abstractHypotheses_motiveApp
  have hfieldShift := Expr.abstractList_add_eq_liftLooseBVars
    (e := S.motiveApp) (fvars := S.fields_bound.fvars)
    (depth := 0) (extra := S.hypotheses.size)
    HmotiveClosed S.fields_nodup
  have hfieldShift' :
      S.motiveApp.abstractList S.fields_bound.fvars
          A.rule.recursiveArgs.size =
        fieldClosed.liftLooseBVars' 0 A.rule.recursiveArgs.size := by
    simpa [fieldClosed, hhypotheses] using hfieldShift
  have hfieldScope := A.alignedMotiveAppFieldClosureScope S hfieldClosure
  have hfieldAvoidsRemaining : fieldClosed.FVarsIn
      (fun fv => fv ∉ remainingMinorFVars) := by
    apply hfieldScope.mono
    intro fv houter hremaining
    have hminor : fv ∈ A.rule.minors_bound.fvars :=
      List.mem_of_mem_drop hremaining
    have hdisjoint := (List.nodup_append.mp
      A.rule.outer_binders_nodup).2.2
    exact hdisjoint fv houter fv hminor rfl
  have hremainingAbstract : fieldClosed.abstractList
      remainingMinorFVars A.rule.allArgs.size = fieldClosed :=
    hfieldAvoidsRemaining.abstractList_eq_self HfieldClosed
  have hprefixNodup : generatedPrefix.Nodup := by
    have hsub : generatedPrefix <+ outer ++ A.rule.minors_bound.fvars :=
      (List.Sublist.refl outer).append
        (List.take_sublist _ A.rule.minors_bound.fvars)
    exact A.rule.outer_binders_nodup.sublist <| by
      simpa [generatedPrefix, outer, List.append_assoc] using hsub
  have houterSplit : generatedPrefix ++ remainingMinorFVars =
      outer ++ A.rule.minors_bound.fvars := by
    simp [generatedPrefix, remainingMinorFVars, outer,
      List.append_assoc]
  have hfullOuterNodup :
      (generatedPrefix ++ remainingMinorFVars).Nodup := by
    rw [houterSplit]
    simpa [outer, List.append_assoc] using A.rule.outer_binders_nodup
  have hprefixShift := Expr.abstractList_add_eq_liftLooseBVars
    (e := fieldClosed) (fvars := generatedPrefix)
    (depth := A.rule.allArgs.size) (extra := remainingMinorFVars.length)
    HfieldClosed hprefixNodup
  have hprefixAppend := Expr.abstractList_after_inner
    (e := fieldClosed) (outer := generatedPrefix)
    (inner := remainingMinorFVars) (k := A.rule.allArgs.size)
    hfullOuterNodup
  rw [hremainingAbstract] at hprefixAppend
  have hprefixToFull :
      (fieldClosed.abstractList generatedPrefix A.rule.allArgs.size
        ).liftLooseBVars' A.rule.allArgs.size remainingMinorFVars.length =
      fieldClosed.abstractList (outer ++ A.rule.minors_bound.fvars)
        A.rule.allArgs.size := by
    have hcombined := hprefixShift.symm.trans hprefixAppend
    rw [houterSplit] at hcombined
    exact hcombined
  have hownerRecInfos : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hownerMotive : owner < (H.recInfos.map (·.motive)).size := by
    simpa using hownerRecInfos
  rcases A.rule.motives_bound.getElem_eq_fvar owner hownerMotive with
    ⟨hownerMotiveFVars, hownerMotiveSource⟩
  let motiveFVar := A.rule.motives_bound.fvars[owner]
  have hmotive : H.recInfos[owner]!.motive = .fvar motiveFVar := by
    rw [getElem!_pos H.recInfos owner hownerRecInfos]
    simpa [motiveFVar] using hownerMotiveSource
  have hnotRuleField : motiveFVar ∉ A.rule.all_args_bound.fvars := by
    intro hfield
    apply A.rule.all_args_outer_fresh motiveFVar hfield
    exact List.mem_append_left _ <|
      List.mem_append_right _ (List.getElem_mem hownerMotiveFVars)
  have hmotiveRuleFields : H.recInfos[owner]!.motive.abstractList
      A.rule.all_args_bound.fvars = H.recInfos[owner]!.motive := by
    rw [hmotive, Expr.abstractList_fvar_of_not_mem hnotRuleField]
  have hmotiveSourceFields := A.alignedOwnerMotiveFieldClosure S HS
    (AddInductive.getIIndices stats traversal.terminal).2
    (mkAppN
      (mkAppN (.const S.constructor.name stats.levels) stats.params)
      S.fields) hmotiveApp
  have hfieldExpected : fieldClosed =
      expected.abstractList A.rule.all_args_bound.fvars := by
    dsimp only [fieldClosed, expected]
    rw [hfieldClosure]
    simp only [Expr.abstractList_app, Expr.abstractList_mkAppN]
    rw [hmotiveSourceFields, hmotiveRuleFields]
  have hfullExpected :
      fieldClosed.abstractList (outer ++ A.rule.minors_bound.fvars)
          A.rule.allArgs.size =
        expected.abstractList A.rule.binders := by
    rw [hfieldExpected]
    have Hclose := Expr.abstractList_after_inner
      (e := expected) (outer := outer ++ A.rule.minors_bound.fvars)
      (inner := A.rule.all_args_bound.fvars) (k := 0) (by
        simpa [outer, RecursorRuleSyntax.binders,
          List.append_assoc] using A.rule.binders_nodup)
    simpa [outer, RecursorRuleSyntax.binders,
      A.rule.all_args_bound.length_fvars, List.append_assoc] using Hclose
  have hsourcePrefix :
      (((S.motiveApp.abstractList S.hypotheses_bound.fvars).abstractList
        S.fields_bound.fvars S.hypotheses.size).abstractList
          sourceBinders
          (A.rule.allArgs.size + A.rule.recursiveArgs.size)) =
        (fieldClosed.abstractList generatedPrefix A.rule.allArgs.size
          ).liftLooseBVars' 0 A.rule.recursiveArgs.size := by
    rw [hcloseHypotheses, hsourceBinders]
    rw [show S.hypotheses.size = A.rule.recursiveArgs.size from hhypotheses]
    rw [hfieldShift']
    have hcommute := Expr.liftLooseBVars'_abstractList_add
      (e := fieldClosed) (fvars := generatedPrefix)
      (start := 0) (cutoff := A.rule.allArgs.size)
      (amount := A.rule.recursiveArgs.size) (by omega) hprefixNodup
    simpa [fieldClosed, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hcommute
  rw [hsourcePrefix]
  have hcommute := Expr.liftLooseBVars_comm
    (fieldClosed.abstractList generatedPrefix A.rule.allArgs.size)
    remainingMinorFVars.length A.rule.recursiveArgs.size
    A.rule.allArgs.size 0 (by omega)
  calc
    _ = ((fieldClosed.abstractList generatedPrefix
            A.rule.allArgs.size).liftLooseBVars'
          A.rule.allArgs.size remainingMinorFVars.length
        ).liftLooseBVars' 0 A.rule.recursiveArgs.size := by
      have hcutoff : A.rule.recursiveArgs.size + A.rule.allArgs.size =
          A.rule.allArgs.size + A.rule.recursiveArgs.size := by omega
      rw [hcutoff] at hcommute
      exact hcommute.symm
    _ = _ := by rw [hprefixToFull, hfullExpected]

/-- Opening the selected minor's translated telescope yields a genuine
abstract context for every constructor field and recursive hypothesis.  The
older parameter/motive/minor prefix is recovered from the complete generated
recursor context, so no local-context well-formedness premise remains hidden
in the eventual minor application. -/
theorem
    RecursorCheck.RuleAlignment.installedSelectedMinorTargetContext
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
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ fieldDomains hypothesisDomains targetResidual,
        fieldDomains.length = A.rule.allArgs.size ∧
        hypothesisDomains.length = A.rule.recursiveArgs.size ∧
        T.minors[minorIdx]! = VExpr.wrapForalls
          (fieldDomains ++ hypothesisDomains) targetResidual ∧
        let base := T.params ++ T.motives ++ T.minors.take minorIdx
        OnCtx ((fieldDomains ++ hypothesisDomains).reverse ++
            (abstractForallContext base []).toCtx)
          (H.outVEnv.IsType Us.length) ∧
        H.outVEnv.IsType Us.length
          ((fieldDomains ++ hypothesisDomains).reverse ++
            (abstractForallContext base []).toCtx)
          targetResidual := by
  dsimp only
  rcases A.installedSelectedMinorTypedSplit with
    ⟨T, _S, _hypothesisOrigins, _traversal, fieldDomains,
      hypothesisDomains, _sourceResidual, targetResidual,
      _hhypothesisOrigins, _hhypothesisStats, _hhypothesisRecInfos,
      _htraversal,
      _htraversalFields, _htraversalRecursiveFields, _htraversalStats,
      _hparameterTail, _hpositions,
      _hlocal, _hsourceFields, _hsourceHypotheses,
      _hsourceContext,
      _HminorSemantic,
      _hproducerShape, hfields, hhypotheses, htarget, _Hsource, _Hresidual,
      _HresidualType, Htyped⟩
  let minorIdx := recursorMinorOffset indTypes owner + i
  let base := T.params ++ T.motives ++ T.minors.take minorIdx
  have Hprefix := T.prefixContext H.outVEnvWF.ordered
  have hminorDecomp : T.minors = T.minors.take minorIdx ++
      T.minors.drop minorIdx :=
    (List.take_append_drop minorIdx T.minors).symm
  rw [hminorDecomp, List.reverse_append, List.reverse_append,
    List.reverse_append, List.append_assoc] at Hprefix
  have HbaseRaw := OnCtx.of_append
    (Γ' := (T.minors.drop minorIdx).reverse) Hprefix
  have Hbase : OnCtx (abstractForallContext base []).toCtx
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length) := by
    rw [abstractForallContext_toCtx]
    rw [show VLCtx.toCtx ([] : VLCtx) = [] by rfl]
    simpa [base, List.reverse_append, List.append_assoc] using HbaseRaw
  have HminorType := Htyped.isType
  rw [htarget] at HminorType
  have Hopened := VEnv.IsType.wrapForalls_inv H.outVEnvWF.ordered
    Hbase HminorType
  exact ⟨T, fieldDomains, hypothesisDomains, targetResidual,
    hfields, hhypotheses, htarget, Hopened.1, Hopened.2⟩

/-- Select the translated minor domain corresponding to recursive-result
ordinal `j`.  The source binder is retained explicitly, and its abstract
target is literally the `j`th member of the hypothesis suffix. -/
theorem
    RecursorCheck.RuleAlignment.installedSelectedMinorHypothesisDomainAt
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
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : MinorPremiseType,
        ∃ hypothesisOrigins : MinorInductionHypothesisTypes
            S.sourceFullContext S.recursiveFields S.hypotheses,
        ∃ traversal : ConstructorFieldTraversal,
        ∃ fieldDomains hypothesisDomains targetResidual sourceDomain,
          S.hypothesis_type_origins = some hypothesisOrigins ∧
          hypothesisOrigins.stats = stats ∧
          hypothesisOrigins.recInfos.map (·.motive) =
            H.recInfos.map (·.motive) ∧
          S.traversal = some traversal ∧
          traversal.fields = S.fields ∧
          traversal.recursiveFields = S.recursiveFields ∧
          traversal.stats = stats ∧
          traversal.parameterTail = A.typing.parameterTail ∧
          traversal.recursivePositions = A.typing.recursivePositions ∧
          S.localIndex = i ∧
          S.fields.size = A.rule.allArgs.size ∧
          S.hypotheses.size = A.rule.recursiveArgs.size ∧
          BindingContextLE S.sourceFullContext H.localContext ∧
          Nonempty (TypedMinorTraversalAt H.recursorWF S
            H.parameterSuffix.parameterDecls) ∧
          A.minorShape = S ∧
          fieldDomains.length = A.rule.allArgs.size ∧
          hypothesisDomains.length = A.rule.recursiveArgs.size ∧
          T.minors[minorIdx]! = VExpr.wrapForalls
            (fieldDomains ++ hypothesisDomains) targetResidual ∧
          let sourceBinders := H.params.fvars ++
            H.bindings.motives.fvars ++
              H.bindings.flatMinors.fvars.take minorIdx
          let position := A.rule.allArgs.size + j
          Expr.ForallBinderAt
            (S.origin.abstractList sourceBinders) position sourceDomain ∧
          TrExprS H.outVEnv Us
            (abstractForallContext
              ((fieldDomains ++ hypothesisDomains).take position)
              (abstractForallContext
                (T.params ++ T.motives ++ T.minors.take minorIdx) []))
            sourceDomain hypothesisDomains[j]! ∧
          H.outVEnv.IsType Us.length
            (abstractForallContext
              ((fieldDomains ++ hypothesisDomains).take position)
              (abstractForallContext
                (T.params ++ T.motives ++ T.minors.take minorIdx) [])).toCtx
            hypothesisDomains[j]! := by
  dsimp only
  rcases A.installedSelectedMinorTypedSplit with
    ⟨T, S, hypothesisOrigins, traversal, fieldDomains, hypothesisDomains,
      _sourceResidual, targetResidual, hhypothesisOrigins,
      hhypothesisStats, hhypothesisRecInfos, htraversal, htraversalFields,
      htraversalRecursiveFields, htraversalStats, hparameterTail, hpositions,
      hlocal, hsourceFields, hsourceHypotheses, hsourceContext,
      HminorSemantic,
      hproducerShape, hfields, hhypotheses, htarget, _Hsource, _Hresidual,
      _HresidualType, Htyped⟩
  let position := A.rule.allArgs.size + j
  have hposition : position <
      A.rule.allArgs.size + A.rule.recursiveArgs.size := by
    dsimp only [position]
    omega
  have hdomains : (fieldDomains ++ hypothesisDomains).length =
      A.rule.allArgs.size + A.rule.recursiveArgs.size := by
    simp [hfields, hhypotheses]
  have hjHypothesis : j < hypothesisDomains.length := by
    rw [hhypotheses]
    exact hj
  rcases Htyped.binderAt_target
      (fieldDomains ++ hypothesisDomains) targetResidual htarget
      hdomains position hposition with
    ⟨suffixSource, _name, sourceDomain, _sourceBody, _bi, _bodyTarget,
      Hprefix, hsuffix, Hdomain, HdomainType, _Hbody⟩
  have Hbinder : Expr.ForallBinderAt
      (S.origin.abstractList
        (H.params.fvars ++ H.bindings.motives.fvars ++
          H.bindings.flatMinors.fvars.take
            (recursorMinorOffset indTypes owner + i)))
      position sourceDomain := Hprefix.binderAt hsuffix
  have hselected :
      (fieldDomains ++ hypothesisDomains)[position] = hypothesisDomains[j]! := by
    dsimp only [position]
    rw [getElem!_pos hypothesisDomains j hjHypothesis]
    simp [hfields]
  rw [hselected] at Hdomain HdomainType
  exact ⟨T, S, hypothesisOrigins, traversal, fieldDomains,
    hypothesisDomains, targetResidual, sourceDomain,
    hhypothesisOrigins, hhypothesisStats, hhypothesisRecInfos, htraversal,
    htraversalFields, htraversalRecursiveFields, htraversalStats,
    hparameterTail, hpositions,
    hlocal, hsourceFields, hsourceHypotheses, hsourceContext,
    HminorSemantic, hproducerShape, hfields, hhypotheses, htarget, Hbinder, Hdomain,
    HdomainType⟩

/-- Identify the source side of the selected recursive-hypothesis translation
with the exact declaration type introduced by `mkRecInfos.loopUTemplates`.  Thus the
pointwise target-domain certificate is no longer mediated by an arbitrary
existential source expression. -/
theorem
    RecursorCheck.RuleAlignment.installedSelectedMinorHypothesisDeclarationDomainAt
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
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ T : RecursorTypeTelescope H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : MinorPremiseType,
        ∃ hypothesisOrigins : MinorInductionHypothesisTypes
            S.sourceFullContext S.recursiveFields S.hypotheses,
        ∃ traversal : ConstructorFieldTraversal,
        ∃ fieldDomains hypothesisDomains targetResidual,
          ∃ D : FVarDeclAt
              S.sourceFullContext S.hypotheses j,
            S.hypothesis_type_origins = some hypothesisOrigins ∧
            hypothesisOrigins.stats = stats ∧
            hypothesisOrigins.recInfos.map (·.motive) =
              H.recInfos.map (·.motive) ∧
            S.traversal = some traversal ∧
            traversal.fields = S.fields ∧
            traversal.recursiveFields = S.recursiveFields ∧
            traversal.stats = stats ∧
            traversal.parameterTail = A.typing.parameterTail ∧
            traversal.recursivePositions = A.typing.recursivePositions ∧
            S.recursiveFields[j]! =
              S.fields[A.typing.recursivePositions[j]!]! ∧
            A.rule.recursiveArgs[j]! =
              A.rule.allArgs[A.typing.recursivePositions[j]!]! ∧
            S.localIndex = i ∧
            S.fields.size = A.rule.allArgs.size ∧
            S.hypotheses.size = A.rule.recursiveArgs.size ∧
            BindingContextLE S.sourceFullContext H.localContext ∧
            Nonempty (TypedMinorTraversalAt H.recursorWF S
              H.parameterSuffix.parameterDecls) ∧
            A.minorShape = S ∧
            fieldDomains.length = A.rule.allArgs.size ∧
            hypothesisDomains.length = A.rule.recursiveArgs.size ∧
            T.minors[minorIdx]! = VExpr.wrapForalls
              (fieldDomains ++ hypothesisDomains) targetResidual ∧
            let sourceBinders := H.params.fvars ++
              H.bindings.motives.fvars ++
                H.bindings.flatMinors.fvars.take minorIdx
            let position := A.rule.allArgs.size + j
            let declarationDomain :=
              ((D.type.abstractList
                  (S.hypotheses_bound.fvars.take j)).abstractList
                S.fields_bound.fvars j).abstractList
                  sourceBinders position
            Expr.ForallBinderAt
              (S.origin.abstractList sourceBinders) position
              declarationDomain ∧
            TrExprS H.outVEnv Us
              (abstractForallContext
                ((fieldDomains ++ hypothesisDomains).take position)
                (abstractForallContext
                  (T.params ++ T.motives ++ T.minors.take minorIdx) []))
              declarationDomain hypothesisDomains[j]! ∧
            H.outVEnv.IsType Us.length
              (abstractForallContext
                ((fieldDomains ++ hypothesisDomains).take position)
                (abstractForallContext
                  (T.params ++ T.motives ++ T.minors.take minorIdx) [])).toCtx
              hypothesisDomains[j]! ∧
            ∃ originRoot sourceType,
              ∃ O : InductionHypothesisType
                hypothesisOrigins.stats hypothesisOrigins.recInfos
                originRoot S.recursiveFields[j]! sourceType,
              D.type = (sourceType.consumeTypeAnnotationsVerified
                S.sourceFullContext.env.isTypeAnnotationWrapper) ∧
              D.type = sourceType ∧
              O.replayTrace S.fields_bound.fvars =
                (A.minorReplayAt j hj).semantic.generated.replayTrace
                  A.rule.all_args_bound.fvars := by
  dsimp only
  rcases A.installedSelectedMinorHypothesisDomainAt j hj with
    ⟨T, S, hypothesisOrigins, traversal, fieldDomains, hypothesisDomains,
      targetResidual, sourceDomain, hhypothesisOrigins,
      hhypothesisStats, hhypothesisRecInfos, htraversal, htraversalFields,
      htraversalRecursiveFields, htraversalStats, hparameterTail, hpositions,
      hlocal, hsourceFields, hsourceHypotheses, hsourceContext,
      HminorSemantic,
      hproducerShape, hfields, hhypotheses, htarget, Hbinder, Hdomain,
      HdomainType⟩
  subst S
  let P := A.minorReplayAt j hj
  have horigins : hypothesisOrigins = P.hypothesisOrigins :=
    Option.some.inj (hhypothesisOrigins.symm.trans P.hypothesisOrigins_eq)
  subst hypothesisOrigins
  let D := P.sourceDeclaration
  let originRoot := P.sourceOriginRoot
  let sourceType := P.sourceType
  let O := P.sourceOrigin
  have hdeclarationType : D.type =
      (sourceType.consumeTypeAnnotationsVerified
        A.minorShape.sourceFullContext.env.isTypeAnnotationWrapper) :=
    P.sourceDeclaration_type
  have hdeclarationTypeExact : D.type = sourceType :=
    hdeclarationType.trans O.consumeTypeAnnotationsVerified_eq_self
  have hjRecursiveFields : j < A.minorShape.recursiveFields.size := by
    rw [← A.minorShape.hypotheses_size, hsourceHypotheses]
    exact hj
  have hjTraversal : j < traversal.recursiveFields.size := by
    rw [htraversalRecursiveFields]
    exact hjRecursiveFields
  have hsourceSelected : A.minorShape.recursiveFields[j]! =
      A.minorShape.fields[
        A.typing.recursivePositions[j]!]! := by
    have Hselected := traversal.decisions.selected_at j hjTraversal
    rw [htraversalRecursiveFields, htraversalFields, hpositions] at Hselected
    exact Hselected.2
  have hruleSelected : A.rule.recursiveArgs[j]! =
      A.rule.allArgs[A.typing.recursivePositions[j]!]! :=
    (A.typing.decisions.selected_at j hj).2
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take
      (recursorMinorOffset indTypes owner + i)
  let position := A.rule.allArgs.size + j
  let declarationDomain :=
    ((D.type.abstractList
        (A.minorShape.hypotheses_bound.fvars.take j)).abstractList
      A.minorShape.fields_bound.fvars j).abstractList
        sourceBinders position
  have HdeclarationBinder :=
    (A.minorShape.hypothesisBinderAtList D
      (HminorSemantic.elim fun HS => D.closed HS.semantic.sourceWF.lctxClosed)).abstractList
      sourceBinders
  simp only [Nat.zero_add] at HdeclarationBinder
  rw [hsourceFields] at HdeclarationBinder
  have HdeclarationBinder' : Expr.ForallBinderAt
      (A.minorShape.origin.abstractList sourceBinders)
        position declarationDomain := by
    exact HdeclarationBinder
  have hsourceDomain : sourceDomain = declarationDomain :=
    Hbinder.unique HdeclarationBinder'
  rw [hsourceDomain] at Hdomain
  exact ⟨T, A.minorShape, P.hypothesisOrigins, traversal, fieldDomains,
    hypothesisDomains, targetResidual, D,
    hhypothesisOrigins, hhypothesisStats, hhypothesisRecInfos, htraversal,
    htraversalFields, htraversalRecursiveFields, htraversalStats,
    hparameterTail, hpositions,
    hsourceSelected, hruleSelected,
    hlocal, hsourceFields, hsourceHypotheses, hsourceContext,
    HminorSemantic, rfl, hfields, hhypotheses,
    htarget, HdeclarationBinder', Hdomain, HdomainType,
    originRoot, sourceType, O, hdeclarationType,
    hdeclarationTypeExact, P.replay⟩

end VerifyInductive
end Lean4Lean
