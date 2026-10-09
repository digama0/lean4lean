import Lean4Lean.Verify.Inductive.Nested.Restoration.ParameterOpening

/-! The steps of the executable nested restoration (`restoreNestedDeclarations` in
`Lean4Lean/Inductive/Add.lean`) as relations: rule, recursor and constructor
restoration, the header, constructor and recursor restoration steps, the generic
fold relation `FoldSteps`, fresh extensions (`FreshExtension`), and the two folds
of a nested restoration run (`NestedRestorationFolds`: source families, then
auxiliary recursors). Section 3.3 of the design notes. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Restoration of one recursor rule, as performed by `restoreRule`. -/
structure RuleRestoration
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name)
    (oldRecName newRecName : Name)
    (oldRule newRule : RecursorRule) : Prop where
  ctor : newRule.ctor = if newRecName == oldRecName then oldRule.ctor
    else result.restoreCtorName env oldRule.ctor
  nfields : newRule.nfields = oldRule.nfields
  rhs : NestedRestoration result env auxRec oldRule.rhs newRule.rhs

theorem restoreRule_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name)
    (oldRecName newRecName : Name) (rule : RecursorRule)
    (Htelescope : RestoreTelescope rule.rhs result.nparams) :
    RuleRestoration result env auxRec oldRecName newRecName rule
      (result.restoreRule env auxRec oldRecName newRecName rule) where
  ctor := rfl
  nfields := rfl
  rhs := restoreNested_refines result env auxRec rule.rhs Htelescope

inductive RulesRestoration
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name)
    (oldRecName newRecName : Name) :
    List RecursorRule → List RecursorRule → Prop
  | nil : RulesRestoration result env auxRec oldRecName newRecName [] []
  | cons : RuleRestoration result env auxRec oldRecName newRecName old new →
      RulesRestoration result env auxRec oldRecName newRecName olds news →
      RulesRestoration result env auxRec oldRecName newRecName
        (old :: olds) (new :: news)

theorem RulesRestoration.length
    (H : RulesRestoration result env auxRec oldRecName newRecName olds news) :
    news.length = olds.length := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem RulesRestoration.entry
    (H : RulesRestoration result env auxRec oldRecName newRecName olds news) :
    ∀ i (hold : i < olds.length) (hnew : i < news.length),
      RuleRestoration result env auxRec oldRecName newRecName
        olds[i] news[i] := by
  induction H with
  | nil =>
    intro i hold
    simp at hold
  | @cons old new olds news Hhead Htail ih =>
    intro i hold hnew
    cases i with
    | zero => simpa using Hhead
    | succ i => exact ih i (by simpa using hold) (by simpa using hnew)

theorem restoreRules_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name)
    (oldRecName newRecName : Name) :
    ∀ rules,
      (∀ rule ∈ rules, RestoreTelescope rule.rhs result.nparams) →
      RulesRestoration result env auxRec oldRecName newRecName rules
        (rules.map (result.restoreRule env auxRec oldRecName newRecName)) := by
  intro rules Htelescope
  induction rules with
  | nil => exact .nil
  | cons rule rules ih =>
    exact .cons
      (restoreRule_refines result env auxRec oldRecName newRecName rule
        (Htelescope rule (by simp)))
      (ih fun tail htail => Htelescope tail (by simp [htail]))

/-- Recursor-level restoration records every overwritten metadata field and
the pointwise rule restoration relation. -/
structure RecursorRestoration
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (oldRecName newRecName : Name)
    (oldInfo newInfo : RecursorVal) : Prop where
  name : newInfo.name = newRecName
  levelParams : newInfo.levelParams = oldInfo.levelParams
  type : NestedRestoration result env auxRec oldInfo.type newInfo.type
  all : newInfo.all = allIndNames
  numParams : newInfo.numParams = oldInfo.numParams
  numIndices : newInfo.numIndices = oldInfo.numIndices
  numMotives : newInfo.numMotives = oldInfo.numMotives
  numMinors : newInfo.numMinors = oldInfo.numMinors
  rules : RulesRestoration result env auxRec oldRecName newRecName
    oldInfo.rules newInfo.rules
  k : newInfo.k = oldInfo.k
  isUnsafe : newInfo.isUnsafe = oldInfo.isUnsafe

/-- The restored recursor type is a forall telescope whose residual is the
motive application of the executable recursor result (`concreteRecursorResult`).
This is the syntactic fact used by `RecursorRestoration.nestedRecursorShape`. -/
theorem RecursorRestoration.typeConcreteRecursorResultForallTelescope
    (Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (Hrestore : RecursorRestoration result prodEnv auxRec allIndNames
      oldRecName newRecName Hentry.info newInfo)
    (Hselections : RecursorBinderGroups c stats recInfos ownerIdx)
    (howner : ownerIdx < recInfos.size)
    (hnoalias : Hselections.NoAlias)
    (hparams : result.nparams = stats.params.size) :
    Expr.ForallTelescope newInfo.type
      (result.nparams + ((recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size +
        recInfos[ownerIdx]!.indices.size + 1))
      (concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx) := by
  have Htype := Hselections.forallTelescope
    (.app (mkAppN recInfos[ownerIdx]!.motive
      recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
  rw [Hselections.residual_eq_concreteRecursorResult howner hnoalias] at Htype
  have Htype' := Htype.inferImplicit_sameResidual (by rfl) 1000 false
  rw [← Hentry.type, ← hparams] at Htype'
  apply Hrestore.type.concreteRecursorResult_forallTelescope
    (numMotives := (recInfos.map (·.motive)).size)
    (numMinors := (recInfos.flatMap (·.minors)).size)
    (numIndices := recInfos[ownerIdx]!.indices.size)
    (ownerIdx := ownerIdx) (by simpa using howner)
  simpa only [Nat.add_assoc] using Htype'

/-- The executable restoration of a generated source recursor type: the common
parameters are opened once, every remaining domain is paired with its restored
domain, and the motive-application residual is unchanged. -/
structure RestoredRecursorTelescope
    (result : Lean4Lean.ElimNestedInductive.Result)
    (prodEnv : Environment) (auxRec : NameMap Name)
    (newInfo : RecursorVal)
    (Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry) where
  opening : NestedRestorationOpening result prodEnv auxRec Hentry.info.type
    newInfo.type
  suffix : ExprReplacement.ForallTelescopeReplacement
    (result.restoreNestedNode prodEnv opening.params auxRec)
    opening.body opening.restoredBody
    ((recInfos.map (·.motive)).size +
      (recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1)
    (concreteRecursorResult (recInfos.map (·.motive)).size
      (recInfos.flatMap (·.minors)).size
      recInfos[ownerIdx]!.indices.size ownerIdx)
    (concreteRecursorResult (recInfos.map (·.motive)).size
      (recInfos.flatMap (·.minors)).size
      recInfos[ownerIdx]!.indices.size ownerIdx)

theorem RecursorRestoration.generatedTelescopeTrace
    (Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (Hrestore : RecursorRestoration result prodEnv auxRec allIndNames
      oldRecName newRecName Hentry.info newInfo)
    (Hselections : RecursorBinderGroups c stats recInfos ownerIdx)
    (howner : ownerIdx < recInfos.size)
    (hnoalias : Hselections.NoAlias)
    (hparams : result.nparams = stats.params.size)
    (hresultParams : result.params.size = result.nparams) :
    Nonempty (RestoredRecursorTelescope result prodEnv auxRec
      newInfo Hentry) := by
  let numMotives := (recInfos.map (·.motive)).size
  let numMinors := (recInfos.flatMap (·.minors)).size
  let numIndices := recInfos[ownerIdx]!.indices.size
  let recResult := concreteRecursorResult numMotives numMinors numIndices
    ownerIdx
  have Hraw := Hselections.forallTelescope
    (.app (mkAppN recInfos[ownerIdx]!.motive
      recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
  rw [Hselections.residual_eq_concreteRecursorResult howner hnoalias] at Hraw
  have Himplicit := Hraw.inferImplicit_sameResidual (by rfl) 1000 false
  rw [← Hentry.type, ← hparams] at Himplicit
  have Htelescope : Expr.ForallTelescope Hentry.info.type
      (result.nparams + (numMotives + numMinors + numIndices + 1))
      recResult := by
    simpa [numMotives, numMinors, numIndices, recResult, Nat.add_assoc] using
      Himplicit
  rcases Hrestore.type.opening hresultParams with ⟨Hopen⟩
  rcases Hopen.suffixTelescopeReplacement Htelescope
      (concreteRecursorResult_looseBVarRange (by simpa [numMotives] using
        howner)) with ⟨restoredResidual, Hsuffix⟩
  have Hidentity := ExprReplacement.restoreNested_concreteRecursorResult
    result prodEnv Hopen.params auxRec numMotives numMinors numIndices ownerIdx
  have hresidual : restoredResidual = recResult := by
    calc
      restoredResidual = recResult.replace
          (result.restoreNestedNode prodEnv Hopen.params auxRec) :=
        Hsuffix.residualReplacement.eq_replace
      _ = recResult := by
        simpa [recResult] using Hidentity.eq_replace.symm
  subst restoredResidual
  exact ⟨⟨Hopen, by
    simpa [numMotives, numMinors, numIndices, recResult] using Hsuffix⟩⟩

/-- The executable restoration suffix and the generated suffix are aligned on
the same parameter-closed executable body. -/
structure RestoredRecursorTelescopeAlignment
    (result : Lean4Lean.ElimNestedInductive.Result)
    (prodEnv : Environment) (auxRec : NameMap Name)
    (newInfo : RecursorVal)
    (Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry) where
  trace : RestoredRecursorTelescope result prodEnv auxRec
    newInfo Hentry
  selections : RecursorBinderGroups c stats recInfos ownerIdx
  noAlias : selections.NoAlias
  nparams_eq : result.nparams = stats.params.size
  oldParamDomains : List VExpr
  oldSuffixTarget : VExpr
  owner_lt : ownerIdx < recInfos.size
  oldParamDomains_length : oldParamDomains.length = result.nparams
  oldPrefix : Expr.ForallTelescope Hentry.info.type result.nparams
    (trace.opening.body.abstractList trace.opening.selection.fvars)
  oldClosed : Hentry.info.type.FVarIdsIn fun _ => False
  oldBVarClosed : Closed Hentry.info.type
  oldSuffix : Expr.ForallTelescopeTypeTranslation venv Hentry.info.levelParams
    (abstractForallContext oldParamDomains [])
    (trace.opening.body.abstractList trace.opening.selection.fvars)
    ((recInfos.map (·.motive)).size +
      (recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1)
    oldSuffixTarget

/-- The opening and the suffix replacement determine the complete telescope of
the restored recursor, independently of any translation of its domains. -/
theorem RestoredRecursorTelescopeAlignment.restoredForallTelescope
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    (H : RestoredRecursorTelescopeAlignment result prodEnv auxRec
      newInfo Hentry) :
    Expr.ForallTelescope newInfo.type
      (result.nparams + ((recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size +
        recInfos[ownerIdx]!.indices.size + 1))
      (concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx) := by
  let suffixArity := (recInfos.map (·.motive)).size +
    (recInfos.flatMap (·.minors)).size +
    recInfos[ownerIdx]!.indices.size + 1
  have HnewPrefix := H.trace.opening.outputPrefixTelescope H.oldPrefix
  have HnewSuffix := H.trace.suffix.newTelescope.abstractN
    H.trace.opening.selection.fvars
  have hresidual :
      (concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx).abstractN
          H.trace.opening.selection.fvars suffixArity =
      concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx :=
    FVarsIn.abstractN_eq_self concreteRecursorResult_noFVars _ _
  have HnewSuffix' : Expr.ForallTelescope
      (H.trace.opening.restoredBody.abstractN
        H.trace.opening.selection.fvars)
      suffixArity
      (concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx) := by
    dsimp [suffixArity] at hresidual ⊢
    simp only [Nat.zero_add] at HnewSuffix
    rw [hresidual] at HnewSuffix
    exact HnewSuffix
  exact HnewPrefix.trans HnewSuffix'

theorem RecursorRestoration.generatedTelescopeAlignment
    (Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (Hrestore : RecursorRestoration result prodEnv auxRec allIndNames
      oldRecName newRecName Hentry.info newInfo)
    (Hselections : RecursorBinderGroups c stats recInfos ownerIdx)
    (howner : ownerIdx < recInfos.size)
    (hnoalias : Hselections.NoAlias)
    (hparams : result.nparams = stats.params.size)
    (hresultParams : result.params.size = result.nparams) :
    Nonempty (RestoredRecursorTelescopeAlignment result prodEnv
      auxRec newInfo Hentry) := by
  rcases Hrestore.generatedTelescopeTrace Hentry Hselections howner hnoalias
      hparams hresultParams with ⟨Htrace⟩
  rcases Hentry.telescopeTranslation Hselections howner hnoalias with
    ⟨Hgenerated⟩
  let suffixArity := (recInfos.map (·.motive)).size +
    (recInfos.flatMap (·.minors)).size +
    recInfos[ownerIdx]!.indices.size + 1
  have Htyped : Expr.ForallTelescopeTypeTranslation venv
      Hentry.info.levelParams [] Hentry.info.type
      (stats.params.size + suffixArity) entry.2.type := by
    simpa [suffixArity, Nat.add_assoc] using Hgenerated.typed
  rcases Htyped.dropPrefix
      (prefixArity := stats.params.size) (suffixArity := suffixArity) with
    ⟨paramDomains, suffixSource, suffixTarget, hparamDomains,
      HsourcePrefix, htarget, Hsuffix⟩
  have HsourcePrefix' : Expr.ForallTelescope Hentry.info.type
      result.nparams suffixSource := by
    simpa [hparams] using HsourcePrefix
  have Hinput : Hentry.info.type.FVarsIn fun _ => False := by
    have := Hgenerated.typed.translation.fvarsIn
    simpa using this
  have hbody : Htrace.opening.body.abstractList
      Htrace.opening.selection.fvars = suffixSource :=
    Htrace.opening.abstractBody_eq_suffix HsourcePrefix' Hinput
      Hgenerated.typed.translation.closed
  refine ⟨⟨Htrace, Hselections, hnoalias, hparams, paramDomains,
    suffixTarget, howner, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact hparamDomains.trans hparams.symm
  · simpa only [hbody] using HsourcePrefix'
  · exact FVarsIn_to_FVarIdsIn Hinput
  · exact Hgenerated.typed.translation.closed
  · rw [hbody]
    simpa [suffixArity] using Hsuffix

/-- A translation of the restored recursor telescope is already a well-formed
abstract type. The final major-premise binder makes the telescope nonempty, so
no separate well-formedness premise is needed. -/
theorem RecursorRestoration.translatedTypeIsType
    (Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (Hrestore : RecursorRestoration result prodEnv auxRec allIndNames
      oldRecName newRecName Hentry.info newInfo)
    (Hselections : RecursorBinderGroups c stats recInfos ownerIdx)
    (howner : ownerIdx < recInfos.size)
    (hnoalias : Hselections.NoAlias)
    (hparams : result.nparams = stats.params.size)
    (Htranslation : TrExprS canonicalEnv Hentry.info.levelParams []
      newInfo.type targetType) :
    canonicalEnv.IsType Hentry.info.levelParams.length [] targetType := by
  have Htelescope := Hrestore.typeConcreteRecursorResultForallTelescope
    Hentry Hselections howner hnoalias hparams
  exact TrExprS.isType_of_forallTelescope Htelescope (by omega) Htranslation

/-- The source nested-recursor shape (`VInductDecl.NestedRecursorShape`), obtained
from the restored kernel recursor type translated in the source environment
`canonicalEnv`. No lowered abstract recursor is used: its type mentions auxiliary
families and need not even be well-formed in `canonicalEnv`. -/
theorem RecursorRestoration.nestedRecursorShape
    (Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (Hrestore : RecursorRestoration result prodEnv auxRec allIndNames
      oldRecName newRecName Hentry.info newInfo)
    (Hselections : RecursorBinderGroups c stats recInfos ownerIdx)
    (howner : ownerIdx < recInfos.size)
    (hnoalias : Hselections.NoAlias)
    (hparams : result.nparams = stats.params.size)
    (sourceDecl : VInductDecl) (owner : VInductiveType)
    (hdeclOwner : ownerIdx < sourceDecl.types.length)
    (hownerEq : sourceDecl.types[ownerIdx] = owner)
    (recursor : VConstVal)
    (hname : recursor.name = sourceDecl.recursorName owner)
    (huvars : recursor.uvars = sourceDecl.uvars ∨
      recursor.uvars = sourceDecl.uvars + 1)
    (hnparams : sourceDecl.nparams = result.nparams)
    (hmotives : sourceDecl.types.length ≤
      (recInfos.map (·.motive)).size)
    (hminors : sourceDecl.ownedConstructors.length ≤
      (recInfos.flatMap (·.minors)).size)
    (hindices : owner.numIndices = recInfos[ownerIdx]!.indices.size)
    (Htranslation : TrExprS canonicalEnv Hentry.info.levelParams []
      newInfo.type recursor.type) :
    Nonempty (sourceDecl.NestedRecursorShape owner recursor) := by
  have Htelescope := Hrestore.typeConcreteRecursorResultForallTelescope
    Hentry Hselections howner hnoalias hparams
  rcases TrExprS.forallTelescope_shape_with_context Htelescope Htranslation with
    ⟨domains, abstractResult, hdomainsLength, htype, Hresult⟩
  have htotal : result.nparams + (recInfos.map (·.motive)).size +
      (recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1 ≤ domains.length := by
    rw [hdomainsLength]
    simp only [Nat.add_assoc, Nat.le_refl]
  have hownerMotive : ownerIdx < (recInfos.map (·.motive)).size := by
    simpa using howner
  have hresultConcrete := TrExprS.concreteRecursorResult_eq
    (numParams := result.nparams) hownerMotive htotal Hresult
  have hdomainsSpec : domains.length =
      sourceDecl.nparams + (recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size + owner.numIndices + 1 := by
    rw [hdomainsLength, hnparams, hindices]
    simp only [Nat.add_assoc]
  rcases List.exists_append_five_of_length_eq domains sourceDecl.nparams
      (recInfos.map (·.motive)).size
      (recInfos.flatMap (·.minors)).size owner.numIndices 1
      hdomainsSpec with
    ⟨params, motives, minors, indices, major, hdomains,
      hparamsLength, hmotivesLength, hminorsLength, hindicesLength,
      hmajorLength⟩
  have hresult : abstractResult = sourceDecl.recursorResultWithCounts
      ownerIdx motives.length minors.length owner := by
    simpa [VInductDecl.recursorResultWithCounts, List.map_reverse,
      hmotivesLength, hminorsLength, hindices] using hresultConcrete
  refine ⟨VInductDecl.NestedRecursorShape.ofWrapped hdeclOwner hownerEq
    hname huvars hparamsLength ?_ ?_ hindicesLength hmajorLength ?_ hresult⟩
  · simpa [hmotivesLength] using hmotives
  · simpa [hminorsLength] using hminors
  · simpa [hdomains] using htype

/-- Translate a restored recursor without requiring the lowered recursor type
to translate in the restored environment.  In a nested block the lowered type
may mention auxiliary constants which are intentionally not installed there;
only its safety and universe-count metadata survive restoration. -/
theorem RecursorRestoration.translatedOfMetadata
    (H : RecursorRestoration result prodEnv auxRec allIndNames
      oldRecName newRecName oldInfo newInfo)
    (Hsafety : safety ≤ (ConstantInfo.recInfo oldInfo).safety)
    (Huvars : oldInfo.levelParams.length = recursor.uvars)
    (Htype : TrExprS venv oldInfo.levelParams [] newInfo.type recursor.type)
    (hname : recursor.name = newRecName) :
    TrConstVal safety venv (.recInfo newInfo) recursor := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
      ConstantInfo.isPartial, H.isUnsafe] using Hsafety
  · rw [ConstantInfo.levelParams, ConstantInfo.toConstantVal,
      H.levelParams]
    exact Huvars
  · change TrExprS venv newInfo.levelParams [] newInfo.type recursor.type
    rw [H.levelParams]
    exact Htype
  · rw [ConstantInfo.name, ConstantInfo.toConstantVal, H.name, ← hname]

theorem restoreRecursor_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (oldRecName newRecName : Name)
    (info : RecursorVal)
    (Htype : RestoreTelescope info.type result.nparams)
    (Hrules : ∀ rule ∈ info.rules,
      RestoreTelescope rule.rhs result.nparams) :
    RecursorRestoration result env auxRec allIndNames oldRecName newRecName
      info (result.restoreRecursor env auxRec allIndNames
        oldRecName newRecName info) where
  name := rfl
  levelParams := rfl
  type := restoreNested_refines result env auxRec info.type Htype
  all := rfl
  numParams := rfl
  numIndices := rfl
  numMotives := rfl
  numMinors := rfl
  rules := restoreRules_refines result env auxRec oldRecName newRecName
    info.rules Hrules
  k := rfl
  isUnsafe := rfl

/-- State transition of the executable family-header restoration step. -/
structure HeaderRestorationStep
    (loweredEnv sourceEnv : Environment) (allIndNames : List Name)
    (indName : Name) (oldInfo : InductiveVal)
    (out : Unit × Environment) where
  newInfo : InductiveVal
  restored : newInfo = { oldInfo with all := allIndNames }
  fresh : sourceEnv.contains newInfo.name = false
  output : out = ((), sourceEnv.add (.inductInfo newInfo))

/-- Changing the mutual-family metadata list does not affect translation of
an inductive header: `TrConstVal` observes only safety, universes, name, and
type. -/
theorem TrConstVal.inductInfo_setAll
    (H : TrConstVal safety venv (.inductInfo oldInfo) header) :
    TrConstVal safety venv
      (.inductInfo { oldInfo with all := allIndNames }) header := by
  cases oldInfo
  simpa [TrConstVal, TrConstant, ConstantInfo.safety,
    ConstantInfo.isUnsafe, ConstantInfo.isPartial,
    ConstantInfo.levelParams, ConstantInfo.type, ConstantInfo.name,
    ConstantInfo.toConstantVal] using H

theorem HeaderRestorationStep.translated
    (H : HeaderRestorationStep loweredEnv sourceProdEnv
      allIndNames indName oldInfo out)
    (Htr : TrConstVal safety venv (.inductInfo oldInfo) header) :
    TrConstVal safety venv (.inductInfo H.newInfo) header := by
  rw [H.restored]
  exact TrConstVal.inductInfo_setAll Htr

theorem restoreInductiveHeaderDecl_refines
    (loweredEnv sourceEnv : Environment) (allIndNames : List Name)
    (allowPrimitive : Bool) (indName : Name) (oldInfo : InductiveVal)
    (hlookup : loweredEnv.find? indName = some (.inductInfo oldInfo)) :
    (Lean4Lean.restoreInductiveHeaderDecl loweredEnv allIndNames
      allowPrimitive indName sourceEnv).WF fun out =>
        Nonempty (HeaderRestorationStep loweredEnv sourceEnv
          allIndNames indName oldInfo out) := by
  intro out hout
  unfold Lean4Lean.restoreInductiveHeaderDecl at hout
  simp only [hlookup] at hout
  change (sourceEnv.checkName oldInfo.name allowPrimitive).bind (fun _ =>
    Except.ok ((), sourceEnv.add (.inductInfo
      { oldInfo with all := allIndNames }))) = Except.ok out at hout
  cases hcheck : sourceEnv.checkName oldInfo.name allowPrimitive with
  | error err =>
    simp only [hcheck, Except.bind] at hout
    cases hout
  | ok checked =>
    simp only [hcheck, Except.bind, Except.ok.injEq] at hout
    subst out
    have hfresh : sourceEnv.contains oldInfo.name = false := by
      cases hcontains : sourceEnv.contains oldInfo.name
      · rfl
      · simp [Environment.checkName, hcontains, (· >>= ·), Except.bind]
          at hcheck
    exact ⟨{
      newInfo := { oldInfo with all := allIndNames }
      restored := rfl
      fresh := hfresh
      output := rfl }⟩

/-- The steps of one run of a stateful list fold, as used by nested declaration
restoration. -/
inductive FoldSteps (P : α → σ → σ → Type) :
    List α → σ → σ → Type
  | nil : FoldSteps P [] source source
  | cons : P head source middle →
      FoldSteps P tail middle target →
      FoldSteps P (head :: tail) source target

/-- Environment additions whose names were checked immediately before each
installation. This relation is shared by all three nested-restoration folds and
states the freshness invariant without any typing assumption. -/
inductive FreshExtension :
    Environment → List ConstantInfo → Environment → Prop
  | nil : FreshExtension env [] env
  | cons : env.find? ci.name = none →
      FreshExtension (env.add ci) cis outEnv →
      FreshExtension env (ci :: cis) outEnv

/-- The kernel environment's `quotInit` flag is unchanged by a fresh extension. -/
theorem FreshExtension.quotInit_eq
    (H : FreshExtension env entries outEnv) :
    outEnv.quotInit = env.quotInit := by
  induction H with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem FreshExtension.append
    (H₁ : FreshExtension env entries middleEnv)
    (H₂ : FreshExtension middleEnv rest outEnv) :
    FreshExtension env (entries ++ rest) outEnv := by
  induction H₁ with
  | nil => exact H₂
  | cons hfresh _Htail ih => exact .cons hfresh (ih H₂)

private theorem find?_none_of_add_none
    {env : Environment} {head : ConstantInfo} {name : Name}
    (hwf : env.constants.WF) (hfresh : env.find? head.name = none)
    (hnext : (env.add head).find? name = none) : env.find? name = none := by
  have hfreshMap : env.constants.find? head.name = none := by
    change env.constants.find?' head.name = none at hfresh
    rwa [hwf.find?'_eq_find?] at hfresh
  have hnextWF := hwf.insert head.name head hfreshMap
  change SMap.find?' (env.constants.insert head.name head) name = none at hnext
  rw [hnextWF.find?'_eq_find?, hwf.find?_insert] at hnext
  split at hnext
  · contradiction
  · change env.constants.find?' name = none
    rwa [hwf.find?'_eq_find?]

private theorem find?_add_self
    {env : Environment} {ci : ConstantInfo}
    (hwf : env.constants.WF) (hfresh : env.find? ci.name = none) :
    (env.add ci).find? ci.name = some ci := by
  have hfreshMap : env.constants.find? ci.name = none := by
    change env.constants.find?' ci.name = none at hfresh
    rwa [hwf.find?'_eq_find?] at hfresh
  have hnextWF := hwf.insert ci.name ci hfreshMap
  change SMap.find?' (env.constants.insert ci.name ci) ci.name = some ci
  rw [hnextWF.find?'_eq_find?, hwf.find?_insert]
  simp

theorem constantsWF_add_checked
    {env : Environment} {ci : ConstantInfo} (hwf : env.constants.WF)
    (hfresh : env.find? ci.name = none) : (env.add ci).constants.WF := by
  have hfreshMap : env.constants.find? ci.name = none := by
    change env.constants.find?' ci.name = none at hfresh
    rwa [hwf.find?'_eq_find?] at hfresh
  exact hwf.insert ci.name ci hfreshMap

theorem FreshExtension.sourceFresh
    (H : FreshExtension env entries outEnv)
    (hwf : env.constants.WF) (hentry : ci ∈ entries) :
    env.find? ci.name = none := by
  induction H with
  | nil => simp at hentry
  | cons hfresh Htail ih =>
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | htail
    · exact hfresh
    · have hnextWF := constantsWF_add_checked hwf hfresh
      exact find?_none_of_add_none hwf hfresh
        (ih hnextWF htail)

theorem FreshExtension.namesNodup
    (H : FreshExtension env entries outEnv) (hwf : env.constants.WF) :
    (entries.map (·.name)).Nodup := by
  induction H with
  | nil => simp
  | cons hfresh Htail ih =>
    have hnextWF := constantsWF_add_checked hwf hfresh
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hnextWF⟩
    intro hname
    rcases List.mem_map.mp hname with ⟨ci, hci, heq⟩
    have htailFresh := Htail.sourceFresh hnextWF hci
    have hheadPresent := find?_add_self hwf hfresh
    rw [← heq, htailFresh] at hheadPresent
    contradiction

theorem FreshExtension.targetWF
    (H : FreshExtension env entries outEnv) (hwf : env.constants.WF) :
    outEnv.constants.WF := by
  induction H with
  | nil => exact hwf
  | cons hfresh _Htail ih => exact ih (constantsWF_add_checked hwf hfresh)

theorem stateForM_refines
    (step : α → StateT σ (Except Exception) Unit)
    (P : α → σ → σ → Type) :
    ∀ (items : List α),
      (∀ item, item ∈ items → ∀ source,
        (step item source).WF fun out =>
          out.1 = () ∧ Nonempty (P item source out.2)) →
      ∀ (source : σ),
      (List.forM items step source).WF fun out =>
        out.1 = () ∧ Nonempty (FoldSteps P items source out.2) := by
  intro items
  induction items with
  | nil =>
    intro _Hstep
    intro source
    exact Except.WF.pure ⟨rfl, ⟨FoldSteps.nil⟩⟩
  | cons head tail ih =>
    intro Hstep
    intro source
    rw [List.forM]
    exact (Hstep head (by simp) source).bind fun out Hout => by
      rcases out with ⟨done, middle⟩
      rcases done with ⟨⟩
      rcases Hout with ⟨_, ⟨Hhead⟩⟩
      have Htail : ∀ item, item ∈ tail → ∀ source,
          (step item source).WF fun out =>
            out.1 = () ∧ Nonempty (P item source out.2) := by
        intro item hitem
        exact Hstep item (by simp [hitem])
      exact (ih Htail middle).mono fun final Hfinal => by
        rcases Hfinal with ⟨hunit, ⟨Htail⟩⟩
        exact ⟨hunit, ⟨FoldSteps.cons Hhead Htail⟩⟩

/-- Constructor restoration: the executable step changes only the type, by the
verified nested-expression traversal. -/
structure ConstructorRestoration
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (oldInfo newInfo : ConstructorVal) : Prop where
  name : newInfo.name = oldInfo.name
  levelParams : newInfo.levelParams = oldInfo.levelParams
  type : NestedRestoration result env {} oldInfo.type newInfo.type
  induct : newInfo.induct = oldInfo.induct
  cidx : newInfo.cidx = oldInfo.cidx
  numParams : newInfo.numParams = oldInfo.numParams
  numFields : newInfo.numFields = oldInfo.numFields
  isUnsafe : newInfo.isUnsafe = oldInfo.isUnsafe

/-- Translate a restored constructor from the metadata that restoration
actually preserves.  The old lowered constructor type need not translate in
the restored source environment, where the auxiliary families are absent. -/
theorem ConstructorRestoration.translatedOfMetadata
    (H : ConstructorRestoration result prodEnv oldInfo newInfo)
    (Hsafety : safety ≤ (ConstantInfo.ctorInfo oldInfo).safety)
    (Huvars : oldInfo.levelParams.length = constructor.uvars)
    (Hname : oldInfo.name = constructor.name)
    (Htype : TrExprS venv oldInfo.levelParams [] newInfo.type
      constructor.type) :
    TrConstVal safety venv (.ctorInfo newInfo) constructor := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
      ConstantInfo.isPartial, H.isUnsafe] using Hsafety
  · rw [ConstantInfo.levelParams, ConstantInfo.toConstantVal,
      H.levelParams]
    exact Huvars
  · change TrExprS venv newInfo.levelParams [] newInfo.type constructor.type
    rw [H.levelParams]
    exact Htype
  · rw [ConstantInfo.name, ConstantInfo.toConstantVal, H.name]
    exact Hname

theorem restoreConstructor_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (info : ConstructorVal)
    (Htelescope : RestoreTelescope info.type result.nparams) :
    ConstructorRestoration result env info
      { info with type := result.restoreNested env info.type } where
  name := rfl
  levelParams := rfl
  type := restoreNested_refines result env {} info.type Htelescope
  induct := rfl
  cidx := rfl
  numParams := rfl
  numFields := rfl
  isUnsafe := rfl

/-- State transition of one executable constructor-restoration step. -/
structure ConstructorRestorationStep
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (ctorName : Name)
    (oldInfo : ConstructorVal) (out : Unit × Environment) where
  newInfo : ConstructorVal
  newInfo_eq : newInfo =
    { oldInfo with type := result.restoreNested loweredEnv oldInfo.type }
  restoration : ConstructorRestoration result loweredEnv oldInfo newInfo
  fresh : sourceEnv.contains newInfo.name = false
  output : out = ((), sourceEnv.add (.ctorInfo newInfo))

theorem restoreConstructorDecl_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (allowPrimitive : Bool)
    (ctorName : Name) (oldInfo : ConstructorVal)
    (hlookup : loweredEnv.find? ctorName = some (.ctorInfo oldInfo))
    (Htelescope : RestoreTelescope oldInfo.type result.nparams) :
    (Lean4Lean.restoreConstructorDecl result loweredEnv allowPrimitive ctorName
      sourceEnv).WF fun out =>
        Nonempty (ConstructorRestorationStep result loweredEnv sourceEnv
          ctorName oldInfo out) := by
  intro out hout
  unfold Lean4Lean.restoreConstructorDecl at hout
  simp only [hlookup] at hout
  change (sourceEnv.checkName oldInfo.name allowPrimitive).bind (fun _ =>
    Except.ok ((), sourceEnv.add (.ctorInfo
      { oldInfo with type := result.restoreNested loweredEnv oldInfo.type }))) =
        Except.ok out at hout
  cases hcheck : sourceEnv.checkName oldInfo.name allowPrimitive with
  | error err =>
    simp only [hcheck, Except.bind] at hout
    cases hout
  | ok checked =>
    simp only [hcheck, Except.bind, Except.ok.injEq] at hout
    subst out
    have hfresh : sourceEnv.contains oldInfo.name = false := by
      cases hcontains : sourceEnv.contains oldInfo.name
      · rfl
      · simp [Environment.checkName, hcontains, (· >>= ·), Except.bind]
          at hcheck
    exact ⟨{
      newInfo := { oldInfo with
        type := result.restoreNested loweredEnv oldInfo.type }
      newInfo_eq := rfl
      restoration := restoreConstructor_refines result loweredEnv oldInfo
        Htelescope
      fresh := hfresh
      output := rfl }⟩

/-- One element of the executable constructor-restoration fold, retaining the
lowered lookup and telescope premise used to justify restoration. -/
structure RestoredConstructorStep
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (ctorName : Name)
    (sourceEnv targetEnv : Environment) where
  oldInfo : ConstructorVal
  lookup : loweredEnv.find? ctorName = some (.ctorInfo oldInfo)
  telescope : RestoreTelescope oldInfo.type result.nparams
  restored : ConstructorRestorationStep result loweredEnv sourceEnv
    ctorName oldInfo ((), targetEnv)

theorem restoreConstructorDecls_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (allowPrimitive : Bool)
    (ctorNames : List Name)
    (Hsources : ∀ ctorName, ctorName ∈ ctorNames →
      ∃ oldInfo : ConstructorVal,
        loweredEnv.find? ctorName = some (.ctorInfo oldInfo) ∧
        RestoreTelescope oldInfo.type result.nparams) :
    ∀ sourceEnv,
      (ctorNames.forM fun ctorName =>
        Lean4Lean.restoreConstructorDecl result loweredEnv allowPrimitive
          ctorName) sourceEnv |>.WF fun out =>
            out.1 = () ∧ Nonempty (FoldSteps
              (RestoredConstructorStep result loweredEnv)
              ctorNames sourceEnv out.2) := by
  apply stateForM_refines
  intro ctorName hctor sourceEnv
  rcases Hsources ctorName hctor with ⟨oldInfo, hlookup, Htelescope⟩
  exact (restoreConstructorDecl_refines result loweredEnv sourceEnv
    allowPrimitive ctorName oldInfo hlookup Htelescope).mono fun out Hout => by
      rcases out with ⟨done, targetEnv⟩
      rcases done with ⟨⟩
      rcases Hout with ⟨Hrestored⟩
      exact ⟨rfl, ⟨{
        oldInfo := oldInfo
        lookup := hlookup
        telescope := Htelescope
        restored := Hrestored }⟩⟩

/-- State transition of one executable recursor-restoration step. The restored
metadata is described by `RecursorRestoration`. -/
structure RecursorRestorationStep
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (oldRecName : Name)
    (oldInfo : RecursorVal) (out : Unit × Environment) where
  newRecName : Name
  newInfo : RecursorVal
  mappedName : newRecName = auxRec.getD oldRecName oldRecName
  produced : newInfo = result.restoreRecursor loweredEnv auxRec allIndNames
    oldRecName (auxRec.getD oldRecName oldRecName) oldInfo
  restoration : RecursorRestoration result loweredEnv auxRec allIndNames
    oldRecName newRecName oldInfo newInfo
  fresh : sourceEnv.contains newInfo.name = false
  output : out = ((), sourceEnv.add (.recInfo newInfo))

theorem restoreRecursorDecl_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool) (oldRecName : Name)
    (oldInfo : RecursorVal)
    (hlookup : loweredEnv.find? oldRecName = some (.recInfo oldInfo))
    (Htype : RestoreTelescope oldInfo.type result.nparams)
    (Hrules : ∀ rule ∈ oldInfo.rules,
      RestoreTelescope rule.rhs result.nparams) :
    (Lean4Lean.restoreRecursorDecl result loweredEnv auxRec allIndNames
      allowPrimitive oldRecName sourceEnv).WF fun out =>
        Nonempty (RecursorRestorationStep result loweredEnv sourceEnv auxRec
          allIndNames oldRecName oldInfo out) := by
  intro out hout
  unfold Lean4Lean.restoreRecursorDecl at hout
  simp only [hlookup] at hout
  change (sourceEnv.checkName (auxRec.getD oldRecName oldRecName)
    allowPrimitive).bind (fun _ => Except.ok ((), sourceEnv.add (.recInfo
      (result.restoreRecursor loweredEnv auxRec allIndNames oldRecName
        (auxRec.getD oldRecName oldRecName) oldInfo)))) = Except.ok out at hout
  cases hcheck : sourceEnv.checkName (auxRec.getD oldRecName oldRecName)
      allowPrimitive with
  | error err =>
    simp only [hcheck, Except.bind] at hout
    cases hout
  | ok checked =>
    simp only [hcheck, Except.bind, Except.ok.injEq] at hout
    subst out
    let newRecName := auxRec.getD oldRecName oldRecName
    let newInfo := result.restoreRecursor loweredEnv auxRec allIndNames
      oldRecName newRecName oldInfo
    have hfresh : sourceEnv.contains newRecName = false := by
      cases hcontains : sourceEnv.contains newRecName
      · rfl
      · simp [Environment.checkName, hcontains, (· >>= ·), Except.bind,
          newRecName] at hcheck
    exact ⟨{
      newRecName := newRecName
      newInfo := newInfo
      mappedName := rfl
      produced := rfl
      restoration := restoreRecursor_refines result loweredEnv auxRec
        allIndNames oldRecName newRecName oldInfo Htype Hrules
      fresh := by
        change sourceEnv.contains newRecName = false
        exact hfresh
      output := rfl }⟩

/-- One element of an executable recursor-restoration fold. -/
structure RestoredRecursorStep
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (oldRecName : Name)
    (sourceEnv targetEnv : Environment) where
  oldInfo : RecursorVal
  lookup : loweredEnv.find? oldRecName = some (.recInfo oldInfo)
  typeTelescope : RestoreTelescope oldInfo.type result.nparams
  ruleTelescopes : ∀ rule ∈ oldInfo.rules,
    RestoreTelescope rule.rhs result.nparams
  restored : RecursorRestorationStep result loweredEnv sourceEnv auxRec
    allIndNames oldRecName oldInfo ((), targetEnv)

theorem restoreRecursorDecls_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool)
    (recNames : List Name)
    (Hsources : ∀ recName, recName ∈ recNames →
      ∃ oldInfo : RecursorVal,
        loweredEnv.find? recName = some (.recInfo oldInfo) ∧
        RestoreTelescope oldInfo.type result.nparams ∧
        ∀ rule ∈ oldInfo.rules,
          RestoreTelescope rule.rhs result.nparams) :
    ∀ sourceEnv,
      (recNames.forM fun recName =>
        Lean4Lean.restoreRecursorDecl result loweredEnv auxRec allIndNames
          allowPrimitive recName) sourceEnv |>.WF fun out =>
            out.1 = () ∧ Nonempty (FoldSteps
              (RestoredRecursorStep result loweredEnv auxRec allIndNames)
              recNames sourceEnv out.2) := by
  apply stateForM_refines
  intro recName hrec sourceEnv
  rcases Hsources recName hrec with
    ⟨oldInfo, hlookup, Htype, Hrules⟩
  exact (restoreRecursorDecl_refines result loweredEnv sourceEnv auxRec
    allIndNames allowPrimitive recName oldInfo hlookup Htype Hrules).mono
      fun out Hout => by
        rcases out with ⟨done, targetEnv⟩
        rcases done with ⟨⟩
        rcases Hout with ⟨Hrestored⟩
        exact ⟨rfl, ⟨{
          oldInfo := oldInfo
          lookup := hlookup
          typeTelescope := Htype
          ruleTelescopes := Hrules
          restored := Hrestored }⟩⟩

/-- The executable restoration of one source family member: its header,
constructor list, and source recursor. -/
structure SourceFamilyRestoration
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (indType : InductiveType)
    (oldInfo : InductiveVal) (out : Unit × Environment) where
  headerEnv : Environment
  constructorEnv : Environment
  header : HeaderRestorationStep loweredEnv sourceEnv allIndNames
    indType.name oldInfo ((), headerEnv)
  constructors : FoldSteps
    (RestoredConstructorStep result loweredEnv) oldInfo.ctors headerEnv
      constructorEnv
  recursor : RestoredRecursorStep result loweredEnv auxRec allIndNames
    (Lean.mkRecName indType.name) constructorEnv out.2
  outputUnit : out.1 = ()

theorem restoreInductiveDecl_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool)
    (indType : InductiveType) (oldInfo : InductiveVal)
    (hlookup : loweredEnv.find? indType.name = some (.inductInfo oldInfo))
    (Hctors : ∀ ctorName, ctorName ∈ oldInfo.ctors →
      ∃ ctorInfo : ConstructorVal,
        loweredEnv.find? ctorName = some (.ctorInfo ctorInfo) ∧
        RestoreTelescope ctorInfo.type result.nparams)
    (recInfo : RecursorVal)
    (hrecLookup : loweredEnv.find? (Lean.mkRecName indType.name) =
      some (.recInfo recInfo))
    (HrecType : RestoreTelescope recInfo.type result.nparams)
    (HrecRules : ∀ rule ∈ recInfo.rules,
      RestoreTelescope rule.rhs result.nparams) :
    (Lean4Lean.restoreInductiveDecl result loweredEnv auxRec allIndNames
      allowPrimitive indType sourceEnv).WF fun out =>
        Nonempty (SourceFamilyRestoration result loweredEnv sourceEnv
          auxRec allIndNames indType oldInfo out) := by
  have Hheader := restoreInductiveHeaderDecl_refines loweredEnv sourceEnv
    allIndNames allowPrimitive indType.name oldInfo hlookup
  have Hcombined :
      ((Lean4Lean.restoreInductiveHeaderDecl loweredEnv allIndNames
          allowPrimitive indType.name sourceEnv).bind fun headerOut =>
        ((oldInfo.ctors.forM fun ctorName =>
          Lean4Lean.restoreConstructorDecl result loweredEnv allowPrimitive
            ctorName) headerOut.2).bind fun constructorOut =>
          Lean4Lean.restoreRecursorDecl result loweredEnv auxRec allIndNames
            allowPrimitive (Lean.mkRecName indType.name) constructorOut.2).WF
        fun out => Nonempty (SourceFamilyRestoration result loweredEnv
          sourceEnv auxRec allIndNames indType oldInfo out) :=
    Hheader.bind fun headerOut HheaderOut => by
    rcases headerOut with ⟨done, headerEnv⟩
    rcases done with ⟨⟩
    rcases HheaderOut with ⟨HheaderResult⟩
    have HconstructorFold := restoreConstructorDecls_refines result loweredEnv
      allowPrimitive oldInfo.ctors Hctors headerEnv
    exact HconstructorFold.bind fun constructorOut HconstructorOut => by
      rcases constructorOut with ⟨done, constructorEnv⟩
      rcases done with ⟨⟩
      rcases HconstructorOut with ⟨_, ⟨HconstructorTrace⟩⟩
      have Hrecursor := restoreRecursorDecl_refines result loweredEnv
        constructorEnv auxRec allIndNames allowPrimitive
        (Lean.mkRecName indType.name) recInfo hrecLookup HrecType HrecRules
      exact Hrecursor.mono fun recursorOut HrecursorOut => by
        rcases recursorOut with ⟨done, targetEnv⟩
        rcases done with ⟨⟩
        rcases HrecursorOut with ⟨HrecursorResult⟩
        exact ⟨{
          headerEnv := headerEnv
          constructorEnv := constructorEnv
          header := HheaderResult
          constructors := HconstructorTrace
          recursor := {
            oldInfo := recInfo
            lookup := hrecLookup
            typeTelescope := HrecType
            ruleTelescopes := HrecRules
            restored := HrecursorResult }
          outputUnit := rfl }⟩
  simpa [Lean4Lean.restoreInductiveDecl, hlookup, bind, StateT.bind] using
    Hcombined

/-- One family member in the outer source-inductive restoration fold. -/
structure RestoredInductiveStep
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (indType : InductiveType)
    (sourceEnv targetEnv : Environment) where
  oldInfo : InductiveVal
  lookup : loweredEnv.find? indType.name = some (.inductInfo oldInfo)
  restored : SourceFamilyRestoration result loweredEnv sourceEnv auxRec
    allIndNames indType oldInfo ((), targetEnv)

theorem restoreInductiveDecls_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool)
    (types : List InductiveType)
    (Hsources : ∀ indType, indType ∈ types →
      ∃ oldInfo : InductiveVal,
        loweredEnv.find? indType.name = some (.inductInfo oldInfo) ∧
        (∀ ctorName, ctorName ∈ oldInfo.ctors →
          ∃ ctorInfo : ConstructorVal,
            loweredEnv.find? ctorName = some (.ctorInfo ctorInfo) ∧
            RestoreTelescope ctorInfo.type result.nparams) ∧
        ∃ recInfo : RecursorVal,
          loweredEnv.find? (Lean.mkRecName indType.name) =
            some (.recInfo recInfo) ∧
          RestoreTelescope recInfo.type result.nparams ∧
          ∀ rule ∈ recInfo.rules,
            RestoreTelescope rule.rhs result.nparams) :
    ∀ sourceEnv,
      (types.forM fun indType =>
        Lean4Lean.restoreInductiveDecl result loweredEnv auxRec allIndNames
          allowPrimitive indType) sourceEnv |>.WF fun out =>
            out.1 = () ∧ Nonempty (FoldSteps
              (RestoredInductiveStep result loweredEnv auxRec allIndNames)
              types sourceEnv out.2) := by
  apply stateForM_refines
  intro indType hind sourceEnv
  rcases Hsources indType hind with
    ⟨oldInfo, hlookup, Hctors, recInfo, hrecLookup, HrecType, HrecRules⟩
  exact (restoreInductiveDecl_refines result loweredEnv sourceEnv auxRec
    allIndNames allowPrimitive indType oldInfo hlookup Hctors recInfo
    hrecLookup HrecType HrecRules).mono fun out Hout => by
      rcases out with ⟨done, targetEnv⟩
      rcases done with ⟨⟩
      rcases Hout with ⟨Hrestored⟩
      exact ⟨rfl, ⟨{
        oldInfo := oldInfo
        lookup := hlookup
        restored := Hrestored }⟩⟩

/-- The two folds of nested declaration restoration: source families first,
then auxiliary recursors. -/
structure NestedRestorationFolds
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (types : List InductiveType)
    (auxRecNames : List Name) (out : Unit × Environment) where
  sourceFamiliesEnv : Environment
  inductives : FoldSteps
    (RestoredInductiveStep result loweredEnv auxRec allIndNames)
    types sourceEnv sourceFamiliesEnv
  auxiliaries : FoldSteps
    (RestoredRecursorStep result loweredEnv auxRec allIndNames)
    auxRecNames sourceFamiliesEnv out.2
  outputUnit : out.1 = ()

theorem find?_none_of_contains_false
    {env : Environment} {name : Name} (hwf : env.constants.WF)
    (hfresh : env.contains name = false) : env.find? name = none := by
  change env.constants.contains name = false at hfresh
  rw [SMap.find?_isSome] at hfresh
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]
  cases hfind : env.constants.find? name <;> simp_all

theorem FoldSteps.constructorFreshExtension
    (H : FoldSteps (RestoredConstructorStep result loweredEnv)
      names sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshExtension sourceEnv entries targetEnv := by
  induction H with
  | nil => exact ⟨[], .nil⟩
  | cons Hstep Htail ih =>
    let ci : ConstantInfo := .ctorInfo Hstep.restored.newInfo
    have hfresh :=
      find?_none_of_contains_false hwf Hstep.restored.fresh
    have htarget := congrArg Prod.snd Hstep.restored.output
    simp only at htarget
    rw [htarget] at Htail ih
    rcases ih (constantsWF_add_checked hwf hfresh) with ⟨entries, Hentries⟩
    exact ⟨ci :: entries, .cons hfresh Hentries⟩

theorem FoldSteps.recursorFreshExtension
    (H : FoldSteps
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshExtension sourceEnv entries targetEnv := by
  induction H with
  | nil => exact ⟨[], .nil⟩
  | cons Hstep Htail ih =>
    let ci : ConstantInfo := .recInfo Hstep.restored.newInfo
    have hfresh :=
      find?_none_of_contains_false hwf Hstep.restored.fresh
    have htarget := congrArg Prod.snd Hstep.restored.output
    simp only at htarget
    rw [htarget] at Htail ih
    rcases ih (constantsWF_add_checked hwf hfresh) with ⟨entries, Hentries⟩
    exact ⟨ci :: entries, .cons hfresh Hentries⟩

theorem SourceFamilyRestoration.freshExtension
    (H : SourceFamilyRestoration result loweredEnv sourceEnv auxRec
      allIndNames indType oldInfo ((), targetEnv))
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshExtension sourceEnv entries targetEnv := by
  let header : ConstantInfo := .inductInfo H.header.newInfo
  have hheaderEnv : H.headerEnv = sourceEnv.add header :=
    congrArg Prod.snd H.header.output
  have hheaderFresh : sourceEnv.find? header.name = none :=
    find?_none_of_contains_false hwf H.header.fresh
  have hwfHeader := constantsWF_add_checked hwf hheaderFresh
  have Hconstructors' : FoldSteps
      (RestoredConstructorStep result loweredEnv) oldInfo.ctors
      (sourceEnv.add header) H.constructorEnv := by
    rw [← hheaderEnv]
    exact H.constructors
  rcases Hconstructors'.constructorFreshExtension hwfHeader with
    ⟨constructors, Hconstructors⟩
  have hwfConstructors : H.constructorEnv.constants.WF :=
    Hconstructors.targetWF hwfHeader
  let recursor : ConstantInfo := .recInfo H.recursor.restored.newInfo
  have htarget : targetEnv = H.constructorEnv.add recursor :=
    congrArg Prod.snd H.recursor.restored.output
  have hrecFresh : H.constructorEnv.find? recursor.name = none :=
    find?_none_of_contains_false hwfConstructors H.recursor.restored.fresh
  rw [htarget]
  exact ⟨header :: constructors ++ [recursor],
    FreshExtension.cons hheaderFresh
      (Hconstructors.append (.cons hrecFresh .nil))⟩

theorem FoldSteps.inductiveFreshExtension
    (H : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      types sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshExtension sourceEnv entries targetEnv := by
  induction H with
  | nil => exact ⟨[], .nil⟩
  | cons Hstep _Htail ih =>
    rcases Hstep.restored.freshExtension hwf with ⟨headEntries, Hhead⟩
    rcases ih (Hhead.targetWF hwf) with ⟨tailEntries, Htail⟩
    exact ⟨headEntries ++ tailEntries, Hhead.append Htail⟩

theorem NestedRestorationFolds.freshExtension
    (H : NestedRestorationFolds result loweredEnv sourceEnv auxRec
      allIndNames types auxRecNames out)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshExtension sourceEnv entries out.2 := by
  rcases H.inductives.inductiveFreshExtension hwf with
    ⟨primaryEntries, Hprimary⟩
  rcases H.auxiliaries.recursorFreshExtension (Hprimary.targetWF hwf) with
    ⟨auxiliaryEntries, Hauxiliary⟩
  exact ⟨primaryEntries ++ auxiliaryEntries,
    Hprimary.append Hauxiliary⟩

theorem restoreNestedDeclarations_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool)
    (types : List InductiveType) (auxRecNames : List Name)
    (Htypes : ∀ indType, indType ∈ types →
      ∃ oldInfo : InductiveVal,
        loweredEnv.find? indType.name = some (.inductInfo oldInfo) ∧
        (∀ ctorName, ctorName ∈ oldInfo.ctors →
          ∃ ctorInfo : ConstructorVal,
            loweredEnv.find? ctorName = some (.ctorInfo ctorInfo) ∧
            RestoreTelescope ctorInfo.type result.nparams) ∧
        ∃ recInfo : RecursorVal,
          loweredEnv.find? (Lean.mkRecName indType.name) =
            some (.recInfo recInfo) ∧
          RestoreTelescope recInfo.type result.nparams ∧
          ∀ rule ∈ recInfo.rules,
            RestoreTelescope rule.rhs result.nparams)
    (Haux : ∀ recName, recName ∈ auxRecNames →
      ∃ oldInfo : RecursorVal,
        loweredEnv.find? recName = some (.recInfo oldInfo) ∧
        RestoreTelescope oldInfo.type result.nparams ∧
        ∀ rule ∈ oldInfo.rules,
          RestoreTelescope rule.rhs result.nparams) :
    (Lean4Lean.restoreNestedDeclarations result loweredEnv auxRec allIndNames
      allowPrimitive types auxRecNames sourceEnv).WF fun out =>
        Nonempty (NestedRestorationFolds result loweredEnv sourceEnv
          auxRec allIndNames types auxRecNames out) := by
  have Hinductives := restoreInductiveDecls_refines result loweredEnv auxRec
    allIndNames allowPrimitive types Htypes sourceEnv
  have Hcombined :
      (((types.forM fun indType => Lean4Lean.restoreInductiveDecl result
          loweredEnv auxRec allIndNames allowPrimitive indType) sourceEnv).bind
        fun primaryOut =>
          (auxRecNames.forM fun recName => Lean4Lean.restoreRecursorDecl result
            loweredEnv auxRec allIndNames allowPrimitive recName)
            primaryOut.2).WF fun out =>
              Nonempty (NestedRestorationFolds result loweredEnv
                sourceEnv auxRec allIndNames types auxRecNames out) :=
    Hinductives.bind fun primaryOut Hprimary => by
      rcases primaryOut with ⟨done, primaryEnv⟩
      rcases done with ⟨⟩
      rcases Hprimary with ⟨_, ⟨HinductiveTrace⟩⟩
      have Hauxiliaries := restoreRecursorDecls_refines result loweredEnv
        auxRec allIndNames allowPrimitive auxRecNames Haux primaryEnv
      exact Hauxiliaries.mono fun out Hout => by
        rcases Hout with ⟨hunit, ⟨HauxTrace⟩⟩
        exact ⟨{
          sourceFamiliesEnv := primaryEnv
          inductives := HinductiveTrace
          auxiliaries := HauxTrace
          outputUnit := hunit }⟩
  simpa [Lean4Lean.restoreNestedDeclarations, bind, StateT.bind] using Hcombined


end VerifyInductive
end Lean4Lean
