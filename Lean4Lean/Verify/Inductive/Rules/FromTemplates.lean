import Lean4Lean.Verify.Inductive.Recursor.Binders.MinorPremises

/-! Rules built from rule templates. The minor pass of the executable records a rule template
(`RecRuleTemplate`, with one `RecCallTemplate` per recursive call) for each constructor, and
`mkRecRulesFromTemplates` instantiates the templates once the pass is over. This file shows
that the instantiated rules are the rules described by `RecursorRuleSyntax`, with their typing
(`RuleFromTemplateTyping`, `TypedRecursorRules`) taken from the facts recorded with each
template. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

def RecursorFVarSuffix.castRoot
    {c c' origin : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Rorigin : RecursorContextWF origin recLparams} {xs : Array Expr}
    (h : c = c') (H : RecursorFVarSuffix R Rorigin xs) :
    RecursorFVarSuffix (h ▸ R) Rorigin xs := by
  cases h
  exact H

/-- An induction hypothesis type recorded by the minor pass and the call
template emitted beside it have the same allocation-insensitive replay payload. -/
theorem InductionHypothesisType.replayTrace_eq_template
    (O : InductionHypothesisType stats recInfos root field type)
    (call : AddInductive.RecCallTemplate)
    (hcall : call = {
      major := field
      args := O.args
      lctx := O.current.lctx
      targetTypeIdx := O.ownerIdx
      targetIndices :=
        O.exposedType.getAppArgs[stats.params.size:]
      template := O.current.lctx.mkLambda O.args <|
        (mkAppN (.bvar O.args.size)
          O.exposedType.getAppArgs[stats.params.size:]).app
            (mkAppN field O.args) })
    (howner : O.ownerIdx < recInfos.size)
    (fieldBinders : List FVarId) :
    O.replayTrace fieldBinders =
      recCallTemplateShape call (recInfos.map (·.motive))
        fieldBinders := by
  subst call
  simp [InductionHypothesisType.replayTrace,
    recCallTemplateShape,
    O.arguments_bound.toFVarArrayIn.exprArrayFVarIds, howner]

/-- The rule builder from templates is a transparent read of the current
local context followed by a pure map.  This is the executable boundary used
by the installation proof; in particular it performs no inference, WHNF, or
fresh-name allocation. -/
theorem AddInductive.mkRecRulesFromTemplates.WF
    (indTypes : Array InductiveType) (elimLevel : Level)
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo) (dIdx : Nat)
    (motives minors : Array Expr) (c : AddInductive.Context) :
    (AddInductive.mkRecRulesFromTemplates indTypes elimLevel stats recInfos
      dIdx motives minors c).WF fun rules =>
        rules = recInfos[dIdx]!.ruleTemplates.toList.map fun blueprint =>
          blueprint.instantiate indTypes stats motives minors
            (AddInductive.getRecLevels elimLevel stats.levels) c.lctx := by
  simp only [AddInductive.mkRecRulesFromTemplates, getLCtx, readThe, read]
  exact Except.WF.pure rfl

/-- Instantiate the typed call row recorded by the minor pass with the complete
minor array and the exact recursor levels.  No call generation, inference,
or constructor traversal is replayed here. -/
theorem TypedCallTemplates.retainedGeneratedCalls
    {recLparams : List Name}
    {Rfield : RecursorContextWF fieldRoot recLparams}
    (H : TypedCallTemplates Rfield decl depth stats
      motives rootScope fields hypotheses calls)
    (hsize : hypotheses.size = fields.size)
    (indTypes : Array InductiveType) (minors : Array Expr)
    (lvls : List Level) :
    TypedRecursiveCallsAfterHypotheses indTypes stats motives
      minors lvls Rfield decl rootScope fields
        (calls.map fun call => call.instantiate indTypes stats motives minors lvls)
        fields.size := by
  refine {
    covered := Nat.le_refl _
    size := by simp [H.size_eq, hsize]
    entries := ?_ }
  intro i hi _hiFields
  have hiHypotheses : i < hypotheses.size := by rwa [hsize]
  rcases H.entry i hiHypotheses with
    ⟨originRoot, Rorigin, priorHypotheses, Hrecent,
      hpriorSize, hchkO, ⟨Horigin⟩⟩
  rcases Horigin.semantic indTypes minors lvls with
    ⟨S, hscope, ⟨Hmotive⟩, _hreplay⟩
  have hiCalls : i < calls.size := by rw [H.size_eq, hsize]; exact hi
  have hbuilt :
      (calls.map fun call =>
        call.instantiate indTypes stats motives minors lvls)[i]! =
          calls[i]!.instantiate indTypes stats motives minors lvls := by
    simp [hiCalls]
  rw [hbuilt]
  rw [show fields[i] = fields[i]! from
    (getElem!_pos fields i hi).symm]
  exact ⟨originRoot, Rorigin, priorHypotheses, Hrecent,
    hpriorSize, hchkO, depth + i, S, hscope, ⟨Hmotive⟩⟩

theorem CallTemplatesMatch.boundGeneratedCalls
    {sourceFullContext fieldRoot : AddInductive.Context}
    {recursiveFields hypotheses : Array Expr}
    {origins : MinorInductionHypothesisTypes sourceFullContext
      recursiveFields hypotheses}
    {calls : Array AddInductive.RecCallTemplate}
    {allFields : Array Expr}
    (H : CallTemplatesMatch origins allFields calls)
    (hfieldRoot : origins.fieldRoot = fieldRoot)
    (hsize : hypotheses.size = recursiveFields.size)
    (indTypes : Array InductiveType) (minors : Array Expr)
    (lvls : List Level) :
    RecursiveCallsPrefix indTypes origins.stats
      (origins.recInfos.map (·.motive)) minors lvls fieldRoot recursiveFields
      (calls.map fun call => call.instantiate indTypes origins.stats
        (origins.recInfos.map (·.motive)) minors lvls)
      recursiveFields.size := by
  subst fieldRoot
  refine {
    covered := Nat.le_refl _
    size := ?_
    entries := ?_ }
  · simp [H.size_eq, hsize]
  · intro i hi _hiFields
    have hiHypotheses : i < hypotheses.size := by omega
    have Hentry := H.entry i hiHypotheses
    rw [getElem!_pos recursiveFields i hi] at Hentry
    rcases Hentry with
      ⟨originRoot, sourceType, O, D, HoriginRoot, htype, hcall⟩
    let value := calls[i]!.instantiate indTypes origins.stats
      (origins.recInfos.map (·.motive)) minors lvls
    have hiCalls : i < calls.size := by rw [H.size_eq]; exact hiHypotheses
    have hvalue :
        (calls.map fun call => call.instantiate indTypes origins.stats
          (origins.recInfos.map (·.motive)) minors lvls)[i]! = value := by
      rw [getElem!_pos _ i (by simpa using hiCalls)]
      simp [value, getElem!_pos calls i hiCalls]
    rw [hvalue]
    refine ⟨{
      exposedType := O.exposedType
      ownerIdx := O.ownerIdx
      owner_valid := O.owner_valid
      localArgs := O.args
      current := O.current
      current_wf := O.current_wf
      current_extends := HoriginRoot.trans O.current_extends
      arguments_bound := O.arguments_bound.rebaseRoot HoriginRoot
      value_eq := ?_ }⟩
    dsimp [value]
    rw [hcall]
    simp only [AddInductive.RecCallTemplate.instantiate]
    simp [AddInductive.getIIndices, O.owner_valid]

/-- A bound rule together with the exact components recorded by the minor pass
and used to build it.  These projection equalities prevent later semantic assembly from
recovering them by replay or alpha-conversion. -/
structure RuleFromTemplate
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (S : MinorPremiseType) (T : ConstructorFieldTraversal)
    (B : AddInductive.RecRuleTemplate)
    (minorIdx : Nat) (fieldRoot outerRoot : AddInductive.Context) where
  certificate : RecursorRuleSyntax indTypes stats motives minors
    lvls S.constructor minorIdx
      (B.instantiate indTypes stats motives minors lvls outerRoot.lctx)
  root_eq : certificate.root = fieldRoot
  target_eq : certificate.target = T.terminal
  allArgs_eq : certificate.allArgs = S.fields
  recursiveArgs_eq : certificate.recursiveArgs = S.recursiveFields
  recursiveResults_eq : certificate.recursiveResults =
    B.recursiveCalls.map fun call =>
      call.instantiate indTypes stats motives minors lvls
  callOrigins : ∃ origins : MinorInductionHypothesisTypes
      S.sourceFullContext S.recursiveFields S.hypotheses,
    S.hypothesis_type_origins = some origins ∧
      CallTemplatesMatch origins S.fields B.recursiveCalls

theorem RuleTemplateMatchesMinor.boundGeneratedRule
    {stats : AddInductive.InductiveStats}
    {S : MinorPremiseType} {minor : Expr}
    {B : AddInductive.RecRuleTemplate}
    (Horigin : RuleTemplateMatchesMinor stats S minor B)
    (indTypes : Array InductiveType) (motives minors : Array Expr)
    (lvls : List Level) (minorIdx : Nat)
    {fieldRoot outerRoot : AddInductive.Context}
    (HfieldWF : BindingContextWF fieldRoot)
    (HouterWF : BindingContextWF outerRoot)
    (HfieldSource : BindingContextLE fieldRoot S.sourceFullContext)
    (HfieldOuter : BindingContextLE fieldRoot outerRoot)
    (Hparams : FVarArrayIn outerRoot stats.params)
    (Hmotives : FVarArrayIn outerRoot motives)
    (Hminors : FVarArrayIn outerRoot minors)
    (HouterNodup : ((Hparams.fvars ++ Hmotives.fvars) ++
      Hminors.fvars).Nodup)
    (Hfields : FVarArrayIn fieldRoot S.fields)
    (HfieldsNodup : Hfields.fvars.Nodup)
    (Hrecursive : FVarArrayIn fieldRoot S.recursiveFields)
    (hrecursive : S.recursiveFields.toList.Sublist S.fields.toList)
    (HrecursiveNodup : Hrecursive.fvars.Nodup)
    (hfieldsFresh : ∀ fv ∈ Hfields.fvars,
      fv ∉ (Hparams.fvars ++ Hmotives.fvars) ++ Hminors.fvars)
    (hminor : minorIdx < minors.size)
    (hminorEq : minors[minorIdx]! = minor)
    (Hcalls : RecursiveCallsPrefix indTypes stats motives minors lvls
      fieldRoot S.recursiveFields
      (B.recursiveCalls.map fun call =>
        call.instantiate indTypes stats motives minors lvls)
      S.recursiveFields.size) :
    ∃ T, S.traversal = some T ∧
      Nonempty (RuleFromTemplate indTypes stats motives minors lvls
        S T B minorIdx fieldRoot outerRoot) := by
  rcases Horigin with
    ⟨hctor, hfields, hlctx, hminorTemplate, traversal, origins,
      htraversal, horigins, htargetOwner, htargetIndices, HcallOrigins⟩
  let Hrule : RecursorRuleSyntax indTypes stats motives minors lvls
      S.constructor minorIdx
      (B.instantiate indTypes stats motives minors lvls outerRoot.lctx) := {
    root := fieldRoot
    outerRoot := outerRoot
    root_wf := HfieldWF
    outer_wf := HouterWF
    root_le_outer := HfieldOuter
    target := traversal.terminal
    allArgs := S.fields
    recursiveArgs := S.recursiveFields
    recursiveResults := B.recursiveCalls.map fun call =>
      call.instantiate indTypes stats motives minors lvls
    minor_valid := hminor
    params_bound := Hparams
    motives_bound := Hmotives
    minors_bound := Hminors
    outer_binders_nodup := HouterNodup
    all_args_bound := Hfields
    recursive_args_bound := Hrecursive
    recursive_args_sublist := hrecursive
    all_args_nodup := HfieldsNodup
    recursive_args_nodup := HrecursiveNodup
    all_args_outer_fresh := hfieldsFresh
    recursive_calls := Hcalls
    ctor_eq := by
      simpa [AddInductive.RecRuleTemplate.instantiate] using hctor
    fields_eq := by
      simp [AddInductive.RecRuleTemplate.instantiate, hfields]
    rhs_eq := by
      simp only [AddInductive.RecRuleTemplate.instantiate]
      rw [hfields, hminorTemplate, hlctx, hminorEq]
      have hfieldLambda := Hfields.mkLambda_mono HfieldSource
        (mkAppN (mkAppN minor S.fields)
          (B.recursiveCalls.map fun call =>
            call.instantiate indTypes stats motives minors lvls))
      exact congrArg (fun body =>
        outerRoot.lctx.mkLambda stats.params <|
        outerRoot.lctx.mkLambda motives <|
          outerRoot.lctx.mkLambda minors body) hfieldLambda }
  exact ⟨traversal, htraversal,
    ⟨⟨Hrule, rfl, rfl, rfl, rfl, rfl,
      ⟨origins, horigins, HcallOrigins⟩⟩⟩⟩

theorem RecursorFieldDecisions.selectedSublist
    (H : RecursorFieldDecisions stats root source c terminal fields
      recursiveFields positions) :
    recursiveFields.toList.Sublist fields.toList := by
  induction H with
  | nil => exact .slnil
  | @nonrecursive c name dom body bi fields recursiveFields positions
      Hdecision _ ih =>
      simpa using ih.append
        (List.nil_sublist [Expr.fvar ⟨c.ngen.curr⟩])
  | @recursive c name dom body bi fields recursiveFields positions target
      Hdecision _ ih =>
      simpa using ih.append
        (List.Sublist.refl [Expr.fvar ⟨c.ngen.curr⟩])

/-- The rule template row has exactly one entry for every constructor
of its source owner.  This is derived from the second-pass row
counts; the rule builder itself does not need to rerun the constructor
traversal to discover its output cardinality. -/
theorem RuleTemplatesMatch.ownerRowSize
    {indTypes : Array InductiveType}
    {stats : AddInductive.InductiveStats}
    {recInfos : Array AddInductive.RecInfo}
    {Horigins : RecInfoBinderTypes c recInfos}
    (H : RuleTemplatesMatch stats recInfos Horigins)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (owner : Nat) (howner : owner < recInfos.size) :
    recInfos[owner]!.ruleTemplates.size =
      indTypes[owner]!.ctors.length := by
  calc
    recInfos[owner]!.ruleTemplates.size =
        Horigins.minorTypes[owner]!.size := H.rows_size owner howner
    _ = recInfos[owner]!.minors.size :=
      (Horigins.minors owner howner).size_eq
    _ = indTypes[owner]!.ctors.length := hcounts owner howner

/-- Per-owner minor cardinalities identify the flattened minor prefix with
the constructor prefix used by recursor installation. -/
theorem recInfoMinorPrefixLength_eq
    (recInfos : Array AddInductive.RecInfo)
    (indTypes : Array InductiveType)
    (hsize : recInfos.size = indTypes.size)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (owner : Nat) (howner : owner ≤ recInfos.size) :
    ((recInfos.toList.take owner).flatMap
      (fun info => info.minors.toList)).length =
      recursorMinorOffset indTypes owner := by
  induction owner with
  | zero => simp [recursorMinorOffset]
  | succ owner ih =>
      have hrec : owner < recInfos.size := by omega
      have hind : owner < indTypes.size := by omega
      rw [recursorMinorOffset_step indTypes owner hind]
      simp [List.take_add_one, hrec, ih (by omega)]
      simpa [getElem!_pos recInfos owner hrec,
        getElem!_pos indTypes owner hind] using hcounts owner hrec

/-- The flattened minor selected by the canonical owner offset is literally
the row-local minor paired with that owner's rule template. -/
theorem recInfoFlatMinorAtOffset
    (recInfos : Array AddInductive.RecInfo)
    (indTypes : Array InductiveType)
    (hsize : recInfos.size = indTypes.size)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (owner : Nat) (howner : owner < recInfos.size)
    (localIndex : Nat)
    (hlocal : localIndex < recInfos[owner]!.minors.size) :
    (recInfos.flatMap (·.minors))[
      recursorMinorOffset indTypes owner + localIndex]! =
      recInfos[owner]!.minors[localIndex]! := by
  have hprefix := recInfoMinorPrefixLength_eq recInfos indTypes hsize
    hcounts owner (Nat.le_of_lt howner)
  have hrowsOwner : owner < recInfos.toList.length := by simpa using howner
  have hrowLocal : localIndex < recInfos.toList[owner].minors.toList.length := by
    simpa [getElem!_pos recInfos owner howner] using hlocal
  have hflatIndex :
      ((recInfos.toList.take owner).flatMap
          (fun info => info.minors.toList)).length + localIndex <
        (recInfos.toList.flatMap
          (fun info => info.minors.toList)).length := by
    rw [hprefix, ← Array.toList_flatMap, Array.length_toList]
    have hindOwner : owner < indTypes.size := by omega
    have hroom := recursorMinorOffset_room indTypes owner hindOwner
    have hrowCount := hcounts owner howner
    have htotal : (recInfos.flatMap (·.minors)).size =
        (indTypes.toList.flatMap (fun type => type.ctors)).length := by
      calc
        (recInfos.flatMap (·.minors)).size =
            (indTypes.flatMap fun type => type.ctors.toArray).size :=
          mkRecInfos.flatMinors_size hsize hcounts
        _ = (indTypes.toList.flatMap
            (fun type => type.ctors)).length :=
          by simpa [ownedConstructors] using
            (ownedConstructors_length_eq_flattened_size indTypes).symm
    rw [htotal]
    omega
  have Hget := List.flatMap_getElem_prefix recInfos.toList
    (fun info => info.minors.toList) owner localIndex hrowsOwner
    hrowLocal hflatIndex
  have harrayIndex : recursorMinorOffset indTypes owner + localIndex <
      (recInfos.flatMap (·.minors)).size := by
    change recursorMinorOffset indTypes owner + localIndex <
      (recInfos.flatMap (·.minors)).toList.length
    simpa [Array.toList_flatMap, hprefix] using hflatIndex
  have Hget' :
      (recInfos.flatMap (·.minors))[
        recursorMinorOffset indTypes owner + localIndex]'harrayIndex =
      recInfos[owner]!.minors[localIndex]'hlocal := by
    change (recInfos.flatMap (·.minors)).toList[
        recursorMinorOffset indTypes owner + localIndex] =
      recInfos[owner]!.minors.toList[localIndex]
    simpa [Array.toList_flatMap, hprefix,
      getElem!_pos recInfos owner howner] using Hget
  rw [getElem!_pos (recInfos.flatMap (·.minors))
      (recursorMinorOffset indTypes owner + localIndex) harrayIndex,
    getElem!_pos recInfos[owner]!.minors localIndex hlocal]
  exact Hget'

theorem RuleTemplateMatchesMinor.boundGeneratedRuleOfSource
    {stats : AddInductive.InductiveStats}
    {recInfos : Array AddInductive.RecInfo}
    {S : MinorPremiseType} {minor : Expr}
    {B : AddInductive.RecRuleTemplate}
    (Horigin : RuleTemplateMatchesMinor stats S minor B)
    {outerRoot : AddInductive.Context} {recLparams : List Name}
    {Router : RecursorContextWF outerRoot recLparams}
    (HS : TypedMinorTraversal Router S)
    (Hhas : S.HasInductionHypothesisTypes stats recInfos)
    (hrecursiveFields : HS.traversal.recursiveFields = S.recursiveFields)
    (indTypes : Array InductiveType) (lvls : List Level)
    (minorIdx : Nat)
    (Hparams : FVarArrayIn outerRoot stats.params)
    (Hbindings : RecInfoBindings outerRoot recInfos)
    (HouterNodup : ((Hparams.fvars ++ Hbindings.motives.fvars) ++
      Hbindings.flatMinors.fvars).Nodup)
    (hminor : minorIdx < (recInfos.flatMap (·.minors)).size)
    (hminorEq : (recInfos.flatMap (·.minors))[minorIdx]! = minor)
    (hfieldsFresh : ∀ fv ∈
      HS.fieldsRecent.toFVarArrayAfter.toFVarArrayIn.fvars,
      fv ∉ (Hparams.fvars ++ Hbindings.motives.fvars) ++
        Hbindings.flatMinors.fvars) :
    Nonempty (RuleFromTemplate indTypes stats
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
      S HS.traversal B minorIdx HS.traversal.terminalContext outerRoot) := by
  rcases Horigin with
    ⟨hctor, hfields, hlctx, hminorTemplate, traversal, origins,
      htraversal, horigins, htargetOwner, htargetIndices, HcallOrigins⟩
  have htraversalEq : HS.traversal = traversal := by
    rw [HS.traversal_eq] at htraversal
    exact Option.some.inj htraversal
  subst traversal
  have hfieldRoot : origins.fieldRoot = HS.traversal.terminalContext :=
    S.hypothesis_origins_fieldRoot origins HS.traversal horigins
      HS.traversal_eq
  have HcallsRaw := HcallOrigins.boundGeneratedCalls hfieldRoot
    S.hypotheses_size indTypes (recInfos.flatMap (·.minors)) lvls
  have Hhas' : origins.stats = stats ∧
      origins.recInfos.map (·.motive) = recInfos.map (·.motive) := by
    simpa [MinorPremiseType.HasInductionHypothesisTypes, horigins] using Hhas
  have hstats : origins.stats = stats := by
    exact Hhas'.1
  have hmotives : origins.recInfos.map (·.motive) =
      recInfos.map (·.motive) := by
    exact Hhas'.2
  rw [hstats, hmotives] at HcallsRaw
  have hselected : S.recursiveFields.toList.Sublist S.fields.toList := by
    rw [← HS.traversal_fields, ← hrecursiveFields]
    exact HS.traversal.decisions.selectedSublist
  rcases FVarArrayIn.ofSublist
      HS.fieldsRecent.toFVarArrayAfter.toFVarArrayIn hselected with
    ⟨Hrecursive⟩
  have HrecursiveNodup : Hrecursive.fvars.Nodup := by
    have hallExpr : S.fields.toList.Nodup := by
      rw [HS.fieldsRecent.toFVarArrayAfter.toFVarArrayIn.expressions]
      exact List.Pairwise.map Expr.fvar
        (fun _ _ hne heq => hne (Expr.fvar.inj heq))
        HS.fieldsRecent.toFVarArrayAfter.nodup
    have hselectedExpr : S.recursiveFields.toList.Nodup :=
      hallExpr.sublist hselected
    rw [Hrecursive.expressions] at hselectedExpr
    change List.Pairwise (fun a b : Expr => a ≠ b)
      (Hrecursive.fvars.map Expr.fvar) at hselectedExpr
    rw [List.pairwise_map] at hselectedExpr
    change List.Pairwise (fun a b : FVarId => a ≠ b) Hrecursive.fvars
    exact hselectedExpr.imp fun hneq heq =>
      hneq (congrArg Expr.fvar heq)
  rcases RuleTemplateMatchesMinor.boundGeneratedRule
    (Horigin := ⟨hctor, hfields, hlctx, hminorTemplate,
      HS.traversal, origins, HS.traversal_eq, horigins,
      htargetOwner, htargetIndices, HcallOrigins⟩)
    indTypes (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
    minorIdx HS.terminalWF.toBindingContextWF Router.toBindingContextWF
    HS.hypothesesRecent.contextLE
    (HS.hypothesesRecent.contextLE.trans HS.extension.contextLE)
    Hparams Hbindings.motives Hbindings.flatMinors HouterNodup
    HS.fieldsRecent.toFVarArrayAfter.toFVarArrayIn
    HS.fieldsRecent.toFVarArrayAfter.nodup Hrecursive hselected
    HrecursiveNodup hfieldsFresh hminor hminorEq HcallsRaw with
      ⟨T, hT, ⟨Hretained⟩⟩
  have hTeq : T = HS.traversal := Option.some.inj
    (hT.symm.trans HS.traversal_eq)
  subst T
  exact ⟨Hretained⟩

/-- Semantic payload indexed by the minor pass's literal components, before
transport to the projections of the retained bound-rule certificate. -/
structure RuleFromTemplateTyping
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (sourceCtor : Constructor) (minorIdx : Nat) (sourceRule : RecursorRule)
    (producerRoot : AddInductive.Context) (target : Expr)
    (allArgs recursiveArgs recursiveResults : Array Expr)
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF semanticRoot recLparams) (decl : VInductDecl)
    (expectedOwnerIdx : Nat) where
  depth : Nat
  context : RecursorContextWF producerRoot recLparams
  fieldRoot : AddInductive.Context
  fieldRootContext : RecursorContextWF fieldRoot recLparams
  parameterDepth : Nat
  parameterSuffix : RecursorParameterContextSuffix fieldRootContext stats
    parameterDepth
  parameterDecls : VLCtx
  parameterDecls_eq : parameterSuffix.parameterDecls = parameterDecls
  fieldRootExtension : RecursorContextExtension fieldRootContext Rroot
  fieldsRecent : RecursorFVarSuffix fieldRootContext context allArgs
  parameterTail : Expr
  parameterPrefix : ParameterPrefix stats 0 sourceCtor.type parameterTail
  parameterTail_fvars : parameterTail.FVarsIn
    (· ∈ ExprArrayFVarIds stats.params)
  parameterTarget : VExpr
  parameterTranslation : TrExprS fieldRootContext.venv recLparams
    fieldRootContext.mlctx.vlctx parameterTail parameterTarget
  parameterType : fieldRootContext.venv.IsType recLparams.length
    fieldRootContext.mlctx.vlctx.toCtx parameterTarget
  parameterTranslation₀ : ∃ t, TrExprS fieldRootContext.venv recLparams
      parameterSuffix.parameterDecls parameterTail t ∧
    fieldRootContext.venv.IsType recLparams.length
      parameterSuffix.parameterDecls.toCtx t
  fieldOpening : ConstructorFieldOpening parameterTail target allArgs
  fieldParameterUp : IsFVarUpSet (fun fv =>
    fv ∈ fieldsRecent.fvars ∨ fv ∈ ExprArrayFVarIds stats.params)
      context.mlctx.vlctx
  fieldCheck : ∃ M : TypeChecker.MLCtx, M.WF context.venv recLparams ∧
    (0 < allArgs.size → context.chk = M) ∧
    ∃ hn : allArgs.size ≤ M.length,
      MLCtxTopAgree context.mlctx M allArgs.size ∧
        (M.dropN allArgs.size hn).vlctx = parameterSuffix.parameterDecls ∧
        ∃ T₀, TrExprS fieldRootContext.venv recLparams
          parameterSuffix.parameterDecls parameterTail T₀ ∧
        ∃ t₀', TrExprS context.venv recLparams M.vlctx target t₀' ∧
          context.venv.IsDefEqU recLparams.length
            parameterSuffix.parameterDecls.toCtx T₀
            (M.mkForall' allArgs.size hn t₀')
  context_venv : context.venv = Rroot.venv
  validStats : RecursorValidAppStatsWF context.venv recLparams
    context.mlctx.vlctx stats decl depth
  ownerIdx : Nat
  owner_lt : ownerIdx < decl.types.length
  expected_owner_lt : expectedOwnerIdx < decl.types.length
  expected_target_valid : AddInductive.isValidIndAppIdx stats target
    expectedOwnerIdx = true
  targetTarget : VExpr
  target_not_forall : target.isForall = false
  target_translation : TrExprS context.venv recLparams context.mlctx.vlctx
    target targetTarget
  target_type : context.venv.IsType recLparams.length
    context.mlctx.vlctx.toCtx targetTarget
  fieldTargetDefEq : fieldRootContext.venv.IsDefEqU recLparams.length
    fieldRootContext.mlctx.vlctx.toCtx parameterTarget
      (context.mlctx.mkForall' allArgs.size fieldsRecent.size_le targetTarget)
  constructorTarget : VExpr
  constructor_translation : TrExprS context.venv recLparams
    context.mlctx.vlctx
      (mkAppN (mkAppN (.const sourceCtor.name stats.levels) stats.params)
        allArgs) constructorTarget
  constructor_typing : context.venv.HasType recLparams.length
    context.mlctx.vlctx.toCtx constructorTarget targetTarget
  target_valid : AddInductive.isValidIndApp? stats target = some ownerIdx
  validated : RecursorValidatedIndAppAt context.venv recLparams
    context.mlctx.vlctx stats decl depth target targetTarget ownerIdx
  fields : List (RecursiveFieldDomainAt context.venv decl recLparams.length)
  selection : RecursiveFieldSelectionsAt context.venv decl recLparams.length
    allArgs recursiveArgs fields
  decisionPositions : List Nat
  decisions : RecursorFieldDecisions stats fieldRoot parameterTail producerRoot
    target allArgs recursiveArgs decisionPositions
  calls : TypedRecursiveCallsAfterHypotheses indTypes stats motives
    minors lvls context decl
      (fun fv => fv ∈ fieldOpening.fvars ∨
        fv ∈ ExprArrayFVarIds stats.params)
      recursiveArgs recursiveResults recursiveArgs.size

theorem RuleFromTemplateTyping.toTyping
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (C : RuleFromTemplateTyping indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule producerRoot target allArgs recursiveArgs
      recursiveResults Rroot decl expectedOwnerIdx)
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (hroot : H.root = producerRoot) (htarget : H.target = target)
    (hall : H.allArgs = allArgs) (hrecursive : H.recursiveArgs = recursiveArgs)
    (hresults : H.recursiveResults = recursiveResults)
    {recInfos : Array AddInductive.RecInfo} {elimLevel : Level}
    (binding : MotiveBinding C.context
      recInfos[C.ownerIdx]! elimLevel)
    (HmotiveTelescope : Nonempty
      (MotiveAppliesTo C.context stats
        recInfos[C.ownerIdx]! binding target C.targetTarget))
    (Hlookup : MotiveTelescopesAt C.context stats decl recInfos
      elimLevel) :
    ∃ S : H.Semantics Rroot decl expectedOwnerIdx,
      ∃ binding' : MotiveBinding S.context
          recInfos[S.ownerIdx]! elimLevel,
        Nonempty (MotiveAppliesTo S.context stats
          recInfos[S.ownerIdx]! binding' H.target S.targetTarget) ∧
        MotiveTelescopesAt S.context stats decl recInfos elimLevel ∧
        S.recursivePositions = C.decisionPositions ∧
        S.parameterDecls = C.parameterDecls ∧
        S.context = (hroot.symm ▸ C.context) ∧
        S.fieldOpening.fvars = C.fieldsRecent.fvars ∧
        Nonempty (TypedRecursiveCallsAfterHypotheses
          indTypes stats motives minors lvls S.context decl
            (fun fv => fv ∈ S.fieldOpening.fvars ∨
              fv ∈ ExprArrayFVarIds stats.params)
            H.recursiveArgs H.recursiveResults H.recursiveArgs.size) := by
  subst producerRoot
  subst target
  subst allArgs
  subst recursiveArgs
  subst recursiveResults
  let S : H.Semantics Rroot decl expectedOwnerIdx := {
    depth := C.depth
    context := C.context
    fieldRoot := C.fieldRoot
    fieldRootContext := C.fieldRootContext
    parameterDepth := C.parameterDepth
    parameterSuffix := C.parameterSuffix
    parameterDecls := C.parameterDecls
    parameterDecls_eq := C.parameterDecls_eq
    fieldRootExtension := C.fieldRootExtension
    fieldsRecent := C.fieldsRecent
    parameterTail := C.parameterTail
    parameterPrefix := C.parameterPrefix
    parameterTail_fvars := C.parameterTail_fvars
    parameterTarget := C.parameterTarget
    parameterTranslation := C.parameterTranslation
    parameterType := C.parameterType
    parameterTranslation₀ := C.parameterTranslation₀
    fieldOpening := C.fieldOpening
    fieldParameterUp := C.fieldParameterUp
    fieldCheck := C.fieldCheck
    context_venv := C.context_venv
    validStats := C.validStats
    ownerIdx := C.ownerIdx
    owner_lt := C.owner_lt
    expected_owner_lt := C.expected_owner_lt
    expected_target_valid := C.expected_target_valid
    targetTarget := C.targetTarget
    target_not_forall := C.target_not_forall
    target_translation := C.target_translation
    target_type := C.target_type
    fieldTargetDefEq := C.fieldTargetDefEq
    constructorTarget := C.constructorTarget
    constructor_translation := by
      simpa [RecursorRuleSyntax.sourceConstructorMajor] using
        C.constructor_translation
    constructor_typing := C.constructor_typing
    target_valid := C.target_valid
    validated := C.validated
    fields := C.fields
    selection := C.selection
    decisionPositions := C.decisionPositions
    decisions := C.decisions
    calls := C.calls.toAbove }
  exact ⟨S, binding, HmotiveTelescope, Hlookup, rfl, rfl, rfl,
    C.fieldOpening.fvars_eq_bound
      C.fieldsRecent.toFVarArrayAfter.toFVarArrayIn,
    ⟨C.calls⟩⟩

/-- Casting a recursor context along an equality of contexts leaves its
checker context unchanged. -/
theorem RecursorContextWF.chk_cast {c c' : AddInductive.Context}
    {U : List Name} (h : c = c') (R : RecursorContextWF c U) :
    (h ▸ R).chk = R.chk := by
  subst h
  rfl

structure RecursorRuleSyntax.CallAt
    {recInfos : Array AddInductive.RecInfo}
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (S : H.Semantics Rroot decl expectedOwnerIdx)
    (minorShape : MinorPremiseType)
    (j : Nat) (hj : j < H.recursiveArgs.size) where
  hypothesisOrigins : MinorInductionHypothesisTypes
    minorShape.sourceFullContext minorShape.recursiveFields
      minorShape.hypotheses
  hypothesisOrigins_eq :
    minorShape.hypothesis_type_origins = some hypothesisOrigins
  sourceOriginRoot : AddInductive.Context
  sourceType : Expr
  sourceOrigin : InductionHypothesisType hypothesisOrigins.stats
    hypothesisOrigins.recInfos sourceOriginRoot
      minorShape.recursiveFields[j]! sourceType
  sourceDeclaration : FVarDeclAt minorShape.sourceFullContext
    minorShape.hypotheses j
  sourceDeclaration_type : sourceDeclaration.type =
    (sourceType.consumeTypeAnnotationsVerified
      minorShape.sourceFullContext.env.isTypeAnnotationWrapper)
  originRoot : AddInductive.Context
  originContext : RecursorContextWF originRoot recLparams
  priorHypotheses : Array Expr
  originRecent : RecursorFVarSuffix S.context originContext
    priorHypotheses
  originCheck : originContext.chk = S.context.chk
  priorHypotheses_size : priorHypotheses.size = j
  callDepth : Nat
  semantic : TypedRecursiveCall indTypes stats
    motives minors lvls originContext decl callDepth
      H.recursiveArgs[j] H.recursiveResults[j]!
  root_scope : semantic.rootScope = fun fv =>
    fv ∈ S.fieldOpening.fvars ∨ fv ∈ ExprArrayFVarIds stats.params
  motiveApplication : Nonempty semantic.MotiveApplication
  replay : sourceOrigin.replayTrace minorShape.fields_bound.fvars =
    semantic.generated.replayTrace H.all_args_bound.fvars

/-- The motive binder and telescope retained at the exact context in which
the rule target was validated, as recorded by the minor pass rather than
recomputed from the later recursor context. -/
structure RecursorRuleSyntax.MotiveAt
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (S : H.Semantics Rroot decl expectedOwnerIdx)
    (recInfos : Array AddInductive.RecInfo) (elimLevel : Level) where
  minorShape : MinorPremiseType
  minorTraversal : ConstructorFieldTraversal
  minorTraversal_eq : minorShape.traversal = some minorTraversal
  decisionPositions_eq : minorTraversal.recursivePositions =
    S.recursivePositions
  calls : TypedRecursiveCallsAfterHypotheses indTypes stats
    motives minors lvls S.context decl
      (fun fv => fv ∈ S.fieldOpening.fvars ∨
        fv ∈ ExprArrayFVarIds stats.params)
      H.recursiveArgs H.recursiveResults H.recursiveArgs.size
  replay : ∀ j (hj : j < H.recursiveArgs.size),
    Nonempty (RecursorRuleSyntax.CallAt
      (recInfos := recInfos) H S minorShape j hj)
  binding : MotiveBinding S.context recInfos[S.ownerIdx]! elimLevel
  telescope : Nonempty (MotiveAppliesTo S.context stats
    recInfos[S.ownerIdx]! binding H.target S.targetTarget)
  motiveLookup : MotiveTelescopesAt S.context stats decl recInfos
    elimLevel

/-- Row-wise motive facts recorded by the minor pass, indexed by the exact semantic batch
stored for installation.  Indexing by the batch prevents a later consumer
from pairing a telescope with a different semantic reconstruction. -/
inductive TypedRecursorRules.MotiveAt
    (recInfos : Array AddInductive.RecInfo) (elimLevel : Level) :
    {ctors : List Constructor} → {start : Nat} →
    {rules : List RecursorRule} →
    TypedRecursorRules indTypes stats
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
      Rroot decl ownerIdx ctors start rules → Prop
  | nil : MotiveAt recInfos elimLevel
      (.nil : TypedRecursorRules indTypes stats
        (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
        Rroot decl ownerIdx [] start [])
  | cons
      (Hrule : RecursorRuleSyntax indTypes stats
        (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
        ctor start rule)
      (S : Hrule.Semantics Rroot decl ownerIdx)
      (Hmotive : Nonempty
        (Hrule.MotiveAt S recInfos elimLevel))
      (Htail : TypedRecursorRules indTypes stats
        (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
        Rroot decl ownerIdx ctors (start + 1) rules)
      (HtailMotive : MotiveAt recInfos elimLevel Htail) :
      MotiveAt recInfos elimLevel
        (.cons Hrule ⟨S⟩ Htail)

/-- The facts recorded by the minor pass for one rule, tied to the exact row of
binder types and local constructor slot from which its template was emitted. -/
structure RecursorRuleSyntax.MinorAt
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (S : H.Semantics Rroot decl expectedOwnerIdx)
    (recInfos : Array AddInductive.RecInfo) (elimLevel : Level)
    (Horigins : RecInfoBinderTypes semanticRoot recInfos)
    (owner localIndex : Nat) where
  producer : H.MotiveAt S recInfos elimLevel
  owner_lt : owner < recInfos.size
  local_lt : localIndex < Horigins.minorTypes[owner]!.size
  shape_eq : producer.minorShape =
    Horigins.minorShapes owner owner_lt localIndex local_lt

theorem RecInfoBinderTypes.minorShapes_congr
    (H : RecInfoBinderTypes c recInfos)
    {owner owner' localIndex localIndex' : Nat}
    (howner : owner = owner')
    (owner_lt : owner < recInfos.size) (owner_lt' : owner' < recInfos.size)
    (hlocal : localIndex = localIndex')
    (local_lt : localIndex < H.minorTypes[owner]!.size)
    (local_lt' : localIndex' < H.minorTypes[owner']!.size) :
    H.minorShapes owner owner_lt localIndex local_lt =
      H.minorShapes owner' owner_lt' localIndex' local_lt' := by
  subst owner'
  subst localIndex'
  rfl

/-- Assemble the semantic certificate for the rule built from a template.
Every field comes from the facts recorded by the minor pass; no constructor traversal,
call generation, inference, or alpha-renaming is replayed. -/
theorem RuleFromTemplate.typingOfProducer
    {stats : AddInductive.InductiveStats}
    {recInfos : Array AddInductive.RecInfo}
    {S : MinorPremiseType} {B : AddInductive.RecRuleTemplate}
    {outerRoot : AddInductive.Context} {recLparams : List Name}
    {Router : RecursorContextWF outerRoot recLparams}
    {indTypes : Array InductiveType} {lvls : List Level}
    {minorIdx expectedOwnerIdx : Nat} {elimLevel : Level}
    (HS : TypedMinorTraversal Router S)
    (H : RuleFromTemplate indTypes stats
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
      S HS.traversal B minorIdx HS.traversal.terminalContext outerRoot)
    (Hsem : TypedRuleTemplateAt Router decl stats recInfos
      elimLevel parameterDecls expectedOwnerIdx S B) :
    ∃ Ssemantic : H.certificate.Semantics Router decl expectedOwnerIdx,
      ∃ producer : H.certificate.MotiveAt Ssemantic recInfos
          elimLevel,
        producer.minorShape = S ∧
        Ssemantic.parameterDecls = parameterDecls := by
  unfold TypedRuleTemplateAt at Hsem
  rcases Hsem with
    ⟨semanticOrigins, hsemanticOrigins, hsemanticStats, hsemanticMotives,
      F, hparameterDecls, depth,
      HvalidStats, fields, Hselection,
      hexpectedValid, hexpectedLt, ownerIdx,
      htargetValid, HvalidatedNonempty, binding, Htail⟩
  rcases HvalidatedNonempty with ⟨Hvalidated⟩
  let HmotiveTelescope := Htail.1
  let Htail' := Htail.2
  let HlookupNonempty := Htail'.1
  let HcallsNonempty := Htail'.2.1
  rcases HlookupNonempty with ⟨Hlookup⟩
  let Hcalls := Classical.choice HcallsNonempty
  rcases H.callOrigins with
    ⟨callOrigins, hcallOrigins, HcallOrigins⟩
  have horigins : callOrigins = semanticOrigins :=
    Option.some.inj (hcallOrigins.symm.trans hsemanticOrigins)
  subst callOrigins
  have htraversalEq : HS.traversal = F.traversal :=
    Option.some.inj (HS.traversal_eq.symm.trans F.traversal_eq)
  have hroot : H.certificate.root = F.traversal.terminalContext :=
    H.root_eq.trans (congrArg (·.terminalContext) htraversalEq)
  have htarget : H.certificate.target = F.traversal.terminal :=
    H.target_eq.trans (congrArg (·.terminal) htraversalEq)
  have hterminalNotForall : F.traversal.terminal.isForall = false := by
    rw [← Expr.abstractList_isForall F.traversal.terminal
      F.traversal.fieldFVars, F.traversal.fieldClosed]
    exact F.traversal.fieldResidual_not_forall
  have Hstaged := Hcalls.retainedGeneratedCalls S.hypotheses_size
    indTypes (recInfos.flatMap (·.minors)) lvls
  let C : RuleFromTemplateTyping indTypes stats
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
      S.constructor minorIdx
      (B.instantiate indTypes stats (recInfos.map (·.motive))
        (recInfos.flatMap (·.minors)) lvls outerRoot.lctx)
      F.traversal.terminalContext F.traversal.terminal S.fields
      S.recursiveFields
      (B.recursiveCalls.map fun call => call.instantiate indTypes stats
        (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls)
      Router decl expectedOwnerIdx := {
    depth := depth
    context := F.terminalWF
    fieldRoot := F.traversal.rootContext
    fieldRootContext := F.rootWF
    parameterDepth := F.parameterDepth
    parameterSuffix := F.parameterSuffix
    parameterDecls := parameterDecls
    parameterDecls_eq := hparameterDecls
    fieldRootExtension := F.fieldsRecent.contextExtension.trans
      F.terminalExtension
    fieldsRecent := F.fieldsRecent
    parameterTail := F.traversal.parameterTail
    parameterPrefix := by
      simpa only [F.traversal_stats, F.traversal_constructor] using
        F.traversal.parameterPrefix
    parameterTail_fvars := F.parameterTail_params
    parameterTarget := F.parameterTarget
    parameterTranslation := F.parameterTranslation
    parameterType := F.parameterType
    parameterTranslation₀ := F.parameterTranslation₀
    fieldOpening := F.fieldOpening
    fieldParameterUp := F.fieldParameterUp
    fieldCheck := F.fieldCheck
    context_venv := F.terminalExtension.venv_eq.symm
    validStats := HvalidStats
    ownerIdx := ownerIdx
    owner_lt := Hvalidated.target_lt
    expected_owner_lt := hexpectedLt
    expected_target_valid := hexpectedValid
    targetTarget := F.terminalTarget
    target_not_forall := hterminalNotForall
    target_translation := F.terminalTranslation
    target_type := F.terminalType
    fieldTargetDefEq := F.fieldTargetDefEq
    constructorTarget := F.constructorApplication.introTarget
    constructor_translation := by
      simpa [mkAppN, F.traversal_constructor, F.traversal_stats] using
        F.constructorApplication.intro
    constructor_typing := F.constructorApplication.typing
    target_valid := htargetValid
    validated := Hvalidated
    fields := fields
    selection := Hselection
    decisionPositions := F.traversal.recursivePositions
    decisions := by
      simpa only [hroot, htarget, H.allArgs_eq, H.recursiveArgs_eq,
        F.traversal_stats, F.traversal_fields,
        F.traversal_recursiveFields] using F.traversal.decisions
    calls := by
      rw [F.fieldOpening.fvars_eq_bound
        F.fieldsRecent.toFVarArrayAfter.toFVarArrayIn]
      exact Hstaged }
  rcases C.toTyping H.certificate hroot htarget H.allArgs_eq
      H.recursiveArgs_eq H.recursiveResults_eq binding HmotiveTelescope
      Hlookup with
    ⟨Ssemantic, binding', HmotiveTelescope', Hlookup', hdecisionPositions,
      hsemanticParameterDecls, hsemanticContext, hsemanticFieldFVars,
      ⟨HproducerCalls⟩⟩
  have hfieldBinders : S.fields_bound.fvars =
      H.certificate.all_args_bound.fvars := by
    rw [← S.fields_bound.exprArrayFVarIds,
      ← H.certificate.all_args_bound.exprArrayFVarIds, H.allArgs_eq]
  have Hreplay : ∀ j (hj : j < H.certificate.recursiveArgs.size),
      Nonempty (RecursorRuleSyntax.CallAt
        (recInfos := recInfos) H.certificate Ssemantic S j hj) := by
    intro j hj
    have hjSource : j < S.recursiveFields.size := by
      rw [← H.recursiveArgs_eq]
      exact hj
    have hjHypotheses : j < S.hypotheses.size := by
      rw [S.hypotheses_size]
      exact hjSource
    rcases HcallOrigins.entry j hjHypotheses with
      ⟨sourceOriginRoot, sourceType, O, D, _HoriginRoot,
        hsourceDeclaration, hcall⟩
    rcases Hcalls.entry j hjHypotheses with
      ⟨originRoot, Rorigin, priorHypotheses, Hrecent,
        hpriorSize, hchkO, ⟨HcallSemantic⟩⟩
    rcases HcallSemantic.semantic indTypes
        (recInfos.flatMap (·.minors)) lvls with
      ⟨Scall, hscope, Hmotive, hsemanticReplay⟩
    have hsourceOwner : O.ownerIdx < semanticOrigins.recInfos.size := by
      have hcallOwner : O.ownerIdx = B.recursiveCalls[j]!.targetTypeIdx := by
        rw [hcall]
      rw [hcallOwner]
      have := HcallSemantic.owner_lt
      have hsizes : semanticOrigins.recInfos.size = recInfos.size := by
        simpa using congrArg Array.size hsemanticMotives
      rw [hsizes]
      simpa using this
    have hsourceReplay := O.replayTrace_eq_template
      B.recursiveCalls[j]! hcall hsourceOwner S.fields_bound.fvars
    have hsemanticReplay' := hsemanticReplay
      H.certificate.all_args_bound.fvars
    rw [hsemanticMotives] at hsourceReplay
    have hblueprintBinders :
        recCallTemplateShape B.recursiveCalls[j]!
            (recInfos.map (·.motive)) S.fields_bound.fvars =
          recCallTemplateShape B.recursiveCalls[j]!
            (recInfos.map (·.motive))
              H.certificate.all_args_bound.fvars := by
      rw [hfieldBinders]
    have hreplay : O.replayTrace S.fields_bound.fvars =
        Scall.generated.replayTrace H.certificate.all_args_bound.fvars :=
      hsourceReplay.trans (hblueprintBinders.trans hsemanticReplay'.symm)
    have hjCalls : j < B.recursiveCalls.size := by
      rw [HcallOrigins.size_eq]
      exact hjHypotheses
    have hbuilt :
        (B.recursiveCalls.map fun call => call.instantiate indTypes stats
          (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls)[j]! =
        B.recursiveCalls[j]!.instantiate indTypes stats
          (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls := by
      rw [getElem!_pos _ j (by simpa using hjCalls)]
      simp [getElem!_pos B.recursiveCalls j hjCalls]
    have HpackageSource :
        ∃ Scall' : TypedRecursiveCall indTypes stats
            (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
            Rorigin decl (depth + j) S.recursiveFields[j]!
              (B.recursiveCalls[j]!.instantiate indTypes stats
                (recInfos.map (·.motive))
                (recInfos.flatMap (·.minors)) lvls),
          Scall'.rootScope = (fun fv =>
              fv ∈ F.fieldsRecent.fvars ∨
                fv ∈ ExprArrayFVarIds stats.params) ∧
          Nonempty Scall'.MotiveApplication ∧
          O.replayTrace S.fields_bound.fvars =
            Scall'.generated.replayTrace
              H.certificate.all_args_bound.fvars :=
      ⟨Scall, hscope, Hmotive, hreplay⟩
    have harg : S.recursiveFields[j]! =
        H.certificate.recursiveArgs[j] := by
      simpa [H.recursiveArgs_eq] using
        getElem!_pos S.recursiveFields j hjSource
    have hresult :
        B.recursiveCalls[j]!.instantiate indTypes stats
            (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls =
          H.certificate.recursiveResults[j]! := by
      rw [H.recursiveResults_eq, hbuilt]
    have hscopeFVars : F.fieldsRecent.fvars =
        Ssemantic.fieldOpening.fvars := hsemanticFieldFVars.symm
    have Hpackage :
        ∃ Scall' : TypedRecursiveCall indTypes stats
            (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
            Rorigin decl (depth + j) H.certificate.recursiveArgs[j]
              H.certificate.recursiveResults[j]!,
          Scall'.rootScope = (fun fv =>
              fv ∈ Ssemantic.fieldOpening.fvars ∨
                fv ∈ ExprArrayFVarIds stats.params) ∧
          Nonempty Scall'.MotiveApplication ∧
          O.replayTrace S.fields_bound.fvars =
            Scall'.generated.replayTrace
              H.certificate.all_args_bound.fvars := by
      rw [← harg, ← hresult, ← hscopeFVars]
      exact HpackageSource
    rcases Hpackage with ⟨Scall', hscope', Hmotive', hreplay'⟩
    refine ⟨{
      hypothesisOrigins := semanticOrigins
      hypothesisOrigins_eq := hsemanticOrigins
      sourceOriginRoot := sourceOriginRoot
      sourceType := sourceType
      sourceOrigin := O
      sourceDeclaration := D
      sourceDeclaration_type := hsourceDeclaration
      originRoot := originRoot
      originContext := Rorigin
      priorHypotheses := priorHypotheses
      originRecent := by
        have HrecentC : RecursorFVarSuffix C.context Rorigin
            priorHypotheses := Hrecent
        have HrecentCast : RecursorFVarSuffix
            (hroot.symm ▸ C.context) Rorigin priorHypotheses := by
          exact RecursorFVarSuffix.castRoot hroot.symm HrecentC
        rw [hsemanticContext]
        exact HrecentCast
      originCheck := by
        rw [hsemanticContext, RecursorContextWF.chk_cast]
        exact hchkO
      priorHypotheses_size := hpriorSize
      callDepth := depth + j
      semantic := Scall'
      root_scope := hscope'
      motiveApplication := Hmotive'
      replay := hreplay' }⟩
  let producer : H.certificate.MotiveAt Ssemantic recInfos
      elimLevel := {
    minorShape := S
    minorTraversal := F.traversal
    minorTraversal_eq := F.traversal_eq
    decisionPositions_eq := hdecisionPositions.symm
    calls := HproducerCalls
    replay := Hreplay
    binding := binding'
    telescope := HmotiveTelescope'
    motiveLookup := Hlookup' }
  exact ⟨Ssemantic, producer, rfl, hsemanticParameterDecls⟩

theorem TypedRecursorRules.ofEntriesWithProducer
    {ctors : List Constructor} {rules : List RecursorRule} {start : Nat}
    (hsize : ctors.length = rules.length)
    (H : ∀ i (hi : i < ctors.length),
      ∃ Hrule : RecursorRuleSyntax indTypes stats
          (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
          ctors[i] (start + i) rules[i],
        ∃ S : Hrule.Semantics Rroot decl ownerIdx,
          Nonempty (Hrule.MotiveAt S recInfos elimLevel)) :
    ∃ Hrules : TypedRecursorRules indTypes stats
        (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
        Rroot decl ownerIdx ctors start rules,
      Nonempty (Hrules.MotiveAt recInfos elimLevel) := by
  induction ctors generalizing rules start with
  | nil =>
    cases rules with
    | nil => exact ⟨.nil, ⟨.nil⟩⟩
    | cons rule rules => simp at hsize
  | cons ctor ctors ih =>
    cases rules with
    | nil => simp at hsize
    | cons rule rules =>
      rcases H 0 (by simp) with ⟨Hhead, Shead, HheadMotive⟩
      have htailSize : ctors.length = rules.length := by simpa using hsize
      rcases ih htailSize (fun i hi => by
        have Hentry := H (i + 1) (by simp; omega)
        have hoffset : start + (i + 1) = start + 1 + i := by omega
        rw [hoffset] at Hentry
        simpa using Hentry) with ⟨Htail, ⟨HtailMotive⟩⟩
      exact ⟨.cons Hhead ⟨Shead⟩ Htail,
        ⟨.cons Hhead Shead HheadMotive Htail HtailMotive⟩⟩

/-- Semantic owner row assembled from the rule templates and the
row of binder types produced by the same second-pass iteration. -/
theorem RuleTemplatesMatch.boundGeneratedRules
    {indTypes : Array InductiveType}
    {stats : AddInductive.InductiveStats}
    {recInfos : Array AddInductive.RecInfo}
    {c : AddInductive.Context}
    {Horigins : RecInfoBinderTypes c recInfos}
    (H : RuleTemplatesMatch stats recInfos Horigins)
    (Hsources : MinorsAndIndicesMatchSource stats indTypes Horigins)
    {recLparams : List Name} {R : RecursorContextWF c recLparams}
    (elimLevel : Level)
    (HsemanticOrigins : TypedRuleTemplates R decl stats
      recInfos elimLevel parameterDecls Horigins)
    (Hsemantics : TypedMinors R Horigins parameterDecls)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : FVarArrayIn c stats.params)
    (hnoalias : RecInfoBindings.NoAlias stats.params recInfos)
    (hsize : recInfos.size = indTypes.size)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (owner : Nat) (howner : owner < indTypes.size) :
    let rules := recInfos[owner]!.ruleTemplates.toList.map fun blueprint =>
      blueprint.instantiate indTypes stats (recInfos.map (·.motive))
        (recInfos.flatMap (·.minors))
        (AddInductive.getRecLevels elimLevel stats.levels) c.lctx
    ∃ Hrules : TypedRecursorRules indTypes stats
        (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
        (AddInductive.getRecLevels elimLevel stats.levels) R decl owner
        indTypes[owner]!.ctors (recursorMinorOffset indTypes owner) rules,
      Nonempty (Hrules.MotiveAt recInfos elimLevel) ∧
      ∀ localIndex (hlocal : localIndex < indTypes[owner]!.ctors.length)
          (hrule : localIndex < rules.length),
        ∃ Hrule : RecursorRuleSyntax indTypes stats
            (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
            (AddInductive.getRecLevels elimLevel stats.levels)
            indTypes[owner]!.ctors[localIndex]
            (recursorMinorOffset indTypes owner + localIndex)
            (rules[localIndex]'hrule),
          ∃ S : Hrule.Semantics R decl owner,
            Nonempty (Hrule.MinorAt S recInfos elimLevel
              Horigins owner localIndex) ∧
            S.parameterDecls = parameterDecls := by
  dsimp only
  have hownerRec : owner < recInfos.size := by omega
  have hrowSize := H.ownerRowSize hcounts owner hownerRec
  let rules := recInfos[owner]!.ruleTemplates.toList.map fun blueprint =>
    blueprint.instantiate indTypes stats (recInfos.map (·.motive))
      (recInfos.flatMap (·.minors))
      (AddInductive.getRecLevels elimLevel stats.levels) c.lctx
  have Hentry : ∀ localIndex
      (hlocal : localIndex < indTypes[owner]!.ctors.length)
      (hrule : localIndex < rules.length),
      ∃ Hrule : RecursorRuleSyntax indTypes stats
          (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
          (AddInductive.getRecLevels elimLevel stats.levels)
          indTypes[owner]!.ctors[localIndex]
          (recursorMinorOffset indTypes owner + localIndex)
          (rules[localIndex]'hrule),
        ∃ S : Hrule.Semantics R decl owner,
          Nonempty (Hrule.MinorAt S recInfos elimLevel
            Horigins owner localIndex) ∧
          S.parameterDecls = parameterDecls := by
    intro localIndex hlocal hrule
    have hshapeLocal : localIndex < Horigins.minorTypes[owner]!.size := by
      rw [← H.rows_size owner hownerRec, hrowSize]
      exact hlocal
    let S := Horigins.minorShapes owner hownerRec localIndex hshapeLocal
    let B := recInfos[owner]!.ruleTemplates[localIndex]!
    have Horigin : RuleTemplateMatchesMinor stats S
        recInfos[owner]!.minors[localIndex]! B :=
      H.entry owner hownerRec localIndex hshapeLocal
    have Hsource := Hsources.rows owner hownerRec howner localIndex hshapeLocal
    have hlocalMinor : localIndex < recInfos[owner]!.minors.size := by
      rw [← (Horigins.minors owner hownerRec).size_eq]
      exact hshapeLocal
    rcases Hsemantics owner hownerRec localIndex hshapeLocal with ⟨HSat⟩
    let HS := HSat.semantic
    have hminorEq := recInfoFlatMinorAtOffset recInfos indTypes hsize hcounts
      owner hownerRec localIndex hlocalMinor
    have hminorValid : recursorMinorOffset indTypes owner + localIndex <
        (recInfos.flatMap (·.minors)).size := by
      have htotal := mkRecInfos.flatMinors_size hsize hcounts
      have hroom := recursorMinorOffset_room indTypes owner howner
      have htotalList : (recInfos.flatMap (·.minors)).size =
          (indTypes.toList.flatMap (fun type => type.ctors)).length := by
        calc
          (recInfos.flatMap (·.minors)).size =
              (indTypes.flatMap fun type => type.ctors.toArray).size := htotal
          _ = (indTypes.toList.flatMap (fun type => type.ctors)).length := by
            simpa [ownedConstructors] using
              (ownedConstructors_length_eq_flattened_size indTypes).symm
      rw [htotalList]
      omega
    have hfieldsFresh : ∀ fv ∈
        HS.fieldsRecent.toFVarArrayAfter.toFVarArrayIn.fvars,
        fv ∉ (Hparams.fvars ++ Hbindings.motives.fvars) ++
          Hbindings.flatMinors.fvars := by
      intro fv hfv
      have hshapeFields :
          HS.fieldsRecent.toFVarArrayAfter.toFVarArrayIn.fvars =
            S.fields_bound.fvars :=
        HS.fieldsRecent.toFVarArrayAfter.toFVarArrayIn
          |>.exprArrayFVarIds.symm.trans S.fields_bound.exprArrayFVarIds
      rw [hshapeFields] at hfv
      have hfresh := H.fields_outer_fresh owner hownerRec localIndex
        hshapeLocal fv hfv
      simpa only [Hparams.exprArrayFVarIds,
        Hbindings.motives.exprArrayFVarIds,
        Hbindings.flatMinors.exprArrayFVarIds] using hfresh
    let T := Hsource.2.2.2.2.choose
    have htraversal : HS.traversal = T := by
      have hT := Hsource.2.2.2.2.choose_spec.1
      exact Option.some.inj (HS.traversal_eq.symm.trans hT)
    have hrecursive : HS.traversal.recursiveFields = S.recursiveFields := by
      rw [htraversal]
      exact Hsource.2.2.2.2.choose_spec.2.2.2.1
    rcases Horigin.boundGeneratedRuleOfSource HS
      Hsource.2.2.2.1 hrecursive indTypes
      (AddInductive.getRecLevels elimLevel stats.levels)
      (recursorMinorOffset indTypes owner + localIndex) Hparams Hbindings
      (Hbindings.outerNodup Hparams hnoalias) hminorValid hminorEq
      hfieldsFresh with ⟨Hrule⟩
    rcases HsemanticOrigins.entry owner hownerRec localIndex hshapeLocal with
      ⟨Hsemantic⟩
    rcases Hrule.typingOfProducer HS Hsemantic with
      ⟨HruleSemantic, HmotiveEvidence, hshapeEq,
        hsemanticParameterDecls⟩
    have hctor : indTypes[owner]!.ctors[localIndex] = S.constructor := by
      have hget := S.sourceConstructor
      rw [Hsource.2.1, Hsource.2.2.1] at hget
      have hlist : indTypes[owner]!.ctors[localIndex]? =
          some indTypes[owner]!.ctors[localIndex] :=
        List.getElem?_eq_getElem hlocal
      rw [hlist] at hget
      exact Option.some.inj hget
    have hblueLocal : localIndex <
        recInfos[owner]!.ruleTemplates.size := by
      rw [hrowSize]
      exact hlocal
    have hruleGet : (rules[localIndex]'hrule) =
        B.instantiate indTypes stats (recInfos.map (·.motive))
          (recInfos.flatMap (·.minors))
          (AddInductive.getRecLevels elimLevel stats.levels) c.lctx := by
      simp [rules, B, hblueLocal]
    rw [hctor, hruleGet]
    exact ⟨Hrule.certificate, HruleSemantic, ⟨{
      producer := HmotiveEvidence
      owner_lt := hownerRec
      local_lt := hshapeLocal
      shape_eq := hshapeEq }⟩, hsemanticParameterDecls⟩
  have hrulesSize : indTypes[owner]!.ctors.length = rules.length := by
    simpa [rules] using hrowSize.symm
  rcases TypedRecursorRules.ofEntriesWithProducer
      hrulesSize (fun localIndex hlocal => by
        have hrule : localIndex < rules.length := by omega
        rcases Hentry localIndex hlocal hrule with
          ⟨Hrule, S, ⟨Horigin⟩, _hparams⟩
        exact ⟨Hrule, S, ⟨Horigin.producer⟩⟩) with
    ⟨Hrules, Hmotive⟩
  exact ⟨Hrules, Hmotive, Hentry⟩

end VerifyInductive

end Lean4Lean
