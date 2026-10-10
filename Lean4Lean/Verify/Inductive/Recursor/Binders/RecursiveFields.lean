import Lean4Lean.Verify.Inductive.Constructor.PrefixUtilities
import Lean4Lean.Verify.Inductive.Recursor.Context.ParameterContext

/-! Recursive-field classification at the recursor universe arity: application
statistics under the recursor universes (`RecursorValidAppStatsWF`), the validated
recursive-field application (`RecursorValidatedIndAppAt`), and the field selections
and decisions of a constructor traversal (`RecursiveFieldSelectionsAt`,
`RecursorFieldDecisions`). -/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment
namespace VerifyInductive

/-- Application statistics interpreted under recursor universes.  Unlike
`ValidAppStatsWF`, this structure does not claim that the recursor universe
list has the declaration's arity: large elimination has one additional
parameter.  The declaration's constant-level arity remains recorded by `levels`,
while all cached executable parameters are translated in the actual recursor
context. -/
structure RecursorValidAppStatsWF
    (env : VEnv) (recLparams : List Name) (Δ : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (depth : Nat) : Prop where
  levels : stats.levels.length = decl.uvars
  consts : checkPositivityStep.IndConstArray stats.levels stats.indConsts
    (decl.types.map (·.name))
  indices : stats.nindices.toList = decl.types.map (·.numIndices)
  params : List.Forall₂ (TrExprS env recLparams Δ) stats.params.toList
    (decl.paramVars depth)
  paramFVars : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv

/-- Reinterpret complete application statistics after introducing the
optional fresh recursor universe parameter. -/
theorem checkPositivityStep.ValidAppStatsWF.toRecursorContext
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    let R := Hc.toAdmissibleRecursorContextWF Helim
    RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      R.mlctx.vlctx stats decl depth := by
  dsimp only
  cases elimLevel with
  | zero =>
    exact {
      levels := H.levels
      consts := H.consts
      indices := H.indices
      params := H.params
      paramFVars := H.paramFVars }
  | param fresh =>
    let shift := VLevel.prependShift c.lparams.length
    have hparamsShift : List.Forall₂
        (TrExprS Hc.venv (fresh :: c.lparams)
          (Hc.mlctx.vlctx.instL shift))
        stats.params.toList
        ((decl.paramVars depth).map fun target => target.instL shift) := by
      have go : ∀ {sources targets},
          List.Forall₂ (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx)
              sources targets →
          List.Forall₂ (TrExprS Hc.venv (fresh :: c.lparams)
              (Hc.mlctx.vlctx.instL shift))
            sources (targets.map fun target => target.instL shift) := by
        intro sources targets Htranslated
        induction Htranslated with
        | nil => exact .nil
        | cons hsource _ ih =>
          exact .cons
            (by simpa [shift] using
              (hsource.prependLevelParam Hc.checking.tr.wf
                Hc.mlctx_wf.tr.wf Helim)) ih
      exact go H.params
    have hparamsTarget :
        (decl.paramVars depth).map (fun target => target.instL shift) =
          decl.paramVars depth := by
      simp [VInductDecl.paramVars, VExpr.instL]
    rw [hparamsTarget] at hparamsShift
    exact {
      levels := H.levels
      consts := H.consts
      indices := H.indices
      params := by
        change List.Forall₂
          (TrExprS Hc.venv (fresh :: c.lparams)
            (Hc.mlctx.prependLevelParam c.lparams.length).vlctx)
          stats.params.toList (decl.paramVars depth)
        simpa only [TypeChecker.MLCtx.prependLevelParam_vlctx, shift]
          using hparamsShift
      paramFVars := H.paramFVars }
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- Restrict recursor application statistics to the exact cached-parameter
suffix, independently of all generated ambient frames. -/
theorem RecursorParameterContextSuffix.scopedStats
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : RecursorParameterContextSuffix R stats depth)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams R.mlctx.vlctx
      stats decl depth) :
    RecursorValidAppStatsWF R.venv recLparams H.parameterDecls
      stats decl 0 where
  levels := Hstats.levels
  consts := Hstats.consts
  indices := Hstats.indices
  params := by
    have hsize : stats.params.size = decl.nparams := by
      have hlength :=
        List.Forall₂.length_eq Hstats.params
      simpa [VInductDecl.paramVars] using hlength
    rw [← checkInductiveTypes.loopType.cachedParamVars_eq_paramVars decl,
      ← hsize]
    exact H.suffixParams
  paramFVars := Hstats.paramFVars

/-- Opening one index under recursor universes weakens every cached
parameter target by exactly one binder. -/
theorem RecursorValidAppStatsWF.withFVar
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (henv : env.WF)
    (hscope' : VLCtx.WF env recLparams.length
      ((some (fv, deps), .vlam fieldType) :: scope)) :
    RecursorValidAppStatsWF env recLparams
      ((some (fv, deps), .vlam fieldType) :: scope)
      stats decl (depth + 1) := by
  let W : VLCtx.FVLift scope
      ((some (fv, deps), .vlam fieldType) :: scope) 0 1 0 :=
    .skip_fvar _ _ .refl
  have hparams := checkPositivityStep.forall₂_map_right
    (f := fun target => target.liftN 1 0)
    (S := TrExprS env recLparams
      ((some (fv, deps), .vlam fieldType) :: scope))
    H.params fun h => h.weakFV henv.orderedStrong W hscope'
  exact {
    levels := H.levels
    consts := H.consts
    indices := H.indices
    params := by
      rw [← checkPositivityStep.VInductDecl.paramVars_liftN]
      exact hparams
    paramFVars := H.paramFVars }

theorem RecursorValidAppStatsWF.params_size
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth) :
    stats.params.size = decl.nparams := by
  have hlength := List.Forall₂.length_eq H.params
  simpa [VInductDecl.paramVars] using hlength

theorem RecursorValidAppStatsWF.types_size
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth) :
    stats.indConsts.size = decl.types.length := by
  rw [H.consts.exact]
  simp

theorem RecursorValidAppStatsWF.indConstAt
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (hi : i < decl.types.length) :
    stats.indConsts[i]? = some (.const decl.types[i].name stats.levels) := by
  rw [H.consts.exact]
  simp [hi]

theorem RecursorValidAppStatsWF.nindicesAt
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (hi : i < decl.types.length) :
    stats.nindices[i]? = some decl.types[i].numIndices := by
  rw [← Array.getElem?_toList, H.indices]
  simp [hi]

theorem RecursorValidAppStatsWF.paramAt
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (hi : i < stats.params.size) :
    ∃ param', (decl.paramVars depth)[i]? = some param' ∧
      TrExprS env recLparams scope stats.params[i] param' := by
  have hsource : stats.params.toList[i]? = some stats.params[i] := by
    simp [hi]
  have htarget : ∃ param', (decl.paramVars depth)[i]? = some param' := by
    have hi' : i < (decl.paramVars depth).length := by
      have hlength := List.Forall₂.length_eq H.params
      simpa using hlength ▸ hi
    exact ⟨(decl.paramVars depth)[i], List.getElem?_eq_getElem hi'⟩
  rcases htarget with ⟨param', htarget⟩
  exact ⟨param', htarget,
    checkPositivityStep.forall₂_get?_eq_some H.params hsource htarget⟩

theorem RecursorValidAppStatsWF.paramFVarAt
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (hi : i < stats.params.size) :
    ∃ fv, stats.params[i] = .fvar fv := by
  exact H.paramFVars _ (by simp)

/-- A validated cached parameter still translates to the matching abstract
parameter after the recursor universe list has been extended.  The argument
uses no equality between the recursor universe arity and `decl.uvars`. -/
theorem RecursorValidAppStatsWF.translatedParam
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true)
    (hargs : List.Forall₂ (TrExprS env recLparams scope)
      type.getAppArgsList args')
    (hj : j < stats.params.size) :
    args'[j]? = (decl.paramVars depth)[j]? := by
  have harity := checkPositivityStep.isValidIndAppIdx.arity hvalid
  have hjArgs : j < type.getAppArgs.size := by omega
  have hsource : type.getAppArgsList[j]? = some type.getAppArgs[j] := by
    rw [← Expr.getAppArgs_toList]
    simp [hjArgs]
  have hlength := List.Forall₂.length_eq hargs
  have hjArgs' : j < args'.length := by
    rw [← hlength, ← Expr.getAppArgs_toList]
    simp [hjArgs]
  have htarget : args'[j]? = some args'[j] :=
    List.getElem?_eq_getElem hjArgs'
  have harg := checkPositivityStep.forall₂_get?_eq_some
    hargs hsource htarget
  rcases H.paramAt hj with ⟨param', hparamTarget, hparam⟩
  rcases H.paramFVarAt hj with ⟨fv, hfv⟩
  have heq := checkPositivityStep.isValidIndAppIdx.param hvalid hj
  rw [hfv] at hparam heq
  have habstract := checkPositivityStep.TrExprS.eqv_fvar_target
    hparam harg heq
  rw [htarget, hparamTarget, ← habstract]

/-- The executable parameter-prefix comparison is structural once the cached
parameters are known to be free variables.  This turns the kernel's
annotation-insensitive `Expr.eqv` guard into the exact application split used
by translation inversion below. -/
theorem RecursorValidAppStatsWF.sourceParameterPrefix
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true) :
    type.getAppArgsList.take stats.params.size = stats.params.toList := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_take]
  by_cases hj : j < stats.params.size
  · rw [if_pos hj]
    have harity := checkPositivityStep.isValidIndAppIdx.arity hvalid
    have hjArgs : j < type.getAppArgs.size := by omega
    have hsource : type.getAppArgsList[j]? =
        some type.getAppArgs[j] := by
      rw [← Expr.getAppArgs_toList]
      simp [hjArgs]
    have hcached : stats.params.toList[j]? = some stats.params[j] := by
      simp [hj]
    rcases H.paramFVarAt hj with ⟨fv, hfv⟩
    have hargEq := checkPositivityStep.isValidIndAppIdx.param hvalid hj
    rw [hfv] at hargEq
    have harg : type.getAppArgs[j] = .fvar fv :=
      Expr.eqv_fvar_eq hargEq
    rw [hsource, hcached, harg, hfv]
  · rw [if_neg hj]
    simp [hj]

theorem RecursorValidAppStatsWF.translatedIndexNoOccurrence
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true)
    (hargs : List.Forall₂ (TrExprS env recLparams scope)
      type.getAppArgsList args')
    (hlit : checkPositivityStep.AvailableLiteralDisjoint env stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) scope)
    (hlower : stats.params.size ≤ j) (hupper : j < args'.length) :
    args'[j].SourceConstFree (decl.types.map (·.name)) := by
  have hlength := List.Forall₂.length_eq hargs
  have hjArgs : j < type.getAppArgs.size := by
    have hsize : type.getAppArgs.size = type.getAppArgsList.length := by
      rw [← Expr.getAppArgs_toList]
      simp
    rw [hsize, hlength]
    exact hupper
  have hsource : type.getAppArgsList[j]? = some type.getAppArgs[j] := by
    rw [← Expr.getAppArgs_toList]
    simp [hjArgs]
  have htarget : args'[j]? = some args'[j] :=
    List.getElem?_eq_getElem hupper
  have harg := checkPositivityStep.forall₂_get?_eq_some
    hargs hsource htarget
  have hno := checkPositivityStep.isValidIndAppIdx.indexNoOccurrence
    hvalid hlower hjArgs
  exact checkPositivityStep.TrExprS.noIndOccAvailable H.consts.names hlit hctx
    harg hno

/-- Recursor-universe form of application validation.  The executable
classifier depends on the declaration's constant levels, while the
translated expression may live under the extra large-elimination universe. -/
theorem RecursorValidAppStatsWF.validIndAppAtTarget
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (htr : TrExprS env recLparams scope type type')
    (hvalid : AddInductive.isValidIndApp? stats type = some typeIdx)
    (hi : typeIdx < decl.types.length)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint env stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) scope) :
    decl.ValidIndAppAt (some (decl.types[typeIdx]'hi).name) depth type' := by
  rcases checkPositivityStep.isValidIndApp?_some hvalid with
    ⟨hsourceBound, hvalidIdx⟩
  have hconst := H.indConstAt hi
  have hhead := checkPositivityStep.isValidIndAppIdx.constHead
    hvalidIdx hconst
  rcases checkPositivityStep.TrExprS.constAppSpine htr hhead with
    ⟨levels', args', hspine, hlevels, hargs⟩
  have hlevelLen : levels'.length = decl.uvars := by
    have hlength := checkPositivityStep.List.mapM_some_length hlevels
    exact hlength.symm.trans H.levels
  have hargsLen : args'.length =
      decl.nparams + decl.types[typeIdx].numIndices := by
    have htranslated := List.Forall₂.length_eq hargs
    have hsource : type.getAppArgsList.length = type.getAppArgs.size := by
      rw [← Expr.getAppArgs_toList]
      simp
    have harity := checkPositivityStep.isValidIndAppIdx.arity hvalidIdx
    have hnindices : stats.nindices[typeIdx]! =
        decl.types[typeIdx].numIndices := by
      simp [Array.getElem!_eq_getD, H.nindicesAt hi]
    have hparamsSize := H.params_size
    omega
  have hparams : args'.take decl.nparams = decl.paramVars depth := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_take]
    by_cases hj : j < decl.nparams
    · rw [if_pos hj]
      apply H.translatedParam hvalidIdx hargs
      rw [H.params_size]
      exact hj
    · rw [if_neg hj]
      simp [VInductDecl.paramVars, hj]
  rw [VInductDecl.ValidIndAppAt, hspine]
  refine ⟨decl.types[typeIdx], List.getElem_mem hi, Or.inr rfl,
    levels', rfl, hlevelLen, hargsLen, hparams, ?_⟩
  intro arg harg
  rcases List.mem_drop_iff_getElem.mp harg with ⟨j, hj, hargEq⟩
  subst arg
  exact H.translatedIndexNoOccurrence (j := decl.nparams + j)
    hvalidIdx hargs hlit hctx
    (by rw [H.params_size]; omega) (by simpa [Nat.add_comm] using hj)

/-- The executable argument suffix after the parameters (the indices to which the
motive is applied) translates exactly to the abstract index suffix of a validated mutual-family application. -/
theorem RecursorValidAppStatsWF.translatedIndices
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (htr : TrExprS env recLparams scope type type')
    (hvalid : AddInductive.isValidIndApp? stats type = some typeIdx)
    (hi : typeIdx < decl.types.length) :
    ∃ levels' params' indices',
      type'.getAppFnArgs =
        (.const (decl.types[typeIdx]'hi).name levels', params' ++ indices') ∧
      params' = decl.paramVars depth ∧
      indices'.length = (decl.types[typeIdx]'hi).numIndices ∧
      List.Forall₂ (TrExprS env recLparams scope)
        (type.getAppArgs[stats.params.size:]).toList indices' ∧
      TrExprS env recLparams scope
        (mkAppN stats.indConsts[typeIdx]! stats.params)
        (VExpr.mkApps
          (.const (decl.types[typeIdx]'hi).name levels') params') := by
  rcases checkPositivityStep.isValidIndApp?_some hvalid with
    ⟨_sourceBound, hvalidIdx⟩
  have hhead := checkPositivityStep.isValidIndAppIdx.constHead
    hvalidIdx (H.indConstAt hi)
  rcases checkPositivityStep.TrExprS.constAppSpine htr hhead with
    ⟨levels', args', hspine, _hlevels, hargs⟩
  let params' := args'.take decl.nparams
  let indices' := args'.drop decl.nparams
  have hsplit : args' = params' ++ indices' := by
    exact (List.take_append_drop decl.nparams args').symm
  have hparams : params' = decl.paramVars depth := by
    dsimp only [params']
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_take]
    by_cases hj : j < decl.nparams
    · rw [if_pos hj]
      apply H.translatedParam hvalidIdx hargs
      rw [H.params_size]
      exact hj
    · rw [if_neg hj]
      simp [VInductDecl.paramVars, hj]
  have hindicesLength : indices'.length =
      (decl.types[typeIdx]'hi).numIndices := by
    have harity := checkPositivityStep.isValidIndAppIdx.arity hvalidIdx
    have hnindices : stats.nindices[typeIdx]! =
        (decl.types[typeIdx]'hi).numIndices := by
      simp [Array.getElem!_eq_getD, H.nindicesAt hi]
    have hargsLength := List.Forall₂.length_eq hargs
    have hsourceLength : type.getAppArgsList.length =
        type.getAppArgs.size := by
      rw [← Expr.getAppArgs_toList]
      simp
    have hargsLen : args'.length =
        stats.params.size + stats.nindices[typeIdx]! := by
      omega
    dsimp only [indices']
    rw [List.length_drop, hargsLen, H.params_size, hnindices]
    omega
  have hindicesTr : List.Forall₂ (TrExprS env recLparams scope)
      (type.getAppArgs[stats.params.size:]).toList indices' := by
    have hdrop := List.forall₂_drop
      hargs stats.params.size
    have hparamsSize := H.params_size
    rw [hparamsSize] at hdrop ⊢
    have hsuffix : (type.getAppArgs[decl.nparams:]).toList =
        type.getAppArgs.toList.drop decl.nparams := by
      rw [List.drop_eq_drop_min]
      simp only [Subarray.toList_eq, Array.array_toSubarray,
        Array.start_toSubarray, Array.stop_toSubarray, Nat.min_self,
        Array.toList_extract, List.extract_eq_take_drop,
        Array.length_toList]
      apply List.take_of_length_le
      simp
    rw [hsuffix]
    simpa only [Expr.getAppArgs_toList] using hdrop
  have hconstSource : stats.indConsts[typeIdx]! =
      .const (decl.types[typeIdx]'hi).name stats.levels := by
    simp [Array.getElem!_eq_getD, H.indConstAt hi]
  have hsourceHead : type.getAppFn = stats.indConsts[typeIdx]! := by
    rw [hhead, hconstSource]
  have hsourcePrefix := H.sourceParameterPrefix hvalidIdx
  have hsourceSplit : type = Expr.mkAppList
      (mkAppN stats.indConsts[typeIdx]! stats.params)
      (type.getAppArgsList.drop stats.params.size) := by
    calc
      type = Expr.mkAppList type.getAppFn type.getAppArgsList :=
        (Expr.mkAppList_getAppArgsList type).symm
      _ = Expr.mkAppList type.getAppFn
          (type.getAppArgsList.take stats.params.size ++
            type.getAppArgsList.drop stats.params.size) := by
        rw [List.take_append_drop]
      _ = Expr.mkAppList
          (Expr.mkAppList type.getAppFn
            (type.getAppArgsList.take stats.params.size))
          (type.getAppArgsList.drop stats.params.size) := by
        rw [Expr.mkAppList_append]
      _ = Expr.mkAppList
          (mkAppN stats.indConsts[typeIdx]! stats.params)
          (type.getAppArgsList.drop stats.params.size) := by
        rw [hsourceHead, hsourcePrefix, Expr.mkAppN_eq_mkAppList]
  have hsplitTr : TrExprS env recLparams scope
      (Expr.mkAppList (mkAppN stats.indConsts[typeIdx]! stats.params)
        (type.getAppArgsList.drop stats.params.size)) type' := by
    rwa [← hsourceSplit]
  rcases checkPositivityStep.TrExprS.mkAppList_inv hsplitTr with
    ⟨familyTarget, _suffixTargets, hfamilyTr, _hsuffixTr, _hout⟩
  have hsourceFamilyHead :
      (mkAppN stats.indConsts[typeIdx]! stats.params).getAppFn =
        .const (decl.types[typeIdx]'hi).name stats.levels := by
    rw [Expr.getAppFn_mkAppN, hconstSource]
    rfl
  rcases checkPositivityStep.TrExprS.constAppSpine hfamilyTr
      hsourceFamilyHead with
    ⟨familyLevels, familyParams, hfamilySpine, hfamilyLevels,
      hfamilyParams⟩
  have hfamilyParams' : List.Forall₂ (TrExprS env recLparams scope)
      stats.params.toList familyParams := by
    simpa [Expr.getAppArgsList_mkAppN, hconstSource,
      Expr.getAppArgsList_const] using hfamilyParams
  have hfamilyParamsEq : familyParams = decl.paramVars depth := by
    exact List.Forall₂.targets_eq_of_unique hfamilyParams' H.params
  have hfamilyLevelsEq : familyLevels = levels' := by
    exact Option.some.inj (hfamilyLevels.symm.trans _hlevels)
  have hfamilyTargetEq : familyTarget = VExpr.mkApps
      (.const (decl.types[typeIdx]'hi).name levels') params' := by
    have hrebuild := VExpr.mkApps_getAppFnArgs familyTarget
    rw [hfamilySpine] at hrebuild
    rw [← hrebuild, hfamilyLevelsEq, hfamilyParamsEq, hparams]
  refine ⟨levels', params', indices', ?_, hparams, hindicesLength,
    hindicesTr, ?_⟩
  · simpa [hsplit] using hspine
  · rwa [hfamilyTargetEq] at hfamilyTr

/-- The result of the recursive-field validation branch: the abstract
application of the target family together with the executable/abstract index
correspondence used by the motive. -/
structure RecursorValidatedIndAppAt
    (env : VEnv) (recLparams : List Name) (scope : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (depth : Nat) (type : Expr) (type' : VExpr) (target : Nat) : Prop where
  target_lt : target < decl.types.length
  owner_valid : AddInductive.isValidIndApp? stats type = some target
  application : decl.ValidIndAppAt
    (some (decl.types[target]'target_lt).name) depth type'
  indices_payload : ∃ levels params indices,
    type'.getAppFnArgs =
      (.const (decl.types[target]'target_lt).name levels, params ++ indices) ∧
    params = decl.paramVars depth ∧
    indices.length = (decl.types[target]'target_lt).numIndices ∧
    List.Forall₂ (TrExprS env recLparams scope)
      (type.getAppArgs[stats.params.size:]).toList indices ∧
    TrExprS env recLparams scope
      (mkAppN stats.indConsts[target]! stats.params)
      (VExpr.mkApps
        (.const (decl.types[target]'target_lt).name levels) params)

theorem RecursorValidAppStatsWF.validatedIndAppAt
    (H : RecursorValidAppStatsWF env recLparams scope stats decl depth)
    (htr : TrExprS env recLparams scope type type')
    (hvalid : AddInductive.isValidIndApp? stats type = some target)
    (htarget : target < decl.types.length)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint env stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) scope) :
    RecursorValidatedIndAppAt env recLparams scope stats decl depth
      type type' target := by
  exact {
    target_lt := htarget
    owner_valid := hvalid
    application := H.validIndAppAtTarget htr hvalid htarget hlit hctx
    indices_payload := H.translatedIndices htr hvalid htarget }

namespace isRecArg.loop

/-- The recursive-field classifier remains sound after generated recursor
frames rebase the abstract universe list. -/
theorem refinesRecursor
    {decl : VInductDecl} {depth : Nat} {type' : VExpr}
    {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) R.mlctx.vlctx)
    (htype : TrExpr R.venv recLparams R.mlctx.vlctx type type')
    (htype₀ : TrExprS R.venv recLparams R.chk.vlctx type type₀) :
    (AddInductive.isRecArg.loop stats type fuel c).WF
      (fun result => ∀ target, result = some target →
        ∃ htarget : target < decl.types.length,
        decl.RecursiveArgAtTarget R.venv recLparams.length
          (decl.types[target]'htarget).name
          R.mlctx.vlctx.toCtx depth type') := by
  induction fuel generalizing c type type' type₀ depth with
  | zero =>
    intro _ h
    simp [AddInductive.isRecArg.loop] at h
  | succ fuel ih =>
    rcases htype with ⟨sourceSyntax, hsource, hsourceEq⟩
    rw [AddInductive.isRecArg.loop]
    refine (whnfInRecursorContext.dualWF R hsource htype₀).bind
      fun normalized ⟨hnormalized, _, hnormalized₀⟩ => ?_
    rcases hnormalized.2 with ⟨exposed, hexposed, hexposedEq⟩
    have hsourceExposed :=
      (hexposedEq.trans R.checking.tr.wf R.mlctx_wf.tr.wf.toCtx
        hsourceEq).symm
    rcases hsourceExposed with ⟨exprType, hsourceExposed⟩
    by_cases hforall : ∃ name dom body bi,
        normalized = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      cases hexposed with
      | forallE hdomType _ hdom hbody =>
        rcases hconsume c recLparams R hdom hdomType with
          ⟨consumedDom', Hdom⟩
        rcases Hdom.body R hbody with ⟨body'', hbody'', hbodyEq⟩
        rcases TrExpr.forallE_source hnormalized₀ with
          ⟨dom₀, bodyN₀, hdom₀, hbodyN₀, hdom₀Type, _, _⟩
        rcases hconsume _ recLparams R.atCheckLCtx hdom₀ hdom₀Type with
          ⟨consumedDom₀, Hdom₀⟩
        rcases Hdom₀.body R.atCheckLCtx hbodyN₀ with ⟨body₀'', hbody₀'', _⟩
        refine withCheckedLocalDecl.recursorWF (name := name) (bi := bi)
          (Q := fun result => ∀ target, result = some target →
            ∃ htarget : target < decl.types.length,
            decl.RecursiveArgAtTarget R.venv recLparams.length
              (decl.types[target]'htarget).name
              R.mlctx.vlctx.toCtx depth type')
          R Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType ?_
        let R' := R.withCheckedLocalDecl (name := name) (bi := bi)
          Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType
        have hopened := R.instantiateFresh (name := name) (bi := bi)
          Hdom.unannotated Hdom.isType hbody''
        have hopened₀ := R.atCheckLCtx.instantiateFresh (name := name) (bi := bi)
          Hdom₀.unannotated Hdom₀.isType hbody₀''
        have Hstats' := Hstats.withFVar R'.checking.tr.wf
          R'.mlctx_wf.tr.wf
        have hctx' : checkPositivityStep.VLCtx.NoIndConsts
            (decl.types.map (·.name)) R'.mlctx.vlctx := by
          apply checkPositivityStep.VLCtx.NoIndConsts.cons hctx
          rfl
        have Hrec := ih R' Hstats' hlit hctx'
          (hopened.trExpr R'.checking.tr.wf R'.mlctx_wf.tr.wf) hopened₀
        exact Hrec.mono fun result hrec target htarget => by
          rcases hrec target htarget with ⟨htarget, hrecursive⟩
          rcases Hdom.source_defeq with ⟨domLevel, hdomEq⟩
          rcases hbodyEq with ⟨bodyType, hbodyEq⟩
          exact ⟨htarget, .forallE
            (by simpa [Hstats.levels] using hsourceExposed)
            (by simpa [Hstats.levels] using hdomEq)
            (by simpa [Hstats.levels] using hbodyEq)
            hrecursive⟩
    · cases normalized <;> try { simp at hforall }
      all_goals
        change (Except.ok (AddInductive.isValidIndApp? stats _)).WF _
        exact Except.WF.pure fun target hvalid => by
          rcases checkPositivityStep.isValidIndApp?_some hvalid with
            ⟨htargetLt, _⟩
          have htargetDecl : target < decl.types.length := by
            rw [← Hstats.types_size]
            exact htargetLt
          refine ⟨htargetDecl, .direct
            (by simpa [Hstats.levels] using hsourceExposed)
            (Hstats.validIndAppAtTarget hexposed hvalid htargetDecl
              hlit hctx)⟩

end isRecArg.loop

theorem isRecArg.refinesRecursor
    {decl : VInductDecl} {depth : Nat} {type' : VExpr}
    {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) R.mlctx.vlctx)
    (htype : TrExpr R.venv recLparams R.mlctx.vlctx type type')
    (htype₀ : TrExprS R.venv recLparams R.chk.vlctx type type₀) :
    (AddInductive.isRecArg stats type c).WF
      (fun result => ∀ target, result = some target →
        ∃ htarget : target < decl.types.length,
        decl.RecursiveArgAtTarget R.venv recLparams.length
          (decl.types[target]'htarget).name
          R.mlctx.vlctx.toCtx depth type') := by
  unfold AddInductive.isRecArg
  have hread : ((read : AddInductive.M AddInductive.Context) c).WF
      (fun c' => c' = c) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun _ h => ?_
  subst h
  exact isRecArg.loop.refinesRecursor R Hstats hconsume hlit hctx
    htype htype₀

/-- Recursive-domain metadata interpreted at an explicit universe arity.
This is the minor-pass analogue of `RecursiveFieldDomain`; it is needed
while large-elimination recursors are being built under their fresh leading
universe parameter. -/
structure RecursiveFieldDomainAt
    (env : VEnv) (decl : VInductDecl) (uvars : Nat) where
  fieldIndex : Nat
  ownerIdx : Nat
  owner_lt : ownerIdx < decl.types.length
  ctx : List VExpr
  depth : Nat
  domain : VExpr
  recursive : decl.RecursiveArgAtTarget env uvars
    (decl.types[ownerIdx]'owner_lt).name ctx depth domain

/-- Recursive-field selections along a constructor telescope, at the recursor
universe arity. -/
inductive RecursiveFieldSelectionsAt
    (env : VEnv) (decl : VInductDecl) (uvars : Nat) :
    Array Expr → Array Expr →
      List (RecursiveFieldDomainAt env decl uvars) → Prop
  | nil : RecursiveFieldSelectionsAt env decl uvars #[] #[] []
  | nonrecursive : RecursiveFieldSelectionsAt env decl uvars bu u fields →
      RecursiveFieldSelectionsAt env decl uvars (bu.push arg) u fields
  | recursive : RecursiveFieldSelectionsAt env decl uvars bu u fields →
      cert.fieldIndex = bu.size →
      RecursiveFieldSelectionsAt env decl uvars (bu.push arg) (u.push arg)
        (fields ++ [cert])

/-- The successful classifier decisions made while traversing constructor
fields.  Unlike `RecursiveFieldSelectionsAt`, this relation records the `none`
branches as well as the selected ordinals, so that two traversals of the same
telescope can be compared by an alpha-invariance theorem. -/
inductive RecursorFieldDecisions (stats : AddInductive.InductiveStats)
    (root : AddInductive.Context) (source : Expr) :
    AddInductive.Context → Expr → Array Expr → Array Expr →
      List Nat → Prop
  | nil : RecursorFieldDecisions stats root source root source #[] #[] []
  | nonrecursive :
      RecursorFieldDecisions stats root source c
        (.forallE name dom body bi) bu u positions →
      -- `isRecArg` runs in the checker context of the earlier fields.
      AddInductive.isRecArg stats dom { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
          checkLCtx := ctorFieldCheck c stats bu } = .ok none →
      RecursorFieldDecisions stats root source { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
          checkLCtx := (ctorFieldCheck c stats bu).mkLocalDecl ⟨c.ngen.curr⟩ name
            (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi }
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))
        (bu.push (.fvar ⟨c.ngen.curr⟩)) u positions
  | recursive :
      RecursorFieldDecisions stats root source c
        (.forallE name dom body bi) bu u positions →
      -- `isRecArg` runs in the checker context of the earlier fields.
      AddInductive.isRecArg stats dom { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
          checkLCtx := ctorFieldCheck c stats bu } = .ok (some target) →
      RecursorFieldDecisions stats root source { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
          checkLCtx := (ctorFieldCheck c stats bu).mkLocalDecl ⟨c.ngen.curr⟩ name
            (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi }
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))
        (bu.push (.fvar ⟨c.ngen.curr⟩))
        (u.push (.fvar ⟨c.ngen.curr⟩)) (positions ++ [bu.size])

theorem RecursorFieldDecisions.positions_length
    (H : RecursorFieldDecisions stats root source c t bu u positions) :
    positions.length = u.size := by
  induction H with
  | nil => rfl
  | nonrecursive _ _ ih => exact ih
  | recursive _ _ ih => simp [ih]

theorem RecursorFieldDecisions.positions_lt
    (H : RecursorFieldDecisions stats root source c t bu u positions) :
    ∀ position ∈ positions, position < bu.size := by
  intro position hposition
  induction H with
  | nil => simp at hposition
  | nonrecursive _ _ ih =>
    have := ih hposition
    simp only [Array.size_push]
    omega
  | recursive _ _ ih =>
    simp only [List.mem_append, List.mem_singleton] at hposition
    rcases hposition with hposition | rfl
    · have := ih hposition
      simp only [Array.size_push]
      omega
    · simp only [Array.size_push]
      omega

/-- The decision mask is not merely cardinality metadata: its `j`th ordinal
selects the exact `j`th member of the recursive-field array from the complete
field array.  This formulation is independent of the fresh identifiers used
by a particular traversal, so it is the pointwise companion of the
alpha-invariance comparison. -/
theorem RecursorFieldDecisions.selected_at
    (H : RecursorFieldDecisions stats root source c t bu u positions)
    (j : Nat) (hj : j < u.size) :
    positions[j]! < bu.size ∧ u[j]! = bu[positions[j]!]! := by
  induction H generalizing j with
  | nil => simp at hj
  | @nonrecursive c name dom body bi bu u positions Hdecision _ ih =>
      rcases ih j hj with ⟨hposition, hselected⟩
      have hposition' : positions[j]! < (bu.push
          (.fvar ⟨c.ngen.curr⟩)).size := by
        simp only [Array.size_push]
        omega
      refine ⟨hposition', ?_⟩
      rw [getElem!_pos u j hj] at hselected ⊢
      rw [getElem!_pos bu positions[j]! hposition] at hselected
      rw [getElem!_pos (bu.push (.fvar ⟨c.ngen.curr⟩))
        positions[j]! hposition']
      simpa only [Array.getElem_push_lt hposition] using hselected
  | @recursive c name dom body bi bu u positions target Hdecision _ ih =>
      by_cases hold : j < u.size
      · rcases ih j hold with ⟨hposition, hselected⟩
        have hpositionBound : j < positions.length := by
          rw [Hdecision.positions_length]
          exact hold
        have hpositionAppendBound : j <
            (positions ++ [bu.size]).length := by
          simp only [List.length_append, List.length_singleton]
          omega
        have hpositionValue : (positions ++ [bu.size])[j]! =
            positions[j]! := by
          rw [getElem!_pos (positions ++ [bu.size]) j
            hpositionAppendBound, getElem!_pos positions j hpositionBound]
          exact List.getElem_append_left hpositionBound
        have hposition' : (positions ++ [bu.size])[j]! <
            (bu.push (.fvar ⟨c.ngen.curr⟩)).size := by
          rw [hpositionValue]
          simp only [Array.size_push]
          omega
        refine ⟨hposition', ?_⟩
        rw [hpositionValue]
        rw [getElem!_pos (u.push (.fvar ⟨c.ngen.curr⟩)) j (by
          simp only [Array.size_push]
          omega)]
        rw [Array.getElem_push_lt hold]
        rw [getElem!_pos u j hold] at hselected
        rw [getElem!_pos bu positions[j]! hposition] at hselected
        rw [getElem!_pos (bu.push (.fvar ⟨c.ngen.curr⟩))
          positions[j]! (by simp only [Array.size_push]; omega)]
        simpa only [Array.getElem_push_lt hposition] using hselected
      · have hjEq : j = u.size := by
          simp only [Array.size_push] at hj
          omega
        subst j
        have hpositionBound : u.size <
            (positions ++ [bu.size]).length := by
          simp [Hdecision.positions_length]
        have hpositionValue : (positions ++ [bu.size])[u.size]! =
            bu.size := by
          simp [Hdecision.positions_length]
        rw [hpositionValue]
        simp

theorem RecursorFieldDecisions.positions_ordered
    (H : RecursorFieldDecisions stats root source c t bu u positions) :
    positions.Pairwise (· < ·) := by
  induction H with
  | nil => simp
  | nonrecursive _ _ ih => exact ih
  | recursive H _ ih =>
    rw [List.pairwise_append]
    refine ⟨ih, by simp, ?_⟩
    intro old hold _ hnew
    simp only [List.mem_singleton] at hnew
    subst hnew
    exact H.positions_lt old hold

theorem RecursiveFieldSelectionsAt.fields_length
    (H : RecursiveFieldSelectionsAt env decl uvars bu u fields) :
    fields.length = u.size := by
  induction H with
  | nil => rfl
  | nonrecursive _ ih => exact ih
  | recursive _ _ ih => simp [ih]

theorem RecursiveFieldSelectionsAt.positions_lt
    (H : RecursiveFieldSelectionsAt env decl uvars bu u fields) :
    ∀ cert ∈ fields, cert.fieldIndex < bu.size := by
  induction H with
  | nil => simp
  | @nonrecursive bu u fields arg _ ih =>
    intro cert hmem
    have := ih cert hmem
    simp only [Array.size_push]
    omega
  | @recursive bu u fields arg cert _ hindex ih =>
    intro old hmem
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl
    · have := ih old hmem
      simp only [Array.size_push]
      omega
    · simp only [Array.size_push, hindex]
      omega

/-- The selections at the recursor universe arity have the same pointwise alignment
between selected recursive fields and the complete constructor-field array
as its declaration-universe counterpart. -/
theorem RecursiveFieldSelectionsAt.arguments_at_positions
    (H : RecursiveFieldSelectionsAt env decl uvars bu u fields) :
    List.Forall₂ (fun cert arg =>
      ∃ h : cert.fieldIndex < bu.size, arg = bu[cert.fieldIndex]'h)
      fields u.toList := by
  induction H with
  | nil => exact .nil
  | @nonrecursive bu u fields arg H ih =>
    have lift : List.Forall₂ (fun cert selected =>
        ∃ h : cert.fieldIndex < (bu.push arg).size,
          selected = (bu.push arg)[cert.fieldIndex]'h)
        fields u.toList := by
      apply List.Forall₂.imp (R := fun cert selected =>
        ∃ h : cert.fieldIndex < bu.size,
          selected = bu[cert.fieldIndex]'h) (fun cert selected hhead => ?_) ih
      rcases hhead with ⟨hpos, heq⟩
      refine ⟨by simp; omega, ?_⟩
      rw [heq]
      exact (Array.getElem_push_lt hpos).symm
    exact lift
  | @recursive bu u fields arg cert H hindex ih =>
    have lift : List.Forall₂ (fun old selected =>
        ∃ h : old.fieldIndex < (bu.push arg).size,
          selected = (bu.push arg)[old.fieldIndex]'h)
        fields u.toList := by
      apply List.Forall₂.imp (R := fun old selected =>
        ∃ h : old.fieldIndex < bu.size,
          selected = bu[old.fieldIndex]'h) (fun old selected hhead => ?_) ih
      rcases hhead with ⟨hpos, heq⟩
      refine ⟨by simp; omega, ?_⟩
      rw [heq]
      exact (Array.getElem_push_lt hpos).symm
    rw [Array.toList_push]
    apply List.Forall₂.append' lift
    apply List.Forall₂.cons
    · refine ⟨by simp [hindex], ?_⟩
      simp [hindex]
    · exact .nil

/-- Specialize recursive-domain metadata at the recursor universe arity to the
declaration universe arity.  Zero is a valid specialization for every recursor universe;
the executable field selection is unchanged, while the abstract context
and domain are instantiated in lockstep. -/
def RecursiveFieldDomainAt.toSource
    (cert : RecursiveFieldDomainAt env decl uvars) :
    RecursiveFieldDomain env decl where
  fieldIndex := cert.fieldIndex
  ownerIdx := cert.ownerIdx
  owner_lt := cert.owner_lt
  ctx := cert.ctx.map (VExpr.instL (List.replicate uvars .zero))
  depth := cert.depth
  domain := cert.domain.instL (List.replicate uvars .zero)
  recursive := cert.recursive.instL (List.replicate uvars .zero)
    (by simp [VLevel.WF])

@[simp] theorem RecursiveFieldDomainAt.toSource_fieldIndex
    (cert : RecursiveFieldDomainAt env decl uvars) :
    cert.toSource.fieldIndex = cert.fieldIndex := rfl

/-- Field selection does not depend on the universe arity.  Specializing each
abstract domain therefore converts the minor-pass selections into the
declaration-universe selections `RecursiveFieldSelections` used by the iota
specification. -/
theorem RecursiveFieldSelectionsAt.toSource
    (H : RecursiveFieldSelectionsAt env decl uvars bu u fields) :
    RecursiveFieldSelections env decl bu u
      (fields.map RecursiveFieldDomainAt.toSource) := by
  induction H with
  | nil => exact .nil
  | nonrecursive _ ih => exact .nonrecursive ih
  | @recursive bu u fields arg cert H hindex ih =>
    simpa using RecursiveFieldSelections.recursive
      (cert := cert.toSource) ih hindex

end VerifyInductive
end Lean4Lean
