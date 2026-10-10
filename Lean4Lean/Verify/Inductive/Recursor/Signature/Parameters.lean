import Lean4Lean.Verify.Inductive.Recursor.Construction

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- Instantiating the identity universe substitution leaves a well-typed context unchanged. -/
theorem onCtx_isType_instL_id {env : VEnv} {Γ : List VExpr} (H : OnCtx Γ (env.IsType U)) :
    Γ.map (VExpr.instL (VLevel.params U)) = Γ := by
  have Hw := OnCtx.levelWF_of_isType H
  induction Γ with
  | nil => rfl
  | cons A Γ ih =>
    simp only [List.map_cons, Hw.2.instL_id]
    exact congrArg (List.cons A) (ih H.1 Hw.1)

theorem checkInductiveTypes.loopType.ParameterContextSuffix.recursorDomains
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : checkInductiveTypes.loopType.ParameterContextSuffix Hc stats depth)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    (H.toRecursorContext Helim).parameterDecls.toCtx =
      H.parameterDecls.toCtx.map (VExpr.instL (recursorDeclarationAbstractLevels c.lparams Helim)) := by
  have Hwf := (checkInductiveTypes.loopType.FrontScopeEmbedding.ofParameterSuffix Hc H).scopeWF Hc.checking.tr.wf
  have hid := onCtx_isType_instL_id Hwf.toCtx
  cases elimLevel with
  | zero => exact hid.symm
  | param fresh =>
    change (H.parameterDecls.instL (VLevel.prependShift c.lparams.length)).toCtx = _
    rw [VLCtx.instL_toCtx]
    rw [recursorDeclarationAbstractLevels]
    conv => lhs; rw [← hid]
    rw [List.map_map]
    apply congrArg (fun f => List.map f H.parameterDecls.toCtx)
    funext e
    exact VExpr.instL_instL
  | succ level | max left right | imax left right | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- The recursor parameter context is the source parameter scope instantiated at the
recursor's universe levels (`recursorDeclarationAbstractLevels`). -/
theorem RecursorConstruction.parameterDomains
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) :
    H.parameterSuffix.parameterDecls.toCtx.reverse =
      R.parameterScope.toCtx.reverse.map
        (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)) := by
  rw [H.parameterDecls,
    checkInductiveTypes.loopType.ParameterContextSuffix.recursorDomains,
    List.map_reverse]
  have hscope : R.recursorHeaders.parameterSuffix.parameterDecls = R.parameterScope :=
    R.recursorHeaders_parameterScope
  rw [hscope]

/-- The executable's closed parameter telescope (ending in `Prop`) translates, at the recursor's
universe parameters, to the source parameter scope instantiated at the recursor's universe
levels. -/
theorem RecursorConstruction.sourceParameterTranslation
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) :
    TrExprS R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
      (H.localContext.lctx.mkForall stats.params (.sort .zero))
      (VExpr.wrapForalls (R.parameterScope.toCtx.reverse.map
        (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
        (.sort .zero)) := by
  have Htr := H.parameterSuffix.closedSortTranslation
  rw [H.recursorEnv, H.recursorWF.lctx_eq, H.parameterDomains] at Htr
  exact Htr

theorem RecursorInput.sourceParameterContext
    (R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv) :
    sourceEnv.IsDefEqCtx decl.uvars [] R.params.reverse R.parameterScope.toCtx := by
  have Hctx := R.sourceStatsWF.paramsContext
  rw [R.sourceHeaderParams, R.sourceParameterScope,
    R.sourceContextVEnv, R.sourceStatsWF.uvars] at Hctx
  exact Hctx

end Lean4Lean.VerifyInductive
