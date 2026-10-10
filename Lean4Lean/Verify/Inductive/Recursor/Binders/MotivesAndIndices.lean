import Lean4Lean.Verify.Inductive.Recursor.Context.UniverseScope
import Lean4Lean.Verify.Typing.EnvironmentRestriction
import Lean4Lean.Verify.Inductive.Recursor.Binders.MotiveFrames

/-! Typing of the motive pass of `mkRecInfos` (`loopInd1`, `loopArgs1`): each family
header is normalized and its parameters and indices are opened under the recursor
universe list, against the checked header (`MotivePassHeaderAt`), and the
executable motive type is definitionally equal to the generated motive telescope.
Part of the recursor phase (section 3.2 of the design notes). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

namespace mkRecInfos.loopArgs1

/-- Abstract variables for indices kept in source binder order
inside a context that stores the most recently opened index first. -/
def indexBVarSpine (n : Nat) : List VExpr :=
  (List.range n).reverse.map .bvar

@[simp] theorem indexBVarSpine_zero : indexBVarSpine 0 = [] := rfl

@[simp] theorem indexBVarSpine_succ (n : Nat) :
    (indexBVarSpine n).map (fun target => target.liftN 1 0) ++
      [.bvar 0] = indexBVarSpine (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show indexBVarSpine (n + 1) =
        .bvar n :: indexBVarSpine n by
      simp [indexBVarSpine, List.range_succ]]
    simp only [List.map_cons, VExpr.liftN,
      List.cons_append]
    rw [ih]
    simp [indexBVarSpine, List.range_succ]

/-- Common parameters beneath `n` index binders followed by those index
variables are exactly the bvar spine of the whole header. -/
theorem VInductDecl.paramVars_append_indexBVarSpine
    (decl : VInductDecl) (n : Nat) :
    decl.paramVars n ++ indexBVarSpine n =
      indexBVarSpine (decl.nparams + n) := by
  unfold VInductDecl.paramVars indexBVarSpine
  rw [Nat.add_comm decl.nparams n, List.range_add,
    List.reverse_append, List.map_append]
  simp [Function.comp_def]

/-- Abstract header selected by the recursor universe policy, factored out
so that the header phase can record a dependency fact for the
small- or large-elimination translation. -/
def recursorTargetSkeletonOf
    (target : VInductiveType) (lparams : List Name) (elimLevel : Level)
    (Helim : AddInductive.AdmissibleElimLevel lparams elimLevel) :
    VInductiveTypeSkeleton :=
  match elimLevel with
  | .zero => target.toSkeleton
  | .param _ =>
    { target.toSkeleton with
      type := target.type.instL (VLevel.prependShift lparams.length) }
  | .succ _ | .max _ _ | .imax _ _ | .mvar _ => False.elim Helim

@[simp] theorem recursorTargetSkeletonOf_zero
    (target : VInductiveType) (lparams : List Name)
    (Helim : AddInductive.AdmissibleElimLevel lparams .zero) :
    recursorTargetSkeletonOf target lparams .zero Helim =
      target.toSkeleton := rfl

@[simp] theorem recursorTargetSkeletonOf_param
    (target : VInductiveType) (lparams : List Name) (fresh : Name)
    (Helim : AddInductive.AdmissibleElimLevel lparams (.param fresh)) :
    recursorTargetSkeletonOf target lparams (.param fresh) Helim =
      { target.toSkeleton with
        type := target.type.instL (VLevel.prependShift lparams.length) } := rfl

/-- All checked inputs needed to open one source family
header during recursor construction.  The family index is part of the
structure, so parameter/index arities cannot be borrowed from another member
of a mutual block. -/
structure MotivePassHeaderAt
    (Hc : ContextWF c) (stats : AddInductive.InductiveStats)
    (decl : VInductDecl) (depth : Nat) (source : InductiveType)
    (familyIdx : Nat) where
  target : VInductiveType
  targetAt : decl.types[familyIdx]? = some target
  checked : checkInductiveTypes.loopInd.HeaderStatsWF
    Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth
  sourceTranslation : TrSourceConst Hc.venv c.lparams source.name
    source.type target.toVConstVal
  /-- The header translation was produced before this declaration's own
  constants were installed.  Recording this fact lets
  nested restoration transport only the index prefix without asserting
  a false global preservation theorem. -/
  sourceTranslationUses : sourceTranslation.type.Avoids
    (fun name => name ∈ decl.sourceNames)
  /-- The same restriction after applying the
  recursor universe policy.  This is recorded at formation time, before the
  installed block can become an apparent dependency. -/
  recursorSourceTranslationRestricted : ∀ elimLevel
      (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel),
    ∃ targetType,
      ∃ translation : TrExprS Hc.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams) []
        source.type targetType,
      translation.Avoids (fun name => name ∈ decl.sourceNames) ∧
        targetType = (recursorTargetSkeletonOf target c.lparams elimLevel
          Helim).type
  targetLookup : Hc.venv.constants target.name = some target.toVConstant
  lparamsNodup : c.lparams.Nodup

/-- The abstract family header seen by generated recursor code.  Small
elimination keeps the checked header unchanged.  Large elimination shifts
the header's abstract universe indices under the fresh leading recursor
parameter; its stored declaration arity is intentionally not changed. -/
def MotivePassHeaderAt.recursorTargetSkeleton
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    VInductiveTypeSkeleton :=
  recursorTargetSkeletonOf H.target c.lparams elimLevel Helim

/-- Common header parameters after the optional leading recursor universe is
introduced.  Term-variable indices are unchanged; only universe indices in
their domain types move. -/
def MotivePassHeaderAt.recursorParams
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    List VExpr :=
  match elimLevel with
  | .zero => H.checked.headers.params
  | .param _ => H.checked.headers.params.map
      (VExpr.instL (VLevel.prependShift c.lparams.length))
  | .succ _ | .max _ _ | .imax _ _ | .mvar _ => False.elim Helim

/-- The abstract common parameters remain definitionally
equal to the cached executable suffix after universe rebasing. -/
theorem MotivePassHeaderAt.recursorParamsContext
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    let R := Hc.toAdmissibleRecursorContextWF Helim
    let Hsuffix := H.checked.parameterSuffix.toRecursorContext Helim
    VEnv.IsDefEqCtx R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams).length []
      (H.recursorParams Helim).reverse Hsuffix.parameterDecls.toCtx := by
  dsimp only
  cases elimLevel with
  | zero => exact H.checked.paramsContext
  | param fresh =>
    let shift := VLevel.prependShift c.lparams.length
    change VEnv.IsDefEqCtx Hc.venv (fresh :: c.lparams).length []
      (H.checked.headers.params.map (VExpr.instL shift)).reverse
      (H.checked.parameterScope.instL shift).toCtx
    have hshift : ∀ level ∈ shift,
        level.WF (fresh :: c.lparams).length := by
      simpa [shift] using
        VLevel.prependShift_wf (n := c.lparams.length)
    have hctx := Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.instL hshift
      H.checked.paramsContext
    simpa only [MotivePassHeaderAt.recursorParams,
      List.map_reverse, List.map_nil, TypeChecker.MLCtx.prependLevelParam_vlctx,
      VLCtx.instL_toCtx, shift] using hctx
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- Recover the abstract domains of an executable source header directly
in the universe context used by generated recursors, and relate those domains
to the cached parameter suffix.  This theorem needs
neither an installed target lookup nor the lowered constructor environment,
so it can be used on the source-environment side of nested lowering. -/
theorem _root_.Lean4Lean.VerifyInductive.checkInductiveTypes.loopInd.HeaderStatsWF.sourceParameterDomainsAt
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : checkInductiveTypes.loopInd.HeaderStatsWF
      Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (source : InductiveType) (target : VInductiveType)
    (Hsource : TrSourceConst Hc.venv c.lparams source.name source.type
      target.toVConstVal)
    (htarget : target ∈ decl.types)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    (Htel : Expr.ForallTelescope source.type decl.nparams residual) :
    let Us := AddInductive.getRecLevelParams elimLevel c.lparams
    let Hsuffix := H.parameterSuffix.toRecursorContext Helim
    ∃ domains targetResidual,
      domains.length = decl.nparams ∧
      TrExprS Hc.venv Us [] source.type
        (VExpr.wrapForalls domains targetResidual) ∧
      VEnv.IsDefEqCtx Hc.venv Us.length []
        domains.reverse Hsuffix.parameterDecls.toCtx := by
  dsimp only
  have hshape : decl.TypeShape Hc.venv H.headers.params target :=
    H.headers.typeShapes target htarget
  rcases hshape with
    ⟨normalized, ownParams, afterParams, indices, result, exprType,
      hnormalized, hparamsTake, _hindicesTake, hparams, _hresult⟩
  rcases VExpr.takeForalls_rebuild hparamsTake with
    ⟨hnormalizedEq, hownLength⟩
  rw [hnormalizedEq] at hnormalized
  cases elimLevel with
  | zero =>
    rcases TrExprS.forallTelescope_shape_with_context Htel Hsource.type with
      ⟨domains, targetResidual, hdomainsLength, htarget, Hresidual⟩
    have Htarget : Hc.venv.IsDefEqU c.lparams.length []
        (VExpr.wrapForalls domains targetResidual)
        (VExpr.wrapForalls ownParams afterParams) := by
      rw [← htarget]
      exact ⟨exprType, by
        simpa [H.uvars] using hnormalized⟩
    have HdomainsOwn := VEnv.IsDefEqU.wrapForalls_context
      Hc.checking.tr.wf (VEnv.IsDefEqCtx.refl (by trivial))
      (hdomainsLength.trans hownLength.symm) Htarget
    have HdomainsOwn' : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
        domains.reverse ownParams.reverse := by
      simpa using HdomainsOwn
    have HownCommon : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
        ownParams.reverse H.headers.params.reverse := by
      simpa [H.uvars] using hparams.symm Hc.checking.tr.wf.ordered
    have HdomainsCommon := VEnv.IsDefEqCtx.trans_empty Hc.checking.tr.wf
      HdomainsOwn' HownCommon
    have HdomainsCached := VEnv.IsDefEqCtx.trans_empty Hc.checking.tr.wf
      HdomainsCommon H.paramsContext
    refine ⟨domains, targetResidual, hdomainsLength, ?_, ?_⟩
    · rw [← htarget]
      exact Hsource.type
    · change VEnv.IsDefEqCtx Hc.venv c.lparams.length []
        domains.reverse H.parameterScope.toCtx
      exact HdomainsCached
  | param fresh =>
    let shift := VLevel.prependShift c.lparams.length
    have hshift : ∀ level ∈ shift,
        level.WF (fresh :: c.lparams).length := by
      simpa [shift] using
        VLevel.prependShift_wf (n := c.lparams.length)
    have Hsource' : TrExprS Hc.venv (fresh :: c.lparams) [] source.type
        (target.type.instL shift) := by
      simpa [VLCtx.instL, shift] using Hsource.type.prependLevelParam
        Hc.checking.tr.wf (by trivial) Helim
    rcases TrExprS.forallTelescope_shape_with_context Htel Hsource' with
      ⟨domains, targetResidual, hdomainsLength, htarget, Hresidual⟩
    have hnormalized' := hnormalized.instL hshift
    have Htarget : Hc.venv.IsDefEqU (fresh :: c.lparams).length []
        (VExpr.wrapForalls domains targetResidual)
        (VExpr.wrapForalls (ownParams.map (VExpr.instL shift))
          (afterParams.instL shift)) := by
      rw [← htarget]
      exact ⟨exprType.instL shift, by
        simpa [VExpr.instL_wrapForalls, H.uvars, shift] using hnormalized'⟩
    have HdomainsOwn := VEnv.IsDefEqU.wrapForalls_context
      Hc.checking.tr.wf (VEnv.IsDefEqCtx.refl (by trivial))
      (by simp [hdomainsLength, hownLength]) Htarget
    have Hparams' :=
      Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.instL hshift hparams
    have HownCommon := Hparams'.symm Hc.checking.tr.wf.ordered
    have HdomainsCommon := VEnv.IsDefEqCtx.trans_empty Hc.checking.tr.wf
      (by simpa using HdomainsOwn) (by
        simpa [List.map_reverse] using HownCommon)
    have Hcached' :=
      Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.instL hshift H.paramsContext
    have HdomainsCached := VEnv.IsDefEqCtx.trans_empty Hc.checking.tr.wf
      HdomainsCommon (by
        simpa [List.map_reverse, VLCtx.instL_toCtx] using Hcached')
    refine ⟨domains, targetResidual, hdomainsLength, ?_, ?_⟩
    · rw [← htarget]
      exact Hsource'
    · change VEnv.IsDefEqCtx Hc.venv (fresh :: c.lparams).length []
        domains.reverse (H.parameterScope.instL shift).toCtx
      simpa [VLCtx.instL_toCtx, shift] using HdomainsCached
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- Expose the next family-local parameter from the abstract `TypeShape`
after shifting it beneath the optional fresh recursor universe parameter. -/
theorem MotivePassHeaderAt.recursorNextParameter
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    (hi : i < decl.nparams) :
    ∃ (ownParams : List VExpr)
        (expectedDomain expectedBody targetType : VExpr),
      ownParams.length = decl.nparams ∧
      ownParams[i]? = some expectedDomain ∧
      VEnv.IsDefEqCtx Hc.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams).length []
        (H.recursorParams Helim).reverse ownParams.reverse ∧
      Hc.venv.IsDefEq
        (AddInductive.getRecLevelParams elimLevel c.lparams).length []
        (H.recursorTargetSkeleton Helim).type
        (VExpr.wrapForalls (ownParams.take i)
          (.forallE expectedDomain expectedBody)) targetType := by
  have hshape : decl.TypeShape Hc.venv
      H.checked.headers.params H.target :=
    H.checked.headers.typeShapes H.target
      (List.mem_of_getElem? H.targetAt)
  cases elimLevel with
  | zero =>
    simpa [AddInductive.getRecLevelParams,
      MotivePassHeaderAt.recursorParams,
      MotivePassHeaderAt.recursorTargetSkeleton,
      VInductDecl.ParamsDefEq, VInductiveType.toSkeleton,
      H.checked.uvars] using
      VInductDecl.TypeShape.nextParameter hshape hi
  | param fresh =>
    let shift := VLevel.prependShift c.lparams.length
    change ∃ (ownParams : List VExpr)
        (expectedDomain expectedBody targetType : VExpr),
      ownParams.length = decl.nparams ∧
      ownParams[i]? = some expectedDomain ∧
      VEnv.IsDefEqCtx Hc.venv (fresh :: c.lparams).length []
        (H.checked.headers.params.map
          (VExpr.instL shift)).reverse ownParams.reverse ∧
      Hc.venv.IsDefEq (fresh :: c.lparams).length []
        (H.target.type.instL shift)
        (VExpr.wrapForalls (ownParams.take i)
          (.forallE expectedDomain expectedBody)) targetType
    rcases VInductDecl.TypeShape.nextParameter hshape hi with
      ⟨ownParams, expectedDomain, expectedBody, targetType,
        hlength, hget, hown, hpresentation⟩
    have hshift : ∀ level ∈ shift,
        level.WF (fresh :: c.lparams).length := by
      simpa [shift] using
        VLevel.prependShift_wf (n := c.lparams.length)
    let ownParams' := ownParams.map (VExpr.instL shift)
    let expectedDomain' := expectedDomain.instL shift
    let expectedBody' := expectedBody.instL shift
    let targetType' := targetType.instL shift
    refine ⟨ownParams', expectedDomain', expectedBody', targetType',
      ?_, ?_, ?_, ?_⟩
    · simp [ownParams', hlength]
    · simp [ownParams', expectedDomain', hget]
    · have hown' :=
        Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.instL hshift hown
      simpa only [MotivePassHeaderAt.recursorParams,
        ownParams', List.map_reverse, List.map_nil, shift] using hown'
    · have hpresentation' := hpresentation.instL hshift
      have instL_wrapForalls (domains : List VExpr) (result : VExpr) :
          (VExpr.wrapForalls domains result).instL shift =
            VExpr.wrapForalls (domains.map (VExpr.instL shift))
              (result.instL shift) := by
        induction domains with
        | nil => rfl
        | cons domain domains ih =>
          change VExpr.forallE (domain.instL shift)
              ((VExpr.wrapForalls domains result).instL shift) =
            VExpr.forallE (domain.instL shift)
              (VExpr.wrapForalls (domains.map (VExpr.instL shift))
                (result.instL shift))
          exact congrArg (VExpr.forallE (domain.instL shift)) ih
      simpa only [MotivePassHeaderAt.recursorTargetSkeleton,
        ownParams', expectedDomain', expectedBody', targetType',
        List.map_nil, List.map_take, List.map_reverse,
        VExpr.instL, instL_wrapForalls] using hpresentation'
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- The next domain exposed by the rebased abstract header telescope is the
cached parameter declaration selected in the current recursor context.
No successful executable `isDefEq` result is used to establish the match. -/
theorem MotivePassHeaderAt.recursorCurrentDomainDefEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {c' : AddInductive.Context}
    {R : RecursorContextWF c'
      (AddInductive.getRecLevelParams elimLevel c.lparams)}
    {Hsuffix : RecursorParameterContextSuffix R stats runtimeDepth}
    {name : Name} {dom body : Expr} {bi : BinderInfo}
    {currentDomain currentBody : VExpr}
    (Hscope : RecursorReusedParameterScope Hsuffix i
      (.forallE name dom body bi))
    (Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) Hscope.older
        (.forallE currentDomain currentBody) i 0)
    (hi : i < stats.params.size)
    (henv : R.venv = Hc.venv)
    (hctx : VEnv.IsDefEqCtx R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams).length []
      (H.recursorParams Helim).reverse Hsuffix.parameterDecls.toCtx) :
    R.venv.IsDefEqU
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      Hscope.older.toCtx currentDomain Hscope.paramType := by
  have hparameterCount : stats.params.size = decl.nparams := by
    have hlength := List.Forall₂.length_eq
      H.checked.suffixParams
    simpa [VInductDecl.paramVars] using hlength
  have hiDecl : i < decl.nparams := by
    rw [← hparameterCount]
    exact hi
  rcases H.recursorNextParameter Helim hiDecl with
    ⟨ownParams, expectedDomain, expectedBody, targetType,
      hownLength, hget, hown, hpresentation⟩
  have hiOwn : i < ownParams.length := by omega
  have hexpected : expectedDomain = ownParams[i] := by
    have hget' : some ownParams[i] = some expectedDomain := by
      simpa [List.getElem?_eq_getElem hiOwn] using hget
    exact (Option.some.inj hget').symm
  have hindices : Hsynthesis.indices = [] :=
    List.eq_nil_of_length_eq_zero Hsynthesis.indexCount
  have hprefixLength : Hsynthesis.params.length =
      (ownParams.take i).length := by
    rw [Hsynthesis.parameterCount, List.length_take]
    omega
  have hpresentationR : R.venv.IsDefEq
      (AddInductive.getRecLevelParams elimLevel c.lparams).length []
      (H.recursorTargetSkeleton Helim).type
      (VExpr.wrapForalls (ownParams.take i)
        (.forallE expectedDomain expectedBody)) targetType := by
    simpa [henv] using hpresentation
  rcases Hsynthesis.nextDomainDefEq R.checking.tr.wf hindices
      hprefixLength hpresentationR with ⟨nextLevel, hnext⟩
  have hscopeCtx : Hscope.older.toCtx = Hsynthesis.params.reverse := by
    simpa [hindices] using Hsynthesis.scopeCtx
  have hnext' : R.venv.IsDefEq
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      Hscope.older.toCtx currentDomain expectedDomain (.sort nextLevel) := by
    rw [hscopeCtx]
    exact hnext
  have hparamsLength : (H.recursorParams Helim).length =
      stats.params.size := by
    have hctxLength := H.checked.paramsContext.length_eq
    have hcachedCtx :=
      checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
        H.checked.cachedScope
    have hcachedLength :=
      List.Forall₂.length_eq
        H.checked.cachedScope
    have hbaseLength : H.checked.headers.params.length =
        stats.params.size := by
      calc
        H.checked.headers.params.length =
            H.checked.headers.params.reverse.length := by simp
        _ = H.checked.parameterScope.toCtx.length := hctxLength
        _ = H.checked.parameterScope.length := hcachedCtx
        _ = stats.params.size := by simpa using hcachedLength.symm
    cases elimLevel with
    | zero => simpa [MotivePassHeaderAt.recursorParams]
        using hbaseLength
    | param fresh => simpa [MotivePassHeaderAt.recursorParams]
        using hbaseLength
    | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
      simp [AddInductive.AdmissibleElimLevel] at Helim
  have hownR : VEnv.IsDefEqCtx R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams).length []
      (H.recursorParams Helim).reverse ownParams.reverse := by
    simpa [henv] using hown
  rcases Hscope.ownParameterDefEq hi hparamsLength hctx hownR with
    ⟨cachedLevel, hcached⟩
  have hcached' : R.venv.IsDefEq
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      Hscope.older.toCtx expectedDomain Hscope.paramType
      (.sort cachedLevel) := by
    simpa [hexpected] using hcached
  exact ⟨_, hnext'.trans_r R.checking.tr.wf
    (Hscope.lift.wf R.checking.tr.wf R.mlctx_wf.tr.wf).1.toCtx
    hcached'⟩

@[simp] theorem MotivePassHeaderAt.recursorTargetSkeleton_zero
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams (.zero)) :
    H.recursorTargetSkeleton Helim = H.target.toSkeleton := rfl

/-- The closed executable source header translates to the rebased abstract
header under the universe list assigned to generated recursors. -/
theorem MotivePassHeaderAt.recursorSourceTranslation
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    TrExprS Hc.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams) []
      source.type (H.recursorTargetSkeleton Helim).type := by
  cases elimLevel with
  | zero => exact H.sourceTranslation.type
  | param fresh =>
    change TrExprS Hc.venv (fresh :: c.lparams) [] source.type
      (H.target.type.instL (VLevel.prependShift c.lparams.length))
    simpa [VLCtx.instL] using H.sourceTranslation.type.prependLevelParam
      Hc.checking.tr.wf (by trivial) Helim
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- The rebased abstract header remains a type in the recursor universe
context. -/
theorem MotivePassHeaderAt.recursorTargetType
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    Hc.venv.IsType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length []
      (H.recursorTargetSkeleton Helim).type := by
  have htarget : Hc.venv.IsType c.lparams.length [] H.target.type := by
    have htyped := H.sourceTranslation.wf
    change Hc.venv.IsType H.target.uvars [] H.target.type at htyped
    rwa [H.sourceTranslation.uvars] at htyped
  cases elimLevel with
  | zero => exact htarget
  | param fresh =>
    let shift := VLevel.prependShift c.lparams.length
    have hshift : ∀ level ∈ shift,
        level.WF (fresh :: c.lparams).length := by
      simpa [shift] using
        VLevel.prependShift_wf (n := c.lparams.length)
    exact htarget.instL hshift
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- Normalize a later mutual-family header in the generated recursor
context and restart the abstract header telescope in the empty closed scope.
This is the first step that remains valid after earlier major and
motive frames have introduced the fresh large-elimination universe. -/
theorem MotivePassHeaderAt.startRecursorHeaderTyping
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {c' : AddInductive.Context}
    (R : RecursorContextWF c'
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    (henv : R.venv = Hc.venv) (hchk : R.chk.vlctx = []) :
    ((monadLift (TypeChecker.whnf source.type) :
        AddInductive.M Expr) c').WF fun normalized =>
      normalized.levelParamsIn c.lparams = true ∧
      FVarsBelow R.mlctx.vlctx source.type normalized ∧
      ∃ normalizedTarget,
        TrExprS R.venv
          (AddInductive.getRecLevelParams elimLevel c.lparams) []
          normalized normalizedTarget ∧
        Nonempty
          (checkInductiveTypes.loopType.ScopedHeaderTelescope
            R.venv
            (AddInductive.getRecLevelParams elimLevel c.lparams)
            (H.recursorTargetSkeleton Helim) [] normalizedTarget 0 0) := by
  let recLparams :=
    AddInductive.getRecLevelParams elimLevel c.lparams
  have htarget : TrExprS R.venv recLparams [] source.type
      (H.recursorTargetSkeleton Helim).type := by
    simpa [recLparams, henv] using H.recursorSourceTranslation Helim
  have htargetType : R.venv.IsType recLparams.length []
      (H.recursorTargetSkeleton Helim).type := by
    simpa [recLparams, henv] using H.recursorTargetType Helim
  let W : VLCtx.FVLift [] R.mlctx.vlctx 0
      R.mlctx.vlctx.toCtx.length 0 :=
    VLCtx.FVLift.from_nil R.mlctx.noBV
  have hsource := htarget.weakFV R.checking.tr.wf.orderedStrong W
    R.mlctx_wf.tr.wf
  have hsource₀ : TrExprS R.venv recLparams R.chk.vlctx source.type
      (H.recursorTargetSkeleton Helim).type := by
    rw [hchk]; exact htarget
  have hnormalize := whnfInRecursorContext.dualWF R hsource hsource₀
  have hsourceNoFVars : FVarsIn (fun _ => False) source.type :=
    htarget.fvarsIn.mono fun fv hfv => by
      simp [VLCtx.fvars] at hfv
  have hfalseUpSet : IsFVarUpSet (fun _ => False) R.mlctx.vlctx := by
    have hsuffix := IsFVarUpSet.suffixFVars ([] : VLCtx)
      R.mlctx.vlctx (by simpa using R.mlctx_wf.tr.wf)
    simpa [VLCtx.fvars] using hsuffix
  have hlevels := whnfInRecursorContext.levelsWF R hsource₀
  refine (hlevels.and hnormalize).mono
    fun normalized ⟨hnormalizedLevels, hnormalized, _, hnormalized₀⟩ => ?_
  refine ⟨hnormalizedLevels c.lparams (fun _ => False)
    ⟨hfalseUpSet, fun _ _ h => h.elim⟩
    H.sourceTranslation.type.levelParamsIn hsourceNoFVars, ?_⟩
  rw [hchk] at hnormalized₀
  rcases hnormalized₀ with ⟨normalizedTarget, hnormalizedTarget, hheader'⟩
  have hheader := hheader'.symm
  have hnormalizedType : R.venv.IsType recLparams.length []
      normalizedTarget :=
    htargetType.defeqU_l R.checking.tr.wf (by trivial) hheader
  rcases htargetType with ⟨targetLevel, htargetHasType⟩
  have hheaderTyped := hheader.of_l R.checking.tr.wf (by trivial)
    htargetHasType
  exact ⟨hnormalized.1, normalizedTarget, hnormalizedTarget,
    ⟨checkInductiveTypes.loopType.ScopedHeaderTelescope.empty
      ⟨targetLevel, htargetHasType⟩ hnormalizedType hheaderTyped⟩⟩

/-- The header normalization of `loopInd1` as a recursor `whnf`
call (`WhnfRunAt`): the closed header translates in the recursor context and has no free
variables. -/
theorem MotivePassHeaderAt.headerWhnfCall
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {c' : AddInductive.Context}
    (R : RecursorContextWF c'
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    (henv : R.venv = Hc.venv) :
    ((monadLift (TypeChecker.whnf source.type) :
        AddInductive.M Expr) c').WF fun normalized =>
      WhnfRunAt c' (fun _ => False) source.type normalized := by
  let recLparams :=
    AddInductive.getRecLevelParams elimLevel c.lparams
  have htarget : TrExprS R.venv recLparams [] source.type
      (H.recursorTargetSkeleton Helim).type := by
    simpa [recLparams, henv] using H.recursorSourceTranslation Helim
  let W : VLCtx.FVLift [] R.mlctx.vlctx 0
      R.mlctx.vlctx.toCtx.length 0 :=
    VLCtx.FVLift.from_nil R.mlctx.noBV
  have hsource := htarget.weakFV R.checking.tr.wf.orderedStrong W
    R.mlctx_wf.tr.wf
  have hsourceNoFVars : FVarsIn (fun _ => False) source.type :=
    htarget.fvarsIn.mono fun fv hfv => by
      simp [VLCtx.fvars] at hfv
  have hfalseUpSet : IsFVarUpSet (fun _ => False) R.mlctx.vlctx := by
    have hsuffix := IsFVarUpSet.suffixFVars ([] : VLCtx)
      R.mlctx.vlctx (by simpa using R.mlctx_wf.tr.wf)
    simpa [VLCtx.fvars] using hsuffix
  intro normalized hrun
  exact ⟨c', recLparams, R, fun _ => False, _, BindingContextLE.refl c',
    hsource, hfalseUpSet, fun _ h => h.elim, hsourceNoFVars, hrun, _,
    htarget.weakFV R.checking.tr.wf.orderedStrong
      (VLCtx.FVLift.from_nil R.chk.noBV) R.check.wf.tr.wf⟩

theorem MotivePassHeaderAt.target_mem
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx) :
    H.target ∈ decl.types :=
  List.mem_of_getElem? H.targetAt

theorem MotivePassHeaderAt.shape
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx) :
    decl.TypeShape Hc.venv H.checked.headers.params H.target :=
  H.checked.headers.typeShapes H.target H.target_mem

theorem MotivePassHeaderAt.parameterCount
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx) :
    stats.params.size = decl.nparams := by
  have hlength := List.Forall₂.length_eq
    H.checked.suffixParams
  simpa [VInductDecl.paramVars] using hlength

theorem MotivePassHeaderAt.indexCount
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx) :
    stats.nindices[familyIdx]? = some H.target.numIndices := by
  have htargetBound : familyIdx < decl.types.length :=
    List.getElem?_eq_some_iff.mp H.targetAt |>.1
  have hstatsLength : stats.nindices.size = decl.types.length := by
    simpa using congrArg List.length H.checked.indices
  have hstatsBound : familyIdx < stats.nindices.size := by omega
  rw [Array.getElem?_eq_getElem hstatsBound]
  have hentry := congrArg (fun values => values[familyIdx]?)
    H.checked.indices
  simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hstatsBound,
    List.getElem?_map, H.targetAt, Option.map_some] at hentry
  exact hentry

def MotivePassHeaderAt.abstractLevels (lparams : List Name) : List VLevel :=
  lparams.map fun name => .param (lparams.idxOf name)

theorem MotivePassHeaderAt.abstractLevels_eq_params
    (hnodup : lparams.Nodup) :
    MotivePassHeaderAt.abstractLevels lparams = VLevel.params lparams.length := by
  apply List.ext_getElem
  · simp [MotivePassHeaderAt.abstractLevels, VLevel.params]
  · intro i hleft hright
    have hi : i < lparams.length := by
      simpa [VLevel.params] using hright
    simp [MotivePassHeaderAt.abstractLevels, VLevel.params,
      hnodup.idxOf_getElem i hi]

theorem MotivePassHeaderAt.targetType_inst_abstractLevels
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx) :
    H.target.type.instL (MotivePassHeaderAt.abstractLevels c.lparams) = H.target.type := by
  rw [MotivePassHeaderAt.abstractLevels_eq_params H.lparamsNodup, ← H.sourceTranslation.uvars]
  have htyped := Classical.choose_spec H.sourceTranslation.wf
  exact (htyped.levelWF (by trivial)).1.instL_id

/-- Universe arguments of the installed family constant as seen from the
generated recursor.  Large elimination inserts one fresh leading universe,
so every declaration universe argument is shifted by one slot. -/
def MotivePassHeaderAt.recursorAbstractLevels
    (lparams : List Name)
    (Helim : AddInductive.AdmissibleElimLevel lparams elimLevel) :
    List VLevel :=
  match elimLevel with
  | .zero => (MotivePassHeaderAt.abstractLevels lparams)
  | .param _ => (MotivePassHeaderAt.abstractLevels lparams).map
      (VLevel.inst (VLevel.prependShift lparams.length))
  | .succ _ | .max _ _ | .imax _ _ | .mvar _ => False.elim Helim

theorem MotivePassHeaderAt.recursorAbstractLevels_length
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim).length = H.target.uvars := by
  cases elimLevel with
  | zero =>
    simp [MotivePassHeaderAt.recursorAbstractLevels,
      MotivePassHeaderAt.abstractLevels_eq_params H.lparamsNodup, H.sourceTranslation.uvars]
  | param fresh =>
    simp [MotivePassHeaderAt.recursorAbstractLevels,
      MotivePassHeaderAt.abstractLevels_eq_params H.lparamsNodup, H.sourceTranslation.uvars]
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

theorem MotivePassHeaderAt.recursorAbstractLevels_wf
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    ∀ level ∈ MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim,
      level.WF
        (AddInductive.getRecLevelParams elimLevel c.lparams).length := by
  cases elimLevel with
  | zero =>
    intro level hlevel
    rw [MotivePassHeaderAt.recursorAbstractLevels,
      MotivePassHeaderAt.abstractLevels_eq_params H.lparamsNodup] at hlevel
    exact VLevel.params_wf hlevel
  | param fresh =>
    let shift := VLevel.prependShift c.lparams.length
    have hshift : ∀ level ∈ shift,
        level.WF (fresh :: c.lparams).length := by
      simpa [shift] using
        VLevel.prependShift_wf (n := c.lparams.length)
    rw [MotivePassHeaderAt.recursorAbstractLevels]
    intro level hlevel
    rw [List.mem_map] at hlevel
    rcases hlevel with ⟨sourceLevel, hsourceLevel, rfl⟩
    exact VLevel.WF.inst hshift
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- The installed family constant at its translated universe
arguments has the abstract header type. -/
theorem MotivePassHeaderAt.constHasType
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx) :
    Hc.venv.HasType c.lparams.length []
      (.const H.target.name (MotivePassHeaderAt.abstractLevels c.lparams)) H.target.type := by
  have hlevels : ∀ level ∈ (MotivePassHeaderAt.abstractLevels c.lparams),
      level.WF c.lparams.length := by
    rw [MotivePassHeaderAt.abstractLevels_eq_params H.lparamsNodup]
    exact VLevel.params_wf
  have hlength : (MotivePassHeaderAt.abstractLevels c.lparams).length = H.target.uvars := by
    rw [MotivePassHeaderAt.abstractLevels_eq_params H.lparamsNodup, VLevel.params_length,
      H.sourceTranslation.uvars]
  have hconst := VEnv.HasType.const (Γ := []) H.targetLookup hlevels hlength
  simpa [H.targetType_inst_abstractLevels] using hconst

/-- The family constant remains typed after the optional recursor-universe
shift, independently of how many earlier mutual frames are in the local
context. -/
theorem MotivePassHeaderAt.recursorConstHasType
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    (henv : R.venv = Hc.venv) :
    R.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length []
      (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
      (H.recursorTargetSkeleton Helim).type := by
  cases elimLevel with
  | zero =>
    simpa [MotivePassHeaderAt.recursorAbstractLevels,
      MotivePassHeaderAt.recursorTargetSkeleton,
      AddInductive.getRecLevelParams, VInductiveType.toSkeleton, henv] using
      H.constHasType
  | param fresh =>
    let shift := VLevel.prependShift c.lparams.length
    have hshift : ∀ level ∈ shift,
        level.WF (fresh :: c.lparams).length := by
      simpa [shift] using
        VLevel.prependShift_wf (n := c.lparams.length)
    have htyped := H.constHasType.instL hshift
    simpa [MotivePassHeaderAt.recursorAbstractLevels,
      MotivePassHeaderAt.recursorTargetSkeleton,
      AddInductive.getRecLevelParams, VExpr.instL, shift, henv] using
      htyped
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- Translation of the executable family constant at the recursor universes:
its universe arguments are translated after the optional fresh leading
recursor parameter. -/
theorem MotivePassHeaderAt.recursorIndConstTranslation
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx}
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope stats decl appDepth)
    (henv : R.venv = Hc.venv) :
    TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams) scope
      stats.indConsts[familyIdx]!
      (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim)) := by
  have hbound : familyIdx < decl.types.length :=
    List.getElem?_eq_some_iff.mp H.targetAt |>.1
  have htarget : decl.types[familyIdx] = H.target := by
    have htargetAt := H.targetAt
    rw [List.getElem?_eq_getElem hbound] at htargetAt
    exact Option.some.inj htargetAt
  have hconst : stats.indConsts[familyIdx]? =
      some (.const decl.types[familyIdx].name stats.levels) := by
    rw [Hstats.consts.exact]
    simp [hbound]
  have hsource : stats.indConsts[familyIdx]! =
      .const H.target.name stats.levels := by
    simp [Array.getElem!_eq_getD, hconst, htarget]
  rw [hsource]
  have hlevels : stats.levels.mapM
      (VLevel.ofLevel
        (AddInductive.getRecLevelParams elimLevel c.lparams)) =
      some (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim) := by
    cases elimLevel with
    | zero =>
      simpa [MotivePassHeaderAt.recursorAbstractLevels,
        MotivePassHeaderAt.abstractLevels,
        AddInductive.getRecLevelParams] using
        H.checked.levelTranslation
    | param fresh =>
      have hshifted := VLevel.mapM_ofLevel_fresh_cons Helim
        H.checked.levelTranslation
      simpa [MotivePassHeaderAt.recursorAbstractLevels,
        MotivePassHeaderAt.abstractLevels,
        AddInductive.getRecLevelParams] using hshifted
    | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
      simp [AddInductive.AdmissibleElimLevel] at Helim
  apply TrExprS.const (by simpa [henv] using H.targetLookup) hlevels
  have hlevelsLength := Hstats.levels
  have huvars := H.checked.uvars
  have htargetUvars := H.sourceTranslation.uvars
  omega

/-- The executable arguments in the abstract header scope,
interpreted under the recursor universe list. -/
theorem MotivePassHeaderAt.recursorScopedArguments
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {indices : Array Expr} {indexTargets : List VExpr}
    {nindices : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope stats decl nindices)
    (Hindices : List.Forall₂ (TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams) scope)
      indices.toList indexTargets)
    (hreplay : indexTargets.length = nindices)
    (hcanonical : indexTargets = indexBVarSpine nindices)
    (harity : (indices.size == stats.nindices[familyIdx]!) = true) :
    List.Forall₂ (TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams) scope)
      (stats.params.toList ++ indices.toList)
      (indexBVarSpine (decl.nparams + H.target.numIndices)) := by
  have htranslated : indices.size = indexTargets.length := by
    simpa using List.Forall₂.length_eq Hindices
  have hguard : indices.size = stats.nindices[familyIdx]! := by
    simpa using harity
  have hfamily : stats.nindices[familyIdx]! = H.target.numIndices := by
    simp [Array.getElem!_eq_getD, H.indexCount]
  have hnindices : nindices = H.target.numIndices := by omega
  have Hall :=
    List.Forall₂.append' Hstats.params Hindices
  rw [hcanonical, VInductDecl.paramVars_append_indexBVarSpine] at Hall
  simpa [hnindices, H.parameterCount] using Hall

/-- Applying the installed family constant to the parameter variables of a
rebased header yields its residual index telescope. -/
theorem MotivePassHeaderAt.recursorCanonicalFamilyPrefix
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {narrowTarget : VExpr} {nindices : Nat}
    (Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (henv : R.venv = Hc.venv) :
    R.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      Hsynthesis.params.reverse
      (VExpr.mkApps
        ((VExpr.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim)).liftN
          Hsynthesis.params.length 0)
        (bvarSpine Hsynthesis.params.length))
      (VExpr.wrapForalls Hsynthesis.indices narrowTarget) := by
  have hhead := H.recursorConstHasType Helim R henv
  have hheadTelescope : R.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length []
      (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
      (VExpr.wrapForalls (Hsynthesis.params ++ Hsynthesis.indices)
        narrowTarget) := by
    apply hhead.defeqU_r R.checking.tr.wf (by trivial)
    exact ⟨Hsynthesis.exprType, Hsynthesis.header⟩
  simpa [bvarSpine] using
    VEnv.HasType.mkApps_wrapForalls_prefix_bvarSpine
      R.checking.tr.wf.ordered hheadTelescope

/-- The family prefix (applied to its parameter variables) remains typed
after reopening the index scope; both the prefix and its residual index telescope are shifted
beneath those ambient index variables. -/
theorem MotivePassHeaderAt.recursorCanonicalFamilyPrefixAtScope
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {narrowTarget : VExpr} {nindices : Nat}
    (Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (henv : R.venv = Hc.venv) :
    R.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length scope.toCtx
      ((VExpr.mkApps
        ((VExpr.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim)).liftN
          Hsynthesis.params.length 0)
        (bvarSpine Hsynthesis.params.length)).liftN
          Hsynthesis.indices.length 0)
      ((VExpr.wrapForalls Hsynthesis.indices narrowTarget).liftN
        Hsynthesis.indices.length 0) := by
  have hprefix := H.recursorCanonicalFamilyPrefix Helim R Hsynthesis henv
  have hweakened := hprefix.weakN R.checking.tr.wf.ordered
    (Ctx.LiftN.zero Hsynthesis.indices.reverse)
  simpa [Hsynthesis.scopeCtx, List.reverse_append] using hweakened

/-- The executable family prefix, before its indices are applied, translates
to the parameter-variable application in the checking scope.
This is the translation counterpart of
`recursorCanonicalFamilyPrefixAtScope`. -/
theorem MotivePassHeaderAt.recursorScopedFamilyPrefixTranslation
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {narrowTarget : VExpr} {nindices : Nat}
    (Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope stats decl nindices)
    (henv : R.venv = Hc.venv) :
    let family := VExpr.mkApps
      (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
      (decl.paramVars nindices)
    TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams) scope
        (mkAppN stats.indConsts[familyIdx]! stats.params) family ∧
      R.venv.HasType
        (AddInductive.getRecLevelParams elimLevel c.lparams).length
        scope.toCtx family
          ((VExpr.wrapForalls Hsynthesis.indices narrowTarget).liftN
            nindices 0) := by
  dsimp only
  have hcanonical := H.recursorCanonicalFamilyPrefixAtScope Helim R
    Hsynthesis henv
  have hparamCount : Hsynthesis.params.length = decl.nparams := by
    rw [Hsynthesis.parameterCount, H.parameterCount]
  have hindexCount : Hsynthesis.indices.length = nindices :=
    Hsynthesis.indexCount
  have hfamilyType : R.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length scope.toCtx
      (VExpr.mkApps
        (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
        (decl.paramVars nindices))
      ((VExpr.wrapForalls Hsynthesis.indices narrowTarget).liftN
        nindices 0) := by
    simpa [bvarSpine, VInductDecl.paramVars, hparamCount,
      hindexCount, VExpr.liftN_mkApps, VExpr.liftN,
      ← List.map_reverse, Function.comp_def, Nat.add_comm] using hcanonical
  have hhead := H.recursorIndConstTranslation Helim R Hstats henv
  have htranslated := checkPositivityStep.TrExprS.mkAppList
    R.checking.tr.wf.orderedStrong Hsynthesis.scopeWF.toCtx hhead Hstats.params
    (show VExpr.WF R.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams).length
        scope.toCtx
        (VExpr.mkApps
          (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
          (decl.paramVars nindices)) from ⟨_, hfamilyType⟩)
  exact ⟨by
    simpa [Expr.mkAppN_eq_mkAppList] using htranslated, hfamilyType⟩

/-- Transport the family-prefix typing from the checking scope into the executable
index context and identify its term with the prefix stored in the motive
frame.  Strict equality is available because the executable constant/free-
variable application has unique translation. -/
theorem MotivePassHeaderAt.recursorFamilyPrefixTyping
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {narrowTarget : VExpr} {nindices : Nat}
    {indices : Array Expr}
    (Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope stats decl nindices)
    (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope R.mlctx.vlctx)
    (henv : R.venv = Hc.venv)
    (Hframe : RecursorMotiveFrameWF R stats familyIdx indices elimLevel) :
    let familyType :=
      ((VExpr.wrapForalls Hsynthesis.indices narrowTarget).liftN
        nindices 0).lift' Hruntime.shift
    R.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      R.mlctx.vlctx.toCtx Hframe.familyTarget familyType := by
  dsimp only
  rcases H.recursorScopedFamilyPrefixTranslation Helim R Hsynthesis Hstats
      henv with ⟨Hfamily, HfamilyType⟩
  have HfamilyWeak : TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      Hruntime.expanded
      (mkAppN stats.indConsts[familyIdx]! stats.params)
      ((VExpr.mkApps
        (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
        (decl.paramVars nindices)).lift' Hruntime.shift) := by
    simpa using Hfamily.weakFV' R.checking.tr.wf.orderedStrong Hruntime.lift
      Hruntime.context.wf
  have HtypeWeak := HfamilyType.weak' R.checking.tr.wf.ordered
    Hruntime.lift.toCtx
  have HtypeRuntime := HtypeWeak.defeqDFC R.checking.tr.wf.ordered
    Hruntime.context.defeqCtx
  have HfamilyEqU : R.venv.IsDefEqU
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      R.mlctx.vlctx.toCtx
      ((VExpr.mkApps
        (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
        (decl.paramVars nindices)).lift' (Hruntime.shift.consN 0))
      Hframe.familyTarget := by
    have Heq := HfamilyWeak.uniq R.checking.tr.wf
      Hruntime.context Hframe.familyTr
    exact Heq.defeqDFC R.checking.tr.wf.ordered Hruntime.context.defeqCtx
  exact HtypeRuntime.defeqU_l R.checking.tr.wf
    R.mlctx_wf.tr.wf.toCtx HfamilyEqU

/-- The family prefix in the checking scope and the prefix stored in the
executable motive frame are not merely definitionally equal.  Their source
is syntax-directed and the checking and executable contexts have the same declaration
spine, so translation uniqueness identifies the terms strictly. -/
theorem MotivePassHeaderAt.recursorFamilyPrefixEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {narrowTarget : VExpr} {nindices : Nat}
    {indices : Array Expr}
    (Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope stats decl nindices)
    (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope R.mlctx.vlctx)
    (henv : R.venv = Hc.venv)
    (Hframe : RecursorMotiveFrameWF R stats familyIdx indices elimLevel) :
    (VExpr.mkApps
        (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
        (decl.paramVars nindices)).lift' Hruntime.shift =
      Hframe.familyTarget := by
  rcases H.recursorScopedFamilyPrefixTranslation Helim R Hsynthesis Hstats
      henv with ⟨Hfamily, _HfamilyType⟩
  have HfamilyWeak : TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      Hruntime.expanded
      (mkAppN stats.indConsts[familyIdx]! stats.params)
      ((VExpr.mkApps
        (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
        (decl.paramVars nindices)).lift' Hruntime.shift) := by
    simpa using Hfamily.weakFV' R.checking.tr.wf.orderedStrong Hruntime.lift
      Hruntime.context.wf
  exact HfamilyWeak.uniqueCtx
    (Lean4Lean.VerifyInductive.VLCtx.IsDefEq.toIsUniqueCtx_ofOnlyLams
      Hruntime.context R.onlyLams)
    Hframe.familyTr

/-- The index arguments recovered from the executable major application are
exactly the weakened index variables of the checking scope.
The source array contains only free variables, so the same
cross-context uniqueness argument applies pointwise. -/
theorem MotivePassHeaderAt.recursorIndexTargetsEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {narrowTarget : VExpr} {nindices : Nat}
    {indices : Array Expr} {indexTargets : List VExpr}
    (_Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope R.mlctx.vlctx)
    (Hindices : List.Forall₂ (TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams) scope)
      indices.toList indexTargets)
    (hcanonical : indexTargets = indexBVarSpine nindices)
    (_Hbound : FVarArrayIn current indices)
    (Hframe : RecursorMotiveFrameWF R stats familyIdx indices elimLevel) :
    (indexBVarSpine nindices).map (fun target =>
        target.lift' Hruntime.shift) = Hframe.familyIndexTargets := by
  have Hweak : List.Forall₂ (TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      Hruntime.expanded) indices.toList
      (indexTargets.map fun target => target.lift' Hruntime.shift) := by
    apply checkPositivityStep.forall₂_map_right Hindices
    intro source target Hsource
    simpa using Hsource.weakFV' R.checking.tr.wf.orderedStrong Hruntime.lift
      Hruntime.context.wf
  have Heq := Lean4Lean.VerifyInductive.TrExprS.forall₂_unique
    (Lean4Lean.VerifyInductive.VLCtx.IsDefEq.toIsUniqueCtx_ofOnlyLams
      Hruntime.context R.onlyLams)
    Hweak Hframe.familyIndicesTr
  simpa [hcanonical] using Heq

/-- Instantiate the abstract parallel motive telescope from the
checked header, weaken it through the executable-context embedding, and identify
its family head with the executable frame by strict translation uniqueness. -/
theorem MotivePassHeaderAt.recursorCanonicalMotiveFrame
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {narrowTarget : VExpr} {nindices : Nat}
    {indices : Array Expr}
    (Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope stats decl nindices)
    (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope R.mlctx.vlctx)
    (henv : R.venv = Hc.venv)
    (hindices : indices.size = nindices)
    (Hframe : RecursorMotiveFrameWF R stats familyIdx indices elimLevel) :
    ∃ Hcanonical : RecursorMotiveClosedFrameWF R stats familyIdx
        indices elimLevel Hframe,
      Hcanonical.familyType =
        ((VExpr.wrapForalls Hsynthesis.indices narrowTarget).liftN
          nindices 0).lift' Hruntime.shift ∧
      Hcanonical.motiveType =
        ((VExpr.wrapForalls Hsynthesis.indices
          (.forallE
            (VExpr.mkApps
              ((VExpr.mkApps
                (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
                (bvarSpine Hsynthesis.params.length)).liftN
                  Hsynthesis.indices.length 0)
              (bvarSpine Hsynthesis.indices.length))
            (.sort Hframe.resultLevel))).liftN nindices 0).lift'
              Hruntime.shift := by
  let familyBase := VExpr.mkApps
    (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
    (bvarSpine Hsynthesis.params.length)
  let Hbase := RecursorMotiveTelescope.wrapForalls Hsynthesis.indices
    familyBase narrowTarget Hframe.resultLevel
  let Hscope := Hbase.liftN nindices 0
  let Hfull := Hscope.lift' Hruntime.shift
  have hparameterCount : Hsynthesis.params.length = decl.nparams := by
    rw [Hsynthesis.parameterCount, H.parameterCount]
  have hfamilyScope : familyBase.liftN nindices 0 =
      VExpr.mkApps
        (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
        (decl.paramVars nindices) := by
    simp [familyBase, bvarSpine, VInductDecl.paramVars, VExpr.liftN,
      hparameterCount, Function.comp_def, Nat.add_comm]
  have hfamily := H.recursorFamilyPrefixEq Helim R Hsynthesis
    Hstats Hruntime henv Hframe
  have hfamilyFull :
      (familyBase.liftN nindices 0).lift' Hruntime.shift =
        Hframe.familyTarget := by
    rw [hfamilyScope]
    exact hfamily
  have Htelescope : RecursorMotiveTelescope Hframe.resultLevel indices.size
      Hframe.familyTarget
      (((VExpr.wrapForalls Hsynthesis.indices narrowTarget).liftN
        nindices 0).lift' Hruntime.shift)
      (((VExpr.wrapForalls Hsynthesis.indices
        (.forallE
          (VExpr.mkApps (familyBase.liftN Hsynthesis.indices.length 0)
            (bvarSpine Hsynthesis.indices.length))
          (.sort Hframe.resultLevel))).liftN nindices 0).lift'
            Hruntime.shift) := by
    have harity : Hsynthesis.indices.length = indices.size :=
      Hsynthesis.indexCount.trans hindices.symm
    have Hfull' := Hfull
    rw [hfamilyFull] at Hfull'
    simpa only [harity] using Hfull'
  refine ⟨{
    familyType :=
      ((VExpr.wrapForalls Hsynthesis.indices narrowTarget).liftN
        nindices 0).lift' Hruntime.shift
    motiveType :=
      ((VExpr.wrapForalls Hsynthesis.indices
        (.forallE
          (VExpr.mkApps (familyBase.liftN Hsynthesis.indices.length 0)
            (bvarSpine Hsynthesis.indices.length))
          (.sort Hframe.resultLevel))).liftN nindices 0).lift'
            Hruntime.shift
    familyTyping := H.recursorFamilyPrefixTyping Helim R Hsynthesis
      Hstats Hruntime henv Hframe
    telescope := Htelescope }, rfl, ?_⟩
  rfl

/-- The motive telescope built by the executable is definitionally equal to
the generated telescope.  The proof closes the
leading index declarations on both sides of the conversion between the checking
and executable contexts, compares the family application with the unannotated
major domain, and then reopens the closed telescope in the executable
context. -/
theorem MotivePassHeaderAt.recursorMotiveTypeDefEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {narrowTarget : VExpr} {nindices : Nat}
    {indices : Array Expr} {indexTargets : List VExpr}
    (Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope stats decl nindices)
    (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope R.mlctx.vlctx)
    (Hindices : List.Forall₂ (TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams) scope)
      indices.toList indexTargets)
    (hcanonical : indexTargets = indexBVarSpine nindices)
    (Hbound : FVarArrayIn current indices)
    (henv : R.venv = Hc.venv)
    (hindices : indices.size = nindices)
    (hfront : Hruntime.frontSourceDomains = Hsynthesis.indices)
    (Hframe : RecursorMotiveFrameWF R stats familyIdx indices elimLevel) :
    ∃ Hcanonical : RecursorMotiveClosedFrameWF R stats familyIdx
        indices elimLevel Hframe,
      R.venv.IsDefEqU
          (AddInductive.getRecLevelParams elimLevel c.lparams).length
          R.mlctx.vlctx.toCtx
          ((VExpr.wrapForalls Hframe.indexDomains
            (.forallE Hframe.majorTarget
              (.sort Hframe.resultLevel))).liftN indices.size 0)
          Hcanonical.motiveType ∧
        R.venv.IsDefEqU
          (AddInductive.getRecLevelParams elimLevel c.lparams).length
          (R.mlctx.vlctx.toCtx.drop indices.size)
          (VExpr.wrapForalls Hframe.indexDomains
            (.forallE Hframe.majorTarget
              (.sort Hframe.resultLevel)))
          (VExpr.wrapForalls Hruntime.frontExpandedDomains
            (.forallE Hframe.majorSourceTarget
              (.sort Hframe.resultLevel))) ∧
        Hcanonical.motiveType =
          (VExpr.wrapForalls Hruntime.frontExpandedDomains
            (.forallE Hframe.majorSourceTarget
              (.sort Hframe.resultLevel))).liftN indices.size 0 ∧
        (let familyBase := VExpr.mkApps
            (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
            (bvarSpine Hsynthesis.params.length)
         let canonicalMajor := VExpr.mkApps
            (familyBase.liftN Hsynthesis.indices.length 0)
            (bvarSpine Hsynthesis.indices.length)
         let canonicalBody :=
            VExpr.forallE canonicalMajor (.sort Hframe.resultLevel)
         canonicalBody.lift' Hruntime.shift =
            .forallE Hframe.majorSourceTarget
              (.sort Hframe.resultLevel)) := by
  rcases H.recursorCanonicalMotiveFrame Helim R Hsynthesis Hstats
      Hruntime henv hindices Hframe with
    ⟨Hcanonical, _hfamilyType, hmotiveType⟩
  let familyBase := VExpr.mkApps
    (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
    (bvarSpine Hsynthesis.params.length)
  let canonicalMajor := VExpr.mkApps
    (familyBase.liftN Hsynthesis.indices.length 0)
    (bvarSpine Hsynthesis.indices.length)
  let canonicalBody :=
    VExpr.forallE canonicalMajor (.sort Hframe.resultLevel)
  have hparameterCount : Hsynthesis.params.length = decl.nparams := by
    rw [Hsynthesis.parameterCount, H.parameterCount]
  have hfamilyScope : familyBase.liftN nindices 0 =
      VExpr.mkApps
        (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
        (decl.paramVars nindices) := by
    simp [familyBase, bvarSpine, VInductDecl.paramVars, VExpr.liftN,
      hparameterCount, Function.comp_def, Nat.add_comm]
  have hfamily := H.recursorFamilyPrefixEq Helim R Hsynthesis
    Hstats Hruntime henv Hframe
  have hfamilyFull :
      (familyBase.liftN nindices 0).lift' Hruntime.shift =
        Hframe.familyTarget := by
    rw [hfamilyScope]
    exact hfamily
  have hindexTargets := H.recursorIndexTargetsEq Helim R Hsynthesis
    Hruntime Hindices hcanonical Hbound Hframe
  have hcanonicalMajor : canonicalMajor.lift' Hruntime.shift =
      Hframe.majorSourceTarget := by
    dsimp only [canonicalMajor]
    rw [VExpr.lift'_mkApps]
    have hfamilyFull' :
        (familyBase.liftN Hsynthesis.indices.length 0).lift'
            Hruntime.shift = Hframe.familyTarget := by
      simpa [Hsynthesis.indexCount] using hfamilyFull
    rw [hfamilyFull']
    have hindexTargets' :
        (bvarSpine Hsynthesis.indices.length).map
            (fun target => target.lift' Hruntime.shift) =
          Hframe.familyIndexTargets := by
      simpa [bvarSpine, indexBVarSpine,
        List.map_reverse, Function.comp_def, Hsynthesis.indexCount] using
        hindexTargets
    rw [hindexTargets']
    exact Hframe.majorSourceEq.symm
  have hcanonicalBody : canonicalBody.lift' Hruntime.shift =
      .forallE Hframe.majorSourceTarget (.sort Hframe.resultLevel) := by
    simp [canonicalBody, hcanonicalMajor]
  rcases Hframe.majorType with ⟨majorLevel, hmajorType⟩
  have hmajorRuntime := Hframe.majorSourceDefEq.of_r R.checking.tr.wf
    R.mlctx_wf.tr.wf.toCtx hmajorType
  have hbodyRuntime : R.venv.IsDefEq
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      R.mlctx.vlctx.toCtx
      (.forallE Hframe.majorSourceTarget (.sort Hframe.resultLevel))
      (.forallE Hframe.majorTarget (.sort Hframe.resultLevel))
      (.sort (.imax majorLevel (.succ Hframe.resultLevel))) :=
    .forallEDF hmajorRuntime (VEnv.HasType.sort Hframe.resultLevelWF)
  have hbodyExpanded := hbodyRuntime.defeqDFC R.checking.tr.wf.ordered
    (Hruntime.context.defeqCtx.symm R.checking.tr.wf.ordered)
  have hfrontLength : Hruntime.frontExpandedDomains.length = indices.size := by
    rw [← Hruntime.front.length_eq, hfront, Hsynthesis.indexCount,
      ← hindices]
  have hcloseLE : indices.size ≤ Hruntime.expanded.toCtx.length := by
    rw [← hfrontLength]
    exact Hruntime.front.expandedLengthLE
  rcases Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.closeHeads
      Hruntime.context.defeqCtx indices.size hcloseLE hbodyExpanded with
    ⟨closedLevel, hclosed⟩
  have hexpandedPrefix :
      (Hruntime.expanded.toCtx.take indices.size).reverse =
        Hruntime.frontExpandedDomains := by
    rw [← hfrontLength]
    exact Hruntime.front.expandedPrefix
  have hruntimePrefix :
      (R.mlctx.vlctx.toCtx.take indices.size).reverse =
        Hframe.indexDomains := Hframe.indexDomains_eq.symm
  rw [hexpandedPrefix, hruntimePrefix] at hclosed
  have hclosedRuntime := hclosed.defeqDFC R.checking.tr.wf.ordered
    (Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.dropHeads
      Hruntime.context.defeqCtx indices.size)
  have hreopened := hclosedRuntime.weakN R.checking.tr.wf.ordered
    (Ctx.LiftN.zero (R.mlctx.vlctx.toCtx.take indices.size))
  have hruntimeLE : indices.size ≤ R.mlctx.vlctx.toCtx.length := by
    have hlength := Hframe.indexDomains_length
    rw [Hframe.indexDomains_eq, List.length_reverse,
      List.length_take] at hlength
    omega
  have hreopened' : R.venv.IsDefEq
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      R.mlctx.vlctx.toCtx
      ((VExpr.wrapForalls Hruntime.frontExpandedDomains
        (.forallE Hframe.majorSourceTarget
          (.sort Hframe.resultLevel))).liftN indices.size 0)
      ((VExpr.wrapForalls Hframe.indexDomains
        (.forallE Hframe.majorTarget
          (.sort Hframe.resultLevel))).liftN indices.size 0)
      ((VExpr.sort closedLevel).liftN indices.size 0) := by
    simpa [List.take_append_drop, Nat.min_eq_left hruntimeLE] using hreopened
  have hnatural := Hruntime.front.closeReopen canonicalBody
  have hnatural' :
      ((VExpr.wrapForalls Hsynthesis.indices canonicalBody).liftN
          indices.size 0).lift' Hruntime.shift =
        (VExpr.wrapForalls Hruntime.frontExpandedDomains
          (.forallE Hframe.majorSourceTarget
            (.sort Hframe.resultLevel))).liftN indices.size 0 := by
    simpa [hfront, Hsynthesis.indexCount, hindices, hfrontLength,
      hcanonicalBody] using hnatural
  have hmotiveType' : Hcanonical.motiveType =
      ((VExpr.wrapForalls Hsynthesis.indices canonicalBody).liftN
        indices.size 0).lift' Hruntime.shift := by
    simpa [familyBase, canonicalMajor, canonicalBody, hindices] using
      hmotiveType
  have hresult := hreopened'.symm
  rw [← hnatural', ← hmotiveType'] at hresult
  exact ⟨Hcanonical, ⟨_, hresult⟩, ⟨_, hclosedRuntime.symm⟩,
    hmotiveType'.trans hnatural', hcanonicalBody⟩

theorem MotivePassHeaderAt.recursorCanonicalFamilyApplication
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {narrowTarget : VExpr} {nindices : Nat}
    (Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (henv : R.venv = Hc.venv)
    (hnindices : nindices = H.target.numIndices) :
    R.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length scope.toCtx
      (VExpr.mkApps
        (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
        (indexBVarSpine (decl.nparams + H.target.numIndices)))
      narrowTarget := by
  have hhead := H.recursorConstHasType Helim R henv
  have hheadTelescope : R.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length []
      (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
      (VExpr.wrapForalls (Hsynthesis.params ++ Hsynthesis.indices)
        narrowTarget) := by
    apply hhead.defeqU_r R.checking.tr.wf (by trivial)
    exact ⟨Hsynthesis.exprType, Hsynthesis.header⟩
  have happ := VEnv.HasType.mkApps_wrapForalls_bvarSpine
    R.checking.tr.wf.ordered hheadTelescope
  have hparamCount : Hsynthesis.params.length = decl.nparams := by
    rw [Hsynthesis.parameterCount, H.parameterCount]
  have hindexCount : Hsynthesis.indices.length = H.target.numIndices := by
    rw [Hsynthesis.indexCount, hnindices]
  simpa [List.reverse_append, Hsynthesis.scopeCtx, hparamCount,
    hindexCount, indexBVarSpine, VExpr.liftN, ← List.map_reverse] using happ

/-- Recursor-universe form of the family application theorem. -/
theorem MotivePassHeaderAt.recursorScopedFamilyApplication
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {type : VExpr}
    {indices : Array Expr} {indexTargets : List VExpr} {nindices : Nat}
    (Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope type
        stats.params.size nindices)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope stats decl nindices)
    (Hindices : List.Forall₂ (TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams) scope)
      indices.toList indexTargets)
    (hreplay : indexTargets.length = nindices)
    (hcanonical : indexTargets = indexBVarSpine nindices)
    (harity : (indices.size == stats.nindices[familyIdx]!) = true)
    (henv : R.venv = Hc.venv) :
    TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams) scope
      (mkAppN (mkAppN stats.indConsts[familyIdx]! stats.params) indices)
      (VExpr.mkApps
        (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
        (indexBVarSpine (decl.nparams + H.target.numIndices))) ∧
    R.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length scope.toCtx
      (VExpr.mkApps
        (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
        (indexBVarSpine (decl.nparams + H.target.numIndices))) type ∧
    R.venv.IsType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length scope.toCtx
      (VExpr.mkApps
        (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
        (indexBVarSpine (decl.nparams + H.target.numIndices))) := by
  have htranslated : indices.size = indexTargets.length := by
    simpa using List.Forall₂.length_eq Hindices
  have hguard : indices.size = stats.nindices[familyIdx]! := by
    simpa using harity
  have hfamily : stats.nindices[familyIdx]! = H.target.numIndices := by
    simp [Array.getElem!_eq_getD, H.indexCount]
  have hnindices : nindices = H.target.numIndices := by omega
  have hargs := H.recursorScopedArguments R Hstats Hindices
    hreplay hcanonical harity
  have hhead := H.recursorIndConstTranslation Helim R Hstats henv
  have happ := H.recursorCanonicalFamilyApplication Helim R Hsynthesis henv
    hnindices
  have huvars : H.target.uvars = decl.uvars := by
    rw [H.sourceTranslation.uvars, H.checked.uvars]
  have htargetWF : H.target.toVConstant.WF Hc.venv :=
    H.sourceTranslation.wf
  have hshape : decl.TypeShape Hc.venv
      H.checked.headers.params H.target :=
    H.shape
  rcases typeShape_forallAritySort huvars Hc.checking.tr.wf htargetWF
      hshape with
    ⟨functionType, typeLevel, hfunctionType, hfunctionShape⟩
  have hlevelsWF := H.recursorAbstractLevels_wf Helim
  have hlevelsLength := H.recursorAbstractLevels_length Helim
  have hfunctionTypeInst := hfunctionType.instL hlevelsWF
  have hlookup : R.venv.constants H.target.name =
      some H.target.toVConstant := by
    simpa [henv] using H.targetLookup
  have hconstBase := VEnv.HasType.const (env := R.venv)
    (U := (AddInductive.getRecLevelParams elimLevel c.lparams).length)
    (Γ := scope.toCtx) hlookup hlevelsWF hlevelsLength
  have hconstType : R.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length scope.toCtx
      (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
      (functionType.instL (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim)) := by
    have hfunctionTypeInst' : R.venv.IsDefEq
        (AddInductive.getRecLevelParams elimLevel c.lparams).length []
        (H.target.type.instL (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
        (functionType.instL (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
        (.sort (typeLevel.inst (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))) := by
      simpa [henv, VExpr.instL] using hfunctionTypeInst
    exact (hfunctionTypeInst'.weak0 R.checking.tr.wf.ordered).defeq hconstBase
  have happType : R.venv.IsType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length scope.toCtx
      (VExpr.mkApps
        (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
        (indexBVarSpine (decl.nparams + H.target.numIndices))) := by
    apply VEnv.HasType.mkApps_isType R.checking.tr.wf
      Hsynthesis.scopeWF.toCtx hconstType
    · simpa [indexBVarSpine] using
        hfunctionShape.instL (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim)
    · exact ⟨type, happ⟩
  have htr : TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams) scope
      (Expr.mkAppList stats.indConsts[familyIdx]!
        (stats.params.toList ++ indices.toList))
      (VExpr.mkApps
        (.const H.target.name (MotivePassHeaderAt.recursorAbstractLevels c.lparams Helim))
        (indexBVarSpine (decl.nparams + H.target.numIndices))) :=
    checkPositivityStep.TrExprS.mkAppList R.checking.tr.wf.orderedStrong
      Hsynthesis.scopeWF.toCtx hhead hargs ⟨_, happ⟩
  refine ⟨?_, happ, happType⟩
  simpa [Expr.mkAppN_eq_mkAppList, Expr.mkAppList_append] using htr

/-- The executable family application has a checked unannotated
domain directly in the current recursor context. -/
theorem MotivePassHeaderAt.recursorMajorDomain
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MotivePassHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {type : VExpr}
    {indices : Array Expr} {indexTargets : List VExpr} {nindices : Nat}
    (Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope type
        stats.params.size nindices)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope stats decl nindices)
    (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope R.mlctx.vlctx)
    (Hindices : List.Forall₂ (TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams) scope)
      indices.toList indexTargets)
    (hreplay : indexTargets.length = nindices)
    (hcanonical : indexTargets = indexBVarSpine nindices)
    (harity : (indices.size == stats.nindices[familyIdx]!) = true)
    (henv : R.venv = Hc.venv)
    (hconsume : RecursorConsumeTypeAnnotationsCompat) :
    ∃ sourceTarget consumedTarget,
      R.UnannotatedDomain
        (mkAppN (mkAppN stats.indConsts[familyIdx]! stats.params) indices)
        sourceTarget consumedTarget := by
  rcases H.recursorScopedFamilyApplication Helim R Hsynthesis Hstats
      Hindices hreplay hcanonical harity henv with
    ⟨hnarrow, _happ, hnarrowType⟩
  rcases Hruntime.transportType R.checking.tr.wf hnarrow hnarrowType with
    ⟨sourceTarget, hsource, hsourceType⟩
  rcases hconsume current _ R hsource hsourceType with
    ⟨consumedTarget, Hconsumed⟩
  exact ⟨sourceTarget, consumedTarget, Hconsumed⟩

/-- Construct the major/motive frame from an opened header in any
existing recursor context.  Earlier family frames of a mutual block remain in
the ambient prefix, while only this family's recent index suffix is closed into
the motive telescope. -/
theorem MotivePassHeaderAt.recursorFrame
    {base root current : AddInductive.Context} {Hbase : ContextWF base}
    (H : MotivePassHeaderAt Hbase stats decl depth source familyIdx)
    {elimLevel : Level}
    (Helim : AddInductive.AdmissibleElimLevel base.lparams elimLevel)
    (Rroot : RecursorContextWF root
      (AddInductive.getRecLevelParams elimLevel base.lparams))
    (Rindices : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel base.lparams))
    {scope : VLCtx} {type : VExpr}
    {indices : Array Expr} {indexTargets : List VExpr} {nindices : Nat}
    (Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        Rindices.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        (H.recursorTargetSkeleton Helim) scope type
        stats.params.size nindices)
    (Hstats : RecursorValidAppStatsWF Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams)
      scope stats decl nindices)
    (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding
      Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams)
      scope Rindices.mlctx.vlctx)
    (Hindices : List.Forall₂ (TrExprS Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams) scope)
      indices.toList indexTargets)
    (hreplay : indexTargets.length = nindices)
    (hcanonical : indexTargets = indexBVarSpine nindices)
    (harity : (indices.size == stats.nindices[familyIdx]!) = true)
    (henv : Rindices.venv = Hbase.venv)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (Hrecent : RecursorFVarSuffix Rroot Rindices indices) :
    Nonempty (RecursorMotiveFrameWF Rindices stats familyIdx indices
      elimLevel) := by
  let majorTy :=
    ((mkAppN (mkAppN stats.indConsts[familyIdx]! stats.params)
      indices).consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper)
  rcases H.recursorMajorDomain Helim Rindices Hsynthesis Hstats
      Hruntime Hindices hreplay hcanonical harity henv hconsume with
    ⟨sourceTarget, majorTarget, Hdom⟩
  have hsourceList : TrExprS Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams)
      Rindices.mlctx.vlctx
      (Expr.mkAppList
        (mkAppN stats.indConsts[familyIdx]! stats.params) indices.toList)
      sourceTarget := by
    simpa only [← Expr.mkAppN_eq_mkAppList] using Hdom.source
  rcases checkPositivityStep.TrExprS.mkAppList_inv hsourceList with
    ⟨familyTarget, familyIndexTargets, hfamily, hfamilyIndices,
      hsourceTarget⟩
  let Rmajor := Rindices.withLocalDecl (name := `t) (bi := .default)
    Hdom.unannotated Hdom.isType
  let cMajor : AddInductive.Context := { current with
    ngen := current.ngen.next
    lctx := current.lctx.mkLocalDecl ⟨current.ngen.curr⟩ `t majorTy .default }
  let major := Expr.fvar ⟨current.ngen.curr⟩
  let majorBody := cMajor.lctx.mkForall #[major] (.sort elimLevel)
  let motiveTy := cMajor.lctx.mkForall indices majorBody
  rcases Helim.sortType (env := Rmajor.venv) (Δ := Rmajor.mlctx.vlctx) with
    ⟨sortLevel, hsort, hsortType⟩
  have hone : 1 ≤ Rmajor.mlctx.length := by
    dsimp only [Rmajor, RecursorContextWF.withLocalDecl, RecursorContextWF.withCheckedLocalDecl, RecursorContextWF.withCheckedLocalDeclOn]
    simp
  have hmajorRecent : #[major].toList.reverse =
      (Rmajor.mlctx.fvarRevList 1 hone).map Expr.fvar := by
    dsimp only [major, Rmajor, RecursorContextWF.withLocalDecl, RecursorContextWF.withCheckedLocalDecl, RecursorContextWF.withCheckedLocalDeclOn]
    simp
  have hmajorClosed := Rmajor.mkForallRecent hsort hsortType 1 hone #[major]
    hmajorRecent
  have hmajorClosed' :
      TrExprS Rindices.venv
          (AddInductive.getRecLevelParams elimLevel base.lparams)
          Rindices.mlctx.vlctx majorBody
          (Rmajor.mlctx.mkForall' 1 hone (.sort sortLevel)) ∧
        Rindices.venv.IsType
          (AddInductive.getRecLevelParams elimLevel base.lparams).length
          Rindices.mlctx.vlctx.toCtx
          (Rmajor.mlctx.mkForall' 1 hone (.sort sortLevel)) := by
    simpa only [majorBody, Rmajor, RecursorContextWF.withLocalDecl, RecursorContextWF.withCheckedLocalDecl, RecursorContextWF.withCheckedLocalDeclOn,
      TypeChecker.MLCtx.dropN] using hmajorClosed
  let hindicesSize := Hrecent.size_le
  have hindicesRecent : indices.toList.reverse =
      (Rindices.mlctx.fvarRevList indices.size hindicesSize).map Expr.fvar :=
    Hrecent.reverse_eq
  have hmotiveClosed := Rindices.mkForallRecent hmajorClosed'.1
    hmajorClosed'.2 indices.size hindicesSize indices hindicesRecent
  let hmajorLE := BindingContextLE.withLocalDecl current
    Rindices.toBindingContextWF `t majorTy .default
  have hmotiveConcrete : motiveTy =
      current.lctx.mkForall indices majorBody := by
    dsimp [motiveTy]
    exact Hrecent.toFVarArrayAfter.toFVarArrayIn.mkForall_mono
      hmajorLE majorBody
  rw [← hmotiveConcrete] at hmotiveClosed
  let Windices := Rindices.onlyLams.dropN_fvlift indices.size hindicesSize
  have hmotiveAtIndices := hmotiveClosed.1.weakFV
    Rindices.checking.tr.wf.orderedStrong Windices Rindices.mlctx_wf.tr.wf
  have hmotiveTypeAtIndices := hmotiveClosed.2.weakN
    Rindices.checking.tr.wf.ordered Windices.toCtx
  let Wmajor : VLCtx.FVLift Rindices.mlctx.vlctx Rmajor.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  have hmotiveAtMajor := hmotiveAtIndices.weakFV
    Rmajor.checking.tr.wf.orderedStrong Wmajor Rmajor.mlctx_wf.tr.wf
  have hmotiveTypeAtMajor := hmotiveTypeAtIndices.weakN
    Rmajor.checking.tr.wf.ordered Wmajor.toCtx
  have hmajorConcrete : majorBody =
      Rmajor.mlctx.mkForall 1 hone (Expr.sort elimLevel) := by
    dsimp only [majorBody]
    rw [← Rmajor.lctx_eq]
    exact Rmajor.mlctx_wf.mkForall_eq 1 hone hmajorRecent trivial
  have hsortConsume : ((Expr.sort elimLevel).consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper) =
      Expr.sort elimLevel := by
    apply Expr.consumeTypeAnnotationsVerified_eq_self <;> rfl
  have hconsumeMajor : (majorBody.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper) = majorBody := by
    rw [hmajorConcrete]
    exact Rmajor.onlyLams.mkForall_consumeTypeAnnotations_eq_self
      1 hone hsortConsume
  have hmotiveMkForall : motiveTy =
      Rindices.mlctx.mkForall indices.size hindicesSize majorBody := by
    rw [hmotiveConcrete]
    exact (congrArg (fun lctx => lctx.mkForall indices majorBody)
      Rindices.lctx_eq).symm.trans
        (Rindices.mlctx_wf.mkForall_eq indices.size hindicesSize
          hindicesRecent (hmajorConcrete ▸ Rmajor.mlctx_wf.mkForall_closed 1 hone trivial))
  have hconsumeMotive : (motiveTy.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper) = motiveTy := by
    rw [hmotiveMkForall]
    exact Rindices.onlyLams.mkForall_consumeTypeAnnotations_eq_self
      indices.size hindicesSize hconsumeMajor
  refine ⟨{
    familyTarget := familyTarget
    familyTr := hfamily
    familyIndexTargets := familyIndexTargets
    familyIndicesTr := hfamilyIndices
    majorSourceTarget := sourceTarget
    majorSourceEq := hsourceTarget
    majorSourceDefEq := by
      rcases Hdom.source_defeq with ⟨level, heq⟩
      exact ⟨.sort level, heq⟩
    majorTarget := majorTarget
    majorTr := Hdom.unannotated
    majorType := Hdom.isType
    indexDomains := MLCtxForallDomains Rindices.mlctx indices.size
      hindicesSize
    indexDomains_length :=
      Rindices.onlyLams.forallDomains_length indices.size hindicesSize
    indexDomains_eq :=
      Rindices.onlyLams.forallDomains_eq_take_reverse indices.size
        hindicesSize
    resultLevel := sortLevel
    resultLevelWF := by
      cases hsort with
      | sort hlevel => exact .of_ofLevel hlevel
    resultLevelOf := by
      cases hsort with
      | sort hlevel => exact hlevel
    motiveTarget :=
      ((Rindices.mlctx.mkForall' indices.size hindicesSize
        (Rmajor.mlctx.mkForall' 1 hone (.sort sortLevel))).liftN
          indices.size 0).liftN 1 0
    motiveTarget_eq := by
      rw [TypeChecker.MLCtx.mkForall'_eq_wrapForalls,
        TypeChecker.MLCtx.mkForall'_eq_wrapForalls]
      have hmajorDomains : MLCtxForallDomains Rmajor.mlctx 1 hone =
          [majorTarget] := by
        dsimp only [Rmajor, RecursorContextWF.withLocalDecl, RecursorContextWF.withCheckedLocalDecl, RecursorContextWF.withCheckedLocalDeclOn]
        simp only [MLCtxForallDomains, List.nil_append]
      rw [hmajorDomains]
      rfl
    motiveClosed := ?_
    motiveTr := ?_
    motiveType := ?_
    motiveSourceEq := ?_ }⟩
  · refine ⟨hindicesSize,
      Rindices.mlctx.mkForall' indices.size hindicesSize
        (Rmajor.mlctx.mkForall' 1 hone (.sort sortLevel)), ?_, ?_, ?_⟩
    · rw [hconsumeMotive]
      exact hmotiveClosed.1
    · exact hmotiveClosed.2
    · rw [TypeChecker.MLCtx.mkForall'_eq_wrapForalls,
        TypeChecker.MLCtx.mkForall'_eq_wrapForalls]
      have hmajorDomains : MLCtxForallDomains Rmajor.mlctx 1 hone =
          [majorTarget] := by
        dsimp only [Rmajor, RecursorContextWF.withLocalDecl, RecursorContextWF.withCheckedLocalDecl, RecursorContextWF.withCheckedLocalDeclOn]
        simp only [MLCtxForallDomains, List.nil_append]
      rw [hmajorDomains]
      rfl
  · change TrExprS Rmajor.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams)
      Rmajor.mlctx.vlctx (motiveTy.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper) _
    rw [hconsumeMotive]
    exact hmotiveAtMajor
  · change Rmajor.venv.IsType
      (AddInductive.getRecLevelParams elimLevel base.lparams).length
      Rmajor.mlctx.vlctx.toCtx _
    exact hmotiveTypeAtMajor
  · exact hconsumeMotive

/-- One cached-parameter substitution interpreted directly under the
recursor universe list. -/
theorem recursorParameterStep
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    {stats : AddInductive.InductiveStats} {i : Nat}
    {name : Name} {dom body : Expr} {bi : BinderInfo}
    {current paramTarget paramType : VExpr}
    (htype : TrExpr R.venv recLparams R.mlctx.vlctx
      (.forallE name dom body bi) current)
    (hparam : TrExprS R.venv recLparams R.mlctx.vlctx
      stats.params[i]! paramTarget)
    (hparamType : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
      paramTarget paramType)
    (hmatch : ∀ {domainTarget},
      TrExprS R.venv recLparams R.mlctx.vlctx dom domainTarget →
      R.venv.IsDefEqU recLparams.length R.mlctx.vlctx.toCtx
        domainTarget paramType) :
    ∃ bodyTarget,
      TrExprS R.venv recLparams R.mlctx.vlctx
        (body.instantiate1 stats.params[i]!) bodyTarget ∧
      R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx bodyTarget := by
  rcases TrExpr.forallE_source htype with
    ⟨domainTarget, sourceBody, hdom, hbody, _hdomType, hbodyType,
      _hcurrent⟩
  have heq := hmatch hdom
  have hparamType' := hparamType.defeqU_r R.checking.tr.wf
    R.mlctx_wf.tr.wf.toCtx heq.symm
  refine ⟨sourceBody.inst paramTarget,
    R.instantiateDefEq hbody hparam hparamType heq, ?_⟩
  exact hbodyType.instN R.checking.tr.wf.ordered .zero hparamType'

/-- Discharge a recursor-universe cached-parameter step from the
rebased abstract family header and the parameter suffix. -/
theorem parameterStepOfCheckedRecursorHeader
    {base current : AddInductive.Context} {Hbase : ContextWF base}
    (H : MotivePassHeaderAt Hbase stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel base.lparams elimLevel)
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel base.lparams))
    {Hsuffix : RecursorParameterContextSuffix R stats runtimeDepth}
    {i : Nat} {name : Name} {dom body : Expr} {bi : BinderInfo}
    {currentTarget currentDomain currentBody : VExpr}
    (Hscope : RecursorReusedParameterScope Hsuffix i
      (.forallE name dom body bi))
    (Hsynthesis :
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        R.venv (AddInductive.getRecLevelParams elimLevel base.lparams)
        (H.recursorTargetSkeleton Helim) Hscope.older
        (.forallE currentDomain currentBody) i 0)
    (hi : i < stats.params.size)
    (henv : R.venv = Hbase.venv)
    (hctx : VEnv.IsDefEqCtx R.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams).length []
      (H.recursorParams Helim).reverse Hsuffix.parameterDecls.toCtx)
    (htypeNarrow : TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams) Hscope.older
      (.forallE name dom body bi) (.forallE currentDomain currentBody))
    (htype : TrExpr R.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams) R.mlctx.vlctx
      (.forallE name dom body bi) currentTarget) :
    ∃ bodyTarget,
      TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams) R.mlctx.vlctx
        (body.instantiate1 stats.params[i]!) bodyTarget ∧
      R.venv.IsType
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        R.mlctx.vlctx.toCtx bodyTarget := by
  rcases Hscope.typing with
    ⟨_paramTy, paramTy', param', _hget, _hparamTy, hparamTyEq,
      hparam, hparamType⟩
  have hnarrowMatch := H.recursorCurrentDomainDefEq Helim Hscope
    Hsynthesis hi henv hctx
  cases htypeNarrow with
  | forallE _hdomType _hbodyType hdomNarrow _hbodyNarrow =>
    apply recursorParameterStep R htype hparam hparamType
    intro domainTarget hdomFull
    have hdomWeak := hdomNarrow.weakFV R.checking.tr.wf.orderedStrong
      Hscope.olderLift R.mlctx_wf.tr.wf
    have hdomainToNarrow := hdomFull.uniq R.checking.tr.wf
      (.refl R.checking.tr.wf R.mlctx_wf.tr.wf) hdomWeak
    have hmatchFull :=
      VEnv.IsDefEqU.weakN R.checking.tr.wf.ordered Hscope.olderLift.toCtx hnarrowMatch
    have hresult := hdomainToNarrow.trans R.checking.tr.wf
      R.mlctx_wf.tr.wf.toCtx hmatchFull
    rw [hparamTyEq]
    simpa [Nat.succ_eq_add_one, VExpr.liftN_liftN, Nat.add_comm]
      using hresult

/-- `whnf` runs are recorded by pairing a run with its own equation. -/
theorem _root_.Except.WF.self {ε α : Type} (x : Except ε α) :
    x.WF fun a => x = .ok a := fun _ h => h

theorem _root_.Lean4Lean.VerifyInductive.ExprArrayFVarIds_push_fvar
    (xs : Array Expr) (x : FVarId) :
    ExprArrayFVarIds (xs.push (.fvar x)) = ExprArrayFVarIds xs ++ [x] := by
  simp [ExprArrayFVarIds, recursorFVarId]

/-- A cached parameter is a variable of the context carrying the suffix. -/
theorem _root_.Lean4Lean.VerifyInductive.RecursorParameterContextSuffix.mem_lctx_of_mem_params
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (Hsuffix : RecursorParameterContextSuffix R stats depth) {fv : FVarId}
    (h : fv ∈ ExprArrayFVarIds stats.params) : fv ∈ c.lctx.fvars := by
  rw [← R.lctx_eq, R.mlctx_wf.tr.fvars_eq, Hsuffix.context, VLCtx.fvars_append,
    Hsuffix.parameterDecls_fvars]
  exact List.mem_append_right _ (List.mem_reverse.mpr h)

/-- The variable introduced by a one-declaration extension is declared with
the given type. -/
theorem _root_.Lean4Lean.VerifyInductive.BindingContextWF.find?_mkLocalDecl_self
    {c : AddInductive.Context} (Hc : BindingContextWF c) (name : Name)
    (ty : Expr) (bi : BinderInfo) :
    (c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi).find? ⟨c.ngen.curr⟩ =
      some (.cdecl c.lctx.decls.size ⟨c.ngen.curr⟩ name ty bi .default) := by
  simp [LocalContext.mkLocalDecl, LocalContext.find?,
    Hc.wf.map_wf.find?_insert]

theorem _root_.Lean4Lean.VerifyInductive.mem_fvars_mkLocalDecl_self
    (c : AddInductive.Context) (name : Name) (ty : Expr) (bi : BinderInfo) :
    (⟨c.ngen.curr⟩ : FVarId) ∈
      (c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi).fvars := by
  simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
    List.map_cons, LocalDecl.fvarId, List.mem_cons]
  exact Or.inl trivial

set_option maxRecDepth 4000 in
/-- Open the index suffix wholly under the recursor universe list.
The cached-parameter telescope remains a suffix of every generated
context, while the abstract header telescope in the checking scope and the
executable context grow in lockstep by one checked index declaration. -/
theorem continueRecursorIndexTelescopeTyping {alpha : Type}
    (stats : AddInductive.InductiveStats)
    (k : Array Expr → AddInductive.M alpha)
    {Q : alpha → Prop}
    {base root : AddInductive.Context} {Hbase : ContextWF base}
    {decl : VInductDecl} {depth familyIdx : Nat} {source : InductiveType}
    (H : MotivePassHeaderAt Hbase stats decl depth source familyIdx)
    {elimLevel : Level}
    (Helim : AddInductive.AdmissibleElimLevel base.lparams elimLevel)
    (Rroot : RecursorContextWF root
      (AddInductive.getRecLevelParams elimLevel base.lparams))
    {rootParameterDecls : VLCtx}
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (Hk : ∀ {current : AddInductive.Context} {runtimeDepth : Nat}
      (R : RecursorContextWF current
        (AddInductive.getRecLevelParams elimLevel base.lparams))
      (_henv : R.venv = Hbase.venv)
      (Hsuffix : RecursorParameterContextSuffix R stats runtimeDepth)
      (_hparameterDecls :
        Hsuffix.parameterDecls = rootParameterDecls)
      {type : Expr} {fullTarget narrowTarget : VExpr} {scope : VLCtx}
      {nindices : Nat} {indices originTypes : Array Expr}
      {indexTargets : List VExpr},
      (Hsynthesis :
        checkInductiveTypes.loopType.ScopedHeaderTelescope
          R.venv (AddInductive.getRecLevelParams elimLevel base.lparams)
          (H.recursorTargetSkeleton Helim) scope narrowTarget
          stats.params.size nindices) →
      Hsynthesis.params.reverse = rootParameterDecls.toCtx →
      scope.drop nindices = rootParameterDecls →
      RecursorValidAppStatsWF R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope stats decl nindices →
      RecursorValidAppStatsWF R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        R.mlctx.vlctx stats decl runtimeDepth →
      (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope R.mlctx.vlctx) →
      Hruntime.frontSourceDomains = Hsynthesis.indices →
      VLCtx.IsDefEq R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        scope R.chk.vlctx →
      TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope type narrowTarget →
      FVarsIn (· ∈ scope.fvars) type →
      type.levelParamsIn base.lparams = true →
      R.typeChecker.UniverseScope base.lparams (· ∈ scope.fvars) →
      TrExpr R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        R.mlctx.vlctx type fullTarget →
      R.venv.IsType
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        R.mlctx.vlctx.toCtx fullTarget →
      List.Forall₂ (TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        R.mlctx.vlctx) indices.toList indexTargets →
      List.Forall₂ (TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope) indices.toList indexTargets →
      indexTargets.length = nindices →
      indexTargets = indexBVarSpine nindices →
      FVarArrayBinderTypes current indices originTypes →
      TrBinderTypes R originTypes →
      RecursorFVarSuffix Rroot R indices →
      IndexTelescopeRun stats current source.type stats.params.size type
        indices →
      (k indices current).WF Q) :
    ∀ {current : AddInductive.Context} {runtimeDepth : Nat}
      (R : RecursorContextWF current
        (AddInductive.getRecLevelParams elimLevel base.lparams))
      (_henv : R.venv = Hbase.venv)
      (Hsuffix : RecursorParameterContextSuffix R stats runtimeDepth)
      (_hparameterDecls : Hsuffix.parameterDecls = rootParameterDecls)
      type fullTarget narrowTarget scope nindices indices originTypes
        indexTargets fuel,
      (Hsynthesis :
        checkInductiveTypes.loopType.ScopedHeaderTelescope
          R.venv (AddInductive.getRecLevelParams elimLevel base.lparams)
          (H.recursorTargetSkeleton Helim) scope narrowTarget
          stats.params.size nindices) →
      Hsynthesis.params.reverse = rootParameterDecls.toCtx →
      scope.drop nindices = rootParameterDecls →
      RecursorValidAppStatsWF R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope stats decl nindices →
      RecursorValidAppStatsWF R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        R.mlctx.vlctx stats decl runtimeDepth →
      (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope R.mlctx.vlctx) →
      Hruntime.frontSourceDomains = Hsynthesis.indices →
      VLCtx.IsDefEq R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        scope R.chk.vlctx →
      TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope type narrowTarget →
      FVarsIn (· ∈ scope.fvars) type →
      type.levelParamsIn base.lparams = true →
      R.typeChecker.UniverseScope base.lparams (· ∈ scope.fvars) →
      TrExpr R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        R.mlctx.vlctx type fullTarget →
      R.venv.IsType
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        R.mlctx.vlctx.toCtx fullTarget →
      List.Forall₂ (TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        R.mlctx.vlctx) indices.toList indexTargets →
      List.Forall₂ (TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope) indices.toList indexTargets →
      indexTargets.length = nindices →
      indexTargets = indexBVarSpine nindices →
      FVarArrayBinderTypes current indices originTypes →
      TrBinderTypes R originTypes →
      RecursorFVarSuffix Rroot R indices →
      IndexTelescopeRun stats current source.type stats.params.size type
        indices →
      (∀ fv ∈ scope.fvars, fv ∈ ExprArrayFVarIds stats.params ∨
        fv ∈ ExprArrayFVarIds indices) →
      (AddInductive.mkRecInfos.loopArgs1 stats type stats.params.size
        indices fuel k current).WF Q
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
      intro _ h
      simp [AddInductive.mkRecInfos.loopArgs1] at h
  | current, runtimeDepth, R, henv, Hsuffix, hparameterDecls, type,
      fullTarget, narrowTarget,
      scope, nindices, indices, originTypes, indexTargets, fuel + 1, Hsynthesis,
      hcanonicalParams, hscopeBase, HnarrowStats, Hstats, Hruntime, hfront, halign,
      htypeNarrow,
      htypeFVars, htypeU, hscopeU, htypeFull,
      htypeFullType, Hindices, HnarrowIndices, hindexCount, hcanonical,
      Horigins, HoriginTypes, Hrecent, Htrace, hscopeFVars => by
      cases type with
      | forallE name dom body bi =>
        rw [AddInductive.mkRecInfos.loopArgs1]
        have hparam : ¬ stats.params.size < stats.params.size := by omega
        rw [if_neg hparam]
        cases htypeNarrow with
        | @forallE indexType narrowBody _ _ _ _ _
            hdomType _hbodyType hdomNarrow hbodyNarrow =>
          rcases TrExpr.forallE_source htypeFull with
            ⟨sourceDom, fullBody, hdomFull, hbodyFull, hdomFullType,
              hbodyFullType, _hfullCurrent⟩
          rcases hconsume current _ R hdomFull hdomFullType with
            ⟨consumedDom, Hdom⟩
          rcases Hdom.body R hbodyFull with
            ⟨consumedBody, hbodyConsumed, hbodyEq⟩
          have henvWF := R.checking.tr.wf
          have hscopeWF₀ := halign.wf
          rcases halign.forallE_align henvWF hdomNarrow hdomType hbodyNarrow with
            ⟨domC, bodyC, hdomC, hdomCType, hdomCU, hbodyC, _⟩
          rcases hconsume _ _ R.atCheckLCtx hdomC hdomCType with ⟨consumed₀, Hdom₀⟩
          rcases Hdom₀.body R.atCheckLCtx hbodyC with
            ⟨consumedBody₀, hbodyConsumed₀, _hbodyEq₀⟩
          refine withCheckedLocalDecl.recursorWF (name := name) (bi := bi) (Q := Q)
            R Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType ?_
          let R' := R.withCheckedLocalDecl (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType
          let Hsuffix' := Hsuffix.withAmbientChecked (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType
          let W : VLCtx.FVLift R.mlctx.vlctx R'.mlctx.vlctx 0 1 0 :=
            .skip_fvar _ _ .refl
          have HindicesWeak : List.Forall₂
              (TrExprS R'.venv
                (AddInductive.getRecLevelParams elimLevel base.lparams)
                R'.mlctx.vlctx)
              indices.toList
              (indexTargets.map fun result => result.liftN 1 0) := by
            apply checkPositivityStep.forall₂_map_right Hindices
            intro source result Hsource
            exact Hsource.weakFV R.checking.tr.wf.orderedStrong W
              R'.mlctx_wf.tr.wf
          have Hindex : TrExprS R'.venv
              (AddInductive.getRecLevelParams elimLevel base.lparams)
              R'.mlctx.vlctx (.fvar ⟨current.ngen.curr⟩) (.bvar 0) := by
            exact TrExprS.fvar (A := consumedDom.lift) (by
              change VLCtx.find? ((some (⟨current.ngen.curr⟩,
                (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper).fvarsList), .vlam consumedDom) ::
                  R.mlctx.vlctx) (Sum.inr ⟨current.ngen.curr⟩) = _
              simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
                VLocalDecl.value, VLocalDecl.type])
          have Hindices' : List.Forall₂
              (TrExprS R'.venv
                (AddInductive.getRecLevelParams elimLevel base.lparams)
                R'.mlctx.vlctx)
              (indices.push (.fvar ⟨current.ngen.curr⟩)).toList
              ((indexTargets.map fun result => result.liftN 1 0) ++
                [.bvar 0]) := by
            simpa using List.Forall₂.append' HindicesWeak
              (.cons Hindex .nil)
          have hopened := R.instantiateFresh (name := name) (bi := bi)
            Hdom.unannotated Hdom.isType hbodyConsumed
          have hctx : VLCtx.IsDefEq R.venv
              (AddInductive.getRecLevelParams elimLevel base.lparams).length
              ((none, .vlam sourceDom) :: R.mlctx.vlctx)
              ((none, .vlam consumedDom) :: R.mlctx.vlctx) :=
            VLCtx.IsDefEq.cons
              (.refl R.checking.tr.wf R.mlctx_wf.tr.wf) nofun
              (.vlam Hdom.source_defeq.choose_spec)
          have hsourceBodyType : R'.venv.IsType
              (AddInductive.getRecLevelParams elimLevel base.lparams).length
              R'.mlctx.vlctx.toCtx fullBody := by
            simpa only [R', RecursorContextWF.withLocalDecl_venv, RecursorContextWF.withCheckedLocalDecl_venv, RecursorContextWF.withCheckedLocalDeclOn_venv,
              RecursorContextWF.withLocalDecl_toCtx, RecursorContextWF.withCheckedLocalDecl_toCtx, RecursorContextWF.withCheckedLocalDeclOn_toCtx, VLCtx.toCtx] using
              hbodyFullType.defeqDFC R.checking.tr.wf.ordered hctx.defeqCtx
          have hbodyEq' := Hdom.bodyDefEqUnannotated R hbodyEq
          have hconsumedBodyType : R'.venv.IsType
              (AddInductive.getRecLevelParams elimLevel base.lparams).length
              R'.mlctx.vlctx.toCtx consumedBody := by
            apply hsourceBodyType.defeqU_l R'.checking.tr.wf
              R'.mlctx_wf.tr.wf.toCtx
            simpa only [R', RecursorContextWF.withLocalDecl_venv, RecursorContextWF.withCheckedLocalDecl_venv, RecursorContextWF.withCheckedLocalDeclOn_venv,
              RecursorContextWF.withLocalDecl_toCtx, RecursorContextWF.withCheckedLocalDecl_toCtx, RecursorContextWF.withCheckedLocalDeclOn_toCtx, VLCtx.toCtx] using
              hbodyEq'
          have hdeps : (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper).fvarsList ⊆ scope.fvars :=
            (fvarsIn_iff.mp
              (Expr.consumeTypeAnnotationsVerified_fvarsIn htypeFVars.1)).1
          rcases Hruntime.recursorUnannotatedDomain R Hdom hdomNarrow with
            ⟨_domainLevel, hdomain⟩
          let Hruntime' :
              checkInductiveTypes.loopType.FrontScopeEmbedding
                R'.venv
                (AddInductive.getRecLevelParams elimLevel base.lparams)
                ((some (⟨current.ngen.curr⟩,
                  (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper).fvarsList),
                  .vlam indexType) :: scope)
                R'.mlctx.vlctx :=
            Hruntime.withIndex R'.mlctx_wf.tr.wf hdeps name bi dom
              hdomNarrow hdomain hdomType
          have halign' := R.alignedBinder (name := name) (bi := bi) halign
            Hdom Hdom₀ hdomNarrow hdomType hdeps
          have hscopeWF := halign'.wf
          have hfreshScope : (⟨current.ngen.curr⟩ : FVarId) ∉ scope.fvars := by
            intro hmem
            rw [halign.fvars] at hmem
            exact R.current_not_mem (R.check.embed.fvars_subset hmem)
          let Wnarrow : VLCtx.FVLift scope
              ((some (⟨current.ngen.curr⟩,
                (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper).fvarsList),
                .vlam indexType) :: scope) 0 1 0 :=
            .skip_fvar _ _ .refl
          have HnarrowIndicesWeak : List.Forall₂
              (TrExprS R'.venv
                (AddInductive.getRecLevelParams elimLevel base.lparams)
                ((some (⟨current.ngen.curr⟩,
                  (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper).fvarsList),
                  .vlam indexType) :: scope))
              indices.toList
              (indexTargets.map fun result => result.liftN 1 0) := by
            apply checkPositivityStep.forall₂_map_right HnarrowIndices
            intro source result Hsource
            exact Hsource.weakFV R.checking.tr.wf.orderedStrong Wnarrow hscopeWF
          have HnarrowIndex : TrExprS R'.venv
              (AddInductive.getRecLevelParams elimLevel base.lparams)
              ((some (⟨current.ngen.curr⟩,
                (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper).fvarsList),
                .vlam indexType) :: scope)
              (.fvar ⟨current.ngen.curr⟩) (.bvar 0) := by
            exact TrExprS.fvar (A := indexType.lift) (by
              simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
                VLocalDecl.value, VLocalDecl.type])
          have HnarrowIndices' : List.Forall₂
              (TrExprS R'.venv
                (AddInductive.getRecLevelParams elimLevel base.lparams)
                ((some (⟨current.ngen.curr⟩,
                  (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper).fvarsList),
                  .vlam indexType) :: scope))
              (indices.push (.fvar ⟨current.ngen.curr⟩)).toList
              ((indexTargets.map fun result => result.liftN 1 0) ++
                [.bvar 0]) := by
            rw [Array.toList_push]
            exact List.Forall₂.append'
              HnarrowIndicesWeak (.cons HnarrowIndex .nil)
          have hopenedNarrow : TrExprS R'.venv
              (AddInductive.getRecLevelParams elimLevel base.lparams)
              ((some (⟨current.ngen.curr⟩,
                (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper).fvarsList),
                .vlam indexType) :: scope)
              (body.instantiate1 (.fvar ⟨current.ngen.curr⟩)) narrowBody := by
            rw [Expr.instantiate1_eq]
            exact hbodyNarrow.inst_fvar R.checking.tr.wf.orderedStrong hscopeWF
          have hopenedFVars : FVarsIn
              (· ∈ VLCtx.fvars ((some (⟨current.ngen.curr⟩,
                (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper).fvarsList),
                .vlam indexType) :: scope))
              (body.instantiate1 (.fvar ⟨current.ngen.curr⟩)) := by
            rw [Expr.instantiate1_eq]
            apply (htypeFVars.2.mono fun fv hfv => by
              rw [VLCtx.fvars_cons_some]
              exact List.mem_cons_of_mem _ hfv).instantiate1
            rw [VLCtx.fvars_cons_some]
            exact List.mem_cons_self
          let x : FVarId := ⟨current.ngen.curr⟩
          have hdomBodyU : dom.levelParamsIn base.lparams = true ∧
              body.levelParamsIn base.lparams = true := by
            simpa [Expr.levelParamsIn] using htypeU
          have hscopeU' : R'.typeChecker.UniverseScope base.lparams
              (· ∈ VLCtx.fvars ((some (⟨current.ngen.curr⟩,
                (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper).fvarsList),
                .vlam indexType) :: scope)) := by
            have hcons : R'.typeChecker.UniverseScope base.lparams
                (fun fv => fv = x ∨ fv ∈ scope.fvars) := by
              refine TypeChecker.VContext.UniverseScope.cons (x := x)
                (deps := (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper).fvarsList)
                (d := .vlam consumedDom) rfl ?_ R.current_not_mem hscopeU
                hdeps ?_
              · intro fv hne
                change (TypeChecker.MLCtx.vlam x name
                  (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper) consumedDom bi
                  R.mlctx).lctx.find? fv = R.mlctx.lctx.find? fv
                have hwf : (TypeChecker.MLCtx.vlam x name
                    (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper) consumedDom bi
                    R.mlctx).WF R.venv
                    (AddInductive.getRecLevelParams elimLevel base.lparams) :=
                  R'.mlctx_wf
                rw [hwf.find?_eq, R.mlctx_wf.find?_eq]
                have hbeq : (fv == x) = false := by simpa using hne
                simp [TypeChecker.MLCtx.decls, LocalDecl.fvarId, hbeq]
              · intro decl hdecl
                have hself := R'.mlctx_wf.find?_vlam_self
                change (TypeChecker.MLCtx.vlam x name
                  (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper) consumedDom bi
                  R.mlctx).lctx.find? x = some decl at hdecl
                rw [hself] at hdecl
                cases hdecl
                exact ⟨Expr.levelParamsIn_consumeTypeAnnotationsVerified
                  hdomBodyU.1, fun v hv => by simp [LocalDecl.value?] at hv⟩
            have hP : (fun fv => fv = x ∨ fv ∈ scope.fvars) =
                (· ∈ VLCtx.fvars ((some (⟨current.ngen.curr⟩,
                  (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper).fvarsList),
                  .vlam indexType) :: scope)) := by
              funext fv
              simp [VLCtx.fvars_cons_some, x]
            exact hP ▸ hcons
          have hopenedU :
              (body.instantiate1 (.fvar ⟨current.ngen.curr⟩)).levelParamsIn
                base.lparams = true := by
            rw [Expr.instantiate1_eq]
            exact Expr.levelParamsIn_instantiate1 hdomBodyU.2 rfl
          have hopened₀ := R.atCheckLCtx.instantiateFresh (name := name) (bi := bi)
            Hdom₀.unannotated Hdom₀.isType hbodyConsumed₀
          have hnormalize := whnfInRecursorContext.dualWF R' hopened hopened₀
          have hnormalizeLevels := whnfInRecursorContext.levelsWF R' hopened₀
          exact ((hnormalize.and hnormalizeLevels).and (Except.WF.self _)).bind
            fun next ⟨⟨⟨hnext, _, hnext₀⟩, hnextLevels⟩, hrun⟩ => by
            have hnormalizedFVars := hnext.1 _ Hruntime'.upset hopenedFVars
            rcases hnext.2 with
              ⟨normalizedFull, hnormalizedFull, hnormalizeEq⟩
            rcases hnext₀ with ⟨normalizedC, hnormalizedC, hnormalizedCEq⟩
            have hindexU : R.venv.IsDefEqU
                (AddInductive.getRecLevelParams elimLevel base.lparams).length
                scope.toCtx indexType consumed₀ := by
              rcases Hdom₀.source_defeq with ⟨_, hsc⟩
              exact hdomCU.trans henvWF hscopeWF₀.toCtx
                ⟨_, hsc.defeqDFC henvWF.ordered (halign.defeqCtx.symm henvWF.ordered)⟩
            have hindex := hindexU.of_l henvWF hscopeWF₀.toCtx
              (Classical.choose_spec hdomType)
            rcases halign.openedNormalForm henvWF hindex
                (by rintro _ _ ⟨⟩; exact ⟨hfreshScope, hdeps⟩)
                hbodyNarrow hbodyConsumed₀ hnormalizedC hnormalizedCEq with
              ⟨normalizedNarrow, hnormalizedNarrow, hnarrow⟩
            have hdomainNarrow : ∃ sourceDom',
                TrExprS R'.venv
                  (AddInductive.getRecLevelParams elimLevel base.lparams)
                  scope dom sourceDom' ∧
                R'.venv.IsDefEqU
                  (AddInductive.getRecLevelParams elimLevel base.lparams).length
                  scope.toCtx sourceDom' indexType :=
              ⟨_, hdomNarrow, ⟨.sort (Classical.choose hdomType),
                Classical.choose_spec hdomType⟩⟩
            have htransition : ∃ sourceBody' normalized',
                TrExprS R'.venv
                  (AddInductive.getRecLevelParams elimLevel base.lparams)
                  ((none, .vlam indexType) :: scope) body sourceBody' ∧
                TrExprS R'.venv
                  (AddInductive.getRecLevelParams elimLevel base.lparams)
                  ((some (⟨current.ngen.curr⟩,
                    (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper).fvarsList),
                    .vlam indexType) :: scope) next normalized' ∧
                R'.venv.IsDefEqU
                  (AddInductive.getRecLevelParams elimLevel base.lparams).length
                  (indexType :: scope.toCtx) sourceBody' normalized' :=
              ⟨narrowBody, normalizedNarrow, hbodyNarrow,
                hnormalizedNarrow, hnarrow⟩
            rcases Hsynthesis.consumeIndex (name := name) (bi := bi)
                R'.checking.tr.wf
                (.forallE hdomType _hbodyType hdomNarrow hbodyNarrow)
                hscopeWF hdomainNarrow htransition with
              ⟨nextNarrow, hnextNarrow, Hsynthesis',
                ⟨hparams, hfrontIndices⟩⟩
            let c' : AddInductive.Context := { current with
              ngen := current.ngen.next
              lctx := current.lctx.mkLocalDecl ⟨current.ngen.curr⟩ name
                (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper) bi
              checkLCtx := current.checkLCtx.mkLocalDecl ⟨current.ngen.curr⟩ name
                (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper) bi }
            have hstep : BindingContextLE current c' :=
              BindingContextLE.withCheckedLocalDecl current R.toBindingContextWF
                name (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper) bi
            have hidsPush : ExprArrayFVarIds (indices.push (.fvar x)) =
                ExprArrayFVarIds indices ++ [x] :=
              ExprArrayFVarIds_push_fvar indices x
            have hscopeFVars' : ∀ fv ∈ VLCtx.fvars ((some (⟨current.ngen.curr⟩,
                  (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper).fvarsList),
                  .vlam indexType) :: scope),
                fv ∈ ExprArrayFVarIds stats.params ∨
                  fv ∈ ExprArrayFVarIds (indices.push (.fvar x)) := by
              intro fv hfv
              rw [VLCtx.fvars_cons_some] at hfv
              rw [hidsPush]
              rcases List.mem_cons.mp hfv with hfv | hfv
              · exact .inr (List.mem_append_right _ (by simp [hfv, x]))
              · rcases hscopeFVars fv hfv with h | h
                · exact .inl h
                · exact .inr (List.mem_append_left _ h)
            have hQmem : ∀ fv, (fv ∈ ExprArrayFVarIds stats.params ∨
                fv ∈ ExprArrayFVarIds (indices.push (.fvar x))) →
                fv ∈ c'.lctx.fvars := by
              intro fv hfv
              rw [hidsPush] at hfv
              rcases hfv with h | h
              · exact hstep.fvars (Hsuffix.mem_lctx_of_mem_params h)
              · rcases List.mem_append.mp h with h | h
                · rw [Horigins.bound.exprArrayFVarIds] at h
                  exact hstep.fvars (Horigins.bound.members fv h)
                · rw [List.mem_singleton.mp h]
                  exact mem_fvars_mkLocalDecl_self current name
                    (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper) bi
            have hcallIndex : WhnfRunAt c'
                (fun fv => fv ∈ ExprArrayFVarIds stats.params ∨
                  fv ∈ ExprArrayFVarIds (indices.push (.fvar x)))
                (body.instantiate1 (.fvar x)) next :=
              ⟨c', _, R', _, _, BindingContextLE.refl c', hopened,
                Hruntime'.upset, fun fv hfv =>
                  ⟨hscopeFVars' fv hfv, hQmem fv (hscopeFVars' fv hfv)⟩,
                hopenedFVars, hrun, _, hopened₀⟩
            have Htrace' : IndexTelescopeRun stats c' source.type
                stats.params.size next (indices.push (.fvar x)) :=
              .index (Htrace.mono hstep)
                (mem_fvars_mkLocalDecl_self current name
                  (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper) bi)
                ⟨_, _, _, _, R.toBindingContextWF.find?_mkLocalDecl_self name
                  (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper) bi⟩
                hcallIndex
            exact continueRecursorIndexTelescopeTyping stats k H Helim
              Rroot hconsume Hk R' (by simpa [R'] using henv)
              Hsuffix' (by
                change Hsuffix.parameterDecls = rootParameterDecls
                exact hparameterDecls)
              next consumedBody nextNarrow
              ((some (⟨current.ngen.curr⟩,
                (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper).fvarsList),
                .vlam indexType) :: scope)
              (nindices + 1)
              (indices.push (.fvar ⟨current.ngen.curr⟩))
              (originTypes.push (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper))
              ((indexTargets.map fun result => result.liftN 1 0) ++
                [.bvar 0]) fuel Hsynthesis' (by
                  rw [hparams]
                  exact hcanonicalParams)
              (by
                change scope.drop nindices = rootParameterDecls
                exact hscopeBase)
              (HnarrowStats.withFVar R'.checking.tr.wf hscopeWF)
              (Hstats.withFVar R'.checking.tr.wf R'.mlctx_wf.tr.wf)
              Hruntime' (by
                change Hruntime.frontSourceDomains ++ [indexType] =
                  Hsynthesis'.indices
                rw [hfront, hfrontIndices]) halign'
              hnextNarrow hnormalizedFVars
              (hnextLevels _ _ hscopeU' hopenedU hopenedFVars) hscopeU'
              ⟨normalizedFull, hnormalizedFull, hnormalizeEq⟩
              hconsumedBodyType Hindices' HnarrowIndices'
              (by simp [hindexCount])
              (by simp [hcanonical])
              (Horigins.pushCurrentChecked R.toBindingContextWF name
                (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper) bi)
              (HoriginTypes.pushChecked (name := name) (bi := bi)
                Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType)
              (Hrecent.pushCurrentChecked name (dom.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper) consumedDom
                bi Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType)
              Htrace' hscopeFVars'
      | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
        | proj =>
          simpa [AddInductive.mkRecInfos.loopArgs1] using
            Hk R henv Hsuffix hparameterDecls Hsynthesis hcanonicalParams
              hscopeBase HnarrowStats Hstats Hruntime
              hfront halign htypeNarrow htypeFVars htypeU hscopeU htypeFull
              htypeFullType Hindices
              HnarrowIndices hindexCount hcanonical Horigins HoriginTypes Hrecent
              Htrace
termination_by
  current runtimeDepth R _henv Hsuffix _hparameterDecls _type _fullTarget _narrowTarget _scope
    _nindices _indices _originTypes _indexTargets fuel => fuel

/-- Walk the cached common-parameter prefix directly in a universe-rebased
recursor context.  The terminal continuation begins at the index
boundary with the parameter suffix of the checking scope; no generated index, major,
or motive declaration is admitted into the parameter telescope. -/
theorem continueRecursorParameterTyping {alpha : Type}
    (stats : AddInductive.InductiveStats)
    (k : Array Expr → AddInductive.M alpha)
    {Q : alpha → Prop}
    {base current : AddInductive.Context} {Hbase : ContextWF base}
    {decl : VInductDecl} {depth runtimeDepth familyIdx : Nat}
    {source : InductiveType}
    (H : MotivePassHeaderAt Hbase stats decl depth source familyIdx)
    {elimLevel : Level}
    (Helim : AddInductive.AdmissibleElimLevel base.lparams elimLevel)
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel base.lparams))
    (henv : R.venv = Hbase.venv)
    (Hsuffix : RecursorParameterContextSuffix R stats runtimeDepth)
    (hctx : VEnv.IsDefEqCtx R.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams).length []
      (H.recursorParams Helim).reverse Hsuffix.parameterDecls.toCtx)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams) R.mlctx.vlctx
      stats decl runtimeDepth)
    (hparamScope : R.typeChecker.UniverseScope base.lparams
      (· ∈ Hsuffix.parameterDecls.fvars))
    (Hk : ∀ {type : Expr} {fullTarget narrowTarget : VExpr},
      (Hsynthesis :
        checkInductiveTypes.loopType.ScopedHeaderTelescope
          R.venv (AddInductive.getRecLevelParams elimLevel base.lparams)
          (H.recursorTargetSkeleton Helim) Hsuffix.parameterDecls
          narrowTarget stats.params.size 0) →
      RecursorValidAppStatsWF R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        Hsuffix.parameterDecls stats decl 0 →
      (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        Hsuffix.parameterDecls R.mlctx.vlctx) →
      Hruntime.frontSourceDomains = Hsynthesis.indices →
      TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        Hsuffix.parameterDecls type narrowTarget →
      FVarsIn (· ∈ Hsuffix.parameterDecls.fvars) type →
      type.levelParamsIn base.lparams = true →
      TrExpr R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        R.mlctx.vlctx type fullTarget →
      R.venv.IsType
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        R.mlctx.vlctx.toCtx fullTarget →
      IndexTelescopeRun stats current source.type stats.params.size type
        #[] →
      ∀ indices fuel,
        indices = #[] →
        (AddInductive.mkRecInfos.loopArgs1 stats type stats.params.size
          indices fuel k current).WF Q) :
    ∀ type fullTarget narrowTarget scope i indices fuel,
      i ≤ stats.params.size →
      (Hscope : ∀ _hi : i < stats.params.size,
        RecursorReusedParameterScope Hsuffix i type) →
      (∀ hi : i < stats.params.size, scope = (Hscope hi).older) →
      (i = stats.params.size → scope = Hsuffix.parameterDecls) →
      checkInductiveTypes.loopType.ScopedHeaderTelescope
        R.venv (AddInductive.getRecLevelParams elimLevel base.lparams)
        (H.recursorTargetSkeleton Helim) scope narrowTarget i 0 →
      TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope type narrowTarget →
      FVarsIn (· ∈ scope.fvars) type →
      type.levelParamsIn base.lparams = true →
      TrExpr R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        R.mlctx.vlctx type fullTarget →
      R.venv.IsType
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        R.mlctx.vlctx.toCtx fullTarget →
      indices = #[] →
      IndexTelescopeRun stats current source.type i type #[] →
      (AddInductive.mkRecInfos.loopArgs1 stats type i indices fuel
        k current).WF Q
  | _, _, _, _, _, _, 0, _, _, _, _, _, _, _, _, _, _, _, _ => by
      intro _ h
      simp [AddInductive.mkRecInfos.loopArgs1] at h
  | type, fullTarget, narrowTarget, scope, i, indices, fuel + 1,
      hbound, Hscope, hscopeEq, hcompleteScope, Hsynthesis,
      htypeNarrow, htypeFVars, htypeU, htypeFull, htypeFullType,
      hindicesEmpty, Htrace => by
      by_cases hdone : stats.params.size ≤ i
      · have hieq : i = stats.params.size := by omega
        subst i
        have hscope : scope = Hsuffix.parameterDecls :=
          hcompleteScope rfl
        subst scope
        exact Hk Hsynthesis (Hsuffix.scopedStats Hstats)
          Hsuffix.parameterEmbedding (by
            change [] = Hsynthesis.indices
            exact (List.eq_nil_of_length_eq_zero
              Hsynthesis.indexCount).symm)
          htypeNarrow htypeFVars htypeU htypeFull
          htypeFullType Htrace indices (fuel + 1) hindicesEmpty
      · have hi : i < stats.params.size := by omega
        cases type with
        | forallE name dom body bi =>
          rw [AddInductive.mkRecInfos.loopArgs1, if_pos hi]
          have htypeNarrow' := htypeNarrow
          cases htypeNarrow with
          | @forallE currentDomain currentBody _ _ _ _ _ hdomType
              _hbodyType hdomNarrow hbodyNarrow =>
            let Hcurrent := Hscope hi
            have hscope : scope = Hcurrent.older := hscopeEq hi
            subst scope
            rcases parameterStepOfCheckedRecursorHeader H Helim R Hcurrent
                Hsynthesis hi henv hctx htypeNarrow' htypeFull with
              ⟨bodyTarget, hopened, hopenedType⟩
            refine AddInductive.M.WF_bind AddInductive.paramCheckLCtx.WF
              fun _ hL => ?_
            subst hL
            have henvWF := R.checking.tr.wf
            have hj₁ : runtimeDepth + (stats.params.size - (i + 1)) ≤
                R.mlctx.length := by
              rw [Hsuffix.mlctx_length]; omega
            have hb₁ := Hsuffix.bottom (i + 1) (by omega)
            have hchk₁ : (R.mlctx.dropN _ hj₁).vlctx =
                (some (Hcurrent.fv, Hcurrent.deps), .vlam Hcurrent.paramType) ::
                  Hcurrent.older :=
              hb₁.1.trans (Hcurrent.olderDrop hi).2
            let Ri := R.paramCheck stats (i + 1) _ hj₁ hb₁.2
            have hnarrowMatch := H.recursorCurrentDomainDefEq Helim
              Hcurrent Hsynthesis hi henv hctx
            have holderWF := Hsynthesis.scopeWF
            have hentryWF : VLCtx.WF R.venv
                (AddInductive.getRecLevelParams elimLevel base.lparams).length
                ((some (Hcurrent.fv, Hcurrent.deps), .vlam Hcurrent.paramType) ::
                  Hcurrent.older) :=
              hchk₁ ▸ (R.mlctx_wf.dropN _ hj₁).tr.wf
            have hctxB : VLCtx.IsDefEq R.venv
                (AddInductive.getRecLevelParams elimLevel base.lparams).length
                ((none, .vlam currentDomain) :: Hcurrent.older)
                ((none, .vlam Hcurrent.paramType) :: Hcurrent.older) :=
              .cons (.refl henvWF holderWF) nofun
                (.vlam (hnarrowMatch.of_l henvWF holderWF.toCtx
                  (Classical.choose_spec hdomType)))
            obtain ⟨bodyC, hbodyC⟩ := hbodyNarrow.defeqDFC henvWF hctxB
            have hopened₀ : TrExprS Ri.venv
                (AddInductive.getRecLevelParams elimLevel base.lparams)
                Ri.chk.vlctx (body.instantiate1 stats.params[i]!) bodyC := by
              change TrExprS R.venv _ (R.mlctx.dropN _ hj₁).vlctx _ _
              rw [hchk₁, Expr.instantiate1_eq, Hcurrent.parameter]
              exact hbodyC.inst_fvar henvWF.orderedStrong hentryWF
            have hnormalize := whnfInRecursorContext.dualWF Ri hopened hopened₀
            have hnormalizeLevels := whnfInRecursorContext.levelsWF Ri hopened₀
            have hparamMem : Hcurrent.fv ∈ Hsuffix.parameterDecls.fvars := by
              rw [Hcurrent.parameterDecls]
              simp
            have holderMem : ∀ fv, fv ∈ Hcurrent.older.fvars →
                fv ∈ Hsuffix.parameterDecls.fvars := by
              intro fv hfv
              rw [Hcurrent.parameterDecls]
              simp [hfv]
            have hopenedU : (body.instantiate1 stats.params[i]!).levelParamsIn
                base.lparams = true := by
              rw [Hcurrent.parameter, Expr.instantiate1_eq]
              have hbodyU : body.levelParamsIn base.lparams = true := by
                simp only [Expr.levelParamsIn, Bool.and_eq_true] at htypeU
                exact htypeU.2
              exact Expr.levelParamsIn_instantiate1 hbodyU rfl
            have hopenedP : FVarsIn (· ∈ Hsuffix.parameterDecls.fvars)
                (body.instantiate1 stats.params[i]!) := by
              rw [Hcurrent.parameter, Expr.instantiate1_eq]
              exact (htypeFVars.2.mono holderMem).instantiate1 hparamMem
            exact ((hnormalize.and hnormalizeLevels).and (Except.WF.self _)).bind
              fun next ⟨⟨⟨hnext, _, hnext₀⟩, hnextLevels⟩, hrun⟩ => by
              have hcallParam : WhnfRunAt current
                  (fun fv => fv ∈ ExprArrayFVarIds stats.params)
                  (body.instantiate1 stats.params[i]!) next := by
                refine ⟨_, _, Ri, (· ∈ Hsuffix.parameterDecls.fvars), _,
                  BindingContextLE.checkLCtx current _, hopened, hparamScope.1,
                  fun fv hfv => ?_, hopenedP, hrun, _, hopened₀⟩
                have hparam : fv ∈ ExprArrayFVarIds stats.params := by
                  rw [Hsuffix.parameterDecls_fvars] at hfv
                  exact List.mem_reverse.mp hfv
                exact ⟨hparam, Hsuffix.mem_lctx_of_mem_params hparam⟩
              have hindices : Hsynthesis.indices = [] :=
                List.eq_nil_of_length_eq_zero Hsynthesis.indexCount
              let Hbody : RecursorReusedParameterScope Hsuffix i body :=
                { Hcurrent with fvars := Hcurrent.fvars.2 }
              have hnext₀' : TrExpr R.venv
                  (AddInductive.getRecLevelParams elimLevel base.lparams)
                  ((some (Hcurrent.fv, Hcurrent.deps),
                    .vlam Hcurrent.paramType) :: Hcurrent.older) next bodyC := by
                have h := hnext₀
                change TrExpr R.venv _ (R.mlctx.dropN _ hj₁).vlctx _ _ at h
                rw [hchk₁] at h
                exact h
              rcases hnext₀' with ⟨normalizedTarget, hnormalizedNarrow, hnormEq⟩
              rcases Hsynthesis.consumeParameter R.checking.tr.wf
                  hindices htypeNarrow' hentryWF
                  ⟨currentDomain, hdomNarrow, hnarrowMatch⟩
                  ⟨bodyC, normalizedTarget, hbodyC,
                    hnormalizedNarrow, hnormEq.symm⟩ with
                ⟨nextNarrow, hnextNarrow, ⟨Hsynthesis'⟩⟩
              exact continueRecursorParameterTyping stats k H Helim R
                henv Hsuffix hctx Hstats hparamScope Hk next bodyTarget
                nextNarrow
                ((some (Hcurrent.fv, Hcurrent.deps),
                  .vlam Hcurrent.paramType) :: Hcurrent.older)
                (i + 1) indices fuel (by omega)
                (fun hlt => Hbody.next hlt hnext.1)
                (fun hlt => Hbody.nextOlder
                  (Hbody.next hlt hnext.1) hlt)
                (fun heq => Hcurrent.scope heq)
                Hsynthesis' hnextNarrow
                (Hbody.unannotatedFVars hnext.1)
                (hnextLevels _ _ hparamScope hopenedU hopenedP)
                hnext.2 hopenedType
                hindicesEmpty (.param Htrace hi hcallParam)
        | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
          | proj =>
            simp only [AddInductive.mkRecInfos.loopArgs1, hi, if_pos]
            exact Except.WF.throw
termination_by
  _type _fullTarget _narrowTarget _scope _i _indices fuel => fuel

/-- Start the universe-rebased cached-parameter walk from the executable
`whnf` call.  This wrapper is valid after arbitrary earlier mutual
recursor frames have accumulated in the executable context. -/
theorem MotivePassHeaderAt.startRecursorParameterTyping
    {alpha : Type} {Q : alpha → Prop}
    {base current : AddInductive.Context} {Hbase : ContextWF base}
    (H : MotivePassHeaderAt Hbase stats decl depth source familyIdx)
    {elimLevel : Level}
    (Helim : AddInductive.AdmissibleElimLevel base.lparams elimLevel)
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel base.lparams))
    (henv : R.venv = Hbase.venv)
    (Hsuffix : RecursorParameterContextSuffix R stats runtimeDepth)
    (hctx : VEnv.IsDefEqCtx R.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams).length []
      (H.recursorParams Helim).reverse Hsuffix.parameterDecls.toCtx)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams) R.mlctx.vlctx
      stats decl runtimeDepth)
    (hparamScope : R.typeChecker.UniverseScope base.lparams
      (· ∈ Hsuffix.parameterDecls.fvars))
    (k : Array Expr → AddInductive.M alpha)
    (Hk : ∀ {type : Expr} {fullTarget narrowTarget : VExpr},
      (Hsynthesis :
        checkInductiveTypes.loopType.ScopedHeaderTelescope
          R.venv (AddInductive.getRecLevelParams elimLevel base.lparams)
          (H.recursorTargetSkeleton Helim) Hsuffix.parameterDecls
          narrowTarget stats.params.size 0) →
      RecursorValidAppStatsWF R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        Hsuffix.parameterDecls stats decl 0 →
      (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        Hsuffix.parameterDecls R.mlctx.vlctx) →
      Hruntime.frontSourceDomains = Hsynthesis.indices →
      TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        Hsuffix.parameterDecls type narrowTarget →
      FVarsIn (· ∈ Hsuffix.parameterDecls.fvars) type →
      type.levelParamsIn base.lparams = true →
      TrExpr R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        R.mlctx.vlctx type fullTarget →
      R.venv.IsType
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        R.mlctx.vlctx.toCtx fullTarget →
      IndexTelescopeRun stats current source.type stats.params.size type
        #[] →
      ∀ indices fuel,
        indices = #[] →
        (AddInductive.mkRecInfos.loopArgs1 stats type stats.params.size
          indices fuel k (headerCheckContext current stats)).WF Q)
    (fuel : Nat) :
    ((monadLift (TypeChecker.whnf source.type) : AddInductive.M Expr)
      { current with checkLCtx := {} } >>= fun normalized =>
        (AddInductive.paramCheckLCtx stats stats.params.size >>= fun L =>
          AddInductive.withCheckLCtx L
            (AddInductive.mkRecInfos.loopArgs1 stats normalized 0 #[] fuel k))
          current).WF Q := by
  -- The closed header is normalized in the empty checker context.
  have hstart := H.startRecursorHeaderTyping Helim
    (R.withCheckLCtx {} R.baseNil) henv rfl
  have hcall := H.headerWhnfCall Helim
    (R.withCheckLCtx {} R.baseNil) henv
  exact (hstart.and hcall).bind fun normalized ⟨⟨hnormalizedU, hnormalized⟩, hcallHeader₀⟩ => by
    have hcallHeader : WhnfRunAt current (fun _ => False) source.type normalized :=
      hcallHeader₀.mono (BindingContextLE.checkLCtx current _) fun _ h => h
    refine AddInductive.M.WF_bind AddInductive.paramCheckLCtx.WF fun _ hL => ?_
    subst hL
    rw [AddInductive.withCheckLCtx_apply]
    -- The telescope is opened on top of the parameters.
    let R₀ := R
    let HsuffixBase := Hsuffix
    let Hsuffix : RecursorParameterContextSuffix
        HsuffixBase.headerCheck stats runtimeDepth := HsuffixBase.toHeaderCheck
    let R := HsuffixBase.headerCheck
    rcases hnormalized.2 with
      ⟨narrowTarget, hnormalizedNarrow, ⟨Hsynthesis⟩⟩
    have hsourceNoFVars : FVarsIn (fun _ => False) source.type :=
      (H.recursorSourceTranslation Helim).fvarsIn.mono fun fv hfv => by
        simp [VLCtx.fvars] at hfv
    have hfalseUpSet : IsFVarUpSet (fun _ => False) R.mlctx.vlctx := by
      have hsuffix := IsFVarUpSet.suffixFVars ([] : VLCtx)
        R.mlctx.vlctx (by simpa using R.mlctx_wf.tr.wf)
      simpa [VLCtx.fvars] using hsuffix
    have hnormalizedNoFVars : FVarsIn (fun _ => False) normalized :=
      hnormalized.1 _ hfalseUpSet hsourceNoFVars
    let W : VLCtx.FVLift [] R.mlctx.vlctx 0
        R.mlctx.vlctx.toCtx.length 0 :=
      VLCtx.FVLift.from_nil R.mlctx.noBV
    have hnormalizedFullS := hnormalizedNarrow.weakFV
      R.checking.tr.wf.orderedStrong W R.mlctx_wf.tr.wf
    have hnormalizedFull : TrExpr R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        R.mlctx.vlctx normalized
        (narrowTarget.liftN R.mlctx.vlctx.toCtx.length 0) :=
      hnormalizedFullS.trExpr R.checking.tr.wf R.mlctx_wf.tr.wf
    have hnormalizedFullType : R.venv.IsType
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        R.mlctx.vlctx.toCtx
        (narrowTarget.liftN R.mlctx.vlctx.toCtx.length 0) :=
      Hsynthesis.currentType.weakN R.checking.tr.wf.ordered W.toCtx
    let Hscope : ∀ hi : 0 < stats.params.size,
        RecursorReusedParameterScope Hsuffix 0 normalized := fun hi =>
      RecursorReusedParameterScope.ofNoFVars hi hnormalizedNoFVars
    have hscopeEq : ∀ hi : 0 < stats.params.size,
        [] = (Hscope hi).older := by
      intro hi
      exact (Hscope hi).older_eq_nil hi |>.symm
    have hcompleteScope : 0 = stats.params.size →
        ([] : VLCtx) = Hsuffix.parameterDecls := by
      intro hzero
      exact (List.eq_nil_of_length_eq_zero (by
        rw [Hsuffix.parameterDecls_length, ← hzero])).symm
    exact continueRecursorParameterTyping stats k H Helim R henv
      Hsuffix hctx Hstats hparamScope
      (fun Hs h1 Hr h2 h3 h4 h5 h6 h7 Ht =>
        Hk Hs h1 Hr h2 h3 h4 h5 h6 h7 (Ht.mono (BindingContextLE.checkLCtx current _)))
      normalized
      (narrowTarget.liftN R.mlctx.vlctx.toCtx.length 0) narrowTarget [] 0
      #[] fuel (by omega) Hscope hscopeEq hcompleteScope Hsynthesis
      hnormalizedNarrow
      (by simpa [VLCtx.fvars] using hnormalizedNoFVars) hnormalizedU
      hnormalizedFull hnormalizedFullType rfl (.start (hcallHeader.mono (BindingContextLE.checkLCtx_rev current _) fun _ h => h))

/-- The index telescope opened by `loopArgs1` mentions only `Us` when its
declarations lie in a universe scope of the index checking scope. -/
theorem _root_.Lean4Lean.VerifyInductive.RecursorFVarSuffix.indexUniverses
    {root c : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {R : RecursorContextWF c recLparams} {xs : Array Expr}
    (H : RecursorFVarSuffix Rroot R xs)
    {Us : List Name} {scope : VLCtx} {targets : List VExpr}
    (hscope : R.typeChecker.UniverseScope Us (· ∈ scope.fvars))
    (Hxs : List.Forall₂ (TrExprS R.venv recLparams scope) xs.toList targets) :
    (c.lctx.mkForall xs (.sort .zero)).levelParamsIn Us = true := by
  refine H.toFVarArrayIn.mkForall_levelParamsIn R.toBindingContextWF H.nodup ?_
    (by simp [Expr.levelParamsIn, Level.paramsIn])
  intro x hx decl hdecl
  have hxArg : Expr.fvar x ∈ xs.toList := by
    rw [H.expressions]
    simpa using hx
  have hexists : ∀ {l : List Expr} {ts : List VExpr},
      List.Forall₂ (TrExprS R.venv recLparams scope) l ts →
      Expr.fvar x ∈ l → ∃ t, TrExprS R.venv recLparams scope (.fvar x) t := by
    intro l ts h hmem
    induction h with
    | nil => simp at hmem
    | cons hab _ ih =>
      rcases List.mem_cons.mp hmem with heq | hmem
      · exact ⟨_, heq ▸ hab⟩
      · exact ih hmem
  obtain ⟨_, ht⟩ := hexists Hxs hxArg
  have hxScope : x ∈ scope.fvars := by simpa [FVarsIn] using ht.fvarsIn
  have hdecl' : R.typeChecker.lctx'.find? x = some decl := by
    change R.mlctx.lctx.find? x = some decl
    rw [R.lctx_eq]
    exact hdecl
  exact (hscope.2 x decl hxScope hdecl').1

/-- Complete parameter and index opening under one recursor-universe
context.  The continuation is reached with the parameter
suffix, the index bvar spine, and a recent-index certificate rooted at
the context in which this family began. -/
theorem MotivePassHeaderAt.startRecursorTyping
    {alpha : Type} {Q : alpha → Prop}
    {base current : AddInductive.Context} {Hbase : ContextWF base}
    (H : MotivePassHeaderAt Hbase stats decl depth source familyIdx)
    {elimLevel : Level}
    (Helim : AddInductive.AdmissibleElimLevel base.lparams elimLevel)
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel base.lparams))
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (henv : R.venv = Hbase.venv)
    (Hsuffix : RecursorParameterContextSuffix R stats runtimeDepth)
    (hctx : VEnv.IsDefEqCtx R.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams).length []
      (H.recursorParams Helim).reverse Hsuffix.parameterDecls.toCtx)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams) R.mlctx.vlctx
      stats decl runtimeDepth)
    (hparamU : ParameterUniverseSupport current stats.params)
    (hlparams : current.lparams = base.lparams)
    (k : Array Expr → AddInductive.M alpha)
    (Hk : ∀ {next : AddInductive.Context} {nextDepth : Nat}
      (Rnext : RecursorContextWF next
        (AddInductive.getRecLevelParams elimLevel base.lparams))
      (_henvNext : Rnext.venv = Hbase.venv)
      (HsuffixNext : RecursorParameterContextSuffix Rnext stats nextDepth)
      (_hparameterDecls :
        HsuffixNext.parameterDecls = Hsuffix.parameterDecls)
      {type : Expr} {fullTarget narrowTarget : VExpr} {scope : VLCtx}
      {nindices : Nat} {indices originTypes : Array Expr}
      {indexTargets : List VExpr},
      (Hsynthesis :
        checkInductiveTypes.loopType.ScopedHeaderTelescope
          Rnext.venv
          (AddInductive.getRecLevelParams elimLevel base.lparams)
          (H.recursorTargetSkeleton Helim) scope narrowTarget
          stats.params.size nindices) →
      Hsynthesis.params.reverse = Hsuffix.parameterDecls.toCtx →
      scope.drop nindices = Hsuffix.parameterDecls →
      RecursorValidAppStatsWF Rnext.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope stats decl nindices →
      RecursorValidAppStatsWF Rnext.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        Rnext.mlctx.vlctx stats decl nextDepth →
      (Hruntime : checkInductiveTypes.loopType.FrontScopeEmbedding Rnext.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope Rnext.mlctx.vlctx) →
      Hruntime.frontSourceDomains = Hsynthesis.indices →
      VLCtx.IsDefEq Rnext.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        scope Rnext.chk.vlctx →
      TrExprS Rnext.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope type narrowTarget →
      FVarsIn (· ∈ scope.fvars) type →
      TrExpr Rnext.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        Rnext.mlctx.vlctx type fullTarget →
      Rnext.venv.IsType
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        Rnext.mlctx.vlctx.toCtx fullTarget →
      List.Forall₂ (TrExprS Rnext.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        Rnext.mlctx.vlctx) indices.toList indexTargets →
      List.Forall₂ (TrExprS Rnext.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope) indices.toList indexTargets →
      indexTargets.length = nindices →
      indexTargets = indexBVarSpine nindices →
      FVarArrayBinderTypes next indices originTypes →
      TrBinderTypes Rnext originTypes →
      RecursorFVarSuffix R Rnext indices →
      (next.lctx.mkForall indices (.sort .zero)).levelParamsIn base.lparams = true →
      IndexTelescopeRun stats next source.type stats.params.size type
        indices →
      (k indices next).WF Q)
    (fuel : Nat) :
    ((monadLift (TypeChecker.whnf source.type) : AddInductive.M Expr)
      { current with checkLCtx := {} } >>= fun normalized =>
        (AddInductive.paramCheckLCtx stats stats.params.size >>= fun L =>
          AddInductive.withCheckLCtx L
            (AddInductive.mkRecInfos.loopArgs1 stats normalized 0 #[] fuel k))
          current).WF Q := by
  have hparamScope : R.typeChecker.UniverseScope base.lparams
      (· ∈ Hsuffix.parameterDecls.fvars) := by
    refine R.universeScope_of_types Hsuffix.parameterEmbedding.upset ?_
    intro fv hfv decl hfind
    rw [← hlparams]
    refine hparamU fv ?_ decl hfind
    rw [Hsuffix.parameterDecls_fvars] at hfv
    exact List.mem_reverse.mp hfv
  refine H.startRecursorParameterTyping Helim R henv Hsuffix hctx
    Hstats hparamScope k ?_ fuel
  intro type fullTarget narrowTarget Hsynthesis HnarrowStats Hruntime hfront
    htypeNarrow htypeFVars htypeU htypeFull htypeFullType Htrace indices
    remaining hindicesEmpty
  subst indices
  have hcanonicalParams : Hsynthesis.params.reverse =
      Hsuffix.parameterDecls.toCtx := by
    have hindices : Hsynthesis.indices = [] :=
      List.eq_nil_of_length_eq_zero Hsynthesis.indexCount
    simpa [hindices] using Hsynthesis.scopeCtx.symm
  -- The index telescope is opened on top of the parameters.
  let RL := Hsuffix.headerCheck
  let HsuffixL : RecursorParameterContextSuffix RL stats runtimeDepth :=
    Hsuffix.toHeaderCheck
  refine continueRecursorIndexTelescopeTyping
    (rootParameterDecls := Hsuffix.parameterDecls) stats k H Helim RL
    hconsume ?_ RL henv HsuffixL rfl type fullTarget narrowTarget
    Hsuffix.parameterDecls 0 #[] #[] [] remaining Hsynthesis
    hcanonicalParams rfl HnarrowStats
    Hstats Hruntime hfront Hsuffix.headerCheck_paramAligned
    htypeNarrow htypeFVars htypeU hparamScope
    htypeFull htypeFullType .nil .nil
    rfl rfl (FVarArrayBinderTypes.empty _)
    (TrBinderTypes.empty RL)
    (RecursorFVarSuffix.empty RL)
    (Htrace.mono (BindingContextLE.checkLCtx_rev current _)) (by
      intro fv hfv
      rw [Hsuffix.parameterDecls_fvars] at hfv
      exact .inl (List.mem_reverse.mp hfv))
  intro next nextDepth Rnext henvNext HsuffixNext hparameterDecls type'
    fullTarget' narrowTarget' scope nindices indices originTypes indexTargets
    Hsynthesis' hcanonical' hscopeBase HnarrowStats' Hstats' Hruntime' hfront'
    halign' htypeNarrow' htypeFVars' _htypeU' hscopeU' htypeFull' htypeFullType'
    Hindices HnarrowIndices hindexCount hcanonical Horigins HoriginTypes
    Hrecent HindexTrace
  exact Hk Rnext henvNext HsuffixNext hparameterDecls Hsynthesis' hcanonical'
    hscopeBase HnarrowStats' Hstats' Hruntime' hfront' halign' htypeNarrow'
    htypeFVars' htypeFull' htypeFullType' Hindices HnarrowIndices hindexCount
    hcanonical Horigins HoriginTypes Hrecent.ofCheckRoot
    (Hrecent.indexUniverses hscopeU' HnarrowIndices) HindexTrace

end mkRecInfos.loopArgs1

end VerifyInductive
end Lean4Lean
