import Lean4Lean.Verify.Inductive.Recursor.Binders.InductionHypothesisTypes

/-! Motive application properties used by the minor pass: the lookup of a generated
motive (`MotiveBinding`), the shared family/motive telescope
(`MotiveAppliesTo`, `MotiveAppliesAbove`), the motive data recorded by the motive
pass (`MotiveDecl`, `ClosedMotiveTelescope`), and their per-family arrays
(`RecInfoMotiveTelescopes`, `RecInfoMotiveApplications`). -/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment
namespace VerifyInductive

/-- Lookup data for one generated motive, stated against its `RecInfo`: the
translations of the executable motive free variable and of its type (the forall over the
index/major telescope recorded when the motive was introduced), and their typing. -/
structure MotiveBinding
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (info : AddInductive.RecInfo) (elimLevel : Level) : Type where
  motiveTarget : VExpr
  motiveTypeTarget : VExpr
  motive : TrExprS R.venv recLparams R.mlctx.vlctx
    info.motive motiveTarget
  motiveType : TrExprS R.venv recLparams R.mlctx.vlctx
    (c.lctx.mkForall info.indices
      (c.lctx.mkForall #[info.major] (.sort elimLevel)))
    motiveTypeTarget
  typing : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
    motiveTarget motiveTypeTarget
  typeIsType : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx
    motiveTypeTarget

/-- The typing property for applying one generated motive.  It is
quantified over the later context in which it is used: the motive pass of
`mkRecInfos` records this property once for each `RecInfo`, while the
minor pass uses it after opening any number of constructor or
higher-order recursive binders.

The validated application supplies the executable/abstract index correspondence.
The other two typing premises say that the exposed family application is a
type and that the proposed major premise inhabits it.  Thus this property is
the declarative fact needed to justify the executable's motive
application, rather than an assertion about the executable classifier. -/
def MotiveApplicationAbove
    {root : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF root recLparams)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (target : Nat) (info : AddInductive.RecInfo)
    (elimLevel : Level) : Prop :=
  ∀ {current : AddInductive.Context}
    (R : RecursorContextWF current recLparams)
    (_Hext : RecursorContextExtension Rroot R)
    {depth : Nat}
    {exposedType major : Expr} {syntaxTarget majorTarget : VExpr},
    MotiveBinding R info elimLevel →
    TrExprS R.venv recLparams R.mlctx.vlctx exposedType syntaxTarget →
    R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx syntaxTarget →
    TrExprS R.venv recLparams R.mlctx.vlctx major majorTarget →
    R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
      majorTarget syntaxTarget →
    RecursorValidatedIndAppAt R.venv recLparams R.mlctx.vlctx stats decl
      depth exposedType syntaxTarget target →
    let itIndices := exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app (mkAppN info.motive itIndices) major
    ∃ motiveTarget,
      TrExprS R.venv recLparams R.mlctx.vlctx motiveApp motiveTarget ∧
      R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx motiveTarget

/-- The smaller fact from which a motive application follows.
It states that the validated terminal family application and the
motive type range over the same abstract index telescope.  Keeping this
separate keeps the motive-pass obligation small: it need not mention a
particular recursive field or induction-hypothesis major. -/
structure MotiveAppliesTo
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (stats : AddInductive.InductiveStats) (info : AddInductive.RecInfo)
    (binding : MotiveBinding R info elimLevel)
    (exposedType : Expr) (syntaxTarget : VExpr) : Type where
  indices : List VExpr
  family : VExpr
  familyActualType : VExpr
  familyType : VExpr
  motiveType : VExpr
  resultLevel : VLevel
  syntax_eq : syntaxTarget = VExpr.mkApps family indices
  indices_translation : List.Forall₂
    (TrExprS R.venv recLparams R.mlctx.vlctx)
    (exposedType.getAppArgs[stats.params.size:]).toList indices
  family_typing : R.venv.HasType recLparams.length
    R.mlctx.vlctx.toCtx family familyActualType
  family_type_defeq : R.venv.IsDefEqU recLparams.length
    R.mlctx.vlctx.toCtx familyActualType familyType
  motive_type_defeq : R.venv.IsDefEqU recLparams.length
    R.mlctx.vlctx.toCtx binding.motiveTypeTarget motiveType
  telescope : RecursorMotiveTelescope resultLevel indices.length family
    familyType motiveType

/-- Fill the syntactic half of `MotiveAppliesTo` directly from the
validated terminal application.  The only remaining inputs are the
typing of the family prefix and its parallel relation to the motive
type. -/
theorem RecursorValidatedIndAppAt.motiveAppliesTo
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : RecursorValidatedIndAppAt R.venv recLparams R.mlctx.vlctx
      stats decl depth exposedType syntaxTarget target)
    (binding : MotiveBinding R info elimLevel)
    (familyActualType familyType motiveType : VExpr)
    (resultLevel : VLevel)
    {levels : List VLevel} {params indices : List VExpr}
    (hspine : syntaxTarget.getAppFnArgs =
      (.const (decl.types[target]'H.target_lt).name levels,
        params ++ indices))
    (Hindices : List.Forall₂
      (TrExprS R.venv recLparams R.mlctx.vlctx)
      (exposedType.getAppArgs[stats.params.size:]).toList indices)
    (Hfamily :
      R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
        (VExpr.mkApps
          (.const (decl.types[target]'H.target_lt).name levels) params)
        familyActualType)
    (HfamilyType : R.venv.IsDefEqU recLparams.length
      R.mlctx.vlctx.toCtx familyActualType familyType)
    (HmotiveType : R.venv.IsDefEqU recLparams.length
      R.mlctx.vlctx.toCtx binding.motiveTypeTarget motiveType)
    (Htelescope :
      RecursorMotiveTelescope resultLevel indices.length
        (VExpr.mkApps
          (.const (decl.types[target]'H.target_lt).name levels) params)
        familyType motiveType) :
    Nonempty (MotiveAppliesTo R stats info binding
      exposedType syntaxTarget) := by
  let family := VExpr.mkApps
    (.const (decl.types[target]'H.target_lt).name levels) params
  have hrebuild := VExpr.mkApps_getAppFnArgs syntaxTarget
  rw [hspine] at hrebuild
  have hsyntax : syntaxTarget = VExpr.mkApps family indices := by
    rw [← hrebuild]
    simp [family, VExpr.mkApps, List.foldl_append]
  exact ⟨{
    indices := indices
    family := family
    familyActualType := familyActualType
    familyType := familyType
    motiveType := motiveType
    resultLevel := resultLevel
    syntax_eq := hsyntax
    indices_translation := Hindices
    family_typing := Hfamily
    family_type_defeq := HfamilyType
    motive_type_defeq := HmotiveType
    telescope := Htelescope }⟩

/-- Exact-target form of motive application.  Besides typing the result, it
records that the strict translation target is literally the motive
local applied to the index spine of `MotiveAppliesTo` and the checked major premise. -/
theorem MotiveAppliesTo.applyMajorTypedExact
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {elimLevel : Level}
    {info : AddInductive.RecInfo}
    {binding : MotiveBinding R info elimLevel}
    (H : MotiveAppliesTo R stats info binding
      exposedType syntaxTarget)
    {major : Expr} {majorTarget : VExpr}
    (Hmajor : TrExprS R.venv recLparams R.mlctx.vlctx major majorTarget)
    (HmajorType : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
      majorTarget syntaxTarget) :
    let itIndices := exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app (mkAppN info.motive itIndices) major
    let motiveTarget :=
      VExpr.app (VExpr.mkApps binding.motiveTarget H.indices) majorTarget
    TrExprS R.venv recLparams R.mlctx.vlctx motiveApp motiveTarget ∧
      R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
        motiveTarget (.sort H.resultLevel) := by
  have HmajorType' : R.venv.HasType recLparams.length
      R.mlctx.vlctx.toCtx majorTarget (VExpr.mkApps H.family H.indices) := by
    rwa [← H.syntax_eq]
  have Hfamily : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
      H.family H.familyType :=
    H.family_typing.defeqU_r R.checking.tr.wf R.mlctx_wf.tr.wf.toCtx
      H.family_type_defeq
  have Hmotive : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
      binding.motiveTarget H.motiveType :=
    binding.typing.defeqU_r R.checking.tr.wf R.mlctx_wf.tr.wf.toCtx
      H.motive_type_defeq
  have Hresult := H.telescope.applyMajorTyped R.checking.tr.wf
    R.mlctx_wf.tr.wf.toCtx Hfamily Hmotive HmajorType'
  let motiveTarget :=
    VExpr.app (VExpr.mkApps binding.motiveTarget H.indices) majorTarget
  have Hresult' : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
      motiveTarget (.sort H.resultLevel) := by
    simpa [motiveTarget, VExpr.mkApps, List.foldl_append] using Hresult
  have HtargetWF : VExpr.WF R.venv recLparams.length
      R.mlctx.vlctx.toCtx motiveTarget := ⟨.sort H.resultLevel, Hresult'⟩
  have Hargs := List.Forall₂.append' H.indices_translation
    (.cons Hmajor .nil)
  have Htranslated := checkPositivityStep.TrExprS.mkAppList
    R.checking.tr.wf.ordered
    R.mlctx_wf.tr.wf.toCtx binding.motive Hargs (by
      simpa [motiveTarget, VExpr.mkApps, List.foldl_append] using HtargetWF)
  exact ⟨by
    simpa [motiveTarget, Expr.mkAppN_eq_mkAppList,
      Expr.mkAppList_append, VExpr.mkApps, List.foldl_append] using Htranslated,
    Hresult'⟩

/-- A shared family/motive telescope types the complete
motive application.  The result sort is stated exactly for equation
typing; the abstract spine is assembled without invoking executable
inference. -/
theorem MotiveAppliesTo.applyMajorTyped
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {elimLevel : Level}
    {info : AddInductive.RecInfo}
    {binding : MotiveBinding R info elimLevel}
    (H : MotiveAppliesTo R stats info binding
      exposedType syntaxTarget)
    {major : Expr} {majorTarget : VExpr}
    (Hmajor : TrExprS R.venv recLparams R.mlctx.vlctx major majorTarget)
    (HmajorType : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
      majorTarget syntaxTarget) :
    let itIndices := exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app (mkAppN info.motive itIndices) major
    ∃ motiveTarget,
      TrExprS R.venv recLparams R.mlctx.vlctx motiveApp motiveTarget ∧
      R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx motiveTarget
        (.sort H.resultLevel) := by
  rcases H.applyMajorTypedExact Hmajor HmajorType with ⟨Htr, Htyped⟩
  exact ⟨_, Htr, Htyped⟩

/-- Typehood wrapper around `applyMajorTyped`. -/
theorem MotiveAppliesTo.applyMajor
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {elimLevel : Level}
    {info : AddInductive.RecInfo}
    {binding : MotiveBinding R info elimLevel}
    (H : MotiveAppliesTo R stats info binding
      exposedType syntaxTarget)
    {major : Expr} {majorTarget : VExpr}
    (Hmajor : TrExprS R.venv recLparams R.mlctx.vlctx major majorTarget)
    (HmajorType : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
      majorTarget syntaxTarget) :
    let itIndices := exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app (mkAppN info.motive itIndices) major
    ∃ motiveTarget,
      TrExprS R.venv recLparams R.mlctx.vlctx motiveApp motiveTarget ∧
      R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx motiveTarget := by
  rcases H.applyMajorTyped Hmajor HmajorType with ⟨target, Htr, Htyped⟩
  exact ⟨target, Htr, H.resultLevel, Htyped⟩

/-- Rooted, context-polymorphic form of `MotiveAppliesTo`.  This
is the invariant established by the motive pass of `mkRecInfos`; later recursive
field traversals supply only the validated terminal application. -/
def MotiveAppliesAbove
    {root : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF root recLparams)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (target : Nat) (info : AddInductive.RecInfo)
    (elimLevel : Level) : Prop :=
  ∀ {current : AddInductive.Context}
    (R : RecursorContextWF current recLparams)
    (_Hext : RecursorContextExtension Rroot R)
    {depth : Nat} {exposedType : Expr} {syntaxTarget : VExpr}
    (binding : MotiveBinding R info elimLevel),
    TrExprS R.venv recLparams R.mlctx.vlctx exposedType syntaxTarget →
    R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx syntaxTarget →
    RecursorValidatedIndAppAt R.venv recLparams R.mlctx.vlctx stats decl
      depth exposedType syntaxTarget target →
    Nonempty (MotiveAppliesTo R stats info binding
      exposedType syntaxTarget)

theorem MotiveAppliesAbove.toApplication
    (H : MotiveAppliesAbove Rroot stats decl target info elimLevel) :
    MotiveApplicationAbove Rroot stats decl target info elimLevel := by
  intro current R Hext depth exposedType major syntaxTarget
    majorTarget binding Hexposed HsyntaxType Hmajor HmajorType Hvalidated
  rcases H R Hext binding Hexposed HsyntaxType Hvalidated with ⟨Hevidence⟩
  exact Hevidence.applyMajor Hmajor HmajorType

/-- Permutation-free motive telescope produced while opening a
family header.  Unlike `MotiveDecl` below, this structure lives only
under the common parameter domains: later motive-pass index/major frames have
not yet been interleaved with sibling motives.  It is therefore the
form that can be compared with the grouped generated-recursor telescope. -/
structure ClosedMotiveTelescope
    (env : VEnv) (levelParams : List Name)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (target : Nat) (info : AddInductive.RecInfo)
    (elimLevel : Level) : Type where
  target_lt : target < decl.types.length
  params : List VExpr
  indices : List VExpr
  levels : List VLevel
  family : VExpr
  familyResult : VExpr
  motiveType : VExpr
  resultLevel : VLevel
  params_length : params.length = stats.params.size
  indices_length : indices.length = info.indices.size
  levels_length : levels.length = (decl.types[target]'target_lt).uvars
  levels_wf : ∀ level ∈ levels, level.WF levelParams.length
  levels_translation : stats.levels.mapM (VLevel.ofLevel levelParams) =
    some levels
  family_eq : family = VExpr.mkApps
    ((VExpr.const (decl.types[target]'target_lt).name
      levels).liftN params.length 0)
    (bvarSpine params.length)
  motiveType_eq : motiveType = VExpr.wrapForalls indices
    (.forallE
      (VExpr.mkApps (family.liftN indices.length 0)
        (bvarSpine indices.length))
      (.sort resultLevel))
  family_typing : env.HasType levelParams.length params.reverse family
    (VExpr.wrapForalls indices familyResult)
  /-- The full index application is itself a type.  This is the
  result-sort fact needed to form the major binder of the
  motive, stated at the expression used there. -/
  familyApplicationType : env.IsType levelParams.length
    (indices.reverse ++ params.reverse)
    (VExpr.mkApps (family.liftN indices.length 0)
      (bvarSpine indices.length))
  telescope : RecursorMotiveTelescope resultLevel indices.length family
    (VExpr.wrapForalls indices familyResult) motiveType

def ClosedMotiveTelescope.mono
    (H : ClosedMotiveTelescope env levelParams stats decl target info
      elimLevel)
    (henv : env ≤ env') :
    ClosedMotiveTelescope env' levelParams stats decl target info
      elimLevel where
  target_lt := H.target_lt
  params := H.params
  indices := H.indices
  levels := H.levels
  family := H.family
  familyResult := H.familyResult
  motiveType := H.motiveType
  resultLevel := H.resultLevel
  params_length := H.params_length
  indices_length := H.indices_length
  levels_length := H.levels_length
  levels_wf := H.levels_wf
  levels_translation := H.levels_translation
  family_eq := H.family_eq
  motiveType_eq := H.motiveType_eq
  family_typing := H.family_typing.mono henv
  familyApplicationType := H.familyApplicationType.mono henv
  telescope := H.telescope

/-- Context-converted form of the telescope's `applyMajorTyped`.  This is the equation
typing interface: the motive-pass parameter scope may be replaced
by the cached or generated parameter scope before the common inner binder
block is introduced. -/
theorem ClosedMotiveTelescope.applyMajorTypedAfterDefEq
    (C : ClosedMotiveTelescope env levelParams stats decl target info
      elimLevel)
    (henv : env.WF) (base added : List VExpr)
    (Hbase : VEnv.IsDefEqCtx env levelParams.length [] C.params.reverse base)
    (hctx : OnCtx (added.reverse ++ base)
      (env.IsType levelParams.length))
    (indexTargets : List VExpr)
    (hindices : indexTargets.length = C.indices.length)
    (motive major : VExpr)
    (Hmotive : env.HasType levelParams.length (added.reverse ++ base) motive
      (C.motiveType.liftN added.length 0))
    (Hmajor : env.HasType levelParams.length (added.reverse ++ base) major
      (VExpr.mkApps (C.family.liftN added.length 0) indexTargets)) :
    env.HasType levelParams.length (added.reverse ++ base)
      (.app (VExpr.mkApps motive indexTargets) major)
      (.sort C.resultLevel) := by
  have HfamilyBase := C.family_typing.defeqDFC henv.ordered Hbase
  have W : Ctx.LiftN added.length 0 base (added.reverse ++ base) := by
    exact .zero added.reverse (by simp)
  have Hfamily := HfamilyBase.weakN henv.ordered W
  have Htelescope := C.telescope.liftN added.length 0
  rw [← hindices] at Htelescope
  exact Htelescope.applyMajorTyped henv hctx Hfamily Hmotive Hmajor

/-- Context-rooted data for one generated motive.  The motive pass of
`mkRecInfos` establishes it at the point where the motive is
introduced.  Its family prefix has a unique translation, while the
stored motive type is compared definitionally after later context extension. -/
structure MotiveDecl
    {root : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF root recLparams)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (target : Nat) (info : AddInductive.RecInfo)
    (elimLevel : Level) : Type where
  canonical : ClosedMotiveTelescope Rroot.venv recLparams stats
    decl target info elimLevel
  target_lt : target < decl.types.length
  indexCount : info.indices.size =
    (decl.types[target]'target_lt).numIndices
  /-- The index telescope passed the declaration-universe
  guard before this family's major and motive declarations were added. -/
  indexUniverses : (root.lctx.mkForall info.indices (.sort .zero)).levelParamsIn root.lparams = true
  family : VExpr
  familyActualType : VExpr
  familyType : VExpr
  motiveActualType : VExpr
  motiveType : VExpr
  resultLevel : VLevel
  /-- The executable motive telescope before it is weakened through
  this family's opened indices, major, and motive declarations.  Keeping
  the closed scope explicit is what permits later inverse weakening to
  discard the interleaved executable frames and return to the cached
  parameter context. -/
  motiveClosedScope : VLCtx
  motiveClosedAmbient : VLCtx
  motiveParameterScope : VLCtx
  motiveClosedContext : motiveClosedScope =
    motiveClosedAmbient ++ motiveParameterScope
  motiveParameterAlignment : VEnv.IsDefEqCtx Rroot.venv
    recLparams.length [] canonical.params.reverse motiveParameterScope.toCtx
  motiveParameterDecls : List.Forall₂
    checkInductiveTypes.loopType.CachedParameterDecl
    stats.params.toList.reverse motiveParameterScope
  /-- The index front also exposes the parameter scope below those
  indices, together with its literal weakening into the closed executable
  context.  This is the context in which the generated motive is first
  built. -/
  motiveSourceScope : VLCtx
  motiveSourceExpanded : VLCtx
  motiveSourceShift : Lift
  motiveSourceAlignment : VEnv.IsDefEqCtx Rroot.venv recLparams.length []
    canonical.params.reverse motiveSourceScope.toCtx
  motiveSourceParameterScope : motiveSourceScope = motiveParameterScope
  motiveSourceLift : VLCtx.FVLift' motiveSourceScope motiveSourceExpanded
    0 motiveSourceShift 0
  motiveSourceContext : VLCtx.IsDefEq Rroot.venv recLparams.length
    motiveSourceExpanded motiveClosedScope
  motiveSourceNoBV : VLCtx.NoBV motiveSourceScope
  motiveSourceFVars : FVarsIn (· ∈ motiveSourceScope.fvars)
    (root.lctx.mkForall info.indices
      (root.lctx.mkForall #[info.major] (.sort elimLevel)))
  /-- The motive translated directly in its parameter scope, from the
checker context in which its indices were opened. -/
  motiveSourceTarget : VExpr
  motiveSourceTr : TrExprS Rroot.venv recLparams motiveSourceScope
    (root.lctx.mkForall info.indices
      (root.lctx.mkForall #[info.major] (.sort elimLevel)))
    motiveSourceTarget
  motiveSourceType : Rroot.venv.IsType recLparams.length
    motiveSourceScope.toCtx motiveSourceTarget
  motiveSourceCanonical : Rroot.venv.IsDefEqU recLparams.length
    motiveSourceScope.toCtx motiveSourceTarget canonical.motiveType
  motiveSourceWF : motiveSourceScope.WF Rroot.venv recLparams.length
  motiveClosedTarget : VExpr
  motiveClosedTr : TrExprS Rroot.venv recLparams motiveClosedScope
    (root.lctx.mkForall info.indices
      (root.lctx.mkForall #[info.major] (.sort elimLevel)))
    motiveClosedTarget
  motiveClosedType : Rroot.venv.IsType recLparams.length
    motiveClosedScope.toCtx motiveClosedTarget
  motiveClosedCanonicalTarget : VExpr
  motiveClosedCanonicalEq :
    canonical.motiveType.lift' motiveSourceShift =
      motiveClosedCanonicalTarget
  motiveClosedCanonicalDefEq : Rroot.venv.IsDefEqU recLparams.length
    motiveClosedScope.toCtx motiveClosedTarget motiveClosedCanonicalTarget
  motiveReopenedCanonicalTarget : VExpr
  motiveTypeCanonicalEq : motiveType = motiveReopenedCanonicalTarget
  familyTr : TrExprS Rroot.venv recLparams Rroot.mlctx.vlctx
    (mkAppN stats.indConsts[target]! stats.params) family
  familyTyping : Rroot.venv.HasType recLparams.length
    Rroot.mlctx.vlctx.toCtx family familyActualType
  familyTypeDefEq : Rroot.venv.IsDefEqU recLparams.length
    Rroot.mlctx.vlctx.toCtx familyActualType familyType
  indicesBound : FVarArrayIn root info.indices
  majorBound : FVarArrayIn root #[info.major]
  motiveTypeTr : TrExprS Rroot.venv recLparams Rroot.mlctx.vlctx
    (root.lctx.mkForall info.indices
      (root.lctx.mkForall #[info.major] (.sort elimLevel))) motiveActualType
  motiveTypeDefEq : Rroot.venv.IsDefEqU recLparams.length
    Rroot.mlctx.vlctx.toCtx motiveActualType motiveType
  telescope : RecursorMotiveTelescope resultLevel info.indices.size
    family familyType motiveType

/-- `MotiveDecl` remains valid after later executable frames extend its
root context.  The paired generated telescope is unchanged, while every
executable target is weakened by the recursor-context lift. -/
def MotiveDecl.mono
    {root current : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams}
    (H : MotiveDecl Rroot stats decl target info elimLevel)
    (Hext : RecursorContextExtension Rroot Rcurrent) :
    MotiveDecl Rcurrent stats decl target info elimLevel := by
  have hmajorSource :
      current.lctx.mkForall #[info.major] (.sort elimLevel) =
        root.lctx.mkForall #[info.major] (.sort elimLevel) :=
    H.majorBound.mkForall_mono Hext.contextLE _
  have hmotiveSource :
      current.lctx.mkForall info.indices
          (current.lctx.mkForall #[info.major] (.sort elimLevel)) =
        root.lctx.mkForall info.indices
          (root.lctx.mkForall #[info.major] (.sort elimLevel)) := by
    calc
      current.lctx.mkForall info.indices
          (current.lctx.mkForall #[info.major] (.sort elimLevel)) =
          current.lctx.mkForall info.indices
            (root.lctx.mkForall #[info.major] (.sort elimLevel)) :=
        congrArg (fun body => current.lctx.mkForall info.indices body)
          hmajorSource
      _ = root.lctx.mkForall info.indices
            (root.lctx.mkForall #[info.major] (.sort elimLevel)) :=
        H.indicesBound.mkForall_mono Hext.contextLE _
  have HmotiveTypeTr := Hext.weakTrExprS H.motiveTypeTr
  rw [← hmotiveSource] at HmotiveTypeTr
  have HmotiveClosedTr := H.motiveClosedTr
  rw [← hmotiveSource] at HmotiveClosedTr
  exact {
    canonical := H.canonical.mono (by
      rw [Hext.venv_eq]
      exact VEnv.LE.rfl)
    target_lt := H.target_lt
    indexCount := H.indexCount
    indexUniverses := by
      rw [H.indicesBound.mkForall_mono Hext.contextLE, Hext.contextLE.lparams_eq]
      exact H.indexUniverses
    family := H.family.lift' (Hext.shift.consN 0)
    familyActualType := H.familyActualType.lift' (Hext.shift.consN 0)
    familyType := H.familyType.lift' (Hext.shift.consN 0)
    motiveActualType := H.motiveActualType.lift' (Hext.shift.consN 0)
    motiveType := H.motiveType.lift' (Hext.shift.consN 0)
    resultLevel := H.resultLevel
    motiveClosedScope := H.motiveClosedScope
    motiveClosedAmbient := H.motiveClosedAmbient
    motiveParameterScope := H.motiveParameterScope
    motiveClosedContext := H.motiveClosedContext
    motiveParameterAlignment := by
      change Rcurrent.venv.IsDefEqCtx recLparams.length []
        H.canonical.params.reverse H.motiveParameterScope.toCtx
      simpa only [Hext.venv_eq] using H.motiveParameterAlignment
    motiveParameterDecls := H.motiveParameterDecls
    motiveSourceScope := H.motiveSourceScope
    motiveSourceExpanded := H.motiveSourceExpanded
    motiveSourceShift := H.motiveSourceShift
    motiveSourceAlignment := by
      change Rcurrent.venv.IsDefEqCtx recLparams.length []
        H.canonical.params.reverse H.motiveSourceScope.toCtx
      simpa only [Hext.venv_eq] using H.motiveSourceAlignment
    motiveSourceParameterScope := H.motiveSourceParameterScope
    motiveSourceLift := H.motiveSourceLift
    motiveSourceContext := by
      simpa only [Hext.venv_eq] using H.motiveSourceContext
    motiveSourceNoBV := H.motiveSourceNoBV
    motiveSourceFVars := by
      rw [hmotiveSource]
      exact H.motiveSourceFVars
    motiveSourceTarget := H.motiveSourceTarget
    motiveSourceTr := by
      rw [hmotiveSource]
      simpa only [Hext.venv_eq] using H.motiveSourceTr
    motiveSourceType := by
      simpa only [Hext.venv_eq] using H.motiveSourceType
    motiveSourceCanonical := by
      show Rcurrent.venv.IsDefEqU recLparams.length H.motiveSourceScope.toCtx
        H.motiveSourceTarget H.canonical.motiveType
      rw [Hext.venv_eq]
      exact H.motiveSourceCanonical
    motiveSourceWF := by
      simpa only [Hext.venv_eq] using H.motiveSourceWF
    motiveClosedTarget := H.motiveClosedTarget
    motiveClosedTr := by
      simpa only [Hext.venv_eq] using HmotiveClosedTr
    motiveClosedType := by
      simpa only [Hext.venv_eq] using H.motiveClosedType
    motiveClosedCanonicalTarget := H.motiveClosedCanonicalTarget
    motiveClosedCanonicalEq := H.motiveClosedCanonicalEq
    motiveClosedCanonicalDefEq := by
      simpa only [Hext.venv_eq] using H.motiveClosedCanonicalDefEq
    motiveReopenedCanonicalTarget := H.motiveReopenedCanonicalTarget.lift'
      (Hext.shift.consN 0)
    motiveTypeCanonicalEq := congrArg
      (fun target => target.lift' (Hext.shift.consN 0))
      H.motiveTypeCanonicalEq
    familyTr := Hext.weakTrExprS H.familyTr
    familyTyping := Hext.weakHasType H.familyTyping
    familyTypeDefEq := Hext.weakDefEqU H.familyTypeDefEq
    indicesBound := H.indicesBound.mono Hext.contextLE
    majorBound := H.majorBound.mono Hext.contextLE
    motiveTypeTr := HmotiveTypeTr
    motiveTypeDefEq := Hext.weakDefEqU H.motiveTypeDefEq
    telescope := H.telescope.lift' (Hext.shift.consN 0) }

/-- Changing only irrelevant `RecInfo` fields, such as the accumulated minor
array, preserves `MotiveDecl`. -/
def MotiveDecl.congrInfo
    (H : MotiveDecl Rroot stats decl target info elimLevel)
    (hindices : info'.indices = info.indices)
    (hmajor : info'.major = info.major) :
    MotiveDecl Rroot stats decl target info' elimLevel where
  canonical := {
    H.canonical with
    indices_length := by simpa [hindices] using H.canonical.indices_length }
  target_lt := H.target_lt
  indexCount := by simpa [hindices] using H.indexCount
  indexUniverses := by simpa only [hindices] using H.indexUniverses
  family := H.family
  familyActualType := H.familyActualType
  familyType := H.familyType
  motiveActualType := H.motiveActualType
  motiveType := H.motiveType
  resultLevel := H.resultLevel
  motiveClosedScope := H.motiveClosedScope
  motiveClosedAmbient := H.motiveClosedAmbient
  motiveParameterScope := H.motiveParameterScope
  motiveClosedContext := H.motiveClosedContext
  motiveParameterAlignment := H.motiveParameterAlignment
  motiveParameterDecls := H.motiveParameterDecls
  motiveSourceScope := H.motiveSourceScope
  motiveSourceExpanded := H.motiveSourceExpanded
  motiveSourceShift := H.motiveSourceShift
  motiveSourceAlignment := H.motiveSourceAlignment
  motiveSourceParameterScope := H.motiveSourceParameterScope
  motiveSourceLift := H.motiveSourceLift
  motiveSourceContext := H.motiveSourceContext
  motiveSourceNoBV := H.motiveSourceNoBV
  motiveSourceFVars := by
    simpa [hindices, hmajor] using H.motiveSourceFVars
  motiveSourceTarget := H.motiveSourceTarget
  motiveSourceTr := by simpa [hindices, hmajor] using H.motiveSourceTr
  motiveSourceType := H.motiveSourceType
  motiveSourceCanonical := H.motiveSourceCanonical
  motiveSourceWF := H.motiveSourceWF
  motiveClosedTarget := H.motiveClosedTarget
  motiveClosedTr := by simpa [hindices, hmajor] using H.motiveClosedTr
  motiveClosedType := H.motiveClosedType
  motiveClosedCanonicalTarget := H.motiveClosedCanonicalTarget
  motiveClosedCanonicalEq := H.motiveClosedCanonicalEq
  motiveClosedCanonicalDefEq := H.motiveClosedCanonicalDefEq
  motiveReopenedCanonicalTarget := H.motiveReopenedCanonicalTarget
  motiveTypeCanonicalEq := H.motiveTypeCanonicalEq
  familyTr := H.familyTr
  familyTyping := H.familyTyping
  familyTypeDefEq := H.familyTypeDefEq
  indicesBound := by simpa [hindices] using H.indicesBound
  majorBound := by simpa [hmajor] using H.majorBound
  motiveTypeTr := by simpa [hindices, hmajor] using H.motiveTypeTr
  motiveTypeDefEq := H.motiveTypeDefEq
  telescope := by simpa [hindices] using H.telescope

/-- `MotiveDecl` supplies the context-polymorphic property `MotiveAppliesAbove`
used by recursive constructor traversal.  Context extensions preserve
`MotiveDecl`; unique translation identifies the validated family prefix and
relates the later motive binding to the stored
generated motive telescope. -/
theorem MotiveDecl.toTelescopeAt
    {root : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    (H : MotiveDecl Rroot stats decl target info
      elimLevel) :
    MotiveAppliesAbove Rroot stats decl target info elimLevel := by
  intro current R Hext depth exposedType syntaxTarget binding Hexposed
    HsyntaxType Hvalidated
  rcases Hvalidated.indices_payload with
    ⟨levels, params, indices, hspine, _hparams, hindicesLength,
      Hindices, HfamilyPayload⟩
  have HfamilyWeak := Hext.weakTrExprS H.familyTr
  have hfamilyEq :
      VExpr.mkApps
          (.const (decl.types[target]'Hvalidated.target_lt).name levels)
          params =
        H.family.lift' (Hext.shift.consN 0) :=
    HfamilyPayload.unique_of_syn HfamilyWeak
  have HfamilyTyping := Hext.weakHasType H.familyTyping
  have HfamilyTyping' : R.venv.HasType recLparams.length
      R.mlctx.vlctx.toCtx
      (VExpr.mkApps
        (.const (decl.types[target]'Hvalidated.target_lt).name levels)
        params)
      (H.familyActualType.lift' (Hext.shift.consN 0)) := by
    rwa [hfamilyEq]
  have HfamilyTypeDefEq := Hext.weakDefEqU H.familyTypeDefEq
  have Htelescope := H.telescope.lift' (Hext.shift.consN 0)
  have hmajorSource :
      current.lctx.mkForall #[info.major] (.sort elimLevel) =
        root.lctx.mkForall #[info.major] (.sort elimLevel) :=
    H.majorBound.mkForall_mono Hext.contextLE _
  have hmotiveSource :
      current.lctx.mkForall info.indices
          (current.lctx.mkForall #[info.major] (.sort elimLevel)) =
        root.lctx.mkForall info.indices
          (root.lctx.mkForall #[info.major] (.sort elimLevel)) := by
    calc
      current.lctx.mkForall info.indices
          (current.lctx.mkForall #[info.major] (.sort elimLevel)) =
          current.lctx.mkForall info.indices
            (root.lctx.mkForall #[info.major] (.sort elimLevel)) :=
        congrArg (fun body => current.lctx.mkForall info.indices body)
          hmajorSource
      _ = root.lctx.mkForall info.indices
            (root.lctx.mkForall #[info.major] (.sort elimLevel)) :=
        H.indicesBound.mkForall_mono Hext.contextLE _
  have HmotiveWeak := Hext.weakTrExprS H.motiveTypeTr
  rw [← hmotiveSource] at HmotiveWeak
  have HbindingActual : R.venv.IsDefEqU recLparams.length
      R.mlctx.vlctx.toCtx binding.motiveTypeTarget
      (H.motiveActualType.lift' (Hext.shift.consN 0)) :=
    (HmotiveWeak.uniq R.checking.tr.wf
      (.refl R.checking.tr.wf R.mlctx_wf.tr.wf)
      binding.motiveType).symm
  have HmotiveDefEq := HbindingActual.trans R.checking.tr.wf
    R.mlctx_wf.tr.wf.toCtx (Hext.weakDefEqU H.motiveTypeDefEq)
  have Htelescope' : RecursorMotiveTelescope H.resultLevel indices.length
      (VExpr.mkApps
        (.const (decl.types[target]'Hvalidated.target_lt).name levels)
        params)
      (H.familyType.lift' (Hext.shift.consN 0))
      (H.motiveType.lift' (Hext.shift.consN 0)) := by
    rw [hfamilyEq, hindicesLength, ← H.indexCount]
    simpa using Htelescope
  exact Hvalidated.motiveAppliesTo binding
    (H.familyActualType.lift' (Hext.shift.consN 0))
    (H.familyType.lift' (Hext.shift.consN 0))
    (H.motiveType.lift' (Hext.shift.consN 0)) H.resultLevel hspine Hindices
    HfamilyTyping' HfamilyTypeDefEq HmotiveDefEq Htelescope'

/-- `MotiveAppliesAbove` is insensitive to the minor array stored
beside the motive, indices, and major.  This extensional form is used for
the in-place record updates performed by the minor pass of `mkRecInfos`. -/
theorem MotiveAppliesAbove.congrInfo
    (H : MotiveAppliesAbove Rroot stats decl target info elimLevel)
    (hmotive : info'.motive = info.motive)
    (hindices : info'.indices = info.indices)
    (hmajor : info'.major = info.major) :
    MotiveAppliesAbove Rroot stats decl target info' elimLevel := by
  intro current R Hext depth exposedType syntaxTarget binding' Hexposed
    HsyntaxType Hvalidated
  let binding : MotiveBinding R info elimLevel := {
    motiveTarget := binding'.motiveTarget
    motiveTypeTarget := binding'.motiveTypeTarget
    motive := by simpa [hmotive] using binding'.motive
    motiveType := by simpa [hindices, hmajor] using binding'.motiveType
    typing := binding'.typing
    typeIsType := binding'.typeIsType }
  rcases H R Hext binding Hexposed HsyntaxType Hvalidated with ⟨Hevidence⟩
  exact ⟨{
    indices := Hevidence.indices
    family := Hevidence.family
    familyActualType := Hevidence.familyActualType
    familyType := Hevidence.familyType
    motiveType := Hevidence.motiveType
    resultLevel := Hevidence.resultLevel
    syntax_eq := Hevidence.syntax_eq
    indices_translation := Hevidence.indices_translation
    family_typing := Hevidence.family_typing
    family_type_defeq := Hevidence.family_type_defeq
    motive_type_defeq := Hevidence.motive_type_defeq
    telescope := Hevidence.telescope }⟩

/-- Pointwise shared family/motive telescopes for a mutual `RecInfo`
array.  This is stronger and easier to establish than storing applications
for arbitrary majors directly. -/
structure RecInfoMotiveTelescopes
    {root : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF root recLparams)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (parameterCtx : List VExpr)
    (recInfos : Array AddInductive.RecInfo) (elimLevel : Level) : Prop where
  telescope : ∀ target (_htarget : target < recInfos.size),
    MotiveAppliesAbove Rroot stats decl target recInfos[target]!
      elimLevel
  motiveDecls : ∀ target (_htarget : target < recInfos.size),
    ∃ S : MotiveDecl Rroot stats decl target
        recInfos[target]! elimLevel,
      VEnv.IsDefEqCtx Rroot.venv recLparams.length []
        S.canonical.params.reverse parameterCtx
  canonical : ∀ target (_htarget : target < recInfos.size),
    ∃ C : ClosedMotiveTelescope Rroot.venv recLparams stats
        decl target recInfos[target]! elimLevel,
      VEnv.IsDefEqCtx Rroot.venv recLparams.length []
        C.params.reverse parameterCtx

theorem RecInfoMotiveTelescopes.empty
    (Rroot : RecursorContextWF root recLparams)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (parameterCtx : List VExpr)
    (elimLevel : Level) :
    RecInfoMotiveTelescopes Rroot stats decl parameterCtx #[] elimLevel where
  telescope target htarget := by simp at htarget
  motiveDecls target htarget := by simp at htarget
  canonical target htarget := by simp at htarget

theorem RecInfoMotiveTelescopes.mono
    (H : RecInfoMotiveTelescopes Rroot stats decl parameterCtx recInfos
      elimLevel)
    (Hext : RecursorContextExtension Rroot Rcurrent) :
    RecInfoMotiveTelescopes Rcurrent stats decl parameterCtx recInfos
      elimLevel where
  telescope target htarget := fun R Hlater =>
    H.telescope target htarget R (Hext.trans Hlater)
  motiveDecls target htarget := by
    rcases H.motiveDecls target htarget with ⟨S, hparams⟩
    refine ⟨S.mono Hext, ?_⟩
    simpa [MotiveDecl.mono,
      ClosedMotiveTelescope.mono, Hext.venv_eq] using hparams
  canonical target htarget := by
    rw [Hext.venv_eq]
    exact H.canonical target htarget

theorem RecInfoMotiveTelescopes.push
    {root : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    (H : RecInfoMotiveTelescopes Rroot stats decl parameterCtx recInfos
      elimLevel)
    (next : AddInductive.RecInfo)
    (Hnext : MotiveAppliesAbove Rroot stats decl recInfos.size next
      elimLevel)
    (Hseed : MotiveDecl Rroot stats decl recInfos.size next
      elimLevel)
    (Hparams :
      VEnv.IsDefEqCtx Rroot.venv recLparams.length []
        Hseed.canonical.params.reverse parameterCtx) :
    RecInfoMotiveTelescopes Rroot stats decl parameterCtx (recInfos.push next)
      elimLevel where
  telescope target htarget := by
    by_cases hlast : target = recInfos.size
    · subst target
      have hget : (recInfos.push next)[recInfos.size]! = next := by simp
      rw [hget]
      exact Hnext
    · have hold : target < recInfos.size := by
        simp only [Array.size_push] at htarget
        omega
      have hget : (recInfos.push next)[target]! = recInfos[target]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos htarget, dif_pos hold]
        exact Array.getElem_push_lt hold
      rw [hget]
      exact H.telescope target hold
  motiveDecls target htarget := by
    by_cases hlast : target = recInfos.size
    · subst target
      have hget : (recInfos.push next)[recInfos.size]! = next := by simp
      rw [hget]
      exact ⟨Hseed, Hparams⟩
    · have hold : target < recInfos.size := by
        simp only [Array.size_push] at htarget
        omega
      have hget : (recInfos.push next)[target]! = recInfos[target]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos htarget, dif_pos hold]
        exact Array.getElem_push_lt hold
      rw [hget]
      exact H.motiveDecls target hold
  canonical target htarget := by
    by_cases hlast : target = recInfos.size
    · subst target
      have hget : (recInfos.push next)[recInfos.size]! = next := by simp
      rw [hget]
      exact ⟨Hseed.canonical, Hparams⟩
    · have hold : target < recInfos.size := by
        simp only [Array.size_push] at htarget
        omega
      have hget : (recInfos.push next)[target]! = recInfos[target]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos htarget, dif_pos hold]
        exact Array.getElem_push_lt hold
      rw [hget]
      exact H.canonical target hold

/-- Adding a minor premise does not change any family's motive telescope.
The executable minor pass updates `RecInfo.minors` in place; this
lemma keeps the motive-pass property available after
every constructor. -/
theorem RecInfoMotiveTelescopes.modifyMinors
    (H : RecInfoMotiveTelescopes Rroot stats decl parameterCtx recInfos
      elimLevel)
    (owner : Nat) (f : Array Expr → Array Expr) :
    RecInfoMotiveTelescopes Rroot stats decl parameterCtx
      (recInfos.modify owner fun info =>
        { info with minors := f info.minors }) elimLevel where
  telescope target htarget := by
    have hold : target < recInfos.size := by simpa using htarget
    apply MotiveAppliesAbove.congrInfo (H.telescope target hold)
    all_goals
      by_cases howner : owner = target
      · subst target
        rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos owner _ hold]
      · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos owner target _
            hold howner]
  motiveDecls target htarget := by
    have hold : target < recInfos.size := by simpa using htarget
    rcases H.motiveDecls target hold with ⟨S, hparams⟩
    by_cases howner : owner = target
    · subst target
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos owner _ hold]
      refine ⟨S.congrInfo rfl rfl, ?_⟩
      simpa [MotiveDecl.congrInfo] using hparams
    · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos owner target _
            hold howner]
      exact ⟨S, hparams⟩
  canonical target htarget := by
    have hold : target < recInfos.size := by simpa using htarget
    rcases H.canonical target hold with ⟨C, hparams⟩
    by_cases howner : owner = target
    · subst target
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos owner _ hold]
      exact ⟨{ C with indices_length := by simpa using C.indices_length },
        hparams⟩
    · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos owner target _
          hold howner]
      exact ⟨C, hparams⟩

/-- Pointwise motive-application properties for the complete mutual `RecInfo`
array.  Array indexing, rather than family names, is intentional: the executable
selects motives with the target returned by `isValidIndApp?`, and the
validated application (`RecursorValidatedIndAppAt`) shows that the same target denotes the
source family. -/
structure RecInfoMotiveApplications
    {root : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF root recLparams)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (recInfos : Array AddInductive.RecInfo) (elimLevel : Level) : Prop where
  application : ∀ target (_htarget : target < recInfos.size),
    MotiveApplicationAbove Rroot stats decl target recInfos[target]!
      elimLevel

theorem RecInfoMotiveApplications.empty
    (Rroot : RecursorContextWF root recLparams)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (elimLevel : Level) :
    RecInfoMotiveApplications Rroot stats decl #[] elimLevel where
  application target htarget := by simp at htarget

theorem RecInfoMotiveTelescopes.applications
    (H : RecInfoMotiveTelescopes Rroot stats decl parameterCtx recInfos
      elimLevel) :
    RecInfoMotiveApplications Rroot stats decl recInfos elimLevel where
  application target htarget :=
    MotiveAppliesAbove.toApplication (H.telescope target htarget)

/-- Recover one motive's lookup data `MotiveBinding` from the binding,
binder-type, and telescope-shape invariants established by the motive pass. -/
theorem MotiveTypes.motiveBinding
    (R : RecursorContextWF c recLparams)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoBinderTypes c recInfos)
    (Hshape : MotiveTypes c recInfos
      Horigins.motiveTypes elimLevel)
    (target : Nat) (htarget : target < recInfos.size) :
    Nonempty (MotiveBinding R recInfos[target]! elimLevel) := by
  have htargetMap : target < (recInfos.map (·.motive)).size := by
    simpa using htarget
  rcases Hbindings.motives.declarationAt R.toBindingContextWF target
      htargetMap with ⟨D⟩
  have hmotive : recInfos[target]!.motive = .fvar D.fvar := by
    have h := D.expression
    simpa [Array.getElem!_eq_getD, Array.getD, htarget] using h
  have htype : D.type =
      c.lctx.mkForall recInfos[target]!.indices
        (c.lctx.mkForall #[recInfos[target]!.major] (.sort elimLevel)) :=
    (Horigins.motives.type_eq D).trans (Hshape.shape target htarget)
  have hfind := D.declaration
  rw [R.toBindingContextWF.wf.find?_eq_find?_toList] at hfind
  have hmember : (.cdecl D.index D.fvar D.userName D.type
      D.binderInfo D.kind) ∈ c.lctx.toList :=
    List.mem_of_find?_eq_some hfind
  have hmember' : (.cdecl D.index D.fvar D.userName D.type
      D.binderInfo D.kind) ∈ R.mlctx.lctx.toList := by
    rw [R.lctx_eq]
    exact hmember
  rcases R.mlctx_wf.tr.find?_of_mem R.checking.tr.wf hmember' with
    ⟨motiveTarget, motiveTypeTarget, hlookup, _hvalueBelow,
      _htypeBelow, hmotiveTr, hmotiveTypeTr⟩
  have hmotiveTyping := R.mlctx_wf.tr.wf.find?_wf
    R.checking.tr.wf.ordered hlookup
  refine ⟨{
    motiveTarget := motiveTarget
    motiveTypeTarget := motiveTypeTarget
    motive := ?_
    motiveType := ?_
    typing := hmotiveTyping
    typeIsType := hmotiveTyping.isType R.checking.tr.wf
      R.mlctx_wf.tr.wf.toCtx }⟩
  · simpa [Lean.LocalDecl.value', hmotive] using hmotiveTr
  · simpa [Lean.LocalDecl.type, htype] using hmotiveTypeTr

end VerifyInductive
end Lean4Lean
