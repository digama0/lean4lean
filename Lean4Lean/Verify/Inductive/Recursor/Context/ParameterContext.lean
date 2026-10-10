import Lean4Lean.Verify.Inductive.Constructor.Tails
import Lean4Lean.Verify.Inductive.Recursor.Signature.Counts
import Lean4Lean.Verify.Inductive.Header.Check
import Lean4Lean.Verify.Inductive.Context

/-! The parameter context of the recursor construction.

The executable chooses the elimination level with `getElimLevel` (zero, or a universe
parameter fresh for the declaration) and runs the recursor construction under the universe
list `getRecLevelParams`, which prepends that parameter in the large-elimination case.
This file moves the facts established in the header and constructor phases to that universe
list: `ContextWF.toAdmissibleRecursorContextWF` builds the recursor context, and
`RecursorParameterContextSuffix` records that the cached parameters sit, unchanged, below the
locals the recursor construction adds (motives, majors, minors, induction hypotheses).
`RecursorReusedParameterScope` exposes one cached parameter of that suffix, for the header
steps that are run again for later families. -/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment
namespace VerifyInductive

@[simp] theorem VInductDecl.recursorName_eq_mkRecName
    (decl : VInductDecl) (type : VInductiveType) :
    decl.recursorName type = Lean.mkRecName type.name := rfl

/-- The recursor's universe list has either the declaration's universe count or one more
(the fresh elimination universe). -/
theorem AddInductive.getRecLevelParams_length :
    (AddInductive.getRecLevelParams elimLevel lparams).length = lparams.length ∨
    (AddInductive.getRecLevelParams elimLevel lparams).length =
      lparams.length + 1 := by
  cases elimLevel with
  | param u => simp [AddInductive.getRecLevelParams]
  | _ => simp [AddInductive.getRecLevelParams]

/-- The elimination levels `getElimLevel` can produce: `0` for a small eliminator, or a
universe parameter fresh for the declaration for a large one. -/
def AddInductive.AdmissibleElimLevel (lparams : List Name) : Level → Prop
  | .zero => True
  | .param name => name ∉ lparams
  | _ => False

theorem AddInductive.getElimLevel.loop.WF
    (lparams : List Name) (candidate : Name) (i fuel : Nat)
    (c : AddInductive.Context) :
    (AddInductive.getElimLevel.loop lparams candidate i fuel c).WF
      fun level => ∃ name, level = .param name ∧ name ∉ lparams := by
  induction fuel generalizing candidate i with
  | zero =>
    rw [AddInductive.getElimLevel.loop]
    exact Except.WF.throw
  | succ fuel ih =>
    rw [AddInductive.getElimLevel.loop]
    by_cases hcontains : lparams.contains candidate = true
    · rw [if_pos hcontains]
      exact ih _ _
    · have hnotMem : candidate ∉ lparams := by
        intro hmem
        exact hcontains (List.contains_iff_mem.mpr hmem)
      have hp : (pure (Level.param candidate) :
          Except Exception Level).WF
          (fun level => ∃ name, level = .param name ∧ name ∉ lparams) :=
        Except.WF.pure ⟨candidate, rfl, hnotMem⟩
      rw [if_neg hcontains]
      exact hp

/-- `getElimLevel` returns an admissible elimination level: zero, or a universe parameter
fresh for the declaration's universe list. -/
theorem AddInductive.getElimLevel.WF
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (c : AddInductive.Context) :
    (AddInductive.getElimLevel stats indTypes c).WF
      (AddInductive.AdmissibleElimLevel c.lparams) := by
  unfold AddInductive.getElimLevel
  have Hlarge : (AddInductive.isLargeEliminator stats indTypes c).WF
      (fun _ => True) := fun _ _ => trivial
  refine Hlarge.bind fun large _ => ?_
  cases large with
  | false =>
    exact Except.WF.pure trivial
  | true =>
    have hread : ((readThe AddInductive.Context :
        AddInductive.M AddInductive.Context) c).WF (fun c' => c' = c) := by
      intro c' h
      cases h
      rfl
    refine readerBind.WF (x := readThe AddInductive.Context) hread
      fun c' hc' => ?_
    subst c'
    exact (AddInductive.getElimLevel.loop.WF c.lparams `u 1
      (c.lparams.length + 1) c).mono fun level Hlevel => by
        rcases Hlevel with ⟨name, rfl, hfresh⟩
        exact hfresh

/-- An admissible elimination level translates under the recursor's universe list
`getRecLevelParams`. -/
theorem AddInductive.AdmissibleElimLevel.ofLevel
    (H : AddInductive.AdmissibleElimLevel lparams elimLevel) :
    ∃ level, VLevel.ofLevel
      (AddInductive.getRecLevelParams elimLevel lparams) elimLevel =
        some level := by
  cases elimLevel with
  | zero => exact ⟨.zero, rfl⟩
  | param name =>
    exact ⟨.param 0, by
      simp [AddInductive.getRecLevelParams, VLevel.ofLevel]⟩
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at H

/-- The motive codomain `Sort elimLevel` translates under the recursor's universe list
to a well-formed sort. The fact is proved directly, without `checkRecursorTypes`. -/
theorem AddInductive.AdmissibleElimLevel.sortType
    (H : AddInductive.AdmissibleElimLevel lparams elimLevel) :
    ∃ level,
      TrExprS env (AddInductive.getRecLevelParams elimLevel lparams) Δ
        (.sort elimLevel) (.sort level) ∧
      env.IsType
        (AddInductive.getRecLevelParams elimLevel lparams).length
        Δ.toCtx (.sort level) := by
  rcases H.ofLevel with ⟨level, hlevel⟩
  refine ⟨level, TrExprS.sort hlevel, ?_⟩
  exact ⟨.succ level, VEnv.HasType.sort (.of_ofLevel hlevel)⟩

/-- A header context, moved to the recursor's universe list, is a recursor context, for
either admissible elimination level. -/
def ContextWF.toAdmissibleRecursorContextWF
    (H : ContextWF c)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    RecursorContextWF
      ({ c with typeCheckerLParams :=
          some <| AddInductive.getRecLevelParams elimLevel c.lparams })
      (AddInductive.getRecLevelParams elimLevel c.lparams) := by
  cases elimLevel with
  | zero =>
    simpa [AddInductive.getRecLevelParams] using H.toRecursorContextWF
  | param name =>
    simpa [AddInductive.getRecLevelParams] using
      H.prependRecursorLevelParam Helim
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

@[simp] theorem ContextWF.toAdmissibleRecursorContextWF_venv
    (H : ContextWF c)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    (H.toAdmissibleRecursorContextWF Helim).venv = H.venv := by
  cases elimLevel with
  | zero => rfl
  | param name => rfl
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- The cached parameters form the bottom of the recursor context, translated under the
recursor's universe list. The locals the recursor construction adds (motives, majors and
so on) accumulate in `ambientDecls`, and the header steps run again for later families
start from the unchanged suffix `parameterDecls`. Only translations that remain valid after
the optional fresh elimination universe is prepended are recorded. -/
structure RecursorParameterContextSuffix
    {c : AddInductive.Context}
    (R : RecursorContextWF c recLparams)
    (stats : AddInductive.InductiveStats) (depth : Nat) : Type where
  ambientDecls : VLCtx
  parameterDecls : VLCtx
  context : R.mlctx.vlctx = ambientDecls ++ parameterDecls
  prefixLength : ambientDecls.length = depth
  cached : List.Forall₂
    checkInductiveTypes.loopType.CachedParameterDecl
    stats.params.toList.reverse parameterDecls
  suffixParams : List.Forall₂
    (TrExprS R.venv recLparams parameterDecls)
    stats.params.toList
    (checkInductiveTypes.loopType.cachedParamVars stats.params.size 0)
  sources : checkInductiveTypes.loopType.SourceTelescope
    R.venv recLparams parameterDecls

/-- The cached parameter suffix is well formed on its own, without the ambient
declarations above it in the recursor context. -/
theorem RecursorParameterContextSuffix.parameterWF
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : RecursorParameterContextSuffix R stats depth) :
    VLCtx.WF R.venv recLparams.length H.parameterDecls := by
  have dropPrefix : ∀ (added suffix : VLCtx),
      VLCtx.WF R.venv recLparams.length (added ++ suffix) →
        VLCtx.WF R.venv recLparams.length suffix := by
    intro added
    induction added with
    | nil => intro suffix Hwf; simpa using Hwf
    | cons decl tail ih =>
      intro suffix Hwf
      exact ih suffix Hwf.1
  have Hwf := R.mlctx_wf.tr.wf
  rw [H.context] at Hwf
  exact dropPrefix H.ambientDecls H.parameterDecls Hwf

theorem VEnv.IsDefEqCtx.instL
    (hls : ∀ level ∈ levels, level.WF U') :
    ∀ {base left right},
      VEnv.IsDefEqCtx env U base left right →
      VEnv.IsDefEqCtx env U'
        (base.map (VExpr.instL levels))
        (left.map (VExpr.instL levels))
        (right.map (VExpr.instL levels))
  | _, _, _, .zero => .zero
  | _, _, _, .succ hctx htype =>
    .succ (VEnv.IsDefEqCtx.instL hls hctx) (htype.instL hls)

/-- Universe instantiation of a header target: only the type is instantiated, the name
and arity are unchanged. -/
def _root_.Lean4Lean.VInductiveTypeSkeleton.instL
    (target : VInductiveTypeSkeleton) (levels : List VLevel) :
    VInductiveTypeSkeleton :=
  { target with type := target.type.instL levels }

def checkInductiveTypes.loopType.ScopedHeaderTelescope.mono
    {env env' : VEnv} (henv : env ≤ env')
    (H : checkInductiveTypes.loopType.ScopedHeaderTelescope
      env Us target scope current i nindices) :
    checkInductiveTypes.loopType.ScopedHeaderTelescope
      env' Us target scope current i nindices where
  params := H.params
  indices := H.indices
  parameterCount := H.parameterCount
  indexCount := H.indexCount
  scopeLength := H.scopeLength
  scopeCtx := H.scopeCtx
  scopeWF := H.scopeWF.mono henv
  currentType := H.currentType.mono henv
  exprType := H.exprType
  header := H.header.mono henv

/-- A scoped header telescope (in the checking context) instantiated by a well-formed
universe substitution. It moves constructor facts to the recursor's universe list when
large elimination prepends its fresh universe parameter. -/
noncomputable def
    checkInductiveTypes.loopType.ScopedHeaderTelescope.instL
    {Us' : List Name}
    (hlevels : ∀ level ∈ levels, level.WF Us'.length)
    (hlength : levels.length = Us.length)
    (H : checkInductiveTypes.loopType.ScopedHeaderTelescope
      env Us target scope current i nindices) :
    checkInductiveTypes.loopType.ScopedHeaderTelescope
      env Us'
      (target.instL levels) (scope.instL levels) (current.instL levels)
      i nindices where
  params := H.params.map (VExpr.instL levels)
  indices := H.indices.map (VExpr.instL levels)
  parameterCount := by simp [H.parameterCount]
  indexCount := by simp [H.indexCount]
  scopeLength := by
    have length_instL : ∀ scope : VLCtx,
        (scope.instL levels).length = scope.length := by
      intro scope
      induction scope with
      | nil => rfl
      | cons entry scope ih =>
        rcases entry with ⟨ofv, decl⟩
        simp [VLCtx.instL, ih]
    have hlength := length_instL scope
    exact hlength.trans H.scopeLength
  scopeCtx := by
    simpa [VLCtx.instL_toCtx, List.map_append, List.map_reverse,
      Function.comp_def] using
      congrArg (List.map (VExpr.instL levels)) H.scopeCtx
  scopeWF := by
    have hsource : VLCtx.WF env levels.length scope := by
      simpa [hlength] using H.scopeWF
    exact hsource.instL hlevels
  currentType := by
    have hsource : env.IsType levels.length scope.toCtx current := by
      simpa [hlength] using H.currentType
    simpa [VLCtx.instL_toCtx] using hsource.instL hlevels
  exprType := H.exprType.instL levels
  header := by
    have hsource : env.IsDefEq levels.length [] target.type
        (VExpr.wrapForalls (H.params ++ H.indices) current) H.exprType := by
      simpa [hlength] using H.header
    simpa [VInductiveTypeSkeleton.instL, List.map_append] using
      hsource.instL hlevels

/-- An installed constant whose instantiated type is the telescope's target, applied to
the bvar spine of the telescope's parameters, has the remaining type `current`. -/
theorem checkInductiveTypes.loopType.ScopedHeaderTelescope.canonicalApplication
    {ctorVal : VConstVal} {levels : List VLevel}
    (H : checkInductiveTypes.loopType.ScopedHeaderTelescope
      env Us target scope current i 0)
    (henv : env.WF)
    (hlookup : env.constants ctorVal.name = some ctorVal.toVConstant)
    (hlevels : ∀ level ∈ levels, level.WF Us.length)
    (hlength : levels.length = ctorVal.uvars)
    (htarget : ctorVal.type.instL levels = target.type) :
    env.HasType Us.length scope.toCtx
      (VExpr.mkApps (.const ctorVal.name levels)
        (bvarSpine H.params.length)) current := by
  have hindices : H.indices = [] :=
    List.eq_nil_of_length_eq_zero H.indexCount
  have hconst := VEnv.HasType.const (Γ := []) hlookup hlevels hlength
  have hhead : env.HasType Us.length []
      (.const ctorVal.name levels) target.type := by
    simpa [htarget] using hconst
  have htelescope : env.HasType Us.length []
      (.const ctorVal.name levels)
      (VExpr.wrapForalls H.params current) := by
    apply hhead.defeqU_r henv (by trivial)
    exact ⟨H.exprType, by simpa [hindices] using H.header⟩
  have happ := VEnv.HasType.mkApps_wrapForalls_bvarSpine
    henv.ordered htelescope
  simpa [hindices, H.scopeCtx, bvarSpine,
    VExpr.liftN] using happ

/-- Move the parameter suffix of the header phase to the recursor context. For small
elimination nothing changes; for large elimination the executable declarations and
free-variable names are unchanged and the abstract types are shifted by one universe
parameter. -/
def checkInductiveTypes.loopType.ParameterContextSuffix.toRecursorContext
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : checkInductiveTypes.loopType.ParameterContextSuffix Hc stats depth)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    let R := Hc.toAdmissibleRecursorContextWF Helim
    RecursorParameterContextSuffix R stats depth := by
  dsimp only
  cases elimLevel with
  | zero =>
    exact {
      ambientDecls := H.ambientDecls
      parameterDecls := H.parameterDecls
      context := H.context
      prefixLength := H.prefixLength
      cached := H.cached
      suffixParams := H.suffixParams
      sources := H.sources }
  | param fresh =>
    let shift := VLevel.prependShift c.lparams.length
    have hcached : List.Forall₂
        checkInductiveTypes.loopType.CachedParameterDecl
        stats.params.toList.reverse (H.parameterDecls.instL shift) := by
      have go : ∀ {params : List Expr} {entries : VLCtx},
          List.Forall₂ checkInductiveTypes.loopType.CachedParameterDecl
              params entries →
          List.Forall₂ checkInductiveTypes.loopType.CachedParameterDecl
              params (entries.instL shift) := by
        intro params entries Hcached
        induction Hcached with
        | nil => exact .nil
        | @cons param entry params entries hentry _ ih =>
          rcases hentry with ⟨fv, deps, type, rfl, rfl⟩
          exact .cons ⟨fv, deps, type.instL shift, rfl, by
            simp [VLocalDecl.instL]⟩ ih
      exact go H.cached
    have hnarrow : List.Forall₂
        (TrExprS Hc.venv (fresh :: c.lparams)
          (H.parameterDecls.instL shift))
        stats.params.toList
        (checkInductiveTypes.loopType.cachedParamVars stats.params.size 0) := by
      have go : ∀ {sources targets},
          List.Forall₂ (TrExprS Hc.venv c.lparams H.parameterDecls)
              sources targets →
          List.Forall₂ (TrExprS Hc.venv (fresh :: c.lparams)
              (H.parameterDecls.instL shift))
            sources (targets.map fun target => target.instL shift) := by
        intro sources targets Htranslated
        induction Htranslated with
        | nil => exact .nil
        | cons hsource _ ih =>
          exact .cons
            (by
              simpa [shift] using
                (hsource.prependLevelParam Hc.checking.tr.wf
                  ((checkInductiveTypes.loopType.FrontScopeEmbedding.ofParameterSuffix
                    Hc H).scopeWF Hc.checking.tr.wf) Helim))
            ih
      have hshifted := go H.suffixParams
      have htargets :
          (checkInductiveTypes.loopType.cachedParamVars
              stats.params.size 0).map (fun target => target.instL shift) =
            checkInductiveTypes.loopType.cachedParamVars
              stats.params.size 0 := by
        induction stats.params.size with
        | zero => rfl
        | succ n ih =>
          rw [checkInductiveTypes.loopType.cachedParamVars_succ,
            List.map_append, List.map_map]
          congr 1
          · rw [show
                (fun target : VExpr => target.instL shift) ∘
                    (fun target : VExpr => target.liftN 1 0) =
                  (fun target : VExpr =>
                    (target.instL shift).liftN 1 0) by
                funext target
                simp [Function.comp_apply]]
            simpa [List.map_map] using congrArg
              (List.map fun target : VExpr => target.liftN 1 0) ih
      rw [htargets] at hshifted
      exact hshifted
    exact {
      ambientDecls := H.ambientDecls.instL shift
      parameterDecls := H.parameterDecls.instL shift
      context := by
        have hcontext := congrArg (fun Δ : VLCtx => Δ.instL shift) H.context
        change (Hc.mlctx.prependLevelParam c.lparams.length).vlctx =
          H.ambientDecls.instL shift ++ H.parameterDecls.instL shift
        simpa only [TypeChecker.MLCtx.prependLevelParam_vlctx,
          shift, VLCtx.instL_eq_map, List.map_append] using hcontext
      prefixLength := by
        rw [VLCtx.instL_eq_map, List.length_map, H.prefixLength]
      cached := hcached
      suffixParams := hnarrow
      sources := H.sources.prependLevelParam Hc.checking.tr.wf
        ((checkInductiveTypes.loopType.FrontScopeEmbedding.ofParameterSuffix
          Hc H).scopeWF Hc.checking.tr.wf) Helim }
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- The constructor telescope target under the recursor's universe list (shifted by one
universe parameter for large elimination). -/
def recursorConstructorTelescopeTarget
    (ctorVal : VConstVal)
    (Helim : AddInductive.AdmissibleElimLevel lparams elimLevel) :
    VInductiveTypeSkeleton :=
  match elimLevel with
  | .zero => constructorTelescopeTarget ctorVal
  | .param _ => (constructorTelescopeTarget ctorVal).instL
      (VLevel.prependShift lparams.length)
  | .succ _ | .max _ _ | .imax _ _ | .mvar _ => False.elim Helim

def recursorDeclarationAbstractLevels
    (lparams : List Name)
    (Helim : AddInductive.AdmissibleElimLevel lparams elimLevel) :
    List VLevel :=
  match elimLevel with
  | .zero => VLevel.params lparams.length
  | .param _ => (VLevel.params lparams.length).map
      (VLevel.inst (VLevel.prependShift lparams.length))
  | .succ _ | .max _ _ | .imax _ _ | .mvar _ => False.elim Helim

theorem recursorDeclarationAbstractLevels_zero
    (ha : AddInductive.AdmissibleElimLevel Us elim) (heq : elim = .zero) :
    recursorDeclarationAbstractLevels Us ha = VLevel.params Us.length := by
  subst elim
  rfl

theorem recursorDeclarationAbstractLevels_param
    (ha : AddInductive.AdmissibleElimLevel Us elim) (heq : elim = .param fresh) :
    recursorDeclarationAbstractLevels Us ha = VLevel.prependShift Us.length := by
  subst elim
  simp only [recursorDeclarationAbstractLevels]
  exact VLevel.inst_map_id VLevel.prependShift_length

theorem checkInductiveTypes.loopInd.HeaderStatsWF.recursorLevelTranslation
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : checkInductiveTypes.loopInd.HeaderStatsWF
      Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hlparams : c.lparams.Nodup)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    stats.levels.mapM (VLevel.ofLevel
      (AddInductive.getRecLevelParams elimLevel c.lparams)) =
      some (recursorDeclarationAbstractLevels c.lparams Helim) := by
  cases elimLevel with
  | zero =>
    simpa [AddInductive.getRecLevelParams,
      recursorDeclarationAbstractLevels,
      List.map_param_idxOf_eq_params hlparams] using H.levelTranslation
  | param fresh =>
    have hshifted := VLevel.mapM_ofLevel_fresh_cons Helim H.levelTranslation
    simpa [AddInductive.getRecLevelParams,
      recursorDeclarationAbstractLevels,
      List.map_param_idxOf_eq_params hlparams] using hshifted
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- The universe list of a generated recursor translates to the identity instantiation of
the recursor's universe parameters. For large elimination this is the fresh elimination
universe followed by the shifted declaration universes. -/
theorem
    checkInductiveTypes.loopInd.HeaderStatsWF.recursorLevelsTranslation
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : checkInductiveTypes.loopInd.HeaderStatsWF
      Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hlparams : c.lparams.Nodup)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    (AddInductive.getRecLevels elimLevel stats.levels).mapM
      (VLevel.ofLevel
        (AddInductive.getRecLevelParams elimLevel c.lparams)) =
      some (VLevel.params
        (AddInductive.getRecLevelParams elimLevel c.lparams).length) := by
  cases elimLevel with
  | zero =>
    simpa [AddInductive.getRecLevels, AddInductive.getRecLevelParams,
      recursorDeclarationAbstractLevels, Level.isParam] using
      H.recursorLevelTranslation hlparams Helim
  | param fresh =>
    have htail := H.recursorLevelTranslation hlparams Helim
    have hhead : VLevel.ofLevel (fresh :: c.lparams) (.param fresh) =
        some (.param 0) := by
      simp [VLevel.ofLevel]
    simp [AddInductive.getRecLevelParams,
      recursorDeclarationAbstractLevels] at htail
    simp only [AddInductive.getRecLevels, Level.isParam,
      ↓reduceIte, List.mapM_cons]
    simp only [AddInductive.getRecLevelParams]
    rw [hhead, htail]
    simp [VLevel.params, VLevel.prependShift]
    rw [List.range_succ_eq_map]
    simp [Function.comp_def, VLevel.inst]
    intro a ha
    simp [ha]
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

theorem recursorDeclarationAbstractLevels_wf
    (Helim : AddInductive.AdmissibleElimLevel lparams elimLevel) :
    ∀ level ∈ recursorDeclarationAbstractLevels lparams Helim,
      level.WF (AddInductive.getRecLevelParams elimLevel lparams).length := by
  cases elimLevel with
  | zero =>
    simpa [recursorDeclarationAbstractLevels,
      AddInductive.getRecLevelParams] using VLevel.params_wf
  | param fresh =>
    let shift := VLevel.prependShift lparams.length
    have hshift : ∀ level ∈ shift,
        level.WF (fresh :: lparams).length := by
      simpa [shift] using VLevel.prependShift_wf (n := lparams.length)
    intro level hlevel
    rw [recursorDeclarationAbstractLevels, List.mem_map] at hlevel
    rcases hlevel with ⟨sourceLevel, hsourceLevel, rfl⟩
    exact VLevel.WF.inst hshift
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

theorem recursorDeclarationAbstractLevels_length
    (Helim : AddInductive.AdmissibleElimLevel lparams elimLevel) :
    (recursorDeclarationAbstractLevels lparams Helim).length =
      lparams.length := by
  cases elimLevel with
  | zero => simp [recursorDeclarationAbstractLevels, VLevel.params]
  | param fresh =>
    simp [recursorDeclarationAbstractLevels, VLevel.params]
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- A large elimination universe is a fresh parameter: it translates to the first
abstract parameter, and the abstract source universes do not mention it. -/
theorem recursorDeclarationAbstractLevels_freeTarget
    (Helim : AddInductive.AdmissibleElimLevel lparams elimLevel) (hne : elimLevel ≠ .zero)
    (htarget : VLevel.ofLevel (AddInductive.getRecLevelParams elimLevel lparams) elimLevel =
      some target) :
    target = .param 0 ∧ ∀ l ∈ recursorDeclarationAbstractLevels lparams Helim,
      ∀ (ls : List VLevel) (u : VLevel), l.inst (ls.set 0 u) = l.inst ls := by
  cases elimLevel with
  | zero => exact absurd rfl hne
  | param fresh =>
    refine ⟨?_, ?_⟩
    · simp [AddInductive.getRecLevelParams, VLevel.ofLevel] at htarget
      exact htarget.symm
    · intro l hl ls u
      simp only [recursorDeclarationAbstractLevels, List.mem_map, VLevel.params,
        List.mem_range] at hl
      obtain ⟨_, ⟨i, _, rfl⟩, rfl⟩ := hl
      rename_i hi
      simp only [VLevel.prependShift, VLevel.inst, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some,
        List.getElem?_set]
      simp
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

theorem VConstVal.type_instL_recursorDeclarationAbstractLevels
    (Hwf : ctorVal.toVConstant.WF env)
    (huvars : ctorVal.uvars = lparams.length)
    (Helim : AddInductive.AdmissibleElimLevel lparams elimLevel) :
    ctorVal.type.instL (recursorDeclarationAbstractLevels lparams Helim) =
      (recursorConstructorTelescopeTarget ctorVal Helim).type := by
  have hlevelWF : ctorVal.type.LevelWF ctorVal.uvars := by
    exact (Classical.choose_spec Hwf).levelWF (by trivial) |>.1
  cases elimLevel with
  | zero =>
    simpa [recursorDeclarationAbstractLevels,
      recursorConstructorTelescopeTarget, constructorTelescopeTarget,
      huvars] using hlevelWF.instL_id
  | param fresh =>
    let shift := VLevel.prependShift lparams.length
    have hid : ctorVal.type.instL (VLevel.params lparams.length) =
        ctorVal.type := by simpa [← huvars] using hlevelWF.instL_id
    rw [recursorDeclarationAbstractLevels,
      recursorConstructorTelescopeTarget, ← VExpr.instL_instL, hid]
    rfl
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- Move one checked constructor tail to the parameter scope and universe list in which
the recursor construction starts. -/
theorem CheckedConstructorTailAt.toRecursorContext
    {c : AddInductive.Context} {Hc : ContextWF c}
    {sourceEnv : VEnv} {decl : VInductDecl}
    {target : VInductiveType} {source : Constructor}
    (Hmaterialized :
      checkInductiveTypes.loopInd.HeaderStatsWF
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    {classes : List Bool}
    (H : CheckedConstructorTailAt sourceEnv c.lparams
      Hmaterialized.parameterScope stats decl target source classes)
    (henv : sourceEnv ≤ Hc.venv)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    let R := Hc.toAdmissibleRecursorContextWF Helim
    let Hsuffix := Hmaterialized.parameterSuffix.toRecursorContext Helim
    ∃ ctorVal tail tailTarget,
      ctorVal ∈ target.ctors ∧
      ctorVal.name = source.name ∧
      ctorVal.uvars = c.lparams.length ∧
      ParameterPrefix stats 0 source.type tail ∧
      TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        Hsuffix.parameterDecls tail tailTarget ∧
      R.venv.IsType
        (AddInductive.getRecLevelParams elimLevel c.lparams).length
        Hsuffix.parameterDecls.toCtx tailTarget ∧
      Nonempty
        (checkInductiveTypes.loopType.ScopedHeaderTelescope
          R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
          (recursorConstructorTelescopeTarget ctorVal Helim)
          Hsuffix.parameterDecls tailTarget stats.params.size 0) := by
  rcases H with
    ⟨ctorVal, tail, tailTarget, sourceDomains, hmem, Hraw, Hprefix,
      Hcomparisons, Htranslated, Htail, Hsynthesis⟩
  rcases Hsynthesis with ⟨Hsynthesis⟩
  dsimp only
  cases elimLevel with
  | zero =>
    refine ⟨ctorVal, tail, tailTarget, hmem, Hraw.name, Hraw.uvars,
      Hprefix, ?_, ?_, ?_⟩
    · change TrExprS Hc.venv c.lparams Hmaterialized.parameterScope
        tail tailTarget
      exact Htranslated.mono henv
    · change Hc.venv.IsType c.lparams.length
        Hmaterialized.parameterScope.toCtx tailTarget
      simpa [Hmaterialized.uvars] using Htail.isType.mono henv
    · refine ⟨?_⟩
      change checkInductiveTypes.loopType.ScopedHeaderTelescope
        Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
        Hmaterialized.parameterScope tailTarget stats.params.size 0
      exact Hsynthesis.mono henv
  | param fresh =>
    let shift := VLevel.prependShift c.lparams.length
    have hshift : ∀ level ∈ shift,
        level.WF (fresh :: c.lparams).length := by
      simpa [shift] using VLevel.prependShift_wf (n := c.lparams.length)
    have hshiftLength : shift.length = c.lparams.length := by
      simp [shift, VLevel.prependShift]
    have hscopeWF : Hmaterialized.parameterScope.WF
        Hc.venv c.lparams.length :=
      (checkInductiveTypes.loopType.FrontScopeEmbedding.ofParameterSuffix
        Hc Hmaterialized.parameterSuffix).scopeWF Hc.checking.tr.wf
    refine ⟨ctorVal, tail, tailTarget.instL shift, hmem, Hraw.name,
      Hraw.uvars, Hprefix, ?_, ?_, ?_⟩
    · change TrExprS Hc.venv (fresh :: c.lparams)
        (Hmaterialized.parameterScope.instL shift) tail
        (tailTarget.instL shift)
      simpa [shift] using (Htranslated.mono henv).prependLevelParam
        Hc.checking.tr.wf hscopeWF Helim
    · have htype := (Htail.isType.mono henv).instL hshift
      change Hc.venv.IsType (fresh :: c.lparams).length
        (Hmaterialized.parameterScope.instL shift).toCtx
        (tailTarget.instL shift)
      simpa [VLCtx.instL_toCtx, shift, Hmaterialized.uvars] using htype
    · refine ⟨?_⟩
      change checkInductiveTypes.loopType.ScopedHeaderTelescope
        Hc.venv (fresh :: c.lparams)
        ((constructorTelescopeTarget ctorVal).instL shift)
        (Hmaterialized.parameterScope.instL shift)
        (tailTarget.instL shift) stats.params.size 0
      simpa [shift] using
        (Hsynthesis.mono henv).instL hshift hshiftLength
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

theorem RecursorParameterContextSuffix.noIndConsts
    (H : RecursorParameterContextSuffix R stats depth)
    (names : List Name) :
    checkPositivityStep.VLCtx.NoIndConsts names H.parameterDecls := by
  have go : ∀ {params : List Expr} {entries : VLCtx},
      List.Forall₂ checkInductiveTypes.loopType.CachedParameterDecl
          params entries →
      checkPositivityStep.VLCtx.NoIndConsts names entries := by
    intro params entries hcached
    induction hcached with
    | nil =>
      intro v mapped type hfind
      simp [VLCtx.find?] at hfind
    | @cons param entry params entries hentry _ ih =>
      rcases hentry with ⟨fv, deps, type, rfl, rfl⟩
      exact checkPositivityStep.VLCtx.NoIndConsts.cons ih rfl
  intro v mapped type hfind
  exact go H.cached hfind

/-- The parameter suffix embeds, as a front scope, into the full recursor context. -/
def RecursorParameterContextSuffix.parameterEmbedding
    {c : AddInductive.Context}
    {R : RecursorContextWF c recLparams}
    (H : RecursorParameterContextSuffix R stats depth) :
    checkInductiveTypes.loopType.FrontScopeEmbedding
      R.venv recLparams H.parameterDecls R.mlctx.vlctx := by
  have hambient : H.ambientDecls.NoBV := by
    apply VLCtx.NoBV.leftOfAppend H.ambientDecls H.parameterDecls
    rw [← H.context]
    exact R.mlctx.noBV
  let W := VLCtx.FVLift.to_append H.parameterDecls hambient
  refine {
    expanded := R.mlctx.vlctx
    shift := .skipN .refl H.ambientDecls.toCtx.length
    lift := ?_
    frontSourceDomains := []
    frontExpandedDomains := []
    front := ?_
    context := .refl R.checking.tr.wf R.mlctx_wf.tr.wf
    upset := ?_
    noBV := ?_
    noIndConsts := H.noIndConsts
    sourceTelescope := H.sources
    wf := ?_ }
  · rw [H.context]
    exact W.toFVLift'
  · exact .zero (by
      rw [H.context]
      exact W.toFVLift')
  · have hwf : VLCtx.WF R.venv recLparams.length
        (H.ambientDecls ++ H.parameterDecls) := by
      rw [← H.context]
      exact R.mlctx_wf.tr.wf
    simpa [H.context] using
      (IsFVarUpSet.suffixFVars H.parameterDecls H.ambientDecls hwf)
  · have hfull : (H.ambientDecls ++ H.parameterDecls).NoBV := by
      rw [← H.context]
      exact R.mlctx.noBV
    change H.parameterDecls.bvars = 0
    change (H.ambientDecls ++ H.parameterDecls).bvars = 0 at hfull
    rw [VLCtx.bvars_append] at hfull
    omega
  · have hwf : VLCtx.WF R.venv recLparams.length
        (H.ambientDecls ++ H.parameterDecls) := by
      rw [← H.context]
      exact R.mlctx_wf.tr.wf
    exact hwf.append_right

/-- A local added by the recursor construction extends only the ambient prefix. The
cached parameter suffix and its translations are unchanged. -/
def RecursorParameterContextSuffix.withAmbient
    {c : AddInductive.Context}
    {R : RecursorContextWF c recLparams}
    (H : RecursorParameterContextSuffix R stats depth)
    (htr : TrExprS R.venv recLparams R.mlctx.vlctx ty ty')
    (hty : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx ty') :
    let R' := @RecursorContextWF.withLocalDecl c recLparams ty ty' name bi
      R htr hty
    RecursorParameterContextSuffix R' stats (depth + 1) := by
  dsimp only
  let entry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty')
  exact {
    ambientDecls := entry :: H.ambientDecls
    parameterDecls := H.parameterDecls
    context := by
      change entry :: R.mlctx.vlctx =
        (entry :: H.ambientDecls) ++ H.parameterDecls
      simpa only [List.cons_append] using congrArg (entry :: ·) H.context
    prefixLength := by simp [H.prefixLength]
    cached := H.cached
    suffixParams := H.suffixParams
    sources := H.sources }

/-- Variant of `RecursorParameterContextSuffix.withAmbient` for a binder opened in both contexts. -/
def RecursorParameterContextSuffix.withAmbientChecked
    {c : AddInductive.Context}
    {R : RecursorContextWF c recLparams}
    (H : RecursorParameterContextSuffix R stats depth)
    (htr : TrExprS R.venv recLparams R.mlctx.vlctx ty ty')
    (hty : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS R.venv recLparams R.chk.vlctx ty ty₀)
    (hty₀ : R.venv.IsType recLparams.length R.chk.vlctx.toCtx ty₀) :
    let R' := @RecursorContextWF.withCheckedLocalDecl c recLparams ty ty' ty₀ name bi
      R htr hty htr₀ hty₀
    RecursorParameterContextSuffix R' stats (depth + 1) := by
  dsimp only
  let entry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty')
  exact {
    ambientDecls := entry :: H.ambientDecls
    parameterDecls := H.parameterDecls
    context := by
      change entry :: R.mlctx.vlctx =
        (entry :: H.ambientDecls) ++ H.parameterDecls
      simpa only [List.cons_append] using congrArg (entry :: ·) H.context
    prefixLength := by simp [H.prefixLength]
    cached := H.cached
    suffixParams := H.suffixParams
    sources := H.sources }

theorem RecursorParameterContextSuffix.parameterDecls_length
    (H : RecursorParameterContextSuffix R stats depth) :
    H.parameterDecls.length = stats.params.size := by
  have hlength := List.Forall₂.length_eq H.cached
  simpa using hlength.symm

theorem RecursorParameterContextSuffix.depth_le
    (H : RecursorParameterContextSuffix R stats depth) :
    depth ≤ R.mlctx.length := by
  rw [← TypeChecker.MLCtx.vlctx_length]
  rw [H.context, List.length_append, H.prefixLength]
  omega

/-- Dropping the ambient prefix of the recursor context leaves exactly the cached
parameter suffix. -/
theorem RecursorParameterContextSuffix.dropAmbient_vlctx
    (H : RecursorParameterContextSuffix R stats depth) :
    (R.mlctx.dropN depth H.depth_le).vlctx = H.parameterDecls := by
  have hdecomp := TypeChecker.MLCtx.vlctx_eq_take_append_dropN
    R.mlctx depth H.depth_le
  have htake : R.mlctx.vlctx.take depth = H.ambientDecls := by
    have := congrArg (List.take depth) H.context
    simpa [H.prefixLength] using this
  exact List.append_cancel_left <| calc
    H.ambientDecls ++ (R.mlctx.dropN depth H.depth_le).vlctx =
        R.mlctx.vlctx := by rw [← htake, ← hdecomp]
    _ = H.ambientDecls ++ H.parameterDecls := H.context

theorem RecursorParameterContextSuffix.parameterAt
    (H : RecursorParameterContextSuffix R stats depth)
    (hi : i < stats.params.size)
    (hj : stats.params.size - 1 - i < H.parameterDecls.length) :
    checkInductiveTypes.loopType.CachedParameterDecl stats.params[i]
      H.parameterDecls[stats.params.size - 1 - i] := by
  let j := stats.params.size - 1 - i
  have hj' : j < stats.params.size := by
    dsimp [j]
    omega
  have hleft : j < stats.params.toList.reverse.length := by
    simpa using hj'
  have hright : j < H.parameterDecls.length := hj
  have hcached := List.forall₂_getElem
    H.cached j hleft hright
  simp only [List.getElem_reverse, Array.getElem_toList] at hcached
  change checkInductiveTypes.loopType.CachedParameterDecl
    stats.params[stats.params.size - 1 - j] H.parameterDecls[j] at hcached
  dsimp [j] at hcached ⊢
  have hindex : stats.params.size - 1 -
      (stats.params.size - 1 - i) = i := by omega
  have helem :
      stats.params[stats.params.size - 1 -
        (stats.params.size - 1 - i)] = stats.params[i] :=
    getElem_congr rfl hindex (by omega)
  rw [← helem]
  exact hcached

theorem RecursorParameterContextSuffix.splitAt
    (H : RecursorParameterContextSuffix R stats depth)
    (hi : i < stats.params.size) :
    ∃ newer entry older,
      H.parameterDecls = newer ++ entry :: older ∧
      newer.length = stats.params.size - 1 - i ∧
      checkInductiveTypes.loopType.CachedParameterDecl stats.params[i]
        entry := by
  let j := stats.params.size - 1 - i
  have hj : j < H.parameterDecls.length := by
    rw [H.parameterDecls_length]
    dsimp [j]
    omega
  refine ⟨H.parameterDecls.take j, H.parameterDecls[j],
    H.parameterDecls.drop (j + 1), ?_, ?_, ?_⟩
  · calc
      H.parameterDecls =
          H.parameterDecls.take j ++ H.parameterDecls.drop j :=
        (List.take_append_drop j H.parameterDecls).symm
      _ = H.parameterDecls.take j ++
          H.parameterDecls[j] :: H.parameterDecls.drop (j + 1) := by
        rw [List.drop_eq_getElem_cons hj]
  · simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj), j]
  · exact H.parameterAt hi hj

theorem RecursorParameterContextSuffix.fvLiftAt
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : RecursorParameterContextSuffix R stats depth)
    (hi : i < stats.params.size) :
    ∃ added newer older fv deps paramType,
      H.parameterDecls =
        newer ++ (some (fv, deps), .vlam paramType) :: older ∧
      newer.length = stats.params.size - 1 - i ∧
      added = H.ambientDecls ++ newer ∧
      R.mlctx.vlctx =
        added ++ (some (fv, deps), .vlam paramType) :: older ∧
      stats.params[i] = .fvar fv ∧
      VLCtx.FVLift ((some (fv, deps), .vlam paramType) :: older)
        R.mlctx.vlctx 0 (VLCtx.toCtx added).length 0 := by
  rcases H.splitAt hi with
    ⟨newer, entry, older, hdecls, hnewer, hcached⟩
  rcases hcached with ⟨fv, deps, paramType, hparam, rfl⟩
  let added := H.ambientDecls ++ newer
  have hcontext : R.mlctx.vlctx =
      added ++ (some (fv, deps), .vlam paramType) :: older := by
    rw [H.context, hdecls]
    simp only [added, List.append_assoc]
  have hfullNoBV :
      (added ++ (some (fv, deps), .vlam paramType) :: older).NoBV := by
    rw [← hcontext]
    exact R.mlctx.noBV
  have hadded : added.NoBV :=
    VLCtx.NoBV.leftOfAppend added
      ((some (fv, deps), .vlam paramType) :: older) hfullNoBV
  have hlift := VLCtx.FVLift.to_append
    ((some (fv, deps), .vlam paramType) :: older) hadded
  rw [← hcontext] at hlift
  exact ⟨added, newer, older, fv, deps, paramType, hdecls, hnewer,
    rfl, hcontext, hparam, hlift⟩

/-- The position of cached parameter `i` in the recursor context, used when the header
steps are run again for a later family. -/
structure RecursorReusedParameterScope
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (Hsuffix : RecursorParameterContextSuffix R stats depth)
    (i : Nat) (e : Expr) : Type where
  added : VLCtx
  newer : VLCtx
  older : VLCtx
  fv : FVarId
  deps : List FVarId
  paramType : VExpr
  parameterDecls : Hsuffix.parameterDecls =
    newer ++ (some (fv, deps), .vlam paramType) :: older
  newerLength : newer.length = stats.params.size - 1 - i
  addedEq : added = Hsuffix.ambientDecls ++ newer
  context : R.mlctx.vlctx =
    added ++ (some (fv, deps), .vlam paramType) :: older
  parameter : stats.params[i]! = .fvar fv
  lift : VLCtx.FVLift ((some (fv, deps), .vlam paramType) :: older)
    R.mlctx.vlctx 0 (VLCtx.toCtx added).length 0
  fvars : FVarsIn (· ∈ older.fvars) e

theorem RecursorReusedParameterScope.olderLength
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : RecursorParameterContextSuffix R stats depth} {e : Expr}
    (H : RecursorReusedParameterScope Hsuffix i e)
    (hi : i < stats.params.size) : H.older.length = i := by
  have htotal := Hsuffix.parameterDecls_length
  have hparts := congrArg List.length H.parameterDecls
  simp only [List.length_append, List.length_cons] at hparts
  rw [htotal, H.newerLength] at hparts
  omega

theorem RecursorParameterContextSuffix.mlctx_length
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : RecursorParameterContextSuffix R stats depth) :
    R.mlctx.length = depth + stats.params.size := by
  rw [← TypeChecker.MLCtx.vlctx_length, H.context, List.length_append,
    H.prefixLength, H.parameterDecls_length]

/-- The first `k` parameters are the bottom of the recursor context. -/
theorem RecursorParameterContextSuffix.bottom
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : RecursorParameterContextSuffix R stats depth) (k : Nat)
    (hk : k ≤ stats.params.size) :
    (R.mlctx.dropN (depth + (stats.params.size - k))
        (by rw [H.mlctx_length]; omega)).vlctx =
      H.parameterDecls.drop (stats.params.size - k) ∧
    paramCheckFVars stats k =
      (R.mlctx.dropN (depth + (stats.params.size - k))
        (by rw [H.mlctx_length]; omega)).fvarList := by
  have hvl : (R.mlctx.dropN (depth + (stats.params.size - k))
      (by rw [H.mlctx_length]; omega)).vlctx =
      H.parameterDecls.drop (stats.params.size - k) := by
    rw [R.onlyLams.vlctx_dropN, H.context, List.drop_append, H.prefixLength]
    rw [List.drop_eq_nil_of_le (by rw [H.prefixLength]; omega)]
    simp
  refine ⟨hvl, ?_⟩
  rw [TypeChecker.MLCtx.fvarList_eq, hvl]
  have hdrop : List.Forall₂ checkInductiveTypes.loopType.CachedParameterDecl
      (stats.params.toList.reverse.drop (stats.params.size - k))
      (H.parameterDecls.drop (stats.params.size - k)) :=
    checkInductiveTypes.loopType.CachedParameterDecl.forall₂_drop _ H.cached
  rw [checkInductiveTypes.loopType.CachedParameterDecl.forall₂_fvars hdrop,
    ← List.map_reverse]
  unfold paramCheckFVars
  congr 1
  rw [List.drop_reverse]
  simp only [List.reverse_reverse]
  congr 1
  simp
  omega

theorem RecursorParameterContextSuffix.headerFVars
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : RecursorParameterContextSuffix R stats depth) :
    paramCheckFVars stats stats.params.size =
      (R.mlctx.dropN depth H.depth_le).fvarList := by
  have h := (H.bottom stats.params.size (Nat.le_refl _)).2
  simp only [Nat.sub_self, Nat.add_zero] at h
  exact h

/-- The checker context of a recursor index telescope: the parameters. -/
def RecursorParameterContextSuffix.headerCheck
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : RecursorParameterContextSuffix R stats depth) :
    RecursorContextWF (headerCheckContext c stats) recLparams :=
  R.paramCheck stats stats.params.size depth H.depth_le H.headerFVars

theorem RecursorParameterContextSuffix.headerCheck_chk_vlctx
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : RecursorParameterContextSuffix R stats depth) :
    H.headerCheck.chk.vlctx = H.parameterDecls := H.dropAmbient_vlctx

/-- The same suffix over the header checker context. -/
def RecursorParameterContextSuffix.toHeaderCheck
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : RecursorParameterContextSuffix R stats depth) :
    RecursorParameterContextSuffix H.headerCheck stats depth := { H with }

theorem RecursorParameterContextSuffix.headerCheck_paramAligned
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : RecursorParameterContextSuffix R stats depth) :
    VLCtx.IsDefEq R.venv recLparams.length H.parameterDecls
      H.headerCheck.chk.vlctx := by
  rw [H.headerCheck_chk_vlctx]
  exact .refl R.checking.tr.wf H.parameterWF

theorem RecursorReusedParameterScope.olderDrop
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : RecursorParameterContextSuffix R stats depth} {e : Expr}
    (H : RecursorReusedParameterScope Hsuffix i e) (hi : i < stats.params.size) :
    Hsuffix.parameterDecls.drop (stats.params.size - i) = H.older ∧
    Hsuffix.parameterDecls.drop (stats.params.size - (i + 1)) =
      (some (H.fv, H.deps), .vlam H.paramType) :: H.older := by
  rw [H.parameterDecls]
  have hn := H.newerLength
  constructor
  · rw [show stats.params.size - i = H.newer.length + 1 by omega, List.drop_append]
    simp
  · rw [show stats.params.size - (i + 1) = H.newer.length by omega, List.drop_append]
    simp

theorem RecursorReusedParameterScope.parameterDefEq
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    {params : List VExpr}
    (H : RecursorReusedParameterScope Hsuffix i e)
    (hi : i < stats.params.size)
    (hparams : params.length = stats.params.size)
    (hctx : VEnv.IsDefEqCtx R.venv recLparams.length []
      params.reverse Hsuffix.parameterDecls.toCtx) :
    ∃ u, R.venv.IsDefEq recLparams.length H.older.toCtx
      (params[i]'(hparams.symm ▸ hi)) H.paramType (.sort u) := by
  have hcachedLength :=
    checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
      Hsuffix.cached
  have hdeclLength := Hsuffix.parameterDecls_length
  have hnewerLe :=
    checkInductiveTypes.loopType.VLCtx.toCtx_length_le H.newer
  have holderLe :=
    checkInductiveTypes.loopType.VLCtx.toCtx_length_le H.older
  have hctxParts := congrArg List.length <|
    congrArg VLCtx.toCtx H.parameterDecls
  simp only [VLCtx.toCtx_append, VLCtx.toCtx, List.length_append,
    List.length_cons] at hctxParts
  have hlistParts := congrArg List.length H.parameterDecls
  simp only [List.length_append, List.length_cons] at hlistParts
  have hnewerCtx : H.newer.toCtx.length = H.newer.length := by omega
  let j := H.newer.toCtx.length
  have hj : j < params.reverse.length := by
    simp only [List.length_reverse, j, hnewerCtx, hparams,
      H.newerLength]
    omega
  have hscopeCtx : Hsuffix.parameterDecls.toCtx =
      H.newer.toCtx ++ H.paramType :: H.older.toCtx := by
    rw [H.parameterDecls]
    simp [VLCtx.toCtx]
  have hctx' : VEnv.IsDefEqCtx R.venv recLparams.length []
      params.reverse (H.newer.toCtx ++ H.paramType :: H.older.toCtx) := by
    rw [← hscopeCtx]
    exact hctx
  have hentry := VEnv.IsDefEqCtx.getElemRight
    R.checking.tr.wf.ordered hctx' hj
  have hjEq : j = stats.params.size - 1 - i := by
    change H.newer.toCtx.length = stats.params.size - 1 - i
    rw [hnewerCtx]
    exact H.newerLength
  have hsourceIndex : params.length - 1 - j = i := by
    rw [hparams, hjEq]
    omega
  have hsourceIndex' :
      params.length - 1 - H.newer.toCtx.length = i := by
    simpa [j] using hsourceIndex
  rcases hentry with ⟨u, hentry⟩
  simp [j] at hentry
  exact ⟨u, by
    simpa only [List.getElem_reverse, hsourceIndex'] using hentry⟩

theorem RecursorReusedParameterScope.parameterPrefixDefEq
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    {params : List VExpr}
    (H : RecursorReusedParameterScope Hsuffix i e)
    (hi : i < stats.params.size)
    (hparams : params.length = stats.params.size)
    (hctx : VEnv.IsDefEqCtx R.venv recLparams.length []
      params.reverse Hsuffix.parameterDecls.toCtx) :
    VEnv.IsDefEqCtx R.venv recLparams.length []
      (params.take i).reverse H.older.toCtx := by
  have hcachedLength :=
    checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
      Hsuffix.cached
  have hdeclLength := Hsuffix.parameterDecls_length
  have hnewerLe :=
    checkInductiveTypes.loopType.VLCtx.toCtx_length_le H.newer
  have holderLe :=
    checkInductiveTypes.loopType.VLCtx.toCtx_length_le H.older
  have hctxParts := congrArg List.length <|
    congrArg VLCtx.toCtx H.parameterDecls
  simp only [VLCtx.toCtx_append, VLCtx.toCtx, List.length_append,
    List.length_cons] at hctxParts
  have hlistParts := congrArg List.length H.parameterDecls
  simp only [List.length_append, List.length_cons] at hlistParts
  have hnewerCtx : H.newer.toCtx.length = H.newer.length := by omega
  have hscopeCtx : Hsuffix.parameterDecls.toCtx =
      H.newer.toCtx ++ H.paramType :: H.older.toCtx := by
    rw [H.parameterDecls]
    simp [VLCtx.toCtx]
  have hctx' : VEnv.IsDefEqCtx R.venv recLparams.length []
      params.reverse (H.newer.toCtx ++ H.paramType :: H.older.toCtx) := by
    rw [← hscopeCtx]
    exact hctx
  let j := H.newer.toCtx.length
  have hjEq : j = stats.params.size - 1 - i := by
    change H.newer.toCtx.length = stats.params.size - 1 - i
    rw [hnewerCtx]
    exact H.newerLength
  have htake : params.length - (j + 1) = i := by
    rw [hparams, hjEq]
    omega
  have htake' : params.length - (H.newer.toCtx.length + 1) = i := by
    simpa [j] using htake
  have hdrop := VEnv.IsDefEqCtx.dropHeads hctx' (j + 1)
  simp [j] at hdrop
  simpa [List.drop_reverse, htake'] using hdrop

theorem RecursorReusedParameterScope.ownParameterDefEq
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    {params ownParams : List VExpr}
    (H : RecursorReusedParameterScope Hsuffix i e)
    (hi : i < stats.params.size)
    (hparamsLength : params.length = stats.params.size)
    (hctx : VEnv.IsDefEqCtx R.venv recLparams.length []
      params.reverse Hsuffix.parameterDecls.toCtx)
    (hown : VEnv.IsDefEqCtx R.venv recLparams.length []
      params.reverse ownParams.reverse) :
    ∃ u, R.venv.IsDefEq recLparams.length H.older.toCtx
      (ownParams[i]'(by
        have hlen : params.length = ownParams.length := by
          simpa using hown.length_eq
        omega)) H.paramType (.sort u) := by
  have hiparams : i < params.length := by omega
  have hlen : params.length = ownParams.length := by
    simpa using hown.length_eq
  have hrev : params.length - 1 - i < params.reverse.length := by
    simp
    omega
  have hentry := VEnv.IsDefEqCtx.getElem hown hrev
  have htake :
      params.length - (params.length - (1 + i) + 1) = i := by omega
  have hindex :
      params.length - (1 + (params.length - (1 + i))) = i := by omega
  have hcommonOwn : ∃ u, R.venv.IsDefEq recLparams.length
      (params.take i).reverse params[i]
      (ownParams[i]'(hlen ▸ hiparams)) (.sort u) := by
    simpa [List.getElem_reverse, List.drop_reverse, hlen.symm,
      Nat.sub_sub, htake, hindex] using hentry
  rcases hcommonOwn with ⟨u, hcommonOwn⟩
  have hprefix := H.parameterPrefixDefEq hi hparamsLength hctx
  have hcommonOwn' := hcommonOwn.defeqDFC
    R.checking.tr.wf.ordered hprefix
  rcases H.parameterDefEq hi hparamsLength hctx with
    ⟨cachedLevel, hcommonCached⟩
  have holderWF :=
    (H.lift.wf R.checking.tr.wf R.mlctx_wf.tr.wf).1
  exact ⟨cachedLevel, hcommonOwn'.symm.trans_r R.checking.tr.wf
    holderWF.toCtx hcommonCached⟩

theorem RecursorReusedParameterScope.older_eq_nil
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    {Hsuffix : RecursorParameterContextSuffix R stats depth} {e : Expr}
    (H : RecursorReusedParameterScope Hsuffix 0 e)
    (hi : 0 < stats.params.size) : H.older = [] :=
  List.eq_nil_of_length_eq_zero (H.olderLength hi)

theorem RecursorReusedParameterScope.scope
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : RecursorParameterContextSuffix R stats depth} {e : Expr}
    (H : RecursorReusedParameterScope Hsuffix i e)
    (hdone : i + 1 = stats.params.size) :
    (some (H.fv, H.deps), .vlam H.paramType) :: H.older =
      Hsuffix.parameterDecls := by
  have hnewerLength : H.newer.length = 0 := by
    rw [H.newerLength]
    omega
  have hnewer : H.newer = [] :=
    List.eq_nil_of_length_eq_zero hnewerLength
  rw [H.parameterDecls, hnewer]
  simp

noncomputable def RecursorReusedParameterScope.ofNoFVars
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    (hi : i < stats.params.size)
    (hfvars : FVarsIn (fun _ => False) e) :
    RecursorReusedParameterScope Hsuffix i e :=
  Classical.choice <| by
    rcases Hsuffix.fvLiftAt hi with
      ⟨added, newer, older, fv, deps, paramType, hdecls, hnewer,
        hadd, hcontext, hparam, hlift⟩
    exact ⟨{
      added := added
      newer := newer
      older := older
      fv := fv
      deps := deps
      paramType := paramType
      parameterDecls := hdecls
      newerLength := hnewer
      addedEq := hadd
      context := hcontext
      parameter := by
        simpa [Array.getElem!_eq_getD, hi] using hparam
      lift := hlift
      fvars := hfvars.mono fun _ h => False.elim h }⟩

theorem RecursorReusedParameterScope.openedFVars
    (H : RecursorReusedParameterScope Hsuffix i body) :
    FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      (body.instantiate1' (.fvar H.fv)) := by
  apply (H.fvars.mono fun fv hfv => by
    rw [VLCtx.fvars_cons_some]
    exact List.mem_cons_of_mem H.fv hfv).instantiate1
  simp only [FVarsIn]
  rw [VLCtx.fvars_cons_some]
  exact List.mem_cons_self

theorem RecursorReusedParameterScope.openedUpSet
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    (H : RecursorReusedParameterScope Hsuffix i body) :
    IsFVarUpSet
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      R.mlctx.vlctx := by
  rw [H.context]
  exact IsFVarUpSet.suffixFVars
    ((some (H.fv, H.deps), .vlam H.paramType) :: H.older)
    H.added (by simpa [H.context] using R.mlctx_wf.tr.wf)

theorem RecursorReusedParameterScope.unannotatedFVars
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    (H : RecursorReusedParameterScope Hsuffix i body)
    (hbelow : FVarsBelow R.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) normalized) :
    FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      normalized := by
  have hopened : FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      (body.instantiate1 stats.params[i]!) := by
    rw [Expr.instantiate1_eq, H.parameter]
    exact H.openedFVars
  exact hbelow _ H.openedUpSet hopened

theorem RecursorReusedParameterScope.olderLift
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    (H : RecursorReusedParameterScope Hsuffix i body) :
    VLCtx.FVLift H.older R.mlctx.vlctx 0
      (VLCtx.toCtx H.added).length.succ 0 := by
  let current : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (H.fv, H.deps), .vlam H.paramType)
  have hcontext : R.mlctx.vlctx =
      (H.added ++ [current]) ++ H.older := by
    simpa only [current, List.append_assoc, List.singleton_append]
      using H.context
  have hfullNoBV : ((H.added ++ [current]) ++ H.older).NoBV := by
    rw [← hcontext]
    exact R.mlctx.noBV
  have hprefixNoBV : (H.added ++ [current]).NoBV :=
    VLCtx.NoBV.leftOfAppend (H.added ++ [current]) H.older hfullNoBV
  have hlift := VLCtx.FVLift.to_append H.older hprefixNoBV
  rw [← hcontext] at hlift
  simpa [current, VLCtx.toCtx] using hlift

/-- The executable type of the cached parameter and its translation under the recursor's
universe list, read from the recursor context. -/
theorem RecursorReusedParameterScope.typing
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    (H : RecursorReusedParameterScope Hsuffix i body) :
    ∃ paramTy paramTy' param',
      (AddInductive.getType stats.params[i]! c).WF
        (fun ty => ty = paramTy) ∧
      TrExprS R.venv recLparams R.mlctx.vlctx paramTy paramTy' ∧
      paramTy' = H.paramType.lift.liftN
        (VLCtx.toCtx H.added).length 0 ∧
      TrExprS R.venv recLparams R.mlctx.vlctx
        stats.params[i]! param' ∧
      R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
        param' paramTy' := by
  have hhead : VLCtx.find?
      ((some (H.fv, H.deps), .vlam H.paramType) :: H.older)
      (.inr H.fv) = some (.bvar 0, H.paramType.lift) := by
    simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type]
  have hfull := H.lift.find? R.mlctx_wf.tr.wf.fvars_nodup hhead
  let param' := (VExpr.bvar 0).liftN (VLCtx.toCtx H.added).length 0
  let paramTy' := H.paramType.lift.liftN
    (VLCtx.toCtx H.added).length 0
  have hfind : R.mlctx.vlctx.find? (.inr H.fv) =
      some (param', paramTy') := by
    simpa [param', paramTy'] using hfull
  have hfv : H.fv ∈ R.mlctx.vlctx.fvars :=
    VLCtx.find?_eq_some.1 ⟨_, hfind⟩
  rcases (R.mlctx_wf.tr.find?_eq_some (fv := H.fv)).2 hfv with
    ⟨localDecl, hlocal⟩
  have hlocal' : c.lctx.find? H.fv = some localDecl := by
    rw [← R.lctx_eq]
    exact hlocal
  have hlist := hlocal
  rw [R.mlctx_wf.tr.1.find?_eq_find?_toList] at hlist
  have hid : H.fv = localDecl.fvarId := by
    simpa using List.find?_some hlist
  have hmem : localDecl ∈ R.mlctx.lctx.toList :=
    List.mem_of_find?_eq_some hlist
  rcases R.mlctx_wf.tr.find?_of_mem R.checking.tr.wf hmem with
    ⟨value', type', hfind', _hvalueBelow, _htypeBelow,
      _hvalue, htype⟩
  rw [← hid] at hfind'
  rw [hfind] at hfind'
  cases hfind'
  refine ⟨localDecl.type, paramTy', param', ?_, htype, rfl, ?_, ?_⟩
  · intro ty hrun
    rw [H.parameter] at hrun
    change Except.ok ((c.lctx.get! H.fv).type) = Except.ok ty at hrun
    simp [LocalContext.get!, hlocal'] at hrun
    exact hrun.symm
  · rw [H.parameter]
    exact .fvar hfind
  · exact R.mlctx_wf.tr.wf.find?_wf R.checking.tr.wf hfind

noncomputable def RecursorReusedParameterScope.next
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    (H : RecursorReusedParameterScope Hsuffix i body)
    (hi : i + 1 < stats.params.size)
    (hbelow : FVarsBelow R.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) normalized) :
    RecursorReusedParameterScope Hsuffix (i + 1) normalized :=
  Classical.choice <| by
    rcases Hsuffix.fvLiftAt hi with
      ⟨added, newer, older, fv, deps, paramType, hdecls, hnewer,
        hadd, hcontext, hparam, hlift⟩
    let currentEntry : Option (FVarId × List FVarId) × VLocalDecl :=
      (some (H.fv, H.deps), .vlam H.paramType)
    let nextEntry : Option (FVarId × List FVarId) × VLocalDecl :=
      (some (fv, deps), .vlam paramType)
    have hdecomp : H.newer ++ currentEntry :: H.older =
        (newer ++ [nextEntry]) ++ older := by
      calc
        H.newer ++ currentEntry :: H.older =
            Hsuffix.parameterDecls := H.parameterDecls.symm
        _ = newer ++ nextEntry :: older := hdecls
        _ = (newer ++ [nextEntry]) ++ older := by
          simp [List.append_assoc]
    have hprefixLength :
        H.newer.length = (newer ++ [nextEntry]).length := by
      simp only [List.length_append, List.length_singleton]
      rw [H.newerLength, hnewer]
      omega
    have htail : currentEntry :: H.older = older :=
      List.append_inj_right hdecomp hprefixLength
    have hnormalized := H.unannotatedFVars hbelow
    have hnextFVars : FVarsIn (· ∈ VLCtx.fvars older) normalized := by
      rw [← htail]
      exact hnormalized
    exact ⟨{
      added := added
      newer := newer
      older := older
      fv := fv
      deps := deps
      paramType := paramType
      parameterDecls := hdecls
      newerLength := hnewer
      addedEq := hadd
      context := hcontext
      parameter := by
        simpa [Array.getElem!_eq_getD, hi] using hparam
      lift := hlift
      fvars := hnextFVars }⟩

/-- The older part of the scope of parameter `i + 1` is the entry of parameter `i`
followed by the older part of the scope of parameter `i`. -/
theorem RecursorReusedParameterScope.nextOlder
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : RecursorParameterContextSuffix R stats depth}
    {e next : Expr}
    (H : RecursorReusedParameterScope Hsuffix i e)
    (Hnext : RecursorReusedParameterScope Hsuffix (i + 1) next)
    (hi : i + 1 < stats.params.size) :
    (some (H.fv, H.deps), .vlam H.paramType) :: H.older =
      Hnext.older := by
  let currentEntry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (H.fv, H.deps), .vlam H.paramType)
  let nextEntry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (Hnext.fv, Hnext.deps), .vlam Hnext.paramType)
  have hdecomp :
      H.newer ++ currentEntry :: H.older =
        (Hnext.newer ++ [nextEntry]) ++ Hnext.older := by
    calc
      H.newer ++ currentEntry :: H.older =
          Hsuffix.parameterDecls := H.parameterDecls.symm
      _ = Hnext.newer ++ nextEntry :: Hnext.older :=
        Hnext.parameterDecls
      _ = (Hnext.newer ++ [nextEntry]) ++ Hnext.older := by
        simp [List.append_assoc]
  have hprefixLength :
      H.newer.length = (Hnext.newer ++ [nextEntry]).length := by
    simp only [List.length_append, List.length_singleton]
    rw [H.newerLength, Hnext.newerLength]
    omega
  simpa only [currentEntry] using
    List.append_inj_right hdecomp hprefixLength

end VerifyInductive
end Lean4Lean
