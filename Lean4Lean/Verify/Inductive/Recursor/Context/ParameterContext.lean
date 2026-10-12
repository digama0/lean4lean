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
`ParameterContextSuffix.toRecursorContext` moves the header phase's cached-parameter suffix
(`Header/ParameterSuffix.lean`) to it; in the recursor frame that suffix records that the cached
parameters sit, unchanged, below the locals the recursor construction adds (motives, majors,
minors, induction hypotheses). -/

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
def ParameterContextSuffix.toRecursorContext
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : ParameterContextSuffix Hc.toSemantics stats depth)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    let R := Hc.toAdmissibleRecursorContextWF Helim
    ParameterContextSuffix R.toSemantics stats depth := by
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
                  ((H.parameterEmbedding).scopeWF Hc.checking.tr.wf) Helim))
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
        ((H.parameterEmbedding).scopeWF Hc.checking.tr.wf) Helim }
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
      (Hmaterialized.parameterSuffix.parameterEmbedding).scopeWF Hc.checking.tr.wf
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

end VerifyInductive
end Lean4Lean
