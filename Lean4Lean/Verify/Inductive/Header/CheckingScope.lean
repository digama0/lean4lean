import Lean4Lean.Verify.Inductive.Context
import Lean4Lean.Verify.LocalContext

/-!
# Scopes inside the executable local context

The header loops of `Lean4Lean/Inductive/Add.lean` keep indices of earlier families and the
cached common parameters in one local context. This file describes the abstract scopes that
the proof carves out of it without strengthening (section 5.1 of
the design notes): the abstract images of the parameter cache
(`cachedParamVars`, `ParameterCachePrefix`, `ParameterContextSuffix`), source telescopes of
all-lambda contexts (`SourceTelescope`), and dependency-closed sub-scopes of a larger
context (`FrontScopeEmbedding`, `ScopeEmbedding`), into which terms and types are moved by
weakening. The scope embeddings are reused by the constructor and recursor phases.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

namespace checkInductiveTypes.loopType

/-- Abstract images of the concrete parameter cache after `done` parameter
binders and `depth` subsequent index binders.  Its recursive presentation
matches the executable `Array.push` order exactly. -/
def cachedParamVars : Nat → Nat → List VExpr
  | 0, _ => []
  | done + 1, depth =>
    (cachedParamVars done depth).map (fun e => e.liftN 1 0) ++
      [.bvar depth]

@[simp] theorem cachedParamVars_zero : cachedParamVars 0 depth = [] := rfl

@[simp] theorem cachedParamVars_succ :
    cachedParamVars (done + 1) depth =
      (cachedParamVars done depth).map (fun e => e.liftN 1 0) ++
        [.bvar depth] := rfl

@[simp] theorem cachedParamVars_length :
    (cachedParamVars done depth).length = done := by
  induction done with
  | zero => rfl
  | succ done ih => simp [cachedParamVars_succ, ih]

theorem cachedParamVars_getElem? :
    (cachedParamVars done depth)[i]? =
      if i < done then some (.bvar (depth + (done - 1 - i))) else none := by
  induction done generalizing depth i with
  | zero => simp
  | succ done ih =>
    simp only [cachedParamVars_succ]
    by_cases hprior : i < done
    · rw [List.getElem?_append_left (by simp [hprior])]
      rw [List.getElem?_map, ih]
      simp only [hprior, if_true, Option.map_some]
      simp [VExpr.liftN]
      congr 2
      omega
    · by_cases hcurrent : i < done + 1
      · have hieq : i = done := by omega
        subst i
        simp
      · have hout : done + 1 ≤ i := by omega
        rw [List.getElem?_eq_none_iff.2 (by simp; omega)]
        simp [hcurrent]

@[simp] theorem cachedParamVars_depth_succ :
    cachedParamVars done (depth + 1) =
      (cachedParamVars done depth).map (fun e => e.liftN 1 0) := by
  induction done with
  | zero => rfl
  | succ done ih =>
    simp [cachedParamVars_succ, ih, List.map_map, VExpr.liftN,
      Function.comp_def]

theorem cachedParamVars_eq_paramVars (decl : VInductDecl) :
    cachedParamVars decl.nparams depth = decl.paramVars depth := by
  apply List.ext_getElem?
  intro i
  rw [cachedParamVars_getElem?]
  by_cases hi : i < decl.nparams
  · rw [VInductDecl.paramVars, List.getElem?_map]
    rw [List.getElem?_reverse (by simp [hi])]
    have hj : decl.nparams - 1 - i < decl.nparams := by omega
    simp [hi, hj]
  · rw [List.getElem?_eq_none_iff.2 (by
      simp [VInductDecl.paramVars]
      omega)]
    simp [hi]

theorem cachedParamVars_zero_eq_bvarSpine (n : Nat) :
    cachedParamVars n 0 = bvarSpine n := by
  unfold bvarSpine
  apply List.ext_getElem?
  intro i
  rw [cachedParamVars_getElem?]
  by_cases hi : i < n
  · rw [List.getElem?_map, List.getElem?_reverse (by simp [hi])]
    have hj : n - 1 - i < n := by omega
    simp [hi, hj]
  · rw [List.getElem?_eq_none_iff.2 (by simp; omega)]
    simp [hi]

/-- Source domains of a dependency-closed scope.
The context is newest first.  At each retained declaration, its source
Lean domain is translated in the already retained older tail. -/
inductive SourceTelescope (env : VEnv) (Us : List Name) :
    VLCtx → Type
  | nil : SourceTelescope env Us []
  | cons
      (tail : SourceTelescope env Us scope)
      (name : Name) (binderInfo : BinderInfo)
      (domain : Expr)
      (translation : TrExprS env Us scope domain target) :
      SourceTelescope env Us
        ((some (fv, deps), .vlam target) :: scope)

def SourceTelescope.mono {env env' : VEnv} (henv : env ≤ env') :
    SourceTelescope env Us scope → SourceTelescope env' Us scope
  | .nil => .nil
  | .cons tail name binderInfo domain translation =>
    .cons (tail.mono henv) name binderInfo domain
      (translation.mono henv)

/-- Prepend one fresh recursor universe parameter to a retained source
telescope without changing its concrete domains. -/
def SourceTelescope.prependLevelParam
    (H : SourceTelescope env Us scope)
    (henv : env.WF) (hscope : scope.WF env Us.length)
    (hfresh : fresh ∉ Us) :
    SourceTelescope env (fresh :: Us)
      (scope.instL (VLevel.prependShift Us.length)) :=
  match H with
  | .nil => .nil
  | .cons tail name binderInfo domain translation =>
    .cons (tail.prependLevelParam henv hscope.1 hfresh)
      name binderInfo domain
      (translation.prependLevelParam henv hscope.1 hfresh)

/-- Close a body through all retained source declarations. -/
def SourceTelescope.closeSource
    (H : SourceTelescope env Us scope) (body : Expr) : Expr :=
  match H with
  | .nil => body
  | .cons (fv := fv) tail name binderInfo domain _ =>
    tail.closeSource (.forallE name domain
      (body.abstractN [fv]) binderInfo)

/-- Retained source scopes consist of free-variable entries only. -/
theorem SourceTelescope.noBV (H : SourceTelescope env Us scope) : scope.bvars = 0 := by
  induction H with
  | nil => rfl
  | cons _ _ _ _ _ ih => simpa [VLCtx.bvars] using ih

@[simp] theorem SourceTelescope.closeSource_mono
    {env env' : VEnv} (henv : env ≤ env')
    (H : SourceTelescope env Us scope) (body : Expr) :
    (H.mono henv).closeSource body = H.closeSource body := by
  induction H generalizing body with
  | nil => rfl
  | cons tail name binderInfo domain translation ih =>
    exact ih _

@[simp] theorem SourceTelescope.closeSource_nil
    (body : Expr) :
    (SourceTelescope.nil : SourceTelescope env Us []).closeSource body =
      body := rfl

theorem _root_.Lean4Lean.VLCtx.WF.mono
    {env env' : VEnv} (henv : env ≤ env') :
    ∀ {scope : VLCtx}, VLCtx.WF env U scope → VLCtx.WF env' U scope
  | [], H => H
  | (ofv, decl) :: scope, ⟨Hscope, Hfresh, Hdecl⟩ => by
    refine ⟨VLCtx.WF.mono henv Hscope, Hfresh, ?_⟩
    cases decl with
    | vlam type => exact Hdecl.mono henv
    | vlet type value => exact Hdecl.mono henv

theorem _root_.Lean4Lean.VLCtx.WF.append_right {env : VEnv} {U : Nat} :
    ∀ {A B : VLCtx}, VLCtx.WF env U (A ++ B) → VLCtx.WF env U B
  | [], _, h => h
  | _ :: A, _, h => VLCtx.WF.append_right (A := A) h.1

/-- Recover the exact source telescope of an executable context containing
only lambda declarations.  Each `MLCtx` node already retains the strict
translation used to install its abstract domain. -/
def MLCtxOnlyLams.sources
    {m : TypeChecker.MLCtx} (H : MLCtxOnlyLams m)
    (Hwf : m.WF env Us) : SourceTelescope env Us m.vlctx :=
  match m with
  | .nil => .nil
  | .vlam _fv name type _type' bi _tail =>
    .cons (MLCtxOnlyLams.sources H.tail_vlam Hwf.1)
      name bi type Hwf.2.2.1
  | .vlet _fv _name _type _value _type' _value' _tail =>
    False.elim H.vlet_false

/-- Local invariant for the first header's common-parameter branch. -/
structure ParameterCachePrefix (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (stats : AddInductive.InductiveStats) (done depth : Nat) : Prop where
  params : List.Forall₂ (TrExprS env Us Δ) stats.params.toList
    (cachedParamVars done depth)
  paramFVars : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv

/-- A concrete cached parameter and the free-variable declaration that owns
it in the retained verifier context. -/
def CachedParameterDecl (param : Expr)
    (entry : Option (FVarId × List FVarId) × VLocalDecl) : Prop :=
  ∃ fv deps type,
    param = .fvar fv ∧ entry = (some (fv, deps), .vlam type)

theorem VLCtx.toCtx_length_le (scope : VLCtx) :
    (VLCtx.toCtx scope).length ≤ scope.length := by
  induction scope with
  | nil => exact Nat.le_refl 0
  | cons entry scope ih =>
    rcases entry with ⟨ofv, decl⟩
    cases decl <;> simp [VLCtx.toCtx] <;> omega

/-- Cached parameter declarations are all lambda declarations, so conversion
to the abstract typing context drops no entries. -/
theorem CachedParameterDecl.forall₂_toCtx_length
    (H : List.Forall₂ CachedParameterDecl params scope) :
    (VLCtx.toCtx scope).length = scope.length := by
  induction H with
  | nil => rfl
  | cons h _ ih =>
    rcases h with ⟨fv, deps, type, rfl, rfl⟩
    simp [VLCtx.toCtx, ih]

/-- Structural companion to `ParameterCachePrefix`.  Cached parameter local
declarations form an exact suffix of the retained context; every index added
after the parameter phase belongs to `ambientDecls`.  The reverse is
intentional:
the executable array stores parameters from oldest to newest, while local
declarations are pushed at the head.

This suffix decomposition is what lets later mutual headers discard ambient
indices and not-yet-used cached parameters and work in the scope of the
parameters they have already processed (`ReusedParameterScope`). -/
structure ParameterContextSuffix (Hc : ContextWF c)
    (stats : AddInductive.InductiveStats) (depth : Nat) : Type where
  ambientDecls : VLCtx
  parameterDecls : VLCtx
  context : Hc.mlctx.vlctx = ambientDecls ++ parameterDecls
  prefixLength : ambientDecls.length = depth
  cached : List.Forall₂ CachedParameterDecl
    stats.params.toList.reverse parameterDecls
  suffixParams : List.Forall₂
    (TrExprS Hc.venv c.lparams parameterDecls)
    stats.params.toList (cachedParamVars stats.params.size 0)
  sources : SourceTelescope Hc.venv c.lparams parameterDecls

/-- Reindex a parameter cache across statistics updates that leave the
cached parameter array unchanged. -/
theorem ParameterCachePrefix.reindex
    (H : ParameterCachePrefix env Us Δ stats done depth)
    (hparams : stats'.params = stats.params) :
    ParameterCachePrefix env Us Δ stats' done depth where
  params := by rw [hparams]; exact H.params
  paramFVars := by rw [hparams]; exact H.paramFVars

/-- Reindex the exact cached suffix across a statistics update that changes
only per-header output fields. -/
def ParameterContextSuffix.reindex
    (H : ParameterContextSuffix Hc stats depth)
    (hparams : stats'.params = stats.params) :
    ParameterContextSuffix Hc stats' depth where
  ambientDecls := H.ambientDecls
  parameterDecls := H.parameterDecls
  context := H.context
  prefixLength := H.prefixLength
  cached := by rw [hparams]; exact H.cached
  suffixParams := by rw [hparams]; exact H.suffixParams
  sources := H.sources

def _root_.Lean4Lean.checkPositivityStep.VLCtx.NoIndConsts
    (names : List Name) (Δ : VLCtx) : Prop :=
  ∀ {v mapped type}, Δ.find? v = some (mapped, type) →
    mapped.containsAnyConst names = false

theorem _root_.Lean4Lean.checkPositivityStep.VLCtx.NoIndConsts.cons
    {Δ : VLCtx} {names : List Name}
    {ofv : Option (FVarId × List FVarId)} {d : VLocalDecl}
    (H : checkPositivityStep.VLCtx.NoIndConsts names Δ)
    (hvalue : d.value.containsAnyConst names = false) :
    checkPositivityStep.VLCtx.NoIndConsts names ((ofv, d) :: Δ) := by
  intro v mapped type hfind
  simp only [VLCtx.find?] at hfind
  split at hfind
  · cases hfind
    exact hvalue
  · simp at hfind
    rcases hfind with ⟨old, _type, hfind, hmap, _⟩
    rw [← hmap]
    simpa only [VExpr.containsAnyConst_liftN] using H hfind

abbrev _root_.Lean4Lean.VLCtx.NoIndConsts :=
  checkPositivityStep.VLCtx.NoIndConsts

theorem _root_.Lean4Lean.VLCtx.NoIndConsts.cons
    {Δ : VLCtx} {names : List Name}
    {ofv : Option (FVarId × List FVarId)} {d : VLocalDecl}
    (H : VLCtx.NoIndConsts names Δ)
    (hvalue : d.value.containsAnyConst names = false) :
    VLCtx.NoIndConsts names ((ofv, d) :: Δ) :=
  checkPositivityStep.VLCtx.NoIndConsts.cons H hvalue

/-- Every local introduced by the inductive machinery denotes its own bound
variable.  Consequently restoring a dropped suffix of such locals cannot
introduce an inductive constant into context lookup results. -/
theorem MLCtxOnlyLams.noIndConsts_of_dropN
    (H : MLCtxOnlyLams m) (n : Nat) (hn : n ≤ m.length)
    (hdrop : VLCtx.NoIndConsts names (m.dropN n hn).vlctx) :
    VLCtx.NoIndConsts names m.vlctx := by
  induction n generalizing m with
  | zero =>
    intro v mapped type hfind
    exact hdrop hfind
  | succ n ih =>
    cases m with
    | nil => simp at hn
    | vlam fv name type type' bi tail =>
      have Htail := H.tail_vlam
      have htail : VLCtx.NoIndConsts names tail.vlctx := by
        apply ih Htail (Nat.le_of_succ_le_succ hn)
        intro v mapped type hfind
        exact hdrop hfind
      change checkPositivityStep.VLCtx.NoIndConsts names
        ((some (fv, type.fvarsList), .vlam type') :: tail.vlctx)
      exact checkPositivityStep.VLCtx.NoIndConsts.cons htail rfl
    | vlet fv name type value type' value' tail =>
      exact H.vlet_false.elim

/-- A lambda-only translated local context can return only bound variables
from lookup, independently of the constants appearing in binder types. -/
theorem MLCtxOnlyLams.noIndConsts
    (H : MLCtxOnlyLams m) : VLCtx.NoIndConsts names m.vlctx := by
  induction m with
  | nil =>
      intro v mapped type hfind
      simp [VLCtx.find?] at hfind
  | vlam fv name type type' bi tail ih =>
      exact VLCtx.NoIndConsts.cons (ih H.tail_vlam) rfl
  | vlet fv name type value type' value' tail ih =>
      exact H.vlet_false.elim

theorem ParameterContextSuffix.noIndConsts
    (H : ParameterContextSuffix Hc stats depth) (names : List Name) :
    checkPositivityStep.VLCtx.NoIndConsts names H.parameterDecls := by
  have go : ∀ {params : List Expr} {entries : VLCtx},
      List.Forall₂ CachedParameterDecl params entries →
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

/-- A semantic header scope embedded in the larger executable local context.
`expanded` is the literal weakening of the semantic scope; it is kept separate
from `runtime` because stripping type annotations can replace an installed binder
domain by a merely definitionally equal expression. -/
inductive FrontFVLift : List VExpr → List VExpr →
    VLCtx → VLCtx → Lift → Prop
  | zero (W : VLCtx.FVLift' scope expanded 0 shift 0) :
      FrontFVLift [] [] scope expanded shift
  | cons (fv deps indexType)
      (hdeps : deps ⊆ scope.fvars)
      (H : FrontFVLift sourceDomains expandedDomains
        scope expanded shift) :
      FrontFVLift (sourceDomains ++ [indexType])
        (expandedDomains ++ [indexType.lift' shift])
        ((some (fv, deps), .vlam indexType) :: scope)
        ((some (fv, deps), .vlam (indexType.lift' shift)) :: expanded)
        (shift.consN 1)

theorem FrontFVLift.expandedPrefix
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    (expanded.toCtx.take expandedDomains.length).reverse =
      expandedDomains := by
  induction H with
  | zero => rfl
  | cons fv deps indexType _ H ih =>
    simp [VLCtx.toCtx, ih, List.take_succ_cons, List.reverse_cons]

theorem FrontFVLift.length_eq
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    sourceDomains.length = expandedDomains.length := by
  induction H with
  | zero => rfl
  | cons _ _ _ _ _ ih => simpa using congrArg Nat.succ ih

theorem FrontFVLift.sourceBaseBVars
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    VLCtx.bvars (scope.drop sourceDomains.length) = VLCtx.bvars scope := by
  induction H with
  | zero => rfl
  | cons fv deps indexType hdeps H ih =>
    simpa [VLCtx.bvars] using ih

theorem FrontFVLift.expandedLengthLE
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    expandedDomains.length ≤ expanded.toCtx.length := by
  induction H with
  | zero => simp
  | cons _ _ _ _ _ ih => simpa [VLCtx.toCtx] using Nat.succ_le_succ ih

theorem FrontFVLift.sourceContext
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    VLCtx.toCtx scope =
      sourceDomains.reverse ++
        VLCtx.toCtx (scope.drop sourceDomains.length) := by
  induction H with
  | zero => simp
  | @cons sourceDomains expandedDomains scope expanded shift fv deps
      indexType _ H ih =>
    simpa [VLCtx.toCtx, List.reverse_append, List.append_assoc] using
      congrArg (indexType :: ·) ih

/-- The retained source front consists exactly of named lambda declarations.
This is the declaration-shape premise needed to turn those free variables
back into the anonymous binders of the canonical equation telescope. -/
theorem FrontFVLift.sourceDeclarations
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type))
      (VLCtx.fvars (scope.take sourceDomains.length))
      (scope.take sourceDomains.length) := by
  induction H with
  | zero => exact .nil
  | @cons sourceDomains expandedDomains scope expanded shift fv deps
      indexType hdeps H ih =>
    simp only [List.length_append, List.length_singleton, Nat.add_one,
      List.take_succ_cons, VLCtx.fvars_cons_some]
    exact List.Forall₂.cons (by exact ⟨deps, indexType, rfl⟩) ih

/-- `toCtx` sees every declaration in the retained source prefix because
`withIndex` adds lambdas only. -/
theorem FrontFVLift.sourceTakenContext
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    (VLCtx.toCtx (scope.take sourceDomains.length)).reverse =
      sourceDomains := by
  induction H with
  | zero => rfl
  | @cons sourceDomains expandedDomains scope expanded shift fv deps
      indexType hdeps H ih =>
    simp [List.take_succ_cons, VLCtx.toCtx, ih, List.reverse_cons]

/-- Taking a declaration prefix can only remove free-variable names. -/
theorem _root_.Lean4Lean.VLCtx.fvars_take_sublist
    (scope : VLCtx) (n : Nat) :
    (VLCtx.fvars (scope.take n)).Sublist scope.fvars := by
  induction n generalizing scope with
  | zero => simp
  | succ n ih =>
    cases scope with
    | nil => simp
    | cons entry scope =>
      rcases entry with ⟨ofv, decl⟩
      cases ofv with
      | none => simpa using ih scope
      | some fv =>
        change (fv.1 :: VLCtx.fvars (scope.take n)).Sublist
          (fv.1 :: VLCtx.fvars scope)
        exact List.cons_sublist_cons.mpr (ih scope)

/-- Recover the fixed free-variable weakening below a front accumulated by
`withIndex`.  Removing the leading source and expanded declarations exposes
the same base weakening from which the front was built. -/
theorem FrontFVLift.base
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift) :
    ∃ baseScope baseExpanded baseShift,
      scope.drop sourceDomains.length = baseScope ∧
      expanded.drop expandedDomains.length = baseExpanded ∧
      shift = baseShift.consN sourceDomains.length ∧
      VLCtx.FVLift' baseScope baseExpanded 0 baseShift 0 := by
  induction H with
  | zero W =>
    exact ⟨_, _, _, rfl, rfl, by simp, W⟩
  | @cons sourceDomains expandedDomains scope expanded shift fv deps
      indexType _ H ih =>
    rcases ih with
      ⟨baseScope, baseExpanded, baseShift, hsource, hexpanded,
        hshift, Hbase⟩
    refine ⟨baseScope, baseExpanded, baseShift, ?_, ?_, ?_, Hbase⟩
    · simpa using hsource
    · simpa using hexpanded
    · rw [hshift]
      simp [Lift.consN]

theorem _root_.Lean4Lean.VLCtx.IsDefEq.drop
    (H : VLCtx.IsDefEq env U left right) (n : Nat) :
    VLCtx.IsDefEq env U (left.drop n) (right.drop n) := by
  induction n generalizing left right with
  | zero => exact H
  | succ n ih =>
    cases H with
    | nil => exact .nil
    | cons H _ _ => exact ih H

theorem Lift.closeReopen_cons (shift : Lift) (n : Nat) :
    Lift.comp (Lift.comp (Lift.skipN .refl n) shift) (.skip .refl) =
      Lift.comp (Lift.skipN .refl (n + 1)) (.cons shift) := by
  induction shift generalizing n with
  | refl => simp
  | skip shift ih => simp
  | cons shift ih =>
    cases n with
    | zero => rfl
    | succ n => simp

theorem VExpr.liftN_lift'_liftN_one (body : VExpr)
    (shift : Lift) (n : Nat) :
    ((body.liftN n 0).lift' shift).liftN 1 0 =
      (body.liftN (n + 1) 0).lift' shift.cons := by
  simp only [← VExpr.lift'_consN_skipN, Lift.consN, Lift.skipN,
    ← VExpr.lift'_comp]
  rw [Lift.closeReopen_cons]
  rw [show n + 1 = Nat.succ n by omega]
  rfl

/-- Closing the leading declarations represented by a front-preserving
free-variable lift and then reopening them in the ambient context commutes
strictly with weakening. -/
theorem FrontFVLift.closeReopen
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift)
    (body : VExpr) :
    ((VExpr.wrapForalls sourceDomains body).liftN
        sourceDomains.length 0).lift' shift =
      (VExpr.wrapForalls expandedDomains (body.lift' shift)).liftN
        expandedDomains.length 0 := by
  induction H generalizing body with
  | zero => simp [VExpr.wrapForalls]
  | @cons sourceDomains expandedDomains scope expanded shift fv deps
      indexType _ H ih =>
    have h := congrArg (fun result => result.liftN 1 0)
      (ih (.forallE indexType body))
    simpa [VExpr.wrapForalls_append, VExpr.wrapForalls, VExpr.liftN,
      VExpr.liftN_liftN, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc, VExpr.liftN_lift'_liftN_one] using h

/-- Closing the retained front turns the full front-preserving shift into
the base shift below that front.  This is the non-reopened naturality law
needed when inverse weakening returns the executable's motive to its
parameter scope. -/
theorem FrontFVLift.closeAtBase
    (H : FrontFVLift sourceDomains expandedDomains scope expanded shift)
    (baseShift : Lift)
    (hshift : shift = baseShift.consN sourceDomains.length)
    (body : VExpr) :
    (VExpr.wrapForalls sourceDomains body).lift' baseShift =
      VExpr.wrapForalls expandedDomains (body.lift' shift) := by
  induction H generalizing body baseShift with
  | zero =>
    simpa [VExpr.wrapForalls] using (congrArg (body.lift' ·) hshift).symm
  | @cons sourceDomains expandedDomains scope expanded shift fv deps
      indexType hdeps H ih =>
    have hprevious : shift = baseShift.consN sourceDomains.length := by
      simpa [Lift.consN] using hshift
    have h := ih baseShift hprevious (.forallE indexType body)
    simpa [VExpr.wrapForalls_append, VExpr.wrapForalls,
      VExpr.lift', Lift.consN] using h

structure FrontScopeEmbedding (env : VEnv) (Us : List Name)
    (scope runtime : VLCtx) : Type where
  expanded : VLCtx
  shift : Lift
  lift : VLCtx.FVLift' scope expanded 0 shift 0
  frontSourceDomains : List VExpr
  frontExpandedDomains : List VExpr
  front : FrontFVLift frontSourceDomains frontExpandedDomains
    scope expanded shift
  context : VLCtx.IsDefEq env Us.length expanded runtime
  upset : IsFVarUpSet (· ∈ scope.fvars) runtime
  noBV : scope.NoBV
  noIndConsts : ∀ names,
    checkPositivityStep.VLCtx.NoIndConsts names scope
  sourceTelescope : SourceTelescope env Us scope
  /-- The semantic scope is well formed in its own right; it is not derived
  from the executable context, since that would be context strengthening. -/
  wf : scope.WF env Us.length

def FrontScopeEmbedding.mono {env env' : VEnv} (henv : env ≤ env')
    (H : FrontScopeEmbedding env Us scope runtime) :
    FrontScopeEmbedding env' Us scope runtime where
  expanded := H.expanded
  shift := H.shift
  lift := H.lift
  frontSourceDomains := H.frontSourceDomains
  frontExpandedDomains := H.frontExpandedDomains
  front := H.front
  context := H.context.mono henv
  upset := H.upset
  noBV := H.noBV
  noIndConsts := H.noIndConsts
  sourceTelescope := H.sourceTelescope.mono henv
  wf := H.wf.mono henv

/-- Retarget only the executable context of a scope embedding along an exact
context equality.  The semantic front is copied field-by-field so its data
projections remain definitionally unchanged, rather than being hidden below
a dependent cast. -/
def FrontScopeEmbedding.retargetRuntime
    (H : FrontScopeEmbedding env Us scope runtime)
    (h : runtime = runtime') :
    FrontScopeEmbedding env Us scope runtime' where
  expanded := H.expanded
  shift := H.shift
  lift := H.lift
  frontSourceDomains := H.frontSourceDomains
  frontExpandedDomains := H.frontExpandedDomains
  front := H.front
  context := by cases h; exact H.context
  upset := by cases h; exact H.upset
  noBV := H.noBV
  noIndConsts := H.noIndConsts
  sourceTelescope := H.sourceTelescope
  wf := H.wf

theorem FrontScopeEmbedding.scopeWF
    (H : FrontScopeEmbedding env Us scope runtime)
    (_henv : env.WF) :
    scope.WF env Us.length :=
  H.wf

theorem FrontScopeEmbedding.transportType
    (H : FrontScopeEmbedding env Us scope runtime)
    (henv : env.WF)
    (htr : TrExprS env Us scope e narrow')
    (htype : env.IsType Us.length scope.toCtx narrow') :
    ∃ runtime', TrExprS env Us runtime e runtime' ∧
      env.IsType Us.length runtime.toCtx runtime' := by
  have hweak : TrExprS env Us H.expanded e (narrow'.lift' H.shift) := by
    simpa using htr.weakFV' henv.ordered H.lift H.context.wf
  have hweakType : env.IsType Us.length H.expanded.toCtx
      (narrow'.lift' H.shift) :=
    htype.weak' henv.ordered H.lift.toCtx
  rcases hweak.defeqDFC henv H.context with ⟨runtime', hruntime⟩
  have heq := hweak.uniq henv H.context hruntime
  have hweakTypeRuntime := hweakType.defeqDFC henv.ordered
    H.context.defeqCtx
  have heqRuntime := heq.defeqDFC henv.ordered H.context.defeqCtx
  exact ⟨runtime', hruntime,
    hweakTypeRuntime.defeqU_l henv
      (H.context.symm henv.ordered).wf.toCtx heqRuntime⟩

/-- Weaken a term together with its independently translated type from the
semantic parameter scope into the executable runtime context. -/
theorem FrontScopeEmbedding.transportTypedTerm
    (H : FrontScopeEmbedding env Us scope runtime)
    (henv : env.WF)
    (hterm : TrExprS env Us scope term termTarget)
    (htype : TrExprS env Us scope type typeTarget)
    (htyping : env.HasType Us.length scope.toCtx termTarget typeTarget)
    (htypeType : env.IsType Us.length scope.toCtx typeTarget) :
    ∃ termRuntime typeRuntime,
      TrExprS env Us runtime term termRuntime ∧
      TrExprS env Us runtime type typeRuntime ∧
      env.HasType Us.length runtime.toCtx termRuntime typeRuntime ∧
      env.IsType Us.length runtime.toCtx typeRuntime := by
  rcases H.transportType henv htype htypeType with
    ⟨typeRuntime, htypeRuntime, htypeRuntimeType⟩
  have htermWeak : TrExprS env Us H.expanded term
      (termTarget.lift' H.shift) := by
    simpa using hterm.weakFV' henv.ordered H.lift H.context.wf
  have htypeWeak : TrExprS env Us H.expanded type
      (typeTarget.lift' H.shift) := by
    simpa using htype.weakFV' henv.ordered H.lift H.context.wf
  rcases htermWeak.defeqDFC henv H.context with
    ⟨termRuntime, htermRuntime⟩
  have htermEq := htermWeak.uniq henv H.context htermRuntime
  have htypeEq := htypeWeak.uniq henv H.context htypeRuntime
  have htermEqRuntime :=
    htermEq.defeqDFC henv.ordered H.context.defeqCtx
  have htypeEqRuntime :=
    htypeEq.defeqDFC henv.ordered H.context.defeqCtx
  have htypingWeak := htyping.weak' henv.ordered H.lift.toCtx
  have htypingRuntime := htypingWeak.defeqDFC henv.ordered
    H.context.defeqCtx
  have htypingTerm := htypingRuntime.defeqU_l henv
    (H.context.symm henv.ordered).wf.toCtx htermEqRuntime
  have htypingBoth := htypingTerm.defeqU_r henv
    (H.context.symm henv.ordered).wf.toCtx htypeEqRuntime
  exact ⟨termRuntime, typeRuntime, htermRuntime, htypeRuntime,
    htypingBoth, htypeRuntimeType⟩

def FrontScopeEmbedding.withIndex
    (H : FrontScopeEmbedding env Us scope runtime)
    (hnewRuntime : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam runtimeType) :: runtime))
    (hdeps : deps ⊆ scope.fvars)
    (sourceName : Name) (sourceBinderInfo : BinderInfo)
    (sourceDomain : Expr)
    (hsourceDomain : TrExprS env Us scope sourceDomain indexType)
    (hdomain : env.IsDefEq Us.length H.expanded.toCtx
      (indexType.lift' H.shift) runtimeType (.sort u))
    (htype : env.IsType Us.length scope.toCtx indexType) :
    FrontScopeEmbedding env Us
      ((some (fv, deps), .vlam indexType) :: scope)
      ((some (fv, deps), .vlam runtimeType) :: runtime) where
  expanded :=
    (some (fv, deps), .vlam (indexType.lift' H.shift)) :: H.expanded
  shift := H.shift.consN 1
  lift := H.lift.cons_fvar (fv, deps) (.vlam indexType) hdeps
  frontSourceDomains := H.frontSourceDomains ++ [indexType]
  frontExpandedDomains :=
    H.frontExpandedDomains ++ [indexType.lift' H.shift]
  front := H.front.cons fv deps indexType hdeps
  context := .cons H.context (by
    have hfresh := hnewRuntime.2.1
    simpa [H.context.fvars] using hfresh) (.vlam hdomain)
  upset := by
    have hfresh := hnewRuntime.2.1
    refine ⟨?_, ?_⟩
    · apply (IsFVarUpSet.congr hnewRuntime.1.fvwf ?_).2 H.upset
      intro fv' hmem
      simp only [VLCtx.fvars_cons_some, List.mem_cons]
      constructor
      · intro h
        rcases h with rfl | h
        · exact False.elim (hfresh _ _ rfl |>.1 hmem)
        · exact h
      · exact Or.inr
    · intro _ dep hdep
      exact List.mem_cons_of_mem _ (hdeps hdep)
  noBV := by
    change scope.bvars = 0
    exact H.noBV
  noIndConsts := fun names =>
    checkPositivityStep.VLCtx.NoIndConsts.cons
      (H.noIndConsts names) rfl
  sourceTelescope := .cons H.sourceTelescope sourceName sourceBinderInfo sourceDomain
    hsourceDomain
  wf := by
    refine ⟨H.wf, ?_, htype⟩
    rintro _ _ ⟨⟩
    refine ⟨fun hmem => ?_, hdeps⟩
    have hsub : scope.fvars ⊆ runtime.fvars := by
      rw [← H.context.fvars]
      exact H.lift.fvars_sublist.subset
    exact (hnewRuntime.2.1 _ _ rfl).1 (hsub hmem)

/-- A dependency-closed semantic subcontext of an executable all-lambda
context.  Unlike `FrontScopeEmbedding`, this deliberately has no contiguous
`front`: callers may retain one named local, skip the next, and retain a
later one.  That is the shape of the recursor context, where indices and
majors are interleaved with the motives selected by the generated telescope.
-/
structure ScopeEmbedding (env : VEnv) (Us : List Name)
    (scope runtime : VLCtx) : Type where
  expanded : VLCtx
  shift : Lift
  lift : VLCtx.FVLift' scope expanded 0 shift 0
  context : VLCtx.IsDefEq env Us.length expanded runtime
  upset : IsFVarUpSet (· ∈ scope.fvars) runtime
  noBV : scope.NoBV
  declarations : List.Forall₂
    (fun fv entry => ∃ deps type,
      entry = (some (fv, deps), .vlam type))
    scope.fvars scope
  sourceTelescope : SourceTelescope env Us scope
  wf : scope.WF env Us.length

def ScopeEmbedding.mono {env env' : VEnv} (henv : env ≤ env')
    (H : ScopeEmbedding env Us scope runtime) :
    ScopeEmbedding env' Us scope runtime where
  expanded := H.expanded
  shift := H.shift
  lift := H.lift
  context := H.context.mono henv
  upset := H.upset
  noBV := H.noBV
  declarations := H.declarations
  sourceTelescope := H.sourceTelescope.mono henv
  wf := H.wf.mono henv

theorem ScopeEmbedding.scopeWF
    (H : ScopeEmbedding env Us scope runtime)
    (_henv : env.WF) : scope.WF env Us.length :=
  H.wf

theorem ScopeEmbedding.fvars_length
    (H : ScopeEmbedding env Us scope runtime) :
    scope.fvars.length = scope.length :=
  List.Forall₂.length_eq H.declarations

theorem VLCtx.fvars_length_of_noBV {scope : VLCtx} (H : scope.NoBV) :
    scope.fvars.length = scope.length := by
  induction scope with
  | nil => rfl
  | cons entry scope ih =>
    rcases entry with ⟨ofv, decl⟩
    cases ofv with
    | none =>
      change VLCtx.bvars scope + 1 = 0 at H
      omega
    | some fv =>
      change VLCtx.bvars scope = 0 at H
      simp [ih H]

theorem ScopeEmbedding.toCtx_length
    (H : ScopeEmbedding env Us scope runtime) :
    scope.toCtx.length = scope.length :=
  VLCtx.toCtx_length_of_forall₂_vlam H.declarations

def ScopeEmbedding.nil : ScopeEmbedding env Us [] [] where
  expanded := []
  shift := .refl
  lift := .refl
  context := .nil
  upset := trivial
  noBV := rfl
  declarations := .nil
  sourceTelescope := .nil
  wf := trivial

/-- A translated local context is dependency-closed for `P` whenever every
selected concrete declaration records only dependencies satisfying `P`. -/
theorem TrLCtx'.isFVarUpSet
    (H : TrLCtx' env Us declarations runtime)
    (hdeps : ∀ declaration ∈ declarations,
      P declaration.fvarId → ∀ fv ∈ declaration.deps, P fv) :
    IsFVarUpSet P runtime := by
  induction H with
  | nil => trivial
  | @cons declarations runtime declaration target Htail Hdecl ih =>
    refine ⟨ih (by
      intro other hother
      exact hdeps other (by simp [hother])), ?_⟩
    intro hselected fv hfv
    exact hdeps declaration (by simp) hselected fv hfv

theorem ScopeEmbedding.fullTargetEq
    (H : ScopeEmbedding env Us scope runtime)
    (henv : env.WF)
    (hnarrow : TrExprS env Us scope e narrow')
    (hfull : TrExpr env Us runtime e full') :
    env.IsDefEqU Us.length runtime.toCtx
      (narrow'.lift' H.shift) full' := by
  rcases hfull with ⟨source', hsource, hsourceEq⟩
  have hweak : TrExprS env Us H.expanded e
      (narrow'.lift' H.shift) := by
    simpa using hnarrow.weakFV' henv.ordered H.lift H.context.wf
  have hsourceEq' := hweak.uniq henv H.context hsource
  exact (hsourceEq'.defeqDFC henv.ordered H.context.defeqCtx).trans
    henv (H.context.symm henv.ordered).wf.toCtx hsourceEq

/-- Retain one newly introduced named lambda.  Its semantic domain is
obtained by inverse weakening; the executable domain need only be
definitionally equal after weakening back into the expanded context. -/
def ScopeEmbedding.withIndex
    (H : ScopeEmbedding env Us scope runtime)
    (hnewRuntime : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam runtimeType) :: runtime))
    (hdeps : deps ⊆ scope.fvars)
    (sourceName : Name) (sourceBinderInfo : BinderInfo)
    (sourceType : Expr)
    (hsource : TrExprS env Us scope sourceType indexType)
    (hdomain : env.IsDefEq Us.length H.expanded.toCtx
      (indexType.lift' H.shift) runtimeType (.sort u))
    (htype : env.IsType Us.length scope.toCtx indexType) :
    ScopeEmbedding env Us
      ((some (fv, deps), .vlam indexType) :: scope)
      ((some (fv, deps), .vlam runtimeType) :: runtime) where
  expanded :=
    (some (fv, deps), .vlam (indexType.lift' H.shift)) :: H.expanded
  shift := H.shift.consN 1
  lift := H.lift.cons_fvar (fv, deps) (.vlam indexType) hdeps
  context := .cons H.context (by
    have hfresh := hnewRuntime.2.1
    simpa [H.context.fvars] using hfresh) (.vlam hdomain)
  upset := by
    have hfresh := hnewRuntime.2.1
    refine ⟨?_, ?_⟩
    · apply (IsFVarUpSet.congr hnewRuntime.1.fvwf ?_).2 H.upset
      intro fv' hmem
      simp only [VLCtx.fvars_cons_some, List.mem_cons]
      constructor
      · intro h
        rcases h with rfl | h
        · exact False.elim (hfresh _ _ rfl |>.1 hmem)
        · exact h
      · exact Or.inr
    · intro _ dep hdep
      exact List.mem_cons_of_mem _ (hdeps hdep)
  noBV := H.noBV
  declarations := .cons ⟨deps, indexType, rfl⟩ H.declarations
  sourceTelescope := .cons H.sourceTelescope sourceName sourceBinderInfo sourceType hsource
  wf := by
    refine ⟨H.wf, ?_, htype⟩
    rintro _ _ ⟨⟩
    refine ⟨fun hmem => ?_, hdeps⟩
    have hsub : scope.fvars ⊆ runtime.fvars := by
      rw [← H.context.fvars]
      exact H.lift.fvars_sublist.subset
    exact (hnewRuntime.2.1 _ _ rfl).1 (hsub hmem)

/-- Skip one newly introduced named lambda while preserving a previously
selected, possibly non-contiguous semantic scope. -/
def ScopeEmbedding.skipIndex
    (H : ScopeEmbedding env Us scope runtime)
    (henv : env.WF)
    (hnewRuntime : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam runtimeType) :: runtime))
    (hskip : fv ∉ scope.fvars) :
    ScopeEmbedding env Us scope
      ((some (fv, deps), .vlam runtimeType) :: runtime) where
  expanded := (some (fv, deps), .vlam runtimeType) :: H.expanded
  shift := H.shift.skipN 1
  lift := H.lift.skip_fvar (fv, deps) (.vlam runtimeType)
  context := by
    have Htype : env.IsType Us.length H.expanded.toCtx runtimeType :=
      hnewRuntime.2.2.defeqDFC henv.ordered
        (H.context.defeqCtx.symm henv.ordered)
    rcases Htype with ⟨level, Htype⟩
    exact .cons H.context (by
      have hfresh := hnewRuntime.2.1
      simpa [H.context.fvars] using hfresh)
      (VLocalDecl.IsDefEq.refl henv H.context.wf.toCtx
        ⟨level, Htype⟩)
  upset := by
    refine ⟨H.upset, ?_⟩
    intro hmem
    exact False.elim (hskip hmem)
  noBV := H.noBV
  declarations := H.declarations
  sourceTelescope := H.sourceTelescope
  wf := H.wf

def fvarSelectionLift (fvars : List FVarId) (P : FVarId → Prop)
    [DecidablePred P] : Lift :=
  match fvars with
  | [] => .refl
  | fv :: fvars =>
    if P fv then .cons (fvarSelectionLift fvars P)
    else .skip (fvarSelectionLift fvars P)

theorem MLCtxOnlyLams.scopedFVarsSourceOracle
    {c : TypeChecker.MLCtx} {env : VEnv} {Us : List Name}
    (H : MLCtxOnlyLams c)
    (henv : env.WF)
    (Hwf : c.WF env Us)
    (P : FVarId → Prop) [DecidablePred P]
    (hup : IsFVarUpSet P c.vlctx)
    (Good : VLCtx → Prop) (hgood : Good [])
    {Lsel : List FVarId}
    (hL : c.vlctx.fvars.filter P <:+ Lsel)
    {Lctx : LocalContext}
    (hsubL : ∀ fv d, c.lctx.find? fv = some d → Lctx.find? fv = some d)
    (oracle : ∀ (tailScope : VLCtx) (fv : FVarId) (type : Expr),
      Good tailScope → (fv :: tailScope.fvars) <:+ Lsel →
      (∃ idx name bi kind,
        Lctx.find? fv = some (.cdecl idx fv name type bi kind)) →
      FVarsIn (· ∈ tailScope.fvars) type → Closed type →
      ∃ t, TrExprS env Us tailScope type t ∧
        env.IsType Us.length tailScope.toCtx t ∧
        Good ((some (fv, type.fvarsList), .vlam t) :: tailScope)) :
    ∃ scope,
      ∃ Hscope : ScopeEmbedding env Us scope c.vlctx,
        scope.fvars = c.vlctx.fvars.filter P ∧
        Hscope.shift = fvarSelectionLift c.vlctx.fvars P ∧
        (∀ fv ∈ scope.fvars, ∃ decl,
          c.lctx.find? fv = some decl) ∧
        (∀ body,
          Hscope.sourceTelescope.closeSource body =
            c.lctx.mkForall
              (scope.fvars.reverse.map Expr.fvar).toArray body) ∧
        Good scope := by
  induction c with
  | nil =>
    refine ⟨[], .nil, rfl, rfl, ?_, ?_, hgood⟩
    · intro fv hfv
      simp at hfv
    · intro body
      change body = ({} : LocalContext).mkForall #[] body
      exact (LocalContext.mkForall_empty {} body).symm
  | @vlam fv name type type' bi tail ih =>
    have HruntimeWF := Hwf.tr.wf
    rcases Hwf with ⟨HtailWF, hfresh, Htype, HtypeType⟩
    have hLtail : tail.vlctx.fvars.filter P <:+ Lsel := by
      refine List.IsSuffix.trans ?_ hL
      simp only [TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some, List.filter_cons]
      split
      · exact List.suffix_cons _ _
      · exact List.suffix_refl _
    have hsubLtail : ∀ fv' d, tail.lctx.find? fv' = some d →
        Lctx.find? fv' = some d := by
      intro fv' d hfind
      apply hsubL
      simp only [TypeChecker.MLCtx.lctx, LocalContext.mkLocalDecl,
        LocalContext.find?, HtailWF.tr.1.map_wf.find?_insert]
      rw [if_neg]
      · exact hfind
      · intro heq
        have heq' : fv = fv' := beq_iff_eq.mp heq
        rw [heq'] at hfresh
        rw [hfind] at hfresh
        contradiction
    rcases ih H.tail_vlam HtailWF hup.1 hLtail hsubLtail with
      ⟨tailScope, HtailScope, htailScopeFVars,
        htailShift, htailDecls, htailClose, htailGood⟩
    by_cases hP : P fv
    · have hdeps : type.fvarsList ⊆ tailScope.fvars := by
        intro dep hdep
        rw [htailScopeFVars]
        exact List.mem_filter.mpr ⟨Htype.fvarsList hdep, by
          simpa using hup.2 hP dep hdep⟩
      have hclosed : Closed type 0 := by
        have h := Htype.closed
        rw [tail.noBV] at h
        exact h
      have htypeFVars : FVarsIn (· ∈ tailScope.fvars) type := by
        apply fvarsIn_iff.mpr
        refine ⟨hdeps, ?_⟩
        exact Htype.fvarsIn.mono fun _ _ => trivial
      have hsuf : (fv :: tailScope.fvars) <:+ Lsel := by
        refine List.IsSuffix.trans ?_ hL
        rw [htailScopeFVars]
        simp only [TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some,
          List.filter_cons]
        have hPb : decide (P fv) = true := by simpa using hP
        simp [hP]
      have hdeclL : ∃ idx name' bi' kind,
          Lctx.find? fv = some (.cdecl idx fv name' type bi' kind) := by
        refine ⟨tail.lctx.decls.size, name, bi, .default, hsubL fv _ ?_⟩
        simp [TypeChecker.MLCtx.lctx, LocalContext.mkLocalDecl,
          LocalContext.find?, HtailWF.tr.1.map_wf.find?_insert]
      rcases oracle tailScope fv type htailGood hsuf hdeclL htypeFVars hclosed with
        ⟨narrowType, HnarrowType, HnarrowIsType, hnextGood⟩
      have Hweak : TrExprS env Us HtailScope.expanded type
          (narrowType.lift' HtailScope.shift) := by
        simpa using HnarrowType.weakFV' henv.ordered HtailScope.lift
          HtailScope.context.wf
      have HtargetEq := Hweak.uniq henv HtailScope.context Htype
      have HtargetType : env.IsType Us.length HtailScope.expanded.toCtx
          type' :=
        HtypeType.defeqDFC henv.ordered
          (HtailScope.context.symm henv.ordered).defeqCtx
      rcases HtargetType with ⟨u, HtargetType⟩
      have Hdomain : env.IsDefEq Us.length HtailScope.expanded.toCtx
          (narrowType.lift' HtailScope.shift) type' (.sort u) :=
        HtargetEq.of_r henv HtailScope.context.wf.toCtx HtargetType
      let Hnext := HtailScope.withIndex HruntimeWF hdeps name bi type
        HnarrowType Hdomain HnarrowIsType
      have hnextFVars : ∀ body,
          Hnext.sourceTelescope.closeSource body =
            HtailScope.sourceTelescope.closeSource
              (.forallE name type (body.abstractN [fv]) bi) := by
        intro body
        rfl
      have holdDecls : ∀ other ∈ tailScope.fvars.reverse,
          ∃ decl, tail.lctx.find? other = some decl := by
        intro other hother
        exact htailDecls other (List.mem_reverse.mp hother)
      have holdNodup : tailScope.fvars.reverse.Nodup :=
        List.nodup_reverse.mpr (HtailScope.scopeWF henv).fvars_nodup
      refine ⟨_, Hnext, by simp [htailScopeFVars, hP], ?_, ?_, ?_, hnextGood⟩
      · change HtailScope.shift.cons = _
        rw [htailShift]
        simp [fvarSelectionLift, hP]
      · intro other hother
        change other ∈ fv :: tailScope.fvars at hother
        simp only [List.mem_cons] at hother
        rcases hother with rfl | hother
        · refine ⟨.cdecl tail.lctx.decls.size other name type bi .default,
            ?_⟩
          simp [TypeChecker.MLCtx.lctx, LocalContext.mkLocalDecl,
            LocalContext.find?, HtailWF.tr.1.map_wf.find?_insert]
        · rcases htailDecls other hother with ⟨decl, hlookup⟩
          refine ⟨decl, ?_⟩
          simp only [TypeChecker.MLCtx.lctx, LocalContext.mkLocalDecl,
            LocalContext.find?, HtailWF.tr.1.map_wf.find?_insert]
          rw [if_neg]
          · exact hlookup
          · intro heq
            have heq' : fv = other := beq_iff_eq.mp heq
            rw [heq'] at hfresh
            rw [hlookup] at hfresh
            contradiction
      · intro body
        have Happ := LocalContext.mkForall_append_fresh
          HtailWF.tr.1 hfresh holdDecls holdNodup
          (body := body) (name := name) (type := type) (bi := bi)
        rw [hnextFVars body, htailClose]
        simpa [Hnext, TypeChecker.MLCtx.lctx, List.reverse_cons]
          using Happ.symm
    · have hskip : fv ∉ tailScope.fvars := by
        rw [htailScopeFVars]
        simp [hP]
      let Hnext := HtailScope.skipIndex henv HruntimeWF hskip
      have hnextFVars : ∀ body,
          Hnext.sourceTelescope.closeSource body =
            HtailScope.sourceTelescope.closeSource body := by
        intro body
        rfl
      refine ⟨_, Hnext, by simp [htailScopeFVars, hP], ?_, ?_, ?_, htailGood⟩
      · change HtailScope.shift.skip = _
        rw [htailShift]
        simp [fvarSelectionLift, hP]
      · intro other hother
        change other ∈ tailScope.fvars at hother
        rcases htailDecls other hother with ⟨decl, hlookup⟩
        refine ⟨decl, ?_⟩
        simp only [TypeChecker.MLCtx.lctx, LocalContext.mkLocalDecl,
          LocalContext.find?, HtailWF.tr.1.map_wf.find?_insert]
        rw [if_neg]
        · exact hlookup
        · intro heq
          have heq' : fv = other := beq_iff_eq.mp heq
          exact hskip (heq' ▸ hother)
      · intro body
        have Hskip := LocalContext.mkForall_skip_fresh
          HtailWF.tr.1
          (selected := tailScope.fvars.reverse) (body := body)
          (name := name) (type := type) (bi := bi)
          (by simpa using hskip)
        rw [hnextFVars body, htailClose]
        simpa [Hnext, TypeChecker.MLCtx.lctx] using Hskip.symm
  | @vlet fv name type value type' value' tail ih =>
    exact H.vlet_false.elim

/-- In a duplicate-free ambient list, filtering for the members of an
ordered sublist recovers that sublist exactly. -/
theorem List.filter_mem_eq_of_sublist_nodup
    {selected ambient : List FVarId}
    (hsub : selected <+ ambient) (hnodup : ambient.Nodup) :
    ambient.filter (· ∈ selected) = selected := by
  induction hsub with
  | slnil => simp
  | @cons selected' ambient' a hsub ih =>
    have ha : a ∉ ambient' := (List.nodup_cons.mp hnodup).1
    have haselected : a ∉ selected' := fun hmem => ha (hsub.subset hmem)
    simp [haselected, ih (List.nodup_cons.mp hnodup).2]
  | @cons_cons selected' ambient' a hsub ih =>
    have ha : a ∉ ambient' := (List.nodup_cons.mp hnodup).1
    have htail : ambient'.filter (· ∈ a :: selected') =
        ambient'.filter (· ∈ selected') := by
      apply List.filter_congr
      intro x hx
      have hxa : x ≠ a := by
        intro heq
        subst x
        exact ha hx
      simp [hxa]
    simp only [List.filter_cons, List.mem_cons, true_or, decide_true,
      ↓reduceIte, htail]
    rw [ih (List.nodup_cons.mp hnodup).2]

/-- The declarations of an all-lambda context are named lambdas. -/
theorem MLCtxOnlyLams.declarations {m : TypeChecker.MLCtx}
    (H : MLCtxOnlyLams m) :
    List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type))
      m.vlctx.fvars m.vlctx := by
  induction m with
  | nil => exact .nil
  | vlam fv name type type' bi tail ih =>
    exact .cons ⟨_, _, rfl⟩ (ih H.tail_vlam)
  | vlet => exact H.vlet_false.elim

/-- Closing over all declarations of an all-lambda context through its own
source telescope is the local-context `mkForall`. -/
theorem MLCtxOnlyLams.sources_closeSource {m : TypeChecker.MLCtx}
    {env : VEnv} {Us : List Name}
    (H : MLCtxOnlyLams m) (Hwf : m.WF env Us) (body : Expr) :
    (MLCtxOnlyLams.sources H Hwf).closeSource body =
      m.lctx.mkForall
        (m.vlctx.fvars.reverse.map Expr.fvar).toArray body := by
  induction m generalizing body with
  | nil =>
    change body = ({} : LocalContext).mkForall #[] body
    exact (LocalContext.mkForall_empty {} body).symm
  | @vlam fv name type type' bi tail ih =>
    have HtailWF := Hwf.1
    have hfresh := Hwf.2.1
    change (MLCtxOnlyLams.sources H.tail_vlam HtailWF).closeSource
        (.forallE name type (body.abstractN [fv]) bi) = _
    rw [ih H.tail_vlam HtailWF]
    have holdDecls : ∀ other ∈ tail.vlctx.fvars.reverse,
        ∃ decl, tail.lctx.find? other = some decl := fun other hother =>
      HtailWF.tr.find?_eq_some.2 (List.mem_reverse.mp hother)
    have holdNodup : tail.vlctx.fvars.reverse.Nodup :=
      List.nodup_reverse.mpr HtailWF.tr.wf.fvars_nodup
    have Happ := LocalContext.mkForall_append_fresh
      HtailWF.tr.1 hfresh holdDecls holdNodup
      (body := body) (name := name) (type := type) (bi := bi)
    simpa [TypeChecker.MLCtx.lctx, List.reverse_cons] using Happ.symm
  | vlet => exact H.vlet_false.elim

/-- A dependency-closed scope of a free-variable weakening: the selected
declarations only depend on selected declarations. -/
theorem _root_.Lean4Lean.VLCtx.FVLift'.upsetScope {Δ Δ' : VLCtx}
    {dk k : Nat} {n : Lift} {env : VEnv} {U : Nat}
    (W : VLCtx.FVLift' Δ Δ' dk n k) (hwf : Δ'.WF env U) :
    IsFVarUpSet (· ∈ Δ.fvars) Δ' := by
  induction W with
  | refl => exact IsFVarUpSet.fvars hwf.fvwf
  | skip_fvar fv d W ih =>
    obtain ⟨fv, deps⟩ := fv
    refine ⟨ih hwf.1, fun h => ?_⟩
    exact ((hwf.2.1 _ _ rfl).1 (W.fvars_sublist.subset h)).elim
  | cons_fvar fv d hd W ih =>
    obtain ⟨fv, deps⟩ := fv
    refine ⟨(IsFVarUpSet.congr hwf.1.fvwf fun x hx => ?_).1 (ih hwf.1), ?_⟩
    · simp only [VLCtx.fvars_cons_some, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h)
        · exact ((hwf.2.1 _ _ rfl).1 hx).elim
        · exact h
    · intro _ dep hdep
      simp only [VLCtx.fvars_cons_some, List.mem_cons]
      exact Or.inr (hd hdep)
  | cons_bvar d W ih => exact ih hwf.1

/-- A checker `MLCtx` embedded in a runtime context is a dependency-selected
scope of it, with its own source telescope. -/
theorem ScopeEmbedding.ofEmbedding {m : TypeChecker.MLCtx}
    {env : VEnv} {Us : List Name} {runtime : VLCtx}
    (Hm : m.WF env Us) (Honly : MLCtxOnlyLams m)
    (hemb : ChkEmbeds env Us.length m.vlctx runtime) :
    ∃ Hs : ScopeEmbedding env Us m.vlctx runtime,
      Hs.sourceTelescope = MLCtxOnlyLams.sources Honly Hm := by
  obtain ⟨Δ', n, W, hD⟩ := hemb
  exact ⟨{
    expanded := Δ'
    shift := n
    lift := W
    context := hD
    upset := hD.isFVarUpSet.1 (W.upsetScope hD.wf)
    noBV := m.noBV
    declarations := MLCtxOnlyLams.declarations Honly
    sourceTelescope := MLCtxOnlyLams.sources Honly Hm
    wf := Hm.tr.wf }, rfl⟩

/-- The checker context of `Hc`, aligned with a semantic scope, supplies an
independent source-aware scope without restricting any runtime
translation. -/
theorem FrontScopeEmbedding.independentSourceScopeOfCheck
    {c : AddInductive.Context} {Hc : ContextWF c}
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length scope Hc.chk.vlctx) :
    ∃ sourceScope,
      ∃ Hsource : ScopeEmbedding Hc.venv c.lparams sourceScope
          Hc.mlctx.vlctx,
        sourceScope.fvars = scope.fvars ∧
        ∀ body,
          Hsource.sourceTelescope.closeSource body =
            Hc.mlctx.lctx.mkForall
              (sourceScope.fvars.reverse.map Expr.fvar).toArray body := by
  obtain ⟨Hsource, hsources⟩ := ScopeEmbedding.ofEmbedding
    Hc.check.wf Hc.check.onlyLams Hc.check.embed
  refine ⟨Hc.chk.vlctx, Hsource, halign.fvars.symm, fun body => ?_⟩
  rw [hsources, MLCtxOnlyLams.sources_closeSource, Hc.lctx_eq]
  have hmem : ∀ fv ∈ Hc.chk.vlctx.fvars.reverse,
      ∃ d, c.checkLCtx.find? fv = some d := by
    intro fv hfv
    rw [← Hc.check.lctx_eq]
    exact Hc.check.wf.tr.find?_eq_some.2 (List.mem_reverse.mp hfv)
  rw [Hc.checkSub.mkForall_eq hmem body]
  exact congrArg (fun l : LocalContext => l.mkForall _ body) Hc.check.lctx_eq

/-- The full source-aware scope of an all-lambda context: the context
itself, with its own source telescope. -/
theorem MLCtxOnlyLams.fullSourceScope
    {c : TypeChecker.MLCtx} {env : VEnv} {Us : List Name}
    (H : MLCtxOnlyLams c) (henv : env.WF) (Hwf : c.WF env Us) :
    ∃ scope,
      ∃ Hscope : ScopeEmbedding env Us scope c.vlctx,
        scope.fvars = c.vlctx.fvars.filter (· ∈ c.vlctx.fvars) ∧
        ∀ body,
          Hscope.sourceTelescope.closeSource body =
            c.lctx.mkForall
              (scope.fvars.reverse.map Expr.fvar).toArray body := by
  obtain ⟨Hscope, hsources⟩ := ScopeEmbedding.ofEmbedding Hwf H
    (ChkEmbeds.refl henv.ordered Hwf.tr.wf)
  refine ⟨c.vlctx, Hscope, ?_, fun body => ?_⟩
  · exact (List.filter_mem_eq_of_sublist_nodup (.refl _)
      Hwf.tr.wf.fvars_nodup).symm
  · rw [hsources]
    exact MLCtxOnlyLams.sources_closeSource H Hwf body

/-- At the parameter/index boundary, discard the ambient prefix retained
from previously checked mutual headers and keep the exact cached-parameter
suffix as the semantic scope. -/
def FrontScopeEmbedding.ofParameterSuffix
    (Hc : ContextWF c)
    (Hsuffix : ParameterContextSuffix Hc stats depth) :
    FrontScopeEmbedding Hc.venv c.lparams Hsuffix.parameterDecls
      Hc.mlctx.vlctx := by
  have hambient : Hsuffix.ambientDecls.NoBV := by
    apply VLCtx.NoBV.leftOfAppend Hsuffix.ambientDecls
      Hsuffix.parameterDecls
    rw [← Hsuffix.context]
    exact Hc.mlctx.noBV
  let W := VLCtx.FVLift.to_append Hsuffix.parameterDecls hambient
  refine {
    expanded := Hc.mlctx.vlctx
    shift := .skipN .refl Hsuffix.ambientDecls.toCtx.length
    lift := ?_
    frontSourceDomains := []
    frontExpandedDomains := []
    front := ?_
    context := .refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
    upset := ?_
    noBV := ?_
    noIndConsts := Hsuffix.noIndConsts
    sourceTelescope := Hsuffix.sources
    wf := ?_ }
  · rw [Hsuffix.context]
    exact W.toFVLift'
  · exact .zero (by
      rw [Hsuffix.context]
      exact W.toFVLift')
  · have hwf : VLCtx.WF Hc.venv c.lparams.length
        (Hsuffix.ambientDecls ++ Hsuffix.parameterDecls) := by
      rw [← Hsuffix.context]
      exact Hc.mlctx_wf.tr.wf
    simpa [Hsuffix.context] using
      (IsFVarUpSet.suffixFVars Hsuffix.parameterDecls
        Hsuffix.ambientDecls hwf)
  · have hfull : (Hsuffix.ambientDecls ++
        Hsuffix.parameterDecls).NoBV := by
      rw [← Hsuffix.context]
      exact Hc.mlctx.noBV
    change Hsuffix.parameterDecls.bvars = 0
    change (Hsuffix.ambientDecls ++
      Hsuffix.parameterDecls).bvars = 0 at hfull
    rw [VLCtx.bvars_append] at hfull
    omega
  · have hwf : VLCtx.WF Hc.venv c.lparams.length
        (Hsuffix.ambientDecls ++ Hsuffix.parameterDecls) := by
      rw [← Hsuffix.context]
      exact Hc.mlctx_wf.tr.wf
    exact hwf.append_right

/-- Relate a domain translated in the semantic scope to the unannotated
domain installed by the executable checker. -/
theorem FrontScopeEmbedding.unannotatedDomain
    (Hc : ContextWF c)
    (H : FrontScopeEmbedding Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hdom : Hc.UnannotatedDomain dom sourceDom consumedDom)
    (hnarrow : TrExprS Hc.venv c.lparams scope dom indexType) :
    ∃ u, Hc.venv.IsDefEq c.lparams.length H.expanded.toCtx
      (indexType.lift' H.shift) consumedDom (.sort u) := by
  have hweak : TrExprS Hc.venv c.lparams H.expanded dom
      (indexType.lift' H.shift) := by
    simpa using hnarrow.weakFV' Hc.checking.tr.wf.ordered H.lift
      H.context.wf
  have hsource := hweak.uniq Hc.checking.tr.wf H.context Hdom.source
  rcases Hdom.source_defeq with ⟨u, hsourceConsumed⟩
  have hsourceConsumed' := hsourceConsumed.defeqDFC
    Hc.checking.tr.wf.ordered
    (H.context.defeqCtx.symm Hc.checking.tr.wf.ordered)
  have hdomainU := hsource.trans Hc.checking.tr.wf H.context.wf.toCtx
    ⟨_, hsourceConsumed'⟩
  exact ⟨u, hdomainU.of_r Hc.checking.tr.wf H.context.wf.toCtx
    hsourceConsumed'.hasType.2⟩

theorem FrontScopeEmbedding.recursorUnannotatedDomain
    (R : RecursorContextWF c recLparams)
    (H : FrontScopeEmbedding R.venv recLparams scope R.mlctx.vlctx)
    (Hdom : R.UnannotatedDomain dom sourceDom consumedDom)
    (hnarrow : TrExprS R.venv recLparams scope dom indexType) :
    ∃ u, R.venv.IsDefEq recLparams.length H.expanded.toCtx
      (indexType.lift' H.shift) consumedDom (.sort u) := by
  have hweak : TrExprS R.venv recLparams H.expanded dom
      (indexType.lift' H.shift) := by
    simpa using hnarrow.weakFV' R.checking.tr.wf.ordered H.lift
      H.context.wf
  have hsource := hweak.uniq R.checking.tr.wf H.context Hdom.source
  rcases Hdom.source_defeq with ⟨u, hsourceConsumed⟩
  have hsourceConsumed' := hsourceConsumed.defeqDFC
    R.checking.tr.wf.ordered
    (H.context.defeqCtx.symm R.checking.tr.wf.ordered)
  have hdomainU := hsource.trans R.checking.tr.wf H.context.wf.toCtx
    ⟨_, hsourceConsumed'⟩
  exact ⟨u, hdomainU.of_r R.checking.tr.wf H.context.wf.toCtx
    hsourceConsumed'.hasType.2⟩

end checkInductiveTypes.loopType
end VerifyInductive
end Lean4Lean
