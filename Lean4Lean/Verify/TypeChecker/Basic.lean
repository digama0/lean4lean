import Lean4Lean.Verify.TypeChecker.CheckerEnv
import Lean4Lean.Verify.Typing.ConditionallyTyped
import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Typing.ProjectionShape
import Lean4Lean.TypeChecker
import Lean4Lean.Verify.NameGenerator
import Lean4Lean.Verify.Typing.UniverseSupport
import Lean4Lean.Verify.ParamUniformEnv

namespace Except

def WF (x : Except ε α) (Q : α → Prop) : Prop := ∀ a, x = .ok a → Q a

theorem WF.bind {x : Except ε α} {f : α → Except ε β} {Q R}
    (h1 : x.WF Q) (h2 : ∀ a, Q a → (f a).WF R) : (x >>= f).WF R := by
  intro b
  simp [(· >>= ·), Except.bind]
  split; · simp
  exact h2 _ (h1 _ rfl) _

theorem WF.pure {Q} (H : Q a) :
    (pure a : Except ε α).WF Q := by rintro _ ⟨⟩; exact H

theorem WF.map {x : Except ε α} {f : α → β} {Q R}
    (h1 : x.WF Q) (h2 : ∀ a, Q a → R (f a)) : (f <$> x).WF R := by
  rw [map_eq_pure_bind]
  exact h1.bind fun _ h => .pure (h2 _ h)

theorem WF.mono {x : Except ε α} {Q R}
    (h1 : x.WF Q) (h2 : ∀ a, Q a → R a) : x.WF R := by
  simpa using h1.bind fun _ h => .pure (h2 _ h)

theorem WF.throw {Q} : (throw e : Except ε α).WF Q := nofun

theorem WF.le {Q R} {x : Except ε α}
    (h1 : x.WF Q) (H : ∀ a, Q a → R a) :
    x.WF R := fun _ e => H _ (h1 _ e)

theorem WF.pureBind  {f : β → Except ε α} {Q}
    {x : β} (H : WF (f x) Q) : ((Pure.pure x : Except ε β) >>= f).WF Q := H

end Except

namespace Lean4Lean
open Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace EquivManager

variable {env : VEnv} {Us : List Name} {Δ : VLCtx}
variable (env Us Δ) in
inductive IsDefEqE : Expr → Expr → Prop
  | rfl : IsDefEqE e e
  | trans : IsDefEqE e₁ e₂ → IsDefEqE e₂ e₃ → IsDefEqE e₁ e₃
  | defeq : TrExprS env Us Δ e₁ e' → TrExpr env Us Δ e₂ e' → IsDefEqE e₁ e₂
  | app : IsDefEqE f₁ f₂ → IsDefEqE a₁ a₂ → IsDefEqE (.app f₁ a₁) (.app f₂ a₂)
  | lam : IsDefEqE d₁ d₂ → IsDefEqE b₁ b₂ → IsDefEqE (.lam _ d₁ b₁ _) (.lam _ d₂ b₂ _)
  | forallE : IsDefEqE d₁ d₂ → IsDefEqE b₁ b₂ → IsDefEqE (.forallE _ d₁ b₁ _) (.forallE _ d₂ b₂ _)
  | letE : IsDefEqE t₁ t₂ → IsDefEqE v₁ v₂ → IsDefEqE b₁ b₂ →
    IsDefEqE (.letE _ t₁ v₁ b₁ _) (.letE _ t₂ v₂ b₂ _)
  | mdata : IsDefEqE e₁ e₂ → IsDefEqE (.mdata _ e₁) (.mdata _ e₂)
  | proj : IsDefEqE e₁ e₂ →
      IsDefEqE (.proj typeName i e₁) (.proj typeName i e₂)

theorem IsDefEqE.symm (H1 : IsDefEqE env Us Δ e₁ e₂) : IsDefEqE env Us Δ e₂ e₁ := by
  induction H1 with
  | rfl => exact .rfl
  | trans _ _ ih1 ih2 => exact .trans ih2 ih1
  | defeq h1 h2 => let ⟨_, h2, h3⟩ := h2; exact .defeq h2 ⟨_, h1, h3.symm⟩
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

variable! (henv : env.WF) (W : VLCtx.FVLift' Δ Δ' 0 n 0) (hΔ : VLCtx.WF env Us.length Δ') in
theorem IsDefEqE.weak' (H1 : IsDefEqE env Us Δ e₁ e₂) : IsDefEqE env Us Δ' e₁ e₂ := by
  induction H1 with
  | rfl => exact .rfl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | defeq h1 h2 => exact .defeq (h1.weakFV' henv W hΔ) (h2.weakFV' henv W hΔ)
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

variable (env Us Δ) in
structure WF (m : EquivManager) where
  wf {i} : i < m.uf.size ↔ ∃ e : Expr, m.toNodeMap[e]? = some i
  defeq {e₁ e₂ : Expr} {i₁ i₂} :
    m.toNodeMap[e₁]? = some i₁ → m.toNodeMap[e₂]? = some i₂ → m.uf.Equiv i₁ i₂ →
    IsDefEqE env Us Δ e₁ e₂

theorem WF.empty : WF env Us Δ {} where
  wf := by simp
  defeq := by simp

variable! (henv : env.WF) (W : VLCtx.FVLift' Δ Δ' 0 n 0) (hΔ : VLCtx.WF env Us.length Δ') in
theorem WF.weak' (wf : WF env Us Δ m) : WF env Us Δ' m where
  wf := wf.wf
  defeq h1 h2 h3 := wf.defeq h1 h2 h3 |>.weak' henv W hΔ

end EquivManager

namespace TypeChecker

inductive MLCtx where
  | nil : MLCtx
  | vlam (id : FVarId) (name : Name) (ty : Expr) (ty' : VExpr) (bi : BinderInfo) : MLCtx → MLCtx
  | vlet (id : FVarId) (name : Name) (ty v : Expr) (ty' v' : VExpr) : MLCtx → MLCtx

@[simp] def MLCtx.vlctx : MLCtx → VLCtx
  | .nil => []
  | .vlam id _ ty ty' _ c => (some (id, ty.fvarsList), .vlam ty') :: c.vlctx
  | .vlet id _ ty v ty' v' c => (some (id, ty.fvarsList ++ v.fvarsList), .vlet ty' v') :: c.vlctx

def MLCtx.lctx : MLCtx → LocalContext
  | .nil => {}
  | .vlam id name ty _ bi c => c.lctx.mkLocalDecl id name ty bi
  | .vlet id name ty val _ _ c => c.lctx.mkLetDecl id name ty val

@[simp] def MLCtx.length : MLCtx → Nat
  | .nil => 0
  | .vlam _ _ _ _ _ c
  | .vlet _ _ _ _ _ _ c => c.length + 1

def MLCtx.decls : MLCtx → List LocalDecl
  | .nil => {}
  | .vlam x name ty _ bi c => .cdecl c.length x name ty bi .default :: c.decls
  | .vlet x name ty v _ _ c => .ldecl c.length x name ty v false default :: c.decls

@[simp] def MLCtx.fvarRevList (c : MLCtx) (n) (hn : n ≤ c.length) : List FVarId :=
  match n, c, hn with
  | 0, _, _ => []
  | n+1, .vlam id _ _ _ _ c, h
  | n+1, .vlet id _ _ _ _ _ c, h => id :: c.fvarRevList n (Nat.le_of_succ_le_succ h)
termination_by structural n

@[simp] theorem MLCtx.fvarRevList_length {c n hn} : (MLCtx.fvarRevList c n hn).length = n := by
  induction n generalizing c <;> [simp; cases c <;> simp [*] at hn ⊢]

@[simp] def MLCtx.letValList (c : MLCtx) (n) (hn : n ≤ c.length) : List (Option (Expr × Expr)) :=
  match n, c, hn with
  | 0, _, _ => []
  | n+1, .vlam _ _ _ _ _ c, h => none :: c.letValList n (Nat.le_of_succ_le_succ h)
  | n+1, .vlet _ _ ty v _ _ c, h => some (ty, v) :: c.letValList n (Nat.le_of_succ_le_succ h)
termination_by structural n

@[simp] theorem MLCtx.letValList_length {c n hn} : (MLCtx.letValList c n hn).length = n := by
  induction n generalizing c <;> [simp; cases c <;> simp [*] at hn ⊢]

@[simp] def MLCtx.dropN (c : MLCtx) (n) (hn : n ≤ c.length) : MLCtx :=
  match n, c, hn with
  | 0, c, _ => c
  | n+1, .vlam _ _ _ _ _ c, h
  | n+1, .vlet _ _ _ _ _ _ c, h => c.dropN n (Nat.le_of_succ_le_succ h)
termination_by structural n

def MLCtx.WF (env : VEnv) (Us : List Name) : MLCtx → Prop
  | .nil => True
  | .vlam fv _ ty ty' _ c =>
    c.WF env Us ∧ c.lctx.find? fv = none ∧
    TrExprS env Us c.vlctx ty ty' ∧
    env.IsType Us.length c.vlctx.toCtx ty'
  | .vlet fv _ ty v ty' v' c =>
    c.WF env Us ∧ c.lctx.find? fv = none ∧
    TrExprS env Us c.vlctx ty ty' ∧ TrExprS env Us c.vlctx v v' ∧
    env.HasType Us.length c.vlctx.toCtx v' ty'

/-- Keep the concrete local context fixed while shifting every stored
abstract universe parameter to make room for one fresh leading parameter. -/
def MLCtx.prependLevelParam (c : MLCtx) (oldUvars : Nat) : MLCtx :=
  match c with
  | .nil => .nil
  | .vlam fv name ty ty' bi tail =>
    .vlam fv name ty (ty'.instL (VLevel.prependShift oldUvars)) bi
      (tail.prependLevelParam oldUvars)
  | .vlet fv name ty value ty' value' tail =>
    .vlet fv name ty value
      (ty'.instL (VLevel.prependShift oldUvars))
      (value'.instL (VLevel.prependShift oldUvars))
      (tail.prependLevelParam oldUvars)

@[simp] theorem MLCtx.prependLevelParam_length
    {c : MLCtx} {oldUvars : Nat} :
    (c.prependLevelParam oldUvars).length = c.length := by
  induction c <;> simp [MLCtx.prependLevelParam, *]

@[simp] theorem MLCtx.prependLevelParam_lctx
    {c : MLCtx} {oldUvars : Nat} :
    (c.prependLevelParam oldUvars).lctx = c.lctx := by
  induction c <;> simp [MLCtx.prependLevelParam, MLCtx.lctx, *]

@[simp] theorem MLCtx.prependLevelParam_decls
    {c : MLCtx} {oldUvars : Nat} :
    (c.prependLevelParam oldUvars).decls = c.decls := by
  induction c <;> simp [MLCtx.prependLevelParam, MLCtx.decls, *]

@[simp] theorem MLCtx.prependLevelParam_vlctx
    {c : MLCtx} {oldUvars : Nat} :
    (c.prependLevelParam oldUvars).vlctx =
      c.vlctx.instL (VLevel.prependShift oldUvars) := by
  induction c <;> simp [MLCtx.prependLevelParam, MLCtx.vlctx,
    VLCtx.instL, VLocalDecl.instL, *]

theorem MLCtx.WF.mono {env env' : VEnv} (henv : env ≤ env') :
    ∀ {c : MLCtx}, c.WF env Us → c.WF env' Us
  | .nil, _ => trivial
  | .vlam .., ⟨hc, hfresh, htr, hty⟩ =>
    ⟨hc.mono henv, hfresh, htr.mono henv, hty.mono henv⟩
  | .vlet .., ⟨hc, hfresh, hty, hvalue, hhas⟩ =>
    ⟨hc.mono henv, hfresh, hty.mono henv, hvalue.mono henv,
      hhas.mono henv⟩

theorem MLCtx.WF.tr : ∀ {c : MLCtx}, c.WF env Us → TrLCtx env Us c.lctx c.vlctx
  | .nil, _ => ⟨.nil, .nil⟩
  | .vlam .., ⟨h1, h2, h3, h4⟩ => .mkLocalDecl h1.tr h2 h3 h4
  | .vlet .., ⟨h1, h2, h3, h4, h5⟩ => .mkLetDecl h1.tr h2 h3 h4 h5

/-- The rebased `MLCtx` is semantically well formed under the extended
universe list; crucially, all concrete local declaration types are unchanged. -/
theorem MLCtx.WF.prependLevelParam
    {c : MLCtx} {env : VEnv} {Us : List Name} {fresh : Name}
    (H : c.WF env Us) (henv : env.WF) (hfresh : fresh ∉ Us) :
    (c.prependLevelParam Us.length).WF env (fresh :: Us) := by
  let shift := VLevel.prependShift Us.length
  have hshift : ∀ level ∈ shift, level.WF (fresh :: Us).length := by
    simpa [shift] using VLevel.prependShift_wf (n := Us.length)
  induction c with
  | nil => trivial
  | vlam fv name ty ty' bi tail ih =>
    rcases H with ⟨Htail, hfind, htr, hty⟩
    refine ⟨ih Htail, by simpa using hfind, ?_, ?_⟩
    · simpa [shift] using htr.prependLevelParam henv Htail.tr.wf hfresh
    · simpa [shift] using hty.instL hshift
  | vlet fv name ty value ty' value' tail ih =>
    rcases H with ⟨Htail, hfind, hty, hvalue, hhas⟩
    refine ⟨ih Htail, by simpa using hfind, ?_, ?_, ?_⟩
    · simpa [shift] using hty.prependLevelParam henv Htail.tr.wf hfresh
    · simpa [shift] using hvalue.prependLevelParam henv Htail.tr.wf hfresh
    · simpa [shift] using hhas.instL hshift

theorem MLCtx.WF.dropN {c : MLCtx} (n hn) : c.WF env Us → (c.dropN n hn).WF env Us :=
  match n, c, hn with
  | 0, _, _ => id
  | n+1, .vlam .., h
  | n+1, .vlet .., h => fun H => H.1.dropN n (Nat.le_of_succ_le_succ h)

theorem MLCtx.dropN_fvars_subset {c : MLCtx} (n hn) : (c.dropN n hn).vlctx.fvars ⊆ c.vlctx.fvars :=
  match n, c, hn with
  | 0, _, _ => fun _ => id
  | n+1, .vlam .., h
  | n+1, .vlet .., h =>
    List.subset_cons_of_subset _ <| dropN_fvars_subset n (Nat.le_of_succ_le_succ h)

theorem MLCtx.noBV (c : MLCtx) : c.vlctx.NoBV := by
  induction c <;> trivial

theorem MLCtx.WF.decls_size {c : MLCtx} (wf : c.WF env Us) :
    c.lctx.decls.size = c.length := by
  rw [← wf.tr.1.decls_wf.toList'_length]
  induction c with
  | nil => rfl
  | vlam _ _ _ _ _ _ ih => simp [lctx, LocalContext.mkLocalDecl, ih wf.1]
  | vlet _ _ _ _ _ _ _ ih => simp [lctx, LocalContext.mkLetDecl, ih wf.1]

theorem MLCtx.WF.toList_eq {c : MLCtx} (wf : c.WF env Us) :
    c.lctx.toList = c.decls := by
  simp [LocalContext.toList]
  induction c with
  | nil => rfl
  | vlam _ _ _ _ _ _ ih => simp [lctx, LocalContext.mkLocalDecl, decls, ih wf.1, wf.1.decls_size]
  | vlet _ _ _ _ _ _ _ ih => simp [lctx, LocalContext.mkLetDecl, decls, ih wf.1, wf.1.decls_size]

theorem MLCtx.WF.find?_eq {c : MLCtx} (wf : c.WF env Us) :
    c.lctx.find? x = c.decls.find? (x == ·.fvarId) := by
  simp [wf.tr.1.find?_eq_find?_toList, wf.toList_eq]

structure VContext extends Context where
  venv : VEnv
  hasPrimitives : VEnv.HasPrimitives venv
  safePrimitives : env.find? n = some ci →
    Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []
  /-- Everything the checker reads of its environment (`CheckerEnv`). -/
  trenv : CheckerEnv safety env venv
  mlctx : MLCtx
  mlctx_wf : mlctx.WF venv lparams
  lctx_eq : mlctx.lctx = lctx

@[simp] abbrev VContext.lctx' (c : VContext) := c.mlctx.lctx
@[simp] abbrev VContext.vlctx (c : VContext) := c.mlctx.vlctx

theorem VContext.trlctx (c : VContext) : TrLCtx c.venv c.lparams c.lctx' c.vlctx := c.mlctx_wf.tr
theorem VContext.Ewf (c : VContext) : VEnv.WF c.venv := c.trenv.wf

theorem VContext.Δwf (c : VContext) : c.vlctx.WF c.venv c.lparams.length := c.trlctx.wf

/-- Every present constructor is listed by its present owner, with the owner's `isUnsafe`.
This is what identifies a constructor at the head of a term with the constructor of its
structure in structure eta. -/
theorem VContext.constructorOwners (c : VContext) :
    VerifyInductive.ConstructorOwnersPresent c.env := c.trenv.constructorOwners

/-- Every constructor name a present header lists is, if present, a constructor of that
header, with its `isUnsafe`. -/
theorem VContext.listedConstructors (c : VContext) :
    VerifyInductive.ListedConstructorsCoherent c.env := c.trenv.listedConstructors

/-- Every visible singleton family whose constructor is present aligns with the abstract
projection registry.  This is what projection inference reads. -/
theorem VContext.projectionRegistry (c : VContext) :
    ProjectionRegistryCoherent c.safety c.env.constants c.venv :=
  c.trenv.projectionRegistry

/-- Every visible recursor has its shapes (`RecursorsCoherent`). This is what recursor reduction
reads, together with the registered ι rules (`VContext.iota`). -/
theorem VContext.recursors (c : VContext) : RecursorsCoherent c.safety c.env.constants c.venv :=
  c.trenv.recursors

/-- The ι rules of the visible recursors are registered. -/
theorem VContext.iota (c : VContext) : IotaRulesRegistered c.safety c.env c.venv :=
  c.trenv.iota

/-- Context strengthening (`VEnv.WF.strengthening`, on `IsDefEqU.weakN_iff`). The caches and
the equivalence manager persist across binders, as in the C++ kernel, and a fact found under a
binder is moved out of it with this. -/
theorem VContext.strengthening (c : VContext) : c.venv.Strengthening := c.Ewf.strengthening

/-- Resolve the exact projection alignment selected by successful concrete
family and constructor lookups in a checking context. -/
theorem VContext.projectionAlignment (c : VContext)
    (hfamily : c.env.find? familyName = some (.inductInfo familyInfo))
    (habstract : c.venv.constants familyName = some familyConstant)
    (hsingle : familyInfo.ctors = [constructorName])
    (hconstructor : c.env.find? constructorName =
      some (.ctorInfo constructorInfo))
    (hinduct : constructorInfo.induct = familyName) :
    Nonempty (ProjectionRegistryAlignmentAt c.env.constants c.venv familyName
      familyInfo constructorName) := by
  have hfamilyMap : c.env.constants.find? familyName =
      some (.inductInfo familyInfo) := by
    rwa [← c.trenv.map_wf.find?'_eq_find?]
  have hconstructorMap : c.env.constants.find? constructorName =
      some (.ctorInfo constructorInfo) := by
    rwa [← c.trenv.map_wf.find?'_eq_find?]
  have hvisible : c.safety ≤
      (ConstantInfo.inductInfo familyInfo).safety :=
    (c.trenv.find?_uniq hfamily habstract).2.1
  exact c.projectionRegistry familyName familyInfo constructorName
    constructorInfo hfamilyMap hvisible hsingle hconstructorMap hinduct

nonrec abbrev VContext.TrExprS (c : VContext) : Expr → VExpr → Prop :=
  TrExprS c.venv c.lparams c.vlctx
nonrec abbrev VContext.TrExpr (c : VContext) : Expr → VExpr → Prop :=
  TrExpr c.venv c.lparams c.vlctx
nonrec abbrev VContext.IsType (c : VContext) : VExpr → Prop :=
  c.venv.IsType c.lparams.length c.vlctx.toCtx
nonrec abbrev VContext.HasType (c : VContext) : VExpr → VExpr → Prop :=
  c.venv.HasType c.lparams.length c.vlctx.toCtx
nonrec abbrev VContext.IsDefEqU (c : VContext) : VExpr → VExpr → Prop :=
  c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx
nonrec abbrev VContext.TrLCtx (c : VContext) : Prop :=
  TrLCtx c.venv c.lparams c.lctx' c.vlctx
nonrec abbrev VContext.FVarsBelow (c : VContext) : Expr → Expr → Prop :=
  FVarsBelow c.vlctx
nonrec abbrev VContext.TrTyping (c : VContext) : Expr → Expr → VExpr → VExpr → Prop :=
  TrTyping c.venv c.lparams c.vlctx

/-- The abstract constant of a structure whose constructor is present: the constructor's
visibility transfers to the family when both record the same `isUnsafe` flag. -/
theorem VContext.familyConstant (c : VContext) {n mkC : Name} {sInfo : InductiveVal}
    {mkInfo : ConstructorVal} {ci' : VConstant}
    (hfind : c.env.find? n = some (.inductInfo sInfo))
    (hci : c.env.find? mkC = some (.ctorInfo mkInfo))
    (hunsafe : mkInfo.isUnsafe = sInfo.isUnsafe)
    (hfc : c.venv.constants mkC = some ci') :
    ∃ ci, c.venv.constants n = some ci := by
  obtain ⟨-, hsafe, -⟩ := c.trenv.find?_uniq hci hfc
  have hvis : c.safety ≤ (ConstantInfo.inductInfo sInfo).safety := by
    simpa [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, hunsafe] using hsafe
  exact c.trenv.find?_iff.1 ⟨_, hfind, hvis⟩

/-- The field count of the constructor of a visible single-constructor family is the syntactic
arity of its stored type beyond the parameters. -/
theorem VContext.constructorArity {c : VContext} {n mkC : Name} {structInfo : InductiveVal}
    {mkInfo : ConstructorVal} {familyConstant : VConstant}
    (hfind : c.env.find? n = some (.inductInfo structInfo))
    (habstract : c.venv.constants n = some familyConstant)
    (hsingle : structInfo.ctors = [mkC])
    (hci : c.env.find? mkC = some (.ctorInfo mkInfo))
    (hinduct : mkInfo.induct = n) :
    mkInfo.numFields = AddInductive.constructorArity mkInfo.type - mkInfo.numParams := by
  obtain ⟨A⟩ := c.projectionAlignment hfind habstract hsingle hci hinduct
  have hciMap : c.env.constants.find? mkC = some (.ctorInfo mkInfo) := by
    rwa [← c.trenv.map_wf.find?'_eq_find?]
  have hcEq : A.constructorInfo = mkInfo := by
    have := A.constructor_lookup
    rw [hciMap] at this
    cases this
    rfl
  rw [← hcEq]
  exact A.constructor_arity

/-- The facts about a single-constructor inductive and its constructor that the checker's
projection, structure-eta and unit-like steps consume, read off the projection registry.

TODO: derive from `c.projectionRegistry` and `Ordered.projectionShape`. -/
theorem VContext.registryShape {c : VContext} {n mkC : Name} {structInfo : InductiveVal}
    {mkInfo : ConstructorVal} {familyConstant : VConstant}
    (hfind : c.env.find? n = some (.inductInfo structInfo))
    (habstract : c.venv.constants n = some familyConstant)
    (hsingle : structInfo.ctors = [mkC])
    (hci : c.env.find? mkC = some (.ctorInfo mkInfo))
    (hinduct : mkInfo.induct = n) :
    ∃ info, c.venv.projections n info ∧ info.ctorName = mkC ∧
    ∃ (decl : VInductDecl) (doms : List VExpr) (result : VExpr),
      c.venv.IsType info.uvars [] info.ctorType ∧
      c.venv.constants info.ctorName = some ⟨info.uvars, info.ctorType⟩ ∧
      info.ctorType = VExpr.wrapForalls doms result ∧
      decl.RawIndAppAt (some n) (doms.length - decl.nparams) result ∧
      result.getAppFnArgs.1 = .const n (VLevel.params decl.uvars) ∧
      decl.nparams = info.nparams ∧ decl.uvars = info.uvars ∧ info.nparams ≤ doms.length ∧
      mkInfo.numParams = info.nparams ∧ mkInfo.numFields = doms.length - info.nparams ∧
      info.numFields = mkInfo.numFields ∧
      structInfo.numParams = info.nparams ∧ structInfo.numIndices = info.nindices ∧
      (∀ type ∈ decl.types, type.name = n → type.numIndices = info.nindices) ∧
      -- the structure type constant has the constructor's universe parameters
      (∃ indType, c.venv.constants n = some ⟨info.uvars, indType⟩) ∧
      -- the canonical sort of a fully applied type
      (∀ (ls : List VLevel) (args : List VExpr), ls.length = info.uvars →
        args.length = info.nparams + info.nindices →
        (∃ u, c.HasType (VExpr.mkApps (.const n ls) args) (.sort u)) →
        c.HasType (VExpr.mkApps (.const n ls) args) (.sort (info.resultLevel.inst ls))) ∧
      -- the parameters of a well-formed type application are typed at the constructor's
      -- parameter binders
      (∀ (ls : List VLevel) (args : List VExpr), ls.length = info.uvars →
        (hargs : args.length = info.nparams + info.nindices) →
        (∃ u, c.HasType (VExpr.mkApps (.const n ls) args) (.sort u)) →
        ∀ k (hk : k < info.nparams) (hk' : k < doms.length),
          c.HasType (args[k]'(by rw [hargs]; omega)) ((doms[k].instL ls).instOuter (args.take k))) := by
  obtain ⟨A⟩ := c.projectionAlignment hfind habstract hsingle hci hinduct
  have hciMap : c.env.constants.find? mkC = some (.ctorInfo mkInfo) := by
    rwa [← c.trenv.map_wf.find?'_eq_find?]
  have hcEq : A.constructorInfo = mkInfo := by
    have := A.constructor_lookup
    rw [hciMap] at this
    cases this
    rfl
  obtain ⟨decl, type, ctor, htype, hctorMem, hname, hctorUvars, huvars, hnparams, hindices,
    hlevel, hctorName, hctorType, hlookup, hwf, ⟨params, Hshape, Hparams⟩, Hraw, hnodup⟩ :=
    c.Ewf.ordered.projectionShape A.projection
  obtain ⟨doms, result, hshape, hle, hvalid, hhead, harity⟩ := Hraw.forallArity
  have hfam := A.family_lookup
  rw [hlookup] at hfam
  have hfam' := Option.some.inj hfam
  have htUvars : type.uvars = A.info.uvars := congrArg VConstant.uvars hfam'
  have htType : type.type = A.familyType := congrArg VConstant.type hfam'
  have hNumFields : mkInfo.numFields = doms.length - A.info.nparams := by
    rw [← hcEq, A.constructor_numFields, VProjectionInfo.numFields, ← hctorType, harity]
  -- the normalized shape of the type constant
  obtain ⟨normalized, ownParams, afterParams, indices, result', exprType, hnorm, hown, hidx,
    HownP, hres⟩ := Hshape
  obtain ⟨ctorParams, tail, hctorParams, HctorP⟩ := Hparams
  have hownLen : ownParams.length = decl.nparams := VExpr.takeForalls_domains_length hown
  have hidxLen : indices.length = type.numIndices := VExpr.takeForalls_domains_length hidx
  have hnormEq : normalized = VExpr.wrapForalls (ownParams ++ indices) result' := by
    rw [VExpr.eq_wrapForalls_of_takeForalls hown, VExpr.eq_wrapForalls_of_takeForalls hidx,
      VExpr.wrapForalls_append]
  have hctorParamsEq : ctorParams = doms.take decl.nparams := by
    have h1 := VExpr.takeForalls_wrapForalls_append (doms.take decl.nparams)
      (doms.drop decl.nparams) result
    rw [List.take_append_drop, show (doms.take decl.nparams).length = decl.nparams by
      simp; omega] at h1
    have h2 := hctorParams
    rw [hshape] at h2
    exact (Prod.mk.inj (Option.some.inj (h2.symm.trans h1))).1
  have hctx : c.venv.IsDefEqCtx decl.uvars [] ownParams.reverse ctorParams.reverse :=
    VEnv.IsDefEqCtx.trans_empty c.Ewf (HownP.symm c.Ewf.orderedStrong) HctorP
  -- the type constant's type is a type, hence so is its normalized telescope
  have htypeWF : c.venv.IsType decl.uvars [] type.type := by
    have := c.Ewf.ordered.constWF hlookup
    change c.venv.IsType type.uvars [] type.type at this
    rwa [htUvars, ← huvars] at this
  have hnormWF : c.venv.IsType decl.uvars [] normalized :=
    let ⟨u, h⟩ := htypeWF; ⟨u, h.defeqU_l c.Ewf (by trivial) ⟨_, hnorm⟩⟩
  rw [hnormEq] at hnormWF
  have hΓtel := (VEnv.IsType.wrapForalls_inv c.Ewf (by trivial) hnormWF).1
  simp only [List.append_nil] at hΓtel
  -- the typing of a well-formed application of the type constant along its telescope
  have spine : ∀ (ls : List VLevel) (args : List VExpr), ls.length = A.info.uvars →
      args.length = A.info.nparams + A.info.nindices →
      (∃ u, c.HasType (VExpr.mkApps (.const n ls) args) (.sort u)) →
      (∀ l ∈ ls, l.WF c.lparams.length) ∧
      (∀ j (hj : j < args.length) (hj' : j < ((ownParams ++ indices).map (VExpr.instL ls)).length),
        c.HasType args[j] (((ownParams ++ indices).map (VExpr.instL ls))[j].instOuter
          (args.take j))) ∧
      c.HasType (VExpr.mkApps (.const n ls) args) ((result'.instL ls).instOuter args) := by
    intro ls args hls hargs ⟨u, hsort⟩
    have hwfApp : VExpr.WF c.venv c.lparams.length c.vlctx.toCtx
        (VExpr.mkApps (.const n ls) args) := ⟨_, hsort⟩
    have ⟨_, hcw⟩ := VExpr.WF.of_mkApps c.Ewf.orderedStrong c.Δwf.toCtx hwfApp
    have ⟨ci', hci', hlsw, hlen'⟩ := VEnv.HasType.const_inv c.Ewf.orderedStrong c.Δwf.toCtx hcw
    have hc := VEnv.HasType.const (Γ := c.vlctx.toCtx) hlookup hlsw (by
      rw [hlookup] at hci'; cases hci'; exact hlen')
    have hdef : c.IsDefEqU (type.toVConstant.type.instL ls) (normalized.instL ls) := by
      have := (hnorm.instL hlsw).weak0 c.Ewf.orderedStrong (Γ := c.vlctx.toCtx)
      exact ⟨_, this⟩
    have hc' := hc.defeqU_r c.Ewf c.Δwf hdef
    rw [hnormEq, VExpr.instL_wrapForalls] at hc'
    have ⟨hargsT, hresT⟩ := VEnv.HasType.mkApps_wrapForalls c.Ewf c.Δwf.toCtx hc' hwfApp
      (by simp [hargs, hownLen, hidxLen, hnparams, hindices])
    exact ⟨hlsw, hargsT, hresT⟩
  refine ⟨A.info, A.projection, A.ctorName, decl, doms, result, ?_, ?_, ?_, ?_, ?_, hnparams,
    huvars, ?_, ?_, hNumFields, ?_, A.nparams, A.nindices, ?_, ⟨_, A.family_lookup⟩, ?_, ?_⟩
  · rw [← huvars, ← hctorType]; exact hwf
  · rw [A.ctorName]; exact A.constructor_abstract
  · rw [← hctorType, hshape]
  · rw [← hname]; exact hvalid
  · rw [← hname]; exact hhead
  · rw [← hnparams]; exact hle
  · rw [← hcEq, A.constructor_numParams, A.nparams]
  · rw [← hcEq, A.constructor_numFields]
  · intro type' htype' hname'
    have : type' = type := by
      have hnodup' : (decl.types.map fun t => t.toVConstVal.name).Nodup := by
        have := hnodup
        simp only [VInductDecl.sourceNames, VInductDecl.typeConstants, List.map_map] at this
        exact (List.nodup_append.1 this).1
      exact List.eq_of_mem_of_nodup_map hnodup' htype' htype (by
        show type'.name = type.name
        rw [hname', hname])
    rw [this, hindices]
  · intro ls args hls hargs hsort
    have ⟨hlsw, hargsT, hresT⟩ := spine ls args hls hargs hsort
    have hΔ₀ : OnCtx (indices.reverse ++ ownParams.reverse) (c.venv.IsType decl.uvars) := by
      rwa [List.reverse_append] at hΓtel
    have e : (indices.reverse ++ ownParams.reverse).reverse = ownParams ++ indices := by simp
    have hconv := VEnv.IsDefEqU.closed_telescope_instOuter c.Ewf hΔ₀ ⟨_, hres⟩ hlsw
      (args := args) (by simp [hargs, hownLen, hidxLen, hnparams, hindices]; omega) (by
        intro k hk hk'
        simp only [e] at hk' ⊢
        exact hargsT k hk hk')
    rw [VExpr.instL, VExpr.instOuter_sort, hlevel] at hconv
    exact hresT.defeqU_r c.Ewf c.Δwf hconv
  · intro ls args hls hargs hsort k hk hk'
    obtain ⟨hlsw, hargsT, -⟩ := spine ls args hls hargs hsort
    have hk1 : k < args.length := by omega
    have hkown : k < ownParams.length := by omega
    have hkctor : k < ctorParams.length := by rw [hctorParamsEq]; simp; omega
    have ⟨u, hdk⟩ := hctx.reverse_getElem k hkown hkctor
    have hΔ₀ : OnCtx (ownParams.take k).reverse (c.venv.IsType decl.uvars) := by
      have : (ownParams ++ indices).reverse =
          (indices.reverse ++ (ownParams.drop k).reverse) ++ (ownParams.take k).reverse := by
        rw [List.append_assoc, ← List.reverse_append, List.take_append_drop, List.reverse_append]
      rw [this] at hΓtel
      exact hΓtel.of_append
    have hconv := VEnv.IsDefEqU.closed_telescope_instOuter c.Ewf hΔ₀ ⟨_, hdk⟩ hlsw
      (args := args.take k) (by simp; omega) (by
        intro j hj hj'
        simp only [List.length_take] at hj
        have := hargsT j (by omega) (by simp; omega)
        simp only [List.reverse_reverse, List.getElem_map, List.getElem_take, List.take_take,
          Nat.min_eq_left (Nat.le_of_lt (show j < k by omega))] at this ⊢
        rw [List.getElem_append_left (by omega)] at this
        exact this)
    have hargk := hargsT k hk1 (by simp; omega)
    rw [List.getElem_map, List.getElem_append_left (by omega)] at hargk
    have hdoms : ctorParams[k] = doms[k] := by
      simp only [hctorParamsEq, List.getElem_take]
    rw [hdoms] at hconv
    exact hargk.defeqU_r c.Ewf c.Δwf hconv

class VContext.MLCWF (c : VContext) (m : MLCtx) : Prop where
  wf : m.WF c.venv c.lparams

instance (c : VContext) : c.MLCWF c.mlctx := ⟨c.mlctx_wf⟩

def _root_.Lean4Lean.InferCache.WF (c : VContext) (s : State) (m : InferCache) : Prop :=
  ∀ ⦃e ty : Expr⦄, m[e]? = some ty → ConditionallyHasType s.ngen c.venv c.lparams c.vlctx e ty

theorem _root_.Lean4Lean.InferCache.WF.empty : InferCache.WF c s {} := fun _ => by simp

def WHNFCache.WF (c : VContext) (s : State) (m : InferCache) : Prop :=
  ∀ ⦃e ty : Expr⦄, m[e]? = some ty → ConditionallyWHNF s.ngen c.venv c.lparams c.vlctx e ty

theorem WHNFCache.WF.empty : WHNFCache.WF c s {} := fun _ => by simp

def UnfoldCache.WF (c : VContext) (m : ExprMap Expr) : Prop :=
  ∀ ⦃e e' : Expr⦄, m[e]? = some e' → ∃ n ls ci, e = .const n ls ∧
      c.env.find? n = some ci ∧ e' = Inner.instantiateDeltaValue ci ls

/-- The declarations of the up-set `P` of the local context mention only the universe
parameters `Us`: both their types and, for let-declarations, their values. These are read off the
concrete local context. -/
def VContext.UniverseScope (c : VContext) (Us : List Name) (P : FVarId → Prop) : Prop :=
  IsFVarUpSet P c.vlctx ∧ ∀ fv decl, P fv → c.lctx'.find? fv = some decl →
    decl.type.levelParamsIn Us = true ∧
    ∀ v, decl.value? true = some v → v.levelParamsIn Us = true

/-- `e₁` mentions only the universe parameters `Us` whenever `e` does and all free variables of
`e` lie in a universe scope `P` of the context. This is the universe-parameter analogue of
`FVarsBelow`. -/
def VContext.LevelsBelow (c : VContext) (e e₁ : Expr) : Prop :=
  ∀ Us P, c.UniverseScope Us P → e.levelParamsIn Us = true → FVarsIn P e →
    e₁.levelParamsIn Us = true

/-- The universe-support invariant of a cache whose values are computed from their keys (the
`whnfCore`, `whnf` and `inferType` caches): conditional on the key living in the current context,
the value stays in every universe scope the key does. -/
def LevelsCache.WF (c : VContext) (m : InferCache) : Prop :=
  ∀ ⦃e e₁ : Expr⦄, m[e]? = some e₁ → FVarsIn (· ∈ c.vlctx.fvars) e → c.LevelsBelow e e₁

theorem LevelsCache.WF.empty : LevelsCache.WF c {} := fun _ => by simp

/-! ### The parameter-uniformity invariant

The nested-inductive restoration needs every checker output computed from a parameter-uniform term
(`Expr.ParamUniformIn`: every occurrence of a head constant is applied to the fixed parameter fvars
`As` at the levels `ls`, and every projection avoids the heads) to be parameter-uniform again. The
invariant below mirrors the universe-support invariant (`VContext.LevelsBelow`): it is conditional on
a *parameter-uniform scope*, an up-set `P` of the local context whose declarations are
parameter-uniform, together with the environment condition
`EnvParamUniform`. The parameter fvars must never be generated by the checker's name generator (whose
prefix is `pfx`), so that the binders the checker opens and closes again are never parameters. -/

/-- The parameter fvars `As` are free variables that the checker's name generator (prefix `pfx`)
never produces. -/
def UngeneratedParams (pfx : Name) (As : List Expr) : Prop :=
  ∀ a ∈ As, ∃ fv, a = .fvar fv ∧ ∀ i, fv ≠ ⟨.num pfx i⟩

theorem UngeneratedParams.fvars (H : UngeneratedParams pfx As) : ∀ a ∈ As, ∃ fv, a = .fvar fv :=
  fun a h => let ⟨fv, h1, _⟩ := H a h; ⟨fv, h1⟩

/-- A parameter-uniform scope: the environment condition, parameters that are never generated,
and an up-set `P` of the local context whose declarations (types and let-values) are
parameter-uniform. -/
structure ParamUniformScopeAt (E : Environment) (Δ : VLCtx) (lctx : LocalContext) (pfx : Name)
    (heads : List Name) (As : List Expr) (ls : List Level) (P : FVarId → Prop) : Prop where
  env : EnvParamUniform E heads As.length ls
  params : UngeneratedParams pfx As
  up : IsFVarUpSet P Δ
  decls : ∀ fv decl, P fv → lctx.find? fv = some decl →
    decl.type.ParamUniformIn E heads As ls ∧ ∀ v, decl.value? true = some v → v.ParamUniformIn E heads As ls

/-- A translated string literal means the environment supports string literals. -/
theorem VContext.strLitsDeclared (c : VContext) (h : c.venv.ContainsLits (.strVal str)) :
    StrLitsDeclared c.env :=
  let ⟨_, h1, _⟩ := c.trenv.find?_iff.2 h.1
  let ⟨_, h2, _⟩ := c.trenv.find?_iff.2 h.2
  ⟨⟨_, h1⟩, ⟨_, h2⟩⟩

/-- `ParamUniformScopeAt` at the environment and local context of `c`. -/
abbrev VContext.ParamUniformScope (c : VContext) (pfx : Name) (heads : List Name) (As : List Expr)
    (ls : List Level) (P : FVarId → Prop) : Prop :=
  ParamUniformScopeAt c.env c.vlctx c.lctx' pfx heads As ls P

/-- `e₁` is parameter-uniform whenever `e` is and the free variables of `e` lie in a
parameter-uniform scope. This is the analogue of `FVarsBelow` and `LevelsBelow`. -/
def VContext.ParamUniformBelow (c : VContext) (pfx : Name) (e e₁ : Expr) : Prop :=
  ∀ heads As ls P, c.ParamUniformScope pfx heads As ls P → e.ParamUniformIn c.env heads As ls → FVarsIn P e →
    e₁.ParamUniformIn c.env heads As ls

/-- The parameter-uniformity clause of type inference: `ParamUniformBelow`, and in addition the
type of a bare head constant at the levels `ls` is its parameter telescope (needed for inferring
the type of a head application from the type of its head). -/
def VContext.ParamUniformTyBelow (c : VContext) (pfx : Name) (e ty : Expr) : Prop :=
  c.ParamUniformBelow pfx e ty ∧ ∀ heads As ls P, c.ParamUniformScope pfx heads As ls P → ∀ n ∈ heads,
    e = .const n ls → HeadType heads As.length ls ty ∧ ty.ProjsOK (projAvoidsHeads c.env heads)

/-- The parameter-uniformity invariant of the `whnfCore` and `whnf` caches. -/
def ParamUniformCache.WF (c : VContext) (pfx : Name) (m : InferCache) : Prop :=
  ∀ ⦃e e₁ : Expr⦄, m[e]? = some e₁ → FVarsIn (· ∈ c.vlctx.fvars) e → c.ParamUniformBelow pfx e e₁

/-- The parameter-uniformity invariant of the `inferOnly := true` type cache. -/
def ParamUniformTyCache.WF (c : VContext) (pfx : Name) (m : InferCache) : Prop :=
  ∀ ⦃e e₁ : Expr⦄, m[e]? = some e₁ → FVarsIn (· ∈ c.vlctx.fvars) e → c.ParamUniformTyBelow pfx e e₁

theorem ParamUniformCache.WF.empty : ParamUniformCache.WF c pfx {} := fun _ => by simp
theorem ParamUniformTyCache.WF.empty : ParamUniformTyCache.WF c pfx {} := fun _ => by simp

/-- The context `Δ'` in which the facts of the equivalence manager hold: the current context, or,
since the manager keeps facts found under closed binders, which may mention their variables, an
extension of the current context by such variables, all reserved by the name generator. Moving
such a fact to the current context uses strengthening (`VContext.strengthening`). -/
def EqvScope (c : VContext) (ngen : NameGenerator) (Δ' : VLCtx) : Prop :=
  Δ' = c.vlctx ∨ c.venv.Strengthening ∧ Δ'.WF c.venv c.lparams.length ∧
    (∃ l, c.vlctx.FVLift' Δ' 0 l 0) ∧ ∀ fv ∈ Δ'.fvars, ngen.Reserves fv

theorem EqvScope.mono {c : VContext} (le : ngen ≤ ngen') :
    EqvScope c ngen Δ' → EqvScope c ngen' Δ'
  | .inl h => .inl h
  | .inr ⟨h1, h2, h3, h4⟩ => .inr ⟨h1, h2, h3, fun fv h => (h4 fv h).mono le⟩

class State.WF (c : VContext) (s : State) where
  trctx : c.TrLCtx
  ngen_wf : ∀ fv ∈ c.vlctx.fvars, s.ngen.Reserves fv
  /-- Every equivalence the manager records holds in the context `Δ'` of `EqvScope`: the current
  one, or an extension of it by variables of closed binders. -/
  ectx : ∃ Δ', EqvScope c s.ngen Δ' ∧ s.eqvManager.WF c.venv c.lparams Δ'
  inferTypeI_wf : s.inferTypeI.WF c s
  inferTypeC_wf : s.inferTypeC.WF c s
  whnfCore_wf : WHNFCache.WF c s s.whnfCoreCache
  whnf_wf : WHNFCache.WF c s s.whnfCache
  unfold_wf : UnfoldCache.WF c s.unfold
  inferTypeI_levels : LevelsCache.WF c s.inferTypeI
  inferTypeC_levels : LevelsCache.WF c s.inferTypeC
  whnfCore_levels : LevelsCache.WF c s.whnfCoreCache
  whnf_levels : LevelsCache.WF c s.whnfCache
  whnfCore_paramUniform : ParamUniformCache.WF c s.ngen.namePrefix s.whnfCoreCache
  whnf_paramUniform : ParamUniformCache.WF c s.ngen.namePrefix s.whnfCache
  inferTypeI_paramUniform : ParamUniformTyCache.WF c s.ngen.namePrefix s.inferTypeI

theorem State.WF.find?_eq_none {id}
    (wf : State.WF c s) (H : ¬s.ngen.Reserves id) : c.lctx'.find? id = none :=
  wf.trctx.find?_eq_none.2 fun h => H (wf.ngen_wf _ h)

def State.LE (s₁ s₂ : State) : Prop :=
  s₁.ngen ≤ s₂.ngen

instance : LE State := ⟨State.LE⟩

theorem State.LE.rfl {s : State} : s ≤ s := NameGenerator.LE.rfl

theorem State.LE.trans {s₁ s₂ s₃ : State} (h₁ : s₁ ≤ s₂) (h₂ : s₂ ≤ s₃) : s₁ ≤ s₃ :=
  NameGenerator.LE.trans h₁ h₂

theorem State.LE.reservesV {s₁ s₂ : State} (h : s₁ ≤ s₂) {{fv}} :
    s₁.ngen.Reserves fv → s₂.ngen.Reserves fv :=
  (·.mono h)

theorem State.LE.reserves {s₁ s₂ : State} (h : s₁ ≤ s₂) {{e}} :
    FVarsIn s₁.ngen.Reserves e → FVarsIn s₂.ngen.Reserves e :=
  (·.mono h.reservesV)

/-- A definitional equality found in the current context is a fact of the equivalence manager's
context. -/
theorem State.WF.eqv_defeq {c : VContext} {s : State}
    (hΔ' : EqvScope c s.ngen Δ') (he₁ : c.TrExprS e₁ e') (he₂ : c.TrExpr e₂ e') :
    EquivManager.IsDefEqE c.venv c.lparams Δ' e₁ e₂ := by
  rcases hΔ' with rfl | ⟨-, hwf, ⟨l, W⟩, -⟩
  · exact .defeq he₁ he₂
  · exact .defeq (he₁.weakFV' c.Ewf.orderedStrong W hwf) (he₂.weakFV' c.Ewf W hwf)

nonrec theorem _root_.Lean4Lean.VLocalDecl.WF.weak' {env : VEnv} (henv : env.Ordered)
    (W : Ctx.Lift' l Γ Γ') : ∀ {d}, VLocalDecl.WF env U Γ d → VLocalDecl.WF env U Γ' (d.lift' l)
  | .vlam _, H => H.weak' henv W
  | .vlet .., H => H.weak' henv W

def M.WF (c : VContext) (vs : State) (x : M α) (Q : α → State → Prop) : Prop :=
  vs.WF c → ∀ a s', x c.toContext vs = .ok (a, s') →
    ∃ vs', vs' = s' ∧ vs ≤ vs' ∧ vs'.WF c ∧ Q a vs'

theorem M.WF.bind {c : VContext} {s : State} {x : M α} {f : α → M β} {Q R}
    (h1 : x.WF c s Q)
    (h2 : ∀ a s', s ≤ s' → Q a s' → (f a).WF c s' R) :
    (x >>= f).WF c s R := by
  intro wf₁ a vs₁
  simp [(· >>= ·), ReaderT.bind, StateT.bind, Except.bind]
  split; · simp
  intro h; rename_i v eq
  obtain ⟨vs₂, eq1, le1, wf₂, h1⟩ := h1 wf₁ _ _ eq
  obtain ⟨vs₃, rfl, le2, wf₃, h2⟩ := h2 _ _ le1 h1 wf₂ _ _ (eq1 ▸ h)
  exact ⟨le1.trans le2, wf₃, h2⟩

theorem M.WF.pure {c : VContext} {s : State} {Q} (H : Q a s) :
    (pure a : M α).WF c s Q := by rintro h _ _ ⟨⟩; exact ⟨_, rfl, .rfl, h, H⟩

theorem M.WF.map {c : VContext} {s : State} {x : M α} {f : α → β} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s ≤ s' → Q a s' → R (f a) s') : (f <$> x).WF c s R := by
  rw [map_eq_pure_bind]
  exact h1.bind fun _ _ le h => .pure (h2 _ _ le h)

theorem M.WF.mono {c : VContext} {s : State} {x : M α} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s ≤ s' → Q a s' → R a s') : x.WF c s R := by
  simpa using h1.bind fun _ _ a1 a2 => .pure (h2 _ _ a1 a2)

theorem M.WF.throw {c : VContext} {s : State} {Q} : (throw e : M α).WF c s Q := nofun

theorem M.WF.and {c : VContext} {s : State} {x : M α} {Q R}
    (h1 : x.WF c s Q) (h2 : x.WF c s R) : x.WF c s fun a s => Q a s ∧ R a s := by
  refine fun wf a s' e => ?_
  have H1 := h1 wf a s' e
  have H2 := h2 wf a s' e
  obtain ⟨s₁, rfl, h2', h3, h4⟩ := H1
  obtain ⟨s₂, eq, -, -, h4'⟩ := H2
  cases eq
  exact ⟨_, rfl, h2', h3, h4, h4'⟩

theorem M.WF.le {c : VContext} {s : State} {Q R} {x : M α}
    (h1 : x.WF c s Q) (H : ∀ a s', s ≤ s' → Q a s' → R a s') :
    x.WF c s R := fun wf _ _ e =>
  let ⟨_, a1, a2, a3, a4⟩ := h1 wf _ _ e
  ⟨_, a1, a2, a3, H _ _ a2 a4⟩

structure Methods.WF (m : Methods) where
  isDefEqCore : c.TrExprS e₁ e₁' → c.TrExprS e₂ e₂' →
    (m.isDefEqCore e₁ e₂).WF c s fun b _ => b → c.IsDefEqU e₁' e₂'
  whnfCore : c.TrExprS e e' →
    (m.whnfCore e cheapProj).WF c s fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e'
  whnf : c.TrExprS e e' →
    (m.whnf e).WF c s fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e'
  /-- An input translating to a `forallE` is returned (up to `mdata` and let bindings). -/
  whnfCore_forallE : c.TrExprS e (.forallE A B) →
    (m.whnfCore e cheapProj).WF c s fun e₁ _ => c.TrExprS e₁ (.forallE A B)
  whnf_forallE : c.TrExprS e (.forallE A B) →
    (m.whnf e).WF c s fun e₁ _ => c.TrExprS e₁ (.forallE A B)
  inferType : e.FVarsIn (· ∈ c.vlctx.fvars) →
    (inferOnly = true → ∃ e', c.TrExprS e e') →
    (m.inferType e inferOnly).WF c s fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty'
  /-- `whnfCore` stays in every universe scope of its input. -/
  whnfCore_levels : c.TrExprS e e' →
    (m.whnfCore e cheapProj).WF c s fun e₁ _ => c.LevelsBelow e e₁
  /-- `whnf` stays in every universe scope of its input. -/
  whnf_levels : c.TrExprS e e' →
    (m.whnf e).WF c s fun e₁ _ => c.LevelsBelow e e₁
  /-- The inferred type stays in every universe scope of the input, in both modes. -/
  inferType_levels : e.FVarsIn (· ∈ c.vlctx.fvars) →
    (inferOnly = true → ∃ e', c.TrExprS e e') →
    (m.inferType e inferOnly).WF c s fun ty _ => c.LevelsBelow e ty
  /-- `whnfCore` preserves parameter uniformity. -/
  whnfCore_paramUniform : c.TrExprS e e' →
    (m.whnfCore e cheapProj).WF c s fun e₁ _ => c.ParamUniformBelow s.ngen.namePrefix e e₁
  /-- `whnf` preserves parameter uniformity. -/
  whnf_paramUniform : c.TrExprS e e' →
    (m.whnf e).WF c s fun e₁ _ => c.ParamUniformBelow s.ngen.namePrefix e e₁
  /-- Type inference (`inferOnly := true`) preserves parameter uniformity. -/
  inferType_paramUniform : c.TrExprS e e' →
    (m.inferType e true).WF c s fun ty _ => c.ParamUniformTyBelow s.ngen.namePrefix e ty
  /-- `whnfCore` returns a constant unchanged. -/
  whnfCore_const : (m.whnfCore (.const n us) cheapProj).WF c s fun e₁ _ => e₁ = .const n us
  /-- `whnf` returns a forall unchanged. -/
  whnf_forall_eq :
    (m.whnf (.forallE n t b bi)).WF c s fun e₁ _ => e₁ = .forallE n t b bi

def RecM.WF (c : VContext) (s : State) (x : RecM α) (Q : α → State → Prop) : Prop :=
  ∀ m, m.WF → M.WF c s (x m) Q

theorem M.WF.liftExcept {c : VContext} {s : State} {x : Except Exception α} {Q} (h : x.WF Q) :
    M.WF c s (liftM x) fun a _ => Q a := by
  rintro wf _ _ eq
  cases x <;> cases eq
  exact ⟨s, rfl, .rfl, wf, h _ rfl⟩

theorem M.WF.lift {c : VContext} {s : State} {x : M α} {Q} (h : x.WF c s Q) :
    RecM.WF c s x Q := fun _ _ => h

instance : Coe (M.WF c s x Q) (RecM.WF c s x Q) := ⟨M.WF.lift⟩

theorem RecM.WF.bind {c : VContext} {s : State} {x : RecM α} {f : α → RecM β} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s ≤ s' → Q a s' → (f a).WF c s' R) : (x >>= f).WF c s R :=
  fun _ h => M.WF.bind (h1 _ h) fun _ _ h1' h2' => h2 _ _ h1' h2' _ h

theorem RecM.WF.bind_le {c : VContext} {s : State} {x : RecM α} {f : α → RecM β} {Q R}
    (h1 : x.WF c s Q) (hs : s₀ ≤ s)
    (h2 : ∀ a s', s₀ ≤ s' → Q a s' → (f a).WF c s' R) : (x >>= f).WF c s R :=
  RecM.WF.bind h1 fun _ _ h => h2 _ _ (hs.trans h)

theorem RecM.WF.pure {c : VContext} {s : State} {Q} (H : Q a s) : (pure a : RecM α).WF c s Q :=
  fun _ _ => .pure H

theorem RecM.WF.and {c : VContext} {s : State} {x : RecM α} {Q R}
    (h1 : x.WF c s Q) (h2 : x.WF c s R) : x.WF c s fun a s => Q a s ∧ R a s :=
  fun m wf => (h1 m wf).and (h2 m wf)

/-- Combine a family of postconditions, each established under its own hypothesis, with an
unconditional one (which supplies the state invariant when no hypothesis holds). -/
theorem RecM.WF.and_forall {c : VContext} {s : State} {x : RecM α} {Q : α → State → Prop}
    {H : ι → Prop} {R : ι → α → Prop}
    (h0 : x.WF c s Q) (h : ∀ i, H i → x.WF c s fun a _ => R i a) :
    x.WF c s fun a s => Q a s ∧ ∀ i, H i → R i a := by
  intro m mwf wf a s' e
  obtain ⟨⟨vs⟩, rfl, le, wf', q⟩ := h0 m mwf wf a s' e
  refine ⟨_, rfl, le, wf', q, fun i hi => ?_⟩
  obtain ⟨⟨vs''⟩, eq, -, -, r⟩ := h i hi m mwf wf a _ e
  cases eq; exact r

theorem RecM.WF.map {c : VContext} {s : State} {x : RecM α} {f : α → β} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s ≤ s' → Q a s' → R (f a) s') : (f <$> x).WF c s R := by
  rw [map_eq_pure_bind]
  exact h1.bind fun _ _ le h => .pure (h2 _ _ le h)

theorem RecM.WF.mono {c : VContext} {s : State} {x : RecM α} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s ≤ s' → Q a s' → R a s') : x.WF c s R := by
  rw [← id_map x]; exact h1.map h2

theorem RecM.WF.throw {c : VContext} {s : State} {Q} : (throw e : RecM α).WF c s Q := nofun

theorem RecM.WF.le {c : VContext} {s : State} {Q R} {x : RecM α}
    (h1 : x.WF c s Q) (H : ∀ a s', s ≤ s' → Q a s' → R a s') :
    x.WF c s R := fun _ h => (h1 _ h).le H

theorem RecM.WF.pureBind {c : VContext} {s : State} {f : β → RecM α} {Q}
    {x : β} (H : WF c s (f x) Q) : ((Pure.pure x : RecM β) >>= f).WF c s Q := H

theorem get.WF {c : VContext} {s : State} :
    M.WF c s get fun a s' => s = a ∧ s = s' := by
  rintro wf _ _ ⟨⟩; exact ⟨_, rfl, .rfl, wf, rfl, rfl⟩

theorem RecM.WF.get {c : VContext} {s : State} {f : State → RecM α} {Q}
    (H : WF c s (f s) Q) : (get >>= f).WF c s Q := H

theorem getEnv.WF {c : VContext} {s : State} :
    M.WF c s getEnv fun a s' => c.env = a ∧ s = s' := by
  rintro wf _ _ ⟨⟩; exact ⟨_, rfl, .rfl, wf, rfl, rfl⟩

theorem M.WF.getEnv {c : VContext} {s : State} {f : Environment → M α} {Q}
    (H : WF c s (f c.env) Q) : (liftM getEnv >>= f).WF c s Q := H

theorem RecM.WF.getEnv {c : VContext} {s : State} {f : Environment → RecM α} {Q}
    (H : WF c s (f c.env) Q) : (liftM getEnv >>= f).WF c s Q := H

theorem getLCtx.WF {c : VContext} {s : State} :
    M.WF c s getLCtx fun a s' => c.lctx' = a ∧ s = s' := by
  rintro wf _ _ ⟨⟩; exact ⟨_, rfl, .rfl, wf, c.lctx_eq, rfl⟩

theorem RecM.WF.getLCtx {c : VContext} {s : State} {f : LocalContext → RecM α} {Q}
    (H : WF c s (f c.lctx') Q) : (getLCtx >>= f).WF c s Q :=
  getLCtx.WF.lift.bind <| by rintro _ _ _ ⟨rfl, rfl⟩; exact H

theorem RecM.WF.readThe {c : VContext} {s : State} {f : Context → RecM α} {Q}
    (H : WF c s (f c.toContext) Q) : (readThe Context >>= f).WF c s Q := H

theorem getNGen.WF {c : VContext} {s : State} :
    M.WF c s getNGen fun a s' => s.ngen = a ∧ s = s' := by
  rintro wf _ _ ⟨⟩; exact ⟨_, rfl, .rfl, wf, rfl, rfl⟩

theorem M.WF.getNGen {c : VContext} {s : State} {f : NameGenerator → M α} {Q}
    (H : WF c s (f s.ngen) Q) : (getNGen >>= f).WF c s Q := H

theorem RecM.WF.getNGen {c : VContext} {s : State} {f : NameGenerator → RecM α} {Q}
    (H : WF c s (f s.ngen) Q) : (getNGen >>= f).WF c s Q := H

theorem RecM.WF.stateWF {c : VContext} {s : State} {x : RecM α} {Q}
    (H : s.WF c → WF c s x Q) : WF c s x Q :=
  fun _ h wf => H wf _ h wf

/-- A postcondition on the result of a successful run from a well-formed state (with well-formed
methods), without the state invariant at the end of the run. Unlike `RecM.WF`, this can be
established for a run whose tail is not known to preserve the state invariant, as long as the
result is already determined. -/
def RecM.Post (c : VContext) (s : State) (x : RecM α) (Q : α → Prop) : Prop :=
  ∀ m, m.WF → s.WF c → ∀ a s', x m c.toContext s = .ok (a, s') → Q a

/-- A postcondition on the result of every successful run, for all methods and states. -/
def RecM.Res (x : RecM α) (Q : α → Prop) : Prop :=
  ∀ m ctx st a st', x m ctx st = .ok (a, st') → Q a

theorem RecM.Res.post {c : VContext} {s : State} {x : RecM α} {Q : α → Prop}
    (H : x.Res Q) : x.Post c s Q := fun m _ _ a s' e => H m _ _ a s' e

theorem RecM.Post.bind {c : VContext} {s : State} {x : RecM α} {f : α → RecM β} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s ≤ s' → Q a s' → (f a).Post c s' R) :
    (x >>= f).Post c s R := by
  intro m mwf wf₁ a vs₁
  simp [(· >>= ·), ReaderT.bind, StateT.bind, Except.bind]
  split; · simp
  intro h; rename_i v eq
  obtain ⟨vs₂, eq1, le1, wf₂, h1⟩ := h1 m mwf wf₁ _ _ eq
  exact h2 _ _ le1 h1 m mwf wf₂ _ _ (eq1 ▸ h)

theorem RecM.Res.bind {x : RecM α} {f : α → RecM β} {Q} (h2 : ∀ a, (f a).Res Q) :
    (x >>= f).Res Q := by
  intro m ctx st a st'
  simp [(· >>= ·), ReaderT.bind, StateT.bind, Except.bind]
  split; · simp
  intro h; exact h2 _ m ctx _ a st' h

theorem RecM.Res.pure {Q : α → Prop} (h : Q a) : (pure a : RecM α).Res Q := by
  rintro _ _ _ _ _ ⟨⟩; exact h

theorem RecM.Post.pure {c : VContext} {s : State} {Q : α → Prop} (h : Q a) :
    (pure a : RecM α).Post c s Q := (RecM.Res.pure h).post

theorem RecM.WF.and_post {c : VContext} {s : State} {x : RecM α} {Q R}
    (h1 : x.WF c s Q) (h2 : x.Post c s R) : x.WF c s fun a s => Q a s ∧ R a := by
  intro m mwf wf a s' e
  obtain ⟨vs, h3, le, wf', q⟩ := h1 m mwf wf a s' e
  exact ⟨vs, h3, le, wf', q, h2 m mwf wf a s' e⟩

@[simp] theorem toLBool_true {b : Bool} : b.toLBool = .true ↔ b = true := by
  cases b <;> simp [Bool.toLBool]

theorem RecM.WF.toLBoolM {Q : State → Prop} {x : RecM Bool}
    (H : x.WF c s fun b s => b → Q s) : (toLBoolM x).WF c s fun b s => b = .true → Q s :=
  H.bind fun _ _ _ H => .pure fun h => H (by simpa using h)

def VContext.withMLC (c : VContext) (m : MLCtx) [wf : c.MLCWF m] : VContext :=
  { c with
    mlctx := m
    mlctx_wf := wf.1
    lctx := m.lctx
    lctx_eq := rfl }

@[simp] theorem VContext.withMLC_self (c : VContext) : c.withMLC c.mlctx = c := by
  simp [withMLC, c.lctx_eq]

/-- `withMLC` only moves the local context; the ambient environment and universe parameters are
untouched, so judgements stated at `c` and at `c.withMLC m` are interchangeable. -/
@[simp] theorem VContext.withMLC_venv (c : VContext) (m) [c.MLCWF m] :
    (c.withMLC m).venv = c.venv := rfl
@[simp] theorem VContext.withMLC_lparams (c : VContext) (m) [c.MLCWF m] :
    (c.withMLC m).lparams = c.lparams := rfl
@[simp] theorem VContext.withMLC_mlctx (c : VContext) (m) [c.MLCWF m] :
    (c.withMLC m).mlctx = m := rfl

theorem MLCtx.WF.find?_vlam {m : MLCtx} (wf : (m.vlam x name ty ty' bi).WF env Us)
    (h : fv ≠ x) : (m.vlam x name ty ty' bi).lctx.find? fv = m.lctx.find? fv := by
  rw [wf.find?_eq, wf.1.find?_eq]; simp [decls, LocalDecl.fvarId, h]

theorem MLCtx.WF.find?_vlet {m : MLCtx} (wf : (m.vlet x name ty v ty' v').WF env Us)
    (h : fv ≠ x) : (m.vlet x name ty v ty' v').lctx.find? fv = m.lctx.find? fv := by
  rw [wf.find?_eq, wf.1.find?_eq]; simp [decls, LocalDecl.fvarId, h]

@[simp] theorem _root_.Lean.LocalDecl.value?_ldecl_true :
    (LocalDecl.ldecl i fv n t v nd k).value? true = some v := by
  cases nd <;> rfl

theorem MLCtx.WF.find?_vlam_self {m : MLCtx} (wf : (m.vlam x name ty ty' bi).WF env Us) :
    (m.vlam x name ty ty' bi).lctx.find? x = some (.cdecl m.length x name ty bi .default) := by
  rw [wf.find?_eq]; simp [decls, LocalDecl.fvarId]

theorem MLCtx.WF.find?_vlet_self {m : MLCtx} (wf : (m.vlet x name ty v ty' v').WF env Us) :
    (m.vlet x name ty v ty' v').lctx.find? x =
      some (.ldecl m.length x name ty v false default) := by
  rw [wf.find?_eq]; simp [decls, LocalDecl.fvarId]

/-- Extending a universe scope by one declaration in scope, keeping the predicate. -/
theorem VContext.UniverseScope.cons_same {c c' : VContext}
    (hfind : ∀ fv, fv ≠ x → c'.lctx'.find? fv = c.lctx'.find? fv)
    (H : c.UniverseScope Us P) (hup : IsFVarUpSet P c'.vlctx)
    (hdecl : ∀ decl, c'.lctx'.find? x = some decl → decl.type.levelParamsIn Us = true ∧
      ∀ v, decl.value? true = some v → v.levelParamsIn Us = true) :
    c'.UniverseScope Us P := by
  refine ⟨hup, fun fv decl hP hd => ?_⟩
  by_cases h : fv = x
  · subst h; exact hdecl _ hd
  · exact H.2 fv decl hP (hfind fv h ▸ hd)

theorem VContext.LevelsBelow.rfl {c : VContext} : c.LevelsBelow e e := fun _ _ _ h _ => h

theorem VContext.LevelsBelow.trans {c : VContext} (H1 : c.LevelsBelow e₁ e₂)
    (F1 : c.FVarsBelow e₁ e₂) (H2 : c.LevelsBelow e₂ e₃) : c.LevelsBelow e₁ e₃ :=
  fun Us P hs h1 f1 => H2 Us P hs (H1 Us P hs h1 f1) (F1 P hs.1 f1)

theorem VContext.LevelsBelow.eqv {c : VContext} (H : c.LevelsBelow e₁ e₂)
    (eq : e₁ == e₁') (eq' : e₂ == e₂') : c.LevelsBelow e₁' e₂' := by
  intro Us P hs h1 f1
  rw [← Expr.levelParamsIn_eqv eq']
  exact H Us P hs (by rwa [Expr.levelParamsIn_eqv eq]) (.eqv (BEq.symm eq) f1)

theorem LevelsCache.WF.insert {c : VContext} (H : LevelsCache.WF c m)
    (h : c.LevelsBelow e e₁) : LevelsCache.WF c (m.insert e e₁) := by
  intro k v hk hf
  rw [Std.HashMap.getElem?_insert] at hk; split at hk
  · cases hk; rename_i eq; exact h.eqv eq BEq.rfl
  · exact H hk hf

/-- A universe scope of a context extended by one declaration restricts to one of the context. -/
theorem VContext.UniverseScope.tail {c c' : VContext}
    (hΔ : c'.vlctx = (some (x, deps), d) :: c.vlctx)
    (hfind : ∀ fv, fv ≠ x → c'.lctx'.find? fv = c.lctx'.find? fv)
    (hnone : c.lctx'.find? x = none)
    (H : c'.UniverseScope Us P) : c.UniverseScope Us P := by
  have h1 := H.1; rw [hΔ] at h1
  refine ⟨h1.1, fun fv decl hP hd => H.2 fv decl hP ?_⟩
  rw [hfind fv (by rintro rfl; simp [hnone] at hd)]; exact hd

/-- A universe scope extends to a declaration whose type, value and dependencies are in scope. -/
theorem VContext.UniverseScope.cons {c c' : VContext}
    (hΔ : c'.vlctx = (some (x, deps), d) :: c.vlctx)
    (hfind : ∀ fv, fv ≠ x → c'.lctx'.find? fv = c.lctx'.find? fv)
    (hid : x ∉ c.vlctx.fvars)
    (H : c.UniverseScope Us P) (hdeps : ∀ fv ∈ deps, P fv)
    (hdecl : ∀ decl, c'.lctx'.find? x = some decl → decl.type.levelParamsIn Us = true ∧
      ∀ v, decl.value? true = some v → v.levelParamsIn Us = true) :
    c'.UniverseScope Us (fun fv => fv = x ∨ P fv) := by
  refine ⟨?_, fun fv decl hP hd => ?_⟩
  · rw [hΔ]
    refine ⟨(IsFVarUpSet.congr c.Δwf.fvwf fun fv h => ?_).1 H.1, fun _ fv h => .inr (hdeps fv h)⟩
    exact ⟨.inr, fun | .inl rfl => (hid h).elim | .inr h => h⟩
  · by_cases h : fv = x
    · subst h; exact hdecl _ hd
    · exact H.2 fv decl (hP.resolve_left h) (hfind fv h ▸ hd)

theorem LevelsCache.WF.fresh {c c' : VContext}
    (hΔ : c'.vlctx = (some (x, deps), d) :: c.vlctx)
    (hfind : ∀ fv, fv ≠ x → c'.lctx'.find? fv = c.lctx'.find? fv)
    (hnone : c.lctx'.find? x = none)
    (hres : ∀ ⦃e e₁ : Expr⦄, m[e]? = some e₁ → FVarsIn R e) (hR : ¬R x)
    (H : LevelsCache.WF c m) : LevelsCache.WF c' m := by
  intro e e₁ h hf Us P hs hl hP
  refine H h ?_ Us P (hs.tail hΔ hfind hnone) hl hP
  refine hf.mp (fun fv h1 h2 => ?_) (hres h)
  rw [hΔ] at h1; simp at h1
  rcases h1 with rfl | h1
  · exact (hR h2).elim
  · exact h1

theorem State.LE.namePrefix {s₁ s₂ : State} (h : s₁ ≤ s₂) :
    s₁.ngen.namePrefix = s₂.ngen.namePrefix := by
  obtain ⟨⟨p, i⟩⟩ := s₁; obtain ⟨⟨p', j⟩⟩ := s₂; cases h; rfl

theorem UngeneratedParams.ne_of_not_reserves {ngen : NameGenerator} {id : FVarId}
    (H : UngeneratedParams pfx As) (hp : ngen.namePrefix = pfx) (h : ¬ngen.Reserves id) :
    ∀ a ∈ As, ∃ fv, a = .fvar fv ∧ fv ≠ id := by
  intro a ha
  obtain ⟨fv, rfl, hfv⟩ := H a ha
  refine ⟨fv, rfl, ?_⟩
  rintro rfl
  exact h fun i hi => absurd hi (hp ▸ hfv i)

theorem VContext.ParamUniformBelow.rfl {c : VContext} : c.ParamUniformBelow pfx e e := fun _ _ _ _ _ h _ => h

theorem VContext.ParamUniformBelow.trans {c : VContext} (H1 : c.ParamUniformBelow pfx e₁ e₂)
    (F1 : c.FVarsBelow e₁ e₂) (H2 : c.ParamUniformBelow pfx e₂ e₃) : c.ParamUniformBelow pfx e₁ e₃ :=
  fun heads As ls P hs h1 f1 => H2 heads As ls P hs (H1 heads As ls P hs h1 f1) (F1 P hs.up f1)

theorem VContext.ParamUniformBelow.eqv {c : VContext} (H : c.ParamUniformBelow pfx e₁ e₂)
    (eq : e₁ == e₁') (eq' : e₂ == e₂') : c.ParamUniformBelow pfx e₁' e₂' := by
  intro heads As ls P hs h1 f1
  exact (H heads As ls P hs (h1.eqv hs.params.fvars (BEq.symm eq)) (.eqv (BEq.symm eq) f1)).eqv
    hs.params.fvars eq'

theorem VContext.ParamUniformTyBelow.eqv_left {c : VContext} (H : c.ParamUniformTyBelow pfx e₁ e₂)
    (eq : e₁ == e₁') : c.ParamUniformTyBelow pfx e₁' e₂ := by
  refine ⟨H.1.eqv eq BEq.rfl, fun heads As ls P hs n hn he => ?_⟩
  subst he
  exact H.2 heads As ls P hs n hn (Expr.eqv_const.1 eq)

theorem ParamUniformCache.WF.insert {c : VContext} (H : ParamUniformCache.WF c pfx m)
    (h : c.ParamUniformBelow pfx e e₁) : ParamUniformCache.WF c pfx (m.insert e e₁) := by
  intro k v hk hf
  rw [Std.HashMap.getElem?_insert] at hk; split at hk
  · cases hk; rename_i eq; exact h.eqv eq BEq.rfl
  · exact H hk hf

theorem ParamUniformTyCache.WF.insert {c : VContext} (H : ParamUniformTyCache.WF c pfx m)
    (h : c.ParamUniformTyBelow pfx e e₁) : ParamUniformTyCache.WF c pfx (m.insert e e₁) := by
  intro k v hk hf
  rw [Std.HashMap.getElem?_insert] at hk; split at hk
  · cases hk; rename_i eq; exact h.eqv_left eq
  · exact H hk hf

/-- A parameter-uniform scope of a context extended by one declaration restricts to one of the
context. -/
theorem VContext.ParamUniformScope.tail {c c' : VContext} (henv : c'.env = c.env)
    (hΔ : c'.vlctx = (some (x, deps), d) :: c.vlctx)
    (hfind : ∀ fv, fv ≠ x → c'.lctx'.find? fv = c.lctx'.find? fv)
    (hnone : c.lctx'.find? x = none)
    (H : c'.ParamUniformScope pfx heads As ls P) : c.ParamUniformScope pfx heads As ls P := by
  have h1 := H.up; rw [hΔ] at h1
  refine ⟨henv ▸ H.env, H.params, h1.1, fun fv decl hP hd => henv ▸ H.decls fv decl hP ?_⟩
  rw [hfind fv (by rintro rfl; simp [hnone] at hd)]; exact hd

/-- Extending a parameter-uniform scope by one declaration in scope, keeping the predicate. -/
theorem VContext.ParamUniformScope.cons_same {c c' : VContext} (henv : c'.env = c.env)
    (hfind : ∀ fv, fv ≠ x → c'.lctx'.find? fv = c.lctx'.find? fv)
    (H : c.ParamUniformScope pfx heads As ls P) (hup : IsFVarUpSet P c'.vlctx)
    (hdecl : ∀ decl, c'.lctx'.find? x = some decl → decl.type.ParamUniformIn c.env heads As ls ∧
      ∀ v, decl.value? true = some v → v.ParamUniformIn c.env heads As ls) :
    c'.ParamUniformScope pfx heads As ls P := by
  refine ⟨henv ▸ H.env, H.params, hup, fun fv decl hP hd => henv ▸ ?_⟩
  by_cases h : fv = x
  · subst h; exact hdecl _ hd
  · exact H.decls fv decl hP (hfind fv h ▸ hd)

theorem ParamUniformCache.WF.fresh {c c' : VContext} (henv : c'.env = c.env)
    (hΔ : c'.vlctx = (some (x, deps), d) :: c.vlctx)
    (hfind : ∀ fv, fv ≠ x → c'.lctx'.find? fv = c.lctx'.find? fv)
    (hnone : c.lctx'.find? x = none)
    (hres : ∀ ⦃e e₁ : Expr⦄, m[e]? = some e₁ → FVarsIn R e) (hR : ¬R x)
    (H : ParamUniformCache.WF c pfx m) : ParamUniformCache.WF c' pfx m := by
  intro e e₁ h hf heads As ls P hs hl hP
  rw [henv] at hl ⊢
  refine H h ?_ heads As ls P (hs.tail henv hΔ hfind hnone) hl hP
  refine hf.mp (fun fv h1 h2 => ?_) (hres h)
  rw [hΔ] at h1; simp at h1
  rcases h1 with rfl | h1
  · exact (hR h2).elim
  · exact h1

theorem ParamUniformTyCache.WF.fresh {c c' : VContext} (henv : c'.env = c.env)
    (hΔ : c'.vlctx = (some (x, deps), d) :: c.vlctx)
    (hfind : ∀ fv, fv ≠ x → c'.lctx'.find? fv = c.lctx'.find? fv)
    (hnone : c.lctx'.find? x = none)
    (hres : ∀ ⦃e e₁ : Expr⦄, m[e]? = some e₁ → FVarsIn R e) (hR : ¬R x)
    (H : ParamUniformTyCache.WF c pfx m) : ParamUniformTyCache.WF c' pfx m := by
  intro e e₁ h hf
  have hf' : FVarsIn (· ∈ c.vlctx.fvars) e := by
    refine hf.mp (fun fv h1 h2 => ?_) (hres h)
    rw [hΔ] at h1; simp at h1
    rcases h1 with rfl | h1
    · exact (hR h2).elim
    · exact h1
  have H' := H h hf'
  refine ⟨fun heads As ls P hs hl hP => ?_, fun heads As ls P hs n hn he => ?_⟩
  · rw [henv] at hl ⊢; exact H'.1 heads As ls P (hs.tail henv hΔ hfind hnone) hl hP
  · rw [henv]; exact H'.2 heads As ls P (hs.tail henv hΔ hfind hnone) n hn he
/-! ### Leaving a binder in the global cache mode

In the global cache mode the state of the body is kept when a binder is closed. Its conditional
cache entries are restricted to the smaller context with strengthening (the
`ConditionallyHasType.weakN_inv` family), the syntactic universe and parameter-uniformity
invariants are restricted without it, and the equivalence manager's context grows by the closed
binder (`EqvScope`). -/

/-- A universe scope of a context, cut down to the variables of the context, is a universe scope
of the context extended by one fresh declaration. -/
theorem VContext.UniverseScope.cons_restrict {c c' : VContext}
    (hΔ : c'.vlctx = (some (x, deps), d) :: c.vlctx)
    (hfind : ∀ fv, fv ≠ x → c'.lctx'.find? fv = c.lctx'.find? fv)
    (hid : x ∉ c.vlctx.fvars)
    (H : c.UniverseScope Us P) :
    c'.UniverseScope Us (fun fv => P fv ∧ fv ∈ c.vlctx.fvars) := by
  refine ⟨?_, fun fv decl hP hd => H.2 fv decl hP.1 ?_⟩
  · rw [hΔ]; exact ⟨(IsFVarUpSet.and_fvars c.Δwf.fvwf).1 H.1, fun h => (hid h.2).elim⟩
  · rwa [← hfind fv (by rintro rfl; exact hid hP.2)]

theorem LevelsCache.WF.weakN_inv {c c' : VContext}
    (hΔ : c'.vlctx = (some (x, deps), d) :: c.vlctx)
    (hfind : ∀ fv, fv ≠ x → c'.lctx'.find? fv = c.lctx'.find? fv)
    (hid : x ∉ c.vlctx.fvars)
    (H : LevelsCache.WF c' m) : LevelsCache.WF c m := by
  intro e e₁ h hf Us P hs hl hP
  refine H h (hf.mono fun fv h => ?_) Us _ (hs.cons_restrict hΔ hfind hid) hl
    (hP.mp (fun _ a b => ⟨a, b⟩) hf)
  rw [hΔ]; simp [h]

/-- A parameter-uniform scope of a context, cut down to the variables of the context, is one of
the context extended by one fresh declaration. -/
theorem VContext.ParamUniformScope.cons_restrict {c c' : VContext} (henv : c'.env = c.env)
    (hΔ : c'.vlctx = (some (x, deps), d) :: c.vlctx)
    (hfind : ∀ fv, fv ≠ x → c'.lctx'.find? fv = c.lctx'.find? fv)
    (hid : x ∉ c.vlctx.fvars)
    (H : c.ParamUniformScope pfx heads As ls P) :
    c'.ParamUniformScope pfx heads As ls (fun fv => P fv ∧ fv ∈ c.vlctx.fvars) := by
  refine ⟨henv ▸ H.env, H.params, ?_, fun fv decl hP hd => henv ▸ H.decls fv decl hP.1 ?_⟩
  · rw [hΔ]; exact ⟨(IsFVarUpSet.and_fvars c.Δwf.fvwf).1 H.up, fun h => (hid h.2).elim⟩
  · rwa [← hfind fv (by rintro rfl; exact hid hP.2)]

theorem ParamUniformCache.WF.weakN_inv {c c' : VContext} (henv : c'.env = c.env)
    (hΔ : c'.vlctx = (some (x, deps), d) :: c.vlctx)
    (hfind : ∀ fv, fv ≠ x → c'.lctx'.find? fv = c.lctx'.find? fv)
    (hid : x ∉ c.vlctx.fvars)
    (H : ParamUniformCache.WF c' pfx m) : ParamUniformCache.WF c pfx m := by
  intro e e₁ h hf heads As ls P hs hl hP
  have hf' : FVarsIn (· ∈ c'.vlctx.fvars) e := hf.mono fun fv h => by rw [hΔ]; simp [h]
  have := H h hf' heads As ls _ (hs.cons_restrict henv hΔ hfind hid) (henv ▸ hl)
    (hP.mp (fun _ a b => ⟨a, b⟩) hf)
  rwa [henv] at this

theorem ParamUniformTyCache.WF.weakN_inv {c c' : VContext} (henv : c'.env = c.env)
    (hΔ : c'.vlctx = (some (x, deps), d) :: c.vlctx)
    (hfind : ∀ fv, fv ≠ x → c'.lctx'.find? fv = c.lctx'.find? fv)
    (hid : x ∉ c.vlctx.fvars)
    (H : ParamUniformTyCache.WF c' pfx m) : ParamUniformTyCache.WF c pfx m := by
  intro e e₁ h hf
  have hf' : FVarsIn (· ∈ c'.vlctx.fvars) e := hf.mono fun fv h => by rw [hΔ]; simp [h]
  have H' := H h hf'
  refine ⟨fun heads As ls P hs hl hP => ?_, fun heads As ls P hs n hn he => ?_⟩
  · have := H'.1 heads As ls _ (hs.cons_restrict henv hΔ hfind hid) (henv ▸ hl)
      (hP.mp (fun _ a b => ⟨a, b⟩) hf)
    rwa [henv] at this
  · have := H'.2 heads As ls _ (hs.cons_restrict henv hΔ hfind hid) n hn he
    rwa [henv] at this

/-- Leaving a binder without restoring the state, given strengthening: the state of the body is
well formed in the context without the binder. -/
theorem State.WF.restrict {c : VContext} {m m'} [cwf : c.MLCWF m] [cwf' : c.MLCWF m']
    {s : State} (hs : c.venv.Strengthening)
    (hΔ : m'.vlctx = (some (x, deps), d) :: m.vlctx)
    (hfind : ∀ fv, fv ≠ x → m'.lctx.find? fv = m.lctx.find? fv)
    (hid : x ∉ m.vlctx.fvars)
    (wf' : s.WF (c.withMLC m')) : s.WF (c.withMLC m) := by
  have trwf : VLCtx.WF c.venv c.lparams.length ((some (x, deps), d) :: m.vlctx) :=
    hΔ ▸ cwf'.1.tr.wf
  have hΔ' : (c.withMLC m').vlctx = (some (x, deps), d) :: (c.withMLC m).vlctx := hΔ
  have hic {ic} (H : InferCache.WF (c.withMLC m') s ic) : InferCache.WF (c.withMLC m) s ic :=
    fun _ _ h => by
      have : ConditionallyHasType s.ngen c.venv c.lparams m'.vlctx _ _ := H h
      rw [hΔ] at this; exact this.weakN_inv c.Ewf trwf
  have hwc {wc} (H : WHNFCache.WF (c.withMLC m') s wc) : WHNFCache.WF (c.withMLC m) s wc :=
    fun _ _ h => by
      have : ConditionallyWHNF s.ngen c.venv c.lparams m'.vlctx _ _ := H h
      rw [hΔ] at this; exact this.weakN_inv c.Ewf trwf
  have hfind' : ∀ fv, fv ≠ x → (c.withMLC m').lctx'.find? fv = (c.withMLC m).lctx'.find? fv :=
    hfind
  exact
  { trctx := cwf.1.tr
    ngen_wf := fun fv h => wf'.ngen_wf fv (by rw [hΔ']; exact List.mem_cons_of_mem _ h)
    ectx := by
      have Wx : VLCtx.FVLift' (c.withMLC m).vlctx (c.withMLC m').vlctx 0
          (Lift.refl.skipN d.depth) 0 := by rw [hΔ']; exact .skip_fvar _ _ .refl
      obtain ⟨Δ', h | ⟨-, hwf, ⟨l, W⟩, hres⟩, hm⟩ := wf'.ectx
      · subst h
        exact ⟨_, .inr ⟨hs, cwf'.1.tr.wf, ⟨_, Wx⟩, wf'.ngen_wf⟩, hm⟩
      · exact ⟨_, .inr ⟨hs, hwf, ⟨_, Wx.comp W⟩, hres⟩, hm⟩
    inferTypeI_wf := hic wf'.inferTypeI_wf, inferTypeC_wf := hic wf'.inferTypeC_wf
    whnfCore_wf := hwc wf'.whnfCore_wf, whnf_wf := hwc wf'.whnf_wf, unfold_wf := wf'.unfold_wf
    inferTypeI_levels := wf'.inferTypeI_levels.weakN_inv (c' := c.withMLC m') hΔ' hfind' hid
    inferTypeC_levels := wf'.inferTypeC_levels.weakN_inv (c' := c.withMLC m') hΔ' hfind' hid
    whnfCore_levels := wf'.whnfCore_levels.weakN_inv (c' := c.withMLC m') hΔ' hfind' hid
    whnf_levels := wf'.whnf_levels.weakN_inv (c' := c.withMLC m') hΔ' hfind' hid
    whnfCore_paramUniform := wf'.whnfCore_paramUniform.weakN_inv (c' := c.withMLC m') rfl hΔ' hfind' hid
    whnf_paramUniform := wf'.whnf_paramUniform.weakN_inv (c' := c.withMLC m') rfl hΔ' hfind' hid
    inferTypeI_paramUniform := wf'.inferTypeI_paramUniform.weakN_inv (c' := c.withMLC m') rfl hΔ' hfind' hid }

def State.next (s : State) : State := { s with ngen := s.ngen.next }


/-- The executable's `withFreshId`, unfolded: run the body on the current name and a state
whose generator has advanced. Nothing is restored when the scope is left, as in the C++ kernel. -/
theorem withFreshId_eq {α} (x : Name → M α) (c : Context) (s : State) :
    (withFreshId x : M α) c s = x s.ngen.curr c { s with ngen := s.ngen.next } := by
  unfold withFreshId instMonadLocalNameGeneratorM
  simp only [bind, ReaderT.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, liftM,
    monadLift, MonadLift.monadLift, Except.bind, pure, Except.pure, ReaderT.pure, StateT.pure,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, mkFreshId, getNGen, setNGen,
    read, readThe, MonadReaderOf.read, ReaderT.read]

/-- A binder scope of the checker: the body runs from the state with the name generator advanced,
and its final state is the result state. -/
theorem M.WF.withFreshId {c : VContext} {s : State} {x : Name → M α} {Q : α → State → Prop}
    (H : ∀ a s', x s.ngen.curr c.toContext s.next = .ok (a, s') →
      ∃ vs', vs' = s' ∧ s.next ≤ vs' ∧ vs'.WF c ∧ Q a vs') :
    ∀ a s', (withFreshId x : M α) c.toContext s = .ok (a, s') →
      ∃ vs', vs' = s' ∧ s ≤ vs' ∧ vs'.WF c ∧ Q a vs' := by
  intro a s' e
  rw [withFreshId_eq] at e
  obtain ⟨vs', rfl, le, hwf, hQ⟩ := H _ _ e
  exact ⟨_, rfl, State.LE.trans .next le, hwf, hQ⟩

/-- Entering a binder: the equivalence manager's facts hold in the extended context, or in the
global cache mode in the extension of their context by the new variable. -/
theorem State.WF.ectx_fresh {c : VContext} {m m'} [cwf : c.MLCWF m] [cwf' : c.MLCWF m']
    {s : State} (wf : s.WF (c.withMLC m))
    (hΔ : m'.vlctx = (some (⟨s.ngen.curr⟩, deps), d) :: m.vlctx)
    (hdeps : deps ⊆ m.vlctx.fvars)
    (hd : VLocalDecl.WF c.venv c.lparams.length m.vlctx.toCtx d) :
    ∃ Δ', EqvScope (c.withMLC m') s.next.ngen Δ' ∧ s.eqvManager.WF c.venv c.lparams Δ' := by
  have h0 := s.ngen.next_reserves_self
  have h1 := s.ngen.not_reserves_self
  have le : s ≤ s.next := .next
  have trwf : m'.vlctx.WF c.venv c.lparams.length := cwf'.1.tr.wf
  obtain ⟨Δ', h | ⟨hs, hwf, ⟨l, W⟩, hres⟩, hm⟩ := wf.ectx
  · subst h
    refine ⟨_, .inl rfl, ?_⟩
    show EquivManager.WF _ _ m'.vlctx _
    rw [hΔ] at trwf ⊢
    exact hm.weak' c.Ewf (.skip_fvar _ _ .refl) trwf
  · have hwf' : VLCtx.WF c.venv c.lparams.length
        ((some (⟨s.ngen.curr⟩, deps), d.lift' l) :: Δ') := by
      refine ⟨hwf, ?_, hd.weak' c.Ewf.orderedStrong W.toCtx⟩
      rintro _ _ ⟨⟩
      exact ⟨mt (hres _) h1, hdeps.trans W.fvars_sublist.subset⟩
    refine ⟨_, .inr ⟨hs, hwf', ⟨l.consN d.depth, ?_⟩, ?_⟩, hm.weak' c.Ewf (.skip_fvar _ _ .refl) hwf'⟩
    · show VLCtx.FVLift' m'.vlctx _ _ _ _
      rw [hΔ]; exact W.cons_fvar (⟨s.ngen.curr⟩, deps) d hdeps
    · intro fv h
      obtain _ | ⟨_, h⟩ := h
      · exact h0
      · exact (hres _ h).mono le

/-- Entering a binder keeps the state well formed: the name generator advances past the fresh
variable and every cache is weakened to the extended context. This is the well-formedness part of
`RecM.WF.withLocalDecl` and `M.WF.withLocalDecl`, and the state at a kept binder of the ghost
telescope proof. -/
theorem State.WF.vlam {c : VContext} {m} [cwf : c.MLCWF m] {s : State}
    (wf : s.WF (c.withMLC m)) (hty : (c.withMLC m).TrExprS ty ty')
    (hty' : (c.withMLC m).IsType ty')
    [cwf' : c.MLCWF (m.vlam ⟨s.ngen.curr⟩ name ty ty' bi)] :
    s.next.WF (c.withMLC (m.vlam ⟨s.ngen.curr⟩ name ty ty' bi)) := by
  let id := s.ngen.curr
  have h0 := s.ngen.next_reserves_self
  have h1 := s.ngen.not_reserves_self
  have le : s ≤ s.next := .next
  have h1' := wf.find?_eq_none h1
  let m' := m.vlam ⟨id⟩ name ty ty' bi
  have trctx : (c.withMLC m').TrLCtx := wf.trctx.mkLocalDecl h1' hty hty'
  have hic {ic} (H : InferCache.WF (c.withMLC m) s ic) : InferCache.WF (c.withMLC m') s.next ic :=
    fun _ _ h => ((H h).fresh c.Ewf.orderedStrong trctx.wf).mono le
  have hwc {wc} (H : WHNFCache.WF (c.withMLC m) s wc) : WHNFCache.WF (c.withMLC m') s.next wc :=
    fun _ _ h => ((H h).fresh c.Ewf trctx.wf).mono le
  have hlc {ic : InferCache}
      (hres : ∀ ⦃e e₁ : Expr⦄, ic[e]? = some e₁ → FVarsIn s.ngen.Reserves e)
      (H : LevelsCache.WF (c.withMLC m) ic) : LevelsCache.WF (c.withMLC m') ic :=
    H.fresh (c := c.withMLC m) rfl (fun _ h => cwf'.1.find?_vlam h) h1' hres h1
  have hhc {ic : InferCache}
      (hres : ∀ ⦃e e₁ : Expr⦄, ic[e]? = some e₁ → FVarsIn s.ngen.Reserves e)
      (H : ParamUniformCache.WF (c.withMLC m) s.ngen.namePrefix ic) :
      ParamUniformCache.WF (c.withMLC m') s.ngen.namePrefix ic :=
    H.fresh (c := c.withMLC m) rfl rfl (fun _ h => cwf'.1.find?_vlam h) h1' hres h1
  have hhtc {ic : InferCache}
      (hres : ∀ ⦃e e₁ : Expr⦄, ic[e]? = some e₁ → FVarsIn s.ngen.Reserves e)
      (H : ParamUniformTyCache.WF (c.withMLC m) s.ngen.namePrefix ic) :
      ParamUniformTyCache.WF (c.withMLC m') s.ngen.namePrefix ic :=
    H.fresh (c := c.withMLC m) rfl rfl (fun _ h => cwf'.1.find?_vlam h) h1' hres h1
  exact
  { ngen_wf := by
      simp [VContext.withMLC]; exact ⟨h0, fun _ h => le.reservesV (wf.ngen_wf _ h)⟩
    ectx := wf.ectx_fresh (cwf' := cwf') rfl hty.fvarsList hty'
    trctx, inferTypeI_wf := hic wf.inferTypeI_wf, inferTypeC_wf := hic wf.inferTypeC_wf
    whnfCore_wf := hwc wf.whnfCore_wf, whnf_wf := hwc wf.whnf_wf, unfold_wf := wf.unfold_wf
    inferTypeI_levels := hlc (fun _ _ h => (wf.inferTypeI_wf h).2.1) wf.inferTypeI_levels
    inferTypeC_levels := hlc (fun _ _ h => (wf.inferTypeC_wf h).2.1) wf.inferTypeC_levels
    whnfCore_levels := hlc (fun _ _ h => (wf.whnfCore_wf h).2.1) wf.whnfCore_levels
    whnf_levels := hlc (fun _ _ h => (wf.whnf_wf h).2.1) wf.whnf_levels
    whnfCore_paramUniform := hhc (fun _ _ h => (wf.whnfCore_wf h).2.1) wf.whnfCore_paramUniform
    whnf_paramUniform := hhc (fun _ _ h => (wf.whnf_wf h).2.1) wf.whnf_paramUniform
    inferTypeI_paramUniform := hhtc (fun _ _ h => (wf.inferTypeI_wf h).2.1) wf.inferTypeI_paramUniform }

protected theorem RecM.WF.withLocalDecl {c : VContext} {m} [cwf : c.MLCWF m]
    {s : State} {f : Expr → RecM α} {Q name ty ty' bi}
    (hty : (c.withMLC m).TrExprS ty ty')
    (hty' : (c.withMLC m).IsType ty')
    (hs : s₀ ≤ s)
    (H : ∀ id cwf' s', s₀ ≤ s' → ¬s.ngen.Reserves id →
      WF (c.withMLC (.vlam id name ty ty' bi m) (wf := cwf')) s' (f (.fvar id))
        fun a s'' => Q a s'') :
    (withLocalDecl name bi ty f).WF (c.withMLC m) s Q := by
  intro _ mwf wf
  let id := s.ngen.curr
  have h0 := s.ngen.next_reserves_self
  have h1 := s.ngen.not_reserves_self
  have le : s ≤ s.next := .next
  have h1' := wf.find?_eq_none h1
  let m' := m.vlam ⟨id⟩ name ty ty' bi
  have cwf' : c.MLCWF m' := ⟨cwf.1, h1', hty, hty'⟩
  have : State.WF (c.withMLC m') s.next := State.WF.vlam (cwf' := cwf') wf hty hty'
  refine M.WF.withFreshId fun a s' e => ?_
  let ⟨s', hs1, hs2, wf', hs4⟩ := H _ _ _ (hs.trans le) h1 _ mwf this a s' e
  exact ⟨s', hs1, hs2, wf'.restrict (cwf' := cwf') c.strengthening rfl
    (fun _ h => cwf'.1.find?_vlam h) (fun h => h1 (wf.ngen_wf _ h)), hs4⟩

protected theorem M.WF.withLocalDecl {c : VContext} {m} [cwf : c.MLCWF m]
    {s : State} {f : Expr → M α} {Q name ty ty' bi}
    (hty : (c.withMLC m).TrExprS ty ty')
    (hty' : (c.withMLC m).IsType ty')
    (hs : s₀ ≤ s)
    (H : ∀ id cwf' s', s₀ ≤ s' → ¬s.ngen.Reserves id →
      WF (c.withMLC (.vlam id name ty ty' bi m) (wf := cwf')) s' (f (.fvar id))
        fun a s'' => Q a s'') :
    (withLocalDecl name bi ty f).WF (c.withMLC m) s Q := by
  intro wf
  let id := s.ngen.curr
  have h0 := s.ngen.next_reserves_self
  have h1 := s.ngen.not_reserves_self
  have le : s ≤ s.next := .next
  have h1' := wf.find?_eq_none h1
  let m' := m.vlam ⟨id⟩ name ty ty' bi
  have cwf' : c.MLCWF m' := ⟨cwf.1, h1', hty, hty'⟩
  have : State.WF (c.withMLC m') s.next := State.WF.vlam (cwf' := cwf') wf hty hty'
  refine M.WF.withFreshId fun a s' e => ?_
  let ⟨s', hs1, hs2, wf', hs4⟩ := H _ _ _ (hs.trans le) h1 this a s' e
  exact ⟨s', hs1, hs2, wf'.restrict (cwf' := cwf') c.strengthening rfl
    (fun _ h => cwf'.1.find?_vlam h) (fun h => h1 (wf.ngen_wf _ h)), hs4⟩

/-- Entering a `let` binder keeps the state well formed, as `State.WF.vlam` for a local
definition. -/
theorem State.WF.vlet {c : VContext} {m} [cwf : c.MLCWF m] {s : State}
    (wf : s.WF (c.withMLC m)) (hty : (c.withMLC m).TrExprS ty ty')
    (hval : (c.withMLC m).TrExprS val val')
    (hval' : (c.withMLC m).HasType val' ty')
    [cwf' : c.MLCWF (m.vlet ⟨s.ngen.curr⟩ name ty val ty' val')] :
    s.next.WF (c.withMLC (m.vlet ⟨s.ngen.curr⟩ name ty val ty' val')) := by
  let id := s.ngen.curr
  have h0 := s.ngen.next_reserves_self
  have h1 := s.ngen.not_reserves_self
  have le : s ≤ s.next := .next
  have h1' := wf.find?_eq_none h1
  let m' := m.vlet ⟨id⟩ name ty val ty' val'
  have trctx : (c.withMLC m').TrLCtx := wf.trctx.mkLetDecl h1' hty hval hval'
  have hic {ic} (H : InferCache.WF (c.withMLC m) s ic) :
      InferCache.WF (c.withMLC m') s.next ic :=
    fun _ _ h => ((H h).fresh c.Ewf.orderedStrong trctx.wf).mono le
  have hwc {wc} (H : WHNFCache.WF (c.withMLC m) s wc) : WHNFCache.WF (c.withMLC m') s.next wc :=
    fun _ _ h => ((H h).fresh c.Ewf trctx.wf).mono le
  have hlc {ic : InferCache}
      (hres : ∀ ⦃e e₁ : Expr⦄, ic[e]? = some e₁ → FVarsIn s.ngen.Reserves e)
      (H : LevelsCache.WF (c.withMLC m) ic) : LevelsCache.WF (c.withMLC m') ic :=
    H.fresh (c := c.withMLC m) rfl (fun _ h => cwf'.1.find?_vlet h) h1' hres h1
  have hhc {ic : InferCache}
      (hres : ∀ ⦃e e₁ : Expr⦄, ic[e]? = some e₁ → FVarsIn s.ngen.Reserves e)
      (H : ParamUniformCache.WF (c.withMLC m) s.ngen.namePrefix ic) :
      ParamUniformCache.WF (c.withMLC m') s.ngen.namePrefix ic :=
    H.fresh (c := c.withMLC m) rfl rfl (fun _ h => cwf'.1.find?_vlet h) h1' hres h1
  have hhtc {ic : InferCache}
      (hres : ∀ ⦃e e₁ : Expr⦄, ic[e]? = some e₁ → FVarsIn s.ngen.Reserves e)
      (H : ParamUniformTyCache.WF (c.withMLC m) s.ngen.namePrefix ic) :
      ParamUniformTyCache.WF (c.withMLC m') s.ngen.namePrefix ic :=
    H.fresh (c := c.withMLC m) rfl rfl (fun _ h => cwf'.1.find?_vlet h) h1' hres h1
  exact
  { ngen_wf := by
      simp [VContext.withMLC]; exact ⟨h0, fun _ h => le.reservesV (wf.ngen_wf _ h)⟩
    ectx := wf.ectx_fresh (cwf' := cwf') rfl
      (List.append_subset.2 ⟨hty.fvarsList, hval.fvarsList⟩) hval'
    trctx, inferTypeI_wf := hic wf.inferTypeI_wf, inferTypeC_wf := hic wf.inferTypeC_wf
    whnfCore_wf := hwc wf.whnfCore_wf, whnf_wf := hwc wf.whnf_wf, unfold_wf := wf.unfold_wf
    inferTypeI_levels := hlc (fun _ _ h => (wf.inferTypeI_wf h).2.1) wf.inferTypeI_levels
    inferTypeC_levels := hlc (fun _ _ h => (wf.inferTypeC_wf h).2.1) wf.inferTypeC_levels
    whnfCore_levels := hlc (fun _ _ h => (wf.whnfCore_wf h).2.1) wf.whnfCore_levels
    whnf_levels := hlc (fun _ _ h => (wf.whnf_wf h).2.1) wf.whnf_levels
    whnfCore_paramUniform := hhc (fun _ _ h => (wf.whnfCore_wf h).2.1) wf.whnfCore_paramUniform
    whnf_paramUniform := hhc (fun _ _ h => (wf.whnf_wf h).2.1) wf.whnf_paramUniform
    inferTypeI_paramUniform := hhtc (fun _ _ h => (wf.inferTypeI_wf h).2.1) wf.inferTypeI_paramUniform }

protected theorem RecM.WF.withLetDecl {c : VContext} {m} [cwf : c.MLCWF m]
    {s : State} {f : Expr → RecM α} {Q name ty ty'}
    (hty : (c.withMLC m).TrExprS ty ty')
    (hval : (c.withMLC m).TrExprS val val')
    (hval' : (c.withMLC m).HasType val' ty')
    (hs : s₀ ≤ s)
    (H : ∀ id cwf' s', s₀ ≤ s' → ¬s.ngen.Reserves id →
      WF (c.withMLC (.vlet id name ty val ty' val' m) (wf := cwf')) s' (f (.fvar id))
        fun a s'' => Q a s'') :
    (withLetDecl name ty val f).WF (c.withMLC m) s Q := by
  intro _ mwf wf
  let id := s.ngen.curr
  have h0 := s.ngen.next_reserves_self
  have h1 := s.ngen.not_reserves_self
  have le : s ≤ s.next := .next
  have h1' := wf.find?_eq_none h1
  let m' := m.vlet ⟨id⟩ name ty val ty' val'
  have cwf' : c.MLCWF m' := ⟨cwf.1, h1', hty, hval, hval'⟩
  have : State.WF (c.withMLC m') s.next := State.WF.vlet (cwf' := cwf') wf hty hval hval'
  refine M.WF.withFreshId fun a s' e => ?_
  let ⟨s', hs1, hs2, wf', hs4⟩ := H _ _ _ (hs.trans le) h1 _ mwf this a s' e
  exact ⟨s', hs1, hs2, wf'.restrict (cwf' := cwf') c.strengthening rfl
    (fun _ h => cwf'.1.find?_vlet h) (fun h => h1 (wf.ngen_wf _ h)), hs4⟩

@[simp] def MLCtx.mkForall (c : MLCtx) (n) (hn : n ≤ c.length) (e : Expr) : Expr :=
  match n, c, hn with
  | 0, _, _ => e
  | n+1, .vlam x name ty _ bi c, h =>
    c.mkForall n (Nat.le_of_succ_le_succ h) (.forallE name ty (.abstract1 x e) bi)
  | n+1, .vlet x name ty val _ _ c, h =>
    c.mkForall n (Nat.le_of_succ_le_succ h) <|
      let e' := Expr.abstract1 x e
      if e'.hasLooseBVar' 0 then
        .letE name ty val e' false
      else
        e'.lowerLooseBVars' 1 1
termination_by structural n

def AllAbove (Δ : VLCtx) (P : FVarId → Prop) (fv : FVarId) : Prop := fv ∈ Δ.fvars → P fv

theorem AllAbove.wf (H : Δ.FVWF) : IsFVarUpSet (AllAbove Δ P) Δ ↔ IsFVarUpSet P Δ :=
  IsFVarUpSet.congr H fun _ h => by simp [h, AllAbove]

/-- A universe scope is still one when relaxed to every variable outside the context. -/
theorem VContext.UniverseScope.allAbove {c : VContext} (H : c.UniverseScope Us P) :
    c.UniverseScope Us (AllAbove c.vlctx P) :=
  ⟨(AllAbove.wf c.Δwf.fvwf).2 H.1, fun fv decl hP hd =>
    H.2 fv decl (hP (c.trlctx.find?_eq_some.1 ⟨_, hd⟩)) hd⟩

/-- A parameter-uniform scope is still one when relaxed to every variable outside the context. -/
theorem VContext.ParamUniformScope.allAbove {c : VContext} (H : c.ParamUniformScope pfx heads As ls P) :
    c.ParamUniformScope pfx heads As ls (AllAbove c.vlctx P) :=
  ⟨H.env, H.params, (AllAbove.wf c.Δwf.fvwf).2 H.up, fun fv decl hP hd =>
    H.decls fv decl (hP (c.trlctx.find?_eq_some.1 ⟨_, hd⟩)) hd⟩

@[simp] def MLCtx.mkForall' (c : MLCtx) (n) (hn : n ≤ c.length) (e : VExpr) : VExpr :=
  match n, c, hn, e with
  | 0, _, _, e => e
  | n+1, .vlam _ _ _ ty _ c, h, e => c.mkForall' n (Nat.le_of_succ_le_succ h) (.forallE ty e)
  | n+1, .vlet _ _ _ _ _ _ c, h, e => c.mkForall' n (Nat.le_of_succ_le_succ h) e
termination_by structural n

@[simp] def MLCtx.mkLambda (c : MLCtx) (n) (hn : n ≤ c.length) (e : Expr) : Expr :=
  match n, c, hn, e with
  | 0, _, _, e => e
  | n+1, .vlam x name ty _ bi c, h, e =>
    c.mkLambda n (Nat.le_of_succ_le_succ h) (.lam name ty (.abstract1 x e) bi)
  | n+1, .vlet x name ty val _ _ c, h, e =>
    c.mkLambda n (Nat.le_of_succ_le_succ h) <|
      let e' := Expr.abstract1 x e
      if e'.hasLooseBVar' 0 then
        .letE name ty val e' false
      else
        e'.lowerLooseBVars' 1 1
termination_by structural n

@[simp] def MLCtx.mkLambda' (c : MLCtx) (n) (hn : n ≤ c.length) (e : VExpr) : VExpr :=
  match n, c, hn, e with
  | 0, _, _, e => e
  | n+1, .vlam _ _ _ ty _ c, h, e => c.mkLambda' n (Nat.le_of_succ_le_succ h) (.lam ty e)
  | n+1, .vlet _ _ _ _ _ _ c, h, e => c.mkLambda' n (Nat.le_of_succ_le_succ h) e
termination_by structural n

-- HACK: MLCtx.mkLet equation generation fails if this is inlined
def MLCtx.mkLetArg (x : FVarId) (name : Name)
    (ty val : Expr) (nd : Option Bool) (e : Expr) : Expr :=
  let e' := Expr.abstract1 x e
  if e'.hasLooseBVar' 0 then
    .letE name ty val e' (nd.getD false)
  else if let some nd := nd then
    .letE name ty val e' nd
  else
    e'.lowerLooseBVars' 1 1

@[simp] def MLCtx.mkLet (c : MLCtx) (n) (hn : n ≤ c.length)
    (nds : List (Option Bool)) (eq : nds.length = n) (e : Expr) (asForall := false) : Expr :=
  match n, c, hn, nds, eq, e with
  | 0, _, _, _, _, e => e
  | n+1, .vlam x name ty _ bi c, h, _ :: nds, eq, e =>
    c.mkLet n (Nat.le_of_succ_le_succ h) nds (Nat.succ_inj.1 eq) <|
      if asForall then .forallE name ty (.abstract1 x e) bi else .lam name ty (.abstract1 x e) bi
  | n+1, .vlet x name ty val _ _ c, h, nd :: nds, eq, e =>
    c.mkLet n (Nat.le_of_succ_le_succ h) nds (Nat.succ_inj.1 eq) <| mkLetArg x name ty val nd e
termination_by structural n

variable! (henv : VEnv.WF env) in
theorem MLCtx.WF.mkForall_trS {c : MLCtx} (wf : c.WF env Us)
    (H1 : TrExprS env Us c.vlctx e e')
    (H2 : env.IsType Us.length c.vlctx.toCtx e') (n hn) :
    TrExprS env Us (c.dropN n hn).vlctx (c.mkForall n hn e) (c.mkForall' n hn e') ∧
    env.IsType Us.length (c.dropN n hn).vlctx.toCtx (c.mkForall' n hn e') := by
  induction n generalizing c e e' with
  | zero => exact ⟨H1, H2⟩
  | succ n ih =>
    match c with
    | .vlam x name ty ty' bi c =>
      let ⟨h1, _, h3, h4⟩ := wf
      refine ih h1 ?_ (.forallE h4 H2) _
      exact .forallE h4 H2 h3 (.abstract .zero H1)
    | .vlet x name ty val ty' val' c =>
      let ⟨h1, _, h3, h4, h5⟩ := wf
      refine ih h1 ?_ H2 _; dsimp; split
      · exact .letE h5 h3 h4 (.abstract .zero H1)
      · rename_i h; simp at h
        rw [Expr.lowerLooseBVars_eq_instantiate h (v := val)]
        exact .inst_let henv (.abstract .zero H1) h4

theorem mkForall_hasType {c : MLCtx}
    (hus : us.Forall₂ (VLevel.ofLevel Us · = some ·) us')
    (hΔ : c.vlctx.SortList env Us.length us')
    (hu : VLevel.ofLevel Us u = some u')
    (H2 : env.HasType Us.length c.vlctx.toCtx e' (.sort u')) (n hn)
    (hus : us.length = n) :
    ∃ u₀', VLevel.ofLevel Us (List.foldl (fun x y => mkLevelIMax' y x) u us) = some u₀' ∧
    env.HasType Us.length (c.dropN n hn).vlctx.toCtx (c.mkForall' n hn e') (.sort u₀') := by
  subst hus
  induction hus generalizing c e' u u' with
  | nil => exact ⟨_, hu, H2⟩
  | cons h _ ih =>
    match c, hΔ with
    | .vlam x name ty ty' bi c, .cons hΔ hu₁ =>
      have ⟨_, h5, h6⟩ := ofLevel_mkLevelIMax' h hu
      refine ih hΔ h5 ?_ (Nat.le_of_succ_le_succ hn)
      refine .defeq (.sortDF ?_ (.of_ofLevel h5) h6.symm) (hu₁.forallE H2)
      exact ⟨.of_ofLevel h, .of_ofLevel hu⟩

theorem MLCtx.WF.mkForall'_congr {c : MLCtx} (wf : c.WF env Us)
    (H : env.IsDefEq Us.length c.vlctx.toCtx e₁ e₂ (.sort u)) (n hn) :
    ∃ u, env.IsDefEq Us.length (c.dropN n hn).vlctx.toCtx
      (c.mkForall' n hn e₁) (c.mkForall' n hn e₂) (.sort u) := by
  induction n generalizing c e₁ e₂ u with
  | zero => exact ⟨_, H⟩
  | succ n ih =>
    match c with
    | .vlam .. => let ⟨_, h⟩ := wf.2.2.2; exact ih wf.1 (.forallEDF h H) _
    | .vlet .. => exact ih wf.1 H _

theorem MLCtx.WF.mkForall_tr (henv : VEnv.WF env) {c : MLCtx} (wf : c.WF env Us)
    (H1 : TrExpr env Us c.vlctx e e')
    (H2 : env.IsType Us.length c.vlctx.toCtx e') (n hn) :
    TrExpr env Us (c.dropN n hn).vlctx (c.mkForall n hn e) (c.mkForall' n hn e') ∧
    env.IsType Us.length (c.dropN n hn).vlctx.toCtx (c.mkForall' n hn e') := by
  let ⟨_, H1, eq⟩ := H1
  let ⟨_, H2⟩ := H2
  have eq := eq.of_r henv wf.tr.wf H2
  have ⟨_, H⟩ := wf.mkForall'_congr eq n hn
  have := wf.mkForall_trS henv H1 ⟨_, eq.hasType.1⟩ n hn
  exact ⟨⟨_, this.1, _, H⟩, this.2.defeqU_l henv (wf.dropN n hn).tr.wf ⟨_, H⟩⟩

variable! (henv : VEnv.WF env) in
theorem MLCtx.WF.mkLambda_trS {c : MLCtx} (wf : c.WF env Us)
    (H1 : TrExprS env Us c.vlctx e e')
    (H2 : env.HasType Us.length c.vlctx.toCtx e' ty') (n hn) :
    TrExprS env Us (c.dropN n hn).vlctx (c.mkLambda n hn e) (c.mkLambda' n hn e') ∧
    env.HasType Us.length (c.dropN n hn).vlctx.toCtx
      (c.mkLambda' n hn e') (c.mkForall' n hn ty') := by
  induction n generalizing c e e' ty' with
  | zero => exact ⟨H1, H2⟩
  | succ n ih =>
    match c with
    | .vlam x name ty ty' bi c =>
      let ⟨h1, _, h3, _, h4⟩ := wf
      refine ih h1 ?_ (.lam h4 H2) _
      exact .lam ⟨_, h4⟩ h3 (.abstract .zero H1)
    | .vlet x name ty val ty' val' c =>
      let ⟨h1, _, h3, h4, h5⟩ := wf
      refine ih h1 ?_ H2 _; dsimp; split
      · exact .letE h5 h3 h4 (.abstract .zero H1)
      · rename_i h; simp at h
        rw [Expr.lowerLooseBVars_eq_instantiate h (v := val)]
        exact .inst_let henv (.abstract .zero H1) h4

theorem MLCtx.WF.mkLambda'_congr {c : MLCtx} (wf : c.WF env Us)
    (H : env.IsDefEq Us.length c.vlctx.toCtx e₁ e₂ ty) (n hn) :
    env.IsDefEq Us.length (c.dropN n hn).vlctx.toCtx
      (c.mkLambda' n hn e₁) (c.mkLambda' n hn e₂) (c.mkForall' n hn ty) := by
  induction n generalizing c e₁ e₂ ty with
  | zero => exact H
  | succ n ih =>
    match c with
    | .vlam .. => let ⟨_, h⟩ := wf.2.2.2; exact ih wf.1 (.lamDF h H) _
    | .vlet .. => exact ih wf.1 H _

theorem MLCtx.WF.mkLambda_tr (henv : VEnv.WF env) {c : MLCtx} (wf : c.WF env Us)
    (H1 : TrExpr env Us c.vlctx e e')
    (H2 : env.HasType Us.length c.vlctx.toCtx e' ty') (n hn) :
    TrExpr env Us (c.dropN n hn).vlctx (c.mkLambda n hn e) (c.mkLambda' n hn e') ∧
    env.HasType Us.length (c.dropN n hn).vlctx.toCtx
      (c.mkLambda' n hn e') (c.mkForall' n hn ty') := by
  let ⟨_, H1, eq⟩ := H1
  have eq := eq.of_r henv wf.tr.wf H2
  have H := wf.mkLambda'_congr eq n hn
  have := wf.mkLambda_trS henv H1 eq.hasType.1 n hn
  exact ⟨⟨_, this.1, _, H⟩, this.2.defeqU_l henv (wf.dropN n hn).tr.wf ⟨_, H⟩⟩

variable! (henv : VEnv.WF env) in
theorem MLCtx.WF.mkLet_trS {c : MLCtx} (wf : c.WF env Us)
    (H1 : TrExprS env Us c.vlctx e e')
    (H2 : env.HasType Us.length c.vlctx.toCtx e' ty') (n hn nds hnds) :
    TrExprS env Us (c.dropN n hn).vlctx (c.mkLet n hn nds hnds e) (c.mkLambda' n hn e') ∧
    env.HasType Us.length (c.dropN n hn).vlctx.toCtx
      (c.mkLambda' n hn e') (c.mkForall' n hn ty') := by
  induction n generalizing c e e' ty' nds with
  | zero => exact ⟨H1, H2⟩
  | succ n ih =>
    match c with
    | .vlam x name ty ty' bi c =>
      let ⟨h1, _, h3, _, h4⟩ := wf; let _ :: _ := nds
      refine ih h1 ?_ (.lam h4 H2) ..
      exact .lam ⟨_, h4⟩ h3 (.abstract .zero H1)
    | .vlet x name ty val ty' val' c =>
      let ⟨h1, _, h3, h4, h5⟩ := wf; let _ :: _ := nds
      refine ih h1 ?_ H2 ..; dsimp [mkLetArg]; split <;> [skip; split]
      · exact .letE h5 h3 h4 (.abstract .zero H1)
      · exact .letE h5 h3 h4 (.abstract .zero H1)
      · rename_i h _ _; simp at h
        rw [Expr.lowerLooseBVars_eq_instantiate h (v := val)]
        exact .inst_let henv (.abstract .zero H1) h4

theorem MLCtx.fvarRevList_prefix (c : MLCtx)
    {n hn} : c.fvarRevList n hn <+: c.vlctx.fvars := by
  induction n generalizing c with
  | zero => simp
  | succ n ih => match c with | .vlam .. | .vlet .. => simp [ih]

theorem MLCtx.fvarRevList_all (c : MLCtx) :
    c.fvarRevList c.length (Nat.le_refl _) = c.vlctx.fvars := by
  induction c with
  | nil => rfl
  | vlam _ _ _ _ _ c ih | vlet _ _ _ _ _ _ c ih => simp [ih]

theorem MLCtx.dropN_all (c : MLCtx) :
    c.dropN c.length (Nat.le_refl _) = .nil := by
  induction c with
  | nil => rfl
  | vlam _ _ _ _ _ c ih | vlet _ _ _ _ _ _ c ih => simpa using ih

/-- The sharper form of `fvarRevList_prefix`: the variables a telescope opened and the ones it
started from, in order. This is what says a term mentioning none of the former lives in the
context the telescope was entered at. -/
theorem MLCtx.fvars_eq_append (c : MLCtx) {n hn} :
    c.vlctx.fvars = c.fvarRevList n hn ++ (c.dropN n hn).vlctx.fvars := by
  induction n generalizing c with
  | zero => simp
  | succ n ih => match c with | .vlam .. | .vlet .. => simp; exact ih _

/-- "Lives in the context the telescope was entered at" is an up-set for the telescope: the
variables it opened are fresh, so the predicate is false on them and their dependency condition
is vacuous. This is what lets `FVarsBelow` -- which `inferType`/`whnf` hand out -- be read as
"still in the base context". -/
theorem MLCtx.WF.isFVarUpSet_dropN : ∀ {c : MLCtx} (_ : c.WF env Us) (n hn),
    IsFVarUpSet (· ∈ (c.dropN n hn).vlctx.fvars) c.vlctx
  | _, wf, 0, _ => .fvars wf.tr.wf.fvwf
  | .vlam _ _ _ _ _ c, ⟨h1, h2, _⟩, _+1, _
  | .vlet _ _ _ _ _ _ c, ⟨h1, h2, _⟩, _+1, _ =>
    ⟨h1.isFVarUpSet_dropN _ _, fun h =>
      (h1.tr.find?_eq_none.1 h2 (dropN_fvars_subset (c := c) _ _ h)).elim⟩

theorem MLCtx.WF.fvars_nodup : ∀ {c : MLCtx}, c.WF env Us → c.vlctx.fvars.Nodup
  | .nil, _ => .nil
  | .vlam _ _ _ _ _ c, ⟨h1, h2, _⟩
  | .vlet _ _ _ _ _ _ c, ⟨h1, h2, _⟩ => by simp [h1.fvars_nodup, h1.tr.find?_eq_none.1 h2]

theorem MLCtx.WF.fvarRevList_nodup {c : MLCtx} (wf : c.WF env Us)
    (n hn) : (c.fvarRevList n hn).Nodup :=
  c.fvarRevList_prefix.sublist.nodup wf.fvars_nodup

inductive MLCtx.PartialForall : MLCtx → Nat → List FVarId → Expr → Prop where
  | nil : PartialForall c 0 [] e
  | vlam : PartialForall c n fvs (.forallE x ty (.abstract1 fv e) bi) →
    PartialForall (c.vlam fv x ty ty' bi) (n+1) (fv :: fvs) e
  | vlet : PartialForall c n fvs (
      let e' := Expr.abstract1 fv e
      if e'.hasLooseBVar' 0 then .letE x ty v e' false
      else e'.lowerLooseBVars' 1 1) →
    PartialForall (c.vlet fv x ty v ty' v') (n+1) (fv :: fvs) e
  | skip : e.looseBVarRange' = 0 → e' = Expr.abstract1 fv e → e'.hasLooseBVar' 0 = false →
    PartialForall c n fvs e →
    PartialForall (c.vlet fv x ty v ty' v') (n+1) fvs e

theorem MLCtx.PartialForall.full : MLCtx.PartialForall c n (c.fvarRevList n hn) e := by
  induction n generalizing c e with
  | zero => exact .nil
  | succ n ih => match c with | .vlam .. | .vlet .. => constructor; apply ih

theorem MLCtx.PartialForall.sublist (H : MLCtx.PartialForall c n l e) : l <+ c.vlctx.fvars := by
  induction H with
  | nil => simp
  | vlam _ ih | vlet _ ih => simp [ih]
  | skip _ _ _ _ ih => exact ih.trans (List.sublist_cons_self ..)

/-- Closedness of the let-binding step of the telescope model. -/
private theorem letStep_closed (hty : Closed ty) (hv : Closed v) (he : Closed e) :
    Closed (let e' := Expr.abstract1 fv e
      if e'.hasLooseBVar' 0 then .letE x ty v e' false else e'.lowerLooseBVars' 1 1) := by
  dsimp only
  split
  · exact ⟨hty, hv, he.abstract1⟩
  · rename_i h
    have h' : (Expr.abstract1 fv e).hasLooseBVar' 0 = false := by simpa using h
    rw [Expr.lowerLooseBVars_eq_instantiate h' (v := .sort .zero)]
    exact Closed.instantiate1 he.abstract1 trivial

theorem MLCtx.WF.mkForall_partial {c : MLCtx} (wf : c.WF env Us) (n hn)
    (harr : arr.toList.reverse = l.map .fvar) (hp : MLCtx.PartialForall c n l e)
    (he : Closed e) :
    c.lctx.mkForall arr e = c.mkForall n hn e := by
  have := congrArg (Array.mk ·.reverse) harr; simp at this
  rw [LocalContext.mkForall, this, ← List.map_reverse, LocalContext.mkBinding_eqN,
    LocalContext.mkBindingListN_eq_fold, List.foldr_reverse]
  · clear harr this
    induction hp with
    | nil => simp
    | vlam hp ih =>
      have hty := wf.2.2.1.closed; simp only [MLCtx.noBV] at hty
      simp
      refine (List.foldl_congr fun _ y h => ?_).trans <|
        .trans (congrFun (congrArg _ ?_) _) (ih wf.1 _ ⟨hty, he.abstract1⟩)
      · refine LocalContext.mkBindingList1N_congr ?_
        rw [wf.find?_eq, wf.1.find?_eq, decls, List.find?, (?_ : (y == _) = false)]
        simp [LocalDecl.fvarId]; rintro ⟨⟩
        have := (List.cons_sublist_cons.2 hp.sublist).nodup wf.fvars_nodup; simp_all
      · simp [LocalContext.mkBindingList1N, wf.find?_eq, decls, LocalDecl.fvarId,
          Expr.abstractN_nil, Expr.abstractN_singleton he.looseBVarRange_le]
    | vlet hp ih =>
      have hty := wf.2.2.1.closed; simp only [MLCtx.noBV] at hty
      have hv := wf.2.2.2.1.closed; simp only [MLCtx.noBV] at hv
      simp
      refine (List.foldl_congr fun _ y h => ?_).trans <|
        .trans (congrFun (congrArg _ ?_) _) (ih wf.1 _ (letStep_closed hty hv he))
      · refine LocalContext.mkBindingList1N_congr ?_
        rw [wf.find?_eq, wf.1.find?_eq, decls, List.find?, (?_ : (y == _) = false)]
        simp [LocalDecl.fvarId]; rintro ⟨⟩
        have := (List.cons_sublist_cons.2 hp.sublist).nodup wf.fvars_nodup; simp_all
      · simp [LocalContext.mkBindingList1N, wf.find?_eq, decls, LocalDecl.fvarId,
          Expr.abstractN_nil, Expr.abstractN_singleton he.looseBVarRange_le]
    | skip h1 h2 h3 hp ih =>
      subst h2; simp [h3]
      rw [Expr.lowerLooseBVars_eq_instantiate h3 (v := default),
        Expr.abstract1_eq_liftLooseBVars h3, Expr.liftLooseBVars_eq_self (by simp [h1]),
        Expr.instantiate1_eq_self h1]
      refine (List.foldl_congr fun _ y h => ?_).trans (ih wf.1 _ he)
      refine LocalContext.mkBindingList1N_congr ?_
      rw [wf.find?_eq, wf.1.find?_eq, decls, List.find?, (?_ : (y == _) = false)]
      simp [LocalDecl.fvarId]; rintro ⟨⟩
      have := (List.cons_sublist_cons.2 hp.sublist).nodup wf.fvars_nodup; simp_all
  · intro _ h
    exact wf.tr.find?_eq_some.2 (hp.sublist.subset (List.mem_reverse.1 h))
  · exact List.nodup_reverse.2 (hp.sublist.nodup wf.fvars_nodup)

theorem MLCtx.WF.mkForall_eq {c : MLCtx} (wf : c.WF env Us) (n hn)
    (harr : arr.toList.reverse = (c.fvarRevList n hn).map .fvar) (he : Closed e) :
    c.lctx.mkForall arr e = c.mkForall n hn e := mkForall_partial wf n hn harr .full he

theorem MLCtx.WF.mkLambda_eq {c : MLCtx} (wf : c.WF env Us) (n hn)
    (harr : arr.toList.reverse = (c.fvarRevList n hn).map .fvar) (he : Closed e) :
    c.lctx.mkLambda arr e = c.mkLambda n hn e := by
  have := congrArg (Array.mk ·.reverse) harr; simp at this
  rw [LocalContext.mkLambda, this, ← List.map_reverse, LocalContext.mkBinding_eqN,
    LocalContext.mkBindingListN_eq_fold, List.foldr_reverse]
  · clear harr this
    induction n generalizing c e with
    | zero => simp
    | succ n ih =>
      match c with
      | .vlam .. =>
        have hty := wf.2.2.1.closed; simp only [MLCtx.noBV] at hty
        simp
        refine (List.foldl_congr fun _ y h => ?_).trans <|
          .trans (congrFun (congrArg _ ?_) _) (ih wf.1 _ ⟨hty, he.abstract1⟩)
        · refine LocalContext.mkBindingList1N_congr ?_
          rw [wf.find?_eq, wf.1.find?_eq, decls, List.find?, (?_ : (y == _) = false)]
          simp [LocalDecl.fvarId]; rintro ⟨⟩
          have := wf.fvarRevList_nodup (n+1) hn; simp_all
        · simp [LocalContext.mkBindingList1N, wf.find?_eq, decls, LocalDecl.fvarId,
            Expr.abstractN_nil, Expr.abstractN_singleton he.looseBVarRange_le]
      | .vlet .. =>
        have hty := wf.2.2.1.closed; simp only [MLCtx.noBV] at hty
        have hv := wf.2.2.2.1.closed; simp only [MLCtx.noBV] at hv
        simp
        refine (List.foldl_congr fun _ y h => ?_).trans <|
          .trans (congrFun (congrArg _ ?_) _) (ih wf.1 _ (letStep_closed hty hv he))
        · refine LocalContext.mkBindingList1N_congr ?_
          rw [wf.find?_eq, wf.1.find?_eq, decls, List.find?, (?_ : (y == _) = false)]
          simp [LocalDecl.fvarId]; rintro ⟨⟩
          have := wf.fvarRevList_nodup (n+1) hn; simp_all
        · simp [LocalContext.mkBindingList1N, wf.find?_eq, decls, LocalDecl.fvarId,
            Expr.abstractN_nil, Expr.abstractN_singleton he.looseBVarRange_le]
  · intro _ h
    exact wf.tr.find?_eq_some.2 ((MLCtx.fvarRevList_prefix ..).subset (List.mem_reverse.1 h))
  · exact List.nodup_reverse.2 (wf.fvarRevList_nodup ..)

theorem MLCtx.WF.mkForall_closed {c : MLCtx} (wf : c.WF env Us) (n hn) (he : Closed e) :
    Closed (c.mkForall n hn e) := by
  induction n generalizing c e with
  | zero => exact he
  | succ n ih =>
    match c with
    | .vlam .. =>
      have hty := wf.2.2.1.closed; simp only [MLCtx.noBV] at hty
      exact ih wf.1 _ ⟨hty, he.abstract1⟩
    | .vlet .. =>
      have hty := wf.2.2.1.closed; simp only [MLCtx.noBV] at hty
      have hv := wf.2.2.2.1.closed; simp only [MLCtx.noBV] at hv
      exact ih wf.1 _ (letStep_closed hty hv he)

namespace Inner

theorem whnf.WF {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (whnf e) fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' :=
  fun _ wf => wf.whnf he

theorem whnf.WF_forallE {c : VContext} {s : State} (he : c.TrExprS e (.forallE A B)) :
    RecM.WF c s (whnf e) fun e₁ _ => c.TrExprS e₁ (.forallE A B) :=
  fun _ wf => wf.whnf_forallE he

/-- Both `whnf` clauses at once. -/
theorem whnf.WF' {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (whnf e) fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' ∧
      (∀ A B, e' = .forallE A B → c.TrExprS e₁ e') := by
  by_cases h : ∃ A B, e' = .forallE A B
  · obtain ⟨A, B, rfl⟩ := h
    exact ((whnf.WF he).and (whnf.WF_forallE he)).mono fun _ _ _ ⟨⟨h1, h2⟩, h3⟩ =>
      ⟨h1, h2, fun _ _ _ => h3⟩
  · exact (whnf.WF he).mono fun _ _ _ ⟨h1, h2⟩ => ⟨h1, h2, fun _ _ hAB => (h ⟨_, _, hAB⟩).elim⟩

theorem envGet.WF {c : VContext} :
    (c.env.get name).WF fun ci => c.env.find? name = some ci := by
  simp [Environment.get]; split <;> [refine .pure ‹_›; exact .throw]

theorem isDefEqCore.WF {c : VContext} {s : State}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' :=
  fun _ wf => wf.isDefEqCore he₁ he₂

theorem inferType.WF' {c : VContext} {s : State} (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    RecM.WF c s (inferType e inferOnly) fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty' :=
  fun _ wf => wf.inferType h1 hinf

/-- With the translation already in hand, `hinf` is satisfied whichever mode is used, so this
holds at both settings of `inferOnly`. -/
theorem inferType.WF {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (inferType e inferOnly) fun ty _ => ∃ ty', c.TrTyping e ty e' ty' := by
  refine .stateWF fun wf => ?_
  refine (inferType.WF' he.fvarsIn fun _ => ⟨_, he⟩).le
    fun _ _ _ ⟨_, _, h1, h2, h3, h4⟩ => ⟨_, h1, he, h3, ?_⟩
  have := h2.uniq c.Ewf (.refl c.Ewf c.Δwf) he
  exact h4.defeqU_l c.Ewf c.Δwf this

theorem inferType.WF_uniq {c : VContext} {s : State}
    (he : c.TrExprS e e') (hty : c.HasType e' ty') :
    RecM.WF c s (inferType e true) fun ty _ => c.TrExpr ty ty' :=
  (inferType.WF he).le fun _ _ _ ⟨_, _, _, h1, h2⟩ =>
  ⟨_, h1, h2.uniqU c.Ewf c.Δwf hty⟩

theorem checkType.WF {c : VContext} {s : State} (h1 : e.FVarsIn (· ∈ c.vlctx.fvars)) :
    RecM.WF c s (inferType e false) fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty' :=
  inferType.WF' h1 nofun

theorem whnfCore.WF {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (whnfCore e cheapProj) fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' :=
  fun _ wf => wf.whnfCore he

theorem whnfCore.WF_forallE {c : VContext} {s : State} (he : c.TrExprS e (.forallE A B)) :
    RecM.WF c s (whnfCore e cheapProj) fun e₁ _ => c.TrExprS e₁ (.forallE A B) :=
  fun _ wf => wf.whnfCore_forallE he

/-- Both `whnfCore` clauses at once. -/
theorem whnfCore.WF' {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (whnfCore e cheapProj) fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' ∧
      (∀ A B, e' = .forallE A B → c.TrExprS e₁ e') := by
  by_cases h : ∃ A B, e' = .forallE A B
  · obtain ⟨A, B, rfl⟩ := h
    exact ((whnfCore.WF he).and (whnfCore.WF_forallE he)).mono fun _ _ _ ⟨⟨h1, h2⟩, h3⟩ =>
      ⟨h1, h2, fun _ _ _ => h3⟩
  · exact (whnfCore.WF he).mono fun _ _ _ ⟨h1, h2⟩ =>
      ⟨h1, h2, fun _ _ hAB => (h ⟨_, _, hAB⟩).elim⟩

theorem whnfCore.WF_levels {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (whnfCore e cheapProj) fun e₁ _ => c.LevelsBelow e e₁ :=
  fun _ wf => wf.whnfCore_levels he

theorem whnf.WF_levels {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (whnf e) fun e₁ _ => c.LevelsBelow e e₁ :=
  fun _ wf => wf.whnf_levels he

theorem inferType.WF_levels_of_fvarsIn {c : VContext} {s : State} (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    RecM.WF c s (inferType e inferOnly) fun ty _ => c.LevelsBelow e ty :=
  fun _ wf => wf.inferType_levels h1 hinf

theorem inferType.WF_levels {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (inferType e inferOnly) fun ty _ => c.LevelsBelow e ty :=
  inferType.WF_levels_of_fvarsIn he.fvarsIn fun _ => ⟨_, he⟩

/-- `whnfCore` with its universe-parameter support. -/
theorem whnfCore.WF_below {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (whnfCore e cheapProj) fun e₁ _ =>
      c.FVarsBelow e e₁ ∧ c.LevelsBelow e e₁ ∧ c.TrExpr e₁ e' :=
  ((whnfCore.WF he).and (whnfCore.WF_levels he)).mono fun _ _ _ ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h3, h2⟩

/-- All three `whnfCore` clauses with its universe-parameter support. -/
theorem whnfCore.WF_below_of_fvarsIn {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (whnfCore e cheapProj) fun e₁ _ => (c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' ∧
      (∀ A B, e' = .forallE A B → c.TrExprS e₁ e')) ∧ c.LevelsBelow e e₁ :=
  (whnfCore.WF' he).and (whnfCore.WF_levels he)

/-- `whnf` with its universe-parameter support. -/
theorem whnf.WF_below {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (whnf e) fun e₁ _ => c.FVarsBelow e e₁ ∧ c.LevelsBelow e e₁ ∧ c.TrExpr e₁ e' :=
  ((whnf.WF he).and (whnf.WF_levels he)).mono fun _ _ _ ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h3, h2⟩

/-- All three `whnf` clauses with its universe-parameter support. -/
theorem whnf.WF_below_of_fvarsIn {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (whnf e) fun e₁ _ => (c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' ∧
      (∀ A B, e' = .forallE A B → c.TrExprS e₁ e')) ∧ c.LevelsBelow e e₁ :=
  (whnf.WF' he).and (whnf.WF_levels he)

/-- `inferType` with its universe-parameter support. -/
theorem inferType.WF_below_of_fvarsIn {c : VContext} {s : State} (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    RecM.WF c s (inferType e inferOnly) fun ty _ =>
      (∃ e' ty', c.TrTyping e ty e' ty') ∧ c.LevelsBelow e ty :=
  (inferType.WF' h1 hinf).and (inferType.WF_levels_of_fvarsIn h1 hinf)

/-- `inferType` with its universe-parameter support. -/
theorem inferType.WF_below {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (inferType e inferOnly) fun ty _ =>
      (∃ ty', c.TrTyping e ty e' ty') ∧ c.LevelsBelow e ty :=
  (inferType.WF he).and (inferType.WF_levels he)

/-! ### The parameter-uniformity clauses of the methods -/

theorem whnfCore.WF_paramUniform {c : VContext} {s : State} (he : c.TrExprS e e')
    (hp : s.ngen.namePrefix = pfx) :
    RecM.WF c s (whnfCore e cheapProj) fun e₁ _ => c.ParamUniformBelow pfx e e₁ :=
  fun _ wf => hp ▸ wf.whnfCore_paramUniform he

theorem whnf.WF_paramUniform {c : VContext} {s : State} (he : c.TrExprS e e')
    (hp : s.ngen.namePrefix = pfx) :
    RecM.WF c s (whnf e) fun e₁ _ => c.ParamUniformBelow pfx e e₁ :=
  fun _ wf => hp ▸ wf.whnf_paramUniform he

theorem inferType.WF_paramUniform {c : VContext} {s : State} (he : c.TrExprS e e')
    (hp : s.ngen.namePrefix = pfx) :
    RecM.WF c s (inferType e) fun ty _ => c.ParamUniformTyBelow pfx e ty :=
  fun _ wf => hp ▸ wf.inferType_paramUniform he

theorem whnfCore.WF_const {c : VContext} {s : State} :
    RecM.WF c s (whnfCore (.const n us) cheapProj) fun e₁ _ => e₁ = .const n us :=
  fun _ wf => wf.whnfCore_const

theorem whnf.WF_forall {c : VContext} {s : State} :
    RecM.WF c s (whnf (.forallE n t b bi)) fun e₁ _ => e₁ = .forallE n t b bi :=
  fun _ wf => wf.whnf_forall_eq

/-- `whnfCore` with its free-variable and parameter-uniformity clauses. -/
theorem whnfCore.WF_and_paramUniform {c : VContext} {s : State} (he : c.TrExprS e e')
    (hp : s.ngen.namePrefix = pfx) :
    RecM.WF c s (whnfCore e cheapProj) fun e₁ _ =>
      (c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e') ∧ c.ParamUniformBelow pfx e e₁ :=
  (whnfCore.WF he).and (whnfCore.WF_paramUniform he hp)

/-- `whnf` with its free-variable and parameter-uniformity clauses. -/
theorem whnf.WF_and_paramUniform {c : VContext} {s : State} (he : c.TrExprS e e')
    (hp : s.ngen.namePrefix = pfx) :
    RecM.WF c s (whnf e) fun e₁ _ => (c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e') ∧ c.ParamUniformBelow pfx e e₁ :=
  (whnf.WF he).and (whnf.WF_paramUniform he hp)

/-- `inferType` with its typing and parameter-uniformity clauses. -/
theorem inferType.WF_and_paramUniform {c : VContext} {s : State} (he : c.TrExprS e e')
    (hp : s.ngen.namePrefix = pfx) :
    RecM.WF c s (inferType e) fun ty _ =>
      (∃ ty', c.TrTyping e ty e' ty') ∧ c.ParamUniformTyBelow pfx e ty :=
  (inferType.WF he).and (inferType.WF_paramUniform he hp)

/-- The prefix of the name generator is constant along a run. -/
theorem State.LE.namePrefix_eq {s₀ s : State} (hp : s₀.ngen.namePrefix = pfx) (le : s₀ ≤ s) :
    s.ngen.namePrefix = pfx := le.namePrefix ▸ hp

/-- An expression translating to a `forallE` is neither an application nor a constant. -/
theorem _root_.Lean4Lean.TrExprS.forallE_shape
    (H : TrExprS env Us Δ e (.forallE A B)) : e.isApp = false ∧ ∀ n ls, e ≠ .const n ls := by
  cases H with
  | lit hl h =>
    rename_i l
    cases l with
    | natVal n =>
      cases n <;> simp [Literal.toConstructor, Expr.natLitToConstructor, Expr.natZero,
        Expr.natSucc] at h <;> cases h
    | strVal s =>
      simp [Literal.toConstructor, Expr.strLitToConstructor] at h; cases h
  | _ => simp [Expr.isApp]

theorem unfoldDefinition_eq_none (h1 : e.isApp = false) (h2 : ∀ n ls, e ≠ .const n ls) :
    unfoldDefinition e = pure none := by
  unfold unfoldDefinition; simp only [h1, Bool.false_eq_true, ↓reduceIte]
  unfold unfoldDefinitionCore; split
  · exact absurd rfl (h2 _ _)
  · rfl

theorem isDelta_is_some : isDelta env e = some ci ↔
    ∃ n, env.find? n = some ci ∧ (∃ v, ci.deltaValue? = some v) ∧
      ∃ ls, e.getAppFn = .const n ls ∧ ls.length = ci.numLevelParams := by
  simp only [isDelta]
  split <;> [split <;> [split; skip]; skip] <;>
    simp_all [Option.isSome_iff_exists] <;> grind

def UnfoldDefinition.WF (c : VContext) (e e₀ : Expr) (e' : VExpr) : Option Expr → Prop
  | some e₁ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e'
  | none => ∀ {{n ci v ls}}, c.env.find? n = some ci → ci.deltaValue? = some v →
    e₀ = .const n ls → ls.length = ci.numLevelParams → False

theorem unfoldDefinitionCore.WF {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (unfoldDefinitionCore e) fun oe _ => UnfoldDefinition.WF c e e e' oe := by
  dsimp [unfoldDefinitionCore]
  split <;> [refine .getEnv ?_; (rename_i H; exact .pure fun _ _ _ _ _ _ h => nomatch H _ _ h)]
  split; rotate_left
  · rename_i H; refine .pure ?_; rintro _ _ _ _ h1 h2 ⟨⟩ hlen
    cases H _ (isDelta_is_some.2 ⟨_, h1, ⟨_, h2⟩, _, rfl, hlen⟩)
  rename_i n ls oci ci h1
  obtain ⟨_, h3, ⟨_, h4⟩, _, ⟨⟩, hlen⟩ := isDelta_is_some.1 h1
  have : UnfoldDefinition.WF c (.const n ls) (.const n ls) e'
      (some (instantiateDeltaValue ci ls)) := by
    let .const a1 a2 a3 := he
    have ⟨rfl, b1, b2, b3⟩ := c.trenv.find?_uniq h3 a1
    simp [instantiateDeltaValue, h4]
    have c1 := c.trenv.of_value h3 b1 h4 |>.instL c.Ewf (by trivial) a2 (b2.trans a3.symm)
    have := c1.weakFV c.Ewf (.from_nil c.mlctx.noBV) c.Δwf
    rw [c1.wf.closedN c.Ewf trivial |>.liftN_eq (Nat.zero_le _)] at this
    simp [VExpr.instL] at this; rw [VLevel.inst_map_id] at this
    · exact ⟨fun _ _ _ => c1.fvarsIn.mono nofun, this⟩
    · exact (List.mapM_eq_some.1 a2).length_eq.symm.trans <| a3.trans b2.symm
  split <;> [rename_i h5; exact .pure this]
  refine .pureBind <| .get ?_
  split <;> [rename_i eq; skip]
  · refine .stateWF fun wf => .pure ?_
    obtain ⟨_, _, _, ⟨⟩, a1, rfl⟩ := wf.unfold_wf eq
    cases h3.symm.trans a1; exact this
  · refine .bind (Q := fun _ _ => True) ?_ fun _ _ _ _ => .pure this
    rintro _ mwf wf _ _ ⟨⟩
    refine ⟨_, rfl, .rfl, { wf with unfold_wf := ?_ }, ⟨⟩⟩
    intro e e'; simp only [Std.HashMap.getElem?_insert]
    split <;> [rintro ⟨⟩; exact (wf.unfold_wf ·)]
    rename_i eq; rw [BEq.comm, Expr.eqv_const] at eq
    exact ⟨_, _, _, eq, h3, rfl⟩

theorem unfoldDefinition.WF {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (unfoldDefinition e) fun oe _ => UnfoldDefinition.WF c e e.getAppFn e' oe := by
  simp [unfoldDefinition]; split; rotate_left
  · rename_i h; refine (unfoldDefinitionCore.WF he).mono fun _ _ _ H => ?_
    rwa [show e.getAppFn = e by revert h; unfold Expr.isApp Expr.getAppFn; split <;> simp]
  have ⟨f', stk⟩ := AppStack.build (e.mkAppList_getAppArgsList ▸ he)
  refine (unfoldDefinitionCore.WF stk.tr).bind fun oe _ _ H => ?_
  cases oe <;> [exact .pure H; refine .pure ?_]
  have ⟨h1, h2⟩ := H
  rw [Expr.mkAppRevRange_eq (l₁ := []) (l₂ := e.getAppArgsRevList) (l₃ := [])
    (by simp [Expr.getAppRevArgs_toList]) (by rfl) (by simp [Expr.getAppRevArgs_eq])]
  simp only [Expr.getAppArgsRevList_reverse]; constructor
  · exact (e.mkAppList_getAppArgsList ▸ h1.mkAppList :)
  · exact h2.rebuild_mkAppList c.Ewf c.Δwf stk.tr (e.mkAppList_getAppArgsList ▸ he :)

theorem ensureSortCore.WF {c : VContext} {s : State} (he : c.TrExprS e e') :
    RecM.WF c s (ensureSortCore e e₀) fun e1 _ =>
      (∃ u, e1 = .sort u) ∧ c.TrExpr e1 e' ∧ c.FVarsBelow e e1 := by
  simp [ensureSortCore]; split
  · let .sort _ := e
    exact .pure ⟨⟨_, rfl⟩, he.trExpr c.Ewf c.Δwf, .rfl⟩
  refine (whnf.WF he).bind fun e _ _ ⟨hb, he⟩ => ?_; split
  · let .sort _ := e
    exact .pure ⟨⟨_, rfl⟩, he, hb⟩
  exact .getEnv <| .getLCtx .throw
