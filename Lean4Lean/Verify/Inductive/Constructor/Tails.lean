import Lean4Lean.Verify.Inductive.Constructor.CheckedFormation
import Lean4Lean.Verify.Expr.Telescope

/-! # The concrete constructor telescopes retained by the constructor check

The recursor construction re-walks the kernel constructor types (`mkRecInfos`) with the cached
common parameters, so it needs the concrete telescopes the constructor check established, not
only their abstract shapes: the replay of the parameter prefix (`ParameterPrefix`), the syntactic
forall spine (`Expr.ForallSpine`), the checked tail with its translation and certificate
(`ConstructorTails`) and the owner normal form (`ConstructorOwnerNormalForms`). These are the
source branch's definitions (`Recursor/Context/RecInfoTraversal.lean`,
`Recursor/Binders/ParameterPrefixes.lean`, `Recursor/Context/FVarArrays.lean`,
`Constructor/Positivity.lean`), produced by the constructor phase and recorded in
`ConstructorCheck`. The source branch's `checkInductiveTypes.loopType.ScopedHeaderTelescope`
is named `ConstructorScopedTelescope` here. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Syntactic forall spine of a constructor type exactly as walked by the
executable constructor check: `k` leading `forallE` binders followed by a
constant-headed codomain.  No `mdata` or `letE` sits on the spine. -/
inductive Expr.ForallSpine : Expr → Nat → Prop
  | codomain {e : Expr} {name : Name} {levels : List Level}
      (hhead : e.getAppFn = .const name levels) : ForallSpine e 0
  | step {name : Name} {dom body : Expr} {bi : BinderInfo} {k : Nat}
      (H : ForallSpine body k) : ForallSpine (.forallE name dom body bi) (k + 1)

/-- Substituting a free variable cannot create a constant application head. -/
theorem Expr.getAppFn_instantiate1'_const
    {e : Expr} {fv : FVarId} {d : Nat} {name : Name} {levels : List Level}
    (H : (e.instantiate1' (.fvar fv) d).getAppFn = .const name levels) :
    e.getAppFn = .const name levels := by
  induction e generalizing d with
  | app f a ihf _ =>
    simp only [Expr.instantiate1', Expr.getAppFn] at H ⊢
    exact ihf H
  | bvar i =>
    simp only [Expr.instantiate1'] at H
    split at H
    · simp [Expr.getAppFn] at H
    · split at H
      · simp [Expr.liftLooseBVars', Expr.getAppFn] at H
      · simp [Expr.getAppFn] at H
  | const _ _ => simpa [Expr.instantiate1'] using H
  | fvar _ | mvar _ | sort _ | lit _ | mdata _ _ _ | proj _ _ _ _
  | lam _ _ _ _ _ _ | forallE _ _ _ _ _ _ | letE _ _ _ _ _ _ _ _ =>
    simp [Expr.instantiate1', Expr.getAppFn] at H

/-- Substituting a free variable cannot create a forall binder. -/
theorem Expr.instantiate1'_fvar_forallE_inv
    {e : Expr} {fv : FVarId} {d : Nat} {name : Name} {dom body : Expr}
    {bi : BinderInfo}
    (H : e.instantiate1' (.fvar fv) d = .forallE name dom body bi) :
    ∃ dom' body', e = .forallE name dom' body' bi ∧
      dom = dom'.instantiate1' (.fvar fv) d ∧
      body = body'.instantiate1' (.fvar fv) (d + 1) := by
  cases e with
  | forallE name' dom' body' bi' =>
    simp only [Expr.instantiate1', Expr.forallE.injEq] at H
    rcases H with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨dom', body', rfl, rfl, rfl⟩
  | bvar i =>
    simp only [Expr.instantiate1'] at H
    split at H
    · cases H
    · split at H
      · simp [Expr.liftLooseBVars'] at H
      · cases H
  | const _ _ | fvar _ | mvar _ | sort _ | lit _ | mdata _ _ | proj _ _ _
  | lam _ _ _ _ | app _ _ | letE _ _ _ _ _ =>
    simp [Expr.instantiate1'] at H

theorem Expr.ForallSpine.of_instantiate1'_fvar
    {e : Expr} {fv : FVarId} {d k : Nat}
    (H : ForallSpine (e.instantiate1' (.fvar fv) d) k) : ForallSpine e k := by
  generalize he : e.instantiate1' (.fvar fv) d = e' at H
  induction H generalizing e d with
  | codomain hhead =>
    subst he
    exact .codomain (Expr.getAppFn_instantiate1'_const hhead)
  | step _ ih =>
    rcases Expr.instantiate1'_fvar_forallE_inv he with ⟨dom', body', rfl, _, hb⟩
    exact .step (ih hb.symm)

theorem AddInductive.constructorArity_eq_zero_of_not_forallE
    {e : Expr} (h : ∀ name dom body bi, e ≠ .forallE name dom body bi) :
    AddInductive.constructorArity e = 0 := by
  cases e with
  | forallE name dom body bi => exact absurd rfl (h name dom body bi)
  | _ => rfl

/-- The executable field count of a pure forall spine is its binder count. -/
theorem Expr.ForallSpine.constructorArity {e : Expr} {k : Nat}
    (H : Expr.ForallSpine e k) : AddInductive.constructorArity e = k := by
  induction H with
  | codomain hhead =>
    apply AddInductive.constructorArity_eq_zero_of_not_forallE
    intro name dom body bi he
    subst he
    simp [Expr.getAppFn] at hhead
  | step _ ih => simp [AddInductive.constructorArity, ih]

/-- The translation of a constant-headed application is not a binder. -/
theorem TrExprS.forallArity_eq_zero_of_const_head {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {e : Expr} {e' : VExpr} {name : Name} {levels : List Level}
    (H : TrExprS env Us Δ e e') (hhead : e.getAppFn = .const name levels) :
    e'.forallArity = 0 := by
  cases e with
  | const => cases H; rfl
  | app => cases H; rfl
  | _ => simp [Expr.getAppFn] at hhead

/-- Translation preserves the binder count of a pure forall spine. -/
theorem TrExprS.forallArity_of_spine {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {e : Expr} {e' : VExpr} {k : Nat}
    (Hspine : Expr.ForallSpine e k) (H : TrExprS env Us Δ e e') : e'.forallArity = k := by
  induction Hspine generalizing Δ e' with
  | codomain hhead => exact TrExprS.forallArity_eq_zero_of_const_head H hhead
  | step _ ih =>
    cases H with
    | forallE _ _ _ hbody => simp [VExpr.forallArity, ih hbody]

/-- Exact concrete common-parameter prefix used by recursor generation. -/
inductive ParameterPrefix (stats : AddInductive.InductiveStats) :
    Nat → Expr → Expr → Prop
  | done : i = stats.params.size → ParameterPrefix stats i tail tail
  | step : stats.params[i]? = some param →
      ParameterPrefix stats (i + 1) (body.instantiate1 param) tail →
      ParameterPrefix stats i (.forallE name dom body bi) tail

/-- Replaying the cached parameter prefix is deterministic. -/
theorem ParameterPrefix.tail_eq
    (Hleft : ParameterPrefix stats i source left)
    (Hright : ParameterPrefix stats i source right) : left = right := by
  induction Hleft with
  | done hi =>
    cases Hright with
    | done => rfl
    | step hparam _ =>
      have hnone : stats.params[stats.params.size]? = none :=
        Array.getElem?_eq_none (by omega)
      rw [hi, hnone] at hparam
      contradiction
  | @step i param body left dom name bi hparam Hleft ih =>
    cases Hright with
    | done hi =>
      have hnone : stats.params[stats.params.size]? = none :=
        Array.getElem?_eq_none (by omega)
      rw [hi, hnone] at hparam
      contradiction
    | step hparam' Hright =>
      have heq : param = _ := Option.some.inj (hparam.symm.trans hparam')
      subst_vars
      exact ih Hright

/-- A pure forall spine of the cached-parameter tail extends to the closed
constructor type: the instantiated parameters are free variables, which cannot
alter the binder structure. -/
theorem ParameterPrefix.forallSpine
    (H : ParameterPrefix stats i source tail)
    (hfv : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv)
    (hspine : Expr.ForallSpine tail k) :
    Expr.ForallSpine source (stats.params.size - i + k) := by
  induction H with
  | done hi =>
    subst hi
    simpa using hspine
  | @step i param body tail name dom bi hparam _ ih =>
    have hi : i < stats.params.size :=
      (Array.getElem?_eq_some_iff.mp hparam).1
    rcases hfv param (Array.mem_of_getElem? hparam) with ⟨fv, rfl⟩
    have hbody := ih hspine
    rw [Expr.instantiate1_eq] at hbody
    have hbody' := Expr.ForallSpine.of_instantiate1'_fvar hbody
    have heq : stats.params.size - i + k =
        stats.params.size - (i + 1) + k + 1 := by omega
    rw [heq]
    exact .step hbody'

/-- The spine count of a forall spine is determined. -/
theorem Expr.ForallSpine.unique (H₁ : Expr.ForallSpine e k₁) (H₂ : Expr.ForallSpine e k₂) :
    k₁ = k₂ := H₁.constructorArity.symm.trans H₂.constructorArity

/-- A partially instantiated common-parameter prefix.  Constructor checking
builds this left-to-right; when `stop = stats.params.size`, it is exactly the
complete prefix replay required by recursor generation. -/
inductive ParameterSegment (stats : AddInductive.InductiveStats) :
    Nat → Nat → Expr → Expr → Prop
  | done : ParameterSegment stats i i source source
  | step {i stop : Nat} {param body tail dom : Expr}
      {name : Name} {bi : BinderInfo} :
      stats.params[i]? = some param →
      ParameterSegment stats (i + 1) stop
        (body.instantiate1 param) tail →
      ParameterSegment stats i stop (.forallE name dom body bi) tail

theorem ParameterSegment.trans
    (H₁ : ParameterSegment stats start middle source current)
    (H₂ : ParameterSegment stats middle stop current tail) :
    ParameterSegment stats start stop source tail := by
  induction H₁ with
  | done => exact H₂
  | step hparam _ ih => exact .step hparam (ih H₂)

theorem ParameterSegment.push
    {body param dom : Expr} {name : Name} {bi : BinderInfo}
    (H : ParameterSegment stats start i source
      (.forallE name dom body bi))
    (hparam : stats.params[i]? = some param) :
    ParameterSegment stats start (i + 1) source
      (body.instantiate1 param) := by
  exact H.trans (.step hparam .done)

theorem ParameterSegment.complete
    (H : ParameterSegment stats start stop source tail)
    (hstop : stop = stats.params.size) :
    ParameterPrefix stats start source tail := by
  induction H with
  | done => exact .done hstop
  | step hparam _ ih => exact .step hparam (ih hstop)

/-- The comparisons performed while consuming the cached common parameters of a constructor
type: each source parameter domain translates in the current scope and is definitionally the
cached parameter type returned by the executable `isDefEq` call. -/
inductive CheckedConstructorParameterPrefix
    (env : VEnv) (Us : List Name) (stats : AddInductive.InductiveStats)
    (original : Expr) :
    Nat → Expr → VLCtx → List VExpr → Prop where
  | zero : CheckedConstructorParameterPrefix env Us stats original
      0 original [] []
  | step
      (H : CheckedConstructorParameterPrefix env Us stats original
        i (.forallE name dom body bi) scope sourceDomains)
      (hparam : stats.params[i]? = some param)
      (hparamFVar : param = .fvar fv)
      (hdomain : TrExprS env Us scope dom sourceDomain)
      (hdomainType : env.IsType Us.length scope.toCtx sourceDomain)
      (hcompare : env.IsDefEqU Us.length scope.toCtx
        sourceDomain paramType) :
      CheckedConstructorParameterPrefix env Us stats original
        (i + 1) (body.instantiate1 param)
        ((some (fv, deps), .vlam paramType) :: scope)
        (sourceDomains ++ [sourceDomain])

/-- What the constructor loop establishes about the parameter prefix of one executable
constructor: the prefix (`ParameterPrefix`) exists, and the checked type is a pure syntactic
forall spine. -/
def ConstructorParamPrefixAt (stats : AddInductive.InductiveStats) (ctor : Constructor) : Prop :=
  (∃ tail, ParameterPrefix stats 0 ctor.type tail) ∧ ∃ k, Expr.ForallSpine ctor.type k

/-- Parameter prefixes of every constructor, selected by family and
constructor positions. -/
structure ConstructorParameterPrefixes
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) : Prop where
  replay : ∀ (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
      (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length),
    ∃ tail, ParameterPrefix stats 0
      indTypes[familyIdx].ctors[ctorIdx].type tail
  /-- Every executable constructor type is a pure syntactic forall spine,
  as walked by the executable check. -/
  spines : ∀ (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
      (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length),
    ∃ k, Expr.ForallSpine indTypes[familyIdx].ctors[ctorIdx].type k

theorem ConstructorParameterPrefixes.ofAll
    {stats : AddInductive.InductiveStats} {indTypes : Array InductiveType}
    (H : ∀ (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
      (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length),
      ConstructorParamPrefixAt stats indTypes[familyIdx].ctors[ctorIdx]) :
    ConstructorParameterPrefixes stats indTypes where
  replay familyIdx hfamily ctorIdx hctor := (H familyIdx hfamily ctorIdx hctor).1
  spines familyIdx hfamily ctorIdx hctor := (H familyIdx hfamily ctorIdx hctor).2

/-- The constructor type as a header-telescope target. -/
def constructorTelescopeTarget (ctorVal : VConstVal) : VInductiveTypeSkeleton where
  toVConstVal := ctorVal
  ctors := []

/-- Definitional header synthesis of a constructor type in the cached parameter scope: the
header phase's `checkInductiveTypes.loopType.ScopedHeaderTelescope` at a constructor target. -/
abbrev ConstructorScopedTelescope (env : VEnv) (Us : List Name) (target : VInductiveTypeSkeleton)
    (scope : VLCtx) (current : VExpr) (i nindices : Nat) : Type :=
  checkInductiveTypes.loopType.ScopedHeaderTelescope env Us target scope current i nindices

/-- The checked parameter prefix and tail of one executable constructor, with the field
classification `classes` its positivity check returned. -/
def CheckedConstructorTailAt
    (env : VEnv) (Us : List Name) (scope : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (target : VInductiveType) (source : Constructor) (classes : List Bool) : Prop :=
  ∃ ctorVal tail tailTarget sourceDomains,
    ctorVal ∈ target.ctors ∧
    TrSourceConstRaw env Us source.name source.type ctorVal ∧
    ParameterPrefix stats 0 source.type tail ∧
    CheckedConstructorParameterPrefix env Us stats source.type
      stats.params.size tail scope sourceDomains ∧
    TrExprS env Us scope tail tailTarget ∧
    ConstructorTailCertificate env decl target scope.toCtx 0 tailTarget classes ∧
    Nonempty
      (ConstructorScopedTelescope env Us (constructorTelescopeTarget ctorVal) scope tailTarget
        stats.params.size 0)

/-- The checked parameter prefixes and tails (`CheckedConstructorTailAt`) of all
constructors `ctors` of one family, with their field classifications `classes`. -/
def FamilyConstructorTails
    (env : VEnv) (Us : List Name) (scope : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (target : VInductiveType) (ctors : List Constructor)
    (classes : List (List Bool)) : Prop :=
  classes.length = ctors.length ∧
  ∀ i (hi : i < ctors.length),
    CheckedConstructorTailAt env Us scope stats decl target ctors[i] classes[i]!

/-- The checked tail of every constructor, by family and constructor position, with the
field classifications `classes` returned by the executable constructor check. -/
structure ConstructorTails
    (env : VEnv) (Us : List Name) (scope : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (indTypes : Array InductiveType) (classes : List (List (List Bool))) : Prop where
  size_eq : indTypes.size = decl.types.length
  classes_length : classes.length = indTypes.size
  row_length : ∀ (familyIdx : Nat), familyIdx < indTypes.size →
    classes[familyIdx]!.length = indTypes[familyIdx]!.ctors.length
  replay : ∀ (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
      (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length),
    CheckedConstructorTailAt env Us scope stats decl
      (decl.types[familyIdx]'(size_eq ▸ hfamily)) indTypes[familyIdx].ctors[ctorIdx]
      classes[familyIdx]![ctorIdx]!

theorem ConstructorTails.ofAll
    {env : VEnv} {Us : List Name} {scope : VLCtx}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {indTypes : Array InductiveType} {classes : List (List (List Bool))}
    (hsize : indTypes.size = decl.types.length)
    (hclasses : classes.length = indTypes.size)
    (H : ∀ (familyIdx : Nat) (hfamily : familyIdx < indTypes.size),
      FamilyConstructorTails env Us scope stats decl
        (decl.types[familyIdx]'(hsize ▸ hfamily)) indTypes[familyIdx].ctors
        classes[familyIdx]!) :
    ConstructorTails env Us scope stats decl indTypes classes where
  size_eq := hsize
  classes_length := hclasses
  row_length familyIdx hfamily := by
    rw [getElem!_pos indTypes familyIdx hfamily]
    exact (H familyIdx hfamily).1
  replay familyIdx hfamily ctorIdx hctor := (H familyIdx hfamily).2 ctorIdx hctor

/-- The owner normal form of a constructor type: its maximal forall telescope ends in a
valid application of family `targetIdx`. -/
structure ConstructorOwnerNormalForm
    (stats : AddInductive.InductiveStats) (targetIdx : Nat)
    (source : Expr) : Type where
  arity : Nat
  residual : Expr
  telescope : Expr.ForallTelescope source arity residual
  maximal : residual.isForall = false
  valid : AddInductive.isValidIndAppIdx stats residual targetIdx = true

/-- The owner normal form of the residual of a constructor's parameter prefix. -/
def ConstructorOwnerNormalFormAt
    (stats : AddInductive.InductiveStats) (targetIdx : Nat)
    (ctor : Constructor) : Prop :=
  ∃ tail,
    ParameterPrefix stats 0 ctor.type tail ∧
    Nonempty (ConstructorOwnerNormalForm stats targetIdx tail)

/-- The owner normal forms of every constructor of every family, indexed by the family
and constructor positions that `mkRecInfos` traverses. -/
structure ConstructorOwnerNormalForms
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) : Prop where
  replay : ∀ familyIdx (hfamily : familyIdx < indTypes.size)
      ctorIdx (hctor : ctorIdx < indTypes[familyIdx].ctors.length),
    ConstructorOwnerNormalFormAt stats familyIdx
      indTypes[familyIdx].ctors[ctorIdx]

end VerifyInductive
end Lean4Lean
