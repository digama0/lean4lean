import Lean4Lean.Theory.VEnv

namespace Lean4Lean
open Lean4Lean

inductive Lookup : List VExpr → Nat → VExpr → Prop where
  | zero : Lookup (ty::Γ) 0 ty.lift
  | succ : Lookup Γ n ty → Lookup (A::Γ) (n+1) ty.lift

namespace VEnv

section
set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:30 => IsDefEq Γ e e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:30 => IsDefEq Γ e1 e2 A
variable (env : VEnv) (uvars : Nat)

inductive IsDefEq : List VExpr → VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  | sortDF :
    l.WF uvars → l'.WF uvars → l ≈ l' →
    Γ ⊢ .sort l ≡ .sort l' : .sort (.succ l)
  | constDF :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF uvars) →
    (∀ l ∈ ls', l.WF uvars) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    Γ ⊢ .const c ls ≡ .const c ls' : ci.type.instL ls
  /-- Abstract case symbols are typed from their declaration-derived schema,
  with permission checked at the occurrence's specialized universes. -/
  | elimDF {schema : InductiveSignature.CaseSchema}
      {owner : Fin schema.signature.families.size} :
    env.eliminators block schema →
    schema.genericType owner = some type →
    type.Closed →
    schema.Permission uvars owner levels target →
    (∀ level ∈ target' :: levels', level.WF uvars) →
    List.Forall₂ (· ≈ ·) (target :: levels) (target' :: levels') →
    Γ ⊢ type.instL (target :: levels) : .sort typeLevel →
    Γ ⊢ .elim block owner.val (target :: levels) ≡
      .elim block owner.val (target' :: levels') : type.instL (target :: levels)
  | appDF :
    Γ ⊢ f ≡ f' : .forallE A B →
    Γ ⊢ a ≡ a' : A →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | projDF :
    env.projections typeName info →
    (∀ l ∈ levels, l.WF uvars) →
    levels.length = info.uvars →
    params.length = info.nparams →
    indexArgs.length = info.nindices →
    info.fieldType typeName levels params index sourceMajor = some fieldType →
    Γ ⊢ fieldType : .sort fieldLevel →
    Γ ⊢ sourceMajor ≡ major :
      VExpr.mkApps (.const typeName levels) (params ++ indexArgs) →
    Γ ⊢ sourceMajor ≡ major' :
      VExpr.mkApps (.const typeName levels) (params ++ indexArgs) →
    info.ctorType.Closed →
    (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero →
    Γ ⊢ .proj typeName index major ≡
      .proj typeName index major' : fieldType
  | lamDF :
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF :
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta :
    A::Γ ⊢ e : B → Γ ⊢ e' : A →
    Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta :
    Γ ⊢ e : .forallE A B →
    Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel :
    Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p →
    Γ ⊢ h ≡ h' : p
  | extra :
    env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
    Γ ⊢ df.lhs.instL ls ≡ df.rhs.instL ls : df.type.instL ls
  /-- Only the same schema's generated case equations may reduce an abstract
  eliminator. Their endpoints retain explicit typing premises. -/
  | elimIota {schema : InductiveSignature.CaseSchema}
      {owner : Fin schema.signature.families.size} :
    env.eliminators block schema →
    schema.genericEquations block owner = some rules →
    df ∈ rules →
    InductiveSignature.CaseSchema.RuleClosed df →
    schema.Permission uvars owner levels target →
    Γ ⊢ df.lhs.instL (target :: levels) : df.type.instL (target :: levels) →
    Γ ⊢ df.rhs.instL (target :: levels) : df.type.instL (target :: levels) →
    Γ ⊢ df.lhs.instL (target :: levels) ≡ df.rhs.instL (target :: levels) :
      df.type.instL (target :: levels)
  | projIota :
    env.projections typeName info →
    Γ ⊢ .proj typeName index (VExpr.mkApps (.const info.ctorName levels) args) : fieldType →
    args[info.nparams + index]? = some field →
    Γ ⊢ field : fieldType →
    Γ ⊢ .proj typeName index (VExpr.mkApps (.const info.ctorName levels) args) ≡ field :
      fieldType
  | structEta :
    env.projections typeName info →
    params.length = info.nparams →
    info.nindices = 0 →
    Γ ⊢ e : VExpr.mkApps (.const typeName levels) params →
    Γ ⊢ VExpr.mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index => .proj typeName index e) :
      VExpr.mkApps (.const typeName levels) params →
    Γ ⊢ VExpr.mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index => .proj typeName index e) ≡ e :
      VExpr.mkApps (.const typeName levels) params
  | unitLike :
    env.projections typeName info →
    params.length = info.nparams →
    info.nindices = 0 →
    info.numFields = 0 →
    Γ ⊢ e : VExpr.mkApps (.const typeName levels) params →
    Γ ⊢ e' : VExpr.mkApps (.const typeName levels) params →
    Γ ⊢ e ≡ e' : VExpr.mkApps (.const typeName levels) params

end

def HasType (env : VEnv) (U : Nat) (Γ : List VExpr) (e A : VExpr) : Prop :=
  IsDefEq env U Γ e e A

def IsType (env : VEnv) (U : Nat) (Γ : List VExpr) (A : VExpr) : Prop :=
  ∃ u, env.HasType U Γ A (.sort u)

def IsDefEqU (env : VEnv) (U : Nat) (Γ : List VExpr) (e₁ e₂ : VExpr) :=
  ∃ A, env.IsDefEq U Γ e₁ e₂ A

variable (env : VEnv) (U : Nat) (Γ₀ : List VExpr) in
/-- Pointwise definitional equality of two local contexts over a common
base `Γ₀`. -/
inductive IsDefEqCtx : List VExpr → List VExpr → Prop
  | zero : IsDefEqCtx Γ₀ Γ₀
  | succ :  IsDefEqCtx Γ₁ Γ₂ → env.IsDefEq U Γ₁ A₁ A₂ (.sort u) → IsDefEqCtx (A₁ :: Γ₁) (A₂ :: Γ₂)

end VEnv

def VExpr.WF (env : VEnv) (U : Nat) (Γ : List VExpr) (e : VExpr) := env.IsDefEqU U Γ e e

def VConstant.WF (env : VEnv) (ci : VConstant) : Prop := env.IsType ci.uvars [] ci.type

def VDefEq.WF (env : VEnv) (df : VDefEq) : Prop :=
  env.HasType df.uvars [] df.lhs df.type ∧ env.HasType df.uvars [] df.rhs df.type
