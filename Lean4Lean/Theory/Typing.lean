import Lean4Lean.Theory.VEnv

namespace Lean4Lean

open Lean (Name FVarId)

inductive Lookup : List VExpr → Nat → VExpr → Prop where
  | zero : Lookup (ty::Γ) 0 ty.lift
  | succ : Lookup Γ n ty → Lookup (ty::Γ) (n+1) ty.lift

variable
  (constants : Name → Option (Option VConstant))
  (IsDefEq : List VExpr → VExpr → VExpr → Prop)
  (uvars : Nat) in
inductive HasType1 : List VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup Γ i ty → HasType1 Γ (.bvar i) ty
  | sort : l.WF uvars → HasType1 Γ (.sort l) (.sort (.succ l))
  | const :
    constants c = some (some ci) →
    (∀ l ∈ ls, l.WF uvars) →
    ls.length = ci.uvars →
    HasType1 Γ (.const c ls) (ci.type.instL ls)
  | app :
    HasType1 Γ f (.forallE A B) →
    HasType1 Γ a A →
    HasType1 Γ (.app f a) (B.inst a)
  | lam :
    HasType1 Γ A (.sort u) →
    HasType1 (A::Γ) body B →
    HasType1 Γ (.lam A body) (.forallE A B)
  | forallE :
    HasType1 Γ A (.sort u) →
    HasType1 (A::Γ) B (.sort v) →
    HasType1 Γ (.forallE A B) (.sort (.imax u v))
  | defeq : IsDefEq Γ A B → HasType1 Γ e A → HasType1 Γ e B

variable
  (defeqs : VDefEq → Prop)
  (HasType : List VExpr → VExpr → VExpr → Prop) in
inductive IsDefEq1 : List VExpr → VExpr → VExpr → Prop where
  | refl :
    HasType Γ e A → IsDefEq1 Γ e e
  | symm :
    IsDefEq1 Γ e e' → IsDefEq1 Γ e' e
  | trans :
    IsDefEq1 Γ e₁ e₂ → IsDefEq1 Γ e₂ e₃ → IsDefEq1 Γ e₁ e₃
  | sort :
    l ≈ l' → IsDefEq1 Γ (.sort l) (.sort l')
  | app :
    HasType Γ f (.forallE A B) → HasType Γ f' (.forallE A B) → IsDefEq1 Γ f f' →
    HasType Γ a A → HasType Γ a' A → IsDefEq1 Γ a a' →
    IsDefEq1 Γ (.app f a) (.app f' a')
  | lam :
    IsDefEq1 Γ A A' →
    IsDefEq1 (A::Γ) body body' →
    IsDefEq1 Γ (.lam A body) (.lam A' body')
  | forallE :
    IsDefEq1 Γ A A' →
    IsDefEq1 (A::Γ) body body' →
    IsDefEq1 Γ (.forallE A body) (.forallE A' body')
  | beta :
    HasType (A::Γ) e B → HasType Γ e' A →
    IsDefEq1 Γ (.app (.lam A e) e') (e.inst e')
  | eta :
    HasType Γ e (.forallE A B) →
    IsDefEq1 Γ (.lam A (.app e.lift (.bvar 0))) e
  | proofIrrel :
    HasType Γ p (.sort .zero) → HasType Γ h p → HasType Γ h' p →
    IsDefEq1 Γ h h'
  | extra :
    defeqs df →
    (∀ l ∈ ls, l.WF uvars) →
    ls.length = df.uvars →
    IsDefEq1 [] (df.lhs.instL ls) (df.rhs.instL ls)

variable (env : VEnv) (uvars : Nat) in
def HasTypeN : Nat → List VExpr → VExpr → VExpr → Prop
  | 0 => fun _ _ _ => False
  | n+1 => HasType1 env.constants (IsDefEq1 env.defeqs (HasTypeN n)) uvars

def IsDefEqN (env : VEnv) (uvars : Nat) (n : Nat) : List VExpr → VExpr → VExpr → Prop :=
  IsDefEq1 env.defeqs (HasTypeN env uvars n)

def HasType (env : VEnv) (uvars : Nat) (Γ : List VExpr) (e A : VExpr) : Prop :=
  ∃ n, HasTypeN env uvars n Γ e A

def IsDefEq (env : VEnv) (uvars : Nat) (Γ : List VExpr) (e A : VExpr) : Prop :=
  ∃ n, IsDefEqN env uvars n Γ e A

def IsType (env : VEnv) (uvars : Nat) (Γ : List VExpr) (A : VExpr) : Prop :=
  ∃ u, HasType env uvars Γ A (.sort u)

theorem HasType.type_isType (h : HasType E U Γ e A) : IsType E U Γ A := sorry

theorem HasType.isDefEq_hasType (h : IsDefEq E U Γ e e') :
    ∃ A, HasType E U Γ e A ∧ HasType E U Γ e' A := sorry
