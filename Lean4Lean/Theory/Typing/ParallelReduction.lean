import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.NormalEq

inductive ReflTransGen (R : α → α → Prop) (a : α) : α → Prop where
  | zero : ReflTransGen R a a
  | trans : ReflTransGen R a b → R b c → ReflTransGen R a c

namespace Lean4Lean

open VExpr

def Extra := List VExpr → VExpr → VExpr → VExpr → VExpr → Prop

section
set_option hygiene false
local notation:65 Γ " ⊢ " e1 " ≫ " e2:30 => ParRed Γ e1 e2
variable (extra : Extra)

inductive ParRed : List VExpr → VExpr → VExpr → Prop where
  | bvar : Γ ⊢ .bvar i ≫ .bvar i
  | sort : Γ ⊢ .sort u ≫ .sort u
  | const : Γ ⊢ .const c ls ≫ .const c ls
  | app : Γ ⊢ f ≫ f' → Γ ⊢ a ≫ a' → Γ ⊢ .app f a ≫ .app f' a'
  | lam : Γ ⊢ A ≫ A' → A::Γ ⊢ body ≫ body' → Γ ⊢ .lam A body ≫ .lam A' body'
  | forallE : Γ ⊢ A ≫ A' → A::Γ ⊢ B ≫ B' → Γ ⊢ .forallE A B ≫ .forallE A' B'
  | beta : A::Γ ⊢ e₁ ≫ e₁' → Γ ⊢ e₂ ≫ e₂' → Γ ⊢ .app (.lam A e₁) e₂ ≫ e₁'.inst e₂'
  | extra : (∀ a a', extra Γ e e' a a' → Γ ⊢ a ≫ a') → Γ ⊢ e ≫ e'

end

theorem ParRed.rfl : ∀ {e}, ParRed E Γ e e
  | .bvar .. => .bvar
  | .sort .. => .sort
  | .const .. => .const
  | .app .. => .app rfl rfl
  | .lam .. => .lam rfl rfl
  | .forallE .. => .forallE rfl rfl

def Extra.IsWeakN (E : Extra) :=
  ∀ {{Γ e e' a a' Γ' n k}},
    Ctx.LiftN n k Γ Γ' → E Γ' (liftN n e k) (liftN n e' k) a a' →
    ∃ b b', E Γ e e' b b' ∧ a = liftN n b k ∧ a' = liftN n b' k

variable (HE : Extra.IsWeakN E) in
theorem ParRed.weakN (W : Ctx.LiftN n k Γ Γ') (H : ParRed E Γ e1 e2) :
    ParRed E Γ' (e1.liftN n k) (e2.liftN n k) := by
  induction H generalizing k Γ' with
  | bvar | sort | const => exact rfl
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | beta _ _ ih1 ih2 =>
    simp [liftN, liftN_inst_hi]
    exact .beta (ih1 W.succ) (ih2 W)
  | extra _ ih =>
    refine .extra fun a a' h => ?_
    obtain ⟨_, _, h', rfl, rfl⟩ := HE W h
    exact ih _ _ h' W

def Extra.IsInstN (E : Extra) :=
  E.IsWeakN ∧
  ∀ {{Γ₀ Γ₁ Γ A₀ k e1 e2 a1 a2 x1 x2}},
    Ctx.InstN Γ₀ a1 A₀ k Γ₁ Γ → E Γ (inst e1 a1 k) (inst e2 a2 k) x1 x2 →
    ∃ b1 b2, E Γ₁ e1 e2 b1 b2 ∧ x1 = inst b1 a1 k ∧ x2 = inst b2 a2 k

variable (HE : Extra.IsInstN E) (H0 : ParRed E Γ₀ a1 a2) in
theorem ParRed.instN (W : Ctx.InstN Γ₀ a1 A₀ k Γ₁ Γ)
    (H : ParRed E Γ₁ e1 e2) : ParRed E Γ (e1.inst a1 k) (e2.inst a2 k) := by
  induction H generalizing Γ k with
  | @bvar _ i =>
    dsimp [inst]
    induction W generalizing i with
    | zero =>
      cases i with simp [inst_lift]
      | zero => exact H0
      | succ h => exact rfl
    | succ _ ih =>
      cases i with simp
      | zero => exact rfl
      | succ h => exact ih.weakN HE.1 .one
  | sort | const => exact rfl
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | beta _ _ ih1 ih2 =>
    simp [inst, inst0_inst_hi]
    exact .beta (ih1 W.succ) (ih2 W)
  | extra _ ih =>
    refine .extra fun a a' h => ?_
    obtain ⟨_, _, h', rfl, rfl⟩ := HE.2 W h
    exact ih _ _ h' W
