import Lean4Lean.Theory.Typing.Strong

namespace Lean4Lean

open VExpr

def Extra := List VExpr → VExpr → VExpr → VExpr → VExpr → Prop

section
set_option hygiene false
local notation:65 Γ " ⊢ " e1 " ≫ " e2:30 => ParRed Γ e1 e2
variable (extra : Extra) (uvars : Nat)

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

namespace VEnv

section
set_option hygiene false
variable (env : VEnv) (uvars : Nat)
local notation:65 Γ " ⊢ " e " : " A:30 => HasType env uvars Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:30 => IsDefEq env uvars Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≣ " e2 " : " A:30 => NormalEq Γ e1 e2 A

inductive NormalEq : List VExpr → VExpr → VExpr → VExpr → Prop where
  | refl : Γ ⊢ e : A → Γ ⊢ e ≣ e : A
  | sortDF :
    l₁.WF uvars → l₂.WF uvars → l.WF uvars → l₁ ≈ l → l₂ ≈ l →
    Γ ⊢ .sort l₁ ≣ .sort l₂ : .sort (.succ l)
  | appDF :
    Γ ⊢ a₁ ≡ a : A → Γ ⊢ a₂ ≡ a : A →
    Γ ⊢ f₁ ≣ f₂ : .forallE A B →
    Γ ⊢ a₁ ≣ a₂ : A →
    Γ ⊢ .app f₁ a₁ ≣ .app f₂ a₂ : B.inst a
  | lamDF :
    Γ ⊢ A₁ ≡ A : .sort u → Γ ⊢ A₂ ≡ A : .sort u →
    Γ ⊢ A₁ ≣ A₂ : .sort u →
    A::Γ ⊢ body₁ ≣ body₂ : B →
    Γ ⊢ .lam A₁ body₁ ≣ .lam A₂ body₂ : .forallE A B
  | forallEDF :
    Γ ⊢ A₁ ≡ A : .sort u → Γ ⊢ A₂ ≡ A : .sort u →
    Γ ⊢ A₁ ≣ A₂ : .sort u →
    A::Γ ⊢ B₁ ≣ B₂ : .sort v →
    Γ ⊢ .forallE A₁ B₁ ≣ .forallE A₂ B₂ : .sort (.imax u v)
  | etaL :
    Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ e ≣ .app e'.lift (.bvar 0) : B →
    Γ ⊢ .lam A e ≣ e' : .forallE A B
  | etaR :
    Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ .app e'.lift (.bvar 0) ≣ e : B →
    Γ ⊢ e' ≣ .lam A e : .forallE A B
  | proofIrrel :
    Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p →
    Γ ⊢ h ≣ h' : p

end

variable (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem NormalEq.defeq (H : env.NormalEq U Γ e1 e2 A) : env.IsDefEq U Γ e1 e2 A := by
  induction H with
  | refl h => exact h
  | sortDF h1 h2 h3 h4 h5 =>
    exact .defeqDF (.sortDF ‹_› ‹_› (VLevel.succ_congr h4)) <| .sortDF h1 h2 (h4.trans h5.symm)
  | appDF ha₁ _ _ _ ih1 ih2 =>
    have ⟨_, h1⟩ := (ih1 hΓ).isType henv hΓ
    have ⟨_, _, hB⟩ := h1.forallE_inv henv
    exact .defeqDF (.instDF henv hΓ hB ha₁) <| .appDF (ih1 hΓ) (ih2 hΓ)
  | lamDF hA₁ hA₂ _ _ _ ih2 =>
    have := ih2 ⟨hΓ, _, hA₁.hasType.2⟩
    exact .trans (.symm <| .lamDF (.symm hA₁) this.hasType.1) (.lamDF hA₂.symm this)
  | forallEDF hA₁ hA₂ _ _ _ ih2 =>
    have := ih2 ⟨hΓ, _, hA₁.hasType.2⟩
    exact .trans (.symm <| .forallEDF (.symm hA₁) this.hasType.1) (.forallEDF hA₂.symm this)
  | etaL h1 _ ih =>
    have ⟨_, h2⟩ := h1.isType henv hΓ
    have ⟨⟨_, hA⟩, _⟩ := h2.forallE_inv henv
    exact .trans (.lamDF hA (ih ⟨hΓ, _, hA⟩)) (.eta h1)
  | etaR h1 _ ih =>
    have ⟨_, h2⟩ := h1.isType henv hΓ
    have ⟨⟨_, hA⟩, _⟩ := h2.forallE_inv henv
    exact .trans (.symm <| .eta h1) (.lamDF hA (ih ⟨hΓ, _, hA⟩))
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h2 h3

theorem NormalEq.symm {env : VEnv} (H : env.NormalEq U Γ e1 e2 A) : env.NormalEq U Γ e2 e1 A := by
  induction H with
  | refl h => exact .refl h
  | sortDF h1 h2 h3 h4 h5 => exact .sortDF h2 h1 h3 h5 h4
  | appDF h1 h2 _ _ ih1 ih2 => exact .appDF h2 h1 ih1 ih2
  | lamDF h1 h2 _ _ ih1 ih2 => exact .lamDF h2 h1 ih1 ih2
  | forallEDF h1 h2 _ _ ih1 ih2 => exact .forallEDF h2 h1 ih1 ih2
  | etaL h1 _ ih => exact .etaR h1 ih
  | etaR h1 _ ih => exact .etaL h1 ih
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h3 h2

/-
variable (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem NormalEq.trans
    (H1 : env.NormalEq U Γ e1 e2 A) (H2 : env.NormalEq U Γ e2 e3 A) :
    env.NormalEq U Γ e1 e3 A := by
  induction id H1 generalizing e3 with
  | refl h => exact H2
  | proofIrrel l1 l2 l3 => exact .proofIrrel l1 l2 (H2.defeq henv hΓ).hasType.2
  | sortDF l1 l2 l3 l4 l5 =>
    cases H2 with
    | refl => exact H1
    | proofIrrel r1 r2 r3 => exact .proofIrrel r1 (H1.defeq henv hΓ).hasType.1 r3
    | sortDF r1 r2 r3 r4 r5 => exact .sortDF l1 r2 l3 l4 r5
  | @appDF _ a₁ a A a₂ f₁ f₂ B l1 l2 _ _ ihl1 ihl2 =>
    generalize eq : inst B a = i at H2
    cases H2 with
    | refl => exact eq ▸ H1
    | proofIrrel r1 r2 r3 => subst eq; exact .proofIrrel r1 (H1.defeq henv hΓ).hasType.1 r3
    | @appDF _ a₁' a' A' a₂' f₁' f₂' B' r1 r2 ihr1 ihr2 =>
      have := ihl1 hΓ ihr1
      exact .appDF _ _ _ _
    | etaR r1 ihr1 =>
      exact .appDF _ _ _ _
  | lamDF h1 h2 _ _ ih1 ih2 => exact .lamDF h2 h1 ih1 ih2
  | forallEDF h1 h2 _ _ ih1 ih2 => exact .forallEDF h2 h1 ih1 ih2
  | etaL h1 _ ih => exact .etaR h1 ih
  | etaR h1 _ ih => exact .etaL h1 ih
-/
