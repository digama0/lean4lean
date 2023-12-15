import Lean4Lean.Theory.Typing.Strong

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

section
set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEq Γ e1 e2
structure Typing where
  univs : Nat
  IsDefEq : List VExpr → VExpr → VExpr → Prop
  HasType : List VExpr → VExpr → VExpr → Prop
  refl : Γ ⊢ e : A → Γ ⊢ e ≡ e
  symm : Γ ⊢ e₁ ≡ e₂ → Γ ⊢ e₂ ≡ e₁
  trans : Γ ⊢ e₁ ≡ e₂ → Γ ⊢ e₂ ≡ e₃ → Γ ⊢ e₁ ≡ e₃
  sort : u.WF univs → Γ ⊢ .sort u : .sort u.succ
  sortDF : u.WF univs → v.WF univs → u ≈ v → Γ ⊢ .sort u ≡ .sort v
  appDF : Γ ⊢ f : .forallE A B → Γ ⊢ f ≡ f' → Γ ⊢ a : A → Γ ⊢ a ≡ a' → Γ ⊢ .app f a ≡ .app f' a'
  lamDF : Γ ⊢ A : .sort u → Γ ⊢ A ≡ A' → A::Γ ⊢ body ≡ body' → Γ ⊢ .lam A body ≡ .lam A' body'
  forallEDF :
    Γ ⊢ A : .sort u → Γ ⊢ A ≡ A' →
    A::Γ ⊢ body : .sort v → A::Γ ⊢ body ≡ body' →
    Γ ⊢ .forallE A body ≡ .forallE A' body'
  eta : Γ ⊢ e : .forallE A B → Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e
  proofIrrel : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ h'
  has_type : Γ ⊢ e₁ ≡ e₂ → ∃ A, Γ ⊢ e₁ : A
  is_type : Γ ⊢ e : A → ∃ u, Γ ⊢ A : .sort u
  sort_inv : Γ ⊢ .sort u : p → u.WF univs
  forallE_inv : Γ ⊢ .forallE A B : V → ∃ u v, Γ ⊢ A : .sort u ∧ A::Γ ⊢ A : .sort v
  uniq : Γ ⊢ e : A₁ → Γ ⊢ e : A₂ → Γ ⊢ A₁ ≡ A₂
  defeq_l : Γ ⊢ e₁ ≡ e₂ → Γ ⊢ e₁ : A → Γ ⊢ e₂ : A
  defeq_r : Γ ⊢ A₁ ≡ A₂ → Γ ⊢ e : A₁ → Γ ⊢ e : A₂
  univ_defInv : Γ ⊢ .sort u ≡ .sort v → u ≈ v

end

section
set_option hygiene false
variable (TY : Typing)
local notation:65 Γ " ⊢ " e " : " A:30 => TY.HasType Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:30 => TY.IsDefEq Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≣ " e2:30 => NormalEq Γ e1 e2

inductive NormalEq : List VExpr → VExpr → VExpr → Prop where
  | refl : Γ ⊢ e : A → Γ ⊢ e ≣ e
  | sortDF : l₁.WF TY.univs → l₂.WF TY.univs → l₁ ≈ l₂ → Γ ⊢ .sort l₁ ≣ .sort l₂
  | appDF :
    Γ ⊢ f₁ : .forallE A B → Γ ⊢ f₂ : .forallE A B →
    Γ ⊢ a₁ : A → Γ ⊢ a₂ : A →
    Γ ⊢ f₁ ≣ f₂ → Γ ⊢ a₁ ≣ a₂ →
    Γ ⊢ .app f₁ a₁ ≣ .app f₂ a₂
  | lamDF :
    Γ ⊢ A : .sort u → Γ ⊢ A₁ ≡ A →
    Γ ⊢ A₁ ≣ A₂ →
    A::Γ ⊢ body₁ ≣ body₂ →
    Γ ⊢ .lam A₁ body₁ ≣ .lam A₂ body₂
  | forallEDF :
    Γ ⊢ A : .sort u → Γ ⊢ A₁ ≡ A → Γ ⊢ A₁ ≣ A₂ →
    A::Γ ⊢ B₁ : .sort v → A::Γ ⊢ B₁ ≣ B₂ →
    Γ ⊢ .forallE A₁ B₁ ≣ .forallE A₂ B₂
  | etaL :
    Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ e ≣ .app e'.lift (.bvar 0) →
    Γ ⊢ .lam A e ≣ e'
  | etaR :
    Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ .app e'.lift (.bvar 0) ≣ e →
    Γ ⊢ e' ≣ .lam A e
  | proofIrrel :
    Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p →
    Γ ⊢ h ≣ h'

end

theorem NormalEq.defeq (H : NormalEq TY Γ e1 e2) : TY.IsDefEq Γ e1 e2 := by
  induction H with
  | refl h => exact TY.refl h
  | sortDF h1 h2 h3 => exact TY.sortDF h1 h2 h3
  | appDF hf₁ _ ha₁ _ _ _ ih1 ih2 => exact TY.appDF hf₁ ih1 ha₁ ih2
  | lamDF hA hA₁ _ _ ihA ihB =>
    have ⟨_, hB⟩ := TY.has_type ihB
    exact TY.trans (TY.symm <| TY.lamDF hA (TY.symm hA₁) (TY.refl hB))
      (TY.lamDF hA (TY.trans (TY.symm hA₁) ihA) ihB)
  | forallEDF hA hA₁ _ hB₁ _ ihA ihB =>
    exact TY.trans (TY.symm <| TY.forallEDF hA (TY.symm hA₁) hB₁ (TY.refl hB₁))
      (TY.forallEDF hA (TY.trans (TY.symm hA₁) ihA) hB₁ ihB)
  | etaL h1 _ ih =>
    have ⟨_, AB⟩ := TY.is_type h1
    have ⟨_, _, hA, _⟩ := TY.forallE_inv AB
    exact TY.trans (TY.lamDF hA (TY.refl hA) ih) (TY.eta h1)
  | etaR h1 _ ih =>
    have ⟨_, AB⟩ := TY.is_type h1
    have ⟨_, _, hA, _⟩ := TY.forallE_inv AB
    exact TY.trans (TY.symm (TY.eta h1)) (TY.lamDF hA (TY.refl hA) ih)
  | proofIrrel h1 h2 h3 => exact TY.proofIrrel h1 h2 h3

theorem NormalEq.symm {env : VEnv} (H : NormalEq TY Γ e1 e2) : NormalEq TY Γ e2 e1 := by
  induction H with
  | refl h => exact .refl h
  | sortDF h1 h2 h3 => exact .sortDF h2 h1 h3.symm
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 => exact .appDF h2 h1 h4 h3 ih1 ih2
  | lamDF h1 h2 _ _ ih1 ih2 => exact .lamDF h1 (TY.trans ih1.defeq h2) ih1 ih2
  | forallEDF h1 h2 _ h4 h5 ih1 ih2 =>
    exact .forallEDF h1 (TY.trans ih1.defeq h2) ih1 (TY.defeq_l h5.defeq h4) ih2
  | etaL h1 _ ih => exact .etaR h1 ih
  | etaR h1 _ ih => exact .etaL h1 ih
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h3 h2

variable (TY : Typing) in
theorem NormalEq.trans
    (H1 : NormalEq TY Γ e1 e2) (H2 : NormalEq TY Γ e2 e3) :
    NormalEq TY Γ e1 e3 := by
  sorry
  -- induction id H1 generalizing e3 with
  -- | refl => exact H2
  -- | proofIrrel l1 l2 l3 =>
  --   induction H2 with
  --   | refl => exact H1
  --   | proofIrrel r1 r2 r3 =>
  --     exact .proofIrrel l1 l2 (TY.defeq_r (TY.uniq r2 l3) r3)
  --   | sortDF r1 =>
  --     have hu := TY.sort_inv l3
  --     have := TY.defeq_l (TY.uniq l3 (TY.sort hu)) l1
  --     cases VLevel.equiv_def.1 (TY.univ_defInv <| TY.uniq this (TY.sort hu)) []
  --   | appDF r1 r2 =>

  --     have hu := TY.sort_inv l3
  --     have := TY.defeq_l (TY.uniq l3 (TY.sort hu)) l1
  --     cases VLevel.equiv_def.1 (TY.univ_defInv <| TY.uniq this (TY.sort hu)) []
  -- | sortDF l1 l2 l3 l4 l5 =>
  --   cases H2 with
  --   | refl => exact H1
  --   | proofIrrel r1 r2 r3 => exact .proofIrrel r1 (H1.defeq henv hΓ).hasType.1 r3
  --   | sortDF r1 r2 r3 r4 r5 => exact .sortDF l1 r2 l3 l4 r5
  -- | @appDF _ a₁ a A a₂ f₁ f₂ B l1 l2 _ _ ihl1 ihl2 =>
  --   generalize eq : inst B a = i at H2
  --   cases H2 with
  --   | refl => exact eq ▸ H1
  --   | proofIrrel r1 r2 r3 => subst eq; exact .proofIrrel r1 (H1.defeq henv hΓ).hasType.1 r3
  --   | @appDF _ a₁' a' A' a₂' f₁' f₂' B' r1 r2 ihr1 ihr2 =>
  --     have := ihl1 hΓ _ ihr1
  --     exact .appDF _ _ _ _
  --   | etaR r1 ihr1 =>
  --     exact .appDF _ _ _ _
  -- | lamDF h1 h2 _ _ ih1 ih2 => exact .lamDF h2 h1 ih1 ih2
  -- | forallEDF h1 h2 _ _ ih1 ih2 => exact .forallEDF h2 h1 ih1 ih2
  -- | etaL h1 _ ih => exact .etaR h1 ih
  -- | etaR h1 _ ih => exact .etaL h1 ih
