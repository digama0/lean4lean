import Lean4Lean.Theory.Typing.Lemmas

namespace Lean4Lean

open VExpr

variable (IsDefEq : List VExpr → VExpr → VExpr → Prop) (Γ₀ : List VExpr) in
inductive IsDefEqCtx : List VExpr → List VExpr → Prop
  | zero : IsDefEqCtx Γ₀ Γ₀
  | succ : IsDefEqCtx Γ₁ Γ₂ → IsDefEq Γ₁ A₁ A₂ → IsDefEqCtx (A₁ :: Γ₁) (A₂ :: Γ₂)

section
set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEq Γ e1 e2
structure Typing where
  env : VEnv
  -- henv : env.Ordered
  univs : Nat
  IsDefEq : List VExpr → VExpr → VExpr → Prop
  HasType : List VExpr → VExpr → VExpr → Prop
  refl : Γ ⊢ e : A → Γ ⊢ e ≡ e
  symm : Γ ⊢ e₁ ≡ e₂ → Γ ⊢ e₂ ≡ e₁
  trans : Γ ⊢ e₁ ≡ e₂ → Γ ⊢ e₂ ≡ e₃ → Γ ⊢ e₁ ≡ e₃
  bvar : Lookup Γ i A → Γ ⊢ .bvar i : A
  sort : u.WF univs → Γ ⊢ .sort u : .sort u.succ
  sortDF : u.WF univs → v.WF univs → u ≈ v → Γ ⊢ .sort u ≡ .sort v
  constDF :
    env.constants c = some (some ci) →
    (∀ l ∈ ls, l.WF univs) → (∀ l ∈ ls', l.WF univs) →
    ls.length = ci.uvars → List.Forall₂ (· ≈ ·) ls ls' →
    Γ ⊢ .const c ls ≡ .const c ls'
  appDF : Γ ⊢ f : .forallE A B → Γ ⊢ f ≡ f' → Γ ⊢ a : A → Γ ⊢ a ≡ a' → Γ ⊢ .app f a ≡ .app f' a'
  lamDF : Γ ⊢ A : .sort u → Γ ⊢ A ≡ A' → A::Γ ⊢ body ≡ body' → Γ ⊢ .lam A body ≡ .lam A' body'
  forallEDF :
    Γ ⊢ A : .sort u → Γ ⊢ A ≡ A' →
    A::Γ ⊢ body : .sort v → A::Γ ⊢ body ≡ body' →
    Γ ⊢ .forallE A body ≡ .forallE A' body'
  const :
    env.constants c = some (some ci) →
    (∀ l ∈ ls, l.WF univs) → ls.length = ci.uvars →
    Γ ⊢ .const c ls : ci.type.instL ls
  app : Γ ⊢ f : .forallE A B → Γ ⊢ a : A → Γ ⊢ .app f a : .inst B a
  lam : Γ ⊢ A : .sort u → A::Γ ⊢ body : B → Γ ⊢ .lam A body : .forallE A B
  forallE : Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v → Γ ⊢ .forallE A B : .sort (.imax u v)
  -- beta : A::Γ ⊢ e : B → Γ ⊢ e' : A → Γ ⊢ .app (.lam A e) e' ≡ e.inst e'
  eta : Γ ⊢ e : .forallE A B → Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e
  proofIrrel : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ h'
  isDefEq_weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    Γ' ⊢ e1.liftN n k ≡ e2.liftN n k ↔ Γ ⊢ e1 ≡ e2
  hasType_weakN_iff (W : Ctx.LiftN n k Γ Γ') : Γ' ⊢ e.liftN n k : A.liftN n k ↔ Γ ⊢ e : A
  hasTypeU_weakN_inv (W : Ctx.LiftN n k Γ Γ') : Γ' ⊢ e.liftN n k : A → ∃ A', Γ ⊢ e : A'
  isDefEq_instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (H : Γ₁ ⊢ e1 ≡ e2) (h₀ : Γ₀ ⊢ e₀ : A₀) : Γ ⊢ e1.inst e₀ k ≡ e2.inst e₀ k
  hasType_instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (H : Γ₁ ⊢ e1 : A) (h₀ : Γ₀ ⊢ e₀ : A₀) : Γ ⊢ e1.inst e₀ k : A.inst e₀ k
  isDefEq_DFC : IsDefEqCtx IsDefEq Γ₀ Γ₁ Γ₂ → Γ₁ ⊢ e1 ≡ e2 → Γ₂ ⊢ e1 ≡ e2
  hasType_DFC : IsDefEqCtx IsDefEq Γ₀ Γ₁ Γ₂ → Γ₁ ⊢ e : A → Γ₂ ⊢ e : A
  has_type : Γ ⊢ e₁ ≡ e₂ → ∃ A, Γ ⊢ e₁ : A
  is_type : Γ ⊢ e : A → ∃ u, Γ ⊢ A : .sort u
  bvar_inv : Γ ⊢ .bvar i : V → ∃ A, Lookup Γ i A
  sort_inv : Γ ⊢ .sort u : V → u.WF univs
  const_inv : Γ ⊢ .const c ls : V →
    ∃ ci, env.constants c = some (some ci) ∧ (∀ l ∈ ls, l.WF univs) ∧ ls.length = ci.uvars
  forallE_inv : Γ ⊢ .forallE A B : V → ∃ u v, Γ ⊢ A : .sort u ∧ A::Γ ⊢ B : .sort v
  app_inv : Γ ⊢ .app f a : V → ∃ A B, Γ ⊢ f : .forallE A B ∧ Γ ⊢ a : A
  lam_inv : Γ ⊢ .lam A e : V → ∃ u B, Γ ⊢ A : .sort u ∧ A::Γ ⊢ e : B
  uniq : Γ ⊢ e : A₁ → Γ ⊢ e : A₂ → Γ ⊢ A₁ ≡ A₂
  defeq_l : Γ ⊢ e₁ ≡ e₂ → Γ ⊢ e₁ : A → Γ ⊢ e₂ : A
  defeq_r : Γ ⊢ A₁ ≡ A₂ → Γ ⊢ e : A₁ → Γ ⊢ e : A₂
  -- univ_defInv : Γ ⊢ .sort u ≡ .sort v → u ≈ v
  forallE_defInv : Γ ⊢ .forallE A B ≡ .forallE A' B' → Γ ⊢ A ≡ A' ∧ A::Γ ⊢ B ≡ B'

theorem Typing.IsDefEq.weakN {TY : Typing} (W : Ctx.LiftN n k Γ Γ') :
    TY.IsDefEq Γ e1 e2 → TY.IsDefEq Γ' (e1.liftN n k) (e2.liftN n k) := (TY.isDefEq_weakN_iff W).2
theorem Typing.HasType.weakN {TY : Typing} (W : Ctx.LiftN n k Γ Γ') :
    TY.HasType Γ e A → TY.HasType Γ' (e.liftN n k) (A.liftN n k) := (TY.hasType_weakN_iff W).2

theorem Typing.IsDefEq.instN {TY : Typing} : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → TY.IsDefEq Γ₁ e1 e2 →
    TY.HasType Γ₀ e₀ A₀ → TY.IsDefEq Γ (e1.inst e₀ k) (e2.inst e₀ k) := TY.isDefEq_instN
theorem Typing.HasType.instN {TY : Typing} : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → TY.HasType Γ₁ e A →
    TY.HasType Γ₀ e₀ A₀ → TY.HasType Γ (e.inst e₀ k) (A.inst e₀ k) := TY.hasType_instN

end

section
set_option hygiene false
variable (TY : Typing)
local notation:65 Γ " ⊢ " e " : " A:30 => TY.HasType Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:30 => TY.IsDefEq Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2:30 => NormalEq Γ e1 e2

inductive NormalEq : List VExpr → VExpr → VExpr → Prop where
  | refl : Γ ⊢ e : A → Γ ⊢ e ≡ₚ e
  | sortDF : l₁.WF TY.univs → l₂.WF TY.univs → l₁ ≈ l₂ → Γ ⊢ .sort l₁ ≡ₚ .sort l₂
  | constDF :
    TY.env.constants c = some (some ci) →
    (∀ l ∈ ls, l.WF TY.univs) →
    (∀ l ∈ ls', l.WF TY.univs) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    Γ ⊢ .const c ls ≡ₚ .const c ls'
  | appDF :
    Γ ⊢ f₁ : .forallE A B → Γ ⊢ f₂ : .forallE A B →
    Γ ⊢ a₁ : A → Γ ⊢ a₂ : A →
    Γ ⊢ f₁ ≡ₚ f₂ → Γ ⊢ a₁ ≡ₚ a₂ →
    Γ ⊢ .app f₁ a₁ ≡ₚ .app f₂ a₂
  | lamDF :
    Γ ⊢ A : .sort u → Γ ⊢ A₁ ≡ A → Γ ⊢ A₁ ≡ₚ A₂ →
    A::Γ ⊢ body₁ ≡ₚ body₂ →
    Γ ⊢ .lam A₁ body₁ ≡ₚ .lam A₂ body₂
  | forallEDF :
    Γ ⊢ A : .sort u → Γ ⊢ A₁ ≡ A → Γ ⊢ A₁ ≡ₚ A₂ →
    A::Γ ⊢ B₁ : .sort v → A::Γ ⊢ B₁ ≡ₚ B₂ →
    Γ ⊢ .forallE A₁ B₁ ≡ₚ .forallE A₂ B₂
  | etaL :
    Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ e ≡ₚ .app e'.lift (.bvar 0) →
    Γ ⊢ .lam A e ≡ₚ e'
  | etaR :
    Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ .app e'.lift (.bvar 0) ≡ₚ e →
    Γ ⊢ e' ≡ₚ .lam A e
  | proofIrrel :
    Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p →
    Γ ⊢ h ≡ₚ h'

end

theorem NormalEq.defeq (H : NormalEq TY Γ e1 e2) : TY.IsDefEq Γ e1 e2 := by
  induction H with
  | refl h => exact TY.refl h
  | sortDF h1 h2 h3 => exact TY.sortDF h1 h2 h3
  | appDF hf₁ _ ha₁ _ _ _ ih1 ih2 => exact TY.appDF hf₁ ih1 ha₁ ih2
  | constDF h1 h2 h3 h4 h5 => exact TY.constDF h1 h2 h3 h4 h5
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

theorem NormalEq.symm (H : NormalEq TY Γ e1 e2) : NormalEq TY Γ e2 e1 := by
  induction H with
  | refl h => exact .refl h
  | sortDF h1 h2 h3 => exact .sortDF h2 h1 h3.symm
  | constDF h1 h2 h3 h4 h5 =>
    exact .constDF h1 h3 h2 (h5.length_eq.symm.trans h4) (h5.flip.imp (fun _ _ h => h.symm))
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 => exact .appDF h2 h1 h4 h3 ih1 ih2
  | lamDF h1 h2 _ _ ih1 ih2 => exact .lamDF h1 (TY.trans ih1.defeq h2) ih1 ih2
  | forallEDF h1 h2 _ h4 h5 ih1 ih2 =>
    exact .forallEDF h1 (TY.trans ih1.defeq h2) ih1 (TY.defeq_l h5.defeq h4) ih2
  | etaL h1 _ ih => exact .etaR h1 ih
  | etaR h1 _ ih => exact .etaL h1 ih
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h3 h2

theorem NormalEq.weakN (W : Ctx.LiftN n k Γ Γ') (H : NormalEq TY Γ e1 e2) :
    NormalEq TY Γ' (e1.liftN n k) (e2.liftN n k) := by
  induction H generalizing k Γ' with
  | refl h => exact .refl (h.weakN W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (h1.weakN W) (h2.weakN W) (h3.weakN W) (h4.weakN W) (ih1 W) (ih2 W)
  | lamDF h1 h2 _ _ ih1 ih2 =>
    exact .lamDF (h1.weakN W) (h2.weakN W) (ih1 W) (ih2 W.succ)
  | forallEDF h1 h2 _ h4 _ ih1 ih2 =>
    exact .forallEDF (h1.weakN W) (h2.weakN W) (ih1 W) (h4.weakN W.succ) (ih2 W.succ)
  | etaL h1 _ ih =>
    refine .etaL (h1.weakN W) ?_
    have := ih W.succ
    simp [liftN] at this; rwa [lift_liftN']
  | etaR h1 _ ih =>
    refine .etaR (h1.weakN W) ?_
    have := ih W.succ
    simp [liftN] at this; rwa [lift_liftN']
  | proofIrrel h1 h2 h3 =>
    exact .proofIrrel (h1.weakN W) (h2.weakN W) (h3.weakN W)

variable (h₀ : Typing.HasType TY Γ₀ e₀ A₀) in
theorem NormalEq.instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : NormalEq TY Γ₁ e1 e2) :
    NormalEq TY Γ (e1.inst e₀ k) (e2.inst e₀ k) := by
  induction H generalizing Γ k with
  | refl h => exact .refl (h.instN W h₀)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (h1.instN W h₀) (h2.instN W h₀) (h3.instN W h₀) (h4.instN W h₀) (ih1 W) (ih2 W)
  | lamDF h1 h2 _ _ ih1 ih2 =>
    exact .lamDF (h1.instN W h₀) (h2.instN W h₀) (ih1 W) (ih2 W.succ)
  | forallEDF h1 h2 _ h4 _ ih1 ih2 =>
    exact .forallEDF (h1.instN W h₀) (h2.instN W h₀) (ih1 W) (h4.instN W.succ h₀) (ih2 W.succ)
  | etaL h1 _ ih =>
    refine .etaL (h1.instN W h₀) ?_
    simpa [inst, lift_instN_lo] using ih W.succ
  | etaR h1 _ ih =>
    refine .etaR (h1.instN W h₀) ?_
    simpa [inst, lift_instN_lo] using ih W.succ
  | proofIrrel h1 h2 h3 => exact .proofIrrel (h1.instN W h₀) (h2.instN W h₀) (h3.instN W h₀)

variable (h₀ : Typing.HasType TY Γ₀ e₀ A₀) (H' : NormalEq TY Γ₀ e₀ e₀') in
theorem NormalEq.instN_r (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : Typing.HasType TY Γ₁ e A) :
    NormalEq TY Γ (e.inst e₀ k) (e.inst e₀' k) := by
  induction e generalizing Γ₁ Γ k A with dsimp [inst]
  | bvar i =>
    have ⟨ty, h⟩ := TY.bvar_inv H; clear H
    induction W generalizing i ty with
    | zero =>
      cases h with simp [inst_lift]
      | zero => exact H'
      | succ h => exact .refl (TY.bvar h)
    | succ _ ih =>
      cases h with simp
      | zero => exact .refl (TY.bvar .zero)
      | succ h => exact (ih _ _ h).weakN .one
  | sort => exact .refl (TY.sort (TY.sort_inv H))
  | const =>
    let ⟨_, h1, h2, h3⟩ := TY.const_inv H
    exact .refl (TY.const h1 h2 h3)
  | app fn arg ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := TY.app_inv H
    specialize ih1 W h1; have hf := h1.instN W h₀
    specialize ih2 W h2; have ha := h2.instN W h₀
    exact .appDF hf (TY.defeq_l ih1.defeq hf) ha (TY.defeq_l ih2.defeq ha) ih1 ih2
  | lam A body ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := TY.lam_inv H
    have hA := h1.instN W h₀
    exact .lamDF hA (TY.refl hA) (ih1 W h1) (ih2 W.succ h2)
  | forallE A B ih1 ih2 =>
    let ⟨_, _, h1, h2⟩ := TY.forallE_inv H
    have hA := h1.instN W h₀
    exact .forallEDF hA (TY.refl hA) (ih1 W h1) (h2.instN W.succ h₀) (ih2 W.succ h2)

variable (TY : Typing) in
theorem NormalEq.defeqDFC (W : IsDefEqCtx TY.IsDefEq Γ₀ Γ₁ Γ₂)
    (H : NormalEq TY Γ₁ e1 e2) : NormalEq TY Γ₂ e1 e2 := by
  induction H generalizing Γ₂ with
  | refl h => refine .refl (TY.hasType_DFC W h)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (TY.hasType_DFC W h1) (TY.hasType_DFC W h2)
      (TY.hasType_DFC W h3) (TY.hasType_DFC W h4) (ih1 W) (ih2 W)
  | lamDF h1 h2 _ _ ih1 ih2 =>
    exact .lamDF (TY.hasType_DFC W h1) (TY.isDefEq_DFC W h2) (ih1 W) (ih2 (W.succ (TY.refl h1)))
  | forallEDF h1 h2 _ h4 _ ih1 ih2 =>
    exact .forallEDF (TY.hasType_DFC W h1) (TY.isDefEq_DFC W h2) (ih1 W)
      (TY.hasType_DFC (W.succ (TY.refl h1)) h4) (ih2 (W.succ (TY.refl h1)))
  | etaL h1 _ ih =>
    have ⟨_, _, h2, _⟩ := let ⟨_, h⟩ := TY.is_type h1; TY.forallE_inv h
    refine .etaL (TY.hasType_DFC W h1) (ih (W.succ (TY.refl h2)))
  | etaR h1 _ ih =>
    have ⟨_, _, h2, _⟩ := let ⟨_, h⟩ := TY.is_type h1; TY.forallE_inv h
    refine .etaR (TY.hasType_DFC W h1) (ih (W.succ (TY.refl h2)))
  | proofIrrel h1 h2 h3 =>
    exact .proofIrrel (TY.hasType_DFC W h1)
      (TY.hasType_DFC W h2) (TY.hasType_DFC W h3)

theorem NormalEq.defeq_l (W : TY.IsDefEq Γ A A') (H : NormalEq TY (A::Γ) e1 e2) :
    NormalEq TY (A'::Γ) e1 e2 := defeqDFC TY (.succ .zero W) H

theorem NormalEq.weakN_inv_DFC (W : Ctx.LiftN n k Γ Γ₂) (W₂ : IsDefEqCtx TY.IsDefEq Γ₀ Γ₁ Γ₂)
    (H : NormalEq TY Γ₁ (e1.liftN n k) (e2.liftN n k)) : NormalEq TY Γ e1 e2 := by
  generalize eq1 : e1.liftN n k = e1' at H
  generalize eq2 : e2.liftN n k = e2' at H
  induction H generalizing Γ Γ₂ e1 e2 k with
  | refl h =>
    cases eq2; cases liftN_inj.1 eq1
    have ⟨_, h'⟩ := TY.hasTypeU_weakN_inv W (TY.hasType_DFC W₂ h)
    exact .refl h'
  | sortDF h1 h2 h3 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    replace h1 := TY.hasType_DFC W₂ h1
    replace h2 := TY.hasType_DFC W₂ h2
    replace h3 := TY.hasType_DFC W₂ h3
    replace h4 := TY.hasType_DFC W₂ h4
    have ⟨_, _, l1, l2⟩ :=
      let ⟨_, h⟩ := TY.hasTypeU_weakN_inv W (TY.app h1 h3) (e := .app ..); TY.app_inv h
    have ⟨_, _, r1, r2⟩ :=
      let ⟨_, h⟩ := TY.hasTypeU_weakN_inv W (TY.app h2 h4) (e := .app ..); TY.app_inv h
    have := (TY.isDefEq_weakN_iff W).1
      (TY.trans (TY.uniq (l1.weakN W) h1) (TY.uniq h2 (r1.weakN W)))
    exact .appDF (TY.defeq_r this l1) r1
      (TY.defeq_r (TY.forallE_defInv this).1 l2) r2 (ih1 W W₂ rfl rfl) (ih2 W W₂ rfl rfl)
  | lamDF h1 h2 _ _ ih1 ih2 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    have := (TY.hasType_weakN_iff (A := .sort ..) W).1 <|
      TY.hasType_DFC W₂ (TY.defeq_l (TY.symm h2) h1)
    exact .lamDF this (TY.refl this) (ih1 W W₂ rfl rfl) (ih2 W.succ (W₂.succ (TY.symm h2)) rfl rfl)
  | forallEDF h1 h2 _ h4 _ ih1 ih2 =>
    cases e1 <;> cases eq1
    cases e2 <;> cases eq2
    replace h4 := (TY.hasType_weakN_iff (A := .sort ..) W.succ).1 <|
      TY.hasType_DFC (W₂.succ (TY.symm h2)) h4
    have := (TY.hasType_weakN_iff (A := .sort ..) W).1 <|
      TY.hasType_DFC W₂ (TY.defeq_l (TY.symm h2) h1)
    exact .forallEDF this (TY.refl this)
      (ih1 W W₂ rfl rfl) h4 (ih2 W.succ (W₂.succ (TY.symm h2)) rfl rfl)
  | etaL h1 _ ih =>
    cases e1 <;> cases eq1
    subst eq2
    have ⟨_, _, hA, hB⟩ := let ⟨_, h⟩ := TY.is_type h1; TY.forallE_inv h
    have h1' := TY.hasType_DFC W₂ h1
    have hA' := TY.hasType_DFC W₂ hA
    have hB' := TY.hasType_DFC (W₂.succ (TY.refl hA)) hB
    have := TY.app (h1'.weakN .one) (TY.bvar .zero)
    rw [instN_bvar0, ← lift, lift_liftN',
      ← show liftN n (.bvar 0) (k+1) = bvar 0 by simp [liftN],
      ← liftN] at this
    have ⟨C, hC⟩ := TY.hasTypeU_weakN_inv W.succ this
    have := (TY.hasType_weakN_iff (A := .forallE ..) W).1 <|
      TY.defeq_r (TY.forallEDF hA' (TY.refl hA') hB' (TY.uniq this (hC.weakN W.succ))) h1'
    refine .etaL this (ih W.succ (W₂.succ (TY.refl hA)) rfl (by simp [liftN, lift_liftN']))
  | etaR h1 _ ih =>
    subst eq1
    cases e2 <;> cases eq2
    have ⟨_, _, hA, hB⟩ := let ⟨_, h⟩ := TY.is_type h1; TY.forallE_inv h
    have h1' := TY.hasType_DFC W₂ h1
    have hA' := TY.hasType_DFC W₂ hA
    have hB' := TY.hasType_DFC (W₂.succ (TY.refl hA)) hB
    have := TY.app (h1'.weakN .one) (TY.bvar .zero)
    rw [instN_bvar0, ← lift, lift_liftN',
      ← show liftN n (.bvar 0) (k+1) = bvar 0 by simp [liftN],
      ← liftN] at this
    have ⟨C, hC⟩ := TY.hasTypeU_weakN_inv W.succ this
    have := (TY.hasType_weakN_iff (A := .forallE ..) W).1 <|
      TY.defeq_r (TY.forallEDF hA' (TY.refl hA') hB' (TY.uniq this (hC.weakN W.succ))) h1'
    refine .etaR this (ih W.succ (W₂.succ (TY.refl hA)) (by simp [liftN, lift_liftN']) rfl)
  | proofIrrel h1 h2 h3 =>
    subst eq1; subst eq2
    have h1' := TY.hasType_DFC W₂ h1
    have h2' := TY.hasType_DFC W₂ h2
    have h3' := TY.hasType_DFC W₂ h3
    have ⟨_, h⟩ := TY.hasTypeU_weakN_inv W h2'
    have hw := TY.uniq h2' (h.weakN W)
    exact .proofIrrel
      ((TY.hasType_weakN_iff (A := .sort ..) W).1 (TY.defeq_l hw h1'))
      ((TY.hasType_weakN_iff W).1 (TY.defeq_r hw h2'))
      ((TY.hasType_weakN_iff W).1 (TY.defeq_r hw h3'))

theorem NormalEq.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    NormalEq TY Γ' (e1.liftN n k) (e2.liftN n k) ↔ NormalEq TY Γ e1 e2 :=
  ⟨fun H => H.weakN_inv_DFC W .zero, fun H => H.weakN W⟩

private def meas : VExpr → Nat
  | .app f a
  | .forallE f a => meas f + meas a + 1
  | .bvar _ | .const .. | .sort _ => 0
  | .lam A e => meas A + meas e + 3

private theorem meas_liftN : meas (e.liftN n k) = meas e := by
  induction e generalizing k <;> simp [*, meas]
private theorem meas_lift : meas e.lift = meas e := meas_liftN

variable (TY : Typing) in
attribute [local simp] meas meas_lift in
theorem NormalEq.trans : NormalEq TY Γ e1 e2 → NormalEq TY Γ e2 e3 → NormalEq TY Γ e1 e3
  | .sortDF l1 _ l3, .sortDF r1 r2 r3 => .sortDF l1 r2 (l3.trans r3)
  | .constDF l1 l2 _ l4 l5, .constDF _ _ r3 r4 r5 =>
    .constDF l1 l2 r3 l4 (l5.trans (fun _ _ _ h1 => h1.trans) r5)
  | .appDF l1 l2 l3 l4 l5 l6, .appDF r1 r2 r3 r4 r5 r6 =>
    .appDF l1 (TY.defeq_r (TY.uniq r1 l2) r2) l3
      (TY.defeq_r (TY.uniq r3 l4) r4) (NormalEq.trans l5 r5) (NormalEq.trans l6 r6)
  | .lamDF l1 l2 l3 l4, .lamDF _ r2 r3 r4 =>
    have r4' := r4.defeq_l (TY.trans (TY.symm (TY.trans l3.defeq r2)) l2)
    .lamDF l1 l2 (NormalEq.trans l3 r3) (NormalEq.trans l4 r4')
  | .forallEDF l1 l2 l3 l4 l5, .forallEDF _ r2 r3 r4 r5 =>
    have r5' := r5.defeq_l (TY.trans (TY.symm (TY.trans l3.defeq r2)) l2)
    .forallEDF l1 l2 (NormalEq.trans l3 r3) l4 (NormalEq.trans l5 r5')
  | .etaR l1 ih, .lamDF _ r2 r3 r4 =>
    have ⟨_, _, hA, hB⟩ := let ⟨_, h⟩ := TY.is_type l1; TY.forallE_inv h
    .etaR (TY.defeq_r (TY.forallEDF hA r3.defeq hB (TY.refl hB)) l1)
      (NormalEq.trans (ih.defeq_l r3.defeq) (r4.defeq_l (TY.trans (TY.symm r2) r3.defeq)))
  | .lamDF _ l2 l3 l4, .etaL r1 ih =>
    have ⟨_, _, hA, hB⟩ := let ⟨_, h⟩ := TY.is_type r1; TY.forallE_inv h
    .etaL (TY.defeq_r (TY.forallEDF hA l3.symm.defeq hB (TY.refl hB)) r1)
      (NormalEq.trans (l4.defeq_l (TY.symm l2)) (ih.defeq_l l3.symm.defeq))
  | H1@(.etaR l1 ihl), .etaL r1 ihr => by
    have := NormalEq.trans ihl ihr
    generalize eq : e1.lift = e1' at this
    have ⟨_, _, hA, _⟩ := let ⟨_, h⟩ := TY.is_type l1; TY.forallE_inv h
    cases this with first | cases eq | cases liftN_inj.1 eq
    | refl h => exact .refl r1
    | proofIrrel h1 h2 h3 =>
      refine .proofIrrel (TY.defeq_r ?_ (TY.forallE hA h1))
        (TY.defeq_l (TY.eta l1) (TY.lam hA h2)) (TY.defeq_l (TY.eta r1) (TY.lam hA h3))
      have hw := let ⟨_, h⟩ := TY.is_type hA; TY.sort_inv h
      exact TY.sortDF ⟨hw, ⟨⟩⟩ ⟨⟩ rfl
    | appDF _ _ _ _ ih => exact (NormalEq.weakN_iff .one).1 ih
  | .refl h, H2 => H2
  | .proofIrrel l1 l2 l3, H2 => .proofIrrel l1 l2 (TY.defeq_l H2.defeq l3)
  | .etaL l1 ih, H2 => by
    refine .etaL (TY.defeq_l H2.defeq l1) (NormalEq.trans ih ?_)
    exact .appDF (l1.weakN .one)
      ((TY.defeq_l H2.defeq l1).weakN .one) (TY.bvar .zero) (TY.bvar .zero)
      (.weakN .one H2) (.refl (TY.bvar .zero))
  | H1, .refl _ => H1
  | H1, .etaR r1 ih => by
    refine .etaR (TY.defeq_l H1.symm.defeq r1) (NormalEq.trans ?_ ih)
    refine .appDF ((TY.defeq_l H1.symm.defeq r1).weakN .one)
      (r1.weakN .one) (TY.bvar .zero) (TY.bvar .zero)
      (.weakN .one H1) (.refl (TY.bvar .zero))
  | H1, .proofIrrel h1 h2 h3 => .proofIrrel h1 (TY.defeq_l H1.symm.defeq h2) h3
termination_by meas e1 + meas e2 + meas e3
