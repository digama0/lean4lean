import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.Pattern

/-! # Unique typing and its consequences. -/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env U Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEq env U Γ e1 e2 A

theorem IsDefEq.uniq (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : Γ ⊢ e₁ ≡ e₂ : A) (h2 : Γ ⊢ e₂ ≡ e₃ : B) : ∃ u, Γ ⊢ A ≡ B : .sort u := by
  suffices ∀ {e A B b n₁ n₂ n}, n₁ ≤ n → n₂ ≤ n →
      env.HasTypeStratified U Γ e A b n₁ → env.HasTypeStratified U Γ e B b n₂ →
      ∃ u, Γ ⊢ A ≡ B : .sort u ∧ ∃ v, u ≈ v ∧
        env.HasTypeStratified U Γ A (.sort u) true (n-1) ∧
        env.HasTypeStratified U Γ B (.sort v) true (n-1) from
    let ⟨n₁, h1⟩ := (h1.strong henv hΓ).hasType'.2.stratify
    let ⟨n₂, h2⟩ := (h2.strong henv hΓ).hasType'.1.stratify
    have ⟨_, h, _⟩ := this (Nat.le_max_left ..) (Nat.le_max_right ..) h1 h2
    ⟨_, h⟩
  clear h1 h2; intro e A B b n₁ n₂ n le₁ le₂ H1
  induction n using WellFounded.induction Nat.lt_wfRel.2
    generalizing n₁ n₂ Γ e A B b with | _ n IH
  dsimp [Nat.lt_wfRel] at IH
  induction H1 generalizing B n₂ n with
  | bvar a1 a2 =>
    intro (.bvar b1 b2); cases a1.uniq b1
    exact ⟨_, b2.hasType, _, rfl, b2.mono (by omega), b2.mono (by omega)⟩
  | sort' a1 a2 a3 =>
    intro (.sort' b1 b2 b3)
    have := VLevel.succ_congr (b3.symm.trans a3)
    exact ⟨_, .symm <| .sortDF b2 a2 this, _, VLevel.succ_congr this,
      .base <| .sort' a2 b2 this.symm, .base <| .sort' b2 a2 this⟩
  | const a1 a2 a3 a4 =>
    intro (.const b1 b2 b3 b4); cases a1.symm.trans b1
    replace le₁ := Nat.sub_le_sub_right le₁ 1
    exact ⟨_, a4.hasType, _, rfl, a4.mono le₁, a4.mono le₁⟩
  | app a1 a2 a3 a4 a5 a6 a7 ih1 ih2 ih3 ih4 ih5 =>
    intro (.app b1 b2 b3 b4 b5 b6 b7)
    have ⟨_, c1, _, c2, c3, c4⟩ := ih3 n IH hΓ (Nat.le_of_succ_le le₁) (Nat.le_of_succ_le le₂) b5
    have ⟨⟨_, d1, d2⟩, _, d3, d4, d5⟩ := IsDefEqU.forallE_inv_stratified henv hΓ ⟨_, c1⟩ c3 c4
    let n+1 := n
    replace le₁ := Nat.le_of_succ_le_succ le₁
    replace le₂ := Nat.le_of_succ_le_succ le₂
    have e1 := have ⟨_, h⟩ := a3.hasType.isType henv hΓ; h.sort_inv henv
    have e2 := have ⟨_, h⟩ := b3.hasType.isType henv hΓ; h.sort_inv henv
    refine have hΓ₁ := ⟨hΓ, _, a3.hasType⟩
      have ⟨_, h, _⟩ := IH _ (Nat.lt_succ_self _) hΓ₁ le₁ (Nat.le_refl _) a4 d4; ?_
    have e3 := IsDefEqU.sort_inv henv hΓ₁ ⟨_, h⟩
    have e4 := have ⟨_, h⟩ := d4.hasType.isType henv hΓ₁; h.sort_inv henv
    refine have hΓ₂ := ⟨hΓ, _, b3.hasType⟩
      have ⟨_, h, _⟩ := IH _ (Nat.lt_succ_self _) hΓ₂ le₂ (Nat.le_refl _) b4 d5; ?_
    have e5 := IsDefEqU.sort_inv henv hΓ₂ ⟨_, h⟩
    exact ⟨_, .defeqDF (.sortDF e4 a2 e3.symm) (d3.instN henv a6.hasType .zero), _,
      e3.trans e5.symm, a7.mono le₁, b7.mono le₂⟩
  | lam a1 a2 a3 a4 ih1 ih2 ih3 ih4 =>
    intro (.lam b1 b2 b3 b4)
    have ⟨_, c1, _, c2, c3, c4⟩ := ih3 n IH ⟨hΓ, _, a1.hasType⟩
      (Nat.le_of_succ_le le₁) (Nat.le_of_succ_le le₂) b3
    let n+1 := n
    replace le₁ := Nat.le_of_succ_le_succ le₁
    replace le₂ := Nat.le_of_succ_le_succ le₂
    have ⟨_, h, _⟩ := IH _ (Nat.lt_succ_self _) hΓ le₁ le₂ a1 b1
    have e1 := IsDefEqU.sort_inv henv hΓ ⟨_, h⟩
    refine have hΓ' := ⟨hΓ, _, a1.hasType⟩
      have ⟨_, h, _⟩ := IH _ (Nat.lt_succ_self _) hΓ' le₁ (Nat.le_refl _) a2 c3; ?_
    have f1 := h.sort_inv_l henv; have f2 := h.sort_inv_r henv
    have e2 := IsDefEqU.sort_inv henv hΓ' ⟨_, h⟩
    have ⟨_, h, _⟩ := IH _ (Nat.lt_succ_self _) hΓ' le₂ (Nat.le_refl _) b2 c4
    have e3 := IsDefEqU.sort_inv henv hΓ' ⟨_, h⟩
    exact ⟨_, .forallEDF a1.hasType (.defeqDF (.symm <| .sortDF f1 f2 e2) c1),
      _, VLevel.imax_congr e1 (e2.trans <| c2.trans e3.symm), a4.mono le₁, b4.mono le₂⟩
  | forallE a1 a2 a3 a4 ih1 ih2 =>
    intro (.forallE b1 b2 b3 b4)
    let n+1 := n
    replace le₁ := Nat.le_of_succ_le_succ le₁
    replace le₂ := Nat.le_of_succ_le_succ le₂
    have ⟨_, h, _⟩ := IH _ (Nat.lt_succ_self _) hΓ le₁ le₂ a3 b3
    have e1 := IsDefEqU.sort_inv henv hΓ ⟨_, h⟩
    refine have hΓ' := ⟨hΓ, _, a3.hasType⟩
      have ⟨_, h, _⟩ := IH _ (Nat.lt_succ_self _) hΓ' le₁ le₂ a4 b4; ?_
    have f1 := h.sort_inv_l henv; have f2 := h.sort_inv_r henv
    have e2 := IsDefEqU.sort_inv henv hΓ' ⟨_, h⟩
    have := VLevel.imax_congr e1 e2
    exact ⟨_, .sortDF ⟨a1, a2⟩ ⟨b1, b2⟩ this, _, rfl,
      .base <| .sort' ⟨a1, a2⟩ ⟨a1, a2⟩ rfl, .base <| .sort' ⟨b1, b2⟩ ⟨a1, a2⟩ this.symm⟩
  | @base Γ e A n₁ a1 ih =>
    intro H2
    replace ih {n'} le := @ih n' (fun y h1 => IH y (Nat.lt_of_lt_of_le h1 le)) hΓ
    generalize eq : true = b at H2
    induction H2 with cases eq
    | @base _ _  _ n' b1 => exact ih (Nat.le_refl _) le₁ le₂ b1
    | @defeq Γ B' B u n' _ b1 b2 b3 b4 b5 _ _ ih' =>
      have ⟨u₁, c1, u₂, c2, c3, c4⟩ := ih' a1 hΓ (Nat.le_of_succ_le le₂) ih rfl
      let n+1 := n
      replace le₂ := Nat.le_of_succ_le_succ le₂
      have ⟨v₁, d1, v₂, _⟩ := IH _ (Nat.lt_succ_self _) hΓ le₂ (Nat.le_refl _) b3 c4
      have e1 := IsDefEqU.sort_inv henv hΓ ⟨_, d1⟩
      have e2 := have ⟨_, h⟩ := c3.hasType.isType henv hΓ; h.sort_inv henv
      have eq : u₁ ≈ u := c2.trans e1.symm
      exact ⟨_, c1.trans (.defeqDF (.symm <| .sortDF e2 b1 eq) b2), _, eq, c3, b4.mono le₂⟩
  | @defeq Γ A' A u n' _ a1 a2 a3 a4 a5 ih1 ih2 ih' =>
    intro H2
    have ⟨u₁, c1, u₂, c2, c3, c4⟩ := ih' _ IH hΓ (Nat.le_of_succ_le le₁) le₂ H2
    let n+1 := n
    replace le₁ := Nat.le_of_succ_le_succ le₁
    have ⟨v₁, d1, v₂, _⟩ := IH _ (Nat.lt_succ_self _) hΓ le₁ (Nat.le_refl _) a3 c3
    have e1 := IsDefEqU.sort_inv henv hΓ ⟨_, d1⟩
    have e2 := have ⟨_, h⟩ := c3.hasType.isType henv hΓ; h.sort_inv henv
    have eq : u ≈ u₂ := e1.trans c2
    exact ⟨_, a2.symm.trans (.defeqDF (.symm <| .sortDF a1 e2 e1) c1), _, eq, a4.mono le₁, c4⟩

theorem IsDefEq.uniqU (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEq U Γ e₁ e₂ A) (h2 : env.IsDefEq U Γ e₂ e₃ B) :
    env.IsDefEqU U Γ A B := let ⟨_, h⟩ := h1.uniq henv hΓ h2; ⟨_, h⟩

theorem isDefEq_iff (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    env.IsDefEq U Γ e₁ e₂ A ↔
    env.HasType U Γ e₁ A ∧ env.HasType U Γ e₂ A ∧ env.IsDefEqU U Γ e₁ e₂ := by
  refine ⟨fun h => ⟨h.hasType.1, h.hasType.2, _, h⟩, fun ⟨_, h2, _, h3⟩ => ?_⟩
  have ⟨_, h⟩ := h3.uniq henv hΓ h2
  exact h.defeqDF h3

theorem IsDefEq.trans_r (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : env.IsDefEq U Γ e₁ e₂ A) (h₂ : env.IsDefEq U Γ e₂ e₃ B) :
    env.IsDefEq U Γ e₁ e₃ B := by
  have ⟨_, h⟩ := h₁.uniq henv hΓ h₂
  exact .trans (.defeqDF h h₁) h₂

theorem IsDefEq.trans_l (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : env.IsDefEq U Γ e₁ e₂ A) (h₂ : env.IsDefEq U Γ e₂ e₃ B) :
    env.IsDefEq U Γ e₁ e₃ A := by
  have ⟨_, h⟩ := h₁.uniq henv hΓ h₂
  exact h₁.trans (.defeqDF (.symm h) h₂)

theorem IsDefEqU.defeqDF (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : env.IsDefEqU U Γ A B) (h₂ : env.IsDefEq U Γ e₁ e₂ A) :
    env.IsDefEq U Γ e₁ e₂ B := by
  have ⟨_, h₁⟩ := h₁
  have ⟨_, hA⟩ := h₂.isType henv hΓ
  exact .defeqDF (hA.trans_l henv hΓ h₁) h₂

theorem IsDefEqU.of_l (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ e₁ e₂) (h2 : env.HasType U Γ e₁ A) :
    env.IsDefEq U Γ e₁ e₂ A := let ⟨_, h⟩ := h1; h2.trans_l henv hΓ h

theorem HasType.defeqU_l (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ e₁ e₂) (h2 : env.HasType U Γ e₁ A) :
    env.HasType U Γ e₂ A := (h1.of_l henv hΓ h2).hasType.2

theorem IsType.defeqU_l (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ A₁ A₂) (h2 : env.IsType U Γ A₁) :
    env.IsType U Γ A₂ := h2.imp fun _ h2 => h2.defeqU_l henv hΓ h1

theorem IsDefEqU.of_r (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ e₁ e₂) (h2 : env.HasType U Γ e₂ A) :
    env.IsDefEq U Γ e₁ e₂ A := (h1.symm.of_l henv hΓ h2).symm

theorem HasType.defeqU_r (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ A₁ A₂) (h2 : env.HasType U Γ e A₁) :
    env.HasType U Γ e A₂ := h1.defeqDF henv hΓ h2

theorem IsDefEqU.trans (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ e₁ e₂) (h2 : env.IsDefEqU U Γ e₂ e₃) :
    env.IsDefEqU U Γ e₁ e₃ := h1.imp fun _ h1 => let ⟨_, h2⟩ := h2; h1.trans_l henv hΓ h2

variable! (henv : VEnv.WF env) (hΓ : OnCtx Γ' (env.IsType U)) in
theorem IsDefEqU.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) ↔ env.IsDefEqU U Γ e1 e2 := by
  refine ⟨fun h => have := henv; have := hΓ; sorry, fun h => h.weakN henv W⟩

variable! (henv : VEnv.WF env) (hΓ : OnCtx Γ' (env.IsType U)) in
theorem _root_.Lean4Lean.VExpr.WF.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    VExpr.WF env U Γ' (e.liftN n k) ↔ VExpr.WF env U Γ e := IsDefEqU.weakN_iff henv hΓ W

theorem IsDefEq.skips (henv : VEnv.WF env) (hΓ : OnCtx Γ' (env.IsType U))
    (W : Ctx.LiftN n k Γ Γ')
    (H : env.IsDefEq U Γ' e₁ e₂ A) (h1 : e₁.Skips n k) (h2 : e₂.Skips n k) :
    ∃ B, env.IsDefEq U Γ' e₁ e₂ B ∧ B.Skips n k := by
  obtain ⟨e₁, rfl⟩ := VExpr.skips_iff_exists.1 h1
  obtain ⟨e₂, rfl⟩ := VExpr.skips_iff_exists.1 h2
  have ⟨_, H⟩ := (IsDefEqU.weakN_iff henv hΓ W).1 ⟨_, H⟩
  exact ⟨_, H.weakN henv W, .liftN⟩

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) (hΓ : OnCtx Γ (env.IsType U)) in
theorem IsDefEq.weakN_iff' (W : Ctx.LiftN n k Γ Γ') :
    env.IsDefEq U Γ' (e1.liftN n k) (e2.liftN n k) (A.liftN n k) ↔ env.IsDefEq U Γ e1 e2 A := by
  refine ⟨fun h => ?_, fun h => h.weakN henv W⟩
  have ⟨_, H⟩ := (IsDefEqU.weakN_iff henv hΓ' W).1 ⟨_, h⟩
  refine IsDefEqU.defeqDF henv hΓ ?_ H
  exact (IsDefEqU.weakN_iff henv hΓ' W).1 <| (H.weakN henv W).uniqU henv hΓ' h.symm

variable! (henv : VEnv.WF env) in
theorem _root_.Lean4Lean.OnCtx.weakN_inv
    (W : Ctx.LiftN n k Γ Γ') (H : OnCtx Γ' (env.IsType U)) : OnCtx Γ (env.IsType U) := by
  induction W with
  | zero As h =>
    clear h
    induction As with
    | nil => exact H
    | cons A As ih => exact ih H.1
  | succ W ih =>
    let ⟨H1, _, H2⟩ := H
    exact ⟨ih H1, _, (IsDefEq.weakN_iff' henv H1 (ih H1) W).1 H2⟩

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem IsDefEq.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    env.IsDefEq U Γ' (e1.liftN n k) (e2.liftN n k) (A.liftN n k) ↔ env.IsDefEq U Γ e1 e2 A :=
  IsDefEq.weakN_iff' henv hΓ' (hΓ'.weakN_inv henv W) W

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem HasType.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    env.HasType U Γ' (e.liftN n k) (A.liftN n k) ↔ env.HasType U Γ e A :=
  IsDefEq.weakN_iff henv hΓ' W

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem IsType.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    env.IsType U Γ' (A.liftN n k) ↔ env.IsType U Γ A :=
  exists_congr fun _ => HasType.weakN_iff henv hΓ' W (A := .sort _)

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem HasType.skips (W : Ctx.LiftN n k Γ Γ')
    (h1 : env.HasType U Γ' e A) (h2 : e.Skips n k) : ∃ B, env.HasType U Γ' e B ∧ B.Skips n k :=
  IsDefEq.skips henv hΓ' W h1 h2 h2

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem IsDefEqU.weak'_iff (W : Ctx.Lift' l Γ Γ') :
    env.IsDefEqU U Γ' (e1.lift' l) (e2.lift' l) ↔ env.IsDefEqU U Γ e1 e2 := by
  generalize e : l.depth = n
  induction n generalizing l Γ' with
  | zero => simp [VExpr.lift'_depth_zero e, W.depth_zero e]
  | succ n ih =>
    obtain ⟨l, k, rfl, rfl⟩ := Lift.depth_succ e
    have ⟨Γ₁, W1, W2⟩ := W.of_cons_skip
    rw [Lift.consN_skip_eq, VExpr.lift'_comp, VExpr.lift'_comp,
      ← Lift.skipN_one, VExpr.lift'_consN_skipN, VExpr.lift'_consN_skipN,
      weakN_iff henv hΓ' W2, ih (hΓ'.weakN_inv henv W2) W1 Lift.depth_consN]

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem IsDefEq.weak'_iff (W : Ctx.Lift' l Γ Γ') :
    env.IsDefEq U Γ' (e1.lift' l) (e2.lift' l) (A.lift' l) ↔ env.IsDefEq U Γ e1 e2 A := by
  generalize e : l.depth = n
  induction n generalizing l Γ' with
  | zero => simp [VExpr.lift'_depth_zero e, W.depth_zero e]
  | succ n ih =>
    obtain ⟨l, k, rfl, rfl⟩ := Lift.depth_succ e
    have ⟨Γ₁, W1, W2⟩ := W.of_cons_skip
    rw [Lift.consN_skip_eq, VExpr.lift'_comp, VExpr.lift'_comp, VExpr.lift'_comp,
      ← Lift.skipN_one, VExpr.lift'_consN_skipN, VExpr.lift'_consN_skipN, VExpr.lift'_consN_skipN,
      weakN_iff henv hΓ' W2, ih (hΓ'.weakN_inv henv W2) W1 Lift.depth_consN]

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem HasType.weak'_iff (W : Ctx.Lift' l Γ Γ') :
    env.HasType U Γ' (e.lift' l) (A.lift' l) ↔ env.HasType U Γ e A :=
  IsDefEq.weak'_iff henv hΓ' W

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem IsType.weak'_iff (W : Ctx.Lift' l Γ Γ') :
    env.IsType U Γ' (e.lift' l) ↔ env.IsType U Γ e :=
  exists_congr fun _ => HasType.weak'_iff henv hΓ' W (A := .sort _)

variable! (henv : VEnv.WF env) (hΓ : OnCtx Γ' (env.IsType U)) in
theorem _root_.Lean4Lean.VExpr.WF.weak'_iff (W : Ctx.Lift' l Γ Γ') :
    VExpr.WF env U Γ' (e.lift' l) ↔ VExpr.WF env U Γ e := IsDefEqU.weak'_iff henv hΓ W
