import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.EnvLemmas

/-!
A bunch of important structural theorems which we can't prove :(
-/

namespace Lean4Lean
namespace VEnv

theorem IsDefEq.uniq (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEq U Γ e₁ e₂ A) (h2 : env.IsDefEq U Γ e₂ e₃ B) :
    ∃ u, env.IsDefEq U Γ A B (.sort u) := sorry

theorem IsDefEq.uniqU (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEq U Γ e₁ e₂ A) (h2 : env.IsDefEq U Γ e₂ e₃ B) :
    env.IsDefEqU U Γ A B := let ⟨_, h⟩ := h1.uniq henv hΓ h2; ⟨_, h⟩

variable! (henv : VEnv.WF env) in
theorem IsDefEqU.weakN (W : Ctx.LiftN n k Γ Γ') (H : env.IsDefEqU U Γ e1 e2) :
    env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) := let ⟨_, H⟩ := H; ⟨_, H.weakN henv W⟩

variable! (henv : VEnv.WF env) in
theorem IsDefEqU.weak' (W : Ctx.Lift' n Γ Γ') (H : env.IsDefEqU U Γ e1 e2) :
    env.IsDefEqU U Γ' (e1.lift' n) (e2.lift' n) := let ⟨_, H⟩ := H; ⟨_, H.weak' henv W⟩

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

theorem IsDefEqU.sort_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v := sorry

theorem IsDefEqU.forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B')) :
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧ ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) := sorry

theorem IsDefEqU.sort_forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ¬env.IsDefEqU U Γ (.sort u) (.forallE A B) := sorry

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
