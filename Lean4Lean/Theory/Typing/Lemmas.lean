import Lean4Lean.Theory.Typing.Basic

namespace Lean4Lean

open Lean (Name FVarId)
open VExpr

inductive Ctx.LiftN (n : Nat) : Nat → List VExpr → List VExpr → Prop where
  | zero (As) (h : As.length = n := by rfl) : Ctx.LiftN n 0 Γ (As ++ Γ)
  | succ : Ctx.LiftN n k Γ Γ' → Ctx.LiftN n (k+1) (A::Γ) (A.liftN n k :: Γ')

def Ctx.LiftN.one : Ctx.LiftN 1 0 Γ (A::Γ) := .zero [_]

variable (Γ₀ : List VExpr) (e₀ A₀ : VExpr) in
inductive Ctx.InstN : Nat → List VExpr → List VExpr → Prop where
  | zero : Ctx.InstN 0 (A₀ :: Γ₀) Γ₀
  | succ : Ctx.InstN k Γ Γ' → Ctx.InstN (k+1) (A::Γ) (A.inst e₀ k :: Γ')

theorem Lookup.lt (H : Lookup Γ i A) : i < Γ.length := by
  induction H with
  | zero => apply Nat.succ_pos
  | succ _ ih => apply Nat.succ_lt_succ ih

theorem Lookup.weakN (W : Ctx.LiftN n k Γ Γ') (H : Lookup Γ i A) :
    Lookup Γ' (liftVar n i k) (A.liftN n k) := by
  induction W generalizing i A with
  | zero As =>
    rw [liftVar_base, Nat.add_comm]
    subst n
    induction As with simp [*]
    | cons _ _ ih => rw [liftN_succ]; exact .succ ih
  | @succ k _ _ _ _ ih =>
    match H with
    | .zero => rw [liftVar_zero, ← lift_liftN']; exact .zero
    | .succ H => rw [liftVar_succ, ← lift_liftN']; exact (ih H).succ

theorem Lookup.weakN_inv (W : Ctx.LiftN n k Γ Γ') (H : Lookup Γ' (liftVar n i k) (A.liftN n k)) :
    Lookup Γ i A := by
  induction W generalizing i A with
  | zero As =>
    rw [liftVar_base, Nat.add_comm] at H
    subst n
    induction As with simp at H
    | nil => exact H
    | cons A As ih =>
      rw [liftN_succ] at H
      generalize eq : lift (liftN ..) = A' at H
      obtain _|H := H; cases liftN_inj.1 eq
      exact ih H
  | @succ k _ _ _ _ ih =>
    generalize eA : liftN n A (k+1) = A' at H
    cases i with
    | zero =>
      simp at H; let .zero := H
      rw [lift, liftN'_comm (h := Nat.zero_le _), Nat.add_comm 1, liftN_inj] at eA
      subst A; exact .zero
    | succ i =>
      simp at H; let .succ H := H
      obtain ⟨_, rfl, rfl⟩ := of_liftN_eq_liftN (k2 := 0) eA
      exact .succ (ih H)

theorem Lookup.instL : Lookup Γ i A → Lookup (Γ.map (VExpr.instL ls)) i (A.instL ls)
  | .zero => instL_liftN ▸ .zero
  | .succ h => instL_liftN ▸ .succ h.instL

def CtxClosed : List VExpr → Prop
  | [] => True
  | A::Γ => CtxClosed Γ ∧ A.ClosedN Γ.length

theorem CtxClosed.lookup (h : CtxClosed Γ) (hL : Lookup Γ n A) : A.ClosedN Γ.length :=
  match hL, h with
  | .zero, ⟨h1, h2⟩ => h2.liftN
  | .succ hL, ⟨h1, h2⟩ => (h1.lookup hL).liftN

namespace VEnv

theorem addConst_le {env env' : VEnv} (h : env.addConst n oci = some env') : env ≤ env' := by
  unfold addConst at h; split at h <;> cases h
  refine ⟨fun n ci h => ?_, fun _ => id⟩
  simp; rwa [if_neg]; rintro rfl; cases h.symm.trans ‹_ = none›

theorem addDefEq_le {env : VEnv} : env ≤ env.addDefEq df :=
  ⟨fun _ _ => id, fun df h => by simp [addDefEq, h]⟩

theorem IsDefEq.sort (h : l.WF U) : HasType env U Γ (.sort l) (.sort (.succ l)) :=
  .sortDF h h rfl
theorem IsDefEq.app (h1 : HasType env U Γ f (.forallE A B)) (h2 : HasType env U Γ a A) :
    HasType env U Γ (.app f a) (B.inst a) := .appDF h1 h2
theorem IsDefEq.lam (h1 : HasType env U Γ A (.sort u)) (h2 : HasType env U (A::Γ) body B) :
    HasType env U Γ (.lam A body) (.forallE A B) := .lamDF h1 h2
theorem IsDefEq.forallE
    (h1 : HasType env U Γ A (.sort u)) (h2 : HasType env U (A::Γ) body (.sort v)) :
    HasType env U Γ (.forallE A body) (.sort (.imax u v)) := .forallEDF h1 h2
theorem IsDefEq.defeq (h1 : IsDefEq env U Γ A B (.sort u))
    (h2 : HasType env U Γ e A) : HasType env U Γ e B := .defeqDF h1 h2
theorem IsDefEq.defeq' (h1 : IsDefEq env U Γ A B (.sort u))
    (h2 : HasType env U Γ e B) : HasType env U Γ e A := .defeq h1.symm h2

theorem IsDefEq.hasType {env : VEnv} (H : env.IsDefEq U Γ e1 e2 A) :
    env.HasType U Γ e1 A ∧ env.HasType U Γ e2 A := ⟨H.trans H.symm, H.symm.trans H⟩

inductive Ordered : VEnv → Prop where
  | nil : Ordered ∅
  | const :
    Ordered env → (∀ ci, oci = some ci → ci.WF env) →
    env.addConst n oci = some env' → Ordered env'
  | defeq : Ordered env → df.WF env → Ordered (env.addDefEq df)

def OnTypes (env : VEnv) (P : Nat → VExpr → VExpr → Prop) : Prop :=
  (∀ {n ci}, env.constants n = some (some ci) → ∃ u, P ci.uvars ci.type (.sort u)) ∧
  (∀ {df}, env.defeqs df → P df.uvars df.lhs df.type ∧ P df.uvars df.rhs df.type)

theorem OnTypes.mono (henv : env' ≤ env) (hP : ∀ {U e A}, P U e A → P' U e A)
    (H : OnTypes env P) : OnTypes env' P' :=
  ⟨fun hci => (H.1 (henv.1 _ _ hci)).imp fun _ => hP, fun hdf => (H.2 (henv.2 _ hdf)).imp hP hP⟩

theorem Ordered.induction (motive : VEnv → Nat → VExpr → VExpr → Prop)
    (mono : ∀ {env env' U e A}, env ≤ env' → motive env U e A → motive env' U e A)
    (type : ∀ {env U e A},
      Ordered env → OnTypes env (motive env) → HasType env U [] e A → motive env U e A)
    (H : Ordered env) : OnTypes env (motive env) := by
  induction H with
  | nil => exact ⟨fun., fun.⟩
  | const h1 h2 h3 ih =>
    apply OnTypes.mono .rfl (mono (addConst_le h3))
    unfold addConst at h3; split at h3 <;> cases h3
    refine ⟨fun h => ?_, ih.2⟩
    simp at h; split at h
    · cases h
      let ⟨_, ht⟩ := h2 _ rfl
      exact ⟨_, type h1 ih ht⟩
    · exact ih.1 h
  | defeq h1 h2 ih =>
    apply OnTypes.mono .rfl (mono addDefEq_le)
    refine ⟨ih.1, fun hdf => ?_⟩
    simp [addDefEq] at hdf
    obtain rfl | hdf := hdf
    · let ⟨hl, hr⟩ := h2
      exact ⟨type h1 ih hl, type h1 ih hr⟩
    · exact ih.2 hdf

variable {env : VEnv} (henv : env.OnTypes fun _ e A => e.ClosedN ∧ A.ClosedN) in
theorem IsDefEq.closedN' (H : env.IsDefEq U Γ e1 e2 A) (hΓ : CtxClosed Γ) :
    e1.ClosedN Γ.length ∧ e2.ClosedN Γ.length ∧ A.ClosedN Γ.length := by
  induction H with
  | bvar h => exact ⟨h.lt, h.lt, hΓ.lookup h⟩
  | const h1 =>
    let ⟨_, h, _⟩ := henv.1 h1
    exact ⟨trivial, trivial, h.instL.mono (Nat.zero_le _)⟩
  | sortDF => exact ⟨trivial, trivial, trivial⟩
  | symm _ ih => let ⟨h1, h2, h3⟩ := ih hΓ; exact ⟨h2, h1, h3⟩
  | trans _ _ ih1 ih2 => exact ⟨(ih1 hΓ).1, (ih2 hΓ).2.1, (ih1 hΓ).2.2⟩
  | appDF _ _ ih1 ih2 =>
    let ⟨hf, hf', _, hB⟩ := ih1 hΓ
    let ⟨ha, ha', _⟩ := ih2 hΓ
    exact ⟨⟨hf, ha⟩, ⟨hf', ha'⟩, hB.inst ha⟩
  | lamDF _ _ ih1 ih2 =>
    let ⟨hA, hA', _⟩ := ih1 hΓ
    let ⟨hb, hb', hB⟩ := ih2 ⟨hΓ, hA⟩
    exact ⟨⟨hA, hb⟩, ⟨hA', hb'⟩, hA, hB⟩
  | forallEDF _ _ ih1 ih2 =>
    let ⟨hA, hA', _⟩ := ih1 hΓ
    let ⟨hb, hb', _⟩ := ih2 ⟨hΓ, hA⟩
    exact ⟨⟨hA, hb⟩, ⟨hA', hb'⟩, trivial⟩
  | defeqDF _ _ ih1 ih2 => exact ⟨(ih2 hΓ).1, (ih2 hΓ).2.1, (ih1 hΓ).2.1⟩
  | beta _ _ ih1 ih2 =>
    let ⟨he', _, hA⟩ := ih2 hΓ
    let ⟨he, _, hB⟩ := ih1 ⟨hΓ, hA⟩
    exact ⟨⟨⟨hA, he⟩, he'⟩, he.inst he', hB.inst he'⟩
  | eta _ ih =>
    let ⟨he, _, hA, hB⟩ := ih hΓ
    exact ⟨⟨hA, he.liftN, Nat.succ_pos _⟩, he, hA, hB⟩
  | proofIrrel _ _ _ _ ih2 ih3 =>
    let ⟨hh, _, _⟩ := ih2 hΓ
    let ⟨hh', _, hp⟩ := ih3 hΓ
    exact ⟨hh, hh', hp⟩
  | extra h1 _ _ =>
    let ⟨⟨hl, _⟩, ⟨hr, hA⟩⟩ := henv.2 h1
    exact ⟨
      hl.instL.mono (Nat.zero_le _),
      hr.instL.mono (Nat.zero_le _),
      hA.instL.mono (Nat.zero_le _)⟩

theorem Ordered.closed (H : Ordered env) : env.OnTypes fun _ e A => e.ClosedN ∧ A.ClosedN :=
  H.induction _ (fun _ => id) fun _ ih h => (IsDefEq.closedN' ih h trivial).2

theorem Ordered.closedC (H : Ordered env)
    (h : env.constants n = some (some ci)) : ci.type.ClosedN :=
  let ⟨_, h⟩ := H.closed.1 h; h.1

theorem IsDefEq.closedN {env : VEnv} (henv : env.Ordered)
    (H : env.IsDefEq U Γ e1 e2 A) (hΓ : CtxClosed Γ) : e1.ClosedN Γ.length :=
  (H.closedN' henv.closed hΓ).1

variable {env env' : VEnv} (henv : env ≤ env') in
theorem IsDefEq.mono (H : env.IsDefEq U Γ e1 e2 A) : env'.IsDefEq U Γ e1 e2 A := by
  induction H with
  | bvar h => exact .bvar h
  | const h1 h2 h3 => exact .const (henv.1 _ _ h1) h2 h3
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | appDF _ _ ih1 ih2 => exact .appDF ih1 ih2
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ ih1 ih2 => exact .beta ih1 ih2
  | eta _ ih => exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 => exact .extra (henv.2 _ h1) h2 h3

theorem HasType.mono {env env' : VEnv} (henv : env ≤ env') :
    env.HasType U Γ e A → env'.HasType U Γ e A := IsDefEq.mono henv

theorem IsType.mono {env env' : VEnv} (henv : env ≤ env') : env.IsType U Γ A → env'.IsType U Γ A
  | ⟨u, h⟩ => ⟨u, h.mono henv⟩

end VEnv

theorem VConstant.WF.mono {env env' : VEnv} (henv : env ≤ env') {ci : VConstant} :
    ci.WF env → ci.WF env'
  | ⟨u, h⟩ => ⟨u, h.mono henv⟩

theorem VDefEq.WF.mono {env env' : VEnv} (henv : env ≤ env') {df : VDefEq} : df.WF env → df.WF env'
  | ⟨h1, h2⟩ => ⟨h1.mono henv, h2.mono henv⟩

namespace VEnv

theorem Ordered.constWF (H : Ordered env) (h : env.constants n = some (some ci)) : ci.WF env := by
  induction H with
  | nil => cases h
  | const _ h2 h3 ih =>
    refine .mono (addConst_le h3) ?_
    unfold addConst at h3; split at h3 <;> cases h3
    simp at h; split at h
    · cases h; exact h2 _ rfl
    · exact ih h
  | defeq _ _ ih => exact .mono addDefEq_le (ih h)

theorem Ordered.defEqWF (H : Ordered env) (h : env.defeqs df) : df.WF env := by
  induction H with
  | nil => cases h
  | const _ _ h3 ih =>
    refine .mono (addConst_le h3) (ih ?_)
    unfold addConst at h3; split at h3 <;> cases h3; exact h
  | defeq _ _ ih =>
    refine .mono addDefEq_le ?_
    obtain rfl | h := h
    · assumption
    · exact ih h

variable {env : VEnv} (henv : env.Ordered) in
theorem CtxWF.closed (h : CtxWF env U Γ) : CtxClosed Γ :=
  match Γ, h with
  | [], _ => trivial
  | _::_, ⟨h1, _, h2⟩ => ⟨h1.closed, h2.closedN henv h1.closed⟩

variable {env : VEnv} (henv : env.Ordered) in
theorem IsDefEq.weakN (W : Ctx.LiftN n k Γ Γ') (H : env.IsDefEq U Γ e1 e2 A) :
    env.IsDefEq U Γ' (e1.liftN n k) (e2.liftN n k) (A.liftN n k) := by
  induction H generalizing k Γ' with
  | bvar h => refine .bvar (h.weakN W)
  | const h1 h2 h3 =>
    rw [(henv.closedC h1).instL.liftN_eq (Nat.zero_le _)]
    exact .const h1 h2 h3
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | appDF _ _ ih1 ih2 => exact liftN_inst_hi .. ▸ .appDF (ih1 W) (ih2 W)
  | lamDF _ _ ih1 ih2 => exact .lamDF (ih1 W) (ih2 W.succ)
  | forallEDF _ _ ih1 ih2 => exact .forallEDF (ih1 W) (ih2 W.succ)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ ih1 ih2 =>
    exact VExpr.liftN_inst_hi .. ▸ VExpr.liftN_instN_hi .. ▸ .beta (ih1 W.succ) (ih2 W)
  | eta _ ih =>
    have := IsDefEq.eta (ih W)
    simp [liftN]; rwa [← lift_liftN']
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 h3 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
    rw [
      hA1.instL.liftN_eq (Nat.zero_le _),
      hA2.instL.liftN_eq (Nat.zero_le _),
      hA3.instL.liftN_eq (Nat.zero_le _)]
    exact .extra h1 h2 h3

variable {env : VEnv} (henv : env.Ordered) in
theorem HasType.weakN (W : Ctx.LiftN n k Γ Γ') (H : env.HasType U Γ e A) :
    env.HasType U Γ' (e.liftN n k) (A.liftN n k) := IsDefEq.weakN henv W H

variable {env : VEnv} (henv : env.Ordered) in
theorem IsType.weakN (W : Ctx.LiftN n k Γ Γ') (H : env.IsType U Γ A) :
    env.IsType U Γ' (A.liftN n k) := let ⟨_, h⟩ := H; ⟨_, h.weakN henv W⟩

variable {env : VEnv} (henv : env.Ordered) in
theorem IsDefEq.weak (H : env.IsDefEq U Γ e1 e2 A) :
    env.IsDefEq U (B::Γ) e1.lift e2.lift A.lift := H.weakN henv .one

variable {env : VEnv} (henv : env.Ordered) in
theorem HasType.weak0 (H : env.HasType U [] e A) : env.HasType U Γ e A := by
  have ⟨h1, _, h2⟩ := H.closedN' henv.closed ⟨⟩
  simpa [h1.liftN_eq (Nat.zero_le _), h2.liftN_eq (Nat.zero_le _)] using H.weakN henv (.zero Γ rfl)

variable {env : VEnv} (henv : env.Ordered) in
theorem CtxWF.lookup (h : CtxWF env U Γ) (hL : Lookup Γ n A) : env.IsType U Γ A :=
  match hL, h with
  | .zero, ⟨h1, h2⟩ => h2.weakN henv .one
  | .succ hL, ⟨h1, h2⟩ => (h1.lookup hL).weakN henv .one

variable {env : VEnv} {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U') in
theorem IsDefEq.instL (H : env.IsDefEq U Γ e1 e2 A) :
    env.IsDefEq U' (Γ.map (VExpr.instL ls)) (e1.instL ls) (e2.instL ls) (A.instL ls) := by
  induction H with
  | bvar h => refine .bvar h.instL
  | @const _ _ ls' _ h1 h2 h3 =>
    simp [VExpr.instL, VExpr.instL_instL]
    exact .const h1 (by simp [h2, VLevel.WF.inst hls]) (by simp [h3])
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF _ _ h3 =>
    exact .sortDF (VLevel.WF.inst hls) (VLevel.WF.inst hls) (VLevel.inst_congr_l h3)
  | appDF _ _ ih1 ih2 => exact VExpr.instL_instN ▸ .appDF ih1 ih2
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ ih1 ih2 => simpa using .beta ih1 ih2
  | eta _ ih => simpa [VExpr.instL] using .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 =>
    simp [VExpr.instL, VExpr.instL_instL]
    exact .extra h1 (by simp [h2, VLevel.WF.inst hls]) (by simp [h3])

theorem HasType.instL {env : VEnv} (hls : ∀ l ∈ ls, l.WF U') (H : env.HasType U Γ e A) :
    env.HasType U' (Γ.map (VExpr.instL ls)) (e.instL ls) (A.instL ls) := IsDefEq.instL hls H

theorem IsType.instL {env : VEnv} (hls : ∀ l ∈ ls, l.WF U') (H : env.IsType U Γ A) :
    env.IsType U' (Γ.map (VExpr.instL ls)) (A.instL ls) := let ⟨_, h⟩ := H; ⟨_, h.instL hls⟩

variable {env : VEnv} (henv : env.Ordered) (h₀ : env.HasType U Γ₀ e₀ A₀) in
theorem IsDefEq.instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : env.IsDefEq U Γ₁ e1 e2 A) :
    env.IsDefEq U Γ (e1.inst e₀ k) (e2.inst e₀ k) (A.inst e₀ k) := by
  induction H generalizing Γ k with
  | @bvar _ i ty h =>
    dsimp [inst]
    induction W generalizing i ty with
    | zero =>
      cases h with simp [inst_lift]
      | zero => exact h₀
      | succ h => exact .bvar h
    | succ _ ih =>
      cases h with (simp; rw [Nat.add_comm, ← VExpr.liftN_instN_lo (hj := Nat.zero_le _)])
      | zero => exact .bvar .zero
      | succ h => exact (ih h).weak henv
  | const h1 h2 h3 =>
    rw [(henv.closedC h1).instL.instN_eq (Nat.zero_le _)]
    exact .const h1 h2 h3
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | appDF _ _ ih1 ih2 => exact VExpr.inst_inst_hi .. ▸ .appDF (ih1 W) (ih2 W)
  | lamDF _ _ ih1 ih2 => exact .lamDF (ih1 W) (ih2 W.succ)
  | forallEDF _ _ ih1 ih2 => exact .forallEDF (ih1 W) (ih2 W.succ)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ ih1 ih2 =>
    exact VExpr.inst_inst_hi .. ▸ VExpr.inst_inst_hi .. ▸ .beta (ih1 W.succ) (ih2 W)
  | @eta _ e A B _ ih =>
    have := IsDefEq.eta (ih W)
    rw [lift, VExpr.liftN_instN_lo (hj := Nat.zero_le _), Nat.add_comm] at this
    simpa [inst]
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 h3 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
    rw [
      hA1.instL.instN_eq (Nat.zero_le _),
      hA2.instL.instN_eq (Nat.zero_le _),
      hA3.instL.instN_eq (Nat.zero_le _)]
    exact .extra h1 h2 h3

theorem HasType.instN {env : VEnv} (henv : env.Ordered) (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (H : env.HasType U Γ₁ e A) (h₀ : env.HasType U Γ₀ e₀ A₀) :
    env.HasType U Γ (e.inst e₀ k) (A.inst e₀ k) := IsDefEq.instN henv h₀ W H

theorem IsType.instN {env : VEnv} (henv : env.Ordered) (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (H : env.IsType U Γ₁ A) (h₀ : env.HasType U Γ₀ e₀ A₀) :
    env.IsType U Γ (A.inst e₀ k) := let ⟨_, h⟩ := H; ⟨_, h.instN henv W h₀⟩

-- variable {env : VEnv} (henv : env.Ordered) (h₀ : env.IsDefEq U Γ₀ e₀ e₀' A₀) in
-- theorem IsDefEq.instDF' (H : env.IsDefEq U (A::Γ) e1 e2 A) :
--     env.IsDefEq U Γ (e1.inst e₀) (e2.inst e₀') (A.inst e₀) := by
--   refine .trans _ (.beta _ _)

theorem IsDefEq.defeqDF_l (henv : Ordered env) (h1 : env.IsDefEq U Γ A A' (.sort u))
    (h2 : env.IsDefEq U (A::Γ) e1 e2 B) : env.IsDefEq U (A'::Γ) e1 e2 B := by
  simpa [instN_bvar0] using
    h2.weakN henv (.succ (.one (A := A'))) |>.instN henv
      (h1.weakN henv (.one (A := A')) |>.symm.defeq (.bvar .zero)) .zero

theorem HasType.defeq_l (henv : Ordered env) (h1 : env.IsDefEq U Γ A A' (.sort u))
    (h2 : env.HasType U (A::Γ) e B) : env.HasType U (A'::Γ) e B := h1.defeqDF_l henv h2

variable {env : VEnv} (henv : env.Ordered)
  (envIH : env.OnTypes fun U e _ => ∀ A B, e = A.forallE B →
    env.IsType U [] A ∧ env.IsType U [A] B) in
theorem IsDefEq.forallE_inv'
    (H : env.IsDefEq U Γ e1 e2 V) (eq : e1 = A.forallE B ∨ e2 = A.forallE B) :
    env.IsType U Γ A ∧ env.IsType U (A::Γ) B := by
  induction H generalizing A B with
  | symm _ ih => exact ih eq.symm
  | trans _ _ ih1 ih2
  | proofIrrel _ h1 h2 _ ih1 ih2 =>
    obtain eq | eq := eq
    · exact ih1 (.inl eq)
    · exact ih2 (.inr eq)
  | forallEDF h1 h2 =>
    obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq
    · exact ⟨⟨_, h1.hasType.1⟩, _, h2.hasType.1⟩
    · exact ⟨⟨_, h1.hasType.2⟩, _, h2.hasType.2.defeq_l henv h1⟩
  | defeqDF _ _ _ ih2 => exact ih2 eq
  | @beta _ _ e _ _ h1 h2 ih1 ih2 =>
    obtain ⟨⟨⟩⟩ | eq := eq
    cases e with
    | bvar i =>
      cases i with simp [inst] at eq
      | zero => exact ih2 (.inl eq)
    | forallE A B =>
      cases eq
      let ⟨A1, A2⟩ := ih1 (.inl rfl)
      exact ⟨A1.instN henv .zero h2, A2.instN henv (.succ .zero) h2⟩
    | _ => cases eq
  | eta _ ih =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih (.inl eq)
  | @extra df ls Γ h1 h2 =>
    suffices ∀ e, VExpr.instL ls e = VExpr.forallE A B →
        (∀ A B, e = VExpr.forallE A B → IsType env df.uvars [] A ∧ IsType env df.uvars [A] B) →
        IsType env U Γ A ∧ IsType env U (A :: Γ) B by
      have ⟨A1, A2⟩ := envIH.2 h1
      cases eq <;> exact this _ ‹_› ‹_›
    intro e eq IH
    cases e <;> cases eq; rename_i A B
    let ⟨⟨_, A1⟩, v, A2⟩ := IH _ _ rfl
    refine ⟨⟨_, (A1.instL h2).weak0 henv⟩, v.inst ls, ?_⟩
    have := (A2.instL h2).weakN henv (.succ (.zero Γ))
    have C1 := (A1.instL h2).closedN henv ⟨⟩
    have C2 := (A2.instL h2).closedN henv ⟨⟨⟩, C1⟩
    rw [C1.liftN_eq (Nat.zero_le _), C2.liftN_eq (by exact Nat.le_refl _)] at this
    simpa [liftN]
  | _ => match eq with.

theorem HasType.forallE_inv (henv : Ordered env) (H : env.HasType U Γ (A.forallE B) V) :
    env.IsType U Γ A ∧ env.IsType U (A::Γ) B := by
  refine H.forallE_inv' henv ?_ (.inl rfl)
  exact henv.induction
    (fun env U e _ => ∀ A B, e = forallE A B → IsType env U [] A ∧ IsType env U [A] B)
    (fun le H A B eq => (H A B eq).imp (.mono le) (.mono le))
    (fun henv IH H A B eq => H.forallE_inv' henv IH (.inl eq))

theorem IsType.forallE_inv (henv : Ordered env) (H : env.IsType U Γ (A.forallE B)) :
    env.IsType U Γ A ∧ env.IsType U (A::Γ) B := let ⟨_, h⟩ := H; h.forallE_inv henv

variable {env : VEnv} (henv : env.Ordered) in
theorem IsDefEq.sort_inv'
    (H : env.IsDefEq U Γ e1 e2 V) (eq : e1 = .sort u ∨ e2 = .sort u) : u.WF U := by
  induction H with
  | symm _ ih => exact ih eq.symm
  | trans _ _ ih1 ih2
  | proofIrrel _ _ _ _ ih1 ih2 =>
    obtain eq | eq := eq <;> [exact ih1 (.inl eq); exact ih2 (.inr eq)]
  | sortDF => obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq <;> assumption
  | defeqDF _ _ _ ih2 => exact ih2 eq
  | @beta _ _ e _ _ h1 _ ih1 ih2 =>
    obtain ⟨⟨⟩⟩ | eq := eq
    cases e with
    | bvar i =>
      cases i with simp [inst] at eq
      | zero => exact ih2 (.inl eq)
    | _ => cases eq <;> exact ih1 (.inl rfl)
  | eta _ ih =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih (.inl eq)
  | @extra df ls _ h1 h2 =>
    suffices ∀ e, VExpr.instL ls e = .sort u → HasType env df.uvars [] e df.type → u.WF U by
      have ⟨A1, A2⟩ := henv.defEqWF h1
      cases eq <;> exact this _ ‹_› ‹_›
    intro e eq IH
    cases e <;> cases eq; rename_i u
    exact VLevel.WF.inst h2
  | _ => match eq with.

theorem HasType.sort_inv (henv : Ordered env) (H : env.HasType U Γ (.sort u) V) : u.WF U :=
  H.sort_inv' henv (.inl rfl)

theorem IsType.sort_inv (henv : Ordered env) (H : env.IsType U Γ (.sort u)) : u.WF U :=
  let ⟨_, h⟩ := H; h.sort_inv henv

variable {env : VEnv} (henv : Ordered env)
  (envIH : env.OnTypes fun U e A => env.HasType U [] e A ∧ env.IsType U [] A) in
theorem IsDefEq.isType' (hΓ : env.CtxWF U Γ) (H : env.IsDefEq U Γ e1 e2 A) : env.IsType U Γ A := by
  induction H with
  | bvar h => exact hΓ.lookup henv h
  | const h1 h2 =>
    let ⟨_, h, _⟩ := envIH.1 h1
    exact ⟨_, (h.instL h2).weak0 henv⟩
  | proofIrrel h1 => exact ⟨_, h1⟩
  | extra h1 h2 =>
    have ⟨_, _, _, h⟩ := envIH.2 h1
    exact ⟨_, (h.instL h2).weak0 henv⟩
  | sortDF h1 => exact ⟨_, .sort h1⟩
  | symm _ ih => exact ih hΓ
  | trans _ _ ih1 => exact ih1 hΓ
  | appDF _ h2 ih1 => exact ((ih1 hΓ).forallE_inv henv).2.instN henv .zero h2.hasType.1
  | lamDF h1 _ _ ih2 =>
    let ⟨_, h⟩ := ih2 ⟨hΓ, _, h1.hasType.1⟩
    exact ⟨_, .forallE h1.hasType.1 h⟩
  | forallEDF h1 _ ih1 ih2 =>
    exact ⟨_, .sort ⟨(ih1 hΓ).sort_inv henv, (ih2 ⟨hΓ, _, h1.hasType.1⟩).sort_inv henv⟩⟩
  | defeqDF h1 => exact ⟨_, h1.hasType.2⟩
  | beta _ h2 ih1 ih2 =>
    have ⟨_, h⟩ := ih2 hΓ
    exact (ih1 ⟨hΓ, _, h.hasType.2⟩).instN henv .zero h2
  | eta _ ih => exact ih hΓ

theorem Ordered.isType (H : Ordered env) :
    env.OnTypes fun U e A => env.HasType U [] e A ∧ env.IsType U [] A :=
  H.induction (fun env U e A => env.HasType U [] e A ∧ env.IsType U [] A)
    (fun h1 h2 => h2.imp (.mono h1) (.mono h1))
    (fun henv ih h => ⟨h, h.isType' henv ih trivial⟩)

variable {env : VEnv} (henv : Ordered env) in
theorem IsDefEq.isType (hΓ : env.CtxWF U Γ) (H : env.IsDefEq U Γ e1 e2 A) : env.IsType U Γ A :=
  H.isType' henv henv.isType hΓ

/- depends on church-rosser
variable {env : VEnv} (henv : env.Ordered) in
theorem IsDefEq.weakN_inv (W : Ctx.LiftN n k Γ Γ')
    (H : env.IsDefEq U Γ' (e1.liftN n k) (e2.liftN n k) (A.liftN n k)) :
    env.IsDefEq U Γ e1 e2 A := by
  generalize eq1 : e1.liftN n k = e1', eq2 : e2.liftN n k = e2', eqA : A.liftN n k = A' at H
  induction H generalizing k e1 e2 A with
  | bvar h =>
    cases eqA; cases e1 <;> cases eq1; cases e2 <;> injection eq2
    cases liftVar_inj.1 ‹_›; exact .bvar (h.weakN_inv W)
  | @const c ci ls Γ h1 h2 h3 =>
    cases e1 <;> cases eq1; cases e2 <;> cases eq2
    rw [VExpr.ClosedN.liftN_eq_rev (eqA ▸ (henv.closedC h1).instL) (Nat.zero_le _)] at eqA
    exact eqA ▸ .const h1 h2 h3
  | symm _ ih => exact .symm (ih W eq2 eq1 eqA)
  | trans _ _ ih1 ih2 => sorry
  -- | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  -- | appDF _ _ ih1 ih2 => exact liftN_inst_hi .. ▸ .appDF (ih1 W) (ih2 W)
  -- | lamDF _ _ ih1 ih2 => exact .lamDF (ih1 W) (ih2 W.succ)
  -- | forallEDF _ _ ih1 ih2 => exact .forallEDF (ih1 W) (ih2 W.succ)
  -- | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  -- | beta _ _ ih1 ih2 =>
  --   exact VExpr.liftN_inst_hi .. ▸ VExpr.liftN_instN_hi .. ▸ .beta (ih1 W.succ) (ih2 W)
  -- | eta _ ih =>
  --   have := IsDefEq.eta (ih W)
  --   simp [liftN]; rwa [← lift_liftN']
  -- | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  -- | extra h1 h2 h3 =>
  --   have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
  --   rw [
  --     hA1.instL.liftN_eq (Nat.zero_le _),
  --     hA2.instL.liftN_eq (Nat.zero_le _),
  --     hA3.instL.liftN_eq (Nat.zero_le _)]
  --   exact .extra h1 h2 h3
  | _ => sorry

variable {env : VEnv} (henv : env.Ordered) in
theorem HasType.weakN_inv (W : Ctx.LiftN n k Γ Γ')
    (H : env.HasType U Γ' (e.liftN n k) (A.liftN n k)) :
    env.HasType U Γ e A := IsDefEq.weakN_inv henv W H

variable {env : VEnv} (henv : env.Ordered) in
theorem IsType.weakN_inv (W : Ctx.LiftN n k Γ Γ') (H : env.IsType U Γ' (A.liftN n k)) :
    env.IsType U Γ A := let ⟨_, h⟩ := H; ⟨_, h.weakN_inv henv W⟩
-/
