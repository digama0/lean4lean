import Lean4Lean.Theory.Typing.Lemmas

namespace Lean4Lean
namespace VEnv

open VExpr

section
set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:30 => IsDefEqStrong Γ e e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:30 => IsDefEqStrong Γ e1 e2 A
variable (env : VEnv) (uvars : Nat)

inductive IsDefEqStrong : List VExpr → VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup Γ i A → u.WF uvars → Γ ⊢ A : .sort u → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  | sortDF :
    l.WF uvars → l'.WF uvars → l ≈ l' →
    Γ ⊢ .sort l ≡ .sort l' : .sort (.succ l)
  | constDF :
    env.constants c = some (some ci) →
    (∀ l ∈ ls, l.WF uvars) →
    (∀ l ∈ ls', l.WF uvars) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    u.WF uvars →
    [] ⊢ ci.type.instL ls : .sort u →
    [] ⊢ ci.type.instL ls' : .sort u →
    Γ ⊢ ci.type.instL ls : .sort u →
    Γ ⊢ ci.type.instL ls' : .sort u →
    Γ ⊢ .const c ls ≡ .const c ls' : ci.type.instL ls
  | appDF :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A : .sort u →
    A::Γ ⊢ B : .sort v →
    Γ ⊢ f ≡ f' : .forallE A B →
    Γ ⊢ a ≡ a' : A →
    Γ ⊢ B.inst a ≡ B.inst a' : .sort v →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | lamDF :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ B : .sort v →
    A'::Γ ⊢ B : .sort v →
    A::Γ ⊢ body ≡ body' : B →
    A'::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : .sort v →
    A'::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF :
    u.WF uvars → Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta :
    u.WF uvars → v.WF uvars → Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v →
    A::Γ ⊢ e : B → Γ ⊢ e' : A →
    Γ ⊢ B.inst e' : .sort v →
    Γ ⊢ e.inst e' : B.inst e' →
    Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A : .sort u →
    A::Γ ⊢ B : .sort v →
    A.lift::A::Γ ⊢ B.liftN 1 1 : .sort v →
    Γ ⊢ e : .forallE A B →
    A::Γ ⊢ e.lift : .forallE A.lift (B.liftN 1 1) →
    Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel :
    Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p →
    Γ ⊢ h ≡ h' : p
  | extra :
    env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
    u.WF uvars →
    [] ⊢ df.type.instL ls : .sort u →
    [] ⊢ df.lhs.instL ls : df.type.instL ls →
    [] ⊢ df.rhs.instL ls : df.type.instL ls →
    Γ ⊢ df.lhs.instL ls : df.type.instL ls →
    Γ ⊢ df.rhs.instL ls : df.type.instL ls →
    Γ ⊢ df.lhs.instL ls ≡ df.rhs.instL ls : df.type.instL ls

end

theorem IsDefEqStrong.hasType {env : VEnv}
    (H : env.IsDefEqStrong U Γ e1 e2 A) :
    env.IsDefEqStrong U Γ e1 e1 A ∧ env.IsDefEqStrong U Γ e2 e2 A :=
  ⟨H.trans H.symm, H.symm.trans H⟩

variable (henv : Ordered env) in
theorem IsDefEqStrong.weakN (W : Ctx.LiftN n k Γ Γ') (H : env.IsDefEqStrong U Γ e1 e2 A) :
    env.IsDefEqStrong U Γ' (e1.liftN n k) (e2.liftN n k) (A.liftN n k) := by
  induction H generalizing k Γ' with
  | bvar h1 h2 h3 => refine .bvar (h1.weakN W) h2 (h3.weakN W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ ih3 ih4 =>
    simp [(henv.closedC h1).instL.liftN_eq (Nat.zero_le _)] at ih3 ih4 ⊢
    exact .constDF h1 h2 h3 h4 h5 h6 h7 h8 (ih3 W) (ih4 W)
  | appDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    refine liftN_inst_hi .. ▸ .appDF h1 h2 (ih1 W) (ih2 W.succ) (ih3 W) (ih4 W) ?_
    exact liftN_inst_hi .. ▸ liftN_inst_hi .. ▸ ih5 W
  | lamDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact .lamDF h1 h2 (ih1 W) (ih2 W.succ) (ih3 W.succ) (ih4 W.succ) (ih5 W.succ)
  | forallEDF h1 h2 _ _ _ ih1 ih2 ih3 => exact .forallEDF h1 h2 (ih1 W) (ih2 W.succ) (ih3 W.succ)
  | defeqDF h1 _ _ ih1 ih2 => exact .defeqDF h1 (ih1 W) (ih2 W)
  | beta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    refine liftN_inst_hi .. ▸ liftN_instN_hi .. ▸ .beta h1 h2
      (ih1 W) (ih2 W.succ) (ih3 W.succ) (ih4 W)
      (liftN_instN_hi .. ▸ ih5 W :)
      (liftN_instN_hi .. ▸ liftN_instN_hi .. ▸ ih6 W :)
  | @eta Γ a u B v e h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    have := IsDefEqStrong.eta h1 h2 (ih1 W) (ih2 W.succ) ?_ (ih4 W) ?_
    · simp [liftN]; rwa [← lift_liftN']
    · specialize ih3 W.succ.succ
      have := liftN'_comm B n 1 (k+1) 1 (Nat.le_add_left ..)
      rw [Nat.add_comm 1] at this; rwa [← this, ← lift_liftN'] at ih3
    · have ih5 : IsDefEqStrong _ _ _ _ _ (liftN n (lift (forallE ..)) _) := ih5 W.succ
      rwa [← lift_liftN', ← lift_liftN'] at ih5
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 h3 h4 h5 h6 h7 _ _ _ _ _ ih4 ih5 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
    simp [
      hA1.instL.liftN_eq (Nat.zero_le _),
      hA2.instL.liftN_eq (Nat.zero_le _),
      hA3.instL.liftN_eq (Nat.zero_le _)] at ih4 ih5 ⊢
    exact IsDefEqStrong.extra h1 h2 h3 h4 h5 h6 h7 (ih4 W) (ih5 W)

theorem IsDefEqStrong.defeq (H : IsDefEqStrong env U Γ e1 e2 A) : env.IsDefEq U Γ e1 e2 A := by
  induction H with
  | bvar h => exact .bvar h
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF _ _ _ _ _ _ _ _ _ ih1 ih2 => exact .appDF ih1 ih2
  | lamDF _ _ _ _ _ _ _ ih1 _ _ ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ _ _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ _ _ _ _ _ _ _ _ ih1 ih2 => exact .beta ih1 ih2
  | eta _ _ _ _ _ _ _ _ _ _ ih => exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 => exact .extra h1 h2 h3

variable {env env' : VEnv} (henv : env ≤ env') in
theorem IsDefEqStrong.mono
    (H : env.IsDefEqStrong U Γ e1 e2 A) : env'.IsDefEqStrong U Γ e1 e2 A := by
  induction H with
  | bvar h1 h2 _ ih => exact .bvar h1 h2 ih
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 h6 _ _ _ _ ih1 ih2 ih3 ih4 =>
    exact .constDF (henv.1 _ _ h1) h2 h3 h4 h5 h6 ih1 ih2 ih3 ih4
  | appDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 => exact .appDF h1 h2 ih1 ih2 ih3 ih4 ih5
  | lamDF h1 h2  _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 => exact .lamDF h1 h2 ih1 ih2 ih3 ih4 ih5
  | forallEDF h1 h2 _ _ _ ih1 ih2 ih3 => exact .forallEDF h1 h2 ih1 ih2 ih3
  | defeqDF h1 _ _ ih1 ih2 => exact .defeqDF h1 ih1 ih2
  | beta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 => exact .beta h1 h2 ih1 ih2 ih3 ih4 ih5 ih6
  | eta h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 => exact .eta h1 h2 ih1 ih2 ih3 ih4 ih5
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 h4 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact .extra (henv.2 _ h1) h2 h3 h4 ih1 ih2 ih3 ih4 ih5

variable (henv : Ordered env) in
theorem IsDefEqStrong.weak0 (H : env.IsDefEqStrong U [] e1 e2 A) :
    env.IsDefEqStrong U Γ e1 e2 A := by
  have ⟨h1, h2, h3⟩ := H.defeq.closedN' henv.closed ⟨⟩
  simpa [h1.liftN_eq (Nat.zero_le _), h2.liftN_eq (Nat.zero_le _),
    h3.liftN_eq (Nat.zero_le _)] using H.weakN henv (.zero Γ rfl)

variable {env : VEnv} {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U') in
theorem IsDefEqStrong.instL (H : env.IsDefEqStrong U Γ e1 e2 A) :
    env.IsDefEqStrong U' (Γ.map (VExpr.instL ls)) (e1.instL ls) (e2.instL ls) (A.instL ls) := by
  induction H with
  | bvar h _ _ ih =>
    exact .bvar h.instL (.inst hls) ih
  | constDF h1 h2 h3 h4 h5 _ _ _ _ _ ih1 ih2 ih3 ih4 =>
    simp [VExpr.instL, VExpr.instL_instL] at ih1 ih2 ih3 ih4 ⊢
    exact .constDF h1
      (by simp [h2, VLevel.WF.inst hls]) (by simp [h3, VLevel.WF.inst hls]) (by simp [h4])
      (by simpa using h5.imp fun _ _ => VLevel.inst_congr_l) (.inst hls) ih1 ih2 ih3 ih4
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF _ _ h3 =>
    exact .sortDF (VLevel.WF.inst hls) (VLevel.WF.inst hls) (VLevel.inst_congr_l h3)
  | appDF _ _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact instL_instN ▸ .appDF (.inst hls) (.inst hls)
      ih1 ih2 ih3 ih4 (instL_instN ▸ instL_instN ▸ ih5)
  | lamDF _ _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact .lamDF (.inst hls) (.inst hls) ih1 ih2 ih3 ih4 ih5
  | forallEDF _ _ _ _ _ ih1 ih2 ih3 =>
    exact .forallEDF (.inst hls) (.inst hls) ih1 ih2 ih3
  | defeqDF _ _ _ ih1 ih2 =>
    exact .defeqDF (.inst hls) ih1 ih2
  | beta _ _ _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    simpa using .beta (.inst hls) (.inst hls) ih1 ih2 ih3 ih4
      (by simpa using ih5) (by simpa using ih6)
  | eta _ _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    simpa [VExpr.instL] using .eta (.inst hls) (.inst hls) ih1 ih2
      (by simpa using ih3) ih4 (by simpa [VExpr.instL] using ih5)
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    simp [VExpr.instL, VExpr.instL_instL] at ih1 ih2 ih3 ih4 ih5 ⊢
    exact .extra h1 (by simp [h2, VLevel.WF.inst hls]) (by simp [h3])
      (.inst hls) ih1 ih2 ih3 ih4 ih5

def CtxStrong (env : VEnv) (U Γ) :=
  OnCtx Γ fun Γ A => ∃ u, env.IsDefEqStrong U Γ A A (.sort u)

variable (henv : Ordered env) in
nonrec theorem CtxStrong.lookup {Γ} (H : CtxStrong env U Γ) (h : Lookup Γ i A) :
    ∃ u, env.IsDefEqStrong U Γ A A (.sort u) :=
  H.lookup h fun ⟨_, h⟩ => ⟨_, h.weakN henv .one⟩

theorem CtxStrong.defeq {Γ} (H : CtxStrong env U Γ) : OnCtx Γ (env.IsType U) :=
  H.mono fun ⟨_, h⟩ => ⟨_, h.defeq⟩

variable (henv : Ordered env) (h₀ : env.IsDefEqStrong U Γ₀ e₀ e₀ A₀) (hΓ₀ : CtxStrong env U Γ₀) in
theorem IsDefEqStrong.instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : env.IsDefEqStrong U Γ₁ e1 e2 A)
    (hΓ : CtxStrong env U Γ) :
    env.IsDefEqStrong U Γ (e1.inst e₀ k) (e2.inst e₀ k) (A.inst e₀ k) := by
  induction H generalizing Γ k with
  | @bvar _ i ty _ h _ h2 ih =>
    dsimp [inst]; clear h2 ih
    induction W generalizing i ty with
    | zero =>
      cases h with simp [inst_lift]
      | zero => exact h₀
      | succ h =>
        let ⟨u, hty⟩ := hΓ₀.lookup henv h
        exact .bvar h (hty.defeq.sort_r henv hΓ₀.defeq) hty
    | succ _ ih =>
      cases h with (simp; rw [Nat.add_comm, ← liftN_instN_lo (hj := Nat.zero_le _)])
      | zero =>
        let ⟨u, hty⟩ := hΓ.lookup henv .zero
        exact .bvar .zero (hty.defeq.sort_r henv hΓ.defeq) hty
      | succ h => exact (ih h hΓ.1).weakN henv .one
  | symm _ ih => exact .symm (ih W hΓ)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W hΓ) (ih2 W hΓ)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ ih3 ih4 =>
    simp [(henv.closedC h1).instL.instN_eq (Nat.zero_le _)] at ih3 ih4 ⊢
    exact .constDF h1 h2 h3 h4 h5 h6 h7 h8 (ih3 W hΓ) (ih4 W hΓ)
  | appDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact inst0_inst_hi .. ▸ .appDF h1 h2
      (ih1 W hΓ) (ih2 W.succ ⟨hΓ, _, ih1 W hΓ⟩)
      (ih3 W hΓ) (ih4 W hΓ) (inst0_inst_hi .. ▸ inst0_inst_hi .. ▸ ih5 W hΓ)
  | lamDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact
      have hΓ' := ⟨hΓ, _, (ih1 W hΓ).hasType.1⟩
      have hΓ'' := ⟨hΓ, _, (ih1 W hΓ).hasType.2⟩
      .lamDF h1 h2 (ih1 W hΓ) (ih2 W.succ hΓ') (ih3 W.succ hΓ'') (ih4 W.succ hΓ') (ih5 W.succ hΓ'')
  | forallEDF h1 h2 _ _ _ ih1 ih2 ih3 =>
    exact .forallEDF h1 h2 (ih1 W hΓ)
      (ih2 W.succ ⟨hΓ, _, (ih1 W hΓ).hasType.1⟩) (ih3 W.succ ⟨hΓ, _, (ih1 W hΓ).hasType.2⟩)
  | defeqDF h1 _ _ ih1 ih2 => exact .defeqDF h1 (ih1 W hΓ) (ih2 W hΓ)
  | beta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    rw [inst0_inst_hi, inst0_inst_hi]; exact
      have hΓ' := ⟨hΓ, _, ih1 W hΓ⟩
      .beta h1 h2
        (ih1 W hΓ) (ih2 W.succ hΓ') (ih3 W.succ hΓ') (ih4 W hΓ)
        (inst0_inst_hi .. ▸ ih5 W hΓ) (inst0_inst_hi .. ▸ inst0_inst_hi .. ▸ ih6 W hΓ)
  | eta h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    have :=
      have hΓ' := ⟨hΓ, _, (ih1 W hΓ).hasType.1⟩
      IsDefEqStrong.eta h1 h2 (ih1 W hΓ) (ih2 W.succ hΓ')
        (by
          have := ih3 W.succ.succ ⟨hΓ', _, by
            rw [← lift_instN_lo]; exact (ih1 W hΓ).hasType.1.weakN henv .one⟩
          rwa [lift_instN_lo, liftN_instN_lo (hj := Nat.le_add_left ..), Nat.add_comm 1])
        (ih4 W hΓ)
        (by
          have := ih5 W.succ hΓ'
          simp only [inst, ← lift_instN_lo] at this
          rwa [liftN_instN_lo (hj := Nat.le_add_left ..), Nat.add_comm 1])
    rw [lift, liftN_instN_lo (hj := Nat.zero_le _), Nat.add_comm] at this
    simpa [inst]
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W hΓ) (ih2 W hΓ) (ih3 W hΓ)
  | extra h1 h2 h3 h4 h5 h6 h7 _ _ _ _ _ ih4 ih5 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
    simp [
      hA1.instL.instN_eq (Nat.zero_le _),
      hA2.instL.instN_eq (Nat.zero_le _),
      hA3.instL.instN_eq (Nat.zero_le _)] at ih4 ih5 ⊢
    exact .extra h1 h2 h3 h4 h5 h6 h7 (ih4 W hΓ) (ih5 W hΓ)

theorem IsDefEqStrong.defeqDF_l (henv : Ordered env) (hΓ : CtxStrong env U Γ)
    (h1 : env.IsDefEqStrong U Γ A A' (.sort u))
    (h2 : env.IsDefEqStrong U (A::Γ) e1 e2 B) : env.IsDefEqStrong U (A'::Γ) e1 e2 B := by
  simpa [instN_bvar0] using
    have hu := h1.defeq.sort_r henv hΓ.defeq
    have hΓ' := ⟨hΓ, _, h1.hasType.2⟩
    h1.weakN henv (.one (A := A'))
      |>.symm.defeqDF hu (.bvar .zero hu (h1.hasType.2.weakN henv .one))
      |>.instN henv hΓ' .zero (h2.weakN henv (.succ (.one (A := A')))) hΓ'

def EnvStrong (env : VEnv) (U : Nat) (e A : VExpr) : Prop :=
  env.IsDefEqStrong U [] e e A ∧
  (∃ u, env.IsDefEqStrong U [] A A (.sort u)) ∧
  ∀ A B, e = A.forallE B →
    (∃ u, env.IsDefEqStrong U [] A A (.sort u)) ∧
    (∃ u, env.IsDefEqStrong U [A] B B (.sort u))

variable (henv : Ordered env) (envIH : env.OnTypes (EnvStrong env)) in
theorem IsDefEqStrong.forallE_inv' (hΓ : CtxStrong env U Γ)
    (H : env.IsDefEqStrong U Γ e1 e2 V) (eq : e1 = A.forallE B ∨ e2 = A.forallE B) :
    (∃ u, env.IsDefEqStrong U Γ A A (.sort u)) ∧ ∃ v, env.IsDefEqStrong U (A::Γ) B B (.sort v) := by
  induction H generalizing A B with
  | symm _ ih => exact ih hΓ eq.symm
  | trans _ _ ih1 ih2
  | proofIrrel _ _ _ _ ih1 ih2 =>
    obtain eq | eq := eq
    · exact ih1 hΓ (.inl eq)
    · exact ih2 hΓ (.inr eq)
  | forallEDF _ _ h1 h2 =>
    obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq
    · exact ⟨⟨_, h1.hasType.1⟩, _, h2.hasType.1⟩
    · exact ⟨⟨_, h1.hasType.2⟩, _, h1.defeqDF_l henv hΓ h2.hasType.2⟩
  | defeqDF _ _ _ _ ih2 => exact ih2 hΓ eq
  | @beta _ _ _ _ _ e _ _ _ h1 _ _ h4 _ _ _ _ ih3 ih4 =>
    obtain ⟨⟨⟩⟩ | eq := eq
    cases e with
    | bvar i =>
      cases i with simp [inst] at eq
      | zero => exact ih4 hΓ (.inl eq)
    | forallE A B =>
      cases eq
      let ⟨⟨_, A1⟩, _, A2⟩ := ih3 ⟨hΓ, _, h1⟩ (.inl rfl)
      refine ⟨⟨_, h4.instN henv hΓ .zero A1 hΓ⟩, _, h4.instN henv hΓ (.succ .zero) A2 ?_⟩
      exact ⟨hΓ, _, h4.instN henv hΓ .zero A1 hΓ⟩
    | _ => cases eq
  | eta _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih hΓ (.inl eq)
  | @extra df ls _ Γ h1 h2 =>
    suffices ∀ e, VExpr.instL ls e = VExpr.forallE A B →
        EnvStrong env df.uvars e df.type →
        (∃ u, IsDefEqStrong env U Γ A A (.sort u)) ∧
        (∃ u, IsDefEqStrong env U (A :: Γ) B B (.sort u)) by
      have ⟨A1, A2⟩ := envIH.2 h1
      cases eq <;> exact this _ ‹_› ‹_›
    intro e eq IH
    cases e <;> cases eq; rename_i A B
    let ⟨⟨_, A1⟩, v, A2⟩ := IH.2.2 _ _ rfl
    refine ⟨⟨_, (A1.instL h2).weak0 henv⟩, v.inst ls, ?_⟩
    have := (A2.instL h2).weakN henv (.succ (.zero Γ))
    have C1 := (A1.instL h2).defeq.closedN henv ⟨⟩
    have C2 := (A2.instL h2).defeq.closedN henv ⟨⟨⟩, C1⟩
    rw [C1.liftN_eq (Nat.zero_le _), C2.liftN_eq (by exact Nat.le_refl _)] at this
    simpa [liftN]
  | _ => nomatch eq

variable (henv : Ordered env) (envIH : env.OnTypes (EnvStrong env)) in
theorem IsDefEqStrong.isType' (hΓ : CtxStrong env U Γ) (H : env.IsDefEqStrong U Γ e1 e2 A) :
    ∃ u, env.IsDefEqStrong U Γ A A (.sort u) := by
  induction H with
  | bvar h => exact hΓ.lookup henv h
  | symm _ ih => exact ih hΓ
  | trans _ _ ih1 => exact ih1 hΓ
  | sortDF h1 => exact ⟨_, .sortDF h1 h1 rfl⟩
  | constDF h1 h2 =>
    let ⟨_, h⟩ := envIH.1 h1
    exact ⟨_, (h.1.instL h2).weak0 henv⟩
  | appDF _ _ _ _ _ h4 _ _ _ ih3 =>
    let ⟨_, ih3⟩ := ih3 hΓ
    have ⟨_, _, ih3⟩ := ih3.forallE_inv' henv envIH hΓ (.inl rfl)
    exact ⟨_, h4.hasType.1.instN henv hΓ .zero ih3 hΓ⟩
  | lamDF h1 h2 h3 h4 => exact ⟨_, .forallEDF h1 h2 h3.hasType.1 h4 h4⟩
  | forallEDF h1 h2 => exact ⟨_, .sortDF ⟨h1, h2⟩ ⟨h1, h2⟩ rfl⟩
  | defeqDF _ h2 => exact ⟨_, h2.hasType.2⟩
  | beta _ _ _ h4 _ h6 => exact ⟨_, h6.hasType.1.instN henv hΓ .zero h4 hΓ⟩
  | eta _ _ _ _ _ _ _ _ _ _ ih => exact ih hΓ
  | proofIrrel h1 => exact ⟨_, h1⟩
  | extra h1 h2 =>
    have ⟨_, h⟩ := (envIH.2 h1).2.2.1
    exact ⟨_, (h.instL h2).weak0 henv⟩

theorem IsDefEqStrong.instDF
    (henv : Ordered env) (hΓ : CtxStrong env U Γ) (hu : u.WF U) (hv : v.WF U)
    (hA : env.IsDefEqStrong U Γ A A (.sort u))
    (hB : env.IsDefEqStrong U (A::Γ) B B (.sort v))
    (hf : env.IsDefEqStrong U (A::Γ) f f' B)
    (ha : env.IsDefEqStrong U Γ a a' A) :
    env.IsDefEqStrong U Γ (f.inst a) (f'.inst a') (B.inst a) :=
  have H2 {f f' B v}
      (hv : v.WF U)
      (hB : env.IsDefEqStrong U (A::Γ) B B (.sort v))
      (hf : env.IsDefEqStrong U (A::Γ) f f' B)
      (hi : IsDefEqStrong env U Γ (inst B a) (inst B a') (sort v)) :
      env.IsDefEqStrong U Γ (f.inst a) (f'.inst a') (B.inst a) :=
    have H1 {a f}
        (hf : env.IsDefEqStrong U (A::Γ) f f' B)
        (ha : IsDefEqStrong env U Γ a a A) :
        env.IsDefEqStrong U Γ (.app (.lam A f) a) (f.inst a) (B.inst a) :=
      IsDefEqStrong.beta hu hv hA hB hf.hasType.1 ha
        (ha.hasType.1.instN henv hΓ .zero hB hΓ)
        (ha.hasType.1.instN henv hΓ .zero hf.hasType.1 hΓ)
    (H1 hf ha.hasType.1).symm.trans <|
      .trans (.appDF hu hv hA hB (.lamDF hu hv hA hB hB hf hf) ha hi) <|
      .defeqDF hv (.symm hi) (H1 hf.hasType.2 ha.hasType.2)
  H2 hv hB hf <| H2 (v := v.succ) hv (.sortDF hv hv rfl) hB (.sortDF hv hv rfl)

variable (henv : Ordered env) (envIH : env.OnTypes (EnvStrong env)) in
theorem IsDefEq.strong' (hΓ : CtxStrong env U Γ)
    (H : env.IsDefEq U Γ e1 e2 A) : env.IsDefEqStrong U Γ e1 e2 A := by
  have hctx {Γ} (H : OnCtx Γ fun Γ A => ∃ u, env.IsDefEqStrong U Γ A A (.sort u)) :
     OnCtx Γ (env.IsType U) := H.mono fun ⟨_, h⟩ => ⟨_, h.defeq⟩
  induction H with
  | bvar h =>
    let ⟨u, hA⟩ := hΓ.lookup henv h
    exact .bvar h (hA.defeq.sort_r henv (hctx hΓ)) hA
  | symm _ ih => exact (ih hΓ).symm
  | trans _ _ ih1 ih2 => exact (ih1 hΓ).trans (ih2 hΓ)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | @constDF _ _ ls₁ ls₂ _ h1 h2 h3 h4 h5 =>
    let ⟨u, h6⟩ := envIH.1 h1
    have H1 := h6.1.instL h2
    have H2 := IsDefEqStrong.defeqDF (u := .succ _) (.inst h2)
      (.symm <| .sortDF (.inst h2) (.inst h3) (VLevel.inst_congr rfl h5)) <| h6.1.instL h3
    exact .constDF h1 h2 h3 h4 h5 (.inst h2) H1 H2 (H1.weak0 henv) (H2.weak0 henv)
  | appDF _ _ ih1 ih2 =>
    let ⟨_, h3⟩ := (ih1 hΓ).isType' henv envIH hΓ
    let ⟨⟨u, hA⟩, ⟨v, hB⟩⟩ := h3.forallE_inv' henv envIH hΓ (.inl rfl)
    have hu := hA.defeq.sort_r henv hΓ.defeq
    have hΓ' : CtxStrong env U (_::_) := ⟨hΓ, _, hA⟩
    have hv := hB.defeq.sort_r henv hΓ'.defeq
    exact .appDF hu hv hA hB (ih1 hΓ) (ih2 hΓ) <|
      .instDF (v := v.succ) henv hΓ hu hv hA (.sortDF hv hv rfl) hB (ih2 hΓ)
  | lamDF hA _ ih1 ih2 =>
    have hu := hA.sort_r henv hΓ.defeq
    have hΓ' : CtxStrong env U (_::_) := ⟨hΓ, _, (ih1 hΓ).hasType.1⟩
    let ⟨_, hB⟩ := (ih2 hΓ').isType' henv envIH hΓ'
    exact .lamDF hu (hB.defeq.sort_r henv hΓ'.defeq) (ih1 hΓ)
      hB ((ih1 hΓ).defeqDF_l henv hΓ hB) (ih2 hΓ') ((ih1 hΓ).defeqDF_l henv hΓ (ih2 hΓ'))
  | forallEDF hA hb ih1 ih2 =>
    have hu := hA.sort_r henv hΓ.defeq
    have hΓ' : CtxStrong env U (_::_) := ⟨hΓ, _, (ih1 hΓ).hasType.1⟩
    exact .forallEDF hu (hb.sort_r henv hΓ'.defeq)
      (ih1 hΓ) (ih2 hΓ') ((ih1 hΓ).defeqDF_l henv hΓ (ih2 hΓ'))
  | defeqDF hAB _ ih1 ih2 =>
    exact .defeqDF (hAB.sort_r henv hΓ.defeq) (ih1 hΓ) (ih2 hΓ)
  | beta _ _ ih1 ih2 =>
    have he' := ih2 hΓ
    have ⟨_, hA⟩ := he'.isType' henv envIH hΓ
    have hΓ' : CtxStrong env U (_::_) := ⟨hΓ, _, hA⟩
    have he := ih1 hΓ'
    have ⟨_, hB⟩ := he.isType' henv envIH hΓ'
    exact .beta (hA.defeq.sort_r henv hΓ.defeq) (hB.defeq.sort_r henv hΓ'.defeq)
      hA hB he he' (he'.instN henv hΓ .zero hB hΓ) (he'.instN henv hΓ .zero he hΓ)
  | eta _ ih =>
    have he := ih hΓ
    let ⟨_, hAB⟩ := he.isType' henv envIH hΓ
    let ⟨⟨u, hA⟩, ⟨v, hB⟩⟩ := hAB.forallE_inv' henv envIH hΓ (.inl rfl)
    have hΓ' : CtxStrong env U (_::_) := ⟨hΓ, _, hA⟩
    exact .eta (hA.defeq.sort_r henv hΓ.defeq) (hB.defeq.sort_r henv hΓ'.defeq)
      hA hB (hB.weakN henv (.succ .one)) he (he.weakN henv .one)
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 hΓ) (ih2 hΓ) (ih3 hΓ)
  | extra h1 h2 h3 =>
    let ⟨⟨hl, ⟨_, ht⟩, _⟩, hr, _, _⟩ := envIH.2 h1
    exact .extra h1 h2 h3 (.inst h2) (ht.instL h2)
      (hl.instL h2) (hr.instL h2) ((hl.instL h2).weak0 henv) ((hr.instL h2).weak0 henv)

theorem CtxStrong.strong' (henv : Ordered env) (envIH : env.OnTypes (EnvStrong env))
    (hΓ : OnCtx Γ (env.IsType U)) : CtxStrong env U Γ := by
  induction Γ with
  | nil => trivial
  | cons _ _ ih => let ⟨hΓ, _, hA⟩ := hΓ; exact ⟨ih hΓ, _, hA.strong' henv envIH (ih hΓ)⟩

theorem Ordered.strong (henv : Ordered env) : OnTypes env (EnvStrong env) :=
  henv.induction _
    (fun le ⟨h1, ⟨_, h2⟩, h3⟩ => ⟨h1.mono le, ⟨_, h2.mono le⟩, fun _ _ eq =>
      let ⟨⟨_, h4⟩, ⟨_, h5⟩⟩ := h3 _ _ eq; ⟨⟨_, h4.mono le⟩, ⟨_, h5.mono le⟩⟩⟩)
    (fun henv IH H =>
      have H' := H.strong' henv IH (Γ := []) ⟨⟩
      ⟨H', H'.isType' henv IH ⟨⟩, fun _ _ eq => H'.forallE_inv' henv IH ⟨⟩ (.inl eq)⟩)

theorem CtxStrong.strong (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) : CtxStrong env U Γ :=
  .strong' henv henv.strong hΓ

theorem IsDefEq.strong (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEq U Γ e1 e2 A) : env.IsDefEqStrong U Γ e1 e2 A :=
  H.strong' henv henv.strong (.strong henv hΓ)

variable (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem IsDefEq.app_inv'
    (H : env.IsDefEq U Γ e1 e2 V) (eq : e1 = .app f a ∨ e2 = .app f a) :
    ∃ A B, env.HasType U Γ f (.forallE A B) ∧ env.HasType U Γ a A := by
  have H' := H.strong henv hΓ; clear H hΓ
  induction H' with
  | symm _ ih => exact ih eq.symm
  | trans _ _ ih1 ih2
  | proofIrrel _ _ _ _ ih1 ih2
  | extra _ _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    obtain eq | eq := eq <;> [exact ih1 (.inl eq); exact ih2 (.inr eq)]
  | appDF _ _ _ _ h1 h2 =>
    obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq
    · exact ⟨_, _, h1.defeq.hasType.1, h2.defeq.hasType.1⟩
    · exact ⟨_, _, h1.defeq.hasType.2, h2.defeq.hasType.2⟩
  | defeqDF _ _ _ _ ih2 => exact ih2 eq
  | beta _ _ hA _ he he' _ _ _ _ _ _ _ ihee =>
    obtain ⟨⟨⟩⟩ | eq := eq
    · exact ⟨_, _, .lam hA.defeq he.defeq, he'.defeq⟩
    · exact ihee (.inl eq)
  | eta _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih (.inl eq)
  | _ => nomatch eq

variable (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem HasType.app_inv (H : env.HasType U Γ (.app f a) V) :
    ∃ A B, env.HasType U Γ f (.forallE A B) ∧ env.HasType U Γ a A :=
  H.app_inv' henv hΓ (.inl rfl)

variable (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem _root_.Lean4Lean.VExpr.WF.app_inv (H : VExpr.WF env U Γ (.app f a)) :
    ∃ A B, env.HasType U Γ f (.forallE A B) ∧ env.HasType U Γ a A :=
  let ⟨_, H⟩ := H; HasType.app_inv henv hΓ H

variable (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem IsDefEq.lam_inv'
    (H : env.IsDefEq U Γ e1 e2 V) (eq : e1 = .lam A body ∨ e2 = .lam A body) :
    env.IsType U Γ A ∧ body.WF env U (A::Γ) := by
  have H' := H.strong henv hΓ; clear H hΓ
  induction H' with
  | symm _ ih => exact ih eq.symm
  | trans _ _ ih1 ih2
  | proofIrrel _ _ _ _ ih1 ih2
  | extra _ _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    obtain eq | eq := eq <;> [exact ih1 (.inl eq); exact ih2 (.inr eq)]
  | lamDF _ _ h1 _ _ h4 h5 =>
    obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq
    · exact ⟨⟨_, h1.defeq.hasType.1⟩, _, h4.defeq.hasType.1⟩
    · exact ⟨⟨_, h1.defeq.hasType.2⟩, _, h5.defeq.hasType.2⟩
  | defeqDF _ _ _ _ ih2 => exact ih2 eq
  | beta _ _ _ _ _ _ _ _ _ _ _ _ _ ihee =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ihee (.inl eq)
  | eta _ _ hA _ _ _ he' _ _ _ ih =>
    obtain ⟨⟨⟩⟩ | eq := eq
    · exact ⟨⟨_, hA.defeq.hasType.1⟩, _, he'.defeq.hasType.1.app (.bvar .zero)⟩
    · exact ih (.inl eq)
  | _ => nomatch eq

variable (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem HasType.lam_inv (H : env.HasType U Γ (.lam A body) V) :
    env.IsType U Γ A ∧ body.WF env U (A::Γ) :=
  H.lam_inv' henv hΓ (.inl rfl)

variable (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem _root_.Lean4Lean.VExpr.WF.lam_inv (H : VExpr.WF env U Γ (.lam A body)) :
    env.IsType U Γ A ∧ body.WF env U (A::Γ) :=
  let ⟨_, H⟩ := H; HasType.lam_inv henv hΓ H

variable (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem IsDefEq.const_inv'
    (H : env.IsDefEq U Γ e1 e2 V) (eq : e1 = .const c ls ∨ e2 = .const c ls) :
    ∃ ci, env.constants c = some (some ci) ∧ (∀ l ∈ ls, l.WF U) ∧ ls.length = ci.uvars := by
  have H' := H.strong henv hΓ; clear H hΓ
  induction H' with
  | symm _ ih => exact ih eq.symm
  | trans _ _ ih1 ih2
  | proofIrrel _ _ _ _ ih1 ih2
  | extra _ _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    obtain eq | eq := eq <;> [exact ih1 (.inl eq); exact ih2 (.inr eq)]
  | constDF h1 h2 h3 h4 h5 _ _ =>
    obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq
    · exact ⟨_, h1, h2, h4⟩
    · exact ⟨_, h1, h3, h5.length_eq.symm.trans h4⟩
  | defeqDF _ _ _ _ ih2 => exact ih2 eq
  | beta _ _ _ _ _ _ _ _ _ _ _ _ _ ihee =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ihee (.inl eq)
  | eta _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih (.inl eq)
  | _ => nomatch eq

variable (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem HasType.const_inv (H : env.HasType U Γ (.const c ls) V) :
    ∃ ci, env.constants c = some (some ci) ∧ (∀ l ∈ ls, l.WF U) ∧ ls.length = ci.uvars :=
  H.const_inv' henv hΓ (.inl rfl)

variable (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem _root_.Lean4Lean.VExpr.WF.const_inv (H : VExpr.WF env U Γ (.const c ls)) :
    ∃ ci, env.constants c = some (some ci) ∧ (∀ l ∈ ls, l.WF U) ∧ ls.length = ci.uvars :=
  let ⟨_, H⟩ := H; HasType.const_inv henv hΓ H
