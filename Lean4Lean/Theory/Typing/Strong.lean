import Lean4Lean.Theory.Typing.Lemmas

namespace Lean4Lean
namespace VEnv

open VExpr

section
set_option hygiene false
variable (env : VEnv) (uvars : Nat)

section
local notation:65 Γ " ⊢ " e " : " A:30 => IsDefEqStrong Γ e e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:30 => IsDefEqStrong Γ e1 e2 A

inductive IsDefEqStrong : List VExpr → VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup Γ i A → u.WF uvars → Γ ⊢ A : .sort u → Γ ⊢ .bvar i : A
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
    u.WF uvars →
    [] ⊢ ci.type.instL ls ≡ ci.type.instL ls' : .sort u →
    Γ ⊢ ci.type.instL ls ≡ ci.type.instL ls' : .sort u →
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
    A::Γ ⊢ A.lift : .sort u →
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

section
local notation:65 Γ " ⊢ " e " : " A:30 => HasTypeStrong Γ e A true
local notation:65 Γ " ⊢ " e " :! " A:30 => HasTypeStrong Γ e A false
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:30 => IsDefEqStrong env uvars Γ e1 e2 A

/--
This is functionally a mutual inductive type,
but using a bool index makes it easier to do induction in lean.
The defeq rule is separated from the structural rules for easy inversion.
-/
inductive HasTypeStrong : List VExpr → VExpr → VExpr → Bool → Prop where
  | bvar : Lookup Γ i A → u.WF uvars → Γ ⊢ A : .sort u → Γ ⊢ .bvar i :! A
  | sort' : l.WF uvars → l'.WF uvars → l ≈ l' → Γ ⊢ .sort l :! .sort (.succ l')
  | const :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF uvars) →
    ls.length = ci.uvars →
    u.WF uvars →
    [] ⊢ ci.type.instL ls : .sort u →
    Γ ⊢ ci.type.instL ls : .sort u →
    Γ ⊢ .const c ls :! ci.type.instL ls
  | app :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A : .sort u →
    A::Γ ⊢ B : .sort v →
    Γ ⊢ .forallE A B : .sort (.imax u v) →
    Γ ⊢ f : .forallE A B →
    Γ ⊢ a : A →
    Γ ⊢ B.inst a : .sort v →
    Γ ⊢ .app f a :! B.inst a
  | lam :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A : .sort u →
    A::Γ ⊢ B : .sort v →
    A::Γ ⊢ body : B →
    Γ ⊢ .forallE A B : .sort (.imax u v) →
    Γ ⊢ .lam A body :! .forallE A B
  | forallE :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A : .sort u →
    A::Γ ⊢ body : .sort v →
    Γ ⊢ .forallE A body :! .sort (.imax u v)
  | base : Γ ⊢ e :! A → Γ ⊢ e : A
  | defeq : u.WF uvars → Γ ⊢ A ≡ B : .sort u →
    Γ ⊢ A : .sort u → Γ ⊢ B : .sort u → Γ ⊢ e : A → Γ ⊢ e : B
end

end

theorem IsDefEqStrong.hasType {env : VEnv}
    (H : env.IsDefEqStrong U Γ e1 e2 A) :
    env.IsDefEqStrong U Γ e1 e1 A ∧ env.IsDefEqStrong U Γ e2 e2 A :=
  ⟨H.trans H.symm, H.symm.trans H⟩

variable! (henv : Ordered env) in
theorem IsDefEqStrong.weakN (W : Ctx.LiftN n k Γ Γ') (H : env.IsDefEqStrong U Γ e1 e2 A) :
    env.IsDefEqStrong U Γ' (e1.liftN n k) (e2.liftN n k) (A.liftN n k) := by
  induction H generalizing k Γ' with
  | bvar h1 h2 _ ih3 => refine .bvar (h1.weakN W) h2 (ih3 W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 h6 h7 _ _ ih2 =>
    simp [(henv.closedC h1).instL.liftN_eq (Nat.zero_le _)] at ih2 ⊢
    exact .constDF h1 h2 h3 h4 h5 h6 h7 (ih2 W)
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
  | @eta Γ a u B v e h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    have := IsDefEqStrong.eta h1 h2 (ih1 W) (ih2 W.succ) ?_ (ih4 W) ?_ ?_
    · simp [liftN]; rwa [← lift_liftN']
    · specialize ih3 W.succ.succ
      have := liftN'_comm B n 1 (k+1) 1 (Nat.le_add_left ..)
      rw [Nat.add_comm 1] at this; rwa [← this, ← lift_liftN'] at ih3
    · have ih5 : IsDefEqStrong _ _ _ _ _ (liftN n (lift (forallE ..)) _) := ih5 W.succ
      rwa [← lift_liftN', ← lift_liftN'] at ih5
    · have ih6 := ih6 W.succ
      rwa [← lift_liftN'] at ih6
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
  | eta _ _ _ _ _ _ _ _ _ _ _ ih => exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 => exact .extra h1 h2 h3

variable! {env env' : VEnv} (henv : env ≤ env') in
theorem IsDefEqStrong.mono
    (H : env.IsDefEqStrong U Γ e1 e2 A) : env'.IsDefEqStrong U Γ e1 e2 A := by
  induction H with
  | bvar h1 h2 _ ih => exact .bvar h1 h2 ih
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 h6 _ _ ih1 ih2 =>
    exact .constDF (henv.1 h1) h2 h3 h4 h5 h6 ih1 ih2
  | appDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 => exact .appDF h1 h2 ih1 ih2 ih3 ih4 ih5
  | lamDF h1 h2  _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 => exact .lamDF h1 h2 ih1 ih2 ih3 ih4 ih5
  | forallEDF h1 h2 _ _ _ ih1 ih2 ih3 => exact .forallEDF h1 h2 ih1 ih2 ih3
  | defeqDF h1 _ _ ih1 ih2 => exact .defeqDF h1 ih1 ih2
  | beta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 => exact .beta h1 h2 ih1 ih2 ih3 ih4 ih5 ih6
  | eta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 => exact .eta h1 h2 ih1 ih2 ih3 ih4 ih5 ih6
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 h4 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact .extra (henv.2 h1) h2 h3 h4 ih1 ih2 ih3 ih4 ih5

variable! (henv : Ordered env) in
theorem IsDefEqStrong.weak0 (H : env.IsDefEqStrong U [] e1 e2 A) :
    env.IsDefEqStrong U Γ e1 e2 A := by
  have ⟨h1, h2, h3⟩ := H.defeq.closedN' henv.closed ⟨⟩
  simpa [h1.liftN_eq (Nat.zero_le _), h2.liftN_eq (Nat.zero_le _),
    h3.liftN_eq (Nat.zero_le _)] using H.weakN henv (.zero Γ rfl)

inductive EqUpToLevels (U : Nat) : VExpr → VExpr → Prop
  | bvar : EqUpToLevels U (.bvar i) (.bvar i)
  | const : (∀ l ∈ ls, l.WF U) → (∀ l ∈ ls', l.WF U) → List.Forall₂ (· ≈ ·) ls ls' →
    EqUpToLevels U (.const c ls) (.const c ls')
  | sort : l.WF U → l'.WF U → l ≈ l' → EqUpToLevels U (.sort l) (.sort l')
  | app : EqUpToLevels U f f' → EqUpToLevels U a a' → EqUpToLevels U (.app f a) (.app f' a')
  | lam : EqUpToLevels U A A' → EqUpToLevels U e e' → EqUpToLevels U (.lam A e) (.lam A' e')
  | forallE : EqUpToLevels U A A' → EqUpToLevels U B B' → EqUpToLevels U (.forallE A B) (.forallE A' B')

variable! {env : VEnv} {ls ls' : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U) (heq : List.Forall₂ (· ≈ ·) ls ls') in
theorem EqUpToLevels.instL (H : env.IsDefEqStrong U' Γ e1 e2 A) :
    EqUpToLevels U (e1.instL ls) (e1.instL ls') ∧ EqUpToLevels U (e2.instL ls) (e2.instL ls') := by
  induction H with
  | bvar => exact ⟨.bvar, .bvar⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 | proofIrrel _ _  _ _ ih1 ih2
  | extra _ _ _ _ _ _ _ _ _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2⟩
  | sortDF h1 h2 h3 =>
    constructor <;> exact .sort (.inst hls) (.inst hls') (VLevel.inst_congr rfl heq)
  | constDF h1 h2 h3 h4 h5 =>
    constructor <;> exact .const
      (List.forall_mem_map.2 fun _ _ => .inst hls)
      (List.forall_mem_map.2 fun _ _ => .inst hls')
      (List.forall₂_map_left_iff.2 <| List.forall₂_map_right_iff.2 <|
        .rfl fun _ _ => VLevel.inst_congr rfl heq)
  | appDF _ _ _ _ _ _ _ _ _ ih1 ih2 => exact ⟨.app ih1.1 ih2.1, .app ih1.2 ih2.2⟩
  | lamDF _ _ _ _ _ _ _ ih1 _ _ ih2 => exact ⟨.lam ih1.1 ih2.1, .lam ih1.2 ih2.2⟩
  | forallEDF _ _ _ _ _ ih1 ih2 => exact ⟨.forallE ih1.1 ih2.1, .forallE ih1.2 ih2.2⟩
  | defeqDF _ _ _ _ ih => exact ih
  | beta _ _ _ _ _ _ _ _ ih1 _ ih3 ih4 _ ih6 => exact ⟨.app (.lam ih1.1 ih3.1) ih4.1, ih6.2⟩
  | eta _ _ _ _ _ _ _ _ ih1 _ _ ih4 ih5 => exact ⟨.lam ih1.1 (.app ih5.1 .bvar), ih4.1⟩


variable! {env : VEnv} (W : OnCtx Γ fun _ A => A.LevelWF U) in
theorem EqUpToLevels.refl (H : env.IsDefEqStrong U Γ e1 e2 A) :
    EqUpToLevels U e1 e1 ∧ EqUpToLevels U e2 e2 := by
  have := IsDefEq.levelWF H.defeq W
  exact LevelWF.instL_id this.1 ▸ LevelWF.instL_id this.2.1 ▸
    EqUpToLevels.instL VLevel.params_wf VLevel.params_wf (.rfl fun _ _ => rfl) H

theorem EqUpToLevels.weakN (H : EqUpToLevels U e e') :
    EqUpToLevels U (e.liftN n k) (e'.liftN n k) := by
  induction H generalizing k with
  | bvar => exact .bvar
  | const h1 h2 h3 => exact .const h1 h2 h3
  | sort h1 h2 h3 => exact .sort h1 h2 h3
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2

variable! (h₀ : EqUpToLevels U e₀ e₀') in
theorem EqUpToLevels.instN (H : EqUpToLevels U e e') :
    EqUpToLevels U (e.inst e₀ k) (e'.inst e₀' k) := by
  induction H generalizing k with
  | bvar => simp [inst, instVar]; split <;> [exact .bvar; split] <;> [exact h₀.weakN; exact .bvar]
  | const h1 h2 h3 => exact .const h1 h2 h3
    | sort h1 h2 h3 => exact .sort h1 h2 h3
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2

def EnvStrong (env : VEnv) (U : Nat) (e A : VExpr) : Prop :=
  env.IsDefEqStrong U [] e e A ∧
  (∃ u, env.IsDefEqStrong U [] A A (.sort u)) ∧
  (∀ U' ls ls', (∀ l ∈ ls, l.WF U') → (∀ l ∈ ls', l.WF U') → List.Forall₂ (· ≈ ·) ls ls' →
    env.IsDefEqStrong U' [] (e.instL ls) (e.instL ls') (A.instL ls)) ∧
  ∀ A B, e = A.forallE B →
    (∃ u, env.IsDefEqStrong U [] A A (.sort u)) ∧
    (∃ u, env.IsDefEqStrong U [A] B B (.sort u))

variable! {env : VEnv} {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U') in
theorem IsDefEqStrong.instL (H : env.IsDefEqStrong U Γ e1 e2 A) :
    env.IsDefEqStrong U' (Γ.map (VExpr.instL ls)) (e1.instL ls) (e2.instL ls) (A.instL ls) := by
  induction H with
  | bvar h _ _ ih =>
    exact .bvar h.instL (.inst hls) ih
  | constDF h1 h2 h3 h4 h5 _ _ _ ih1 ih2 =>
    simp [VExpr.instL, VExpr.instL_instL] at ih1 ih2 ⊢
    exact .constDF h1
      (by simp [VLevel.WF.inst hls]) (by simp [VLevel.WF.inst hls]) (by simp [h4])
      (by simpa using h5.imp fun _ _ => VLevel.inst_congr_l) (.inst hls) ih1 ih2
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
  | eta _ _ _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    simpa [VExpr.instL] using .eta (.inst hls) (.inst hls) ih1 ih2
      (by simpa using ih3) ih4 (by simpa [VExpr.instL] using ih5) (by simpa [VExpr.instL] using ih6)
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    simp [VExpr.instL, VExpr.instL_instL] at ih1 ih2 ih3 ih4 ih5 ⊢
    exact .extra h1 (by simp [VLevel.WF.inst hls]) (by simp [h3])
      (.inst hls) ih1 ih2 ih3 ih4 ih5

def CtxStrong (env : VEnv) (U Γ) :=
  OnCtx Γ fun Γ A => ∃ u, env.IsDefEqStrong U Γ A A (.sort u)

variable! (henv : Ordered env) in
nonrec theorem CtxStrong.lookup {Γ} (H : CtxStrong env U Γ) (h : Lookup Γ i A) :
    ∃ u, env.IsDefEqStrong U Γ A A (.sort u) :=
  H.lookup h fun ⟨_, h⟩ => ⟨_, h.weakN henv .one⟩

theorem CtxStrong.defeq {Γ} (H : CtxStrong env U Γ) : OnCtx Γ (env.IsType U) :=
  H.mono fun ⟨_, h⟩ => ⟨_, h.defeq⟩

theorem CtxStrong.levelWF : ∀ {Γ}, CtxStrong env U Γ → OnCtx Γ fun _ A => A.LevelWF U
  | [], h => h
  | _::_, ⟨h1, _, h2⟩ => ⟨levelWF h1, (h2.defeq.levelWF (levelWF h1)).1⟩

variable! (henv : Ordered env) (h₀ : env.IsDefEqStrong U Γ₀ e₀ e₀ A₀) (hΓ₀ : CtxStrong env U Γ₀) in
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
  | constDF h1 h2 h3 h4 h5 h6 h7 _ _ ih2 =>
    simp [(henv.closedC h1).instL.instN_eq (Nat.zero_le _)] at ih2 ⊢
    exact .constDF h1 h2 h3 h4 h5 h6 h7 (ih2 W hΓ)
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
  | eta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
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
        (by simpa [inst, ← lift_instN_lo] using ih6 W.succ hΓ')
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

variable! (henv : Ordered env) (envIH : env.OnTypes (EnvStrong env)) in
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
  | eta _ _ _ _ _ _ _ _ _ _ _ ih =>
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
    let ⟨⟨_, A1⟩, v, A2⟩ := IH.2.2.2 _ _ rfl
    refine ⟨⟨_, (A1.instL h2).weak0 henv⟩, v.inst ls, ?_⟩
    have := (A2.instL h2).weakN henv (.succ (.zero Γ))
    have C1 := (A1.instL h2).defeq.closedN henv ⟨⟩
    have C2 := (A2.instL h2).defeq.closedN henv ⟨⟨⟩, C1⟩
    rw [C1.liftN_eq (Nat.zero_le _), C2.liftN_eq (by exact Nat.le_refl _)] at this
    simpa [liftN]
  | _ => nomatch eq

variable! (henv : Ordered env) (envIH : env.OnTypes (EnvStrong env)) in
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
  | eta _ _ _ _ _ _ _ _ _ _ _ ih => exact ih hΓ
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

variable! (henv : Ordered env) (envIH : env.OnTypes (EnvStrong env))
  (W : CtxStrong env U Γ) in
theorem EqUpToLevels.defeq (H : env.IsDefEqStrong U Γ e1 e2 A)
    (H1 : EqUpToLevels U e1 e1') (H2 : EqUpToLevels U e2 e2') :
    env.IsDefEqStrong U Γ e1' e2' A := by
  induction H generalizing e1' e2' with
  | bvar h1 h2 h3 => let .bvar := H1; let .bvar := H2; exact .bvar h1 h2 h3
  | constDF h1 h2 h3 h4 h5 h6 _ _ ih1 ih2 =>
    let .const a1 a2 a3 := H1
    let .const b1 b2 b3 := H2
    let ⟨_, c1⟩ := envIH.1 h1
    have c2 := a3.flip.trans (T := (· ≈ ·)) (fun _ _ _  => (·.symm.trans)) <|
      h5.trans (T := (· ≈ ·)) (fun _ _ _ => Eq.trans) b3
    have := c1.2.2.1 _ _ _ a2 b2 c2
    exact .defeqDF (.inst a1) (.symm ((c1.2.2.1 _ _ _ a1 a2 a3).weak0 henv)) <|
      .constDF h1 a2 b2 (a3.length_eq.symm.trans h4) c2 (.inst a2) this (this.weak0 henv)
  | symm _ ih => exact (ih W H2 H1).symm
  | trans h1 _ ih1 ih2 =>
    have H3 := (EqUpToLevels.refl W.levelWF h1).2; exact (ih1 W H1 H3).trans (ih2 W H3 H2)
  | sortDF h1 h2 h3 =>
    let .sort a1 a2 a3 := H1
    let .sort b1 b2 b3 := H2
    exact .defeqDF (by exact a1)
      (.symm <| .sortDF (by exact a1) (by exact a2) (VLevel.succ_congr a3))
      (.sortDF a2 b2 (a3.symm.trans <| h3.trans b3))
  | appDF h1 h2 h3 h4 h5 h6 _ ih1 ih2 ih3 ih4 ih5 =>
    let .app a1 a2 := H1
    let .app b1 b2 := H2
    have := ih4 W a2 (EqUpToLevels.refl W.levelWF h6).2 |>.trans h6.symm
    exact .defeqDF h2 (.instDF henv W h1 (by exact h2) h3 (.sortDF h2 h2 rfl) h4 this) <|
      .appDF h1 h2 h3 h4 (ih3 W a1 b1) (ih4 W a2 b2) <|
      .instDF henv W h1 (by exact h2) h3 (.sortDF h2 h2 rfl) h4 (ih4 W a2 b2)
  | lamDF h1 h2 h3 h4 h5 h6 h7 ih1 ih2 ih3 ih4 =>
    let .lam a1 a2 := H1
    let .lam b1 b2 := H2
    have c1 := ih1 W a1 (EqUpToLevels.refl W.levelWF h3).2 |>.trans h3.symm
    have c2 := ih1 W (EqUpToLevels.refl W.levelWF h3).1 b1
    have h4' := c1.symm.defeqDF_l henv W h4
    exact have ih := ih4 ⟨W, _, h3.hasType.1⟩ a2 b2
      .defeqDF (by exact ⟨h1, h2⟩) (.forallEDF h1 h2 c1 h4' h4) <|
      .lamDF h1 h2 (ih1 W a1 b1) h4' (.defeqDF_l henv W c2 h4)
        (.defeqDF_l henv W c1.symm ih) (.defeqDF_l henv W c2 ih)
  | forallEDF h1 h2 h3 _ _ ih1 ih2 =>
    let .forallE a1 a2 := H1
    let .forallE b1 b2 := H2
    have c1 := ih1 W a1 (EqUpToLevels.refl W.levelWF h3).2 |>.trans h3.symm
    have c2 := ih1 W (EqUpToLevels.refl W.levelWF h3).1 b1
    exact .forallEDF h1 h2 (ih1 W a1 b1)
      (.defeqDF_l henv W c1.symm <| ih2 ⟨W, _, h3.hasType.1⟩ a2 b2)
      (.defeqDF_l henv W c2 <| ih2 ⟨W, _, h3.hasType.1⟩ a2 b2)
  | defeqDF h1 h2 _ _ ih => exact .defeqDF h1 h2 (ih W H1 H2)
  | beta h1 h2 h3 h4 h5 h6 h7 _ ih1 _ ih3 ih4 ih5 ih6 =>
    let .app a1 a3 := H1; let .lam a1 a2 := a1
    have c1 := ih1 W a1 (EqUpToLevels.refl W.levelWF h3).2 |>.trans h3.symm
    have c2 := ih4 W a3 (EqUpToLevels.refl W.levelWF h6).2 |>.trans h6.symm
    have c3 := ih3 ⟨W, _, h3⟩ a2 a2
    have hb := (EqUpToLevels.refl (CtxStrong.levelWF (by exact ⟨W, _, h3⟩)) h4).2
    have c4 := ih5 W (.instN a3 hb) (EqUpToLevels.refl W.levelWF h7).2
    refine .trans ?_ (ih6 W (.instN a3 a2) H2)
    refine .defeqDF h2 (.instDF henv W h1 (by exact h2) h3 (.sortDF h2 h2 rfl) h4 c2) ?_
    exact .beta h1 h2 c1.hasType.1 (.defeqDF_l henv W c1.symm h4)
      (.defeqDF_l henv W c1.symm c3) (.defeqDF h1 c1.symm c2.hasType.1)
      c4.hasType.1 (.instN henv c2.hasType.1 W .zero c3 W)
  | eta h1 h2 h3 h4 h5 h6 h7 h8 ih1 ih2 ih3 ih4 ih5 =>
    let .lam a1 a3 := H1; let .app a2 a3 := a3; let .bvar := a3
    have c1 := ih1 W a1 (EqUpToLevels.refl W.levelWF h3).2 |>.trans h3.symm
    have c2 := have W' := ⟨W, _, h3⟩; ih5 W' a2 (EqUpToLevels.refl W'.levelWF h7).2
    have c3 := IsDefEqStrong.appDF h1 h2 h8 h5 c2 (.bvar .zero h1 h8)
    rw [instN_bvar0] at c3; specialize c3 h4
    refine .trans
      (.symm <| .lamDF h1 h2 c1.symm h4 (.defeqDF_l henv W c1.symm h4) c3.symm
        (.defeqDF_l henv W c1.symm c3.symm)) ?_
    exact .trans (.eta h1 h2 h3 h4 h5 h6 h7 h8) (ih4 W (EqUpToLevels.refl W.levelWF h6).1 H2)
  | proofIrrel h1 _ _ _ ih1 ih2 => exact .proofIrrel h1 (ih1 W H1 H1) (ih2 W H2 H2)
  | extra h1 h2 h3 h4 h5 h6 h7 h8 h9 _ ih1 ih2 =>
    have c1 := ih1 trivial H1 (EqUpToLevels.refl (by trivial) h6).2
    have c2 := ih2 trivial H2 (EqUpToLevels.refl (by trivial) h7).2
    refine .weak0 henv <| c1.trans <| .trans ?_ c2.symm
    exact .extra h1 h2 h3 h4 h5 h6 h7 h6 h7

variable! (henv : Ordered env) (envIH : env.OnTypes (EnvStrong env)) in
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
    have := h6.2.2.1 _ _ _ h2 h3 h5
    exact .constDF h1 h2 h3 h4 h5 (.inst h2) this (this.weak0 henv)
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
      hA hB (hB.weakN henv (.succ .one)) he (he.weakN henv .one) (hA.weakN henv .one)
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

theorem Ordered.strong (henv : Ordered env) : OnTypes env (EnvStrong env) := by
  refine henv.induction _ (fun le ⟨h1, ⟨_, h2⟩, h3, h4⟩ => ?_) (fun henv IH H => ?_)
  · refine ⟨h1.mono le, ⟨_, h2.mono le⟩, ?_, ?_⟩
    · exact fun _ _ _ h4 h5 h6 => (h3 _ _ _ h4 h5 h6).mono le
    · exact fun _ _ eq => let ⟨⟨_, h4⟩, ⟨_, h5⟩⟩ := h4 _ _ eq; ⟨⟨_, h4.mono le⟩, ⟨_, h5.mono le⟩⟩
  · have H' := H.strong' henv IH (Γ := []) ⟨⟩
    refine ⟨H', H'.isType' henv IH ⟨⟩, fun _ _ _ h1 h2 h3 => ?_, ?_⟩
    · exact EqUpToLevels.defeq henv IH (by trivial) (.instL h1 H')
        (EqUpToLevels.refl (by trivial) (.instL h1 H')).1 (EqUpToLevels.instL h1 h2 h3 H').1
    · exact fun _ _ eq => H'.forallE_inv' henv IH ⟨⟩ (.inl eq)

theorem CtxStrong.strong (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) : CtxStrong env U Γ :=
  .strong' henv henv.strong hΓ

theorem IsDefEq.strong (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEq U Γ e1 e2 A) : env.IsDefEqStrong U Γ e1 e2 A :=
  H.strong' henv henv.strong (.strong henv hΓ)

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
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
  | eta _ _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih (.inl eq)
  | _ => nomatch eq

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem HasType.app_inv (H : env.HasType U Γ (.app f a) V) :
    ∃ A B, env.HasType U Γ f (.forallE A B) ∧ env.HasType U Γ a A :=
  H.app_inv' henv hΓ (.inl rfl)

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem _root_.Lean4Lean.VExpr.WF.app_inv (H : VExpr.WF env U Γ (.app f a)) :
    ∃ A B, env.HasType U Γ f (.forallE A B) ∧ env.HasType U Γ a A :=
  let ⟨_, H⟩ := H; HasType.app_inv henv hΓ H

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
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
  | eta _ _ hA _ _ _ he' _ _ _ _ ih =>
    obtain ⟨⟨⟩⟩ | eq := eq
    · exact ⟨⟨_, hA.defeq.hasType.1⟩, _, he'.defeq.hasType.1.app (.bvar .zero)⟩
    · exact ih (.inl eq)
  | _ => nomatch eq

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem HasType.lam_inv (H : env.HasType U Γ (.lam A body) V) :
    env.IsType U Γ A ∧ body.WF env U (A::Γ) :=
  H.lam_inv' henv hΓ (.inl rfl)

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem _root_.Lean4Lean.VExpr.WF.lam_inv (H : VExpr.WF env U Γ (.lam A body)) :
    env.IsType U Γ A ∧ body.WF env U (A::Γ) :=
  let ⟨_, H⟩ := H; HasType.lam_inv henv hΓ H

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem IsDefEq.const_inv'
    (H : env.IsDefEq U Γ e1 e2 V) (eq : e1 = .const c ls ∨ e2 = .const c ls) :
    ∃ ci, env.constants c = some ci ∧ (∀ l ∈ ls, l.WF U) ∧ ls.length = ci.uvars := by
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
  | eta _ _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih (.inl eq)
  | _ => nomatch eq

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem HasType.const_inv (H : env.HasType U Γ (.const c ls) V) :
    ∃ ci, env.constants c = some ci ∧ (∀ l ∈ ls, l.WF U) ∧ ls.length = ci.uvars :=
  H.const_inv' henv hΓ (.inl rfl)

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem _root_.Lean4Lean.VExpr.WF.const_inv (H : VExpr.WF env U Γ (.const c ls)) :
    ∃ ci, env.constants c = some ci ∧ (∀ l ∈ ls, l.WF U) ∧ ls.length = ci.uvars :=
  let ⟨_, H⟩ := H; HasType.const_inv henv hΓ H

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem IsDefEq.eqUpToLevels (H : env.IsDefEq U Γ e1 e2 A)
    (H1 : EqUpToLevels U e2 e2') : env.IsDefEq U Γ e1 e2' A :=
  have W := .strong' henv henv.strong hΓ
  have := H.strong henv hΓ
  (EqUpToLevels.defeq henv henv.strong W (H.strong henv hΓ)
    (EqUpToLevels.refl W.levelWF this).1 H1).defeq

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U')) {ls ls' : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U) (hls' : ∀ l ∈ ls', l.WF U) (heq : List.Forall₂ (· ≈ ·) ls ls') in
theorem IsDefEq.instL_r (H : env.IsDefEq U' Γ e1 e2 A) :
    env.IsDefEq U (Γ.map (VExpr.instL ls)) (e1.instL ls) (e2.instL ls') (A.instL ls) :=
  have := H.strong henv hΓ
  IsDefEq.eqUpToLevels henv (hΓ.instL hls) (this.instL hls).defeq
    (EqUpToLevels.instL hls hls' heq this).2

theorem IsDefEqStrong.hasType' {env : VEnv}
    (H : env.IsDefEqStrong U Γ e1 e2 A) :
    env.HasTypeStrong U Γ e1 A true ∧ env.HasTypeStrong U Γ e2 A true := by
  induction H with
  | bvar h1 h2 _ ih3 => refine and_self_iff.2 <| .base <| .bvar h1 h2 ih3.1
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 | proofIrrel _ _ _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2⟩
  | sortDF h1 h2 h3 => exact ⟨.base <| .sort' h1 h1 rfl, .base <| .sort' h2 h1 h3.symm⟩
  | constDF h1 h2 h3 h4 h5 h6 h7 h8 ih1 ih2 =>
    exact ⟨.base <| .const h1 h2 h4 h6 ih1.1 ih2.1,
      .defeq h6 h8.symm ih2.2 ih2.1 <| .base <|
      .const h1 h3 (h5.length_eq.symm.trans h4) h6 ih1.2 ih2.2⟩
  | appDF h1 h2 h3 h4 h5 h6 h7 ih1 ih2 ih3 ih4 ih5 =>
    have := HasTypeStrong.base <| .forallE h1 h2 ih1.1 ih2.1
    exact ⟨.base <| .app h1 h2 ih1.1 ih2.1 this ih3.1 ih4.1 ih5.1,
      .defeq h2 h7.symm ih5.2 ih5.1 <| .base <| .app h1 h2 ih1.2 ih2.2 this ih3.2 ih4.2 ih5.2⟩
  | lamDF h1 h2 h3 h4 h5 h6 h7 ih1 ih2 ih3 ih4 ih5 =>
    refine ⟨.base <| .lam h1 h2 ih1.1 ih2.1 ih4.1 ?a,
      .defeq (by exact ⟨h1, h2⟩) (.symm <| .forallEDF h1 h2 h3 h4 h5) ?b ?a ?_⟩
    · exact .base <| .forallE h1 h2 ih1.1 ih2.1
    · exact .base <| .forallE h1 h2 ih1.2 ih3.1
    · exact .base <| .lam h1 h2 ih1.2 ih3.1 ih5.2 ?b
  | forallEDF h1 h2 h3 h4 h5 ih1 ih2 ih3 =>
    exact ⟨.base <| .forallE h1 h2 ih1.1 ih2.1, .base <| .forallE h1 h2 ih1.2 ih3.2⟩
  | defeqDF h1 h2 h3 ih1 ih2 =>
    exact ⟨.defeq h1 h2 ih1.1 ih1.2 ih2.1, .defeq h1 h2 ih1.1 ih1.2 ih2.2⟩
  | beta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    have := HasTypeStrong.base <| .forallE h1 h2 ih1.1 ih2.1
    refine ⟨.base <| .app h1 h2 ih1.1 ih2.1 this ?_ ih4.1 ih5.1, ih6.1⟩
    refine .base <| .lam h1 h2 ih1.1 ih2.1 ih3.1 ?_
    exact .base <| .forallE h1 h2 ih1.1 ih2.1
  | @eta Γ A u B v e h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    refine have a1 := .base <| .forallE h1 h2 ih6.1 ih3.1
      have := ih6.1.app h1 h2 ih3.1 a1 ih5.1 (.base <| .bvar .zero h1 ih6.1); ?_
    rw [instN_bvar0] at this; specialize this ih2.1
    refine ⟨.base <| .lam h1 h2 ih1.1 ih2.1 (.base this) ?_, ih4.1⟩
    exact .base <| .forallE h1 h2 ih1.1 ih2.1
  | extra h1 h2 h3 h4 h5 h6 h7 _ _ _ _ _ ih4 ih5 => exact ⟨ih4.1, ih5.1⟩

theorem HasTypeStrong.refl {env : VEnv}
    (H : env.HasTypeStrong U Γ e A b) : env.IsDefEqStrong U Γ e e A := by
  induction H with
  | bvar h1 h2 _ ih1 => refine .bvar h1 h2 ih1
  | sort' h1 h2 h3 =>
    refine .defeqDF ?_ (.sortDF ?_ ?_ (VLevel.succ_congr h3)) (.sortDF h1 h1 rfl) <;> assumption
  | const h1 h2 h3 h4 h5 h6 ih1 ih2 =>
    exact .constDF h1 h2 h2 h3 (.rfl fun _ _ => rfl) h4 ih1 ih2
  | app h1 h2 h3 h4 _ h5 h6 h7 ih1 ih2 _ ih3 ih4 ih5 =>
    exact .appDF h1 h2 ih1 ih2 ih3 ih4 ih5
  | lam h1 h2 h3 h4 h5 _ ih1 ih2 ih3 =>
    exact .lamDF h1 h2 ih1 ih2 ih2 ih3 ih3
  | forallE h1 h2 h3 h4 ih1 ih2 =>
    exact .forallEDF h1 h2 ih1 ih2 ih2
  | base _ ih => exact ih
  | defeq h1 h2 h3 h4 h5 ih1 ih2 ih3 => exact .defeqDF h1 h2 ih3

theorem HasTypeStrong.hasType {env : VEnv}
    (H : env.HasTypeStrong U Γ e A b) :  env.HasType U Γ e A := H.refl.defeq.hasType.1

set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env U Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEq env U Γ e1 e2 A
section
local notation:65 Γ " ⊢ " e " : " A " !! " n:30 => HasTypeStratified Γ e A true n
local notation:65 Γ " ⊢ " e " :! " A " !! " n:30 => HasTypeStratified Γ e A false n

variable (env : VEnv) (U : Nat) in
inductive HasTypeStratified : List VExpr → VExpr → VExpr → Bool → Nat → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ A : .sort u !! n → Γ ⊢ .bvar i :! A !! n+1
  | sort' : l.WF U → l'.WF U → l ≈ l' → Γ ⊢ .sort l :! .sort (.succ l') !! n
  | const :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF U) →
    ls.length = ci.uvars →
    Γ ⊢ ci.type.instL ls : .sort u !! n →
    Γ ⊢ .const c ls :! ci.type.instL ls !! n+1
  | app :
    u.WF U → v.WF U →
    Γ ⊢ A : .sort u !! n →
    A::Γ ⊢ B : .sort v !! n →
    Γ ⊢ f : .forallE A B !! n →
    Γ ⊢ a : A !! n →
    Γ ⊢ B.inst a : .sort v !! n →
    Γ ⊢ .app f a :! B.inst a !! n+1
  | lam :
    Γ ⊢ A : .sort u !! n →
    A::Γ ⊢ B : .sort v !! n →
    A::Γ ⊢ body : B !! n →
    Γ ⊢ .forallE A B : .sort (.imax u v) !! n →
    Γ ⊢ .lam A body :! .forallE A B !! n+1
  | forallE :
    u.WF U → v.WF U →
    Γ ⊢ A : .sort u !! n →
    A::Γ ⊢ body : .sort v !! n →
    Γ ⊢ .forallE A body :! .sort (.imax u v) !! n+1
  | base : Γ ⊢ e :! A !! n → Γ ⊢ e : A !! n
  | defeq : u.WF U → Γ ⊢ A ≡ B : .sort u →
    Γ ⊢ A : .sort u !! n → Γ ⊢ B : .sort u !! n → Γ ⊢ e : A !! n → Γ ⊢ e : B !! n+1
end

theorem HasTypeStratified.hasType (H : env.HasTypeStratified U Γ e A b n) : Γ ⊢ e : A := by
  induction H with
  | bvar h1 h2 ih1 => refine .bvar h1
  | sort' h1 h2 h3 =>
    exact IsDefEq.defeq (.sortDF (by exact h1) h2 (VLevel.succ_congr h3)) (.sort h1)
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app _ _ _ _ _ _ _ _ _ ih3 ih4 => exact .app ih3 ih4
  | lam _ _ _ _ ih1 _ ih3 => exact .lam ih1 ih3
  | forallE _ _ _ _ ih1 ih2 => exact .forallE ih1 ih2
  | base _ ih => exact ih
  | defeq _ h2 _ _ _ _ _ ih3 => exact h2.defeq ih3

theorem HasTypeStratified.mono (le : m ≤ n) (H : HasTypeStratified env U Γ e A b m) :
    env.HasTypeStratified U Γ e A b n := by
  induction H generalizing n with try let n+1 := n; replace le := Nat.le_of_succ_le_succ le
  | bvar h1 h2 ih1 => exact .bvar h1 (ih1 le)
  | sort' h1 h2 h3 => exact .sort' h1 h2 h3
  | const h1 h2 h3 _ ih1 => exact .const h1 h2 h3 (ih1 le)
  | app h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact .app h1 h2 (ih1 le) (ih2 le) (ih3 le) (ih4 le) (ih5 le)
  | lam _ _ _ _ ih1 ih2 ih3 ih4 => exact .lam (ih1 le) (ih2 le) (ih3 le) (ih4 le)
  | forallE h1 h2 _ _ ih1 ih2 => exact .forallE h1 h2 (ih1 le) (ih2 le)
  | base _ ih => exact .base (ih le)
  | defeq h1 h2 _ _ _ ih1 ih2 ih3 => exact .defeq h1 h2 (ih1 le) (ih2 le) (ih3 le)

theorem HasTypeStrong.stratify (H : HasTypeStrong env U Γ e A b) :
    ∃ n, HasTypeStratified env U Γ e A b n := by
  generalize true = b at H ⊢
  induction H with
  | bvar h1 h2 _ ih1 => let ⟨n, ih1⟩ := ih1; exact ⟨_, .bvar h1 ih1⟩
  | sort' h1 h2 h3 => exact ⟨0, .sort' h1 h2 h3⟩
  | const h1 h2 h3 _ _ _ _ ih1 => let ⟨_, ih1⟩ := ih1; exact ⟨_, .const h1 h2 h3 ih1⟩
  | app h1 h2 _ _ _ _ _ _ ih1 ih2 _ ih3 ih4 ih5 =>
    let ⟨n₁, ih1⟩ := ih1; let ⟨n₂, ih2⟩ := ih2; let ⟨n₃, ih3⟩ := ih3
    let ⟨n₄, ih4⟩ := ih4; let ⟨n₅, ih5⟩ := ih5
    refine ⟨max n₁ (max n₂ (max n₃ (max n₄ n₅))) + 1,
      .app h1 h2 (ih1.mono ?_) (ih2.mono ?_) (ih3.mono ?_) (ih4.mono ?_) (ih5.mono ?_)⟩ <;> omega
  | lam _ _ _ _ _ _ ih1 ih2 ih3 ih4 =>
    let ⟨n₁, ih1⟩ := ih1; let ⟨n₂, ih2⟩ := ih2; let ⟨n₃, ih3⟩ := ih3; let ⟨n₄, ih4⟩ := ih4
    refine ⟨max n₁ (max n₂ (max n₃ n₄)) + 1,
      .lam (ih1.mono ?_) (ih2.mono ?_) (ih3.mono ?_) (ih4.mono ?_)⟩ <;> omega
  | forallE h1 h2 _ _ ih1 ih2 =>
    let ⟨n₁, ih1⟩ := ih1; let ⟨n₂, ih2⟩ := ih2
    refine ⟨max n₁ n₂ + 1, .forallE h1 h2 (ih1.mono ?_) (ih2.mono ?_)⟩ <;> omega
  | base _ ih => let ⟨_, ih⟩ := ih; exact ⟨_, .base ih⟩
  | defeq h1 h2 _ _ _ ih1 ih2 ih3 =>
    let ⟨n₁, ih1⟩ := ih1; let ⟨n₂, ih2⟩ := ih2; let ⟨n₃, ih3⟩ := ih3
    refine ⟨max n₁ (max n₂ n₃) + 1,
      .defeq h1 h2.defeq (ih1.mono ?_) (ih2.mono ?_) (ih3.mono ?_)⟩ <;> omega
