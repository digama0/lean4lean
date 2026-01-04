import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Strong

namespace Lean4Lean
namespace VEnv

open VExpr

def DefInv (env : VEnv) (U : Nat) (Γ : List VExpr) : VExpr → VExpr → Prop
  | .forallE A B, .forallE A' B' =>
    ∃ u v, env.IsDefEq U Γ A A' (.sort u) ∧ env.IsDefEq U (A::Γ) B B' (.sort v)
  | .forallE .., .sort .. | .sort .., .forallE .. => False
  | .sort u, .sort v => u ≈ v
  | _, _ => True

variable! (henv : Ordered env) in
nonrec theorem DefInv.symm (h : DefInv env U Γ e1 e2) : DefInv env U Γ e2 e1 := by
  cases e1 <;> cases e2 <;> try trivial
  · exact h.symm
  · let ⟨u, v, h1, h2⟩ := h; exact ⟨u, v, h1.symm, h1.defeqDF_l henv h2.symm⟩

section
set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:30 => HasType1 Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:30 => IsDefEq1 Γ e1 e2 A

variable (env : VEnv) (uvars : Nat)

variable (IsDefEq1 : List VExpr → VExpr → VExpr → VExpr → Prop) in
inductive HasType1 : List VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ .bvar i : A
  | const :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF uvars) →
    ls.length = ci.uvars →
    Γ ⊢ .const c ls : ci.type.instL ls
  | sort : l.WF uvars → Γ ⊢ .sort l : .sort (.succ l)
  | app : Γ ⊢ f : .forallE A B → Γ ⊢ a : A → Γ ⊢ .app f a : B.inst a
  | lam : Γ ⊢ A : .sort u → A::Γ ⊢ body : B → Γ ⊢ .lam A body : .forallE A B
  | forallE : Γ ⊢ A : .sort u → A::Γ ⊢ body : .sort v → Γ ⊢ .forallE A body : .sort (.imax u v)
  | defeq : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e : A → Γ ⊢ e : B

variable
  (HasType1 : List VExpr → VExpr → VExpr → Prop)
  (defEq : List VExpr → VExpr → VExpr → VExpr → Prop) in
inductive IsDefEq1 : List VExpr → VExpr → VExpr → VExpr → Prop where
  | refl : Γ ⊢ e : A → Γ ⊢ e ≡ e : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  | constDF :
    env.constants c = some ci →
    (∀ l ∈ ls, l.WF uvars) →
    (∀ l ∈ ls', l.WF uvars) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    Γ ⊢ .const c ls ≡ .const c ls' : ci.type.instL ls
  | sortDF : l.WF uvars → l'.WF uvars → l ≈ l' → Γ ⊢ .sort l ≡ .sort l' : .sort l.succ
  | appDF :
    Γ ⊢ f ≡ f' : .forallE A B → Γ ⊢ a ≡ a' : A → Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | lamDF : Γ ⊢ A ≡ A' : .sort u → A::Γ ⊢ b ≡ b' : B → Γ ⊢ .lam A b ≡ .lam A' b' : .forallE A B
  | forallEDF :
    Γ ⊢ A ≡ A' : .sort u → A::Γ ⊢ B ≡ B' : .sort v →
    Γ ⊢ .forallE A B ≡ .forallE A' B' : .sort (.imax u v)
  | defeqDF : defEq Γ A B (.sort u) → Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₁ ≡ e₂ : B
  | beta : A::Γ ⊢ e : B → Γ ⊢ e' : A → Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta : Γ ⊢ e : .forallE A B → Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ h' : p
  | extra :
    env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
    Γ ⊢ df.lhs.instL ls ≡ df.rhs.instL ls : df.type.instL ls

end

variable! (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) in
theorem IsDefEq.induction1
    (defEq : List VExpr → VExpr → VExpr → VExpr → Prop)
    (hasType : List VExpr → VExpr → VExpr → Prop)
    (hty : ∀ {Γ e A}, HasType1 env U defEq Γ e A → hasType Γ e A)
    (hdf : ∀ {Γ e1 e2 A}, IsDefEq1 env U hasType defEq Γ e1 e2 A → defEq Γ e1 e2 A)
    (H : env.IsDefEq U Γ e1 e2 A) :
    HasType1 env U defEq Γ e1 A ∧
    HasType1 env U defEq Γ e2 A ∧
    IsDefEq1 env U hasType defEq Γ e1 e2 A := by
  have H' := H.strong henv hΓ; clear hΓ H
  induction H' with
  | bvar h => exact ⟨.bvar h, .bvar h, .refl (hty (.bvar h))⟩
  | symm _ ih => exact ⟨ih.2.1, ih.1, .symm ih.2.2⟩
  | trans _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2.1, .trans ih1.2.2 ih2.2.2⟩
  | @constDF _ _ ls₁ ls₂ u _ h1 h2 h3 h4 h5 =>
    exact ⟨.const h1 h2 h4,
      .defeq (u := u.inst ls₁) sorry <| .const h1 h3 (h5.length_eq.symm.trans h4),
      .constDF h1 h2 h3 h4 h5⟩
  | @sortDF l l' _ h1 h2 h3 =>
    refine ⟨.sort h1, ?_, .sortDF h1 h2 h3⟩
    exact .defeq (hdf <| .symm <| .sortDF (l' := l'.succ) h1 h2 (VLevel.succ_congr h3)) (.sort h2)
  | appDF _ _ _ _ _ _ _ _ _ ihf iha ihBa =>
    let ⟨hf, hf', ff⟩ := ihf; let ⟨ha, ha', aa⟩ := iha
    exact ⟨.app hf ha, .defeq (hdf ihBa.2.2.symm) (.app hf' ha'), .appDF ff aa⟩
  | lamDF _ _ _ _ _ _ _ ihA ihB _ ihb ihb' =>
    refine ⟨.lam ihA.1 ihb.1, ?_, .lamDF ihA.2.2 ihb.2.2⟩
    exact .defeq (hdf <| .symm <| .forallEDF ihA.2.2 ihB.2.2) <| .lam ihA.2.1 ihb'.2.1
  | forallEDF _ _ _ _ _ ih1 ih2 ih3 =>
    exact ⟨.forallE ih1.1 ih2.1, .forallE ih1.2.1 ih3.2.1, .forallEDF ih1.2.2 ih2.2.2⟩
  | defeqDF _ _ _ ih1 ih2 =>
    exact ⟨.defeq (hdf ih1.2.2) ih2.1, .defeq (hdf ih1.2.2) ih2.2.1, .defeqDF (hdf ih1.2.2) ih2.2.2⟩
  | beta _ _ _ _ _ _ _ _ ihA _ ihe ihe' _ ihee =>
    exact ⟨.app (.lam ihA.1 ihe.1) ihe'.1, ihee.1, .beta (hty ihe.1) (hty ihe'.1)⟩
  | eta _ _ _ _ _ _ _ ihA _ _ ihe ihe' =>
    have := HasType1.app ihe'.1 (.bvar .zero)
    rw [instN_bvar0] at this
    exact ⟨.lam ihA.1 this, ihe.1, .eta (hty ihe.1)⟩
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    exact ⟨ih2.1, ih3.1, .proofIrrel (hty ih1.1) (hty ih2.1) (hty ih3.1)⟩
  | extra h1 h2 h3 _ _ _ _ _ _ _ _ _ ihl' ihr' =>
    exact ⟨ihl'.1, ihr'.1, .extra h1 h2 h3⟩

variable! {env : VEnv}
  {defEq : List VExpr → VExpr → VExpr → VExpr → Prop}
  (IH : ∀ {Γ e1 e2 A}, defEq Γ e1 e2 A → env.IsDefEq U Γ e1 e2 A) in
theorem HasType1.induction (H : env.HasType1 U defEq Γ e A) : env.HasType U Γ e A := by
  induction H with
  | bvar h => exact .bvar h
  | const h1 h2 h3 => exact .const h1 h2 h3
  | sort h => exact .sort h
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | defeq h1 _ ih => exact (IH h1).defeq ih

variable! {env : VEnv}
  {hasType : List VExpr → VExpr → VExpr → Prop}
  {defEq : List VExpr → VExpr → VExpr → VExpr → Prop}
  (hty : ∀ {Γ e A}, hasType Γ e A → env.HasType U Γ e A)
  (hdf : ∀ {Γ e1 e2 A}, defEq Γ e1 e2 A → env.IsDefEq U Γ e1 e2 A) in
theorem IsDefEq1.induction
    (H : env.IsDefEq1 U hasType defEq Γ e1 e2 A) : env.IsDefEq U Γ e1 e2 A := by
  induction H with
  | refl h => exact hty h
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | appDF _ _ ih1 ih2 => exact .appDF ih1 ih2
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF h1 _ ih => exact .defeqDF (hdf h1) ih
  | beta h1 h2 => exact .beta (hty h1) (hty h2)
  | eta h => exact .eta (hty h)
  | proofIrrel h1 h2 h3 => exact .proofIrrel (hty h1) (hty h2) (hty h3)
  | extra h1 h2 h3 => exact .extra h1 h2 h3

/-
variable!
  {U : Nat}
  (hasType : List VExpr → VExpr → VExpr → Prop)
  (hasType' : List VExpr → VExpr → VExpr → Prop)
  (defEq : List VExpr → VExpr → VExpr → VExpr → Prop)
  (refl : ∀ {Γ e A}, hasType Γ e A → hasType' Γ e A)
  (sort : ∀ {Γ l l'}, l.WF U → l'.WF U → l ≈ l' →
    hasType' Γ (.sort l') (.sort l.succ))
  (app : ∀ {Γ f a A B},
    hasType' Γ f (.forallE A B) → hasType' Γ a A → hasType' Γ (.app f a) (B.inst a))
in
protected theorem IsDefEq1.hasType_ind
    (H : IsDefEq1 env U hasType defEq Γ e1 e2 A) :
    hasType' Γ e1 A ∧ hasType' Γ e2 A := by
  induction H with
  | refl h => exact ⟨refl h, refl h⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2⟩
  | sortDF h1 h2 h3 => exact ⟨sort h1 h1 rfl, sort h1 h2 h3⟩
  | appDF _ _ ih1 ih2 =>
    exact ⟨app ih1.1 ih2.1, app _ _⟩
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF h1 _ ih => exact .defeqDF (hdf h1) ih
  | beta h1 h2 => exact .beta (hty h1) (hty h2)
  | eta h => exact .eta (hty h)
  | proofIrrel h1 h2 h3 => exact .proofIrrel (hty h1) (hty h2) (hty h3)
  | extra h1 h2 h3 => exact .extra h1 h2 h3

variable!
  (hasType : List VExpr → VExpr → VExpr → Prop)
  (defEq : List VExpr → VExpr → VExpr → VExpr → Prop) in
inductive IsDefEqU1 : List VExpr → VExpr → VExpr → VLevel → Prop
  | refl : hasType Γ A (.sort u) → IsDefEqU1 Γ A A u

variable! (henv : Ordered env)
  {hasType : List VExpr → VExpr → VExpr → Prop}
  {defEq : List VExpr → VExpr → VExpr → VExpr → Prop}
  (refl : ∀ {Γ e A}, hasType Γ e A → defEq' Γ e e A)
  (hdf : ∀ {Γ e1 e2 A}, defEq Γ e1 e2 A → env.IsDefEq U Γ e1 e2 A) in
theorem IsDefEq1.unique_typing1
    (H : env.IsDefEq1 U hasType defEq Γ e1 e2 A) :
    hasType Γ e1 A ∧ hasType Γ e2 A := by
  induction H with
  | refl h => exact hty h
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | appDF _ _ ih1 ih2 => exact .appDF ih1 ih2
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF h1 _ ih => exact .defeqDF (hdf h1) ih
  | beta h1 h2 => exact .beta (hty h1) (hty h2)
  | eta h => exact .eta (hty h)
  | proofIrrel h1 h2 h3 => exact .proofIrrel (hty h1) (hty h2) (hty h3)
  | extra h1 h2 h3 => exact .extra h1 h2 h3

variable! (henv : Ordered env) in
theorem HasType1.unique_typing'
    (H1 : env.HasType1 U (IsDefEq1 env U hasType defEq) Γ e A1)
    (H2 : env.HasType1 U (IsDefEq1 env U hasType defEq) Γ e A2) :
    ∃ u, env.IsDefEq1 U hasType defEq Γ A1 A2 (.sort u) := by
  generalize eq1 : e = e' at H2
  induction H1 generalizing e' A2 with subst eq1
  | defeq h1 _ ih =>
    let ⟨_, ih⟩ := ih _ rfl H2
    exact ⟨_, h1.trans _⟩
    done
  | _ => ?_
  <;> cases H2

  case bvar.bvar _ =>
    done
  case const.const _ _ _ =>
    done
  case sort.sort _ =>
    done
  case app.app _ _ _ _ =>
    done
  case lam.lam _ _ _ _ =>
    done
  case forallE.forallE _ _ _ _ =>
    done
  case defeq.defeq _ _ _ =>
    done
  _
  -- | bvar h =>
  --   refine .bvar h.instL
  -- | @const _ _ ls' _ h1 h2 h3 =>
  --   simp [instL, instL_instL]
  --   exact .const h1 (by simp [h2, VLevel.WF.inst hls]) (by simp [h3])
  -- | sort _ _ h3 =>
  --   exact .sortDF (VLevel.WF.inst hls) (VLevel.WF.inst hls) (VLevel.inst_congr_l h3)
  -- | app _ _ ih1 ih2 => exact instL_instN ▸ .appDF ih1 ih2
  -- | lam _ _ ih1 ih2 => exact .lamDF ih1 ih2
  -- | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  -- | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  -- | beta _ _ ih1 ih2 => simpa using .beta ih1 ih2
  -- | eta _ ih => simpa [instL] using .eta ih
  -- | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  -- | extra h1 h2 h3 =>
  --   simp [instL, instL_instL]
  --   exact .extra h1 (by simp [h2, VLevel.WF.inst hls]) (by simp [h3])
-/

/-
variable! (henv : Ordered env) in
theorem IsDefEq.unique_typing'
    (H1 : env.IsDefEq U Γ e1 e2 A1) (H2 : env.IsDefEq U Γ e1 e2 A2) :
    ∃ u, env.IsDefEq U Γ A1 A2 (.sort u) := by
  generalize eq1 : e1 = e1', eq2 : e2 = e2' at H2
  induction H1 generalizing A2 with
  | bvar h =>

    refine .bvar h.instL
  | @const _ _ ls' _ h1 h2 h3 =>
    simp [instL, instL_instL]
    exact .const h1 (by simp [h2, VLevel.WF.inst hls]) (by simp [h3])
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF _ _ h3 =>
    exact .sortDF (VLevel.WF.inst hls) (VLevel.WF.inst hls) (VLevel.inst_congr_l h3)
  | appDF _ _ ih1 ih2 => exact instL_instN ▸ .appDF ih1 ih2
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ ih1 ih2 => simpa using .beta ih1 ih2
  | eta _ ih => simpa [instL] using .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 =>
    simp [instL, instL_instL]
    exact .extra h1 (by simp [h2, VLevel.WF.inst hls]) (by simp [h3])
-/


/- depends on church-rosser
variable! {env : VEnv} (henv : env.Ordered) in
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
    rw [ClosedN.liftN_eq_rev (eqA ▸ (henv.closedC h1).instL) (Nat.zero_le _)] at eqA
    exact eqA ▸ .const h1 h2 h3
  | symm _ ih => exact .symm (ih W eq2 eq1 eqA)
  | trans _ _ ih1 ih2 => sorry
  -- | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  -- | appDF _ _ ih1 ih2 => exact liftN_inst_hi .. ▸ .appDF (ih1 W) (ih2 W)
  -- | lamDF _ _ ih1 ih2 => exact .lamDF (ih1 W) (ih2 W.succ)
  -- | forallEDF _ _ ih1 ih2 => exact .forallEDF (ih1 W) (ih2 W.succ)
  -- | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  -- | beta _ _ ih1 ih2 =>
  --   exact liftN_inst_hi .. ▸ liftN_instN_hi .. ▸ .beta (ih1 W.succ) (ih2 W)
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

variable! {env : VEnv} (henv : env.Ordered) in
theorem HasType.weakN_inv (W : Ctx.LiftN n k Γ Γ')
    (H : env.HasType U Γ' (e.liftN n k) (A.liftN n k)) :
    env.HasType U Γ e A := IsDefEq.weakN_inv henv W H

variable! {env : VEnv} (henv : env.Ordered) in
theorem IsType.weakN_inv (W : Ctx.LiftN n k Γ Γ') (H : env.IsType U Γ' (A.liftN n k)) :
    env.IsType U Γ A := let ⟨_, h⟩ := H; ⟨_, h.weakN_inv henv W⟩
-/
