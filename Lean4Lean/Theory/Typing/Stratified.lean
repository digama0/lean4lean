import Lean4Lean.Theory.Typing.Lemmas

namespace Lean4Lean
namespace VEnv

open VExpr

def DefInv (env : VEnv) (U : Nat) (Γ : List VExpr) : VExpr → VExpr → Prop
  | .forallE A B, .forallE A' B' =>
    ∃ u v, env.IsDefEq U Γ A A' (.sort u) ∧ env.IsDefEq U (A::Γ) B B' (.sort v)
  | .forallE .., .sort .. | .sort .., .forallE .. => False
  | .sort u, .sort v => u ≈ v
  | _, _ => True

variable (henv : Ordered env) in
nonrec theorem DefInv.symm (h : DefInv env U Γ e1 e2) : DefInv env U Γ e2 e1 := by
  cases e1 <;> cases e2 <;> try trivial
  · exact h.symm
  · let ⟨u, v, h1, h2⟩ := h; exact ⟨u, v, h1.symm, h1.defeqDF_l henv h2.symm⟩

/-
section
set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:30 => HasType1 Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:30 => IsDefEq1 Γ e1 e2

variable (env : VEnv) (uvars : Nat)

variable (IsDefEq1 : List VExpr → VExpr → VExpr → Prop) in
inductive HasType1 : List VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ .bvar i : A
  | const :
    env.constants c = some (some ci) →
    (∀ l ∈ ls, l.WF uvars) →
    ls.length = ci.uvars →
    Γ ⊢ .const c ls : ci.type.instL ls
  | sort : l.WF uvars → Γ ⊢ .sort l : .sort (.succ l)
  | app : Γ ⊢ f : .forallE A B → Γ ⊢ a : A → Γ ⊢ .app f a : B.inst a
  | lam : Γ ⊢ A : .sort u → A::Γ ⊢ body : B → Γ ⊢ .lam A body : .forallE A B
  | forallE : Γ ⊢ A : .sort u → A::Γ ⊢ body : .sort v → Γ ⊢ .forallE A body : .sort (.imax u v)
  | defeq : Γ ⊢ A ≡ B → Γ ⊢ e : A → Γ ⊢ e : B
  | inst : A::Γ ⊢ e : B → Γ ⊢ e' : A → Γ ⊢ e.inst e' : B.inst e'

variable (HasType1 : List VExpr → VExpr → VExpr → Prop) in
inductive IsDefEq1 : List VExpr → VExpr → VExpr → Prop where
  | refl : Γ ⊢ e : A → Γ ⊢ e ≡ e
  | symm : Γ ⊢ e ≡ e' → Γ ⊢ e' ≡ e
  | trans : Γ ⊢ e₁ ≡ e₂ → Γ ⊢ e₂ ≡ e₃ → Γ ⊢ e₁ ≡ e₃
  | sortDF : l.WF uvars → l'.WF uvars → l ≈ l' → Γ ⊢ .sort l ≡ .sort l'
  | appDF :
    Γ ⊢ f : .forallE A B → Γ ⊢ f' : .forallE A B → Γ ⊢ a : A → Γ ⊢ a' : A →
    Γ ⊢ f ≡ f' → Γ ⊢ a ≡ a' → Γ ⊢ .app f a ≡ .app f' a'
  | lamDF : Γ ⊢ A ≡ A' → A::Γ ⊢ B ≡ B' → Γ ⊢ .lam A B ≡ .lam A' B'
  | forallEDF : Γ ⊢ A ≡ A' → A::Γ ⊢ B ≡ B' → Γ ⊢ .forallE A B ≡ .forallE A' B'
  | instDF :
    A::Γ ⊢ f : B → A::Γ ⊢ f' : B → Γ ⊢ a : A → Γ ⊢ a' : A →
    Γ ⊢ f ≡ f' → Γ ⊢ a ≡ a' → Γ ⊢ .inst f a ≡ .inst f' a'
  | beta : A::Γ ⊢ e : B → Γ ⊢ e' : A → Γ ⊢ .app (.lam A e) e' ≡ e.inst e'
  | eta : Γ ⊢ e : .forallE A B → Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e
  | proofIrrel : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ h'
  | extra :
    env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
    Γ ⊢ df.lhs.instL ls ≡ df.rhs.instL ls

end

theorem IsDefEq.induction1
    (defEq : List VExpr → VExpr → VExpr → Prop)
    (hasType : List VExpr → VExpr → VExpr → Prop)
    (hty : ∀ {Γ e A}, HasType1 env U defEq Γ e A → hasType Γ e A)
    (hdf : ∀ {Γ e1 e2}, IsDefEq1 env U hasType Γ e1 e2 → defEq Γ e1 e2)
    (H : env.IsDefEq U Γ e1 e2 A) :
    HasType1 env U defEq Γ e1 A ∧
    HasType1 env U defEq Γ e2 A ∧
    IsDefEq1 env U hasType Γ e1 e2 := by
  induction H with
  | bvar h => exact ⟨.bvar h, .bvar h, .refl (hty (.bvar h))⟩
  | @const _ _ ls' _ h1 h2 h3 =>
    refine ⟨.const h1 h2 h3, .const h1 h2 h3, .refl <| hty <| .const h1 h2 h3⟩
  | symm _ ih =>
    let ⟨ty1, ty2, df⟩ := ih
    exact ⟨ty2, ty1, .symm df⟩
  | trans _ _ ih1 ih2 =>
    let ⟨ty1, ty2, df1⟩ := ih1; let ⟨_, ty3, df2⟩ := ih2
    exact ⟨ty1, ty3, .trans df1 df2⟩
  | sortDF h1 h2 h3 =>
    refine ⟨.sort h1, .defeq (hdf ?_) (.sort h2), .sortDF h1 h2 h3⟩
    exact .symm <| .sortDF h1 h2 <| VLevel.succ_congr h3
  | appDF _ _ ih1 ih2 =>
    let ⟨hf, hf', ff⟩ := ih1; let ⟨ha, ha', aa⟩ := ih2
    refine' ⟨.app hf ha, .defeq (hdf (.instDF hB _ _ _ _ _)) (.app hf' ha'),
      .appDF (hty hf) (hty hf') (hty ha) (hty ha') ff aa⟩

    exact instL_instN ▸ .appDF ih1 ih2
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ ih1 ih2 => simpa using .beta ih1 ih2
  | eta _ ih => simpa [instL] using .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 =>
    simp [instL, instL_instL]
    exact .extra h1 (by simp [h2, VLevel.WF.inst hls]) (by simp [h3])



variable (henv : Ordered env) in
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

variable {env : VEnv} (henv : env.Ordered) in
theorem HasType.weakN_inv (W : Ctx.LiftN n k Γ Γ')
    (H : env.HasType U Γ' (e.liftN n k) (A.liftN n k)) :
    env.HasType U Γ e A := IsDefEq.weakN_inv henv W H

variable {env : VEnv} (henv : env.Ordered) in
theorem IsType.weakN_inv (W : Ctx.LiftN n k Γ Γ') (H : env.IsType U Γ' (A.liftN n k)) :
    env.IsType U Γ A := let ⟨_, h⟩ := H; ⟨_, h.weakN_inv henv W⟩
-/
