import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.NormalEq

inductive ReflTransGen (R : α → α → Prop) (a : α) : α → Prop where
  | zero : ReflTransGen R a a
  | trans : ReflTransGen R a b → R b c → ReflTransGen R a c

namespace Lean4Lean

open VExpr

section
set_option hygiene false
variable (TY : Typing)
local notation:65 Γ " ⊢ " e1 " ≫ " e2:30 => ParRed Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ⋙ " e2:30 => CParRed Γ e1 e2

inductive ParRed : List VExpr → VExpr → VExpr → Prop where
  | bvar : Γ ⊢ .bvar i ≫ .bvar i
  | sort : Γ ⊢ .sort u ≫ .sort u
  | const : Γ ⊢ .const c ls ≫ .const c ls
  | app : Γ ⊢ f ≫ f' → Γ ⊢ a ≫ a' → Γ ⊢ .app f a ≫ .app f' a'
  | lam : Γ ⊢ A ≫ A' → A::Γ ⊢ body ≫ body' → Γ ⊢ .lam A body ≫ .lam A' body'
  | forallE : Γ ⊢ A ≫ A' → A::Γ ⊢ B ≫ B' → Γ ⊢ .forallE A B ≫ .forallE A' B'
  | beta : A::Γ ⊢ e₁ ≫ e₁' → Γ ⊢ e₂ ≫ e₂' → Γ ⊢ .app (.lam A e₁) e₂ ≫ e₁'.inst e₂'
  | extra : TY.Pat p r → p.Matches e m1 m2 → r.2.OK (TY.IsDefEq Γ) m1 m2 →
    (∀ a, Γ ⊢ m2 a ≫ m2' a) → Γ ⊢ e ≫ r.1.apply m1 m2'

def IsNeutral (Γ : List VExpr) (e : VExpr) : Prop :=
  (∀ A e₁ e₂, e ≠ .app (.lam A e₁) e₂) ∧
  (∀ p r m1 m2, TY.Pat p r → p.Matches e m1 m2 → ¬r.2.OK (TY.IsDefEq Γ) m1 m2)

inductive CParRed : List VExpr → VExpr → VExpr → Prop where
  | bvar : Γ ⊢ .bvar i ⋙ .bvar i
  | sort : Γ ⊢ .sort u ⋙ .sort u
  | const : IsNeutral TY Γ (.const c ls) → Γ ⊢ .const c ls ⋙ .const c ls
  | app : IsNeutral TY Γ (.app f a) → Γ ⊢ f ⋙ f' → Γ ⊢ a ⋙ a' → Γ ⊢ .app f a ⋙ .app f' a'
  | lam : Γ ⊢ A ⋙ A' → A::Γ ⊢ body ⋙ body' → Γ ⊢ .lam A body ⋙ .lam A' body'
  | forallE : Γ ⊢ A ⋙ A' → A::Γ ⊢ B ⋙ B' → Γ ⊢ .forallE A B ⋙ .forallE A' B'
  | beta : A::Γ ⊢ e₁ ⋙ e₁' → Γ ⊢ e₂ ⋙ e₂' → Γ ⊢ .app (.lam A e₁) e₂ ⋙ e₁'.inst e₂'
  | extra : TY.Pat p r → p.Matches e m1 m2 → r.2.OK (TY.IsDefEq Γ) m1 m2 →
    (∀ a, Γ ⊢ m2 a ⋙ m2' a) → Γ ⊢ e ⋙ r.1.apply m1 m2'

end

variable {TY : Typing}

protected theorem ParRed.rfl : ∀ {e}, ParRed TY Γ e e
  | .bvar .. => .bvar
  | .sort .. => .sort
  | .const .. => .const
  | .app .. => .app ParRed.rfl ParRed.rfl
  | .lam .. => .lam ParRed.rfl ParRed.rfl
  | .forallE .. => .forallE ParRed.rfl ParRed.rfl

theorem ParRed.weakN (W : Ctx.LiftN n k Γ Γ') (H : ParRed TY Γ e1 e2) :
    ParRed TY Γ' (e1.liftN n k) (e2.liftN n k) := by
  induction H generalizing k Γ' with
  | bvar | sort | const => exact .rfl
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | beta _ _ ih1 ih2 =>
    simp [liftN, liftN_inst_hi]
    exact .beta (ih1 W.succ) (ih2 W)
  | extra h1 h2 h3 _ ih =>
    rw [Pattern.RHS.liftN_apply]
    refine .extra h1 (Pattern.matches_liftN.2 ⟨_, h2, funext_iff.1 rfl⟩)
      (h3.weakN W) (fun a => ih _ W)

variable (H₀ : ParRed TY Γ₀ a1 a2) (H₀' : TY.HasType Γ₀ a1 A₀) in
theorem ParRed.instN (W : Ctx.InstN Γ₀ a1 A₀ k Γ₁ Γ)
    (H : ParRed TY Γ₁ e1 e2) : ParRed TY Γ (e1.inst a1 k) (e2.inst a2 k) := by
  induction H generalizing Γ k with
  | @bvar _ i =>
    dsimp [inst]
    induction W generalizing i with
    | zero =>
      cases i with simp [inst_lift]
      | zero => exact H₀
      | succ h => exact .rfl
    | succ _ ih =>
      cases i with simp
      | zero => exact .rfl
      | succ h => exact ih.weakN .one
  | sort | const => exact .rfl
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | beta _ _ ih1 ih2 =>
    simp [inst, inst0_inst_hi]
    exact .beta (ih1 W.succ) (ih2 W)
  | extra h1 h2 h3 _ ih =>
    rw [Pattern.RHS.instN_apply]
    exact .extra h1 (Pattern.matches_instN h2) (h3.instN W H₀') (fun a => ih _ W)

theorem ParRed.defeq (H : ParRed TY Γ e e') (he : TY.HasType Γ e A) : TY.IsDefEq Γ e e' := by
  induction H generalizing A with
  | bvar | sort | const => exact TY.refl he
  | app _ _ ih1 ih2 =>
    have ⟨_, _, h1, h2⟩ := TY.app_inv he
    exact TY.appDF h1 (ih1 h1) h2 (ih2 h2)
  | lam _ _ ih1 ih2 =>
    have ⟨_, _, h1, h2⟩ := TY.lam_inv he
    exact TY.lamDF h1 (ih1 h1) (ih2 h2)
  | forallE _ _ ih1 ih2 =>
    have ⟨_, _, h1, h2⟩ := TY.forallE_inv he
    exact TY.forallEDF h1 (ih1 h1) h2 (ih2 h2)
  | beta _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := TY.app_inv he
    have ⟨_, _, hA, hb⟩ := TY.lam_inv hf
    have hf' := TY.lam hA hb
    replace ha := TY.defeq_r (TY.forallE_defInv (TY.uniq hf hf')).1 ha
    exact TY.trans (TY.appDF hf' (TY.lamDF hA (TY.refl hA) (ih1 hb)) ha (ih2 ha))
      (TY.beta (TY.defeq_l (ih1 hb) hb) (TY.defeq_l (ih2 ha) ha))
  | @extra p r e m1 m2 Γ m2' h1 h2 h3 _ ih =>
    exact TY.trans (TY.pat_wf h1 h2 he h3) <|
     .apply_pat ih (TY.defeq_l (TY.pat_wf h1 h2 he h3) he)

theorem ParRed.hasType (H : ParRed TY Γ e e') (he : TY.HasType Γ e A) : TY.HasType Γ e' A :=
  TY.defeq_l (H.defeq he) he

theorem ParRed.defeqDFC (W : IsDefEqCtx TY.IsDefEq Γ₀ Γ₁ Γ₂)
    (h : TY.HasType Γ₁ e1 A) (H : ParRed TY Γ₁ e1 e2) : ParRed TY Γ₂ e1 e2 := by
  induction H generalizing Γ₂ A with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := TY.app_inv h
    exact .app (ih1 W hf) (ih2 W ha)
  | lam _ _ ih1 ih2 =>
    have ⟨_, _, hA, he⟩ := TY.lam_inv h
    exact .lam (ih1 W hA) (ih2 (W.succ (TY.refl hA)) he)
  | forallE _ _ ih1 ih2 =>
    have ⟨_, _, hA, hB⟩ := TY.forallE_inv h
    exact .forallE (ih1 W hA) (ih2 (W.succ (TY.refl hA)) hB)
  | beta _ _ ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := TY.app_inv h
    have ⟨_, _, hA, hb⟩ := TY.lam_inv hf
    exact .beta (ih1 (W.succ (TY.refl hA)) hb) (ih2 W ha)
  | @extra p r e m1 m2 Γ m2' h1 h2 h3 _ ih =>
    exact .extra h1 h2 (h3.map fun a b h => TY.isDefEq_DFC W h) fun a =>
      let ⟨_, h⟩ := h2.hasType h a; ih a W h


theorem ParRed.apply_pat {p : Pattern} (r : p.RHS) {m1 m2 m3}
    (H : ∀ a, ParRed TY Γ (m2 a) (m3 a)) : ParRed TY Γ (r.apply m1 m2) (r.apply m1 m3) := by
  match r with
  | .fixed .. => exact .rfl
  | .app f a => exact .app (apply_pat f H) (apply_pat a H)
  | .var f => exact H _

theorem CParRed.toParRed (H : CParRed TY Γ e e') : ParRed TY Γ e e' := by
  induction H with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | beta _ _ ih1 ih2 => exact .beta ih1 ih2
  | extra h1 h2 h3 _ ih3 => exact .extra h1 h2 h3 ih3

theorem CParRed.exists (H : TY.HasType Γ e A) : ∃ e', CParRed TY Γ e e' := by
  induction e using VExpr.brecOn generalizing Γ A with | _ e e_ih => ?_
  have neut e
      (H' : TY.HasType Γ e A)
      (e_ih : VExpr.below (motive := fun {e} =>
        ∀ {Γ A}, TY.HasType Γ e A → ∃ e', CParRed TY Γ e e') e)
      (hn : IsNeutral TY Γ e → ∃ e', CParRed TY Γ e e') : ∃ e', CParRed TY Γ e e' := by
    by_cases h : ∃ A e₁ e₂, e = .app (.lam A e₁) e₂
    · obtain ⟨A, e, a, rfl⟩ := h
      have ⟨_, _, hf, ha⟩ := TY.app_inv H'
      have ⟨_, _, _, he⟩ := TY.lam_inv hf
      have ⟨_, he⟩ := e_ih.1.2.2.1.1 he
      have ⟨_, ha⟩ := e_ih.2.1.1 ha
      exact ⟨_, .beta he ha⟩
    by_cases h' : ∃ p r m1 m2, TY.Pat p r ∧ p.Matches e m1 m2 ∧ r.2.OK (TY.IsDefEq Γ) m1 m2
    · let ⟨p, r, m1, m2, h1, hp2, hp3⟩ := h'
      suffices ∃ m3 : p.Path.2 → VExpr, ∀ a, CParRed TY Γ (m2 a) (m3 a) from
        let ⟨_, h3⟩ := this; ⟨_, .extra h1 hp2 hp3 h3⟩
      clear H hn h h' r h1 hp3
      induction p generalizing e A with
      | const => exact ⟨nofun, nofun⟩
      | app f a ih1 ih2 =>
        let .app hm1 hm2 := hp2
        have ⟨_, _, H1, H2⟩ := TY.app_inv H'
        have ⟨m2l, hl⟩ := ih1 _ H1 e_ih.1.2 _ _ hm1
        have ⟨m2r, hr⟩ := ih2 _ H2 e_ih.2.1.2 _ _ hm2
        exact ⟨Sum.elim m2l m2r, Sum.rec hl hr⟩
      | var _ ih =>
        let .var hm1 := hp2
        have ⟨_, _, H1, H2⟩ := TY.app_inv H'
        have ⟨m2l, hl⟩ := ih _ H1 e_ih.1.2 _ _ hm1
        have ⟨e', hs⟩ := e_ih.2.1.1 H2
        exact ⟨Option.rec e' m2l, Option.rec hs hl⟩
    · exact hn ⟨
        fun _ _ _ hn => h ⟨_, _, _, hn⟩,
        fun _ _ _ _ h1 h2 h3 => h' ⟨_, _, _, _, h1, h2, h3⟩⟩
  cases e with
  | bvar i => exact ⟨_, .bvar⟩
  | sort => exact ⟨_, .sort⟩
  | const n ls => exact neut _ H e_ih fun hn => ⟨_, .const hn⟩
  | app ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := TY.app_inv H
    have ⟨_, h1⟩ := e_ih.1.1 hf
    have ⟨_, h2⟩ := e_ih.2.1.1 ha
    exact neut _ H e_ih fun hn => ⟨_, .app hn h1 h2⟩
  | lam ih1 ih2 =>
    have ⟨_, _, hA, he⟩ := TY.lam_inv H
    have ⟨_, h1⟩ := e_ih.1.1 hA
    have ⟨_, h2⟩ := e_ih.2.1.1 he
    exact ⟨_, .lam h1 h2⟩
  | forallE ih1 ih2 =>
    have ⟨_, _, hA, hB⟩ := TY.forallE_inv H
    have ⟨_, h1⟩ := e_ih.1.1 hA
    have ⟨_, h2⟩ := e_ih.2.1.1 hB
    exact ⟨_, .forallE h1 h2⟩
