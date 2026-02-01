import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.NormalEq

-- TODO: remove, this is now part of ChurchRosser.lean

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
  | extra : TY.Pat p r → p.Matches e m1 m2 → r.2.OK (TY.IsDefEqU Γ) m1 m2 →
    (∀ a, Γ ⊢ m2 a ≫ m2' a) → Γ ⊢ e ≫ r.1.apply m1 m2'

def NonNeutral (TY : Typing) (Γ : List VExpr) (e : VExpr) : Prop :=
  (∃ A e₁ e₂, e = .app (.lam A e₁) e₂) ∨
  (∃ p r m1 m2, TY.Pat p r ∧ p.Matches e m1 m2 ∧ r.2.OK (TY.IsDefEqU Γ) m1 m2)

inductive CParRed : List VExpr → VExpr → VExpr → Prop where
  | bvar : Γ ⊢ .bvar i ⋙ .bvar i
  | sort : Γ ⊢ .sort u ⋙ .sort u
  | const : ¬NonNeutral TY Γ (.const c ls) → Γ ⊢ .const c ls ⋙ .const c ls
  | app : ¬NonNeutral TY Γ (.app f a) → Γ ⊢ f ⋙ f' → Γ ⊢ a ⋙ a' → Γ ⊢ .app f a ⋙ .app f' a'
  | lam : Γ ⊢ A ⋙ A' → A::Γ ⊢ body ⋙ body' → Γ ⊢ .lam A body ⋙ .lam A' body'
  | forallE : Γ ⊢ A ⋙ A' → A::Γ ⊢ B ⋙ B' → Γ ⊢ .forallE A B ⋙ .forallE A' B'
  | beta : A::Γ ⊢ e₁ ⋙ e₁' → Γ ⊢ e₂ ⋙ e₂' → Γ ⊢ .app (.lam A e₁) e₂ ⋙ e₁'.inst e₂'
  | extra : TY.Pat p r → p.Matches e m1 m2 → r.2.OK (TY.IsDefEqU Γ) m1 m2 →
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

variable! (H₀ : ParRed TY Γ₀ a1 a2) (H₀' : TY.HasType Γ₀ a1 A₀) in
theorem ParRed.instN (W : Ctx.InstN Γ₀ a1 A₀ k Γ₁ Γ)
    (H : ParRed TY Γ₁ e1 e2) : ParRed TY Γ (e1.inst a1 k) (e2.inst a2 k) := by
  induction H generalizing Γ k with
  | @bvar _ i =>
    dsimp [inst]
    induction W generalizing i with
    | zero =>
      cases i with simp
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

theorem ParRed.defeq (H : ParRed TY Γ e e') (he : TY.HasType Γ e A) : TY.IsDefEqU Γ e e' := by
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

theorem ParRed.defeqDFC (W : IsDefEqCtx TY.IsDefEqU Γ₀ Γ₁ Γ₂)
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
    exact .extra h1 h2 (h3.map fun a b h => TY.isDefEqU_DFC W h) fun a =>
      let ⟨_, h⟩ := h2.hasType h a; ih a W h

theorem ParRed.apply_pat {p : Pattern} (r : p.RHS) {m1 m2 m3}
    (H : ∀ a, ParRed TY Γ (m2 a) (m3 a)) : ParRed TY Γ (r.apply m1 m2) (r.apply m1 m3) := by
  match r with
  | .fixed .. => exact .rfl
  | .app f a => exact .app (apply_pat f H) (apply_pat a H)
  | .var f => exact H _

theorem Pattern.RHS.apply_liftN {p : Pattern} (r : p.RHS) {m1 m2} :
    (r.apply m1 m2).liftN k n = r.apply m1 (fun a => (m2 a).liftN k n) := by
  induction r with simp! [*]
  | fixed _ _ h => exact instL_liftN.symm.trans ((h.liftN_eq (Nat.zero_le _)).symm ▸ rfl)

-- theorem IsDefEqU.applyL {p : Pattern} (r : p.RHS) {m1 m1' m2}
--     (H : ∀ a, List.Forall₂ (· ≈ ·) (m1 a) (m1' a))
--     (H2 : TY.HasType Γ (r.apply m1 m2) A) :
--     TY.IsDefEqU Γ (r.apply m1 m2) (r.apply m1' m2) := by
--   match r with
--   | .fixed .. =>
--     dsimp [Pattern.RHS.apply]
--     exact TY.hasType_instL _ _
--   | .app f a => exact .app (apply_pat f H) (apply_pat a H)
--   | .var f => exact H _

theorem ParRed.weakN_inv (W : Ctx.LiftN n k Γ Γ')
    (H : ParRed TY Γ' (e1.liftN n k) e2') :
    ∃ e2, ParRed TY Γ e1 e2 ∧ e2' = e2.liftN n k := by
  generalize eq : e1.liftN n k = e1' at H
  induction H generalizing e1 Γ k with
  | bvar => cases e1 <;> cases eq; exact ⟨_, .bvar, rfl⟩
  | sort => cases e1 <;> cases eq; exact ⟨_, .sort, rfl⟩
  | const => cases e1 <;> cases eq; exact ⟨_, .const, rfl⟩
  | app h1 h2 ih1 ih2 =>
    cases e1 <;> cases eq
    obtain ⟨_, a1, rfl⟩ := ih1 W rfl
    obtain ⟨_, b1, rfl⟩ := ih2 W rfl
    exact ⟨_, .app a1 b1, rfl⟩
  | lam h1 h2 ih1 ih2 =>
    cases e1 <;> cases eq
    obtain ⟨_, a1, rfl⟩ := ih1 W rfl
    obtain ⟨_, b1, rfl⟩ := ih2 W.succ rfl
    exact ⟨_, .lam a1 b1, rfl⟩
  | forallE h1 h2 ih1 ih2 =>
    cases e1 <;> cases eq
    obtain ⟨_, a1, rfl⟩ := ih1 W rfl
    obtain ⟨_, b1, rfl⟩ := ih2 W.succ rfl
    exact ⟨_, .forallE a1 b1, rfl⟩
  | beta h1 h2 ih1 ih2 =>
    cases e1 <;> injection eq
    rename_i f a eq eq2; cases eq2
    cases f <;> cases eq
    obtain ⟨_, a1, rfl⟩ := ih1 W.succ rfl
    obtain ⟨_, b1, rfl⟩ := ih2 W rfl
    exact ⟨_, .beta a1 b1, (liftN_inst_hi ..).symm⟩
  | @extra p r e m1 m2 Γ' m2' h1 h2 h3 h4 ih =>
    suffices ∃ m3 m3' : _ → _, p.Matches e1 m1 m3 ∧
        (∀ a, ParRed TY Γ (m3 a) (m3' a)) ∧
        (∀ a, m2 a = (m3 a).liftN n k) ∧
        (∀ a, m2' a = (m3' a).liftN n k) by
      let ⟨m3, m3', a1, a2, a3, a4⟩ := this
      refine ⟨_, .extra h1 a1 (h3.map fun _ _ h => ?_) a2,
        .trans (by congr; funext; apply a4) r.1.apply_liftN.symm⟩
      rw [(funext a3 : m2 = _), ← Pattern.RHS.apply_liftN, ← Pattern.RHS.apply_liftN] at h
      exact (TY.isDefEqU_weakN_iff W).1 h
    clear h1 h3 r
    induction h2 generalizing e1 with
    | const => cases e1 <;> cases eq; exact ⟨_, nofun, .const, nofun, nofun, nofun⟩
    | var h1 ih1 =>
      cases e1 <;> cases eq
      have ⟨_, _, a1, a2, a3, a4⟩ := ih1 (h4 <| some ·) (ih <| some ·) rfl
      have ⟨_, b2, b4⟩ := ih none W rfl
      exact ⟨_, Option.rec _ _, .var a1, Option.rec b2 a2, Option.rec rfl a3, Option.rec b4 a4⟩
    | app h1 h2 ih1 ih2 =>
      cases e1 <;> cases eq
      have ⟨_, _, a1, a2, a3, a4⟩ := ih1 (h4 <| .inl ·) (ih <| .inl ·) rfl
      have ⟨_, _, b1, b2, b3, b4⟩ := ih2 (h4 <| .inr ·) (ih <| .inr ·) rfl
      exact ⟨_, Sum.rec _ _, .app a1 b1, Sum.rec a2 b2, Sum.rec a3 b3, Sum.rec a4 b4⟩

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
  revert e_ih; change let motive := ?_; ∀ _: e.below (motive := motive), _; intro motive e_ih
  have neut {e} (H' : TY.HasType Γ e A) (e_ih : e.below (motive := motive)) :
      NonNeutral TY Γ e → ∃ e', CParRed TY Γ e e' := by
    rintro (⟨A, e, a, rfl⟩ | ⟨p, r, m1, m2, h1, hp2, hp3⟩)
    · have ⟨_, _, hf, ha⟩ := TY.app_inv H'
      have ⟨_, _, _, he⟩ := TY.lam_inv hf
      have ⟨_, he⟩ := e_ih.1.2.2.1 he
      have ⟨_, ha⟩ := e_ih.2.1 ha
      exact ⟨_, .beta he ha⟩
    · suffices ∃ m3 : p.Path.2 → VExpr, ∀ a, CParRed TY Γ (m2 a) (m3 a) from
        let ⟨_, h3⟩ := this; ⟨_, .extra h1 hp2 hp3 h3⟩
      clear H r h1 hp3
      induction p generalizing e A with
      | const => exact ⟨nofun, nofun⟩
      | app f a ih1 ih2 =>
        let .app hm1 hm2 := hp2
        have ⟨_, _, H1, H2⟩ := TY.app_inv H'
        have ⟨m2l, hl⟩ := ih1 H1 e_ih.1.2 _ _ hm1
        have ⟨m2r, hr⟩ := ih2 H2 e_ih.2.2 _ _ hm2
        exact ⟨Sum.elim m2l m2r, Sum.rec hl hr⟩
      | var _ ih =>
        let .var hm1 := hp2
        have ⟨_, _, H1, H2⟩ := TY.app_inv H'
        have ⟨m2l, hl⟩ := ih H1 e_ih.1.2 _ _ hm1
        have ⟨e', hs⟩ := e_ih.2.1 H2
        exact ⟨Option.rec e' m2l, Option.rec hs hl⟩
  cases e with
  | bvar i => exact ⟨_, .bvar⟩
  | sort => exact ⟨_, .sort⟩
  | const n ls => exact Classical.byCases (neut H e_ih) fun hn => ⟨_, .const hn⟩
  | app ih1 ih2 =>
    have ⟨_, _, hf, ha⟩ := TY.app_inv H
    have ⟨_, h1⟩ := e_ih.1.1 hf
    have ⟨_, h2⟩ := e_ih.2.1 ha
    exact Classical.byCases (neut H e_ih) fun hn => ⟨_, .app hn h1 h2⟩
  | lam ih1 ih2 =>
    have ⟨_, _, hA, he⟩ := TY.lam_inv H
    have ⟨_, h1⟩ := e_ih.1.1 hA
    have ⟨_, h2⟩ := e_ih.2.1 he
    exact ⟨_, .lam h1 h2⟩
  | forallE ih1 ih2 =>
    have ⟨_, _, hA, hB⟩ := TY.forallE_inv H
    have ⟨_, h1⟩ := e_ih.1.1 hA
    have ⟨_, h2⟩ := e_ih.2.1 hB
    exact ⟨_, .forallE h1 h2⟩

theorem ParRed.triangle (H1 : TY.HasType Γ e A) (H : ParRed TY Γ e e') (H2 : CParRed TY Γ e o) :
    ∃ o', ParRed TY Γ e' o' ∧ NormalEq TY Γ o' o := by
  induction e using VExpr.brecOn generalizing Γ A e' o with | _ e e_ih => ?_
  revert e_ih; change let motive := ?_; ∀ _: e.below (motive := motive), _; intro motive e_ih
  induction H2 generalizing A e' with
  | bvar =>
    cases H with
    | bvar => exact ⟨_, .rfl, .refl H1⟩
    | extra h1 h2 => cases h2
  | sort =>
    cases H with
    | sort => exact ⟨_, .rfl, .refl H1⟩
    | extra h1 h2 => cases h2
  | const hn =>
    cases H with
    | const => exact ⟨_, .rfl, .refl H1⟩
    | extra h1 h2 h3 => cases hn (.inr ⟨_, _, _, _, h1, h2, h3⟩)
  | app hn _ _ ih1 ih2 =>
    have ⟨_, _, l1, l2⟩ := TY.app_inv H1
    cases H with
    | app r1 r2 =>
      let ⟨_, p1, n1⟩ := ih1 l1 r1 e_ih.1.2; let ⟨_, p2, n2⟩ := ih2 l2 r2 e_ih.2.2
      have o1 := p1.hasType (r1.hasType l1); have o2 := p2.hasType (r2.hasType l2)
      exact ⟨_, .app p1 p2, .appDF o1 (TY.defeq_l n1.defeq o1) o2 (TY.defeq_l n2.defeq o2) n1 n2⟩
    | extra h1 h2 h3 => cases hn (.inr ⟨_, _, _, _, h1, h2, h3⟩)
    | beta => cases hn (.inl ⟨_, _, _, rfl⟩)
  | lam _ _ ih1 ih2 =>
    have ⟨_, _, l1, l2⟩ := TY.lam_inv H1
    cases H with
    | lam r1 r2 =>
      let ⟨_, p1, n1⟩ := ih1 l1 r1 e_ih.1.2; let ⟨_, p2, n2⟩ := ih2 l2 r2 e_ih.2.2
      have := TY.symm <| TY.trans (r1.defeq l1) (p1.defeq (r1.hasType l1))
      exact ⟨_, .lam p1 (p2.defeqDFC (.succ .zero (r1.defeq l1)) (r2.hasType l2)),
        .lamDF l1 this (TY.trans (TY.symm n1.defeq) this) n2⟩
    | extra h1 h2 => cases h2
  | forallE _ _ ih1 ih2 =>
    have ⟨_, _, l1, l2⟩ := TY.forallE_inv H1
    cases H with
    | forallE r1 r2 =>
      let ⟨_, p1, n1⟩ := ih1 l1 r1 e_ih.1.2; let ⟨_, p2, n2⟩ := ih2 l2 r2 e_ih.2.2
      exact ⟨_, .forallE p1 (p2.defeqDFC (.succ .zero (r1.defeq l1)) (r2.hasType l2)),
        .forallEDF l1 (TY.symm <| TY.trans (r1.defeq l1) (p1.defeq (r1.hasType l1)))
          n1 (p2.hasType (r2.hasType l2)) n2⟩
    | extra h1 h2 => cases h2
  | beta l1 l2 ih1 ih2 =>
    have ⟨_, _, lf, la⟩ := TY.app_inv H1
    have ⟨_, _, lA, le⟩ := TY.lam_inv lf
    have hw := (TY.forallE_defInv (TY.uniq lf (TY.lam lA le))).1
    have la' := TY.defeq_r hw la
    obtain ⟨⟨-, ⟨-, e_ih1 : VExpr.below ..⟩, ⟨he, e_ih2 : VExpr.below ..⟩⟩,
      ⟨ha, e_ih3 : VExpr.below ..⟩⟩ := e_ih
    cases H with
    | app rf ra =>
      let ⟨_, p3, n3⟩ := ha la ra l2
      cases rf with
      | lam rA re =>
        let ⟨_, p2, n2⟩ := he le re l1
        refine ⟨_, .beta (p2.defeqDFC (.succ .zero (rA.defeq lA)) (re.hasType le)) p3, ?_⟩
        refine .trans
          (.instN_r (p3.hasType (ra.hasType la')) n3 .zero (p2.hasType (re.hasType le)))
          (.instN (l2.toParRed.hasType la') .zero n2)
      | extra h1 h2 => cases h2
    | beta re ra =>
      let ⟨_, p2, n2⟩ := he le re l1
      let ⟨_, p3, n3⟩ := ha la ra l2
      refine ⟨_, .instN p3 (ra.hasType la') .zero p2, ?_⟩
      refine .trans
        (.instN_r (p3.hasType (ra.hasType la')) n3 .zero (p2.hasType (re.hasType le)))
        (.instN (l2.toParRed.hasType la') .zero n2)
    | extra h1 h2 => cases h2 with | app h | var h => cases h
  | @extra p r e m1 m2 Γ m2' l1 l2 l3 l4 ih =>
    have :
      (∃ m3 m3' : p.Path.snd → VExpr, p.Matches e' m1 m3 ∧
        (∀ a, ParRed TY Γ (m2 a) (m3 a)) ∧
        (∀ a, ParRed TY Γ (m3 a) (m3' a)) ∧
        (∀ a, NormalEq TY Γ (m3' a) (m2' a))) ∨
      (∃ p₁ e₁' e₁ m1₁ m2₁, Subpattern p₁ p ∧ (p₁ = p → e₁ = e ∧ e₁' = e' ∧ m1₁ ≍ m1 ∧ m2₁ ≍ m2) ∧
        p₁.Matches e₁ m1₁ m2₁ ∧ ∃ p' r m1 m2 m2',
        TY.Pat p' r ∧ p'.Matches e₁ m1 m2 ∧ r.2.OK (TY.IsDefEqU Γ) m1 m2 ∧
        (∀ a, ParRed TY Γ (m2 a) (m2' a)) ∧ e₁' = r.1.apply m1 m2') := by
      clear l1 l3 l4 r
      induction H generalizing p A with
      | const =>
        cases id l2; exact .inl ⟨_, _, l2, nofun, fun _ => .rfl, nofun⟩
      | @app Γ f f' a a' hf ha ih1 ih2 =>
        have ⟨_, _, Hf, Ha⟩ := TY.app_inv H1
        cases l2 with
        | var lf =>
          match ih1 lf (ih <| some ·) Hf e_ih.1.2 with
          | .inr ⟨_, _, _, _, _, h1, h2, h3⟩ =>
            refine .inr ⟨_, _, _, _, _, h1.varL, ?_, h3⟩
            rintro rfl; cases h1.antisymm (.varL .refl)
          | .inl ⟨_, _, f1, f2, f3, f4⟩ =>
            have ⟨_, a3, a4⟩ := ih none Ha ha e_ih.2.2
            exact .inl ⟨_, (·.elim _ _), .var f1,
              (·.casesOn ha f2), (·.casesOn a3 f3), (·.casesOn a4 f4)⟩
        | app lf la =>
          match ih1 lf (ih <| .inl ·) Hf e_ih.1.2 with
          | .inr ⟨_, _, _, _, _, h1, h2, h3⟩ =>
            refine .inr ⟨_, _, _, _, _, h1.appL, ?_, h3⟩
            rintro rfl; cases h1.antisymm (.appL .refl)
          | .inl ⟨_, _, f1, f2, f3, f4⟩ =>
            match ih2 la (ih <| .inr ·) Ha e_ih.2.2 with
            | .inr ⟨_, _, _, _, _, h1, h2, h3⟩ =>
              refine .inr ⟨_, _, _, _, _, h1.appR, ?_, h3⟩
              rintro rfl; cases h1.antisymm (.appR .refl)
            | .inl ⟨_, _, a1, a2, a3, a4⟩ =>
              exact .inl ⟨_, Sum.elim _ _, .app f1 a1,
                (·.casesOn f2 a2), (·.casesOn f3 a3), (·.casesOn f4 a4)⟩
      | beta _ _ => cases l2 with | var h | app h => cases h
      | @extra _ _ _ _ _ _ _ r1 r2 r3 r4 =>
        exact .inr ⟨_, _, _, _, _, .refl, fun _ => ⟨rfl, rfl, .rfl, .rfl⟩,
          l2, _, _, _, _, _, r1, r2, r3, r4, rfl⟩
      | _ => cases l2
    match this with
    | .inl ⟨m3, m3', h1, h2, h3, h4⟩ =>
      refine
        have h := .extra l1 h1 (l3.map fun _ _ h => ?_) h3
        ⟨_, h, .apply_pat (fun a _ _ => h4 a) (h.hasType (H.hasType H1))⟩
      have ⟨_, h1⟩ := TY.has_type h
      refine TY.trans (TY.symm (.apply_pat (fun _ _ => (h2 _).defeq) h1))
        (TY.trans h (.apply_pat (fun _ _ => (h2 _).defeq) (TY.defeq_l h h1)))
    | .inr ⟨_, _, _, _, _, h1, h2, l2', _, _, _, _, m3, r1, r2, r3, r4, e⟩ =>
      obtain ⟨_, -, -, hr, -⟩ := Pattern.matches_inter.1 ⟨⟨_, _, r2⟩, ⟨_, _, l2'⟩⟩
      obtain ⟨rfl, rfl, ⟨⟩⟩ := TY.pat_uniq l1 r1 h1 hr
      obtain ⟨rfl, rfl, ⟨⟩, ⟨⟩⟩ := h2 rfl; subst e
      obtain ⟨rfl, rfl⟩ := l2'.uniq r2
      suffices ∃ m3' : p.Path.snd → VExpr,
          (∀ a, ParRed TY Γ (m3 a) (m3' a)) ∧
          (∀ a, NormalEq TY Γ (m3' a) (m2' a)) by
        let ⟨m3', h3, h4⟩ := this
        refine ⟨_, ?h3, .apply_pat (fun a _ _ => h4 a) ((?h3).hasType (H.hasType H1))⟩
        exact .apply_pat _ h3
      clear H r l1 l2 l3 l4 this h1 h2 r1 r2 r3 hr
      induction l2' generalizing A with
      | const => exact ⟨nofun, nofun, nofun⟩
      | app _ _ ih1 ih2 =>
        have ⟨_, _, Hf, Ha⟩ := TY.app_inv H1
        obtain ⟨⟨hl, e_ih1 : VExpr.below ..⟩, ⟨hr, e_ih2 : VExpr.below ..⟩⟩ := id e_ih
        have ⟨g1, l1, l2⟩ := ih1 (ih <| .inl ·) _ Hf e_ih1 (r4 <| .inl ·)
        have ⟨g2, r1, r2⟩ := ih2 (ih <| .inr ·) _ Ha e_ih2 (r4 <| .inr ·)
        exact ⟨Sum.elim g1 g2, (·.casesOn l1 r1), (·.casesOn l2 r2)⟩
      | var _ ih1 =>
        have ⟨_, _, Hf, Ha⟩ := TY.app_inv H1
        obtain ⟨⟨hl, e_ih1 : VExpr.below ..⟩, ⟨hr, e_ih2 : VExpr.below ..⟩⟩ := id e_ih
        have ⟨g1, l1, l2⟩ := ih1 (ih <| some ·) _ Hf e_ih1 (r4 <| some ·)
        have ⟨g2, r1, r2⟩ := ih none Ha (r4 none) e_ih2
        exact ⟨(·.elim g2 g1), (·.casesOn r1 l1), (·.casesOn r2 l2)⟩

theorem ParRed.church_rosser (H : TY.HasType Γ e A)
    (H1 : ParRed TY Γ e e₁) (H2 : ParRed TY Γ e e₂) :
      ∃ e₁' e₂', ParRed TY Γ e₁ e₁' ∧ ParRed TY Γ e₂ e₂' ∧ NormalEq TY Γ e₁' e₂' := by
  let ⟨e', h'⟩ := CParRed.exists H
  let ⟨_, l1, l2⟩ := H1.triangle H h'
  let ⟨_, r1, r2⟩ := H2.triangle H h'
  exact ⟨_, _, l1, r1, l2.trans r2.symm⟩

def ParRedS (TY : Typing) (Γ : List VExpr) : VExpr → VExpr → Prop := ReflTransGen (ParRed TY Γ)

theorem ParRedS.hasType (H : ParRedS TY Γ e e') : TY.HasType Γ e A → TY.HasType Γ e' A := by
  induction H with
  | rfl => exact id
  | tail h1 h2 ih => exact h2.hasType ∘ ih

theorem ParRedS.defeq (H : ParRedS TY Γ e e') (h : TY.HasType Γ e A) : TY.IsDefEqU Γ e e' := by
  induction H with
  | rfl => exact TY.refl h
  | tail h1 h2 ih => refine TY.trans ih (h2.defeq (hasType h1 h))

theorem ParRedS.defeqDFC (W : IsDefEqCtx TY.IsDefEqU Γ₀ Γ₁ Γ₂)
    (h : TY.HasType Γ₁ e1 A) (H : ParRedS TY Γ₁ e1 e2) : ParRedS TY Γ₂ e1 e2 := by
  induction H with
  | rfl => exact .rfl
  | tail h1 h2 ih => refine .tail ih (h2.defeqDFC W (hasType h1 h))

theorem ParRedS.app (hf : ParRedS TY Γ f f') (ha : ParRedS TY Γ a a') :
    ParRedS TY Γ (f.app a) (f'.app a') := by
  have : ParRedS TY Γ (f.app a) (f.app a') := by
    induction ha with
    | rfl => exact .rfl
    | tail a1 a2 iha => exact .tail iha (.app .rfl a2)
  refine this.trans ?_; clear this ha
  induction hf with
  | rfl =>  exact .rfl
  | tail f1 f2 ihf => exact .tail ihf (.app f2 .rfl)

theorem ParRedS.lam (hf : ParRedS TY Γ A A') (ha : ParRedS TY (A::Γ) body body') :
    ParRedS TY Γ (A.lam body) (A'.lam body') := by
  have : ParRedS TY Γ (A.lam body) (A.lam body') := by
    induction ha with
    | rfl => exact .rfl
    | tail a1 a2 iha => exact .tail iha (.lam .rfl a2)
  refine this.trans ?_; clear this ha
  induction hf with
  | rfl =>  exact .rfl
  | tail f1 f2 ihf => exact .tail ihf (.lam f2 .rfl)

theorem ParRedS.forallE (hf : ParRedS TY Γ A A') (ha : ParRedS TY (A::Γ) body body') :
    ParRedS TY Γ (A.forallE body) (A'.forallE body') := by
  have : ParRedS TY Γ (A.forallE body) (A.forallE body') := by
    induction ha with
    | rfl => exact .rfl
    | tail a1 a2 iha => exact .tail iha (.forallE .rfl a2)
  refine this.trans ?_; clear this ha
  induction hf with
  | rfl =>  exact .rfl
  | tail f1 f2 ihf => exact .tail ihf (.forallE f2 .rfl)

theorem ParRedS.inst (Ha : TY.HasType Γ a A)
    (hf : ParRedS TY (A :: Γ) f f') (ha : ParRedS TY Γ a a') :
    ParRedS TY Γ (f.inst a) (f'.inst a') := by
  have : ParRedS TY Γ (f.inst a) (f.inst a') := by
    induction ha with
    | rfl => exact .rfl
    | tail a1 a2 iha => exact .tail iha (.instN a2 (ParRedS.hasType a1 Ha) .zero .rfl)
  replace Ha := ha.hasType Ha
  refine this.trans ?_; clear this ha
  induction hf with
  | rfl =>  exact .rfl
  | tail _ h ihf => exact .tail ihf (.instN .rfl Ha .zero h)

theorem ParRedS.weakN (W : Ctx.LiftN n k Γ Γ') (H : ParRedS TY Γ e e') :
    ParRedS TY Γ' (e.liftN n k) (e'.liftN n k) := by
  induction H with
  | rfl =>  exact .rfl
  | tail _ h ih => exact .tail ih (.weakN W h)

inductive ParRedExt : Type where
  | base : ParRedExt
  | lift : ParRedExt → ParRedExt
  | app : ParRedExt → ParRedExt

def ParRedExt.depth : ParRedExt → Nat
  | .base => 0
  | .lift l
  | .app l => l.depth + 1

def ParRedExt.apply : ParRedExt → VExpr → VExpr
  | .base, e => e
  | .lift l, e => (l.apply e).lift
  | .app l, e => (l.apply e).lift.app (.bvar 0)

def ParRedExt.meas : ParRedExt → Nat
  | .base => 0
  | .lift l => l.meas + 1
  | .app l => l.meas + 2

def IsApp := fun | VExpr.app .. => True | _ => False

theorem ParRedExt.isApp {l : ParRedExt} (H : l.apply (.app f a) = e') : IsApp e' := by
  induction l generalizing e' with simp [apply] at H
  | lift l ih =>
    specialize ih rfl; unfold IsApp at ih; split at ih <;> cases ih <;>
    · rename_i h1; cases h1 ▸ H; trivial
  | _ => subst H; trivial

theorem hasType_app_bvar0
    (H : TY.HasType (A :: Γ) (e.lift.app (bvar 0)) B) :
    ∃ B', TY.HasType Γ e (.forallE A B') := by
  have ⟨_, _, c1, c2⟩ := TY.app_inv H
  replace c1 :=
    have ⟨_, d1⟩ := TY.is_type c1
    have ⟨_, _, d2, d3⟩ := TY.forallE_inv d1
    have := TY.forallEDF d2 (TY.uniq c2 (TY.bvar .zero)) d3 (TY.refl d3)
    TY.defeq_r this c1
  have : A.lift.lam (e.lift.lift.app (bvar 0)) =
      (A.lam (e.lift.app (bvar 0))).lift := by
    simp [VExpr.liftN, liftN'_liftN_lo, liftN_liftN]
  have := (TY.isDefEqU_weakN_iff .one).1 (this ▸ TY.eta c1)
  have ⟨_, f1⟩ := TY.has_type this
  have ⟨_, _, f2, f3⟩ := TY.lam_inv f1
  exact ⟨_, TY.defeq_l this (TY.lam f2 f3)⟩

theorem ParRedExt.parRed_beta :
  NormalEq TY Γ f (lam A e') → ∀ {a B}, TY.HasType Γ (f.app a) B →
    ∃ e, ParRedS TY Γ (f.app a) e ∧ NormalEq TY Γ e (e'.inst a) := by
  refine (?_ : _ ∧ ∀ (l : ParRedExt), l.depth ≤ Γ.length →
    NormalEq TY Γ f (l.apply ((lam A e').lift.app (bvar 0))) →
    ∃ e, ParRedS TY Γ f e ∧ NormalEq TY Γ e (l.apply e')).1
  induction f using VExpr.brecOn generalizing Γ A e' with | _ f f_ih => ?_
  revert f_ih; change let motive := ?_; ∀ _: f.below (motive := motive), _; intro motive f_ih
  refine ⟨fun h1 a B h2 => ?_, fun l W h1 => ?_⟩
  · cases h1 with
    | @refl _ _ B H =>
      clear f_ih motive
      exact have h := .beta .rfl .rfl; ⟨_, .tail .rfl h, .refl (h.hasType h2)⟩
    | lamDF a1 a2 a3 a4 =>
      have ⟨_, _, H1, H2⟩ := TY.app_inv h2
      have ⟨_, _, H3, H4⟩ := TY.lam_inv H1
      have ⟨u1, u2⟩ := TY.forallE_defInv (TY.uniq (TY.lam H3 H4) H1)
      exact ⟨_, .tail .rfl <| .beta .rfl .rfl,
        .instN (TY.defeq_r (TY.trans (TY.symm u1) a2) H2) .zero a4⟩
    | @etaL _ _ A' _ _ a1 a2 =>
      have ⟨_, _, c1, c2⟩ := TY.lam_inv a1
      have ⟨_, d1, d2⟩ := f_ih.2.1.2 .base (Nat.zero_le _) a2
      have ⟨_, _, c3, c4⟩ := TY.app_inv h2
      have ⟨_, _, c1, c2⟩ := TY.lam_inv c3
      have ⟨u1, u2⟩ := TY.forallE_defInv (TY.uniq (TY.lam c1 c2) c3)
      exact ⟨_, .tail (ParRedS.app (.lam .rfl d1) .rfl) <| .beta .rfl .rfl,
        .instN (TY.defeq_r (TY.symm u1) c4) .zero d2⟩
    | etaR a1 a2 =>
      have ⟨_, _, H1, H2⟩ := TY.app_inv h2
      have ⟨u1, u2⟩ := TY.forallE_defInv (TY.uniq H1 a1)
      have := a2.instN (TY.defeq_r u1 H2) .zero
      simp [inst, inst_lift] at this
      exact ⟨_, .rfl, this⟩
    | proofIrrel a1 a2 a3 =>
      have ⟨_, _, H1, H2⟩ := TY.app_inv h2
      have hf := TY.uniq a2 H1; have := TY.defeq_l hf a1
      have ⟨_, _, b1, b2⟩ := TY.forallE_inv this
      have := TY.univ_defInv (TY.uniq (TY.forallE b1 b2) this)
      have b3 := let ⟨_, h⟩ := TY.is_type b2; TY.sort_inv h
      have b2 := TY.defeq_r (TY.sortDF b3 (by trivial) (VLevel.imax_eq_zero.1 this)) b2
      have ⟨_, _, c1, c2⟩ := TY.lam_inv a3
      have ⟨u1, u2⟩ := TY.forallE_defInv (TY.trans (TY.uniq (TY.lam c1 c2) a3) hf)
      exact ⟨_, .rfl, .proofIrrel (TY.isDefEq_instN .zero b2 H2) (TY.app H1 H2)
        (TY.isDefEq_instN .zero (TY.defeq_r u2 c2) (TY.defeq_r (TY.symm u1) H2))⟩
  generalize eq : l.apply .. = s at h1
  cases h1 with
  | @refl _ _ B H =>
    subst eq; clear f_ih motive
    generalize ls : l.meas = n
    induction n using Nat.strongRecOn generalizing l Γ B with | _ _ ih; subst ls
    cases l with
    | base =>
      refine have h := .beta .rfl .rfl; ⟨_, .tail .rfl h, ?_⟩
      simp [instN_bvar0] at h ⊢; exact .refl (h.hasType H)
    | lift l =>
      let A::Γ := Γ
      have ⟨_, a1⟩ := TY.isDefEq_weakN_inv .one H
      have ⟨_, a2, a3⟩ := ih _ (by simp [meas]) l (by simpa [depth] using W) a1 rfl
      exact ⟨_, .weakN .one a2, .weakN .one a3⟩
    | app l =>
      let A::Γ := Γ
      have ⟨_, _, H1, H2⟩ := TY.app_inv H
      have ⟨_, a1, a2⟩ := ih _ (by simp [meas]) (lift l) W H1 rfl
      have := a1.hasType H1
      refine ⟨_, .app a1 .rfl, .appDF this (TY.defeq_l a2.defeq this) H2 H2 a2 (.refl H2)⟩
  | @appDF _ _ A' B' f' _ a' a1 a2 a3 a4 a5 a6 =>
    obtain ⟨n, rfl, ⟨rfl, h⟩ | ⟨l', W', rfl, h⟩⟩ : ∃ n, a' = bvar n ∧
        (f' = (A.lam e').liftN (n+1) ∧ l.apply e' = liftN n e' ∨
        ∃ l', l'.depth ≤ l.depth ∧
          f' = apply l' ((A.lam e').lift.app (bvar 0)) ∧
          l.apply e' = (l'.apply e').app (bvar n)) := by
      clear W a2 a4 a5 a6
      induction l generalizing f' a' with
      | base => cases eq; exact ⟨_, rfl, .inl ⟨rfl, by simp [apply]⟩⟩
      | lift l ih =>
        simp [apply] at eq
        generalize eq' : apply .. = s at eq; cases s <;> cases eq
        obtain ⟨n, rfl, ⟨rfl, h⟩ | ⟨l', W', rfl, h⟩⟩ := ih eq'
        · refine ⟨_, rfl, .inl ⟨by simp [liftN_liftN], ?_⟩⟩
          have := congrArg VExpr.lift h
          simpa [lift_inst_hi, liftN'_liftN']
        · exact ⟨_, rfl, .inr ⟨lift _, Nat.succ_le_succ W', rfl, congrArg VExpr.lift h⟩⟩
      | app l ih => cases eq; exact ⟨_, rfl, .inr ⟨lift _, Nat.le_refl _, rfl, rfl⟩⟩
    · have ⟨_, _, c1, c2⟩ := TY.lam_inv (TY.defeq_l a5.defeq a1)
      have ⟨u1, u2⟩ := TY.forallE_defInv (TY.uniq (TY.defeq_l a5.defeq a1) (TY.lam c1 c2))
      have ⟨_, b1, b2⟩ := f_ih.1.1.1 a5 (TY.app a1 a3)
      replace b2 := b2.trans (.instN_r (TY.defeq_r u1 a3) a6 .zero c2)
      have := congrArg (liftN n) (instN_bvar0 e' 0)
      simp [liftN_inst_hi, liftN'_liftN', liftN] at this
      rw [Nat.add_comm, this, ← h] at b2
      exact ⟨_, b1, b2⟩
    · have ⟨_, b1, b2⟩ := f_ih.1.1.2 l' (Nat.le_trans W' W) a5
      rw [h]; have := b1.hasType a1
      exact ⟨_, .app b1 .rfl, .appDF this (TY.defeq_l b2.defeq this) a3 a4 b2 a6⟩
  | @etaL _ _ A' _ _ a1 a2 =>
    subst eq
    have ⟨_, b1, b2⟩ := f_ih.2.1.2 (app l) (by exact Nat.succ_le_succ W) a2
    have ⟨_, c1⟩ := TY.has_type b2.symm.defeq
    let ⟨_, b3⟩ := hasType_app_bvar0 c1
    exact ⟨_, .lam .rfl b1, .etaL b3 b2⟩
  | @proofIrrel _ p _ _ a1 a2 a3 =>
    subst eq; refine ⟨_, .rfl, .proofIrrel a1 a2 ?_⟩
    clear a2; induction l generalizing Γ p with
    | base =>
      have ⟨_, _, b1, b2⟩ := TY.app_inv a3
      have ⟨_, _, b3, b4⟩ := TY.lam_inv b1
      have ⟨u1, u2⟩ := TY.forallE_defInv (TY.uniq (TY.lam b3 b4) b1)
      have := TY.beta b4 (TY.defeq_r (TY.symm u1) b2)
      simp [instN_bvar0] at this
      exact TY.defeq_l this a3
    | lift l ih =>
      let A::Γ := Γ
      have ⟨_, b1⟩ := TY.isDefEq_weakN_inv .one a3
      have u1 := TY.uniq a3 ((TY.isDefEq_weakN_iff .one).2 b1)
      have := (TY.isDefEq_weakN_iff (A := sort _) .one).1 (TY.defeq_l u1 a1)
      have := ih (Nat.le_of_succ_le_succ W) this b1
      exact TY.defeq_r (TY.symm u1) ((TY.isDefEq_weakN_iff .one).2 this)
    | app l ih =>
      let A::Γ := Γ
      let ⟨_, b1⟩ := hasType_app_bvar0 a3
      have H := TY.uniq a3 (TY.app ((TY.isDefEq_weakN_iff .one).2 b1) (TY.bvar .zero))
      simp [instN_bvar0] at H
      have ⟨_, _, b2, b3⟩ := have ⟨_, b2⟩ := TY.is_type b1; TY.forallE_inv b2
      have wf := let ⟨_, h⟩ := TY.is_type b2; TY.sort_inv h
      have := TY.forallE b2 (TY.defeq_l H a1)
      have := TY.defeq_r (TY.sortDF (by exact ⟨wf, ⟨⟩⟩) (by trivial) VLevel.imax_zero) this
      have := ih (Nat.le_of_succ_le_succ W) this b1
      have := TY.app ((TY.isDefEq_weakN_iff .one).2 this) (TY.bvar .zero)
      simp [instN_bvar0] at this
      exact TY.defeq_r (TY.symm H) this
  | _ => cases l.isApp eq

theorem NormalEq.parRed (H1 : NormalEq TY Γ e₁ e₂) (H2 : ParRed TY Γ e₂ e₂') :
    ∃ e₁', ParRedS TY Γ e₁ e₁' ∧ NormalEq TY Γ e₁' e₂' := by
  induction H1 generalizing e₂' with
  | refl l1 => exact ⟨_, .tail .rfl H2, .refl (H2.hasType l1)⟩
  | sortDF l1 l2 l3 =>
    cases H2 with
    | sort => exact ⟨_, .tail .rfl .sort, .sortDF l1 l2 l3⟩
    | extra r1 r2 => cases r2
  | constDF l1 l2 l3 l4 l5 =>
    cases H2 with
    | const => exact ⟨_, .tail .rfl .const, .constDF l1 l2 l3 l4 l5⟩
    | extra r1 r2 r3 r4 =>
      sorry
  | @appDF Γ f A B f₂ a b l1 l2 l3 l4 l5 l6 ih1 ih2 =>
    cases H2 with
    | app r1 r2 =>
      let ⟨_, a1, a2⟩ := ih1 r1
      let ⟨_, b1, b2⟩ := ih2 r2
      exact ⟨_, .app a1 b1,
        .appDF (a1.hasType l1) (r1.hasType l2) (b1.hasType l3) (r2.hasType l4) a2 b2⟩
    | @beta A _ e e' _ b' r1 r2 =>
      let ⟨f', a1, a2⟩ := ih1 (.lam .rfl r1)
      let ⟨a', b1, b2⟩ := ih2 r2
      let ⟨_, _, d1, d2⟩ := TY.lam_inv l2
      let ⟨u1, u2⟩ := TY.forallE_defInv (TY.uniq (TY.lam d1 d2) l2)
      replace d2 := r1.hasType (TY.defeq_r u2 d2)
      replace l3 := b1.hasType (TY.defeq_r (TY.symm u1) l3)
      let ⟨_, h1, h2⟩ := ParRedExt.parRed_beta a2
        (TY.app (TY.defeq_l a2.symm.defeq (TY.lam d1 d2)) l3)
      exact ⟨_, .trans (a1.app b1) h1, h2.trans (.instN_r l3 b2 .zero d2)⟩
    | extra r1 r2 r3 r4 =>
      sorry
  | lamDF l1 l2 l3 l4 ih1 =>
    cases H2 with
    | lam r1 r2 =>
      have ⟨_, h1⟩ := TY.has_type l4.defeq
      have h2 := TY.defeq_l l4.defeq h1
      replace r2 := r2.defeqDFC (.succ .zero l3) <| TY.isDefEq_DFC (.succ .zero (TY.symm l3)) h2
      let ⟨_, b1, b2⟩ := ih1 r2
      exact ⟨_, .lam .rfl (b1.defeqDFC (.succ .zero (TY.symm l2)) h1),
        .lamDF l1 l2 (TY.trans (TY.symm (r1.defeq (TY.defeq_l (TY.symm l3) l1))) l3) b2⟩
    | extra _ r2 => cases r2
  | forallEDF l1 l2 l3 l4 l5 ih1 ih2 =>
    cases H2 with
    | forallE r1 r2 =>
      let ⟨_, a1, a2⟩ := ih1 r1
      have h2 := TY.defeq_l l5.defeq l4
      have W := TY.trans l3.symm.defeq l2
      replace r2 := r2.defeqDFC (.succ .zero W) <| TY.isDefEq_DFC (.succ .zero (TY.symm W)) h2
      let ⟨_, b1, b2⟩ := ih2 r2
      have := r1.defeq (TY.defeq_l (TY.symm W) l1)
      exact ⟨_, .forallE a1 (b1.defeqDFC (.succ .zero (TY.symm l2)) l4),
        .forallEDF l1 (TY.trans a2.defeq <| TY.trans (TY.symm this) W) a2 (b1.hasType l4) b2⟩
    | extra _ r2 => cases r2
  | etaL l1 l2 ih1 =>
    let ⟨_, a1, a2⟩ := ih1 (.app (.weakN .one H2) .bvar)
    exact ⟨_, .lam .rfl a1, .etaL (H2.hasType l1) a2⟩
  | @etaR Γ e A _ _ l1 l2 ih1 =>
    cases H2 with
    | lam r1 r2 =>
      let ⟨t, a1, a2⟩ := ih1 r2
      have ⟨_, c1⟩ := TY.is_type l1
      have ⟨_, _, c1, c2⟩ := TY.forallE_inv c1
      suffices
          (∃ A', ParRedS TY Γ e (A'.lam t) ∧ TY.IsDefEqU Γ A' A) ∨
          (∃ e', ParRedS TY Γ e e' ∧ t = .app (.lift e') (.bvar 0)) by
        obtain ⟨_, h1, h2⟩ | ⟨_, h, rfl⟩ := this
        · exact ⟨_, h1, .lamDF c1 h2 (TY.symm (r1.defeq c1)) a2⟩
        · have := a2.etaR (h.hasType l1)
          have ⟨_, a3⟩ := TY.has_type a2.symm.defeq
          exact ⟨_, h, this.trans (.lamDF c1 (TY.refl c1) (TY.symm (r1.defeq c1)) (.refl a3))⟩
      generalize eq : e.lift.app (.bvar 0) = e' at a1
      clear l2 ih1 a2
      induction a1 generalizing e with subst eq
      | rfl => exact .inr ⟨_, .rfl, rfl⟩ | tail _ a1 ih
      obtain ⟨_, h1, h2⟩ | ⟨e', h, rfl⟩ := ih l1 rfl
      · have ⟨_, _, d1, d2⟩ := TY.lam_inv (h1.hasType l1)
        exact .inl ⟨_, h1.tail <| .lam .rfl (a1.defeqDFC (.succ .zero (TY.symm h2))
          (TY.isDefEq_DFC (.succ .zero h2) d2)), h2⟩
      generalize eq : e'.lift = e1 at a1
      cases a1 with
      | app b1 b2 =>
        cases b2 with | bvar => ?_ | extra _ h => cases h
        cases eq; obtain ⟨_, b1', rfl⟩ := b1.weakN_inv .one
        exact .inr ⟨_, .tail h b1', rfl⟩
      | beta b1 b2 =>
        cases b2 with | bvar => ?_ | extra _ h => cases h
        cases e' <;> cases eq
        obtain ⟨_, b1', rfl⟩ := b1.weakN_inv (.succ .one)
        rw [instN_bvar0]
        have l1' := h.hasType l1
        have ⟨_, _, d1, d2⟩ := TY.lam_inv l1'
        have ⟨u1, u2⟩ := TY.forallE_defInv (TY.uniq (TY.lam d1 d2) l1')
        exact .inl ⟨_, .tail h <| .lam .rfl b1', u1⟩
      | extra b1 b2 b3 b4 =>
        cases b2 with | app _ h => cases h | var => cases TY.pat_not_var b1
    | extra _ r2 => cases r2
  | proofIrrel l1 l2 l3 => exact ⟨_, .rfl, .proofIrrel l1 l2 (H2.hasType l3)⟩

theorem NormalEq.parRedS (H1 : NormalEq TY Γ e₁ e₂) (H2 : ParRedS TY Γ e₂ e₂') :
    ∃ e₁', ParRedS TY Γ e₁ e₁' ∧ NormalEq TY Γ e₁' e₂' := by
  induction H2 with
  | rfl => exact ⟨_, .rfl, H1⟩
  | tail h1 h2 ih =>
    let ⟨_, a1, a2⟩ := ih
    let ⟨_, b1, b2⟩ := a2.parRed h2
    exact ⟨_, .trans a1 b1, b2⟩

def Typing.CRDefEq (Γ : List VExpr) (e₁ e₂ : VExpr) : Prop :=
  (∃ A, TY.HasType Γ e₁ A) ∧ (∃ A, TY.HasType Γ e₂ A) ∧
  ∃ e₁' e₂', ParRedS TY Γ e₁ e₁' ∧ ParRedS TY Γ e₂ e₂' ∧ NormalEq TY Γ e₁' e₂'

theorem ParRedS.church_rosser  (H : TY.HasType Γ e A)
    (H1 : ParRedS TY Γ e e₁) (H2 : ParRedS TY Γ e e₂) : TY.CRDefEq Γ e₁ e₂ := by
  refine ⟨⟨_, H1.hasType H⟩, ⟨_, H2.hasType H⟩, ?_⟩
  induction H2 with
  | rfl => exact ⟨_, _, .rfl, H1, .refl (H1.hasType H)⟩
  | @tail b c h1 H2 ih =>
    replace H := ParRedS.hasType h1 H
    have ⟨_, A2, a1, a2, a3⟩ := ih
    have ⟨_, _, b1, b2, b3⟩ :
        ∃ e₁' e₂', ParRed TY Γ A2 e₁' ∧ ParRedS TY Γ c e₂' ∧ NormalEq TY Γ e₁' e₂' := by
      clear a3; induction a2 with
      | rfl => exact ⟨_, _, H2, .rfl, .refl (H2.hasType H)⟩
      | tail h1 h2 ih =>
        have ⟨_, _, a1, a2, a3⟩ := ih
        have ⟨_, _, b1, b2, b3⟩ := a1.church_rosser (ParRedS.hasType h1 H) h2
        have ⟨_, c1, c2⟩ := a3.symm.parRed b1
        exact ⟨_, _, b2, .trans a2 c1, (c2.trans b3).symm⟩
    have ⟨_, c1, c2⟩ := a3.parRed b1
    exact ⟨_, _, .trans a1 c1, b2, c2.trans b3⟩

theorem Typing.CRDefEq.normalEq (H : NormalEq TY Γ e₁ e₂) : TY.CRDefEq Γ e₁ e₂ :=
  ⟨TY.has_type H.defeq, TY.has_type H.symm.defeq, _, _, .rfl, .rfl, H⟩

theorem Typing.CRDefEq.refl (H : TY.HasType Γ e A) : TY.CRDefEq Γ e e :=
  .normalEq (.refl H)

theorem Typing.CRDefEq.defeq : TY.CRDefEq Γ e₁ e₂ → TY.IsDefEqU Γ e₁ e₂
  | ⟨⟨_, h1⟩, ⟨_, h2⟩, _, _, h3, h4, h5⟩ =>
    TY.trans (h3.defeq h1) <| TY.trans h5.defeq (TY.symm (h4.defeq h2))

theorem Typing.CRDefEq.symm : TY.CRDefEq Γ e₁ e₂ → TY.CRDefEq Γ e₂ e₁
  | ⟨h1, h2, _, _, h3, h4, h5⟩ => ⟨h2, h1, _, _, h4, h3, h5.symm⟩

theorem Typing.CRDefEq.trans : TY.CRDefEq Γ e₁ e₂ → TY.CRDefEq Γ e₂ e₃ → TY.CRDefEq Γ e₁ e₃
  | ⟨l1, ⟨_, l2⟩, _, _, l3, l4, l5⟩, ⟨_, r2, _, _, r3, r4, r5⟩ => by
    let ⟨_, _, _, _, m1, m2, m3⟩ := l4.church_rosser l2 r3
    let ⟨_, a1, a2⟩ := l5.parRedS m1
    let ⟨_, b1, b2⟩ := r5.symm.parRedS m2
    exact ⟨l1, r2, _, _, .trans l3 a1, .trans r4 b1, a2.trans <| m3.trans b2.symm⟩

theorem VEnv.IsDefEq.toTyping (H : TY.env.IsDefEq TY.univs Γ e₁ e₂ A) :
    TY.IsDefEqU Γ e₁ e₂ ∧ TY.HasType Γ e₁ A := by
  induction H with
  | bvar h => exact ⟨TY.refl (TY.bvar h), TY.bvar h⟩
  | symm _ ih => exact ⟨TY.symm ih.1, TY.defeq_l ih.1 ih.2⟩
  | trans _ _ ih1 ih2 => exact ⟨TY.trans ih1.1 ih2.1, ih1.2⟩
  | sortDF h1 h2 h3 => exact ⟨TY.sortDF h1 h2 h3, TY.sort h1⟩
  | constDF h1 h2 h3 h4 h5 => exact ⟨TY.constDF h1 h2 h3 h4 h5, TY.const h1 h2 h4⟩
  | appDF h1 h2 ih1 ih2 => exact ⟨TY.appDF ih1.2 ih1.1 ih2.2 ih2.1, TY.app ih1.2 ih2.2⟩
  | lamDF h1 h2 ih1 ih2 => exact ⟨TY.lamDF ih1.2 ih1.1 ih2.1, TY.lam ih1.2 ih2.2⟩
  | forallEDF h1 h2 ih1 ih2 => exact ⟨TY.forallEDF ih1.2 ih1.1 ih2.2 ih2.1, TY.forallE ih1.2 ih2.2⟩
  | defeqDF h1 h2 ih1 ih2 => exact ⟨ih2.1, TY.defeq_r ih1.1 ih2.2⟩
  | beta h1 h2 ih1 ih2 =>
    have h := TY.beta ih1.2 ih2.2
    exact ⟨h, TY.defeq_l (TY.symm h) (TY.isDefEq_instN .zero ih1.2 ih2.2)⟩
  | eta h1 ih1 => have h := TY.eta ih1.2; exact ⟨h, TY.defeq_l (TY.symm h) ih1.2⟩
  | proofIrrel h1 h2 h3 ih1 ih2 ih3 => exact ⟨TY.proofIrrel ih1.2 ih2.2 ih3.2, ih2.2⟩
  | extra h1 h2 h3 => exact ⟨TY.extraDF h1 h2 h3, TY.extra h1 h2 h3⟩

theorem VEnv.IsDefEqU.church_rosser
    (H : TY.env.IsDefEq TY.univs Γ e₁ e₂ A) : TY.CRDefEq Γ e₁ e₂ := by
  have mk {Γ e₁ e₂ A e₁' e₂'} (H : TY.env.IsDefEq TY.univs Γ e₁ e₂ A)
      (h1 : ParRedS TY Γ e₁ e₁') (h2 : ParRedS TY Γ e₂ e₂') (h3 : NormalEq TY Γ e₁' e₂') :
      TY.CRDefEq Γ e₁ e₂ :=
    ⟨⟨_, H.toTyping.2⟩, ⟨_, H.symm.toTyping.2⟩, _, _, h1, h2, h3⟩
  induction H with
  | bvar h => exact .refl (TY.bvar h)
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | sortDF h1 h2 h3 => exact .normalEq (.sortDF h1 h2 h3)
  | constDF h1 h2 h3 h4 h5 => exact .normalEq (.constDF h1 h2 h3 h4 h5)
  | appDF h1 h2 ih1 ih2 =>
    obtain ⟨-, -, _, _, a1, a2, a3⟩ := ih1
    obtain ⟨-, -, _, _, b1, b2, b3⟩ := ih2
    have c1 := h1.toTyping; have c2 := h2.toTyping
    exact mk (.appDF h1 h2) (.app a1 b1) (.app a2 b2) <|
      .appDF (a1.hasType c1.2) (a2.hasType h1.symm.toTyping.2)
        (b1.hasType c2.2) (b2.hasType h2.symm.toTyping.2) a3 b3
  | lamDF h1 h2 ih1 ih2 =>
    obtain ⟨-, -, _, _, a1, a2, a3⟩ := ih1
    obtain ⟨-, -, _, _, b1, b2, b3⟩ := ih2
    have c1 := h1.toTyping; have c2 := h2.toTyping
    have b2' := b2.defeqDFC (.succ .zero c1.1) h2.symm.toTyping.2
    have := TY.symm (a1.defeq c1.2)
    exact mk (.lamDF h1 h2) (.lam a1 b1) (.lam a2 b2') <|
      .lamDF c1.2 this (TY.trans (TY.symm a3.defeq) this) b3
  | forallEDF h1 h2 ih1 ih2 =>
    obtain ⟨-, -, _, _, a1, a2, a3⟩ := ih1
    obtain ⟨-, -, _, _, b1, b2, b3⟩ := ih2
    have c1 := h1.toTyping; have c2 := h2.toTyping
    have b2' := b2.defeqDFC (.succ .zero c1.1) h2.symm.toTyping.2
    exact mk (.forallEDF h1 h2) (.forallE a1 b1) (.forallE a2 b2') <|
      .forallEDF c1.2 (TY.symm (a1.defeq c1.2)) a3 (b1.hasType c2.2) b3
  | defeqDF _ _ _ ih2 => exact ih2
  | beta h1 h2 ih1 ih2 =>
    refine have h := .beta h1 h2; mk h (.tail .rfl (.beta .rfl .rfl)) .rfl ?_
    exact .refl h.hasType.2.toTyping.2
  | eta h1 ih1 =>
    have := h1.toTyping.2
    exact .normalEq <| .etaL this <| .refl <|
      TY.app ((TY.isDefEq_weakN_iff .one).2 this) (TY.bvar .zero)
  | proofIrrel h1 h2 h3 ih1 ih2 ih3 =>
    exact .normalEq <| .proofIrrel h1.toTyping.2 h2.toTyping.2 h3.toTyping.2
  | @extra _ _ Γ h1 h2 h3 =>
    have ⟨_, _, _, _, a1, a2, a3, a4⟩ := TY.extra_pat h1 h2 h3 (Γ := Γ)
    refine have h := .extra h1 h2 h3; mk h (.tail .rfl (.extra a1 a2 a3 fun _ => .rfl)) .rfl ?_
    exact a4 ▸ .refl h.symm.toTyping.2
