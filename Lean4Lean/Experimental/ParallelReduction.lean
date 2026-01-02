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
      have ⟨_, he⟩ := e_ih.1.2.2.1 he
      have ⟨_, ha⟩ := e_ih.2.1 ha
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
        have ⟨m2r, hr⟩ := ih2 _ H2 e_ih.2.2 _ _ hm2
        exact ⟨Sum.elim m2l m2r, Sum.rec hl hr⟩
      | var _ ih =>
        let .var hm1 := hp2
        have ⟨_, _, H1, H2⟩ := TY.app_inv H'
        have ⟨m2l, hl⟩ := ih _ H1 e_ih.1.2 _ _ hm1
        have ⟨e', hs⟩ := e_ih.2.1 H2
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
    have ⟨_, h2⟩ := e_ih.2.1 ha
    exact neut _ H e_ih fun hn => ⟨_, .app hn h1 h2⟩
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
    | extra h1 h2 h3 => cases hn.2 _ _ _ _ h1 h2 h3
  | app hn _ _ ih1 ih2 =>
    have ⟨_, _, l1, l2⟩ := TY.app_inv H1
    obtain ⟨⟨hl, e_ih1 : VExpr.below ..⟩, ⟨hr, e_ih2 : VExpr.below ..⟩⟩ := id e_ih
    cases H with
    | app r1 r2 =>
      let ⟨_, p1, n1⟩ := ih1 l1 r1 e_ih1; let ⟨_, p2, n2⟩ := ih2 l2 r2 e_ih2
      have o1 := p1.hasType (r1.hasType l1); have o2 := p2.hasType (r2.hasType l2)
      exact ⟨_, .app p1 p2, .appDF o1 (TY.defeq_l n1.defeq o1) o2 (TY.defeq_l n2.defeq o2) n1 n2⟩
    | extra h1 h2 h3 => cases hn.2 _ _ _ _ h1 h2 h3
    | beta => cases hn.1 _ _ _ rfl
  | lam _ _ ih1 ih2 =>
    have ⟨_, _, l1, l2⟩ := TY.lam_inv H1
    obtain ⟨⟨hl, e_ih1 : VExpr.below ..⟩, ⟨hr, e_ih2 : VExpr.below ..⟩⟩ := e_ih
    cases H with
    | lam r1 r2 =>
      let ⟨_, p1, n1⟩ := ih1 l1 r1 e_ih1; let ⟨_, p2, n2⟩ := ih2 l2 r2 e_ih2
      exact ⟨_, .lam p1 (p2.defeqDFC (.succ .zero (r1.defeq l1)) (r2.hasType l2)),
        .lamDF l1 (TY.symm <| TY.trans (r1.defeq l1) (p1.defeq (r1.hasType l1))) n1 n2⟩
    | extra h1 h2 => cases h2
  | forallE _ _ ih1 ih2 =>
    have ⟨_, _, l1, l2⟩ := TY.forallE_inv H1
    obtain ⟨⟨hl, e_ih1 : VExpr.below ..⟩, ⟨hr, e_ih2 : VExpr.below ..⟩⟩ := e_ih
    cases H with
    | forallE r1 r2 =>
      let ⟨_, p1, n1⟩ := ih1 l1 r1 e_ih1; let ⟨_, p2, n2⟩ := ih2 l2 r2 e_ih2
      exact ⟨_, .forallE p1 (p2.defeqDFC (.succ .zero (r1.defeq l1)) (r2.hasType l2)),
        .forallEDF l1 (TY.symm <| TY.trans (r1.defeq l1) (p1.defeq (r1.hasType l1)))
          n1 (p2.hasType (r2.hasType l2)) n2⟩
    | extra h1 h2 => cases h2
  | beta l1 l2 ih1 ih2 =>
    have ⟨_, _, lf, la⟩ := TY.app_inv H1
    have ⟨_, _, lA, le⟩ := TY.lam_inv lf
    have hw := (TY.forallE_defInv (TY.uniq lf (TY.lam lA le))).1
    have la' := TY.defeq_r hw la
    obtain ⟨⟨-, ⟨hA, e_ih1 : VExpr.below ..⟩, ⟨he, e_ih2 : VExpr.below ..⟩⟩,
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
        TY.Pat p' r ∧ p'.Matches e₁ m1 m2 ∧ r.2.OK (TY.IsDefEq Γ) m1 m2 ∧
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
