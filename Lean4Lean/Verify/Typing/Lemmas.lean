import Lean4Lean.Verify.Typing.Expr
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.UniqueTyping

namespace Lean4Lean
open VEnv Lean

theorem InScope.mono {P Q : FVarId → Prop} (H : ∀ fv, P fv → Q fv) :
    ∀ {e k}, InScope P e k → InScope Q e k
  | .bvar _, _, h | .sort .., _, h | .const .., _, h | .lit .., _, h => h
  | .fvar _, _, h => H _ h
  | .app .., _, ⟨h1, h2⟩
  | .lam .., _, ⟨h1, h2⟩
  | .forallE .., _, ⟨h1, h2⟩ => ⟨h1.mono H, h2.mono H⟩
  | .letE .., _, ⟨h1, h2, h3⟩ => ⟨h1.mono H, h2.mono H, h3.mono H⟩
  | .proj _ _ e, _, h | .mdata _ e, _, h => h.mono (e := e) H

theorem VLocalDecl.WF.hasType :
    ∀ {d}, VLocalDecl.WF env U Δ d → env.HasType U (VLCtx.toCtx ((ofv, d) :: Δ)) d.value d.type
  | .vlam _, _ => .bvar .zero
  | .vlet .., hA => hA

theorem VLocalDecl.is_liftN {Δ : VLCtx} :
    ∀ {d}, Ctx.LiftN (VLocalDecl.depth d) 0 Δ.toCtx (VLCtx.toCtx ((ofv, d) :: Δ))
  | .vlam _ => .one
  | .vlet .. => .zero []

variable (henv : Ordered env) in
theorem VLCtx.WF.find?_wf {Δ : VLCtx} (hΔ : VLCtx.WF env U Δ) (H : Δ.find? v = some (e, A)) :
    env.HasType U Δ.toCtx e A := by
  let (ofv, d') :: Δ := Δ
  unfold VLCtx.find? at H; split at H
  · cases H; exact hΔ.2.2.hasType
  · simp [bind, Option.bind_eq_some] at H
    obtain ⟨⟨d'', n'⟩, H, rfl, rfl⟩ := H
    obtain h3 := hΔ.1.find?_wf H
    exact h3.weakN henv VLocalDecl.is_liftN

theorem VLCtx.WF.toCtx : ∀ {Δ}, VLCtx.WF env U Δ → OnCtx Δ.toCtx (env.IsType U)
  | [], _ => ⟨⟩
  | (_, .vlam _) :: _, ⟨hΔ, _, hA⟩ => ⟨hΔ.toCtx, hA⟩
  | (_, .vlet ..) :: _, ⟨hΔ, _, _⟩ => hΔ.toCtx

variable (env : VEnv) (U : Nat) in
inductive VLCtx.IsDefEq : VLCtx → VLCtx → Prop
  | nil : VLCtx.IsDefEq [] []
  | vlam {Δ₁ Δ₂ : VLCtx} :
    VLCtx.IsDefEq Δ₁ Δ₂ →
    (do Δ₁.lookup (some (← ofv))) = none →
    env.IsDefEq U Δ₁.toCtx type₁ type₂ (.sort u) →
    VLCtx.IsDefEq ((ofv, .vlam type₁) :: Δ₁) ((ofv, .vlam type₂) :: Δ₂)
  | vlet {Δ₁ Δ₂ : VLCtx} :
    VLCtx.IsDefEq Δ₁ Δ₂ →
    (do Δ₁.lookup (some (← ofv))) = none →
    env.IsDefEq U Δ₁.toCtx value₁ value₂ type₁ →
    env.IsDefEq U Δ₁.toCtx type₁ type₂ (.sort u) →
    VLCtx.IsDefEq ((ofv, .vlet type₁ value₁) :: Δ₁) ((ofv, .vlet type₂ value₂) :: Δ₂)

variable (henv : Ordered env) in
theorem VLCtx.IsDefEq.refl : ∀ {Δ}, VLCtx.WF env U Δ → VLCtx.IsDefEq env U Δ Δ
  | [], _ => .nil
  | (_, .vlam ..) :: _, ⟨h1, h2, _, h3⟩ => .vlam (IsDefEq.refl h1) h2 h3
  | (_, .vlet ..) :: _, ⟨h1, h2, h3⟩ =>
    let ⟨_, h4⟩ := h3.isType henv h1.toCtx
    .vlet (IsDefEq.refl h1) h2 h3 h4

theorem VLCtx.IsDefEq.defeqCtx : VLCtx.IsDefEq env U Δ₁ Δ₂ → env.IsDefEqCtx U [] Δ₁.toCtx Δ₂.toCtx
  | .nil => .zero
  | .vlam h1 _ h3 => .succ h1.defeqCtx h3
  | .vlet h1 _ _ _ => h1.defeqCtx

theorem VLCtx.IsDefEq.lookup_eq_none :
    VLCtx.IsDefEq env U Δ₁ Δ₂ → (Δ₁.lookup fv = none ↔ Δ₂.lookup fv = none)
  | .nil => by simp
  | .vlam h1 _ _ | .vlet h1 _ _ _ => by simp [List.lookup]; split <;> simp [h1.lookup_eq_none]

theorem VLCtx.IsDefEq.find? :
    VLCtx.IsDefEq env U Δ₁ Δ₂ → (Δ₁.lookup fv = none ↔ Δ₂.lookup fv = none)
  | .nil => by simp
  | .vlam h1 _ _ | .vlet h1 _ _ _ => by simp [List.lookup]; split <;> simp [h1.lookup_eq_none]

theorem VLCtx.IsDefEq.bind_lookup_eq_none (H : VLCtx.IsDefEq env U Δ₁ Δ₂) :
    (do Δ₁.lookup (some (← ofv))) = none ↔ (do Δ₂.lookup (some (← ofv))) = none := by
  simp only [bind, Option.bind_eq_none]
  repeat rw [forall_comm, forall_comm (α := VLocalDecl)]; refine forall_congr' fun _ => ?_
  simp only [← Option.eq_none_iff_forall_not_mem, H.lookup_eq_none]

theorem VLCtx.IsDefEq.wf : VLCtx.IsDefEq env U Δ₁ Δ₂ → VLCtx.WF env U Δ₁
  | .nil => ⟨⟩
  | .vlam h1 h2 h3 => ⟨h1.wf, h2, _, h3.hasType.1⟩
  | .vlet h1 h2 h3 _ => ⟨h1.wf, h2, h3.hasType.1⟩

variable (henv : Ordered env) in
theorem VLCtx.IsDefEq.symm : VLCtx.IsDefEq env U Δ₁ Δ₂ → VLCtx.IsDefEq env U Δ₂ Δ₁
  | .nil => .nil
  | .vlam h1 h2 h3 =>
    .vlam h1.symm (by simpa [h1.bind_lookup_eq_none] using h2) (h3.symm.defeqDFC henv h1.defeqCtx)
  | .vlet h1 h2 h3 h4 =>
    .vlet h1.symm (by simpa [h1.bind_lookup_eq_none] using h2)
      (h4.defeqDF h3.symm |>.defeqDFC henv h1.defeqCtx) (h4.symm.defeqDFC henv h1.defeqCtx)

variable (henv : Ordered env) in
theorem VLCtx.IsDefEq.find?_uniq (hΔ : VLCtx.IsDefEq env U Δ₁ Δ₂)
    (H1 : Δ₁.find? v = some (e₁, A₁)) (H2 : Δ₂.find? v = some (e₂, A₂)) :
    env.IsDefEqU U Δ₁.toCtx A₁ A₂ ∧ env.IsDefEq U Δ₁.toCtx e₁ e₂ A₁ := by
  match hΔ with
  | .vlam (type₁ := A₁) (type₂ := A₂) hΔ h2 h3 =>
    revert H1 H2; unfold VLCtx.find?; split
    · rintro ⟨⟩ ⟨⟩; exact ⟨⟨_, h3.weak henv⟩, .bvar .zero⟩
    · simp [bind, Option.bind_eq_some]
      rintro ⟨d₁', n₁'⟩ H1' rfl rfl ⟨d₂', n₂'⟩ H2' rfl rfl
      obtain ⟨h2, h3⟩ := find?_uniq hΔ H1' H2'
      exact ⟨h2.weakN henv .one, h3.weak henv⟩
  | .vlet hΔ _ h3 h4 =>
    revert H1 H2; unfold VLCtx.find?; split
    · rintro ⟨⟩ ⟨⟩; exact ⟨⟨_, h4⟩, h3⟩
    · simp [bind, Option.bind_eq_some]
      rintro ⟨d₁', n₁'⟩ H1' rfl rfl ⟨d₂', n₂'⟩ H2' rfl rfl
      simpa [VLocalDecl.depth] using find?_uniq hΔ H1' H2'

theorem TrProj.wf (H1 : TrProj Δ s i e e') (H2 : VExpr.WF env U Γ e) : VExpr.WF env U Γ e' := sorry

variable (henv : Ordered env) {Us : List Name} (hΔ : VLCtx.WF env Us.length Δ) in
theorem TrExpr.wf (H : TrExpr env Us Δ e e') : VExpr.WF env Us.length Δ.toCtx e' := by
  induction H with
  | bvar h1 | fvar h1 => exact ⟨_, hΔ.find?_wf henv h1⟩
  | sort h1 => exact ⟨_, .sort (.of_ofLevel h1)⟩
  | const h1 h2 h3 =>
    simp [List.mapM_eq_some] at h2
    refine ⟨_, .const h1 (fun l hl => ?_) (h2.length_eq.symm.trans h3)⟩
    have ⟨_, _, h⟩ := h2.forall_exists_r _ hl; exact .of_ofLevel h
  | app h1 h2 => exact ⟨_, .app h1 h2⟩
  | lam h1 _ _ _ ih2 =>
    have ⟨_, h1'⟩ := h1
    have ⟨_, h2'⟩ := ih2 ⟨hΔ, rfl, h1⟩
    refine ⟨_, .lam h1' h2'⟩
  | forallE h1 h2 => have ⟨_, h1'⟩ := h1; have ⟨_, h2'⟩ := h2; exact ⟨_, .forallE h1' h2'⟩
  | letE h1 _ _ _ _ _ ih3 => exact ih3 ⟨hΔ, rfl, h1⟩
  | lit _ ih | mdata _ ih => exact ih hΔ
  | proj _ h2 ih => exact h2.wf (ih hΔ)

variable (henv : Ordered env) (hΔ : VLCtx.IsDefEq env U Δ₁ Δ₂) in
theorem TrProj.uniq (H1 : TrProj Δ₁ s i e₁ e₁') (H2 : TrProj Δ₂ s i e₂ e₂')
    (H : env.IsDefEqU U Δ₁.toCtx e₁ e₂) :
    env.IsDefEqU U Δ₁.toCtx e₁' e₂' := sorry

variable (henv : Ordered env) (Us : List Name) (hΔ : VLCtx.IsDefEq env Us.length Δ₁ Δ₂) in
theorem TrExpr.uniq (H1 : TrExpr env Us Δ₁ e e₁) (H2 : TrExpr env Us Δ₂ e e₂) :
    env.IsDefEqU Us.length Δ₁.toCtx e₁ e₂ := by
  induction H1 generalizing Δ₂ e₂ with
  | bvar l1 => let .bvar r1 := H2; exact ⟨_, (hΔ.find?_uniq henv l1 r1).2⟩
  | fvar l1 => let .fvar r1 := H2; exact ⟨_, (hΔ.find?_uniq henv l1 r1).2⟩
  | sort l1 => let .sort r1 := H2; cases l1.symm.trans r1; exact ⟨_, .sort (.of_ofLevel l1)⟩
  | const l1 l2 l3 =>
    let .const r1 r2 r3 := H2; cases l1.symm.trans r1; cases l2.symm.trans r2
    exact (TrExpr.const l1 l2 l3).wf henv hΔ.wf
  | app l1 l2 _ _ ih3 ih4 =>
    let .app _ _ r3 r4 := H2
    exact ⟨_, .appDF
      (ih3 hΔ r3 |>.of_l henv hΔ.wf.toCtx l1)
      (ih4 hΔ r4 |>.of_l henv hΔ.wf.toCtx l2)⟩
  | lam l1 _ _ ih2 ih3 =>
    let ⟨_, l1⟩ := l1; let .lam _ r2 r3 := H2
    have hA := ih2 hΔ r2 |>.of_l henv hΔ.wf.toCtx l1
    have ⟨_, hb⟩ := ih3 (hΔ.vlam rfl hA) r3
    exact ⟨_, .lamDF hA hb⟩
  | forallE l1 l2 _ _ ih3 ih4 =>
    let ⟨_, l1'⟩ := l1; let ⟨_, l2⟩ := l2; let .forallE _ _ r3 r4 := H2
    have hA := ih3 hΔ r3 |>.of_l henv hΔ.wf.toCtx l1'
    have hB := ih4 (.vlam hΔ rfl hA) r4 |>.of_l (Γ := _::_) henv ⟨hΔ.wf.toCtx, l1⟩ l2
    exact ⟨_, .forallEDF hA hB⟩
  | letE l1 _ _ _ ih2 ih3 ih4 =>
    have hΓ := hΔ.wf.toCtx
    let .letE _ r2 r3 r4 := H2
    have ⟨_, hb⟩ := l1.isType henv hΓ
    exact ih4 (.vlet hΔ rfl (ih3 hΔ r3 |>.of_l henv hΓ l1) (ih2 hΔ r2 |>.of_l henv hΓ hb)) r4
  | lit _ ih1 => let .lit r1 := H2; exact ih1 hΔ r1
  | mdata _ ih1 => let .mdata r1 := H2; exact ih1 hΔ r1
  | proj _ l2 ih1 => let .proj r1 r2 := H2; exact l2.uniq r2 (ih1 hΔ r1)
