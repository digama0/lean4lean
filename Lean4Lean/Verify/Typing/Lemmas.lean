import Batteries.Data.String.Lemmas
import Lean4Lean.Verify.Typing.Expr
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.UniqueTyping

namespace Lean4Lean
open VEnv Lean
open scoped List

theorem InScope.mp (H : ∀ fv, P fv → Q fv → R fv) :
    ∀ {e}, InScope P e k → InScope Q e k → InScope R e k
  | .bvar _, l, _ | .sort .., l, _ | .const .., l, _ | .lit .., l, _ => l
  | .fvar _, l, r => H _ l r
  | .app .., ⟨l1, l2⟩, ⟨r1, r2⟩
  | .lam .., ⟨l1, l2⟩, ⟨r1, r2⟩
  | .forallE .., ⟨l1, l2⟩, ⟨r1, r2⟩ => ⟨l1.mp H r1, l2.mp H r2⟩
  | .letE .., ⟨l1, l2, l3⟩, ⟨r1, r2, r3⟩ => ⟨l1.mp H r1, l2.mp H r2, l3.mp H r3⟩
  | .proj _ _ e, l, r | .mdata _ e, l, r => l.mp (e := e) H r

theorem InScope.mono (H : ∀ fv, P fv → Q fv) (h : InScope P e k) : InScope Q e k :=
  h.mp (fun _ h _ => H _ h) h

theorem InScope.mono_r (H : k ≤ k') : ∀ {e}, InScope P e k → InScope P e k'
  | .bvar _, h => Nat.lt_of_lt_of_le h H
  | .fvar _, h | .sort .., h | .const .., h | .lit .., h => h
  | .app .., ⟨h1, h2⟩ => ⟨h1.mono_r H, h2.mono_r H⟩
  | .lam .., ⟨h1, h2⟩
  | .forallE .., ⟨h1, h2⟩ => ⟨h1.mono_r H, h2.mono_r (Nat.succ_le_succ H)⟩
  | .letE .., ⟨h1, h2, h3⟩ => ⟨h1.mono_r H, h2.mono_r H, h3.mono_r (Nat.succ_le_succ H)⟩
  | .proj _ _ e, h | .mdata _ e, h => h.mono_r (e := e) H

theorem InScope.mix : ∀ {e}, InScope P e k → InScope Q e k' → InScope P e k'
  | .bvar _, _, l | .sort .., l, _ | .const .., l, _ | .lit .., l, _ => l
  | .fvar _, l, _ => l
  | .app .., ⟨l1, l2⟩, ⟨r1, r2⟩
  | .lam .., ⟨l1, l2⟩, ⟨r1, r2⟩
  | .forallE .., ⟨l1, l2⟩, ⟨r1, r2⟩ => ⟨l1.mix r1, l2.mix r2⟩
  | .letE .., ⟨l1, l2, l3⟩, ⟨r1, r2, r3⟩ => ⟨l1.mix r1, l2.mix r2, l3.mix r3⟩
  | .proj _ _ e, l, r | .mdata _ e, l, r => l.mix (e := e) r

theorem InScope.natLitToConstructor : InScope P (.natLitToConstructor n) k := by
  cases n <;> simp [InScope]

theorem InScope.strLitToConstructor : InScope P (.strLitToConstructor s) k := by
  simp [InScope, String.foldr_eq]; induction s.data <;> simp [*, InScope]

theorem InScope.toConstructor : ∀ {l : Literal}, InScope P l.toConstructor k
  | .natVal _ => .natLitToConstructor
  | .strVal _ => .strLitToConstructor

theorem InScope.fvars_cons :
    InScope (· ∈ VLCtx.fvars Δ) e k → InScope (· ∈ VLCtx.fvars ((ofv, d) :: Δ)) e k :=
  InScope.mono fun a h => by cases ofv <;> simp [h]

theorem VLocalDecl.WF.hasType : ∀ {d}, VLocalDecl.WF env U (VLCtx.toCtx Δ) d →
    env.HasType U (VLCtx.toCtx ((ofv, d) :: Δ)) d.value d.type
  | .vlam _, _ => .bvar .zero
  | .vlet .., hA => hA

theorem VLocalDecl.is_liftN {Δ : VLCtx} :
    ∀ {d}, Ctx.LiftN (VLocalDecl.depth d) 0 Δ.toCtx (VLCtx.toCtx ((ofv, d) :: Δ))
  | .vlam _ => .one
  | .vlet .. => .zero []

variable (env : VEnv) (U : Nat) (Γ : List VExpr) in
inductive VLocalDecl.IsDefEq : VLocalDecl → VLocalDecl → Prop
  | vlam : env.IsDefEq U Γ type₁ type₂ (.sort u) → VLocalDecl.IsDefEq (.vlam type₁) (.vlam type₂)
  | vlet :
    env.IsDefEq U Γ value₁ value₂ type₁ → env.IsDefEq U Γ type₁ type₂ (.sort u) →
    VLocalDecl.IsDefEq (.vlet type₁ value₁) (.vlet type₂ value₂)

variable (henv : Ordered env) (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.LiftN n k Γ Γ') in
theorem VLocalDecl.weakN_iff : VLocalDecl.WF env U Γ' (d.liftN n k) ↔ VLocalDecl.WF env U Γ d :=
  match d with
  | .vlam .. => IsType.weakN_iff henv hΓ' W
  | .vlet .. => HasType.weakN_iff henv hΓ' W

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

theorem VLCtx.WF.fvars_nodup : ∀ {Δ}, VLCtx.WF env U Δ → Δ.fvars.Nodup
  | [], _ => .nil
  | (none, _) :: Δ, ⟨hΔ, _, _⟩ => fvars_nodup (Δ := Δ) hΔ
  | (some fv, _) :: Δ, ⟨hΔ,  h, _⟩ => by
    suffices fv ∉ fvars Δ from (fvars_nodup hΔ).cons (fun _ h e => this (e ▸ h))
    simpa using h

namespace VLCtx

inductive LiftN : VLCtx → VLCtx → Nat → Nat → Nat → Prop
  | refl : LiftN Δ Δ 0 0 0
  | skip_fvar (fv d) : LiftN Δ Δ' 0 n 0 → LiftN Δ ((some fv, d) :: Δ') 0 (n + d.depth) 0
  | cons_bvar (d) : LiftN Δ Δ' dk n k →
    LiftN ((none, d) :: Δ) ((none, d.liftN n k) :: Δ') (dk + 1) n (k + d.depth)

theorem LiftN.toCtx (W : LiftN Δ Δ' dk n k) : Ctx.LiftN n k Δ.toCtx Δ'.toCtx := by
  induction W with
  | refl => exact .zero []
  | @skip_fvar _ Δ' _ _ d _ ih =>
    match d with
    | .vlet .. => exact ih
    | .vlam A =>
      generalize hΓ' : VLCtx.toCtx Δ' = Γ' at ih
      let .zero As eq := ih
      simp [VLCtx.toCtx, hΓ']
      exact .zero (A :: As) (eq ▸ rfl)
  | cons_bvar d _ ih =>
    match d with
    | .vlet .. => exact ih
    | .vlam A => exact .succ ih

variable (henv : Ordered env) in
theorem LiftN.wf (W : LiftN Δ Δ' dk n k) (hΔ' : Δ'.WF env U) : Δ.WF env U := by
  induction W with
  | refl => exact hΔ'
  | skip_fvar _ _ _ ih => exact ih hΔ'.1
  | cons_bvar _ W ih =>
    let ⟨hΔ', _, h2⟩ := hΔ'
    exact ⟨ih hΔ', nofun, (VLocalDecl.weakN_iff henv hΔ'.toCtx W.toCtx).1 h2⟩

variable (henv : Ordered env) in
theorem LiftN.fvars_suffix (W : LiftN Δ Δ' dk n k) : Δ.fvars <:+ Δ'.fvars := by
  induction W with
  | refl => exact List.suffix_refl _
  | skip_fvar _ _ _ ih => exact ih.trans (List.suffix_cons ..)
  | cons_bvar _ _ ih => exact ih

theorem LiftN.find? (W : VLCtx.LiftN Δ Δ' dk n k) (hΔ' : Δ'.WF env U)
    (H : VLCtx.find? Δ v = some (e, A)) : VLCtx.find? Δ' v = some (e.liftN n k, A.liftN n k) := by
  induction W generalizing v e A with
  | refl => simp [H]
  | @skip_fvar _ Δ' _ fv' _ W ih =>
    simp [VLCtx.find?]
    cases v with simp [VLCtx.next, bind]
    | inl => exact ⟨_, ih hΔ'.1 H, by simp [VExpr.liftN_liftN]⟩
    | inr fv =>
      cases eq : fv' == fv <;> simp
      · exact ⟨_, ih hΔ'.1 H, by simp [VExpr.liftN_liftN]⟩
      · refine ((List.pairwise_cons.1 hΔ'.fvars_nodup).1 fv' ?_ rfl).elim
        exact W.fvars_suffix.subset ((beq_iff_eq ..).1 eq ▸ find?_eq_some.1 ⟨_, H⟩)
  | cons_bvar d _ ih =>
    simp [VLCtx.find?] at H ⊢
    obtain ⟨_|i⟩ | fv := v <;> simp [VLCtx.next, bind] at H ⊢ <;>
      [(obtain ⟨rfl, rfl⟩ := H);
       (obtain ⟨⟨e, A⟩, H, rfl, rfl⟩ := H
        refine ⟨_, ih (v := .inl i) hΔ'.1 H, ?_⟩);
       (obtain ⟨⟨e, A⟩, H, rfl, rfl⟩ := H
        refine ⟨_, ih (v := .inr fv) hΔ'.1 H, ?_⟩)] <;>
      open VLocalDecl in
      cases d <;> simp [VExpr.lift_liftN', liftN, value, type, depth, VExpr.liftN]

end VLCtx

theorem TrProj.weakN (W : Ctx.LiftN n k Γ Γ')
    (H : TrProj Γ s i e e') : TrProj Γ' s i (e'.liftN n k) (e'.liftN n k) := sorry

variable (henv : Ordered env) in
theorem TrExpr.weakN (W : VLCtx.LiftN Δ Δ' dk n k) (hΔ' : Δ'.WF env Us.length)
    (H : TrExpr env Us Δ e e') : TrExpr env Us Δ' e (e'.liftN n k) := by
  induction H generalizing Δ' dk k with
  | bvar h1 => exact .bvar (W.find? hΔ' h1)
  | fvar h1 => exact .fvar (W.find? hΔ' h1)
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (h1.weakN henv W.toCtx) (h2.weakN henv W.toCtx) (ih1 W hΔ') (ih2 W hΔ')
  | lam h1 _ _ ih1 ih2 =>
    have h1 := h1.weakN henv W.toCtx
    exact .lam h1 (ih1 W hΔ') (ih2 (W.cons_bvar _) ⟨hΔ', nofun, h1⟩)
  | forallE h1 h2 _ _ ih1 ih2 =>
    have h1 := h1.weakN henv W.toCtx
    have h2 := h2.weakN henv W.toCtx.succ
    exact .forallE h1 h2 (ih1 W hΔ') (ih2 (W.cons_bvar _) ⟨hΔ', nofun, h1⟩)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    have h1 := h1.weakN henv W.toCtx
    exact .letE h1 (ih1 W hΔ') (ih2 W hΔ') (ih3 (W.cons_bvar _) ⟨hΔ', nofun, h1⟩)
  | lit _ ih => exact .lit (ih W hΔ')
  | mdata _ ih => exact .mdata (ih W hΔ')
  | proj _ h2 ih => exact .proj (ih W hΔ') (h2.weakN W.toCtx)

variable (henv : Ordered env) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem HasType.skips (W : Ctx.LiftN n k Γ Γ')
    (h1 : env.HasType U Γ' e A) (h2 : e.Skips n k) : ∃ B, env.HasType U Γ' e B ∧ B.Skips n k :=
  IsDefEq.skips henv hΓ' W h1 h2 h2

theorem TrProj.weakN_inv (henv : Ordered env) (hΓ' : OnCtx Γ' (env.IsType U))
    (W : Ctx.LiftN n k Γ Γ') : TrProj Γ' s i (e.liftN n k) e' → ∃ e', TrProj Γ s i e e' := sorry

theorem TrProj.defeqDFC (henv : Ordered env) (hΓ : env.IsDefEqCtx U [] Γ₁ Γ₂)
    (he : env.IsDefEqU U Γ₁ e₁ e₂) (H : TrProj Γ₁ s i e₁ e') :
    ∃ e', TrProj Γ₂ s i e₂ e' := sorry

variable (env : VEnv) (U : Nat) in
inductive VLCtx.IsDefEq : VLCtx → VLCtx → Prop
  | nil : VLCtx.IsDefEq [] []
  | cons {Δ₁ Δ₂ : VLCtx} :
    VLCtx.IsDefEq Δ₁ Δ₂ →
    (∀ fv, ofv = some fv → fv ∉ Δ₁.fvars) →
    VLocalDecl.IsDefEq env U Δ₁.toCtx d₁ d₂ →
    VLCtx.IsDefEq ((ofv, d₁) :: Δ₁) ((ofv, d₂) :: Δ₂)

variable (henv : Ordered env) (hΓ : OnCtx Γ (IsType env U)) in
theorem VLocalDecl.IsDefEq.refl : ∀ {d}, VLocalDecl.WF env U Γ d → VLocalDecl.IsDefEq env U Γ d d
  | .vlam _, ⟨_, h1⟩ => .vlam h1
  | .vlet .., h1 => let ⟨_, h2⟩ := h1.isType henv hΓ; .vlet h1 h2

variable (henv : Ordered env) in
theorem VLCtx.IsDefEq.refl : ∀ {Δ}, VLCtx.WF env U Δ → VLCtx.IsDefEq env U Δ Δ
  | [], _ => .nil
  | (_, _) :: _, ⟨h1, h2, h3⟩ => .cons (IsDefEq.refl h1) h2 (.refl henv h1.toCtx h3)

theorem VLCtx.IsDefEq.defeqCtx : VLCtx.IsDefEq env U Δ₁ Δ₂ → env.IsDefEqCtx U [] Δ₁.toCtx Δ₂.toCtx
  | .nil => .zero
  | .cons h1 _ (.vlam h2) => .succ h1.defeqCtx h2
  | .cons h1 _ (.vlet ..) => h1.defeqCtx

theorem VLCtx.IsDefEq.fvars : VLCtx.IsDefEq env U Δ₁ Δ₂ → Δ₁.fvars = Δ₂.fvars
  | .nil => by simp
  | .cons (ofv := none) h1 h2 _ => h1.fvars
  | .cons (ofv := some fv) h1 h2 _ => by simp [h1.fvars]

theorem VLocalDecl.IsDefEq.wf : VLocalDecl.IsDefEq env U Γ d₁ d₂ → VLocalDecl.WF env U Γ d₁
  | .vlam h3 => ⟨_, h3.hasType.1⟩
  | .vlet h3 _ => h3.hasType.1

theorem VLCtx.IsDefEq.wf : VLCtx.IsDefEq env U Δ₁ Δ₂ → VLCtx.WF env U Δ₁
  | .nil => ⟨⟩
  | .cons h1 h2 h3 => ⟨h1.wf, h2, h3.wf⟩

theorem VLocalDecl.IsDefEq.symm :
    VLocalDecl.IsDefEq env U Δ d₁ d₂ → VLocalDecl.IsDefEq env U Δ d₂ d₁
  | .vlam h1 => .vlam h1.symm
  | .vlet h1 h2 => .vlet (h2.defeqDF h1.symm) h2.symm

theorem VLocalDecl.IsDefEq.defeqDFC (henv : Ordered env) (hΓ : IsDefEqCtx env U Γ₀ Γ₁ Γ₂)
    : VLocalDecl.IsDefEq env U Γ₁ d₁ d₂ → VLocalDecl.IsDefEq env U Γ₂ d₁ d₂
  | .vlam h1 => .vlam (h1.defeqDFC henv hΓ)
  | .vlet h1 h2 => .vlet (h1.defeqDFC henv hΓ) (h2.defeqDFC henv hΓ)

variable (henv : Ordered env) in
theorem VLCtx.IsDefEq.symm : VLCtx.IsDefEq env U Δ₁ Δ₂ → VLCtx.IsDefEq env U Δ₂ Δ₁
  | .nil => .nil
  | .cons h1 h2 h3 =>
    .cons h1.symm (by simpa [h1.fvars] using h2) (h3.symm.defeqDFC henv h1.defeqCtx)

variable (henv : Ordered env) in
theorem VLCtx.IsDefEq.find?_uniq (hΔ : VLCtx.IsDefEq env U Δ₁ Δ₂)
    (H1 : Δ₁.find? v = some (e₁, A₁)) (H2 : Δ₂.find? v = some (e₂, A₂)) :
    env.IsDefEqU U Δ₁.toCtx A₁ A₂ ∧ env.IsDefEq U Δ₁.toCtx e₁ e₂ A₁ := by
  let .cons hΔ h1 h2 := hΔ
  match h2 with
  | .vlam (type₁ := A₁) (type₂ := A₂) h2 =>
    revert H1 H2; unfold VLCtx.find?; split
    · rintro ⟨⟩ ⟨⟩; exact ⟨⟨_, h2.weak henv⟩, .bvar .zero⟩
    · simp [bind, Option.bind_eq_some]
      rintro ⟨d₁', n₁'⟩ H1' rfl rfl ⟨d₂', n₂'⟩ H2' rfl rfl
      obtain ⟨h2, h3⟩ := find?_uniq hΔ H1' H2'
      exact ⟨h2.weakN henv .one, h3.weak henv⟩
  | .vlet h3 h4 =>
    revert H1 H2; unfold VLCtx.find?; split
    · rintro ⟨⟩ ⟨⟩; exact ⟨⟨_, h4⟩, h3⟩
    · simp [bind, Option.bind_eq_some]
      rintro ⟨d₁', n₁'⟩ H1' rfl rfl ⟨d₂', n₂'⟩ H2' rfl rfl
      simpa [VLocalDecl.depth] using find?_uniq hΔ H1' H2'

variable (henv : Ordered env) in
theorem TrExpr.inScope (H : TrExpr env Us Δ e e') : InScope (· ∈ Δ.fvars) e Δ.bvars := by
  induction H with
  | @bvar e A Δ i h1 =>
    simp [InScope]
    induction Δ generalizing i e A with
    | nil => cases h1
    | cons d Δ ih =>
      match d, i with
      | (none, _), 0 => exact Nat.succ_pos _
      | (none, _), _ + 1 =>
        simp [VLCtx.find?, VLCtx.next, bind] at h1
        obtain ⟨⟨_, _⟩, h1, rfl, rfl⟩ := h1
        exact Nat.succ_lt_succ (ih h1)
      | (some _, _), _ =>
        simp [VLCtx.find?, VLCtx.next, bind] at h1
        obtain ⟨⟨_, _⟩, h1, rfl, rfl⟩ := h1
        exact ih h1
  | fvar h1 => exact VLCtx.find?_eq_some.1 ⟨_, h1⟩
  | sort | const | lit | mdata => trivial
  | app _ _ _ _ ih1 ih2
  | lam _ _ _ ih1 ih2
  | forallE _ _ _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | letE _ _ _ _ ih1 ih2 ih3 => exact ⟨ih1, ih2, ih3⟩
  | proj _ _ ih => exact ih

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
  | app h1 h2 => exact ⟨_, h1.app h2⟩
  | lam h1 _ _ _ ih2 =>
    have ⟨_, h1'⟩ := h1
    have ⟨_, h2'⟩ := ih2 ⟨hΔ, nofun, h1⟩
    refine ⟨_, h1'.lam h2'⟩
  | forallE h1 h2 => have ⟨_, h1'⟩ := h1; have ⟨_, h2'⟩ := h2; exact ⟨_, .forallE h1' h2'⟩
  | letE h1 _ _ _ _ _ ih3 => exact ih3 ⟨hΔ, nofun, h1⟩
  | lit _ ih | mdata _ ih => exact ih hΔ
  | proj _ h2 ih => exact h2.wf (ih hΔ)

variable (henv : Ordered env) (hΓ : IsDefEqCtx env U [] Γ₁ Γ₂) in
theorem TrProj.uniq (H1 : TrProj Γ₁ s i e₁ e₁') (H2 : TrProj Γ₂ s i e₂ e₂')
    (H : env.IsDefEqU U Γ₁ e₁ e₂) :
    env.IsDefEqU U Γ₁ e₁' e₂' := sorry

variable (henv : Ordered env) {Us : List Name} (hΔ : VLCtx.IsDefEq env Us.length Δ₁ Δ₂) in
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
    have ⟨_, hb⟩ := ih3 (hΔ.cons nofun <| .vlam hA) r3
    exact ⟨_, .lamDF hA hb⟩
  | forallE l1 l2 _ _ ih3 ih4 =>
    let ⟨_, l1'⟩ := l1; let ⟨_, l2⟩ := l2; let .forallE _ _ r3 r4 := H2
    have hA := ih3 hΔ r3 |>.of_l henv hΔ.wf.toCtx l1'
    have hB := ih4 (hΔ.cons nofun <| .vlam hA) r4 |>.of_l (Γ := _::_) henv ⟨hΔ.wf.toCtx, l1⟩ l2
    exact ⟨_, .forallEDF hA hB⟩
  | letE l1 _ _ _ ih2 ih3 ih4 =>
    have hΓ := hΔ.wf.toCtx
    let .letE _ r2 r3 r4 := H2
    have ⟨_, hb⟩ := l1.isType henv hΓ
    refine ih4 (hΔ.cons nofun ?_) r4
    exact .vlet (ih3 hΔ r3 |>.of_l henv hΓ l1) (ih2 hΔ r2 |>.of_l henv hΓ hb)
  | lit _ ih1 => let .lit r1 := H2; exact ih1 hΔ r1
  | mdata _ ih1 => let .mdata r1 := H2; exact ih1 hΔ r1
  | proj _ l2 ih1 => let .proj r1 r2 := H2; exact l2.uniq r2 (ih1 hΔ r1)

theorem TrExpr.weakN_inv (henv : Ordered env)
    (W : VLCtx.LiftN Δ Δ₂ dk n k) (hΔ : VLCtx.IsDefEq env Us.length Δ₁ Δ₂)
    (H : TrExpr env Us Δ₁ e e') (hs : InScope (· ∈ VLCtx.fvars Δ) e dk) :
    ∃ e', TrExpr env Us Δ e e' := by
  induction H generalizing Δ Δ₂ dk k with
  | @bvar e A Δ₁ i h1 =>
    suffices ∃ p, Δ.find? (.inl i) = some p from let ⟨_, h⟩ := this; ⟨_, .bvar h⟩
    simp [InScope] at hs
    induction W generalizing i e A Δ₁ with | @cons_bvar _ Δ₂ _ _ _ d _ ih => ?_ | _ => cases hs
    obtain ⟨d, Δ₂, rfl, hΔ₁⟩ : ∃ d Δ₁', Δ₁ = (none, d) :: Δ₁' ∧
        VLCtx.IsDefEq env Us.length Δ₁' Δ₂ := by cases d <;> cases hΔ <;> exact ⟨_, _, rfl, ‹_›⟩
    simp [VLCtx.find?] at h1 ⊢
    rcases i with _ | i <;> simp [VLCtx.next, bind] at h1 ⊢
    obtain ⟨_, h1, _⟩ := h1
    have ⟨_, h1⟩ := ih h1 hΔ₁ (Nat.lt_of_succ_lt_succ hs)
    exact ⟨_, _, h1, rfl⟩
  | @fvar _ _ _ fv => let ⟨_, h⟩ := VLCtx.find?_eq_some.2 hs; exact ⟨_, .fvar h⟩
  | sort h1 => exact ⟨_, .sort h1⟩
  | const h1 h2 h3 => exact ⟨_, .const h1 h2 h3⟩
  | app h1 h2 hf ha ih1 ih2 =>
    have hΔ₁ := hΔ.wf; have hΔ₂ := (hΔ.symm henv).wf
    let ⟨f₁, ih1⟩ := ih1 W hΔ hs.1
    let ⟨a₁, ih2⟩ := ih2 W hΔ hs.2
    have h1 := h1.defeqU_l henv hΔ₁.toCtx <| hf.uniq henv hΔ (ih1.weakN henv W hΔ₂)
    have h2 := h2.defeqU_l henv hΔ₁.toCtx <| ha.uniq henv hΔ (ih2.weakN henv W hΔ₂)
    have := VExpr.WF.weakN_iff henv hΔ₂.toCtx W.toCtx (e := f₁.app a₁)
    have := this.1 ⟨_, (h1.app h2).defeqDFC henv hΔ.defeqCtx⟩
    have ⟨_, _, h1, h2⟩ := this.app_inv henv (W.wf henv hΔ₂).toCtx
    exact ⟨_, .app h1 h2 ih1 ih2⟩
  | lam h1 ht _ ih1 ih2 =>
    let ⟨_, h1⟩ := h1
    have hΔ₁ := hΔ.wf; have hΔ₂ := (hΔ.symm henv).wf
    let ⟨ty₁, ih1⟩ := ih1 W hΔ hs.1
    have htt := ht.uniq henv hΔ (ih1.weakN henv W hΔ₂) |>.of_l henv hΔ₁.toCtx h1
    have ⟨_, ih2⟩ := ih2 (W.cons_bvar (.vlam _))
      (hΔ.cons (ofv := none) nofun <| .vlam htt) hs.2.fvars_cons
    have h1 := HasType.weakN_iff (A := .sort _) henv hΔ₂.toCtx W.toCtx
      |>.1 (htt.hasType.2.defeqDFC henv hΔ.defeqCtx)
    exact ⟨_, .lam ⟨_, h1⟩ ih1 ih2⟩
  | forallE h1 h2 ht hb ih1 ih2 =>
    let ⟨_, h1⟩ := h1; let ⟨_, h2⟩ := h2
    have hΔ₁ := hΔ.wf; have hΔ₂ := (hΔ.symm henv).wf
    let ⟨ty₁, ih1⟩ := ih1 W hΔ hs.1
    have htt := ht.uniq henv hΔ (ih1.weakN henv W hΔ₂) |>.of_l henv hΔ₁.toCtx h1
    have hΔ' := hΔ.cons (ofv := none) nofun <| .vlam htt
    have ⟨_, ih2⟩ := ih2 (W.cons_bvar (.vlam _)) hΔ' hs.2.fvars_cons
    have h1' := htt.hasType.2.defeqDFC henv hΔ.defeqCtx
    have h1 := HasType.weakN_iff (A := .sort _) henv hΔ₂.toCtx W.toCtx |>.1 h1'
    have hΔ₂' : VLCtx.WF _ _ ((none, .vlam _) :: _) := ⟨hΔ₂, nofun, _, h1'⟩
    have h2 := (HasType.weakN_iff (A := .sort _) henv hΔ₂'.toCtx (W.cons_bvar (.vlam _)).toCtx).1 <|
      hb.uniq henv hΔ' (ih2.weakN henv (W.cons_bvar _) hΔ₂')
      |>.of_l (Γ := _::_) henv ⟨hΔ₁.toCtx, _, htt.hasType.1⟩ h2
      |>.hasType.2.defeqDFC henv (.succ hΔ.defeqCtx htt)
    exact ⟨_, .forallE ⟨_, h1⟩ ⟨_, h2⟩ ih1 ih2⟩
  | letE h1 ht hv _ ih1 ih2 ih3 =>
    have hΔ₁ := hΔ.wf; have hΔ₂ := (hΔ.symm henv).wf
    let ⟨ty₁, ih1⟩ := ih1 W hΔ hs.1
    let ⟨val₁, ih2⟩ := ih2 W hΔ hs.2.1
    have hvv := hv.uniq henv hΔ (ih2.weakN henv W hΔ₂) |>.of_l henv hΔ₁.toCtx h1
    let ⟨_, h2⟩ := h1.isType henv hΔ₁.toCtx
    have htt := ht.uniq henv hΔ (ih1.weakN henv W hΔ₂) |>.of_l henv hΔ₁.toCtx h2
    have ⟨_, ih3⟩ := ih3 (W.cons_bvar (.vlet ..)) (hΔ.cons nofun <| .vlet hvv htt) hs.2.2.fvars_cons
    have h1 := HasType.weakN_iff henv hΔ₂.toCtx W.toCtx
      |>.1 ((htt.defeqDF hvv).hasType.2.defeqDFC henv hΔ.defeqCtx)
    exact ⟨_, .letE h1 ih1 ih2 ih3⟩
  | lit _ ih => let ⟨_, ih⟩ := ih W hΔ .toConstructor; exact ⟨_, .lit ih⟩
  | mdata _ ih => let ⟨_, ih⟩ := ih W hΔ hs; exact ⟨_, .mdata ih⟩
  | proj h1 h2 ih =>
    have hΔ₂ := (hΔ.symm henv).wf
    let ⟨_, ih⟩ := ih W hΔ hs
    have htt := h1.uniq henv hΔ (ih.weakN henv W hΔ₂)
    have ⟨_, h2⟩ := h2.defeqDFC henv hΔ.defeqCtx htt
    have ⟨_, h2⟩ := h2.weakN_inv henv hΔ₂.toCtx W.toCtx
    exact ⟨_, .proj ih h2⟩

def VLocalDecl.OnVars (P : Nat → Prop) : VLocalDecl → Prop
  | .vlam A => A.OnVars P
  | .vlet A e => A.OnVars P ∧ e.OnVars P

def IsUpSet (P : Nat → Prop) : List VExpr → Prop
  | [] => True
  | A :: Γ => (P 0 → A.OnVars (fun k => P (k + 1))) ∧ IsUpSet (fun k => P (k + 1)) Γ

def VLocalDecl.ClosedN : VLocalDecl → (k : Nat := 0) → Prop
  | .vlam A, k => A.ClosedN k
  | .vlet A e, k => A.ClosedN k ∧ e.ClosedN k

def VLCtx.Closed : VLCtx → Prop
  | [] => True
  | (none, _) :: _ => False
  | (some _, d) :: (Δ : VLCtx) => Δ.Closed ∧ d.ClosedN Δ.bvars

def IsFVarUpSet (P : FVarId → Prop) : VLCtx → Prop
  | [] => True
  | (none, _) :: Δ => IsFVarUpSet P Δ
  | (some fv, d) :: (Δ : VLCtx) =>
    (P fv → d.OnVars fun i => ∀ fv, Δ.vlamName i = some (some fv) → P fv) ∧
    IsFVarUpSet P Δ

theorem IsFVarUpSet.congr :
    ∀ {Δ}, (H : ∀ fv ∈ VLCtx.fvars Δ, P fv ↔ Q fv) → IsFVarUpSet P Δ ↔ IsFVarUpSet Q Δ
  | [], _ => .rfl
  | (none, _) :: Δ, H => congr (Δ := Δ) H
  | (some fv, d) :: (Δ : VLCtx), H => by
    refine and_congr (imp_congr (H _ (.head _)) ?_) (congr fun fv h => H _ (.tail _ h))
    apply iff_of_eq; congr; funext i; refine forall_congr fun fv => propext ?_
    exact imp_congr_right fun ha => H _ (.tail _ (VLCtx.vlamName_mem_fvars ha))

theorem IsFVarUpSet.and_fvars : IsFVarUpSet P Δ ↔ IsFVarUpSet (fun fv => P fv ∧ fv ∈ Δ.fvars) Δ :=
  IsFVarUpSet.congr fun _ h => (and_iff_left h).symm

theorem IsFVarUpSet.trivial : ∀ {Δ}, IsFVarUpSet (fun _ => True) Δ
  | [] => ⟨⟩
  | (none, _) :: Δ => trivial (Δ := Δ)
  | (some _, d) :: Δ =>
    ⟨fun _ => by cases d <;> simp [VLocalDecl.OnVars, VExpr.OnVars], trivial⟩

theorem IsFVarUpSet.fvars : IsFVarUpSet (· ∈ Δ.fvars) Δ :=
  (IsFVarUpSet.congr fun _ => iff_true_intro).2 trivial
