import Batteries.Data.String.Lemmas
import Lean4Lean.Verify.Typing.Expr
import Lean4Lean.Verify.Expr
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Instantiate

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
  cases n <;> simp [InScope, Expr.natLitToConstructor, Expr.natZero, Expr.natSucc]

theorem InScope.strLitToConstructor : InScope P (.strLitToConstructor s) k := by
  simp [InScope, String.foldr_eq, Expr.strLitToConstructor]
  induction s.data <;> simp [*, InScope]

theorem InScope.toConstructor : ∀ {l : Literal}, InScope P l.toConstructor k
  | .natVal _ => .natLitToConstructor
  | .strVal _ => .strLitToConstructor

theorem InScope.fvars_cons :
    InScope (· ∈ VLCtx.fvars Δ) e k → InScope (· ∈ VLCtx.fvars ((ofv, d) :: Δ)) e k :=
  InScope.mono fun a h => by cases ofv <;> simp [h]

theorem Closed.getAppFn {e} (h : Closed e) : Closed e.getAppFn := by
  unfold Expr.getAppFn; split
  · exact Closed.getAppFn h.1
  · exact h

theorem InScope.realLooseBVarRange_le : InScope P e k → e.realLooseBVarRange ≤ k := by
  induction e generalizing k <;>
    simp +contextual [*, InScope, Expr.realLooseBVarRange, Nat.max_le, Nat.sub_le_of_le_add]
  exact id

theorem VLocalDecl.WF.hasType : ∀ {d}, VLocalDecl.WF env U (VLCtx.toCtx Δ) d →
    env.HasType U (VLCtx.toCtx ((ofv, d) :: Δ)) d.value d.type
  | .vlam _, _ => .bvar .zero
  | .vlet .., hA => hA

nonrec theorem VLocalDecl.WF.instN (henv : env.Ordered) (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (h₀ : env.HasType U Γ₀ e₀ A₀) : ∀ {d}, WF env U Γ₁ d → WF env U Γ (d.inst e₀ k)
  | .vlam _,  H | .vlet .., H => H.instN henv W h₀

theorem VLocalDecl.is_liftN {Δ : VLCtx} :
    ∀ {d}, Ctx.LiftN (VLocalDecl.depth d) 0 Δ.toCtx (VLCtx.toCtx ((ofv, d) :: Δ))
  | .vlam _ => .one
  | .vlet .. => .zero []

variable! (env : VEnv) (U : Nat) (Γ : List VExpr) in
inductive VLocalDecl.IsDefEq : VLocalDecl → VLocalDecl → Prop
  | vlam : env.IsDefEq U Γ type₁ type₂ (.sort u) → VLocalDecl.IsDefEq (.vlam type₁) (.vlam type₂)
  | vlet :
    env.IsDefEq U Γ value₁ value₂ type₁ → env.IsDefEq U Γ type₁ type₂ (.sort u) →
    VLocalDecl.IsDefEq (.vlet type₁ value₁) (.vlet type₂ value₂)

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.LiftN n k Γ Γ') in
theorem VLocalDecl.weakN_iff : VLocalDecl.WF env U Γ' (d.liftN n k) ↔ VLocalDecl.WF env U Γ d :=
  match d with
  | .vlam .. => IsType.weakN_iff henv hΓ' W
  | .vlet .. => HasType.weakN_iff henv hΓ' W

namespace VLCtx

variable! (henv : Ordered env) in
theorem WF.find?_wf {Δ : VLCtx} (hΔ : WF env U Δ) (H : Δ.find? v = some (e, A)) :
    env.HasType U Δ.toCtx e A := by
  let (ofv, d') :: Δ := Δ
  unfold find? at H; split at H
  · cases H; exact hΔ.2.2.hasType
  · simp at H
    obtain ⟨d'', n', H, rfl, rfl⟩ := H
    obtain h3 := hΔ.1.find?_wf H
    exact h3.weakN henv VLocalDecl.is_liftN

theorem WF.toCtx : ∀ {Δ}, WF env U Δ → OnCtx Δ.toCtx (env.IsType U)
  | [], _ => ⟨⟩
  | (_, .vlam _) :: _, ⟨hΔ, _, hA⟩ => ⟨hΔ.toCtx, hA⟩
  | (_, .vlet ..) :: _, ⟨hΔ, _, _⟩ => hΔ.toCtx

instance : Coe (WF env U Δ) (OnCtx Δ.toCtx (env.IsType U)) := ⟨(·.toCtx)⟩

theorem WF.fvars_nodup : ∀ {Δ}, WF env U Δ → Δ.fvars.Nodup
  | [], _ => .nil
  | (none, _) :: Δ, ⟨hΔ, _, _⟩ => fvars_nodup (Δ := Δ) hΔ
  | (some fv, _) :: Δ, ⟨hΔ,  h, _⟩ => by
    suffices fv ∉ fvars Δ from (fvars_nodup hΔ).cons (fun _ h e => this (e ▸ h))
    simpa using h

theorem liftVar_zero : liftVar 0 k v = v := by cases v <;> simp [liftVar]

inductive FVLift : VLCtx → VLCtx → Nat → Nat → Nat → Prop
  | refl : FVLift Δ Δ 0 0 0
  | skip_fvar (fv d) : FVLift Δ Δ' 0 n 0 → FVLift Δ ((some fv, d) :: Δ') 0 (n + d.depth) 0
  | cons_bvar (d) : FVLift Δ Δ' dk n k →
    FVLift ((none, d) :: Δ) ((none, d.liftN n k) :: Δ') (dk + 1) n (k + d.depth)

protected theorem FVLift.toCtx (W : FVLift Δ Δ' dk n k) : Ctx.LiftN n k Δ.toCtx Δ'.toCtx := by
  induction W with
  | refl => exact .zero []
  | @skip_fvar _ Δ' _ _ d _ ih =>
    match d with
    | .vlet .. => exact ih
    | .vlam A =>
      generalize hΓ' : toCtx Δ' = Γ' at ih
      let .zero As eq := ih
      simp [toCtx, hΓ']
      exact .zero (A :: As) (eq ▸ rfl)
  | cons_bvar d _ ih =>
    match d with
    | .vlet .. => exact ih
    | .vlam A => exact .succ ih

variable! (henv : VEnv.WF env) in
theorem FVLift.wf (W : FVLift Δ Δ' dk n k) (hΔ' : Δ'.WF env U) : Δ.WF env U := by
  induction W with
  | refl => exact hΔ'
  | skip_fvar _ _ _ ih => exact ih hΔ'.1
  | cons_bvar _ W ih =>
    let ⟨hΔ', _, h2⟩ := hΔ'
    exact ⟨ih hΔ', nofun, (VLocalDecl.weakN_iff henv hΔ'.toCtx W.toCtx).1 h2⟩

theorem FVLift.fvars_suffix (W : FVLift Δ Δ' dk n k) : Δ.fvars <:+ Δ'.fvars := by
  induction W with
  | refl => exact List.suffix_refl _
  | skip_fvar _ _ _ ih => exact ih.trans (List.suffix_cons ..)
  | cons_bvar _ _ ih => exact ih

protected theorem FVLift.find? (W : FVLift Δ Δ' dk n k) (hΔ' : Δ'.WF env U)
    (H : find? Δ v = some (e, A)) : find? Δ' v = some (e.liftN n k, A.liftN n k) := by
  induction W generalizing v e A with
  | refl => simp [H]
  | @skip_fvar _ Δ' _ fv' _ W ih =>
    simp [find?]
    cases v with simp [next, bind]
    | inl => exact ⟨_, _, ih hΔ'.1 H, by simp [VExpr.liftN_liftN]⟩
    | inr fv =>
      cases eq : fv' == fv <;> simp
      · exact ⟨_, _, ih hΔ'.1 H, by simp [VExpr.liftN_liftN]⟩
      · refine ((List.pairwise_cons.1 hΔ'.fvars_nodup).1 fv' ?_ rfl).elim
        exact W.fvars_suffix.subset ((beq_iff_eq ..).1 eq ▸ find?_eq_some.1 ⟨_, H⟩)
  | cons_bvar d _ ih =>
    simp [find?] at H ⊢
    obtain ⟨_|i⟩ | fv := v <;> simp [next, bind] at H ⊢ <;>
      [(obtain ⟨rfl, rfl⟩ := H);
       (obtain ⟨e, A, H, rfl, rfl⟩ := H
        refine ⟨_, _, ih (v := .inl i) hΔ'.1 H, ?_⟩);
       (obtain ⟨e, A, H, rfl, rfl⟩ := H
        refine ⟨_, _, ih (v := .inr fv) hΔ'.1 H, ?_⟩)] <;>
      open VLocalDecl in
      cases d <;> simp [VExpr.lift_liftN', liftN, value, type, depth, VExpr.liftN]

inductive BVLift : (Δ Δ' : VLCtx) → (dn dk n k : Nat) → Prop
  | refl : BVLift Δ Δ 0 0 0 0
  | skip (d) : BVLift Δ Δ' dn 0 n 0 → BVLift Δ ((none, d) :: Δ') (dn + 1) 0 (n + d.depth) 0
  | cons (d) : BVLift Δ Δ' dn dk n k →
    BVLift ((none, d) :: Δ) ((none, d.liftN n k) :: Δ') dn (dk + 1) n (k + d.depth)

theorem BVLift.toCtx (W : BVLift Δ Δ' dn dk n k) : Ctx.LiftN n k Δ.toCtx Δ'.toCtx := by
  induction W with
  | refl => exact .zero []
  | @skip _ Δ' _ _ d _ ih =>
    match d with
    | .vlet .. => exact ih
    | .vlam A =>
      generalize hΓ' : VLCtx.toCtx Δ' = Γ' at ih
      let .zero As eq := ih
      simp [VLCtx.toCtx, hΓ']
      exact .zero (A :: As) (eq ▸ rfl)
  | cons d _ ih =>
    match d with
    | .vlet .. => exact ih
    | .vlam A => exact .succ ih

variable! (henv : VEnv.WF env) in
theorem BVLift.wf (W : BVLift Δ Δ' dn dk n k) (hΔ' : Δ'.WF env U) : Δ.WF env U := by
  induction W with
  | refl => exact hΔ'
  | skip _ _ ih => exact ih hΔ'.1
  | cons _ W ih =>
    let ⟨hΔ', _, h2⟩ := hΔ'
    exact ⟨ih hΔ', nofun, (VLocalDecl.weakN_iff henv hΔ'.toCtx W.toCtx).1 h2⟩

theorem BVLift.fvars_eq (W : BVLift Δ Δ' dn dk n k) : Δ.fvars = Δ'.fvars := by
  induction W with
  | refl => rfl
  | skip _ _ ih => exact ih
  | cons _ _ ih => exact ih

protected theorem BVLift.find? (W : BVLift Δ Δ' dn dk n k) (H : find? Δ v = some (e, A)) :
    find? Δ' (liftVar dn dk v) = some (e.liftN n k, A.liftN n k) := by
  induction W generalizing v e A with
  | refl => simp [H, liftVar_zero]
  | @skip _ Δ' _ fv' _ W ih =>
    obtain v | fv := v <;> simp [find?, liftVar, next] <;>
      exact ⟨_, _, ih H, by simp [VExpr.liftN_liftN]⟩
  | cons d _ ih =>
    obtain (_ | v) | fv := v <;> simp [liftVar] <;>
      [ simp [find?, next] at H ⊢ <;> simp [← H];
        split <;> (
          rename_i h
          simp [Nat.add_right_comm _ 1, find?, next] at H ⊢
          obtain ⟨e, A, H, rfl, rfl⟩ := H
          have := ih H
          simp [liftVar, h] at this
          refine ⟨_, _, this, ?_⟩);
        ( simp [find?, liftVar, next] at H ⊢
          obtain ⟨e, A, H, rfl, rfl⟩ := H
          refine ⟨_, _, ih H, ?_⟩ )] <;>
      open VLocalDecl in
      cases d <;> simp [VExpr.lift_liftN', liftN, value, type, depth, VExpr.liftN]

variable (Δ₀ : VLCtx) (e₀ A₀ : VExpr) in
inductive InstN : Nat → Nat → VLCtx → VLCtx → Prop where
  | zero : InstN 0 0 ((none, .vlam A₀) :: Δ₀) Δ₀
  | succ : InstN dk k Γ Γ' → InstN (dk + 1) (k + d.depth) ((none, d)::Γ) ((none, d.inst e₀ k) :: Γ')

protected theorem InstN.toCtx (W : InstN Δ₀ e₀ A₀ dk k Δ₁ Δ) :
    Ctx.InstN Δ₀.toCtx e₀ A₀ k Δ₁.toCtx Δ.toCtx := by
  induction W with
  | zero => exact .zero
  | @succ _ _ _ _ d _ ih =>
    match d with
    | .vlet .. => exact ih
    | .vlam A => exact .succ ih

variable! (henv : Ordered env) (h₀ : env.HasType U (toCtx Δ₀) e₀ A₀) in
theorem InstN.wf (W : InstN Δ₀ e₀ A₀ dk k Δ₁ Δ) (hΔ' : Δ₁.WF env U) : Δ.WF env U := by
  induction W with
  | zero => exact hΔ'.1
  | succ W ih => let ⟨hΔ', _, h2⟩ := hΔ'; exact ⟨ih hΔ', nofun, h2.instN henv W.toCtx h₀⟩

theorem InstN.fvars_eq (W : InstN Δ₀ e₀ A₀ dk k Δ₁ Δ) :
    Δ₁.fvars = Δ₀.fvars ∧ Δ.fvars = Δ₀.fvars := by
  induction W with
  | zero => exact ⟨rfl, rfl⟩
  | succ _ ih => exact ih

end VLCtx

theorem TrProj.weakN (W : Ctx.LiftN n k Γ Γ')
    (H : TrProj Γ s i e e') : TrProj Γ' s i (e'.liftN n k) (e'.liftN n k) := sorry

variable! (henv : Ordered env) in
theorem TrExprS.weakFV (W : VLCtx.FVLift Δ Δ' dk n k) (hΔ' : Δ'.WF env Us.length)
    (H : TrExprS env Us Δ e e') : TrExprS env Us Δ' e (e'.liftN n k) := by
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

variable! (henv : Ordered env) in
theorem TrExprS.weakBV (W : VLCtx.BVLift Δ Δ' dn dk n k)
    (H : TrExprS env Us Δ e e') : TrExprS env Us Δ' (e.liftLooseBVars' dk dn) (e'.liftN n k) := by
  induction H generalizing Δ' dk k with
  | bvar h1 => exact .bvar (W.find? h1)
  | fvar h1 => exact .fvar (W.find? h1)
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (h1.weakN henv W.toCtx) (h2.weakN henv W.toCtx) (ih1 W) (ih2 W)
  | lam h1 _ _ ih1 ih2 =>
    exact .lam (h1.weakN henv W.toCtx) (ih1 W) (ih2 (W.cons _))
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (h1.weakN henv W.toCtx) (h2.weakN henv W.toCtx.succ) (ih1 W) (ih2 (W.cons _))
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (h1.weakN henv W.toCtx) (ih1 W) (ih2 W) (ih3 (W.cons _))
  | lit _ ih =>
    refine .lit (Expr.liftLooseBVars_eq_self ?_ ▸ ih W :)
    exact InScope.toConstructor.realLooseBVarRange_le (P := default)
  | mdata _ ih => exact .mdata (ih W)
  | proj _ h2 ih => exact .proj (ih W) (h2.weakN W.toCtx)

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem HasType.skips (W : Ctx.LiftN n k Γ Γ')
    (h1 : env.HasType U Γ' e A) (h2 : e.Skips n k) : ∃ B, env.HasType U Γ' e B ∧ B.Skips n k :=
  IsDefEq.skips henv hΓ' W h1 h2 h2

theorem TrProj.weakN_inv (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U))
    (W : Ctx.LiftN n k Γ Γ') : TrProj Γ' s i (e.liftN n k) e' → ∃ e', TrProj Γ s i e e' := sorry

theorem TrProj.defeqDFC (henv : VEnv.WF env) (hΓ : env.IsDefEqCtx U [] Γ₁ Γ₂)
    (he : env.IsDefEqU U Γ₁ e₁ e₂) (H : TrProj Γ₁ s i e₁ e') :
    ∃ e', TrProj Γ₂ s i e₂ e' := sorry

variable! (env : VEnv) (U : Nat) in
inductive VLCtx.IsDefEq : VLCtx → VLCtx → Prop
  | nil : VLCtx.IsDefEq [] []
  | cons {Δ₁ Δ₂ : VLCtx} :
    VLCtx.IsDefEq Δ₁ Δ₂ →
    (∀ fv, ofv = some fv → fv ∉ Δ₁.fvars) →
    VLocalDecl.IsDefEq env U Δ₁.toCtx d₁ d₂ →
    VLCtx.IsDefEq ((ofv, d₁) :: Δ₁) ((ofv, d₂) :: Δ₂)

variable! (henv : Ordered env) (hΓ : OnCtx Γ (IsType env U)) in
theorem VLocalDecl.IsDefEq.refl : ∀ {d}, VLocalDecl.WF env U Γ d → VLocalDecl.IsDefEq env U Γ d d
  | .vlam _, ⟨_, h1⟩ => .vlam h1
  | .vlet .., h1 => let ⟨_, h2⟩ := h1.isType henv hΓ; .vlet h1 h2

variable! (henv : Ordered env) in
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

variable! (henv : Ordered env) in
theorem VLCtx.IsDefEq.symm : VLCtx.IsDefEq env U Δ₁ Δ₂ → VLCtx.IsDefEq env U Δ₂ Δ₁
  | .nil => .nil
  | .cons h1 h2 h3 =>
    .cons h1.symm (by simpa [h1.fvars] using h2) (h3.symm.defeqDFC henv h1.defeqCtx)

variable! (henv : VEnv.WF env) in
theorem VLCtx.IsDefEq.find?_uniq (hΔ : VLCtx.IsDefEq env U Δ₁ Δ₂)
    (H1 : Δ₁.find? v = some (e₁, A₁)) (H2 : Δ₂.find? v = some (e₂, A₂)) :
    env.IsDefEqU U Δ₁.toCtx A₁ A₂ ∧ env.IsDefEq U Δ₁.toCtx e₁ e₂ A₁ := by
  let .cons hΔ h1 h2 := hΔ
  match h2 with
  | .vlam (type₁ := A₁) (type₂ := A₂) h2 =>
    revert H1 H2; unfold VLCtx.find?; split
    · rintro ⟨⟩ ⟨⟩; exact ⟨⟨_, h2.weak henv⟩, .bvar .zero⟩
    · simp
      rintro d₁' n₁' H1' rfl rfl d₂' n₂' H2' rfl rfl
      obtain ⟨h2, h3⟩ := find?_uniq hΔ H1' H2'
      exact ⟨h2.weakN henv .one, h3.weak henv⟩
  | .vlet h3 h4 =>
    revert H1 H2; unfold VLCtx.find?; split
    · rintro ⟨⟩ ⟨⟩; exact ⟨⟨_, h4⟩, h3⟩
    · simp
      rintro d₁' n₁' H1' rfl rfl d₂' n₂' H2' rfl rfl
      simpa [VLocalDecl.depth] using find?_uniq hΔ H1' H2'

theorem VLCtx.IsDefEq.find?_defeqDFC (hΔ : VLCtx.IsDefEq env U Δ₁ Δ₂)
    (H : Δ₁.find? v = some (e₁, A₁)) :
    ∃ e₂ A₂, Δ₂.find? v = some (e₂, A₂) := by
  let .cons hΔ _ _ := hΔ
  revert H; unfold VLCtx.find?; split
  · exact fun _ => ⟨_, _, rfl⟩
  · simp; rintro e A H rfl rfl
    obtain ⟨_, _, H⟩ := find?_defeqDFC hΔ H
    exact ⟨_, _, _, _, H, rfl, rfl⟩

theorem TrExprS.inScope (H : TrExprS env Us Δ e e') : InScope (· ∈ Δ.fvars) e Δ.bvars := by
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
        obtain ⟨_, _, h1, rfl, rfl⟩ := h1
        exact Nat.succ_lt_succ (ih h1)
      | (some _, _), _ =>
        simp [VLCtx.find?, VLCtx.next, bind] at h1
        obtain ⟨_, _, h1, rfl, rfl⟩ := h1
        exact ih h1
  | fvar h1 => exact VLCtx.find?_eq_some.1 ⟨_, h1⟩
  | sort | const | lit | mdata => trivial
  | app _ _ _ _ ih1 ih2
  | lam _ _ _ ih1 ih2
  | forallE _ _ _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | letE _ _ _ _ ih1 ih2 ih3 => exact ⟨ih1, ih2, ih3⟩
  | proj _ _ ih => exact ih

theorem TrProj.wf (H1 : TrProj Δ s i e e') (H2 : VExpr.WF env U Γ e) : VExpr.WF env U Γ e' := sorry

variable! (henv : Ordered env) {Us : List Name} (hΔ : VLCtx.WF env Us.length Δ) in
theorem TrExprS.wf (H : TrExprS env Us Δ e e') : VExpr.WF env Us.length Δ.toCtx e' := by
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

variable! (henv : Ordered env) {Us : List Name} (hΔ : VLCtx.WF env Us.length Δ) in
theorem TrExprS.trExpr (H : TrExprS env Us Δ e e') : TrExpr env Us Δ e e' :=
  ⟨_, H, H.wf henv hΔ⟩

theorem TrExpr.defeq (henv : VEnv.WF env) (hΔ : OnCtx Δ.toCtx (env.IsType Us.length))
    (h1 : TrExpr env Us Δ e e₁) (h2 : env.IsDefEqU Us.length Δ.toCtx e₁ e₂) :
    TrExpr env Us Δ e e₂ := let ⟨_, H, h1⟩ := h1; ⟨_, H, h1.trans henv hΔ h2⟩

theorem TrExpr.app (henv : VEnv.WF env) (hΔ : OnCtx Δ.toCtx (env.IsType Us.length))
    (h1 : env.HasType Us.length Δ.toCtx f' (.forallE A B))
    (h2 : env.HasType Us.length Δ.toCtx a' A)
    (h3 : TrExpr env Us Δ f f')
    (h4 : TrExpr env Us Δ a a') :
    TrExpr env Us Δ (.app f a) (.app f' a') :=
  let ⟨_, s3, h3⟩ := h3
  let ⟨_, s4, h4⟩ := h4
  have h3 := h3.of_r henv hΔ h1
  have h4 := h4.of_r henv hΔ h2
  ⟨_, .app h3.hasType.1 h4.hasType.1 s3 s4, _, h3.appDF h4⟩

variable! (henv : VEnv.WF env) (hΓ : IsDefEqCtx env U [] Γ₁ Γ₂) in
theorem TrProj.uniq (H1 : TrProj Γ₁ s i e₁ e₁') (H2 : TrProj Γ₂ s i e₂ e₂')
    (H : env.IsDefEqU U Γ₁ e₁ e₂) :
    env.IsDefEqU U Γ₁ e₁' e₂' := sorry

variable! (henv : VEnv.WF env) {Us : List Name} (hΔ : VLCtx.IsDefEq env Us.length Δ₁ Δ₂) in
theorem TrExprS.uniq (H1 : TrExprS env Us Δ₁ e e₁) (H2 : TrExprS env Us Δ₂ e e₂) :
    env.IsDefEqU Us.length Δ₁.toCtx e₁ e₂ := by
  induction H1 generalizing Δ₂ e₂ with
  | bvar l1 => let .bvar r1 := H2; exact ⟨_, (hΔ.find?_uniq henv l1 r1).2⟩
  | fvar l1 => let .fvar r1 := H2; exact ⟨_, (hΔ.find?_uniq henv l1 r1).2⟩
  | sort l1 => let .sort r1 := H2; cases l1.symm.trans r1; exact ⟨_, .sort (.of_ofLevel l1)⟩
  | const l1 l2 l3 =>
    let .const r1 r2 r3 := H2; cases l1.symm.trans r1; cases l2.symm.trans r2
    exact (TrExprS.const l1 l2 l3).wf henv hΔ.wf
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
  | proj _ l2 ih1 => let .proj r1 r2 := H2; exact l2.uniq henv hΔ.defeqCtx r2 (ih1 hΔ r1)

variable! (henv : VEnv.WF env) {Us : List Name} (hΔ : VLCtx.IsDefEq env Us.length Δ₁ Δ₂) in
theorem TrExprS.defeqDFC (H : TrExprS env Us Δ₁ e e₁) : ∃ e₂, TrExprS env Us Δ₂ e e₂ := by
  induction H generalizing Δ₂ with
  | bvar h1 => have ⟨_, _, h1⟩ := hΔ.find?_defeqDFC h1; exact ⟨_, .bvar h1⟩
  | fvar h1 => have ⟨_, _, h1⟩ := hΔ.find?_defeqDFC h1; exact ⟨_, .fvar h1⟩
  | sort h1 => exact ⟨_, .sort h1⟩
  | const h1 h2 h3 => exact ⟨_, .const h1 h2 h3⟩
  | app h1 h2 h3 h4 ih3 ih4 =>
    let ⟨_, h3'⟩ := ih3 hΔ
    let ⟨_, h4'⟩ := ih4 hΔ
    have h1 := h1.defeqDFC henv hΔ.defeqCtx
    have h2 := h2.defeqDFC henv hΔ.defeqCtx
    have h1 := h1.defeqU_l henv (hΔ.symm henv).wf (h3'.uniq henv (hΔ.symm henv) h3).symm
    have h2 := h2.defeqU_l henv (hΔ.symm henv).wf (h4'.uniq henv (hΔ.symm henv) h4).symm
    exact ⟨_, .app h1 h2 h3' h4'⟩
  | lam h1 h2 h3 ih2 ih3 =>
    let ⟨_, h1'⟩ := h1
    let ⟨_, h2'⟩ := ih2 hΔ
    have h1 := h1.defeqDFC henv hΔ.defeqCtx
    have h1 := h1.defeqU_l henv (hΔ.symm henv).wf (h2'.uniq henv (hΔ.symm henv) h2).symm
    have ht := (h2.uniq henv hΔ h2').of_l henv hΔ.wf h1'
    let ⟨_, h3'⟩ := ih3 (hΔ.cons nofun <| .vlam ht)
    exact ⟨_, .lam h1 h2' h3'⟩
  | forallE h1 h2 h3 h4 ih3 ih4 =>
    let ⟨_, h1'⟩ := h1
    let ⟨_, h2'⟩ := h2
    let ⟨_, h3'⟩ := ih3 hΔ
    have ht := (h3.uniq henv hΔ h3').of_l henv hΔ.wf h1'
    have hΔ' := hΔ.cons (ofv := none) nofun (.vlam ht)
    let ⟨_, h4'⟩ := ih4 hΔ'
    have h1 := h1.defeqDFC henv hΔ.defeqCtx
    have h2 := h2.defeqDFC henv (hΔ.defeqCtx.succ ht)
    have h1 := h1.defeqU_l henv (hΔ.symm henv).wf (h3'.uniq henv (hΔ.symm henv) h3).symm
    have h2 := h2.defeqU_l henv (hΔ'.symm henv).wf (h4'.uniq henv (hΔ'.symm henv) h4).symm
    exact ⟨_, .forallE h1 h2 h3' h4'⟩
  | letE h1 h2 h3 h4 ih2 ih3 ih4 =>
    let ⟨_, h2'⟩ := ih2 hΔ
    let ⟨_, h3'⟩ := ih3 hΔ
    have ⟨_, h0⟩ := h1.isType henv hΔ.wf
    have t0 := (h2.uniq henv hΔ h2').of_l henv hΔ.wf h0
    have t1 := (h3.uniq henv hΔ h3').of_l henv hΔ.wf h1
    have t2 := (h2'.uniq henv (hΔ.symm henv) h2).symm
    have t3 := (h3'.uniq henv (hΔ.symm henv) h3).symm
    have hΔ' := hΔ.cons (ofv := none) nofun (.vlet t1 t0)
    let ⟨_, h4'⟩ := ih4 hΔ'
    have h0 := h0.defeqDFC henv hΔ.defeqCtx
    have h0 := h0.defeqU_l henv (hΔ.symm henv).wf t2
    have h1 := h1.defeqDFC henv hΔ.defeqCtx
    have h1 := h1.defeqU_l henv (hΔ.symm henv).wf t3
    have h1 := h1.defeqU_r henv (hΔ.symm henv).wf t2
    exact ⟨_, .letE h1 h2' h3' h4'⟩
  | lit _ ih1 => let ⟨_, h1⟩ := ih1 hΔ; exact ⟨_, .lit h1⟩
  | mdata _ ih1 => let ⟨_, h1⟩ := ih1 hΔ; exact ⟨_, .mdata h1⟩
  | proj h1 h2 ih1 =>
    let ⟨_, h1'⟩ := ih1 hΔ
    let ⟨_, h2⟩ := h2.defeqDFC henv hΔ.defeqCtx (h1.uniq henv hΔ h1')
    exact ⟨_, .proj h1' h2⟩

theorem TrExprS.weakFV_inv (henv : VEnv.WF env)
    (W : VLCtx.FVLift Δ Δ₂ dk n k) (hΔ : VLCtx.IsDefEq env Us.length Δ₁ Δ₂)
    (H : TrExprS env Us Δ₁ e e') (hs : InScope (· ∈ VLCtx.fvars Δ) e dk) :
    ∃ e', TrExprS env Us Δ e e' := by
  induction H generalizing Δ Δ₂ dk k with
  | @bvar e A Δ₁ i h1 =>
    suffices ∃ p, Δ.find? (.inl i) = some p from let ⟨_, h⟩ := this; ⟨_, .bvar h⟩
    simp [InScope] at hs
    induction W generalizing i e A Δ₁ with | @cons_bvar _ Δ₂ _ _ _ d _ ih => ?_ | _ => cases hs
    obtain ⟨d, Δ₂, rfl, hΔ₁⟩ : ∃ d Δ₁', Δ₁ = (none, d) :: Δ₁' ∧
        VLCtx.IsDefEq env Us.length Δ₁' Δ₂ := by cases d <;> cases hΔ <;> exact ⟨_, _, rfl, ‹_›⟩
    simp [VLCtx.find?] at h1 ⊢
    rcases i with _ | i <;> simp [VLCtx.next, bind] at h1 ⊢
    obtain ⟨_, _, h1, _⟩ := h1
    have ⟨_, h1⟩ := ih h1 hΔ₁ (Nat.lt_of_succ_lt_succ hs)
    exact ⟨_, _, _, _, h1, rfl, rfl⟩
  | @fvar _ _ _ fv => let ⟨_, h⟩ := VLCtx.find?_eq_some.2 hs; exact ⟨_, .fvar h⟩
  | sort h1 => exact ⟨_, .sort h1⟩
  | const h1 h2 h3 => exact ⟨_, .const h1 h2 h3⟩
  | app h1 h2 hf ha ih1 ih2 =>
    have hΔ₁ := hΔ.wf; have hΔ₂ := (hΔ.symm henv).wf
    let ⟨f₁, ih1⟩ := ih1 W hΔ hs.1
    let ⟨a₁, ih2⟩ := ih2 W hΔ hs.2
    have h1 := h1.defeqU_l henv hΔ₁.toCtx <| hf.uniq henv hΔ (ih1.weakFV henv W hΔ₂)
    have h2 := h2.defeqU_l henv hΔ₁.toCtx <| ha.uniq henv hΔ (ih2.weakFV henv W hΔ₂)
    have := VExpr.WF.weakN_iff henv hΔ₂.toCtx W.toCtx (e := f₁.app a₁)
    have := this.1 ⟨_, (h1.app h2).defeqDFC henv hΔ.defeqCtx⟩
    have ⟨_, _, h1, h2⟩ := this.app_inv henv (W.wf henv hΔ₂).toCtx
    exact ⟨_, .app h1 h2 ih1 ih2⟩
  | lam h1 ht _ ih1 ih2 =>
    let ⟨_, h1⟩ := h1
    have hΔ₁ := hΔ.wf; have hΔ₂ := (hΔ.symm henv).wf
    let ⟨ty₁, ih1⟩ := ih1 W hΔ hs.1
    have htt := ht.uniq henv hΔ (ih1.weakFV henv W hΔ₂) |>.of_l henv hΔ₁.toCtx h1
    have ⟨_, ih2⟩ := ih2 (W.cons_bvar (.vlam _))
      (hΔ.cons (ofv := none) nofun <| .vlam htt) hs.2.fvars_cons
    have h1 := HasType.weakN_iff (A := .sort _) henv hΔ₂.toCtx W.toCtx
      |>.1 (htt.hasType.2.defeqDFC henv hΔ.defeqCtx)
    exact ⟨_, .lam ⟨_, h1⟩ ih1 ih2⟩
  | forallE h1 h2 ht hb ih1 ih2 =>
    let ⟨_, h1⟩ := h1; let ⟨_, h2⟩ := h2
    have hΔ₁ := hΔ.wf; have hΔ₂ := (hΔ.symm henv).wf
    let ⟨ty₁, ih1⟩ := ih1 W hΔ hs.1
    have htt := ht.uniq henv hΔ (ih1.weakFV henv W hΔ₂) |>.of_l henv hΔ₁.toCtx h1
    have hΔ' := hΔ.cons (ofv := none) nofun <| .vlam htt
    have ⟨_, ih2⟩ := ih2 (W.cons_bvar (.vlam _)) hΔ' hs.2.fvars_cons
    have h1' := htt.hasType.2.defeqDFC henv hΔ.defeqCtx
    have h1 := HasType.weakN_iff (A := .sort _) henv hΔ₂.toCtx W.toCtx |>.1 h1'
    have hΔ₂' : VLCtx.WF _ _ ((none, .vlam _) :: _) := ⟨hΔ₂, nofun, _, h1'⟩
    have h2 := (HasType.weakN_iff (A := .sort _) henv hΔ₂'.toCtx (W.cons_bvar (.vlam _)).toCtx).1 <|
      hb.uniq henv hΔ' (ih2.weakFV henv (W.cons_bvar _) hΔ₂')
      |>.of_l (Γ := _::_) henv ⟨hΔ₁.toCtx, _, htt.hasType.1⟩ h2
      |>.hasType.2.defeqDFC henv (.succ hΔ.defeqCtx htt)
    exact ⟨_, .forallE ⟨_, h1⟩ ⟨_, h2⟩ ih1 ih2⟩
  | letE h1 ht hv _ ih1 ih2 ih3 =>
    have hΔ₁ := hΔ.wf; have hΔ₂ := (hΔ.symm henv).wf
    let ⟨ty₁, ih1⟩ := ih1 W hΔ hs.1
    let ⟨val₁, ih2⟩ := ih2 W hΔ hs.2.1
    have hvv := hv.uniq henv hΔ (ih2.weakFV henv W hΔ₂) |>.of_l henv hΔ₁.toCtx h1
    let ⟨_, h2⟩ := h1.isType henv hΔ₁.toCtx
    have htt := ht.uniq henv hΔ (ih1.weakFV henv W hΔ₂) |>.of_l henv hΔ₁.toCtx h2
    have ⟨_, ih3⟩ := ih3 (W.cons_bvar (.vlet ..)) (hΔ.cons nofun <| .vlet hvv htt) hs.2.2.fvars_cons
    have h1 := HasType.weakN_iff henv hΔ₂.toCtx W.toCtx
      |>.1 ((htt.defeqDF hvv).hasType.2.defeqDFC henv hΔ.defeqCtx)
    exact ⟨_, .letE h1 ih1 ih2 ih3⟩
  | lit _ ih => let ⟨_, ih⟩ := ih W hΔ .toConstructor; exact ⟨_, .lit ih⟩
  | mdata _ ih => let ⟨_, ih⟩ := ih W hΔ hs; exact ⟨_, .mdata ih⟩
  | proj h1 h2 ih =>
    have hΔ₂ := (hΔ.symm henv).wf
    let ⟨_, ih⟩ := ih W hΔ hs
    have htt := h1.uniq henv hΔ (ih.weakFV henv W hΔ₂)
    have ⟨_, h2⟩ := h2.defeqDFC henv hΔ.defeqCtx htt
    have ⟨_, h2⟩ := h2.weakN_inv henv hΔ₂.toCtx W.toCtx
    exact ⟨_, .proj ih h2⟩

variable! (henv : Ordered env) (h₀ : TrExprS env Us Δ₀ e₀ e₀') in
theorem TrExprS.instN_var (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) (H : Δ₁.find? v = some (e', A)) :
    TrExprS env Us Δ (Expr.instantiate1'.go e₀ (VLCtx.varToExpr v) dk) (e'.inst e₀' k) := by
  induction W generalizing v e' A with
  | zero =>
    obtain (_|i)|fv := v <;> simp [VLCtx.varToExpr, Expr.instantiate1'.go, Expr.liftLooseBVars_zero]
    · cases H; simp [VLocalDecl.value, VExpr.inst]; exact h₀
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      simp [VLocalDecl.depth, VExpr.inst_liftN]
      exact .bvar H
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      simp [VLocalDecl.depth, VExpr.inst_liftN]
      exact .fvar H
  | @succ _ k _ _ d _ ih =>
    obtain (_|i)|fv := v <;> simp [VLCtx.varToExpr, Expr.instantiate1'.go]
    · cases H
      cases d <;> exact .bvar <| by simp [VLocalDecl.value, VExpr.inst, VLocalDecl.depth]; rfl
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      have := ih H; revert this
      simp [VLCtx.varToExpr, Expr.instantiate1'.go]; split <;> [skip; split]
      · intro | .bvar h => ?_
        exact .bvar <| by
          simp [VLCtx.find?, VLCtx.next]
          refine ⟨_, _, h, ?_, rfl⟩
          cases d <;> simp [VLocalDecl.depth, VLocalDecl.inst, VExpr.lift_instN_lo]
      · intro H
        have := Expr.liftLooseBVars_add ▸ H.weakBV henv (.skip (d.inst e₀' k) .refl)
        cases d <;> simpa [← VExpr.lift_instN_lo, VExpr.liftN_zero,
          VLocalDecl.inst, VLocalDecl.depth] using this
      · obtain _|i := i; · omega
        intro | .bvar h => ?_
        exact .bvar <| by
          simp [VLCtx.find?, VLCtx.next]
          refine ⟨_, _, h, ?_, rfl⟩
          cases d <;> simp [VLocalDecl.depth, VLocalDecl.inst, VExpr.lift_instN_lo]
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      have .fvar h := ih H
      exact .fvar <| by
        simp [VLCtx.find?, VLCtx.next]
        refine ⟨_, _, h, ?_, rfl⟩
        cases d <;> simp [VLocalDecl.depth, VLocalDecl.inst, VExpr.lift_instN_lo]

theorem TrProj.instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (H : TrProj Γ₁ s i e e') : TrProj Γ s i (e.inst e₀ k) (e'.inst e₀ k) := sorry

variable! (henv : Ordered env) (h₀ : TrExprS env Us Δ₀ e₀ e₀')
  (t₀ : env.HasType Us.length Δ₀.toCtx e₀' A₀) in
theorem TrExprS.instN (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) (H : TrExprS env Us Δ₁ e e') :
    TrExprS env Us Δ (Expr.instantiate1'.go e₀ e dk) (e'.inst e₀' k) := by
  induction H generalizing Δ dk k with
  | bvar h1 | fvar h1 => exact instN_var henv h₀ W h1
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (h1.instN henv W.toCtx t₀) (h2.instN henv W.toCtx t₀) (ih1 W) (ih2 W)
  | lam h1 _ _ ih1 ih2 =>
    exact .lam (h1.instN henv W.toCtx t₀) (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (h1.instN henv W.toCtx t₀) (h2.instN henv W.toCtx.succ t₀)
      (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (h1.instN henv W.toCtx t₀) (ih1 W) (ih2 W) (ih3 (W.succ (d := .vlet ..)))
  | lit _ ih =>
    refine .lit (Expr.instantiate1'_go_eq_self ?_ ▸ ih W :)
    exact InScope.toConstructor.realLooseBVarRange_le (P := default)
  | mdata _ ih => exact .mdata (ih W)
  | proj _ h2 ih => exact .proj (ih W) (h2.instN W.toCtx)

theorem TrExprS.inst {Δ : VLCtx} (henv : Ordered env)
    (t₀ : env.HasType Us.length Δ.toCtx e₀' A₀)
    (H : TrExprS env Us ((none, .vlam A₀) :: Δ) e e')
    (h₀ : TrExprS env Us Δ e₀ e₀') :
    TrExprS env Us Δ (e.instantiate1' e₀) (e'.inst e₀') :=
  h₀.instN henv t₀ .zero H

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

inductive LambdaBodyN : Nat → Expr → Expr → Prop
  | zero : LambdaBodyN 0 e e
  | succ : LambdaBodyN n body e → LambdaBodyN (n+1) (.lam i ty body bi) e

theorem LambdaBodyN.safe (H : LambdaBodyN n e1 e2) : e1.Safe → e2.Safe := by
  induction H with
  | zero => exact id
  | succ _ ih => exact fun h => ih h.2

theorem LambdaBodyN.closed (H : LambdaBodyN n e1 e2) : e1.Closed k → e2.Closed (k + n) := by
  induction H generalizing k with
  | zero => exact id
  | succ _ ih => exact fun h => (Nat.add_right_comm .. ▸ ih h.2 :)

theorem LambdaBodyN.add (H1 : LambdaBodyN m e1 e2) (H2 : LambdaBodyN n e2 e3) :
    LambdaBodyN (n + m) e1 e3 := by
  induction H1 with
  | zero => exact H2
  | succ _ ih => exact .succ (ih H2)

inductive BetaReduce : Expr → Expr → Prop
  | refl : BetaReduce e e
  | trans : BetaReduce e₁ e₂ → BetaReduce e₂ e₃ → BetaReduce e₁ e₃
  | app : BetaReduce f f' → BetaReduce (.app f a) (.app f' a)
  | beta : BetaReduce (.app (.lam i ty body bi) e) (body.instantiate1' e)

theorem BetaReduce.appRevList (H : BetaReduce f f') :
    BetaReduce (f.mkAppRevList es) (f'.mkAppRevList es) := by
  induction es with
  | nil => exact H
  | cons _ _ ih => exact .app ih

private def instantiateListUp : Expr → List Expr → Nat → Expr
  | e, [], _ => e
  | e, a :: as, n => Expr.instantiate1'.go a (instantiateListUp e as (n+1)) n

private theorem instantiateListUp_eq_self (h : e.realLooseBVarRange ≤ i) :
    instantiateListUp e as i = e := by
  induction as generalizing i with simp [instantiateListUp] | cons a as ih => ?_
  rw [ih, Expr.instantiate1'_go_eq_self h]; omega

theorem BetaReduce.cheapBetaReduce (hs : e.Safe) (hc : e.Closed) :
    BetaReduce e e.cheapBetaReduce := by
  simp [Expr.cheapBetaReduce]
  split; · exact .refl
  split; · exact .refl
  let rec loop {e i fn args cont} (H : LambdaBodyN i e fn) (hi : i ≤ args.size) :
    ∃ n fn', LambdaBodyN n e fn' ∧ n ≤ args.size ∧
      Expr.cheapBetaReduce.loop args cont i fn = cont n fn' := by
    unfold Expr.cheapBetaReduce.loop; split
    · split
      · exact loop (by simpa [Nat.add_comm] using H.add (.succ .zero)) ‹_›
      · exact ⟨_, _, H, Nat.le_of_lt ‹_›, rfl⟩
    · exact ⟨_, _, H, hi, rfl⟩
  refine let ⟨i, fn, h1, h2, eq⟩ := loop .zero (Nat.zero_le _); eq ▸ ?_; clear eq
  simp [Expr.getAppArgs_eq] at h2 ⊢
  obtain ⟨l₁, l₂, rfl, eq⟩ : ∃ l₁ l₂, l₁.length = i ∧ e.getAppArgsRevList.reverse = l₁ ++ l₂ :=
    ⟨_, _, List.length_take_of_le (by simp [h2]), (List.take_append_drop ..).symm⟩
  have eqr := congrArg List.reverse eq; simp at eqr
  have inst_reduce (l₂) {{r}} (hr : instantiateListUp fn (l₁.reverse ++ l₂) 0 = r) :
    BetaReduce ((instantiateListUp e.getAppFn l₂ 0).mkAppRevList l₁.reverse) r := by
    generalize e.getAppFn = e₀ at h1
    have inst_lam {n ty body bi} (as j) :
        instantiateListUp (.lam n ty body bi) as j =
        .lam n (instantiateListUp ty as j) (instantiateListUp body as (j+1)) bi := by
      induction as generalizing j <;> simp [instantiateListUp, Expr.instantiate1'.go, *]
    subst r; clear h2 eq eqr
    induction l₁ generalizing e₀ fn l₂ with
    | nil => let .zero := h1; exact .refl
    | cons a l ih =>
      let .succ (body := body) h1 := h1
      rw [inst_lam]
      simp; refine .trans (.appRevList .beta) (ih _ (a::l₂) _ h1)
  split <;> rename_i h3
  · simp [Expr.hasLooseBVars, (h1.safe hs.getAppFn).looseBVarRange_eq] at h3
    rw [Expr.mkAppRange_eq (l₂ := l₂) (l₃ := []) (by simp [eq]) rfl (by simp [← eq])]
    rw [← e.mkAppRevList_getAppArgsRevList, eqr]; simp
    exact .appRevList <| inst_reduce [] <| instantiateListUp_eq_self (by simp [h3])
  split <;> [rename_i n; exact .refl]
  have hc := h1.closed hc.getAppFn
  simp [InScope] at hc; rw [if_pos hc]
  rw [Expr.mkAppRange_eq (l₂ := l₂) (l₃ := []) (by simp [eq]) rfl (by simp [← eq])]
  conv => lhs; rw [← e.mkAppRevList_getAppArgsRevList]
  simp [eqr]
  refine .appRevList <| inst_reduce [] ?_
  rw [List.getElem?_append_left (by omega), Nat.sub_right_comm, ← List.getElem?_reverse hc]
  suffices ∀ l₁ i, ∀ n < l₁.length,
      instantiateListUp (Expr.bvar (i + n)) l₁ i = (l₁[n]?.getD default).liftLooseBVars' 0 i by
    simpa [Expr.liftLooseBVars_zero] using this l₁.reverse 0 n (by simp [hc])
  intro l₁ i n lt
  induction l₁ generalizing n i with
  | nil => cases lt
  | cons a l ih =>
    simp [instantiateListUp]
    obtain _ | n := n
    · rw [instantiateListUp_eq_self (by apply Nat.le_refl)]
      simp [Expr.instantiate1'.go]
    · simp [← Nat.add_assoc, Nat.add_right_comm _ _ 1] at lt ⊢
      have := by simpa using @Expr.instantiate1'_go_liftLooseBVars (s := 0)
      rw [ih (i+1) _ lt, this]

theorem TrExpr.beta (H : TrExpr env Us Δ e e')
    (henv : VEnv.WF env) (hΓ : VLCtx.WF env Us.length Δ)
    (H : BetaReduce e e₂) : TrExpr env Us Δ e₂ e' := by
  induction H generalizing e' with
  | refl => exact H
  | trans _ _ ih1 ih2 => exact ih2 (ih1 H)
  | app _ ih =>
    let ⟨_, .app hf ha tf ta, _, df⟩ := H
    have ⟨_, _, hf', ha'⟩ := df.app_inv' henv hΓ (.inl rfl)
    exact ((ih ⟨_, tf, _, hf'⟩).app henv hΓ hf' ha' (ta.trExpr henv hΓ)).defeq henv hΓ ⟨_, df⟩
  | beta =>
    let ⟨_, .app hf ha tf ta, _, df⟩ := H
    let .lam hA tA tb := tf
    have ⟨⟨_, hA⟩, _, hb⟩ := hf.lam_inv henv hΓ
    have ht := hf.uniqU henv hΓ (hA.lam hb)
    have ⟨⟨_, Ae⟩, _, be⟩ := ht.forallE_inv henv hΓ
    have hΓΓ := VLCtx.IsDefEq.cons (.refl henv hΓ) (ofv := none) nofun (.vlam Ae.symm)
    have ⟨_, tb'⟩ := tb.defeqDFC henv hΓΓ
    have beta := hb.beta (Ae.defeq ha)
    have be' := (tb.uniq henv hΓΓ tb').of_l henv hΓΓ.wf hb
    have hi := be'.instDF henv hΓ (.defeq Ae ha)
    exact ⟨_, .inst henv ha tb' ta, _, beta.trans_l henv hΓ hi |>.symm.trans_l henv hΓ df⟩
