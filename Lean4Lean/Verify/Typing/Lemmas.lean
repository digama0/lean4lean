import Batteries.Data.String.Lemmas
import Lean4Lean.Verify.Typing.Expr
import Lean4Lean.Verify.Expr
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Instantiate

namespace Lean4Lean
open VEnv Lean
open scoped List

theorem fvarsIn_iff : FVarsIn P e ↔ (∀ fv ∈ e.fvarsList, P fv) ∧ FVarsIn (fun _ => True) e := by
  induction e <;> simp [FVarsIn, Expr.fvarsList, *] <;> grind

theorem FVarsIn.mp (H : ∀ fv, P fv → Q fv → R fv) :
    ∀ {e}, FVarsIn P e → FVarsIn Q e → FVarsIn R e
  | .bvar _, l, _ | .sort .., l, _ | .const .., l, _ | .lit .., l, _ => l
  | .fvar _, l, r => H _ l r
  | .app .., ⟨l1, l2⟩, ⟨r1, r2⟩
  | .lam .., ⟨l1, l2⟩, ⟨r1, r2⟩
  | .forallE .., ⟨l1, l2⟩, ⟨r1, r2⟩ => ⟨l1.mp H r1, l2.mp H r2⟩
  | .letE .., ⟨l1, l2, l3⟩, ⟨r1, r2, r3⟩ => ⟨l1.mp H r1, l2.mp H r2, l3.mp H r3⟩
  | .proj _ _ e, l, r | .mdata _ e, l, r => l.mp (e := e) H r

theorem FVarsIn.mono (H : ∀ fv, P fv → Q fv) (h : FVarsIn P e) : FVarsIn Q e :=
  h.mp (fun _ h _ => H _ h) h

theorem Closed.mono (H : k ≤ k') : ∀ {e}, Closed e k → Closed e k'
  | .bvar _, h => Nat.lt_of_lt_of_le h H
  | .fvar _, h | .sort .., h | .const .., h | .lit .., h => h
  | .app .., ⟨h1, h2⟩ => ⟨h1.mono H, h2.mono H⟩
  | .lam .., ⟨h1, h2⟩
  | .forallE .., ⟨h1, h2⟩ => ⟨h1.mono H, h2.mono (Nat.succ_le_succ H)⟩
  | .letE .., ⟨h1, h2, h3⟩ => ⟨h1.mono H, h2.mono H, h3.mono (Nat.succ_le_succ H)⟩
  | .proj _ _ e, h | .mdata _ e, h => h.mono (e := e) H

theorem FVarsIn.natLitToConstructor : FVarsIn P (.natLitToConstructor n) := by
  cases n <;> simp [FVarsIn, Expr.natLitToConstructor, Expr.natZero, Expr.natSucc]

theorem Closed.natLitToConstructor : Closed (.natLitToConstructor n) k := by
  cases n <;> simp [Closed, Expr.natLitToConstructor, Expr.natZero, Expr.natSucc]

theorem FVarsIn.strLitToConstructor : FVarsIn P (.strLitToConstructor s) := by
  simp [FVarsIn, String.foldr_eq, Expr.strLitToConstructor]
  induction s.data <;> simp [*, FVarsIn, Level.hasMVar']

theorem Closed.strLitToConstructor : Closed (.strLitToConstructor s) k := by
  simp [Closed, String.foldr_eq, Expr.strLitToConstructor]
  induction s.data <;> simp [*, Closed]

theorem FVarsIn.toConstructor : ∀ {l : Literal}, FVarsIn P l.toConstructor
  | .natVal _ => .natLitToConstructor
  | .strVal _ => .strLitToConstructor

theorem FVarsIn.litType {l : Literal} : FVarsIn P l.type := by
  cases l <;> simp [FVarsIn, Literal.type]

theorem Closed.toConstructor : ∀ {l : Literal}, Closed l.toConstructor k
  | .natVal _ => .natLitToConstructor
  | .strVal _ => .strLitToConstructor

theorem toConstructor : ∀ {l : Literal}, Closed l.toConstructor k
  | .natVal _ => .natLitToConstructor
  | .strVal _ => .strLitToConstructor

theorem Closed.litType {l : Literal} : Closed l.type k := by cases l <;> trivial

theorem FVarsIn.fvars_cons :
    FVarsIn (· ∈ VLCtx.fvars Δ) e → FVarsIn (· ∈ VLCtx.fvars ((ofv, d) :: Δ)) e :=
  FVarsIn.mono fun a h => by cases ofv <;> simp [h]

theorem FVarsIn.abstract_instantiate1 (h : FVarsIn (· ≠ v) e) :
    (Expr.instantiate1' e (.fvar v) k).abstract1 v k = e := by
  induction e generalizing k with simp_all [Expr.instantiate1', Expr.abstract1, FVarsIn]
  | bvar i =>
    split <;> [skip; split]
    · simp [Expr.abstract1, *]
    · simp [Expr.abstract1, Expr.liftLooseBVars', *]
    · obtain _|i := i <;> simp [Expr.abstract1] <;> omega
  | fvar v' => exact Ne.symm h

theorem FVarsIn.abstract_eq_self (h : FVarsIn (· ≠ v) e) (hc : Closed e k) :
    e.abstract1 v k = e := by
  induction e generalizing k <;> simp_all [FVarsIn, Closed, Expr.abstract1]
  exact Ne.symm h

theorem FVarsIn.liftLooseBVars (h : FVarsIn P e) : FVarsIn P (Expr.liftLooseBVars' e s d) := by
  induction e generalizing s <;> simp_all [FVarsIn, Expr.liftLooseBVars']

theorem FVarsIn.instantiate1_go (h1 : FVarsIn P e) (h2 : FVarsIn P a) :
    FVarsIn P (Expr.instantiate1' e a k) := by
  induction e generalizing k <;> simp_all [FVarsIn, Expr.instantiate1']
  (repeat' split) <;> simp [*, FVarsIn.liftLooseBVars, FVarsIn]

theorem FVarsIn.instantiate1 (h1 : FVarsIn P e) (h2 : FVarsIn P a) :
    FVarsIn P (Expr.instantiate1' e a) := h1.instantiate1_go h2

theorem FVarsIn.instantiateList (h1 : FVarsIn P e) (h2 : ∀ a ∈ as, FVarsIn P a) (k := 0) :
    FVarsIn P (Expr.instantiateList e as k) := by
  induction as generalizing e <;> simp_all [Expr.instantiateList, FVarsIn.instantiate1_go]

theorem FVarsIn.abstract1 (h1 : FVarsIn P e) :
    FVarsIn P (Expr.abstract1 a e k) := by
  induction e generalizing k <;> simp_all [FVarsIn, Expr.abstract1]
  split <;> simp [FVarsIn, *]

theorem FVarsIn.appRevList :
    FVarsIn P (f.mkAppRevList es) ↔ FVarsIn P f ∧ ∀ e ∈ es, FVarsIn P e := by
  induction es <;> simp [FVarsIn, and_comm, and_left_comm, *]

theorem Closed.abstract1 (h1 : Closed e k) :
    Closed (Expr.abstract1 a e k) (k+1) := by
  induction e generalizing k with simp_all [Closed, Expr.abstract1]
  | bvar => omega
  | fvar => split <;> simp [Closed]

theorem Closed.getAppFn {e} (h : Closed e) : Closed e.getAppFn := by
  unfold Expr.getAppFn; split
  · exact Closed.getAppFn h.1
  · exact h

theorem Closed.getAppArgsRevList {e} (h : Closed e)
    {{a}} (ha : a ∈ e.getAppArgsRevList) : Closed a := by
  revert a; unfold Expr.getAppArgsRevList; split <;> simp
  exact ⟨h.2, Closed.getAppArgsRevList h.1⟩

theorem Closed.getAppArgsList {e} (h : Closed e)
    {{a}} (ha : a ∈ e.getAppArgsList) : Closed a :=
  h.getAppArgsRevList (by simpa [← Expr.getAppArgsList_reverse])

theorem Closed.looseBVarRange_le : Closed e k → e.looseBVarRange' ≤ k := by
  induction e generalizing k <;>
    simp +contextual [*, Closed, Expr.looseBVarRange', Nat.max_le]
  exact id

theorem Closed.looseBVarRange_zero (H : Closed e) : e.looseBVarRange' = 0 := by
  simpa using H.looseBVarRange_le

theorem VLocalDecl.WF.hasType : ∀ {d}, VLocalDecl.WF env U (VLCtx.toCtx Δ) d →
    env.HasType U (VLCtx.toCtx ((ofv, d) :: Δ)) d.value d.type
  | .vlam _, _ => .bvar .zero
  | .vlet .., hA => hA

nonrec theorem VLocalDecl.WF.weakN (henv : env.Ordered) (W : Ctx.LiftN n k Γ Γ') :
    ∀ {d}, WF env U Γ d → WF env U Γ' (d.liftN n k)
  | .vlam _,  H | .vlet .., H => H.weakN henv W

nonrec theorem VLocalDecl.WF.instN (henv : env.Ordered) (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (h₀ : env.HasType U Γ₀ e₀ A₀) : ∀ {d}, WF env U Γ₁ d → WF env U Γ (d.inst e₀ k)
  | .vlam _,  H | .vlet .., H => H.instN henv W h₀

nonrec theorem VLocalDecl.WF.instL {env : VEnv} (hls : ∀ l ∈ ls, l.WF U') :
    ∀ {d}, WF env ls.length Γ d → WF env U' (Γ.map (·.instL ls)) (d.instL ls)
  | .vlam _,  H | .vlet .., H => H.instL hls

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
  | (some (fv, _), _) :: Δ, ⟨hΔ,  h, _⟩ => by
    suffices fv ∉ fvars Δ from (fvars_nodup hΔ).cons (fun _ h (e:fv=_) => this (e ▸ h))
    exact (h _ _ rfl).1

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

theorem FVLift.from_nil : ∀ {Δ : VLCtx}, Δ.NoBV → FVLift [] Δ 0 Δ.toCtx.length 0
  | [], _ => .refl
  | (some _, .vlam _) :: _, H => .skip_fvar _ _ (.from_nil H)
  | (some _, .vlet _ _) :: _, H => .skip_fvar _ _ (.from_nil H)

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
    let (fv', deps) := fv'; simp [find?]
    cases v with simp [next]
    | inl => exact ⟨_, _, ih hΔ'.1 H, by simp [VExpr.liftN_liftN]⟩
    | inr fv =>
      cases eq : fv' == fv <;> simp
      · exact ⟨_, _, ih hΔ'.1 H, by simp [VExpr.liftN_liftN]⟩
      · refine ((List.pairwise_cons.1 hΔ'.fvars_nodup).1 fv' ?_ rfl).elim
        exact W.fvars_suffix.subset ((beq_iff_eq ..).1 eq ▸ find?_eq_some.1 ⟨_, H⟩)
  | cons_bvar d _ ih =>
    simp [find?] at H ⊢
    obtain ⟨_|i⟩ | fv := v <;> simp [next] at H ⊢ <;>
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
      [ (simp [find?, next] at H ⊢; simp [← H]);
        split <;> (
          rename_i h
          simp [Nat.add_right_comm _ 1, find?, next] at H ⊢
          obtain ⟨e, A, H, rfl, rfl⟩ := H
          have := ih H
          simp [liftVar, h] at this
          refine ⟨_, _, this, ?_⟩);
        ( simp [find?, next] at H ⊢
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

variable (Δ₀ : VLCtx) (e₀ A₀ : VExpr) in
inductive InstLet : Nat → Nat → VLCtx → VLCtx → Prop where
  | zero : InstLet 0 0 ((none, .vlet A₀ e₀) :: Δ₀) Δ₀
  | succ : InstLet dk k Γ Γ' → InstLet (dk + 1) (k + d.depth) ((none, d)::Γ) ((none, d) :: Γ')

protected theorem InstLet.toCtx (W : InstLet Δ₀ e₀ A₀ dk k Δ₁ Δ) : Δ₁.toCtx = Δ.toCtx := by
  induction W with
  | zero => rfl
  | @succ _ _ _ _ d _ ih =>
    match d with
    | .vlet .. => exact ih
    | .vlam _ => exact congrArg (_::·) ih

theorem InstLet.wf (W : InstLet Δ₀ e₀ A₀ dk k Δ₁ Δ) (hΔ' : Δ₁.WF env U) : Δ.WF env U := by
  induction W with
  | zero => exact hΔ'.1
  | succ W ih => let ⟨hΔ', _, h2⟩ := hΔ'; exact ⟨ih hΔ', nofun, W.toCtx ▸ h2⟩

theorem InstLet.fvars_eq (W : InstLet Δ₀ e₀ A₀ dk k Δ₁ Δ) :
    Δ₁.fvars = Δ₀.fvars ∧ Δ.fvars = Δ₀.fvars := by
  induction W with
  | zero => exact ⟨rfl, rfl⟩
  | succ _ ih => exact ih

variable (Δ₀ : VLCtx) (v₀ : FVarId) (d₀ : VLocalDecl) in
inductive Abstract : Nat → Nat → VLCtx → VLCtx → Prop where
  | zero : Abstract 0 0 ((some (v₀, deps), d₀) :: Δ₀) ((none, d₀) :: Δ₀)
  | succ : Abstract dk k Γ Γ' → Abstract (dk + 1) (k + d.depth) ((none, d) :: Γ) ((none, d) :: Γ')

protected theorem Abstract.toCtx (W : Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ) : Δ₁.toCtx = Δ.toCtx := by
  induction W with
  | zero => cases d₀ <;> rfl
  | @succ _ _ _ _ d _ ih =>
    match d with
    | .vlet .. => exact ih
    | .vlam A => exact congrArg (_ :: ·) ih

theorem Abstract.wf (W : Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ) (hΔ' : Δ₁.WF env U) : Δ.WF env U := by
  induction W with
  | zero => exact ⟨hΔ'.1, nofun, hΔ'.2.2⟩
  | succ W ih => let ⟨hΔ', _, h2⟩ := hΔ'; exact ⟨ih hΔ', nofun, W.toCtx ▸ h2⟩

theorem Abstract.fvars_eq (W : Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ) :
    Δ₁.fvars = v₀ :: Δ₀.fvars ∧ Δ.fvars = Δ₀.fvars := by
  induction W with
  | zero => exact ⟨rfl, rfl⟩
  | succ _ ih => exact ih

theorem Abstract.find?_self (W : Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ) :
    Δ₁.find? (.inr v₀) = some (d₀.value.liftN k, d₀.type.liftN k) := by
  induction W with simp [find?, next]
  | succ _ ih => exact ⟨_, _, ih, by simp [VExpr.liftN_liftN]⟩

protected theorem Abstract.find? (W : Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ) (h : v ≠ .inr v₀) :
    Δ.find? v = Δ₁.find? (clear% h; match v with
      | .inl i => if i < dk then .inl i else if i = dk then .inr v₀ else .inl (i - 1)
      | .inr v' => .inr v') := by
  induction W generalizing v with
  | zero =>
    obtain (_|i)|v := v <;> simp [find?, next]
    cases eq : v₀ == v; · simp
    · simp at h eq; cases h eq.symm
  | @succ dk k _ _ _ _ ih =>
    obtain (_|i)|v := v <;> simp [find?, next]
    · have := @ih (.inl i) nofun; revert this
      by_cases h : i < dk <;> simp +contextual [h]
      by_cases h : i = dk <;> simp +contextual [h]
      obtain _|i := i <;> [omega; simp]
    · simp [ih h]

theorem instL_eq_map (Δ : VLCtx) : Δ.instL ls = Δ.map (fun (ofv, d) => (ofv, d.instL ls)) := by
  induction Δ <;> simp [instL, *]

@[simp] theorem instL_toCtx (Δ : VLCtx) : (Δ.instL ls).toCtx = Δ.toCtx.map (·.instL ls) := by
  induction Δ with
  | nil => rfl
  | cons head => obtain ⟨_, _|_⟩ := head <;> rw [instL, VLocalDecl.instL] <;> simp [toCtx, *]

variable! (hls : ∀ l ∈ (ls : List _), VLevel.WF U l) in
protected theorem WF.instL : ∀ {Δ}, VLCtx.WF env ls.length Δ →
    VLCtx.WF env U (Δ.instL ls)
  | [], _ => ⟨⟩
  | (_, d) :: Δ, ⟨h1, h2, h3⟩ =>
    ⟨h1.instL, by simpa [instL_eq_map, fvars] using h2, by simpa using h3.instL hls⟩

theorem find?_instL : find? Δ v = some (e, A) →
    find? (Δ.instL ls) v = some (e.instL ls, A.instL ls) := by
  induction Δ generalizing v e A with
  | nil => nofun
  | cons d Δ ih =>
    simp [find?, instL]; split <;> simp
    · rintro rfl rfl; cases d.2 <;> exact ⟨rfl, by simp [VLocalDecl.instL, VLocalDecl.type]⟩
    · rintro e A h rfl rfl
      exact ⟨_, _, ih h, by cases d.2 <;> simp [VLocalDecl.instL, VLocalDecl.depth]⟩

variable (env : VEnv) (U) in
inductive SortList : VLCtx → List VLevel → Prop
  | nil : SortList Δ []
  | cons : SortList Δ ls → env.HasType U Δ.toCtx A (.sort u) →
    SortList ((some fv, .vlam A) :: Δ) (u :: ls)

end VLCtx

theorem TrProj.weakN (W : Ctx.LiftN n k Γ Γ')
    (H : TrProj Γ s i e e') : TrProj Γ' s i (e.liftN n k) (e'.liftN n k) := sorry

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

variable! (henv : WF env) in
theorem TrExpr.weakFV (W : VLCtx.FVLift Δ Δ' dk n k) (hΔ' : Δ'.WF env Us.length)
    (H : TrExpr env Us Δ e e') : TrExpr env Us Δ' e (e'.liftN n k) :=
  let ⟨_, H1, H2⟩ := H
  ⟨_, H1.weakFV henv W hΔ', H2.weakN henv W.toCtx⟩

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
    exact Closed.toConstructor.looseBVarRange_le
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

variable! {env env' : VEnv} (henv : env ≤ env') in
theorem TrExprS.mono (H : TrExprS env Us Δ e e') : TrExprS env' Us Δ e e' := by
  induction H with
  | bvar h1 => exact .bvar h1
  | fvar h1 => exact .fvar h1
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const (henv.1 h1) h2 h3
  | app h1 h2 _ _ ih1 ih2 => exact .app (h1.mono henv) (h2.mono henv) ih1 ih2
  | lam h1 _ _ ih1 ih2 => exact .lam (h1.mono henv) ih1 ih2
  | forallE h1 h2 _ _ ih1 ih2 => exact .forallE (h1.mono henv) (h2.mono henv) ih1 ih2
  | letE h1 _ _ _ ih1 ih2 ih3 => exact .letE (h1.mono henv) ih1 ih2 ih3
  | lit _ ih => refine .lit ih
  | mdata _ ih => exact .mdata ih
  | proj _ h2 ih => exact .proj ih h2

variable! {env env' : VEnv} (henv : env ≤ env') in
theorem TrExpr.mono (H : TrExpr env Us Δ e e') : TrExpr env' Us Δ e e' :=
  let ⟨_, H1, H2⟩ := H; ⟨_, H1.mono henv, H2.mono henv⟩

variable! (env : VEnv) (U : Nat) in
inductive VLCtx.IsDefEq : VLCtx → VLCtx → Prop
  | nil : VLCtx.IsDefEq [] []
  | cons {Δ₁ Δ₂ : VLCtx} :
    VLCtx.IsDefEq Δ₁ Δ₂ →
    (∀ fv deps, ofv = some (fv, deps) → fv ∉ Δ₁.fvars ∧ deps ⊆ Δ₁.fvars) →
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

theorem TrExprS.closed (H : TrExprS env Us Δ e e') : Closed e Δ.bvars := by
  induction H with
  | @bvar e A Δ i h1 =>
    simp [Closed]
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
  | fvar | sort | const | lit | mdata => trivial
  | app _ _ _ _ ih1 ih2
  | lam _ _ _ ih1 ih2
  | forallE _ _ _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | letE _ _ _ _ ih1 ih2 ih3 => exact ⟨ih1, ih2, ih3⟩
  | proj _ _ ih => exact ih

theorem ofLevel_hasMVar (h : VLevel.ofLevel ls l = some l') : l.hasMVar' = false := by
  induction l generalizing l' with simp [VLevel.ofLevel, bind, Level.hasMVar'] at h ⊢
  | succ _ ih => obtain ⟨l', h, ⟨⟩⟩ := h; exact ih h
  | max _ _ ih1 ih2 | imax _ _ ih1 ih2 => obtain ⟨_, h1, _, h2, ⟨⟩⟩ := h; exact ⟨ih1 h1, ih2 h2⟩

theorem TrExprS.fvarsIn (H : TrExprS env Us Δ e e') : FVarsIn (· ∈ Δ.fvars) e := by
  induction H with
  | fvar h1 => exact VLCtx.find?_eq_some.1 ⟨_, h1⟩
  | sort h => exact ofLevel_hasMVar h
  | const _ h =>
    rw [List.mapM_eq_some] at h
    intro _ hl
    have ⟨_, _, h⟩ := h.forall_exists_l _ hl
    exact ofLevel_hasMVar h
  | bvar | lit | mdata => trivial
  | app _ _ _ _ ih1 ih2
  | lam _ _ _ ih1 ih2
  | forallE _ _ _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | letE _ _ _ _ ih1 ih2 ih3 => exact ⟨ih1, ih2, ih3⟩
  | proj _ _ ih => exact ih

theorem TrExprS.fvarsList (H : TrExprS env Us Δ e e') : e.fvarsList ⊆ Δ.fvars :=
  (fvarsIn_iff.1 H.fvarsIn).1

theorem TrExpr.closed (H : TrExpr env Us Δ e e') : Closed e Δ.bvars :=
  let ⟨_, H, _⟩ := H; H.closed

theorem TrExpr.fvarsIn (H : TrExpr env Us Δ e e') : FVarsIn (· ∈ Δ.fvars) e :=
  let ⟨_, H, _⟩ := H; H.fvarsIn

theorem TrExpr.fvarsList (H : TrExpr env Us Δ e e') : e.fvarsList ⊆ Δ.fvars :=
  (fvarsIn_iff.1 H.fvarsIn).1

theorem TrProj.wf (H1 : TrProj Δ s i e e') (H2 : VExpr.WF env U Γ e) : VExpr.WF env U Γ e' := sorry

variable! (henv : Ordered env) {Us : List Name} (hΔ : VLCtx.WF env Us.length Δ) in
theorem TrExprS.wf (H : TrExprS env Us Δ e e') : VExpr.WF env Us.length Δ.toCtx e' := by
  induction H with
  | bvar h1 | fvar h1 => exact ⟨_, hΔ.find?_wf henv h1⟩
  | sort h1 => exact ⟨_, HasType.sort (.of_ofLevel h1)⟩
  | const h1 h2 h3 => exact ⟨_,
    HasType.const h1 (.of_mapM_ofLevel h2) ((List.mapM_eq_some.1 h2).length_eq.symm.trans h3)⟩
  | app h1 h2 => exact ⟨_, h1.app h2⟩
  | lam h1 _ _ _ ih2 =>
    have ⟨_, h1'⟩ := h1
    have ⟨_, h2'⟩ := ih2 ⟨hΔ, nofun, h1⟩
    refine ⟨_, h1'.lam h2'⟩
  | forallE h1 h2 => have ⟨_, h1'⟩ := h1; have ⟨_, h2'⟩ := h2; exact ⟨_, h1'.forallE h2'⟩
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
  | sort l1 =>
    let .sort r1 := H2; cases l1.symm.trans r1; exact ⟨_, HasType.sort (.of_ofLevel l1)⟩
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
theorem TrExpr.uniq (H1 : TrExpr env Us Δ₁ e e₁) (H2 : TrExpr env Us Δ₂ e e₂) :
    env.IsDefEqU Us.length Δ₁.toCtx e₁ e₂ := by
  let ⟨_, H1, eq1⟩ := H1
  let ⟨_, H2, eq2⟩ := H2
  exact eq1.symm.trans henv hΔ.wf <| (H1.uniq henv hΔ H2).trans henv hΔ.wf <|
    eq2.defeqDFC henv (hΔ.defeqCtx.symm henv)

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

theorem TrExpr.lam (henv : VEnv.WF env) (hΔ : VLCtx.WF env Us.length Δ)
    (h1 : env.IsType Us.length Δ.toCtx ty')
    (h2 : TrExpr env Us Δ ty ty')
    (h3 : TrExpr env Us ((none, .vlam ty') :: Δ) body body') :
    TrExpr env Us Δ (.lam name ty body bi) (.lam ty' body') :=
  let ⟨_, h1⟩ := h1
  let ⟨_, s2, h2⟩ := h2
  let ⟨_, s3, _, h3⟩ := h3
  have := h2.symm.of_l henv hΔ h1
  have hΔΔ := .cons (.refl henv hΔ) (ofv := none) nofun (.vlam this)
  let ⟨_, s3'⟩ := s3.defeqDFC henv hΔΔ
  let ⟨_, h3'⟩ := s3.uniq henv hΔΔ s3'
  ⟨_, .lam ⟨_, this.hasType.2⟩ s2 s3', _,
    .symm <| .lamDF this <| h3.symm.trans_l henv hΔΔ.wf.toCtx h3'⟩

theorem TrExpr.forallE (henv : VEnv.WF env) (hΔ : VLCtx.WF env Us.length Δ)
    (h1 : env.IsType Us.length Δ.toCtx ty')
    (h2 : env.IsType Us.length (ty' :: Δ.toCtx) body')
    (h3 : TrExpr env Us Δ ty ty')
    (h4 : TrExpr env Us ((none, .vlam ty') :: Δ) body body') :
    TrExpr env Us Δ (.forallE name ty body bi) (.forallE ty' body') :=
  let ⟨_, h1⟩ := h1
  let ⟨_, h2⟩ := h2
  let ⟨_, s3, h3⟩ := h3
  let ⟨_, s4, _, h4⟩ := h4
  have := h3.symm.of_l henv hΔ h1
  have hΔΔ := .cons (.refl henv hΔ) (ofv := none) nofun (.vlam this)
  let ⟨_, s4'⟩ := s4.defeqDFC henv hΔΔ
  let ⟨_, h4'⟩ := s4.uniq henv hΔΔ s4'
  have h4 := h4.trans_r henv hΔΔ.wf h2 |>.symm.trans_l henv hΔΔ.wf h4'
  have h5 := h4.hasType.2.defeq_l henv this
  ⟨_, .forallE ⟨_, this.hasType.2⟩ ⟨_, h5⟩ s3 s4', _, .symm <| .forallEDF this h4⟩

theorem TrExpr.letE (henv : VEnv.WF env) (hΔ : VLCtx.WF env Us.length Δ)
    (h1 : env.HasType Us.length Δ.toCtx val' ty')
    (h2 : TrExpr env Us Δ ty ty')
    (h3 : TrExpr env Us Δ val val')
    (h4 : TrExpr env Us ((none, .vlet ty' val') :: Δ) body body') :
    TrExpr env Us Δ (.letE name ty val body nd) body' :=
  have ⟨_, h0⟩ := h1.isType henv hΔ
  let ⟨_, s2, h2⟩ := h2
  let ⟨_, s3, h3⟩ := h3
  let ⟨_, s4, _, h4⟩ := h4
  have h1' := h1.defeqU_r henv hΔ h2.symm |>.defeqU_l henv hΔ h3.symm
  have h2' := h2.symm.of_l henv hΔ h0
  have h3' := h3.symm.of_l henv hΔ h1
  have hΔΔ := VLCtx.IsDefEq.cons (.refl henv hΔ) (ofv := none) nofun (.vlet h3' h2')
  let ⟨_, s4'⟩ := s4.defeqDFC henv hΔΔ
  let ⟨_, h4'⟩ := s4.uniq henv hΔΔ s4'
  ⟨_, .letE h1' s2 s3 s4', _, h4'.symm.trans_l henv hΔ h4⟩

theorem TrExpr.lit (h : TrExpr env Us Δ l.toConstructor e') : TrExpr env Us Δ (.lit l) e' :=
  let ⟨_, s2, h2⟩ := h; ⟨_, .lit s2, h2⟩

theorem TrExpr.mdata (h : TrExpr env Us Δ e e') : TrExpr env Us Δ (.mdata d e) e' :=
  let ⟨_, s2, h2⟩ := h; ⟨_, .mdata s2, h2⟩

theorem TrExpr.proj {env Us Δ e e' s i e''} (henv : VEnv.WF env) (hΔ : VLCtx.WF env Us.length Δ)
    (H : TrExpr env Us Δ e e') (H2 : TrProj Δ.toCtx s i e' e'') :
    TrExpr env Us Δ (.proj s i e) e'' :=
  let ⟨_, s2, h2⟩ := H
  have ⟨_, H2'⟩ := H2.defeqDFC henv (.refl hΔ) h2.symm
  ⟨_, .proj s2 H2', H2'.uniq henv (.refl hΔ) H2 h2⟩

theorem TrExprS.weakFV_inv (henv : VEnv.WF env)
    (W : VLCtx.FVLift Δ Δ₂ dk n k) (hΔ : VLCtx.IsDefEq env Us.length Δ₁ Δ₂)
    (H : TrExprS env Us Δ₁ e e') (hc : Closed e dk) (hv : FVarsIn (· ∈ VLCtx.fvars Δ) e) :
    ∃ e', TrExprS env Us Δ e e' := by
  induction H generalizing Δ Δ₂ dk k with
  | @bvar e A Δ₁ i h1 =>
    suffices ∃ p, Δ.find? (.inl i) = some p from let ⟨_, h⟩ := this; ⟨_, .bvar h⟩
    simp [Closed] at hc
    induction W generalizing i e A Δ₁ with | @cons_bvar _ Δ₂ _ _ _ d _ ih => ?_ | _ => cases hc
    obtain ⟨d, Δ₂, rfl, hΔ₁⟩ : ∃ d Δ₁', Δ₁ = (none, d) :: Δ₁' ∧
        VLCtx.IsDefEq env Us.length Δ₁' Δ₂ := by cases d <;> cases hΔ <;> exact ⟨_, _, rfl, ‹_›⟩
    simp [VLCtx.find?] at h1 ⊢
    rcases i with _ | i <;> simp [VLCtx.next] at h1 ⊢
    obtain ⟨_, _, h1, _⟩ := h1
    have ⟨_, h1⟩ := ih h1 hΔ₁ (Nat.lt_of_succ_lt_succ hc) hv
    exact ⟨_, _, _, _, h1, rfl, rfl⟩
  | @fvar _ _ _ fv => let ⟨_, h⟩ := VLCtx.find?_eq_some.2 hv; exact ⟨_, .fvar h⟩
  | sort h1 => exact ⟨_, .sort h1⟩
  | const h1 h2 h3 => exact ⟨_, .const h1 h2 h3⟩
  | app h1 h2 hf ha ih1 ih2 =>
    have hΔ₁ := hΔ.wf; have hΔ₂ := (hΔ.symm henv).wf
    let ⟨f₁, ih1⟩ := ih1 W hΔ hc.1 hv.1
    let ⟨a₁, ih2⟩ := ih2 W hΔ hc.2 hv.2
    have h1 := h1.defeqU_l henv hΔ₁.toCtx <| hf.uniq henv hΔ (ih1.weakFV henv W hΔ₂)
    have h2 := h2.defeqU_l henv hΔ₁.toCtx <| ha.uniq henv hΔ (ih2.weakFV henv W hΔ₂)
    have := VExpr.WF.weakN_iff henv hΔ₂.toCtx W.toCtx (e := f₁.app a₁)
    have := this.1 ⟨_, (h1.app h2).defeqDFC henv hΔ.defeqCtx⟩
    have ⟨_, _, h1, h2⟩ := this.app_inv henv (W.wf henv hΔ₂).toCtx
    exact ⟨_, .app h1 h2 ih1 ih2⟩
  | lam h1 ht _ ih1 ih2 =>
    let ⟨_, h1⟩ := h1
    have hΔ₁ := hΔ.wf; have hΔ₂ := (hΔ.symm henv).wf
    let ⟨ty₁, ih1⟩ := ih1 W hΔ hc.1 hv.1
    have htt := ht.uniq henv hΔ (ih1.weakFV henv W hΔ₂) |>.of_l henv hΔ₁.toCtx h1
    have ⟨_, ih2⟩ := ih2 (W.cons_bvar (.vlam _))
      (hΔ.cons (ofv := none) nofun <| .vlam htt) hc.2 hv.2.fvars_cons
    have h1 := HasType.weakN_iff (A := .sort _) henv hΔ₂.toCtx W.toCtx
      |>.1 (htt.hasType.2.defeqDFC henv hΔ.defeqCtx)
    exact ⟨_, .lam ⟨_, h1⟩ ih1 ih2⟩
  | forallE h1 h2 ht hb ih1 ih2 =>
    let ⟨_, h1⟩ := h1; let ⟨_, h2⟩ := h2
    have hΔ₁ := hΔ.wf; have hΔ₂ := (hΔ.symm henv).wf
    let ⟨ty₁, ih1⟩ := ih1 W hΔ hc.1 hv.1
    have htt := ht.uniq henv hΔ (ih1.weakFV henv W hΔ₂) |>.of_l henv hΔ₁.toCtx h1
    have hΔ' := hΔ.cons (ofv := none) nofun <| .vlam htt
    have ⟨_, ih2⟩ := ih2 (W.cons_bvar (.vlam _)) hΔ' hc.2 hv.2.fvars_cons
    have h1' := htt.hasType.2.defeqDFC henv hΔ.defeqCtx
    have h1 := HasType.weakN_iff (A := .sort _) henv hΔ₂.toCtx W.toCtx |>.1 h1'
    have hΔ₂' : VLCtx.WF _ _ ((none, .vlam _) :: _) := ⟨hΔ₂, nofun, _, h1'⟩
    have h2 := (HasType.weakN_iff (A := .sort _) henv hΔ₂'.toCtx (W.cons_bvar (.vlam _)).toCtx).1 <|
      hb.uniq henv hΔ' (ih2.weakFV henv (W.cons_bvar _) hΔ₂')
      |>.of_l (Γ := _::_) henv ⟨hΔ₁.toCtx, _, htt.hasType.1⟩ h2
      |>.hasType.2.defeqDFC henv (.succ hΔ.defeqCtx htt)
    exact ⟨_, .forallE ⟨_, h1⟩ ⟨_, h2⟩ ih1 ih2⟩
  | letE h1 ht ha _ ih1 ih2 ih3 =>
    have hΔ₁ := hΔ.wf; have hΔ₂ := (hΔ.symm henv).wf
    let ⟨ty₁, ih1⟩ := ih1 W hΔ hc.1 hv.1
    let ⟨val₁, ih2⟩ := ih2 W hΔ hc.2.1 hv.2.1
    have hvv := ha.uniq henv hΔ (ih2.weakFV henv W hΔ₂) |>.of_l henv hΔ₁.toCtx h1
    let ⟨_, h2⟩ := h1.isType henv hΔ₁.toCtx
    have htt := ht.uniq henv hΔ (ih1.weakFV henv W hΔ₂) |>.of_l henv hΔ₁.toCtx h2
    have ⟨_, ih3⟩ := ih3 (W.cons_bvar (.vlet ..))
      (hΔ.cons nofun <| .vlet hvv htt) hc.2.2 hv.2.2.fvars_cons
    have h1 := HasType.weakN_iff henv hΔ₂.toCtx W.toCtx
      |>.1 ((htt.defeqDF hvv).hasType.2.defeqDFC henv hΔ.defeqCtx)
    exact ⟨_, .letE h1 ih1 ih2 ih3⟩
  | lit _ ih => let ⟨_, ih⟩ := ih W hΔ .toConstructor .toConstructor; exact ⟨_, .lit ih⟩
  | mdata _ ih => let ⟨_, ih⟩ := ih W hΔ hc hv; exact ⟨_, .mdata ih⟩
  | proj h1 h2 ih =>
    have hΔ₂ := (hΔ.symm henv).wf
    let ⟨_, ih⟩ := ih W hΔ hc hv
    have htt := h1.uniq henv hΔ (ih.weakFV henv W hΔ₂)
    have ⟨_, h2⟩ := h2.defeqDFC henv hΔ.defeqCtx htt
    have ⟨_, h2⟩ := h2.weakN_inv henv hΔ₂.toCtx W.toCtx
    exact ⟨_, .proj ih h2⟩

variable! (henv : Ordered env) (h₀ : TrExprS env Us Δ₀ e₀ e₀') in
theorem TrExprS.instN_var (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) (H : Δ₁.find? v = some (e', A)) :
    TrExprS env Us Δ (Expr.instantiate1' (VLCtx.varToExpr v) e₀ dk) (e'.inst e₀' k) := by
  induction W generalizing v e' A with
  | zero =>
    obtain (_|i)|fv := v <;> simp [VLCtx.varToExpr, Expr.instantiate1', Expr.liftLooseBVars_zero]
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
    obtain (_|i)|fv := v <;> simp [VLCtx.varToExpr, Expr.instantiate1']
    · cases H
      cases d <;> exact .bvar <| by simp [VLocalDecl.value, VExpr.inst, VLocalDecl.depth]; rfl
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      have := ih H; revert this
      simp [VLCtx.varToExpr, Expr.instantiate1']; split <;> [skip; split]
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
    TrExprS env Us Δ (Expr.instantiate1' e e₀ dk) (e'.inst e₀' k) := by
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
    refine .lit (Expr.instantiate1'_eq_self ?_ ▸ ih W :)
    exact Closed.toConstructor.looseBVarRange_le
  | mdata _ ih => exact .mdata (ih W)
  | proj _ h2 ih => exact .proj (ih W) (h2.instN W.toCtx)

theorem TrExprS.inst {Δ : VLCtx} (henv : Ordered env)
    (t₀ : env.HasType Us.length Δ.toCtx e₀' A₀)
    (H : TrExprS env Us ((none, .vlam A₀) :: Δ) e e')
    (h₀ : TrExprS env Us Δ e₀ e₀') :
    TrExprS env Us Δ (e.instantiate1' e₀) (e'.inst e₀') :=
  h₀.instN henv t₀ .zero H

theorem TrExpr.inst (henv : VEnv.WF env) (hΔ : VLCtx.WF env Us.length Δ)
    (t₀ : env.HasType Us.length Δ.toCtx e₀' A₀)
    (H : TrExpr env Us ((none, .vlam A₀) :: Δ) e e')
    (h₀ : TrExpr env Us Δ e₀ e₀') :
    TrExpr env Us Δ (e.instantiate1' e₀) (e'.inst e₀') :=
  have ⟨_, h0⟩ := t₀.isType henv hΔ
  have ⟨_, s1, _, h1⟩ := H
  have ⟨_, s2, h2⟩ := h₀
  have h2' := h2.symm.of_l henv hΔ t₀
  have hΔΔ := VLCtx.IsDefEq.cons (.refl henv hΔ) (ofv := none) nofun (.vlam h0)
  let ⟨_, s1'⟩ := s1.defeqDFC henv hΔΔ
  let ⟨_, h1'⟩ := s1.uniq henv hΔΔ s1'
  ⟨_, .inst henv h2'.hasType.2 s1' s2, _,
    .instDF henv hΔ (h1'.symm.trans_l henv hΔΔ.wf.toCtx h1) h2'.symm⟩

variable! (henv : Ordered env) (h₀ : TrExprS env Us Δ₀ e₀ e₀') in
theorem TrExprS.instN_let_var (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ)
    (H : Δ₁.find? v = some (e', A)) :
    TrExprS env Us Δ (Expr.instantiate1' (VLCtx.varToExpr v) e₀ dk) e' := by
  induction W generalizing v e' A with
  | zero =>
    obtain (_|i)|fv := v <;> simp [VLCtx.varToExpr, Expr.instantiate1', Expr.liftLooseBVars_zero]
    · cases H; simp [VLocalDecl.value]; exact h₀
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      simp [VLocalDecl.depth]
      exact .bvar H
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      simp [VLocalDecl.depth]
      exact .fvar H
  | @succ _ k _ _ d _ ih =>
    obtain (_|i)|fv := v <;> simp [VLCtx.varToExpr, Expr.instantiate1']
    · cases H
      cases d <;> exact .bvar <| by simp [VLocalDecl.value]; rfl
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      have := ih H; revert this
      simp [VLCtx.varToExpr, Expr.instantiate1']; split <;> [skip; split]
      · intro | .bvar h => ?_
        exact .bvar <| by
          simp [VLCtx.find?, VLCtx.next]
          refine ⟨_, _, h, ?_, rfl⟩
          cases d <;> simp [VLocalDecl.depth]
      · intro H
        have := Expr.liftLooseBVars_add ▸ H.weakBV henv (.skip d .refl)
        cases d <;> simpa [VLocalDecl.depth] using this
      · obtain _|i := i; · omega
        intro | .bvar h => ?_
        exact .bvar <| by
          simp [VLCtx.find?, VLCtx.next]
          refine ⟨_, _, h, ?_, rfl⟩
          cases d <;> simp [VLocalDecl.depth]
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      have .fvar h := ih H
      exact .fvar <| by
        simp [VLCtx.find?, VLCtx.next]
        refine ⟨_, _, h, ?_, rfl⟩
        cases d <;> simp [VLocalDecl.depth]

variable! (henv : Ordered env) (h₀ : TrExprS env Us Δ₀ e₀ e₀') in
theorem TrExprS.instN_let (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ) (H : TrExprS env Us Δ₁ e e') :
    TrExprS env Us Δ (Expr.instantiate1' e e₀ dk) e' := by
  induction H generalizing Δ dk k with
  | bvar h1 | fvar h1 => exact instN_let_var henv h₀ W h1
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (W.toCtx ▸ h1) (W.toCtx ▸ h2) (ih1 W) (ih2 W)
  | lam h1 _ _ ih1 ih2 =>
    exact .lam (W.toCtx ▸ h1) (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (W.toCtx ▸ h1) (W.toCtx ▸ h2)
      (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (W.toCtx ▸ h1) (ih1 W) (ih2 W) (ih3 (W.succ (d := .vlet ..)))
  | lit _ ih =>
    refine .lit (Expr.instantiate1'_eq_self ?_ ▸ ih W :)
    exact Closed.toConstructor.looseBVarRange_le
  | mdata _ ih => exact .mdata (ih W)
  | proj _ h2 ih => exact .proj (ih W) (W.toCtx ▸ h2)

theorem TrExprS.inst_let {Δ : VLCtx} (henv : Ordered env)
    (H : TrExprS env Us ((none, .vlet A₀ e₀') :: Δ) e e')
    (h₀ : TrExprS env Us Δ e₀ e₀') :
    TrExprS env Us Δ (e.instantiate1' e₀) e' :=
  h₀.instN_let henv .zero H

theorem TrExpr.inst_let (henv : VEnv.WF env) (hΔ : VLCtx.WF env Us.length Δ)
    (t₀ : env.HasType Us.length Δ.toCtx e₀' A₀)
    (H : TrExpr env Us ((none, .vlet A₀ e₀') :: Δ) e e')
    (h₀ : TrExpr env Us Δ e₀ e₀') :
    TrExpr env Us Δ (e.instantiate1' e₀) e' :=
  have ⟨_, h0⟩ := t₀.isType henv hΔ
  have ⟨_, s1, _, h1⟩ := H
  have ⟨_, s2, h2⟩ := h₀
  have h2' := h2.symm.of_l henv hΔ t₀
  have hΔΔ := VLCtx.IsDefEq.cons (.refl henv hΔ) (ofv := none) nofun (.vlet h2' h0)
  let ⟨_, s1'⟩ := s1.defeqDFC henv hΔΔ
  let ⟨_, h1'⟩ := s1.uniq henv hΔΔ s1'
  ⟨_, .inst_let henv s1' s2, _, h1'.symm.trans_l henv hΔ h1⟩

theorem ofLevel_mkLevelMax'
    (h1 : VLevel.ofLevel Us u = some u') (h2 : VLevel.ofLevel Us v = some v') :
    ∃ w, VLevel.ofLevel Us (mkLevelMax' u v) = some w ∧ w ≈ .max u' v' := by
  let subsumes (u v : Level) : Bool :=
    if v.isExplicit && u.getOffset ≥ v.getOffset then true
    else match u with
      | Level.max u₁ u₂ => v == u₁ || v == u₂
      | _ => false
  let mkLevelMaxCore (u v : Level) :=
    if u == v then u
    else if u.isZero then v
    else if v.isZero then u
    else if subsumes u v then u
    else if subsumes v u then v
    else if u.getLevelOffset == v.getLevelOffset then
      if u.getOffset ≥ v.getOffset then u else v
    else
      .max u v
  change ∃ w, VLevel.ofLevel Us (mkLevelMaxCore u v) = some w ∧ w ≈ .max u' v'
  have le {u v u' v'} (h : subsumes u v)
      (hu : VLevel.ofLevel Us u = some u')
      (hv : VLevel.ofLevel Us v = some v') : v'.LE u' := by
    simp [subsumes] at h
    obtain ⟨h1, h2⟩ | h := h
    · clear subsumes mkLevelMaxCore
      induction v generalizing u u' v' with simp [VLevel.ofLevel] at hv h2 ⊢
      | zero => subst v'; exact VLevel.zero_le
      | succ _ ih =>
        obtain ⟨_, hv, rfl⟩ := hv
        generalize eq : u.getOffset' = n at h2
        unfold Level.getOffset' at eq; split at eq <;> subst eq <;> [skip; cases h2]
        simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, rfl⟩ := hu
        simp [Level.isExplicit] at h1
        exact VLevel.succ_le_succ (ih hu hv h1.2 (Nat.le_of_succ_le_succ h2))
      | _ => cases h1
    · split at h <;> [skip; cases h]
      simp [VLevel.ofLevel] at hu; obtain ⟨_, hu1, _, hu2, rfl⟩ := hu
      simp at h; obtain rfl | rfl := h
      · cases hv.symm.trans hu1
        exact VLevel.le_max_left
      · cases hv.symm.trans hu2
        exact VLevel.le_max_right
  simp only [mkLevelMaxCore]; split
  · simp_all; exact VLevel.max_self.symm
  split
  · let .zero := u; simp [VLevel.ofLevel] at h1; subst u'
    exact ⟨_, h2, VLevel.zero_le.max_eq_right.symm⟩
  split
  · let .zero := v; simp [VLevel.ofLevel] at h2; subst v'
    exact ⟨_, h1, VLevel.zero_le.max_eq_left.symm⟩
  split
  · exact ⟨_, h1, (le ‹_› h1 h2).max_eq_left.symm⟩
  split
  · exact ⟨_, h2, (le ‹_› h2 h1).max_eq_right.symm⟩
  split
  · rename_i h
    simp at h ⊢
    let rec lem1 {v : Level} {u' v'}
        (hu : VLevel.ofLevel Us v.getLevelOffset = some u')
        (hv : VLevel.ofLevel Us v = some v') : u'.LE v' := by
      unfold Level.getLevelOffset at hu; split at hu
      · simp [VLevel.ofLevel] at hv; obtain ⟨_, hv, rfl⟩ := hv
        exact VLevel.le_trans (lem1 hu hv) VLevel.le_succ
      · cases hu.symm.trans hv; exact VLevel.le_refl _
    let rec lem2 {u v : Level} {u' v'}
        (h1 : u.getLevelOffset = v.getLevelOffset)
        (h2 : u.getOffset' ≤ v.getOffset')
        (hu : VLevel.ofLevel Us u = some u')
        (hv : VLevel.ofLevel Us v = some v') : u'.LE v' := by
      revert h1 h2; unfold Level.getLevelOffset Level.getOffset'
      split <;> simp <;> split <;> (try simp)
      · simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, rfl⟩ := hu
        simp [VLevel.ofLevel] at hv; obtain ⟨_, hv, rfl⟩ := hv
        exact (VLevel.succ_le_succ <| lem2 · · hu hv)
      · rintro rfl; exact lem1 (v := .succ _) hu hv
      · rintro rfl; cases hu.symm.trans hv; exact VLevel.le_refl _
    split <;> rename_i h3
    · exact ⟨_, h1, (lem2 h.symm h3 h2 h1).max_eq_left.symm⟩
    · exact ⟨_, h2, (lem2 h (Nat.le_of_not_le h3) h1 h2).max_eq_right.symm⟩
  simp [VLevel.ofLevel]; exact ⟨_, ⟨_, h1, _, h2, rfl⟩, rfl⟩

theorem ofLevel_isNeverZero (h : VLevel.ofLevel Us u = some u') (H : u.isNeverZero) :
    u'.IsNeverZero := by
  induction u generalizing u' with simp [Level.isNeverZero, VLevel.ofLevel] at H h <;> intro ls
  | succ =>
    obtain ⟨_, h1, rfl⟩ := h
    exact Nat.succ_ne_zero _
  | max _ _ ih1 ih2 =>
    obtain ⟨_, h1, _, h2, rfl⟩ := h
    intro h
    rw [VLevel.eval, ← Nat.le_zero, Nat.max_le] at h; simp at h
    exact H.elim (ih1 h1 · _ h.1) (ih2 h2 · _ h.2)
  | imax _ _ ih1 ih2 =>
    obtain ⟨_, h1, _, h2, rfl⟩ := h
    simp [VLevel.eval, Nat.imax, ih2 h2 H ls]

theorem ofLevel_mkLevelIMax'
    (h1 : VLevel.ofLevel Us u = some u') (h2 : VLevel.ofLevel Us v = some v') :
    ∃ w, VLevel.ofLevel Us (mkLevelIMax' u v) = some w ∧ w ≈ .imax u' v' := by
  let mkLevelIMaxCore (u v : Level) :=
    if v.isNeverZero then mkLevelMax' u v
    else if v.isZero then v
    else if u.isZero then v
    else if u == v then u
    else .imax u v
  change ∃ w, VLevel.ofLevel Us (mkLevelIMaxCore u v) = some w ∧ w ≈ .imax u' v'
  simp only [mkLevelIMaxCore]; split
  · have ⟨_, a1, a2⟩ := ofLevel_mkLevelMax' h1 h2
    exact ⟨_, a1, .trans a2 (ofLevel_isNeverZero h2 ‹_›).imax_eq_max.symm⟩
  split
  · let .zero := v; simp [VLevel.ofLevel] at h2; subst v'
    exact ⟨.zero, rfl, rfl⟩
  split
  · let .zero := u; simp [VLevel.ofLevel] at h1; subst u'
    exact ⟨_, h2, VLevel.zero_imax.symm⟩
  split
  · simp_all; exact VLevel.imax_self.symm
  simp [VLevel.ofLevel]; exact ⟨_, ⟨_, h1, _, h2, rfl⟩, rfl⟩

variable! {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U') in
theorem TrProj.instL (H : TrProj Γ s i e e') :
    TrProj (Γ.map (VExpr.instL ls)) s i (e.instL ls) (e'.instL ls) := sorry

section

variable (henv : VEnv.WF env) {Us ps : List Name} {ls : List Level} {ls' : List VLevel}
  (hΔ : VLCtx.WF env ls'.length Δ)
  (Hls : ls.mapM (VLevel.ofLevel Us) = some ls')
  (eq : ps.length = ls.length)

include Hls eq

section
variable (eqF : (fun x => ((List.idxOf? x ps).bind fun x => ls[x]?).getD (Level.param x)) = F)
include eqF

attribute [-simp] Bool.forall_bool in
theorem substParams_wf (red) (H : VLevel.ofLevel ps u = some u') :
    ∃ u₁, VLevel.ofLevel Us (u.substParams' F red) = some u₁ ∧ u₁ ≈ u'.inst ls' := by
  induction u generalizing u' red with simp_all [VLevel.ofLevel, Level.substParams']
  | zero => subst u'; rfl
  | succ _ ih =>
    obtain ⟨_, H, rfl⟩ := H
    exact let ⟨_, h1, h2⟩ := ih _ H; ⟨_, ⟨_, h1, rfl⟩, VLevel.succ_congr h2⟩
  | max _ _ ih1 ih2 =>
    obtain ⟨_, H1, _, H2, rfl⟩ := H
    generalize (_ && _) = red'
    let ⟨_, a1, a2⟩ := ih1 (red := red') H1
    let ⟨_, b1, b2⟩ := ih2 (red := red') H2
    split
    · have ⟨w, c1, c2⟩ := ofLevel_mkLevelMax' a1 b1
      exact ⟨_, c1, .trans c2 <| VLevel.max_congr a2 b2⟩
    · simp [VLevel.ofLevel]
      exact ⟨_, ⟨_, a1, _, b1, rfl⟩, VLevel.max_congr a2 b2⟩
  | imax _ _ ih1 ih2 =>
    obtain ⟨_, H1, _, H2, rfl⟩ := H
    generalize (_ && _) = red'
    let ⟨_, a1, a2⟩ := ih1 (red := red') H1
    let ⟨_, b1, b2⟩ := ih2 (red := red') H2
    split
    · have ⟨w, c1, c2⟩ := ofLevel_mkLevelIMax' a1 b1
      exact ⟨_, c1, .trans c2 <| VLevel.imax_congr a2 b2⟩
    · simp [VLevel.ofLevel]
      exact ⟨_, ⟨_, a1, _, b1, rfl⟩, VLevel.imax_congr a2 b2⟩
  | param x =>
    obtain ⟨H, rfl⟩ := H; subst eqF; simp
    have := List.idxOf_eq_idxOf? x ps; revert this
    split <;> simp [*, Nat.ne_of_lt, VLevel.inst]; rintro rfl; clear ‹_› eq
    generalize List.idxOf x ps = n at *
    rw [List.mapM_eq_some] at Hls
    induction Hls generalizing n with
    | nil => cases H
    | cons Hl _ ih =>
      obtain _|n := n <;> simp
      · exact ⟨_, Hl, rfl⟩
      · exact ih _ (Nat.lt_of_succ_lt_succ H)

theorem substParams_wf_list (red) {us us' : List _} (H : us.mapM (VLevel.ofLevel ps) = some us') :
    ∃ us₁, (us.map (Level.substParams' F red)).mapM (VLevel.ofLevel Us) = some us₁ ∧
      List.Forall₂ (· ≈ ·) us₁ (us'.map (·.inst ls')) := by
  induction us generalizing us' with simp_all
  | cons u us ih =>
    obtain ⟨_, H1, _, H2, rfl⟩ := H
    have ⟨_, h1, h2⟩ := ih H2
    have ⟨_, h3, h4⟩ := substParams_wf Hls eq eqF red H1
    refine ⟨_, ⟨_, h3, _, h1, rfl⟩, .cons h4 h2⟩

end

include henv hΔ

theorem TrExprS.instL (H : TrExprS env ps Δ e e') :
    TrExpr env Us (Δ.instL ls') (e.instantiateLevelParams ps ls) (e'.instL ls') := by
  simp [Expr.instantiateLevelParams_eq]
  generalize (_ && _) = red, eqF : (fun x : Name => _) = F
  have Hls' := VLevel.WF.of_mapM_ofLevel Hls
  have eq' := eq.trans (List.mapM_eq_some.1 Hls).length_eq
  induction H with
  | bvar h1 => exact (bvar (VLCtx.find?_instL h1)).trExpr henv (hΔ.instL Hls')
  | fvar h1 => exact (fvar (VLCtx.find?_instL h1)).trExpr henv (hΔ.instL Hls')
  | sort h1 =>
    simp [Expr.instantiateLevelParamsCore']
    have ⟨_, a1, a2⟩ := substParams_wf Hls eq eqF red h1
    exact ⟨_, .sort a1, _, .sortDF (.of_ofLevel a1) (.inst Hls') a2⟩
  | const h1 h2 h3 =>
    have ⟨_, a1, a2⟩ := substParams_wf_list Hls eq eqF red h2
    refine ⟨_, .const h1 a1 (by simp [h3]), _, .constDF h1 (.of_mapM_ofLevel a1) ?_ ?_ a2⟩
    · simp; exact fun _ _ => .inst Hls'
    · simp [← (List.mapM_eq_some.1 a1).length_eq, h3]
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app henv (hΔ.instL Hls')
      (VLCtx.instL_toCtx _ ▸ h1.instL Hls')
      (VLCtx.instL_toCtx _ ▸ h2.instL Hls') (ih1 hΔ) (ih2 hΔ)
  | lam h1 h2 _ ih1 ih2 =>
    exact .lam henv (hΔ.instL Hls')
      (VLCtx.instL_toCtx _ ▸ h1.instL Hls') (ih1 hΔ) (ih2 ⟨hΔ, nofun, eq' ▸ h1⟩)
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE henv (hΔ.instL Hls')
      (VLCtx.instL_toCtx _ ▸ h1.instL Hls')
      (VLCtx.instL_toCtx _ ▸ h2.instL Hls') (ih1 hΔ) (ih2 ⟨hΔ, nofun, eq' ▸ h1⟩)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE henv (hΔ.instL Hls')
      (VLCtx.instL_toCtx _ ▸ h1.instL Hls') (ih1 hΔ) (ih2 hΔ) (ih3 ⟨hΔ, nofun, eq' ▸ h1⟩)
  | lit _ ih =>
    refine .lit (Expr.instantiateLevelParamsCore_eq_self ?_ ▸ ih hΔ :)
    exact Literal.toConstructor_hasLevelParam
  | mdata _ ih => exact .mdata (ih hΔ)
  | proj _ h2 ih =>
    exact .proj henv (hΔ.instL Hls') (ih hΔ)
      (VLCtx.instL_toCtx _ ▸ h2.instL Hls')

theorem TrExpr.instL (H : TrExpr env ps Δ e e') :
    TrExpr env Us (Δ.instL ls') (e.instantiateLevelParams ps ls) (e'.instL ls') :=
  let ⟨_, s1, h1⟩ := H
  have Hls' := .of_mapM_ofLevel Hls
  (s1.instL henv hΔ Hls eq).defeq henv (hΔ.instL Hls') (VLCtx.instL_toCtx _ ▸ h1.instL Hls')

end

theorem TrExprS.abstract (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ) (H : TrExprS env Us Δ₁ e e') :
    TrExprS env Us Δ (e.abstract1 v₀ dk) e' := by
  induction H generalizing dk k Δ with
  | bvar h1 =>
    exact .bvar <| (W.find? (by nofun)).trans <| by
      simp; split <;> [skip; rw [if_neg (by omega), if_neg (by omega)]] <;> exact h1
  | @fvar _ _ _ fv h1 =>
    if h : fv = v₀ then
      rw [h, W.find?_self] at h1; cases h1
      rw [Expr.abstract1, if_pos (by simp [h])]
      exact .bvar <| (W.find? (by nofun)).trans (by simpa using W.find?_self)
    else
      have := W.find? (v := .inr fv) (by rintro ⟨⟩; trivial)
      simp at this
      rw [Expr.abstract1, if_neg]
      · exact .fvar (this.trans h1)
      · simp; rintro rfl; trivial
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 => exact .app (W.toCtx ▸ h1) (W.toCtx ▸ h2) (ih1 W) (ih2 W)
  | lam h1 _ _ ih1 ih2 => exact .lam (W.toCtx ▸ h1) (ih1 W) (ih2 W.succ)
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (W.toCtx ▸ h1) (W.toCtx ▸ h2) (ih1 W) (ih2 W.succ)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (W.toCtx ▸ h1) (ih1 W) (ih2 W) (ih3 W.succ)
  | lit _ ih =>
    exact .lit (FVarsIn.toConstructor.abstract_eq_self .toConstructor ▸ ih W)
  | mdata _ ih => exact .mdata (ih W)
  | proj _ h2 ih => exact .proj (ih W) (W.toCtx ▸ h2)

theorem TrExpr.abstract (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ) (H : TrExpr env Us Δ₁ e e') :
    TrExpr env Us Δ (e.abstract1 v₀ dk) e' :=
  let ⟨_, s, h⟩ := H; ⟨_, s.abstract W, W.toCtx ▸ h⟩

def TrExprS.IsUnique : Expr → Prop
  | .bvar _
  | .fvar _
  | .sort _
  | .const ..
  | .mvar ..
  | .lit _ => True
  | .app f a => IsUnique f ∧ IsUnique a
  | .lam _ t b _ => IsUnique t ∧ IsUnique b
  | .forallE _ t b _ => IsUnique t ∧ IsUnique b
  | .letE _ _ v b _ => IsUnique v ∧ IsUnique b
  | .mdata _ e => IsUnique e
  | .proj .. => False

theorem TrExprS.IsUnique.natLitToConstructor : ∀ {n : Nat}, IsUnique (.natLitToConstructor n)
  | 0 => ⟨⟩
  | _+1 => ⟨⟨⟩, ⟨⟩⟩

theorem TrExprS.IsUnique.strLitToConstructor {s : String} : IsUnique (.strLitToConstructor s) := by
  refine ⟨⟨⟩, ?_⟩; simp [String.foldr_eq]
  induction s.data with simp
  | nil => exact ⟨⟨⟩, ⟨⟩⟩
  | cons _ _ ih => exact ⟨⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟨⟩, ⟨⟩⟩⟩, ih⟩

theorem TrExprS.IsUnique.toConstructor : ∀ {l : Literal}, IsUnique l.toConstructor
  | .natVal _ => .natLitToConstructor
  | .strVal _ => .strLitToConstructor

inductive TrExprS.IsUniqueDecl : VLocalDecl → VLocalDecl → Prop
  | vlam : IsUniqueDecl (.vlam ty) (.vlam ty')
  | vlet : IsUniqueDecl (.vlet ty val) (.vlet ty' val)

inductive TrExprS.IsUniqueCtx : VLCtx → VLCtx → Prop
  | base : IsUniqueCtx Δ Δ
  | cons : IsUniqueCtx Δ₁ Δ₂ → IsUniqueDecl d₁ d₂ → IsUniqueCtx ((ofv, d₁) :: Δ₁) ((ofv, d₂) :: Δ₂)

theorem TrExprS.IsUniqueCtx.find?_uniq (hΔ : IsUniqueCtx Δ₁ Δ₂)
    (H1 : Δ₁.find? v = some (e₁, A₁)) (H2 : Δ₂.find? v = some (e₂, A₂)) : e₁ = e₂ := by
  induction hΔ generalizing v e₁ e₂ A₁ A₂ with
  | base => cases H1.symm.trans H2; rfl
  | @cons _ _ _ _ ofv _ hd ih =>
    revert H1 H2; simp [VLCtx.find?]; split
    · rintro ⟨⟩ ⟨⟩; cases hd <;> rfl
    · simp; rintro _ _ h1 rfl rfl _ _ h2 rfl rfl
      congr 1
      · cases hd <;> rfl
      · exact ih h1 h2

theorem TrExprS.unique' (hΔ : IsUniqueCtx Δ₁ Δ₂) (H : IsUnique e)
    (H1 : TrExprS env Us Δ₁ e e₁) (H2 : TrExprS env Us Δ₂ e e₂) : e₁ = e₂ := by
  induction H1 generalizing Δ₂ e₂ with cases H2
  | bvar => exact hΔ.find?_uniq ‹_› ‹_›
  | fvar => exact hΔ.find?_uniq ‹_› ‹_›
  | sort h1
  | const _ h1 => cases h1.symm.trans ‹_›; rfl
  | app _ _ _ _ ih1 ih2 => cases ih1 hΔ H.1 ‹_›; cases ih2 hΔ H.2 ‹_›; rfl
  | lam _ _ _ ih1 ih2
  | forallE _ _ _ _ ih1 ih2 => cases ih1 hΔ H.1 ‹_›; cases ih2 (hΔ.cons .vlam) H.2 ‹_›; rfl
  | letE _ _ _ _ _ ih1 ih2 => cases ih1 hΔ H.1 ‹_›; cases ih2 (hΔ.cons .vlet) H.2 ‹_›; rfl
  | lit _ ih => exact ih hΔ .toConstructor ‹_›
  | mdata _ ih => exact ih hΔ H ‹_›
  | proj => cases H

theorem TrExprS.unique (H : IsUnique e)
    (H1 : TrExprS env Us Δ e e₁) (H2 : TrExprS env Us Δ e e₂) : e₁ = e₂ := H1.unique' .base H H2

theorem TrExprS.lit_has_type (wf : env.Ordered) (henv : env.HasPrimitives)
    (H : TrExprS env Us Δ (.lit l) e') : env.contains l.typeName := by
  match l with
  | .natVal n =>
    induction n generalizing e' with
    | zero =>
      let .lit H := H
      let .const H .. := H
      have ⟨_, H⟩ := wf.constWF (henv.natZero H ▸ H)
      have ⟨_, H, _⟩ := H.const_inv wf trivial
      exact ⟨_, H⟩
    | succ _ ih =>
      let .lit H1 := H
      let .app _ _ _ H1 := H1
      exact ih H1
  | .strVal s =>
    let .lit H := H
    let .app _ _ H _ := H
    let .const H .. := H
    let ⟨_, H⟩ := wf.constWF (henv.stringMk H ▸ H)
    let ⟨H1, _, H⟩ := H.forallE_inv wf
    let ⟨_, H, _⟩ := H.const_inv wf (by exact ⟨trivial, H1⟩)
    exact ⟨_, H⟩

theorem TrExprS.natZero (henv : env.HasPrimitives) (H : env.contains ``Nat) :
    TrExprS env Us Δ .natZero .natZero ∧ env.HasType Us.length Δ.toCtx .natZero .nat := by
  let ⟨⟨_, H⟩, _⟩ := henv.nat H
  cases henv.natZero H
  exact ⟨.const H rfl rfl, .const H nofun rfl⟩

theorem TrExprS.natSucc (henv : env.HasPrimitives) (H : env.contains ``Nat) :
    TrExprS env Us Δ .natSucc .natSucc ∧
    env.HasType Us.length Δ.toCtx .natSucc (.forallE .nat .nat) := by
  let ⟨_, _, H⟩ := henv.nat H
  cases henv.natSucc H
  exact ⟨.const H rfl rfl, .const H nofun rfl⟩

theorem TrExprS.natLit (henv : env.HasPrimitives) (H : env.contains ``Nat) :
    TrExprS env Us Δ (.lit (.natVal n)) (.natLit n) ∧
    env.HasType Us.length Δ.toCtx (.natLit n) .nat := by
  induction n with
  | zero => exact let ⟨h1, h2⟩ := natZero henv H; ⟨.lit h1, h2⟩
  | succ n ih => exact let ⟨h1, h2⟩ := natSucc henv H; ⟨.lit (.app h2 ih.2 h1 ih.1), .app h2 ih.2⟩

theorem TrExprS.stringMk (henv : env.HasPrimitives) (H : env.contains ``String) :
    TrExprS env Us Δ (.const ``String.mk []) .stringMk ∧
    env.HasType Us.length Δ.toCtx .stringMk (.forallE .listChar .string) := by
  let ⟨⟨_, H⟩, _⟩ := henv.string H
  cases henv.stringMk H
  exact ⟨.const H rfl rfl, .const H nofun rfl⟩

theorem TrExprS.charOfNat (wf : env.Ordered) (henv : env.HasPrimitives)
    (H : env.contains ``String) :
    TrExprS env Us Δ (.const ``Char.ofNat []) .charOfNat ∧
    env.HasType Us.length Δ.toCtx .charOfNat (.forallE .nat .char) := by
  let ⟨_, _, _, H⟩ := henv.string H
  let ⟨_, H1, _, H3⟩ := H.const_inv wf trivial
  exact ⟨.const H1 rfl H3, (H.instL (ls := []) nofun).weak0 wf⟩

theorem VEnv.HasPrimitives.nat_of_string (wf : Ordered env) (henv : env.HasPrimitives)
    (H : env.contains ``String) : env.contains ``Nat := by
  let ⟨_, _, _, H⟩ := henv.string H
  let ⟨_, H⟩ := H.isType wf trivial
  let ⟨⟨_, H⟩, _⟩ := H.forallE_inv wf
  let ⟨_, H, _⟩ := H.const_inv wf trivial
  exact ⟨_, H⟩

theorem TrExprS.listChar (wf : env.Ordered) (henv : env.HasPrimitives) (H : env.contains ``String) :
    TrExprS env Us Δ (.app (.const ``List [.zero]) (.const ``Char [])) .listChar ∧
    env.IsType Us.length Δ.toCtx .listChar := by
  let ⟨⟨_, H⟩, _⟩ := henv.string H
  let ⟨_, H⟩ := wf.constWF (henv.stringMk H ▸ H)
  let ⟨⟨_, H⟩, _⟩ := H.forallE_inv wf
  refine ⟨?_, _, (H.instL (ls := []) nofun).weak0 wf⟩
  let ⟨_, _, A, B⟩ := H.app_inv wf trivial
  let ⟨_, A1, _, A3⟩ := A.const_inv wf trivial
  let ⟨_, B1, _, B3⟩ := B.const_inv wf trivial
  exact .app ((A.instL (ls := []) nofun).weak0 wf) ((B.instL (ls := []) nofun).weak0 wf)
    (.const A1 rfl A3) (.const B1 rfl B3)

theorem TrExprS.listCharNil (wf : env.Ordered) (henv : env.HasPrimitives)
    (H : env.contains ``String) :
    TrExprS env Us Δ (.app (.const ``List.nil [.zero]) (.const ``Char [])) .listCharNil ∧
    env.HasType Us.length Δ.toCtx .listCharNil .listChar := by
  let ⟨_, H, _⟩ := henv.string H
  refine ⟨?_, (H.instL (ls := []) nofun).weak0 wf⟩
  let ⟨_, _, A, B⟩ := H.app_inv wf trivial
  let ⟨_, A1, _, A3⟩ := A.const_inv wf trivial
  let ⟨_, B1, _, B3⟩ := B.const_inv wf trivial
  exact .app ((A.instL (ls := []) nofun).weak0 wf) ((B.instL (ls := []) nofun).weak0 wf)
    (.const A1 rfl A3) (.const B1 rfl B3)

theorem TrExprS.listCharCons (wf : env.Ordered) (henv : env.HasPrimitives)
    (H : env.contains ``String) :
    TrExprS env Us Δ (.app (.const ``List.cons [.zero]) (.const ``Char [])) .listCharCons ∧
    env.HasType Us.length Δ.toCtx .listCharCons
      (.forallE .char <| .forallE .listChar .listChar) := by
  let ⟨_, _, H, _⟩ := henv.string H
  refine ⟨?_, (H.instL (ls := []) nofun).weak0 wf⟩
  let ⟨_, _, A, B⟩ := H.app_inv wf trivial
  let ⟨_, A1, _, A3⟩ := A.const_inv wf trivial
  let ⟨_, B1, _, B3⟩ := B.const_inv wf trivial
  exact .app ((A.instL (ls := []) nofun).weak0 wf) ((B.instL (ls := []) nofun).weak0 wf)
    (.const A1 rfl A3) (.const B1 rfl B3)

theorem TrExprS.listCharLit (wf : env.Ordered) (henv : env.HasPrimitives)
    (H : env.contains ``String) (s : List Char) :
    TrExprS env Us Δ (s.foldr
      (init := .app (.const ``List.nil [.zero]) (.const ``Char []))
      (fun c e => .app (.app
        (.app (.const ``List.cons [.zero]) (.const ``Char []))
        (.app (.const ``Char.ofNat []) (.lit (.natVal c.toNat)))) e)) (.listCharLit s) ∧
    env.HasType Us.length Δ.toCtx (.listCharLit s) .listChar := by
  induction s with
  | nil => exact TrExprS.listCharNil wf henv H
  | cons x _ ih =>
    have a := TrExprS.listCharCons wf henv H (Us := Us) (Δ := Δ)
    have b := TrExprS.charOfNat wf henv H (Us := Us) (Δ := Δ)
    have c := TrExprS.natLit henv (henv.nat_of_string wf H) (Us := Us) (Δ := Δ) (n := x.toNat)
    have d1 := b.1.app b.2 c.2 c.1; have d2 := b.2.app c.2
    have e1 := a.1.app a.2 d2 d1; have e2 := a.2.app d2
    exact ⟨e1.app e2 ih.2 ih.1, e2.app ih.2⟩

theorem TrExprS.trLiteral (wf : env.Ordered) (henv : env.HasPrimitives)
    (H : env.contains l.typeName) :
    TrExprS env Us Δ (.lit l) (.trLiteral l) ∧
    env.HasType Us.length Δ.toCtx (.trLiteral l) (.const l.typeName []) := by
  match l with
  | .natVal n => exact TrExprS.natLit henv H
  | .strVal s =>
    have a := TrExprS.stringMk henv H (Us := Us) (Δ := Δ)
    have b := TrExprS.listCharLit wf henv H (Us := Us) (Δ := Δ) s.data
    exact ⟨.lit (.app a.2 b.2 a.1 (String.foldr_eq .. ▸ b.1)), a.2.app b.2⟩

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
  | (some (fv, deps), _) :: (Δ : VLCtx) =>
    IsFVarUpSet P Δ ∧
    (P fv → ∀ fv' ∈ deps, P fv')

theorem IsFVarUpSet.congr : ∀ {Δ}, VLCtx.FVWF Δ →
    (H : ∀ fv ∈ VLCtx.fvars Δ, P fv ↔ Q fv) → IsFVarUpSet P Δ ↔ IsFVarUpSet Q Δ
  | [], _, _ => .rfl
  | (none, _) :: Δ, ⟨h1, _⟩, H => congr (Δ := Δ) h1 H
  | (some (fv, deps), d) :: (Δ : VLCtx), ⟨h1, h2⟩, H => by
    refine and_congr (congr h1 fun fv h => H _ (.tail _ h)) (imp_congr (H _ (.head _)) ?_)
    refine forall_congr' fun fv => imp_congr_right fun h => ?_
    exact H _ (by simp [(h2 _ _ rfl).2 h])

theorem IsFVarUpSet.and_fvars (H : VLCtx.FVWF Δ) :
    IsFVarUpSet P Δ ↔ IsFVarUpSet (fun fv => P fv ∧ fv ∈ Δ.fvars) Δ :=
  IsFVarUpSet.congr H fun _ h => (and_iff_left h).symm

theorem IsFVarUpSet.trivial : ∀ {Δ}, IsFVarUpSet (fun _ => True) Δ
  | [] => ⟨⟩
  | (none, _) :: Δ => trivial (Δ := Δ)
  | (some _, _) :: _ => ⟨trivial, fun _ _ _ => ⟨⟩⟩

theorem IsFVarUpSet.fvars (H : VLCtx.FVWF Δ) : IsFVarUpSet (· ∈ Δ.fvars) Δ :=
  (IsFVarUpSet.congr H fun _ => iff_true_intro).2 trivial

def AllAbove (Δ : VLCtx) (P : FVarId → Prop) (fv : FVarId) : Prop := fv ∈ Δ.fvars → P fv

theorem AllAbove.wf (H : Δ.FVWF) : IsFVarUpSet (AllAbove Δ P) Δ ↔ IsFVarUpSet P Δ :=
  IsFVarUpSet.congr H fun _ h => by simp [h, AllAbove]

def FVarsBelow (Δ e e') := ∀ P, IsFVarUpSet P Δ → FVarsIn P e → FVarsIn P e'

theorem FVarsBelow.rfl : FVarsBelow Δ e e := fun _ _ => id

theorem FVarsBelow.trans (H1 : FVarsBelow Δ e₁ e₂) (H2 : FVarsBelow Δ e₂ e₃) :
    FVarsBelow Δ e₁ e₃ := fun _ h => H2 _ h ∘ H1 _ h

def TrTyping (env : VEnv) (Us : List Name) (Δ : VLCtx) (e A : Expr) (e' A' : VExpr) : Prop :=
  FVarsBelow Δ e A ∧ TrExprS env Us Δ e e' ∧ TrExprS env Us Δ A A' ∧
  env.HasType Us.length Δ.toCtx e' A'

inductive LambdaBodyN : Nat → Expr → Expr → Prop
  | zero : LambdaBodyN 0 e e
  | succ : LambdaBodyN n body e → LambdaBodyN (n+1) (.lam i ty body bi) e

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

theorem BetaReduce.appList (H : BetaReduce f f') :
    BetaReduce (f.mkAppList es) (f'.mkAppList es) := by
  induction es generalizing f f' with
  | nil => exact H
  | cons _ _ ih => exact ih (.app H)

theorem FVarsBelow.betaReduce (H : BetaReduce e e') : FVarsBelow Δ e e' := by
  intro P hP he
  induction H with
  | refl => exact he
  | trans _ _ ih1 ih2 => exact ih2 (ih1 he)
  | app _ ih => exact ⟨ih he.1, he.2⟩
  | beta => exact he.1.2.instantiate1 he.2

theorem BetaReduce.cheapBetaReduce (hc : e.Closed) : BetaReduce e e.cheapBetaReduce := by
  simp [Expr.cheapBetaReduce]
  split; · exact .refl
  split; · exact .refl
  let rec loop {e' i fn args} (H : LambdaBodyN i e' fn) (hi : i ≤ args.size) :
    ∃ n fn', LambdaBodyN n e' fn' ∧ n ≤ args.size ∧
      Expr.cheapBetaReduce.loop e args i fn = Expr.cheapBetaReduce.cont e args n fn' := by
    unfold Expr.cheapBetaReduce.loop; split
    · split
      · exact loop (by simpa [Nat.add_comm] using H.add (.succ .zero)) ‹_›
      · exact ⟨_, _, H, Nat.le_of_lt ‹_›, rfl⟩
    · exact ⟨_, _, H, hi, rfl⟩
  refine let ⟨i, fn, h1, h2, eq⟩ := loop .zero (Nat.zero_le _); eq ▸ ?_; clear eq
  simp [Expr.getAppArgs_eq] at h2 ⊢
  obtain ⟨l₁, l₂, rfl, eq⟩ : ∃ l₁ l₂, l₁.length = i ∧ e.getAppArgsList = l₁ ++ l₂ :=
    ⟨_, _, List.length_take_of_le (by simp [h2]), (List.take_append_drop ..).symm⟩
  have eqr := congrArg List.reverse eq; simp at eqr
  have inst_reduce (h : ∀ x ∈ l₁, x.Closed) (l₂)
      {{r}} (hr : fn.instantiateList (l₁.reverse ++ l₂) = r) :
      BetaReduce ((e.getAppFn.instantiateList l₂).mkAppList l₁) r := by
    generalize e.getAppFn = e₀ at h1
    subst r; clear h2 eq eqr
    induction l₁ generalizing e₀ fn l₂ with
    | nil => let .zero := h1; exact .refl
    | cons a l ih =>
      let .succ (body := body) h1 := h1
      rw [Expr.instantiateList_lam]
      simp at h ⊢; refine .trans (.appList .beta) ?_
      rw [Expr.instantiateList_instantiate1_comm h.1.looseBVarRange_zero]
      exact ih _ h.2 (a::l₂) _ h1
  have hl₁ : ∀ x ∈ l₁, x.Closed := by
    have := eqr ▸ hc.getAppArgsList; simp [or_imp, forall_and] at this
    exact this.1
  unfold Expr.cheapBetaReduce.cont; split <;> rename_i h3
  · simp [Expr.hasLooseBVars] at h3
    rw [Expr.mkAppRange_eq (l₂ := l₂) (l₃ := []) (by simp [eq]) rfl (by simp [← eq])]
    rw [← e.mkAppList_getAppArgsList, eqr]; simp
    refine .appList <| inst_reduce hl₁ [] <| Expr.instantiateList_eq_self (by simp [h3])
  split <;> [rename_i n; exact .refl]
  have hc := h1.closed hc.getAppFn
  simp [Closed] at hc; rw [if_pos hc]
  rw [Expr.mkAppRange_eq (l₂ := l₂) (l₃ := []) (by simp [eq]) rfl (by simp [← eq])]
  conv => lhs; rw [← e.mkAppList_getAppArgsList]
  simp [eqr]
  refine .appList <| inst_reduce hl₁ [] ?_
  rw [List.getElem?_append_left (by omega), Nat.sub_right_comm, ← List.getElem?_reverse hc]
  suffices ∀ l₁, (∀ x ∈ l₁, x.Closed) → ∀ n < l₁.length,
      (Expr.bvar n).instantiateList l₁ = l₁[n]?.getD default by
    simpa [Expr.liftLooseBVars_zero] using this l₁.reverse (by simpa using hl₁) n (by simp [hc])
  intro l₁ hl₁ n lt
  induction l₁ generalizing n with
  | nil => cases lt
  | cons a l ih =>
    simp at hl₁
    obtain _ | n := n <;> simp [Expr.instantiate1']
    · exact Expr.instantiateList_eq_self hl₁.1.looseBVarRange_zero
    · exact ih hl₁.2 _ (Nat.lt_of_succ_lt_succ lt)

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

theorem FVarsBelow.cheapBetaReduce (he : e.Closed) : FVarsBelow Δ e e.cheapBetaReduce :=
  .betaReduce (.cheapBetaReduce he)

theorem TrExpr.cheapBetaReduce (H : TrExpr env Us Δ e e')
    (henv : VEnv.WF env) (hΓ : VLCtx.WF env Us.length Δ)
    (noBV : Δ.NoBV) : TrExpr env Us Δ e.cheapBetaReduce e' :=
  H.beta henv hΓ <| .cheapBetaReduce <| noBV ▸ H.closed.mono (by simp)

theorem TrExprS.uninstantiateN
    (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ)
    (H : TrExprS env Us Δ₁ (Expr.instantiate1' e (.fvar v₀) dk) e')
    (sc : FVarsIn (· ≠ v₀) e) :
    TrExprS env Us Δ e e' := by
  have := H.abstract W
  rwa [sc.abstract_instantiate1] at this

theorem TrExpr.uninstantiateN
    (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ)
    (H : TrExpr env Us Δ₁ (Expr.instantiate1' e (.fvar v₀) dk) e')
    (sc : FVarsIn (· ≠ v₀) e) :
    TrExpr env Us Δ e e' :=
  let ⟨_, s, h⟩ := H; ⟨_, s.uninstantiateN W sc, W.toCtx ▸ h⟩

theorem TrExprS.uninstantiate
    (H : TrExprS env Us ((some (v, deps), d) :: Δ) (e.instantiate1' (.fvar v)) e')
    (sc : FVarsIn (· ≠ v) e) :
    TrExprS env Us ((none, d) :: Δ) e e' := H.uninstantiateN .zero sc

theorem TrExpr.uninstantiate
    (H : TrExpr env Us ((some (v, deps), d) :: Δ) (e.instantiate1' (.fvar v)) e')
    (sc : FVarsIn (· ≠ v) e) :
    TrExpr env Us ((none, d) :: Δ) e e' := H.uninstantiateN .zero sc

theorem TrExprS.inst_fvar {Δ : VLCtx} (henv : Ordered env)
    (hΔ : VLCtx.WF env Us.length ((some (a, deps), d) :: Δ))
    (H : TrExprS env Us ((none, d) :: Δ) e e') :
    TrExprS env Us ((some (a, deps), d) :: Δ) (e.instantiate1' (.fvar a)) e' := by
  refine
    have W := .skip_fvar (a, deps) d .refl
    have := H.weakFV henv (.cons_bvar _ W) ⟨hΔ, nofun, hΔ.2.2.weakN henv W.toCtx⟩
    ?_
  have hf := TrExprS.fvar (env := env) (Us := Us) (fv := a) (Δ := (some (a, deps), d) :: Δ) <| by
    simp [VLCtx.find?, VLCtx.next]; exact ⟨rfl, rfl⟩
  match d with
  | .vlam A₀ =>
    have := this.inst henv (.bvar .zero) (Δ := (some (a, deps), .vlam _) :: Δ) hf
    rwa [VLocalDecl.depth, VExpr.instN_bvar0] at this
  | .vlet A₀ e₀ =>
    simp [VLocalDecl.depth, VLocalDecl.liftN] at this
    exact this.inst_let henv hf

theorem TrExprS.eqv (H : TrExprS env Us Δ e₁ e') : e₁ == e₂ → TrExprS env Us Δ e₂ e' := by
  simp [(· == ·)]
  induction H generalizing e₂ <;> (cases e₂ <;> try change false = _ → _; rintro ⟨⟩)
  all_goals simp [Expr.eqv']; grind [TrExprS]

theorem TrExpr.eqv (H : TrExpr env Us Δ e₁ e') (h : e₁ == e₂) : TrExpr env Us Δ e₂ e' :=
  let ⟨_, h1, h2⟩ := H; ⟨_, h1.eqv h, h2⟩

theorem fvarsList_eqv {e₁ e₂ : Expr} : e₁ == e₂ → e₁.fvarsList = e₂.fvarsList := by
  simp [(· == ·)]
  induction e₁ generalizing e₂ <;> (cases e₂ <;> try change false = _ → _; rintro ⟨⟩)
  all_goals simp [Expr.eqv']; intros; subst_vars; simp [Expr.fvarsList]
  all_goals grind

theorem FVarsIn.eqv : e₁ == e₂ → FVarsIn P e₁ → FVarsIn P e₂ := by
  simp [(· == ·)]
  induction e₁ generalizing e₂ <;> (cases e₂ <;> try change false = _ → _; rintro ⟨⟩)
  all_goals simp [Expr.eqv']; intros; subst_vars; revert ‹FVarsIn ..›; simp [FVarsIn]
  all_goals grind

theorem FVarsBelow.eqv (H : FVarsBelow Δ e₁ ty₁)
    (eq : e₁ == e₂) (eq' : ty₁ == ty₂) : FVarsBelow Δ e₂ ty₂ :=
  fun _ hP he => .eqv eq' (H _ hP (.eqv (BEq.symm eq) he))

theorem TrTyping.eqv (H : TrTyping env Us Δ e₁ ty₁ e' ty')
    (eq : e₁ == e₂) (eq' : ty₁ == ty₂) : TrTyping env Us Δ e₂ ty₂ e' ty' :=
  let ⟨h1, h2, h3, h4⟩ := H
  ⟨.eqv h1 eq eq', h2.eqv eq, h3.eqv eq', h4⟩
