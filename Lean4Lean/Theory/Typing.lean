import Lean4Lean.Theory.VEnv

namespace Lean4Lean

open Lean (Name FVarId)

inductive Ctx.LiftN (n : Nat) : Nat → List VExpr → List VExpr → Prop where
  | zero : As.length = n → Ctx.LiftN n 0 Γ (As ++ Γ)
  | succ : Ctx.LiftN n k Γ Γ' → Ctx.LiftN n (k+1) (A::Γ) (A.liftN n k :: Γ')

inductive Lookup : List VExpr → Nat → VExpr → Prop where
  | zero : Lookup (ty::Γ) 0 ty.lift
  | succ : Lookup Γ n ty → Lookup (A::Γ) (n+1) ty.lift

theorem Lookup.lt (H : Lookup Γ i A) : i < Γ.length := by
  induction H with
  | zero => apply Nat.succ_pos
  | succ _ ih => apply Nat.succ_lt_succ ih

theorem Lookup.weakN (W : Ctx.LiftN n k Γ Γ') (H : Lookup Γ i A) :
    Lookup Γ' (liftVar n i k) (A.liftN n k) := by
  induction W generalizing i A with
  | @zero Γ As =>
    rw [liftVar_base]
    subst n
    induction As with simp [*, Nat.succ_add]
    | cons _ _ ih => rw [VExpr.liftN_zero]; exact .succ ih
  | @succ k _ _ _ _ ih =>
    match H with
    | .zero => rw [liftVar_zero, ← VExpr.lift_liftN']; exact .zero
    | .succ H => rw [liftVar_succ, ← VExpr.lift_liftN']; exact (ih H).succ

variable (uvars : Nat) {U : Nat}
variable
  (constants : Name → Option (Option VConstant))
  (IsDefEq : List VExpr → VExpr → VExpr → Prop) in
inductive HasType1 : List VExpr → VExpr → VExpr → Prop where
  | bvar : Lookup Γ i ty → HasType1 Γ (.bvar i) ty
  | sort : l.WF uvars → HasType1 Γ (.sort l) (.sort (.succ l))
  | const :
    constants c = some (some ci) →
    (∀ l ∈ ls, l.WF uvars) →
    ls.length = ci.uvars →
    HasType1 Γ (.const c ls) (ci.type.instL ls)
  | app :
    HasType1 Γ f (.forallE A B) →
    HasType1 Γ a A →
    HasType1 Γ (.app f a) (B.inst a)
  | lam :
    HasType1 Γ A (.sort u) →
    HasType1 (A::Γ) body B →
    HasType1 Γ (.lam A body) (.forallE A B)
  | forallE :
    HasType1 Γ A (.sort u) →
    HasType1 (A::Γ) B (.sort v) →
    HasType1 Γ (.forallE A B) (.sort (.imax u v))
  | defeq : IsDefEq Γ A B → HasType1 Γ e A → HasType1 Γ e B

theorem HasType1.mono
    {constants constants' : Name → Option (Option VConstant)}
    {IsDefEq IsDefEq' : List VExpr → VExpr → VExpr → Prop}
    (hconst : ∀ {n a}, constants n = some a → constants' n = some a)
    (hdefeq : ∀ {Γ e1 e2}, IsDefEq Γ e1 e2 → IsDefEq' Γ e1 e2)
    (H : HasType1 U constants IsDefEq Γ e A) :
    HasType1 U constants' IsDefEq' Γ e A := by
  induction H with
  | bvar h => exact .bvar h
  | sort h => exact .sort h
  | const h1 h2 h3 => exact .const (hconst h1) h2 h3
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | defeq h1 _ ih2 => exact .defeq (hdefeq h1) ih2

theorem HasType1.closedN (H : HasType1 U C DF Γ e B) : e.ClosedN Γ.length := by
  induction H with
  | bvar h => exact h.lt
  | sort | const => trivial
  | app _ _ ih1 ih2
  | lam _ _ ih1 ih2
  | forallE _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | defeq _ _ ih => exact ih

variable
  (defeqs : VDefEq → Prop)
  (HasType : List VExpr → VExpr → VExpr → Prop) in
inductive IsDefEq1 : List VExpr → VExpr → VExpr → Prop where
  | refl :
    HasType Γ e A → IsDefEq1 Γ e e
  | symm :
    IsDefEq1 Γ e e' → IsDefEq1 Γ e' e
  | trans :
    IsDefEq1 Γ e₁ e₂ → IsDefEq1 Γ e₂ e₃ → IsDefEq1 Γ e₁ e₃
  | sort :
    l.WF uvars → l'.WF uvars → l ≈ l' →
    IsDefEq1 Γ (.sort l) (.sort l')
  | app :
    HasType Γ f (.forallE A B) → HasType Γ f' (.forallE A B) → IsDefEq1 Γ f f' →
    HasType Γ a A → HasType Γ a' A → IsDefEq1 Γ a a' →
    IsDefEq1 Γ (.app f a) (.app f' a')
  | lam :
    IsDefEq1 Γ A A' →
    IsDefEq1 (A::Γ) body body' →
    IsDefEq1 Γ (.lam A body) (.lam A' body')
  | forallE :
    IsDefEq1 Γ A A' →
    IsDefEq1 (A::Γ) body body' →
    IsDefEq1 Γ (.forallE A body) (.forallE A' body')
  | beta :
    HasType (A::Γ) e B → HasType Γ e' A →
    IsDefEq1 Γ (.app (.lam A e) e') (e.inst e')
  | eta :
    HasType Γ e (.forallE A B) →
    IsDefEq1 Γ (.lam A (.app e.lift (.bvar 0))) e
  | proofIrrel :
    HasType Γ p (.sort .zero) → HasType Γ h p → HasType Γ h' p →
    IsDefEq1 Γ h h'
  | extra :
    defeqs df →
    (∀ l ∈ ls, l.WF uvars) →
    ls.length = df.uvars →
    IsDefEq1 Γ (df.lhs.instL ls) (df.rhs.instL ls)

theorem IsDefEq1.mono
    {defeqs defeqs' : VDefEq → Prop}
    {HasType HasType' : List VExpr → VExpr → VExpr → Prop}
    (hdefeq : ∀ {df}, defeqs df → defeqs' df)
    (htype : ∀ {Γ e A}, HasType Γ e A → HasType' Γ e A)
    (H : IsDefEq1 U defeqs HasType Γ e1 e2) :
    IsDefEq1 U defeqs' HasType' Γ e1 e2 := by
  induction H with
  | refl h => exact .refl (htype h)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sort h1 h2 h3 => exact .sort h1 h2 h3
  | app h11 h12 _ h21 h22 _ ih1 ih2 =>
    exact .app (htype h11) (htype h12) ih1 (htype h21) (htype h22) ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | beta h1 h2 => exact .beta (htype h1) (htype h2)
  | eta h1 => exact .eta (htype h1)
  | proofIrrel h1 h2 h3 => exact .proofIrrel (htype h1) (htype h2) (htype h3)
  | extra h1 h2 h3 => exact .extra (hdefeq h1) h2 h3

-- theorem IsDefEq1.hasType (H : IsDefEq1 U DF (HasType1 U C DF') Γ e e') :
--     (∃ A, HasType1 U C DF' Γ e A) ∧ (∃ A, HasType1 U C DF' Γ e' A) := by
--   induction H with
--   | refl h => exact ⟨⟨_, h⟩, _, h⟩
--   | symm _ ih => exact ⟨ih.2, ih.1⟩
--   | trans _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2⟩
--   | sort h1 h2 h3 => exact ⟨⟨_, .sort h1⟩, ⟨_, .sort h2⟩⟩
--   | app h11 h12 _ h21 h22 _ ih1 ih2 => exact ⟨⟨_, .app h11 h21⟩, ⟨_, .app h12 h22⟩⟩
--   | lam h1 h2 ih1 ih2 =>
--     have ⟨⟨A11, h11⟩, ⟨A12, h12⟩⟩ := ih1
--     have ⟨⟨A21, h21⟩, ⟨A22, h22⟩⟩ := ih2
--     exact ⟨⟨_, .lam _ hA⟩, ⟨_, .lam h12 h22⟩⟩
--   | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
--   | beta h1 h2 => exact .beta (htype h1) (htype h2)
--   | eta h1 => exact .eta (htype h1)
--   | proofIrrel h1 h2 h3 => exact .proofIrrel (htype h1) (htype h2) (htype h3)
--   | extra h1 h2 h3 => exact .extra (hdefeq h1) h2 h3

def Typing := Nat → List VExpr → VExpr → VExpr → Prop

def Typing.IsClosedN (T : Typing) : Prop :=
  ∀ {u Γ e A}, T u Γ e A → e.ClosedN Γ.length

def Typing.IsWeakN (T : Typing) : Prop :=
  ∀ {u n k Γ Γ' e A}, Ctx.LiftN n k Γ Γ' → T u Γ e A → T u Γ' (e.liftN n k) (A.liftN n k)

def Typing.IsWeakN.weak (hT : IsWeakN T) : T U Γ e B → T U (A::Γ) e.lift B.lift :=
  hT (.zero (As := [A]) rfl)

def Typing.IsType (T : Typing) (U : Nat) (Γ : List VExpr) (A : VExpr) : Prop :=
  ∃ u, T U Γ A (.sort u)

theorem Typing.IsType.closedN (hT : T.IsClosedN) : IsType T U Γ A → A.ClosedN Γ.length
  | ⟨_, h⟩ => hT h

theorem Typing.IsType.weakN (hT : T.IsWeakN) (W : Ctx.LiftN n k Γ Γ') :
    IsType T U Γ B → IsType T U Γ' (B.liftN n k)
  | ⟨_, h⟩ => ⟨_, hT W h⟩

theorem Typing.IsType.weak (hT : T.IsWeakN) : IsType T U Γ B → IsType T U (A::Γ) B.lift
  | ⟨_, h⟩ => ⟨_, hT (.zero (As := [A]) rfl) h⟩

def VConstant.WF (T : Typing) (ci : VConstant) : Prop := T.IsType ci.uvars [] ci.type

def VDefEq.WF (T : Typing) (df : VDefEq) : Prop :=
  ∃ A, T df.uvars [] df.lhs A ∧ T df.uvars [] df.rhs A

structure VPreEnv where
  env : VEnv
  protected T : Typing

def VPreEnv.HasTypeN (P : VPreEnv) : Nat → Typing
  | 0 => P.T
  | n+1 => fun U Γ e A =>
    P.HasTypeN n U Γ e A ∨
    HasType1 U P.env.constants (IsDefEq1 U P.env.defeqs (P.HasTypeN n U)) Γ e A

structure VPreEnv.LE (P1 P2 : VPreEnv) : Prop where
  env : P1.env ≤ P2.env
  T : P1.T u Γ e A → P2.T u Γ e A

instance : LE VPreEnv := ⟨VPreEnv.LE⟩

theorem VPreEnv.le_refl (env : VPreEnv) : env ≤ env := ⟨VEnv.le_refl _, id⟩

theorem VPreEnv.le_trans {a b c : VPreEnv} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  ⟨VEnv.le_trans h1.1 h2.1, h2.2 ∘ h1.2⟩

namespace VPreEnv
variable (P : VPreEnv)

theorem HasTypeN.mono {P P' : VPreEnv} {n n' : Nat} (hP : P ≤ P') (hn : n ≤ n')
    (H : P.HasTypeN n U Γ e A) : P'.HasTypeN n' U Γ e A :=
  match n, n', hn with
  | 0, 0, _ => hP.2 H
  | 0, _+1, _ => Or.inl <| HasTypeN.mono hP (Nat.zero_le _) H
  | _+1, _+1, hn =>
    have IH := fun {Γ e A} =>
      HasTypeN.mono hP (Nat.le_of_succ_le_succ hn) (Γ := Γ) (e := e) (A := A)
    Or.imp IH (HasType1.mono @hP.1.1 (IsDefEq1.mono @hP.1.2 IH)) H

def IsDefEqN (n U : Nat) : List VExpr → VExpr → VExpr → Prop :=
  IsDefEq1 U P.env.defeqs (P.HasTypeN n U)

theorem IsDefEqN.mono {P P' : VPreEnv} {n n' : Nat} (hP : P ≤ P') (hn : n ≤ n') :
    P.IsDefEqN n U Γ e A → P'.IsDefEqN n' U Γ e A :=
  IsDefEq1.mono @hP.1.2 (HasTypeN.mono hP hn)

def HasType : Typing := fun U Γ e A => ∃ n, P.HasTypeN U n Γ e A

theorem HasType.mono {P P' : VPreEnv} (hP : P ≤ P') : P.HasType U Γ e A → P'.HasType U Γ e A
  | ⟨n, h⟩ => ⟨n, h.mono hP (Nat.le_refl _)⟩

def IsDefEq (P : VPreEnv) (U : Nat) (Γ : List VExpr) (e A : VExpr) : Prop :=
  ∃ n, P.IsDefEqN n U Γ e A

theorem IsDefEq.mono {P P' : VPreEnv} (hP : P ≤ P') : P.IsDefEq U Γ e A → P'.IsDefEq U Γ e A
  | ⟨n, h⟩ => ⟨n, h.mono hP (Nat.le_refl _)⟩

def IsType (P : VPreEnv) := P.HasType.IsType

theorem IsType.mono {P P' : VPreEnv} (hP : P ≤ P') : P.IsType U Γ A → P'.IsType U Γ A
  | ⟨u, h⟩ => ⟨u, h.mono hP⟩

end VPreEnv

structure VPreEnvWF extends VPreEnv where
  closedN : T.IsClosedN
  weakN : T.IsWeakN
  constWF : env.constants n = some (some ci) → ci.WF T
  defeqWF : env.defeqs df → df.WF T

instance : LE VPreEnvWF := ⟨(·.toVPreEnv ≤ ·.toVPreEnv)⟩

variable {P : VPreEnvWF}

namespace VPreEnv

theorem HasTypeN.closedN {P : VPreEnvWF} : ∀ {n}, P.HasTypeN n U Γ e B → e.ClosedN Γ.length
  | 0, h => P.closedN h
  | _+1, .inl h => HasTypeN.closedN h
  | _+1, .inr h => HasType1.closedN h

theorem HasType.closedN : P.HasType.IsClosedN
  | _, _, _, _, ⟨_, h⟩ => h.closedN

theorem IsType.closedN : P.IsType U Γ A → A.ClosedN Γ.length :=
  Typing.IsType.closedN HasType.closedN

end VPreEnv

variable
  {C : Name → Option (Option VConstant)}
  {DF : List VExpr → VExpr → VExpr → Prop}
  (closedN : T.IsClosedN)
  (hconst : ∀ {n ci}, C n = some (some ci) → ci.WF T)
  (hdefeq : ∀ {n k Γ Γ' A B}, Ctx.LiftN n k Γ Γ' → DF Γ A B → DF Γ' (A.liftN n k) (B.liftN n k)) in
theorem HasType1.weakN
    (W : Ctx.LiftN n k Γ Γ')
    (H : HasType1 U C DF Γ e B) :
    HasType1 U C DF Γ' (e.liftN n k) (B.liftN n k) := by
  induction H generalizing k Γ' with
  | bvar h => refine .bvar (h.weakN W)
  | sort h => exact .sort h
  | const h1 h2 h3 =>
    rw [((hconst h1).closedN closedN).instL.liftN_eq (Nat.zero_le _)]
    exact .const h1 h2 h3
  | app _ _ ih1 ih2 => exact (by simpa using VExpr.liftN_inst_hi ..) ▸ .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | defeq h1 _ ih2 => exact .defeq (hdefeq W h1) (ih2 W)

variable
  {DF : VDefEq → Prop}
  {TY : List VExpr → VExpr → VExpr → Prop}
  (closedN : T.IsClosedN)
  (hdefeq : ∀ {df}, DF df → df.WF T)
  (htype : ∀ {n k Γ Γ' e A}, Ctx.LiftN n k Γ Γ' → TY Γ e A → TY Γ' (e.liftN n k) (A.liftN n k)) in
theorem IsDefEq1.weakN (W : Ctx.LiftN n k Γ Γ') (H : IsDefEq1 U DF TY Γ e1 e2) :
    IsDefEq1 U DF TY Γ' (e1.liftN n k) (e2.liftN n k) := by
  induction H generalizing k Γ' with
  | refl h => exact .refl (htype W h)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | sort h1 h2 h3 => exact .sort h1 h2 h3
  | app h11 h12 _ h21 h22 _ ih1 ih2 =>
    exact .app (htype W h11) (htype W h12) (ih1 W) (htype W h21) (htype W h22) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | beta h1 h2 =>
    exact (by simpa using VExpr.liftN_inst_hi ..) ▸ .beta (htype W.succ h1) (htype W h2)
  | eta h1 =>
    have := IsDefEq1.eta (uvars := U) (defeqs := DF) (htype W h1)
    simp [VExpr.liftN]; rwa [VExpr.liftN_zero, ← VExpr.lift_liftN']
  | proofIrrel h1 h2 h3 => exact .proofIrrel (htype W h1) (htype W h2) (htype W h3)
  | extra h1 h2 h3 =>
    have ⟨A, hA1, hA2⟩ := hdefeq h1
    rw [(closedN hA1).instL.liftN_eq (Nat.zero_le _), (closedN hA2).instL.liftN_eq (Nat.zero_le _)]
    exact .extra h1 h2 h3

namespace VPreEnv

theorem HasTypeN.weakN : ∀ {n}, (P.HasTypeN n).IsWeakN
  | 0 => P.weakN
  | _+1 => fun
    | W, .inl h => .inl <| HasTypeN.weakN W h
    | W, .inr h => .inr <| HasType1.weakN P.closedN P.constWF
      (IsDefEq1.weakN P.closedN P.defeqWF HasTypeN.weakN) W h

theorem IsDefEqN.weakN (W : Ctx.LiftN n k Γ Γ')
    (h : P.IsDefEqN U N Γ e1 e2) : P.IsDefEqN U N Γ' (e1.liftN n k) (e2.liftN n k) :=
  IsDefEq1.weakN P.closedN P.defeqWF HasTypeN.weakN W h

theorem HasType.weakN : P.HasType.IsWeakN := fun W ⟨_, h⟩ => ⟨_, h.weakN W⟩

theorem IsType.weakN (W : Ctx.LiftN n k Γ Γ') : P.IsType U Γ B → P.IsType U Γ' (B.liftN n k)
  | ⟨_, h⟩ => ⟨_, h.weakN W⟩

end VPreEnv

def Typing.CtxWF (T : Typing) (Γ : List VExpr) : Prop := ∀ {n A}, Lookup Γ n A → T.IsType uvars Γ A

def Typing.CtxWF.zero {T : Typing} : T.CtxWF U [] := fun.

def Typing.CtxWF.succ {T : Typing} (hT : T.IsWeakN)
    (H : T.CtxWF U Γ) (hA : T.IsType U Γ A) : T.CtxWF U (A::Γ)
  | _, _, .zero => hA.weak hT
  | _, _, .succ h => (H h).weak hT

-- theorem HasType.type_isType {T : Typing} (hΓ : T.CtxWF U Γ)
--     (H : HasType1 U C DF Γ e A) : ∃ u, HasType1 U C DF Γ A (.sort u) := by
--   induction H with
--   | bvar h => exact hΓ h
--   | sort h => exact ⟨_, n+1, .sort h⟩
--   | const h1 h2 h3 =>
--     have := henv.1 h1
--     exact _
--   | app _ _ ih1 ih2 => exact .app ih1 ih2
--   | lam _ _ ih1 ih2 => exact .lam ih1 ih2
--   | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
--   | defeq h1 _ ih2 => exact .defeq (hdefeq h1) ih2

-- theorem IsDefEq.hasType (h : IsDefEq U E Γ e e') :
--     ∃ A, HasType U E Γ e A ∧ HasType U E Γ e' A := sorry
