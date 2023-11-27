import Lean4Lean.Theory.VEnv

namespace Lean4Lean

open Lean (Name FVarId)
open VExpr

inductive Ctx.LiftN (n : Nat) : Nat → List VExpr → List VExpr → Prop where
  | zero (As) (h : As.length = n := by rfl) : Ctx.LiftN n 0 Γ (As ++ Γ)
  | succ : Ctx.LiftN n k Γ Γ' → Ctx.LiftN n (k+1) (A::Γ) (A.liftN n k :: Γ')

variable (Γ₀ : List VExpr) (e₀ A₀ : VExpr) in
inductive Ctx.InstN : Nat → List VExpr → List VExpr → Prop where
  | zero : Ctx.InstN 0 (A₀ :: Γ₀) Γ₀
  | succ : Ctx.InstN k Γ Γ' → Ctx.InstN (k+1) (A::Γ) (A.inst e₀ k :: Γ')

def Typing := List VExpr → VExpr → VExpr → Prop

instance : LE Typing := ⟨fun T₁ T₂ => ∀ Γ e A, T₁ Γ e A → T₂ Γ e A⟩

theorem Typing.le_refl (T : Typing) : T ≤ T := fun _ _ _ => id

theorem Typing.le_trans {a b c : Typing} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  fun _ _ _ => h2 _ _ _ ∘ h1 _ _ _

def Typing.IsClosedN (T : Typing) : Prop :=
  ∀ {Γ e A}, T Γ e A → e.ClosedN Γ.length

def Typing.IsWeakN (T : Typing) : Prop :=
  ∀ {n k Γ Γ' e A}, Ctx.LiftN n k Γ Γ' → T Γ e A → T Γ' (e.liftN n k) (A.liftN n k)

def Typing.IsWeakN.weak (hT : IsWeakN T) : T Γ e B → T (A::Γ) e.lift B.lift :=
  hT (.zero [A])

def Typing.IsInstN (T₁ : Typing) (T₀ := T₁) (T := T₁) : Prop :=
  ∀ {Γ₀ e₀ A₀ Γ₁ e₁ A₁ Γ k},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → T₀ Γ₀ e₀ A₀ → T₁ Γ₁ e₁ A₁ → T Γ (e₁.inst e₀ k) (A₁.inst e₀ k)

def Typing.IsType (T : Typing) (Γ : List VExpr) (A : VExpr) : Prop :=
  ∃ u, T Γ A (.sort u)

theorem Typing.IsType.closedN (hT : T.IsClosedN) : IsType T Γ A → A.ClosedN Γ.length
  | ⟨_, h⟩ => hT h

theorem Typing.IsType.weakN (hT : T.IsWeakN) (W : Ctx.LiftN n k Γ Γ') :
    IsType T Γ B → IsType T Γ' (B.liftN n k)
  | ⟨_, h⟩ => ⟨_, hT W h⟩

theorem Typing.IsType.weak (hT : T.IsWeakN) : IsType T Γ B → IsType T (A::Γ) B.lift
  | ⟨_, h⟩ => ⟨_, hT (.zero [A]) h⟩

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
  | zero As =>
    rw [liftVar_base]
    subst n
    induction As with simp [*, Nat.succ_add]
    | cons _ _ ih => rw [liftN_succ]; exact .succ ih
  | @succ k _ _ _ _ ih =>
    match H with
    | .zero => rw [liftVar_zero, ← lift_liftN']; exact .zero
    | .succ H => rw [liftVar_succ, ← lift_liftN']; exact (ih H).succ

def Typing.CtxWF (T : Typing) (Γ : List VExpr) : Prop := ∀ {n A}, Lookup Γ n A → T.IsType Γ A

def Typing.CtxWF.zero {T : Typing} : T.CtxWF [] := fun.

def Typing.CtxWF.succ {T : Typing} (hT : T.IsWeakN)
    (H : T.CtxWF Γ) (hA : T.IsType Γ A) : T.CtxWF (A::Γ)
  | _, _, .zero => hA.weak hT
  | _, _, .succ h => (H h).weak hT

variable
  (DF : VDefEq → Prop)
  (HasType : List VExpr → VExpr → VExpr → Prop)
  (uvars : Nat) in
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
    HasType Γ A (.sort u) → HasType Γ A' (.sort u') → IsDefEq1 Γ A A' →
    IsDefEq1 (A::Γ) body body' →
    IsDefEq1 Γ (.lam A body) (.lam A' body')
  | forallE :
    HasType Γ A (.sort u) → HasType Γ A' (.sort u') → IsDefEq1 Γ A A' →
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
    DF df →
    (∀ l ∈ ls, l.WF uvars) →
    ls.length = df.uvars →
    IsDefEq1 Γ (df.lhs.instL ls) (df.rhs.instL ls)

theorem IsDefEq1.mono
    {DF DF' : VDefEq → Prop}
    {TY TY' : Typing}
    (hDF : ∀ {df}, DF df → DF' df)
    (hTY : TY ≤ TY')
    (H : IsDefEq1 DF TY U Γ e1 e2) :
    IsDefEq1 DF' TY' U Γ e1 e2 := by
  induction H with
  | refl h => exact .refl (hTY _ _ _ h)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sort h1 h2 h3 => exact .sort h1 h2 h3
  | app h11 h12 _ h21 h22 _ ih1 ih2 =>
    exact .app (hTY _ _ _ h11) (hTY _ _ _ h12) ih1 (hTY _ _ _ h21) (hTY _ _ _ h22) ih2
  | lam h1 h2 _ _ ih1 ih2 => exact .lam (hTY _ _ _ h1) (hTY _ _ _ h2) ih1 ih2
  | forallE h1 h2 _ _ ih1 ih2 => exact .forallE (hTY _ _ _ h1) (hTY _ _ _ h2) ih1 ih2
  | beta h1 h2 => exact .beta (hTY _ _ _ h1) (hTY _ _ _ h2)
  | eta h1 => exact .eta (hTY _ _ _ h1)
  | proofIrrel h1 h2 h3 => exact .proofIrrel (hTY _ _ _ h1) (hTY _ _ _ h2) (hTY _ _ _ h3)
  | extra h1 h2 h3 => exact .extra (hDF h1) h2 h3

variable (env : VEnv) (TY : Typing) (uvars : Nat) in
inductive HasType1 : Typing where
  | bvar : Lookup Γ i ty → HasType1 Γ (.bvar i) ty
  | sort : l.WF uvars → HasType1 Γ (.sort l) (.sort (.succ l))
  | const :
    env.constants c = some (some ci) →
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
  | defeq : IsDefEq1 env.defeqs TY uvars Γ A B → HasType1 Γ e A → HasType1 Γ e B

theorem HasType1.mono
    {env env' : VEnv} {TY TY' : Typing}
    (henv : env ≤ env')
    (hTY : TY ≤ TY') :
    HasType1 env TY U ≤ HasType1 env' TY' U := by
  intro Γ e A H
  induction H with
  | bvar h => exact .bvar h
  | sort h => exact .sort h
  | const h1 h2 h3 => exact .const (henv.1 _ _ h1) h2 h3
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | defeq h1 _ ih2 => exact .defeq (IsDefEq1.mono (henv.2 _) hTY h1) ih2

theorem HasType1.closedN
    (hTY : ∀ {Γ e A}, TY Γ e A → e.ClosedN Γ.length)
    (H : HasType1 env TY U Γ e B) : e.ClosedN Γ.length := by
  induction H with
  -- | base h => exact hTY h
  | bvar h => exact h.lt
  | sort | const => trivial
  | app _ _ ih1 ih2
  | lam _ _ ih1 ih2
  | forallE _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | defeq _ _ ih => exact ih

-- theorem IsDefEq1.hasType (H : IsDefEq1 DF (HasType1 C DF' U) U Γ e e') :
--     (∃ A, HasType1 C DF' U Γ e A) ∧ (∃ A, HasType1 C DF' U Γ e' A) := by
--   induction H with
--   | refl h => exact ⟨⟨_, h⟩, _, h⟩
--   | symm _ ih => exact ⟨ih.2, ih.1⟩
--   | trans _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2⟩
--   | sort h1 h2 h3 => exact ⟨⟨_, .sort h1⟩, ⟨_, .sort h2⟩⟩
--   | app h11 h12 _ h21 h22 _ ih1 ih2 => exact ⟨⟨_, .app h11 h21⟩, ⟨_, .app h12 h22⟩⟩
--   | lam h1 h2 _ _ ih1 ih2 =>
--     have ⟨⟨A11, h11⟩, ⟨A12, h12⟩⟩ := ih1
--     have ⟨⟨A21, h21⟩, ⟨A22, h22⟩⟩ := ih2
--     refine' ⟨⟨_, .lam h1 h21⟩, ⟨_, .lam h2 _⟩⟩
--   | forallE h1 h2 _ _ ih1 ih2 => exact .forallE ih1 ih2
--   | beta h1 h2 => exact .beta (htype h1) (htype h2)
--   | eta h1 => exact .eta (htype h1)
--   | proofIrrel h1 h2 h3 => exact .proofIrrel (htype h1) (htype h2) (htype h3)
--   | extra h1 h2 h3 => exact .extra (hdefeq h1) h2 h3

def VConstant.WF (T : Nat → Typing) (ci : VConstant) : Prop := (T ci.uvars).IsType [] ci.type

def VDefEq.WF (T : Nat → Typing) (df : VDefEq) : Prop :=
  ∃ A, T df.uvars [] df.lhs A ∧ T df.uvars [] df.rhs A

namespace VEnv

structure PreWF (T : Nat → Typing) (env : VEnv) : Prop where
  const : env.constants n = some (some ci) → ci.WF T
  defeq : env.defeqs df → df.WF T
  closedN : ∀ {U}, (T U).IsClosedN

def HasTypeN (env : VEnv) : Nat → Nat → Typing
  | 0 => fun _ _ _ _ => False
  | n+1 => fun U => HasType1 env (env.HasTypeN n U) U

theorem HasTypeN.mono {env env' : VEnv} {n n' : Nat} (henv : env ≤ env') (hn : n ≤ n') :
    env.HasTypeN n U ≤ env'.HasTypeN n' U :=
  match n, n', hn with
  | 0, _, _ => fun.
  | _+1, _+1, hn => HasType1.mono henv (HasTypeN.mono henv (Nat.le_of_succ_le_succ hn))

def IsDefEqN (env : VEnv) (n U : Nat) : List VExpr → VExpr → VExpr → Prop :=
  IsDefEq1 env.defeqs (env.HasTypeN n U) U

theorem IsDefEqN.mono {env env' : VEnv} {n n' : Nat} (henv : env ≤ env') (hn : n ≤ n') :
    env.IsDefEqN n U Γ e1 e2 → env'.IsDefEqN n' U Γ e1 e2 :=
  IsDefEq1.mono @henv.2 (HasTypeN.mono henv hn)

def HasType (env : VEnv) (U : Nat) : Typing := fun Γ e A => ∃ n, env.HasTypeN n U Γ e A

theorem HasType.mono {env env' : VEnv} (henv : env ≤ env') : env.HasType U ≤ env'.HasType U
  | _, _, _, ⟨n, h⟩ => ⟨n, h.mono henv (Nat.le_refl _)⟩

def IsDefEq (env : VEnv) (U : Nat) (Γ : List VExpr) (e A : VExpr) : Prop :=
  ∃ n, env.IsDefEqN n U Γ e A

theorem IsDefEq.mono {env env' : VEnv} (henv : env ≤ env') :
    env.IsDefEq U Γ e A → env'.IsDefEq U Γ e A
  | ⟨n, h⟩ => ⟨n, h.mono henv (Nat.le_refl _)⟩

def IsType (env : VEnv) (U : Nat) := (env.HasType U).IsType

theorem IsType.mono {env env' : VEnv} (henv : env ≤ env') : env.IsType U Γ A → env'.IsType U Γ A
  | ⟨u, h⟩ => ⟨u, h.mono henv⟩

end VEnv

variable
  {DF : VDefEq → Prop}
  {TY : Typing}
  (closedN : ∀ {U}, (T U).IsClosedN)
  (hDF : ∀ {df}, DF df → df.WF T)
  (hTY : TY.IsWeakN) in
theorem IsDefEq1.weakN (W : Ctx.LiftN n k Γ Γ') (H : IsDefEq1 DF TY U Γ e1 e2) :
    IsDefEq1 DF TY U Γ' (e1.liftN n k) (e2.liftN n k) := by
  induction H generalizing k Γ' with
  | refl h => exact .refl (hTY W h)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | sort h1 h2 h3 => exact .sort h1 h2 h3
  | app h11 h12 _ h21 h22 _ ih1 ih2 =>
    exact .app (hTY W h11) (hTY W h12) (ih1 W) (hTY W h21) (hTY W h22) (ih2 W)
  | lam h1 h2 _ _ ih1 ih2 => exact .lam (hTY W h1) (hTY W h2) (ih1 W) (ih2 W.succ)
  | forallE h1 h2 _ _ ih1 ih2 => exact .forallE (hTY W h1) (hTY W h2) (ih1 W) (ih2 W.succ)
  | beta h1 h2 =>
    exact (by simpa using liftN_inst_hi ..) ▸ .beta (hTY W.succ h1) (hTY W h2)
  | eta h1 =>
    have := IsDefEq1.eta (DF := DF) (uvars := U) (hTY W h1)
    simp [liftN]; rwa [← lift_liftN']
  | proofIrrel h1 h2 h3 => exact .proofIrrel (hTY W h1) (hTY W h2) (hTY W h3)
  | extra h1 h2 h3 =>
    have ⟨A, hA1, hA2⟩ := hDF h1
    rw [(closedN hA1).instL.liftN_eq (Nat.zero_le _), (closedN hA2).instL.liftN_eq (Nat.zero_le _)]
    exact .extra h1 h2 h3

variable
  {env : VEnv} {TY : Typing} (henv : env.PreWF T) (hTY : TY.IsWeakN) in
theorem HasType1.weakN : (HasType1 env TY U).IsWeakN := by
  intro n k Γ Γ' e A W H
  induction H generalizing k Γ' with
  | bvar h => refine .bvar (h.weakN W)
  | sort h => exact .sort h
  | const h1 h2 h3 =>
    rw [((henv.const h1).closedN henv.closedN).instL.liftN_eq (Nat.zero_le _)]
    exact .const h1 h2 h3
  | app _ _ ih1 ih2 => exact (by simpa using liftN_inst_hi ..) ▸ .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | defeq h1 _ ih2 => exact .defeq (IsDefEq1.weakN henv.closedN henv.defeq hTY W h1) (ih2 W)

variable
  {DF : VDefEq → Prop}
  {TY TY₀ : Typing}
  (closedN : ∀ {U}, (T U).IsClosedN)
  (hDF : ∀ {df}, DF df → df.WF T)
  (hTY : ∀ {Γ₁ e₁ A₁ Γ k},
    Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → TY Γ₁ e₁ A₁ → TY₀ Γ (e₁.inst e₀ k) (A₁.inst e₀ k)) in
theorem IsDefEq1.instN
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (he : IsDefEq1 DF TY U Γ₁ e1 e2) :
    IsDefEq1 DF TY₀ U Γ (e1.inst e₀ k) (e2.inst e₀ k) := by
  induction he generalizing Γ k with
  | refl h => exact .refl (hTY W h)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | sort h1 h2 h3 => exact .sort h1 h2 h3
  | app h11 h12 _ h21 h22 _ ih1 ih2 =>
    exact .app (hTY W h11) (hTY W h12) (ih1 W) (hTY W h21) (hTY W h22) (ih2 W)
  | lam h1 h2 _ _ ih1 ih2 => exact .lam (hTY W h1) (hTY W h2) (ih1 W) (ih2 W.succ)
  | forallE h1 h2 _ _ ih1 ih2 => exact .forallE (hTY W h1) (hTY W h2) (ih1 W) (ih2 W.succ)
  | beta h1 h2 =>
    exact (by simpa using inst_inst_hi ..) ▸ .beta (hTY W.succ h1) (hTY W h2)
  | @eta _ e A B h1 =>
    simp [inst]
    have := IsDefEq1.eta (DF := DF) (uvars := U) (hTY W h1)
    rwa [lift, liftN_inst_lo 1 e e₀ k 0 (Nat.zero_le _), Nat.add_comm] at this
  | proofIrrel h1 h2 h3 => exact .proofIrrel (hTY W h1) (hTY W h2) (hTY W h3)
  | extra h1 h2 h3 =>
    have ⟨A, hA1, hA2⟩ := hDF h1
    rw [(closedN hA1).instL.instN_eq (Nat.zero_le _),
        (closedN hA2).instL.instN_eq (Nat.zero_le _)]
    exact .extra h1 h2 h3

variable
  {env : VEnv} {TY TY₀ : Typing} (henv : env.PreWF T)
  (hTY : TY.IsInstN TY₀ TY')
  (hle : TY₀ ≤ HasType1 env TY' U)
  (weakN : (HasType1 env TY' U).IsWeakN) in
theorem HasType1.instN : (HasType1 env TY U).IsInstN TY₀ (HasType1 env TY' U) := by
  intro Γ₀ e₀ A₀ Γ₁ e₁ A₁ Γ k W h₀ he
  induction he generalizing Γ k with
  | @bvar _ i ty h =>
    dsimp [inst]
    induction W generalizing i ty with
    | zero =>
      cases h with simp [inst_lift, h₀]
      | zero => exact hle _ _ _ h₀
      | succ h => exact .bvar h
    | succ _ ih =>
      cases h with (simp; rw [Nat.add_comm, ← liftN_inst_lo (hj := Nat.zero_le _)])
      | zero => exact .bvar .zero
      | succ h => refine weakN.weak (ih h)
  | sort h => exact .sort h
  | const h1 h2 h3 =>
    rw [← ((henv.const h1).closedN henv.closedN).instL.liftN_eq (Nat.zero_le _), inst_liftN]
    exact .const h1 h2 h3
  | app _ _ ih1 ih2 =>
    have := HasType1.app (ih1 W) (ih2 W)
    rwa [← inst_inst_hi _ _ _ 0 k] at this
  | lam _ _ ih1 ih2 =>
    exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | defeq h1 _ ih2 =>
    refine .defeq (IsDefEq1.instN henv.closedN henv.2 (hTY · h₀) W h1) (ih2 W)

-- variable {env : VEnv} {TY TY₀ : Typing} (henv : env.PreWF T)
--   (weakN : TY.IsWeakN)
--   (instN : TY.IsInstN TY₀) in
-- theorem HasType1.defeq_l
--     (h1 : HasType1 env TY U (A::Γ) e B)
--     (h2 : IsDefEq1 env.defeqs TY U Γ A A') :
--     HasType1 env TY U (A'::Γ) e B := by
--   have h1 := HasType1.weakN henv weakN (.succ (.zero [A'])) h1
--   have h2 := IsDefEq1.weakN (DF := env.defeqs) henv.closedN henv.defeq @weakN (.zero [A']) h2
--   simp at h1 h2
--   have h3 := HasType1.defeq h2.symm (.bvar .zero)
--   have' h4 := HasType1.instN henv _ (Typing.le_refl _) _ (_) h1 h3

namespace VEnv

theorem HasTypeN.closedN {env : VEnv} : ∀ {n U}, (env.HasTypeN n U).IsClosedN
  | _+1, _, _, _, _, h => HasType1.closedN HasTypeN.closedN h

variable {env : VEnv} (henv : env.PreWF T) in
theorem HasTypeN.weakN : ∀ {n U}, (env.HasTypeN n U).IsWeakN
  | _+1, _, _, _, _, _, _, _, W, h => HasType1.weakN henv HasTypeN.weakN W h

theorem IsDefEqN.weakN {env : VEnv} (henv : env.PreWF T) (W : Ctx.LiftN n k Γ Γ')
    (h : env.IsDefEqN U N Γ e1 e2) : env.IsDefEqN U N Γ' (e1.liftN n k) (e2.liftN n k) :=
  IsDefEq1.weakN henv.closedN henv.defeq (HasTypeN.weakN henv) W h

theorem HasType.weakN (henv : env.PreWF T) :
    (HasType env U).IsWeakN := fun W ⟨_, h⟩ => ⟨_, h.weakN henv W⟩

theorem IsType.weakN {env : VEnv} (henv : env.PreWF T) (W : Ctx.LiftN n k Γ Γ') :
    env.IsType U Γ B → env.IsType U Γ' (B.liftN n k)
  | ⟨_, h⟩ => ⟨_, h.weakN henv W⟩

variable {env : VEnv} (henv : env.PreWF T) in
theorem HasTypeN.instN' {n₁ n₀ n} (hn : n₀ + n₁ ≤ n) :
    (HasTypeN env n₁ U).IsInstN (HasTypeN env (n₀+1) U) (HasTypeN env n U) :=
  match n₁, n with
  | 0, _ => fun.
  | _+1, n'+1 => HasType1.instN henv
    (HasTypeN.instN' (Nat.le_of_succ_le_succ hn))
    (HasTypeN.mono (n' := n'+1) (VEnv.le_refl _) <|
      Nat.le_trans (Nat.add_le_add_left (Nat.le_add_left ..) _) hn)
    (HasTypeN.weakN henv (n := n'+1))

theorem HasTypeN.instN (henv : env.PreWF T) {n₁ n₀ n} (hn : n₀ + n₁ ≤ n + 1) :
    (HasTypeN env n₁ U).IsInstN (HasTypeN env n₀ U) (HasTypeN env n U) :=
  match n₀ with
  | 0 => fun.
  | _+1 => HasTypeN.instN' henv (by rwa [Nat.add_right_comm, Nat.add_le_add_iff_right] at hn)

theorem HasType.instN (henv : env.PreWF T) : (HasType env U).IsInstN :=
  fun W ⟨_, h⟩ ⟨_, h'⟩ => ⟨_, h.instN henv (Nat.le_succ ..) W h'⟩

theorem IsType.instN {env : VEnv} (henv : env.PreWF T) (W : Ctx.LiftN n k Γ Γ') :
    env.IsType U Γ B → env.IsType U Γ' (B.liftN n k)
  | ⟨_, h⟩ => ⟨_, h.weakN henv W⟩

end VEnv

-- variable
--   {T : Nat → Typing}
--   {C : Name → Option (Option VConstant)}
--   (hconst : ∀ {n ci}, C n = some (some ci) → ci.WF T)
--   (hT : ∀ {U Γ e A}, T U Γ e A → HasType1 env TY U Γ e A) in
-- theorem HasType.type_isType (hΓ : (HasType1 env TY U).CtxWF Γ)
--     (H : HasType1 env TY U Γ e A) : (HasType1 env TY U).IsType Γ A := by
--   induction H with
--   | bvar h => exact hΓ h
--   | sort h => exact ⟨_, .sort h⟩
--   | const h1 h2 h3 =>
--     have ⟨u, hci⟩ := hconst h1
--     have := hT hci
--     exact _
--   | app _ _ ih1 ih2 => exact .app ih1 ih2
--   | lam _ _ ih1 ih2 => exact .lam ih1 ih2
--   | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
--   | defeq h1 _ ih2 => exact .defeq (hdefeq h1) ih2

-- theorem IsDefEq.hasType (h : IsDefEq U E Γ e e') :
--     ∃ A, HasType U E Γ e A ∧ HasType U E Γ e' A := sorry
