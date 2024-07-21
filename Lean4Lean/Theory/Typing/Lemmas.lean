import Lean4Lean.Theory.Typing.Basic

namespace Lean4Lean

open VExpr

inductive Ctx.LiftN (n : Nat) : Nat → List VExpr → List VExpr → Prop where
  | zero (As) (h : As.length = n := by rfl) : Ctx.LiftN n 0 Γ (As ++ Γ)
  | succ : Ctx.LiftN n k Γ Γ' → Ctx.LiftN n (k+1) (A::Γ) (A.liftN n k :: Γ')

def Ctx.LiftN.one : Ctx.LiftN 1 0 Γ (A::Γ) := .zero [_]

theorem Ctx.LiftN.isSuffix (H : Ctx.LiftN n k Γ Γ') :
    ∃ Γ₀ As Δ Δ',
      As.length = n ∧ Δ.length = k ∧ Δ'.length = k ∧
      Γ = Δ ++ Γ₀ ∧ Γ' = Δ' ++ As ++ Γ₀ := by
  induction H with
  | @zero Γ As h => exact ⟨Γ, As, [], [], h, rfl, rfl, rfl, rfl⟩
  | succ _ ih =>
    obtain ⟨_, _, Δ, Δ', hn, hΔ, hΔ', rfl, rfl⟩ := ih
    exact ⟨_, _, _ :: Δ, _ :: Δ', hn, by simp [hΔ], by simp [hΔ'], rfl, rfl⟩

theorem Ctx.LiftN.comp (h1 : k1 ≤ k2) (h2 : k2 ≤ n1 + k1) :
    Ctx.LiftN n1 k1 Γ₀ Γ₁ → Ctx.LiftN n2 k2 Γ₁ Γ₂ → Ctx.LiftN (n1+n2) k1 Γ₀ Γ₂
  | .zero As h, H2 => by
    obtain ⟨Γ₀', _, Δ, Δ', hn, hΔ, hΔ', eq, rfl⟩ := H2.isSuffix
    obtain ⟨As, rfl, rfl⟩ := (List.append_eq_append_of_length_le (by rwa [h, hΔ])).1 eq.symm
    rw [← List.append_assoc]
    exact .zero _ (by simp [← h, hΔ, hΔ', hn, Nat.add_left_comm, Nat.add_comm])
  | .succ H1, .succ H2 =>
    have h1 := Nat.le_of_succ_le_succ h1
    have h2 := Nat.le_of_succ_le_succ h2
    liftN'_liftN' h1 h2 ▸ (H1.comp h1 h2 H2).succ

inductive Ctx.Lift' : Lift → List VExpr → List VExpr → Prop where
  | refl : Ctx.Lift' .refl Γ Γ
  | skip : Ctx.Lift' l Γ Γ' → Ctx.Lift' (.skip l) Γ (A :: Γ')
  | cons : Ctx.Lift' l Γ Γ' → Ctx.Lift' (.cons l) (A::Γ) (A.lift' l :: Γ')

theorem Ctx.liftN_iff_lift' : Ctx.LiftN n k Γ Γ' ↔ Ctx.Lift' (.consN (.skipN n) k) Γ Γ' := by
  constructor <;> intro h
  · induction h with
    | zero As =>
      subst n
      induction As with
      | nil => simp [Lift'.refl]
      | cons _ _ ih => exact .skip ih
    | succ _ ih => rw [← lift'_consN_skipN]; exact .cons ih
  · induction k generalizing Γ Γ' with
    | zero =>
      obtain ⟨_, rfl, eq⟩ : ∃ As, Γ' = As ++ Γ ∧ As.length = n := by
        induction n generalizing Γ' with
        | zero => cases h; exact ⟨[], rfl, rfl⟩
        | succ n ih => let .skip h := h; obtain ⟨_, rfl, rfl⟩ := ih h; exact ⟨_::_, rfl, rfl⟩
      exact .zero _ eq
    | succ k ih => let .cons h := h; rw [lift'_consN_skipN]; exact .succ (ih h)

theorem Ctx.Lift'.comp (H1 : Ctx.Lift' l₁ Γ₁ Γ₂) (H2 : Ctx.Lift' l₂ Γ₂ Γ₃) :
    Ctx.Lift' (.comp l₁ l₂) Γ₁ Γ₃ := by
  induction H2 generalizing l₁ Γ₁ with
  | refl => exact H1
  | skip _ ih => exact .skip (ih H1)
  | cons H2 ih =>
    cases H1 with
    | refl => exact .cons H2
    | skip H1 => exact .skip (ih H1)
    | cons H1 => rw [← VExpr.lift'_comp]; exact .cons (ih H1)

theorem Ctx.Lift'.of_cons_skip (H : Ctx.Lift' (Lift.consN (.skip l) k) Γ₁ Γ₃) :
    ∃ Γ₂, Ctx.Lift' (Lift.consN l k) Γ₁ Γ₂ ∧ Ctx.LiftN 1 k Γ₂ Γ₃ := by
  induction k generalizing Γ₁ Γ₃ with
  | zero => let .skip H := H; exact ⟨_, H, .one⟩
  | succ k ih =>
    let .cons (A := A) H := H
    let ⟨_, h1, h2⟩ := ih H
    refine ⟨_, .cons h1, ?_⟩
    simp only [Ctx.liftN_iff_lift'] at h2 ⊢
    simpa [← VExpr.lift'_comp, ← Lift.consN_comp] using h2.cons (A := lift' A (.consN l k))

theorem Ctx.Lift'.depth_zero (h : l.depth = 0) : Ctx.Lift' l Γ Γ' → Γ = Γ'
  | .refl => rfl
  | .cons (l := l) H => by rw [VExpr.lift'_depth_zero (l := l) h, H.depth_zero (l := l) h]

variable (Γ₀ : List VExpr) (e₀ A₀ : VExpr) in
inductive Ctx.InstN : Nat → List VExpr → List VExpr → Prop where
  | zero : Ctx.InstN 0 (A₀ :: Γ₀) Γ₀
  | succ : Ctx.InstN k Γ Γ' → Ctx.InstN (k+1) (A::Γ) (A.inst e₀ k :: Γ')

theorem Lookup.lt (H : Lookup Γ i A) : i < Γ.length := by
  induction H with
  | zero => apply Nat.succ_pos
  | succ _ ih => apply Nat.succ_lt_succ ih

def Lookup.ofLt (hi : i < Γ.length) : {A // Lookup Γ i A} :=
  match Γ, i with
  | _::_, 0 => ⟨_, .zero⟩
  | _::_, _+1 => let ⟨_, h⟩ := ofLt (Nat.lt_of_succ_lt_succ hi); ⟨_, .succ h⟩

theorem Lookup.uniq (hA : Lookup Γ i A) (hB : Lookup Γ i B) : A = B :=
  match hA, hB with
  | .zero, .zero => rfl
  | .succ hA, .succ hB => Lookup.uniq hA hB ▸ rfl

theorem Lookup.weakN (W : Ctx.LiftN n k Γ Γ') (H : Lookup Γ i A) :
    Lookup Γ' (liftVar n i k) (A.liftN n k) := by
  induction W generalizing i A with
  | zero As =>
    rw [liftVar_base, Nat.add_comm]
    subst n
    induction As with simp [*]
    | cons _ _ ih => rw [liftN_succ]; exact .succ ih
  | @succ k _ _ _ _ ih =>
    match H with
    | .zero => rw [liftVar_zero, ← lift_liftN']; exact .zero
    | .succ H => rw [liftVar_succ, ← lift_liftN']; exact (ih H).succ

theorem Lookup.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    Lookup Γ' (liftVar n i k) (A.liftN n k) ↔ Lookup Γ i A := by
  refine ⟨fun H => ?_, fun H => H.weakN W⟩
  induction W generalizing i A with
  | zero As =>
    rw [liftVar_base, Nat.add_comm] at H
    subst n
    induction As with simp at H
    | nil => exact H
    | cons A As ih =>
      rw [liftN_succ] at H
      generalize eq : lift (liftN ..) = A' at H
      obtain _|H := H; cases liftN_inj.1 eq
      exact ih H
  | @succ k _ _ _ _ ih =>
    generalize eA : liftN n A (k+1) = A' at H
    cases i with
    | zero =>
      simp at H; let .zero := H
      rw [lift, liftN'_comm (h := Nat.zero_le _), Nat.add_comm 1, liftN_inj] at eA
      subst A; exact .zero
    | succ i =>
      simp at H; let .succ H := H
      obtain ⟨_, rfl, rfl⟩ := of_liftN_eq_liftN (k2 := 0) eA
      exact .succ (ih H)

theorem Lookup.weak'_iff (W : Ctx.Lift' l Γ Γ') :
    Lookup Γ' (l.liftVar i) (A.lift' l) ↔ Lookup Γ i A := by
  generalize e : l.depth = n
  induction n generalizing l Γ' with
  | zero => rw [liftVar_depth_zero e, VExpr.lift'_depth_zero e, W.depth_zero e]
  | succ n ih =>
    obtain ⟨l, k, rfl, rfl⟩ := Lift.depth_succ e
    have ⟨Γ₁, W1, W2⟩ := W.of_cons_skip
    rw [Lift.consN_skip_eq, liftVar_comp, liftVar_consN_skipN, lift'_comp, lift'_consN_skipN,
      weakN_iff W2, ih W1 Lift.depth_consN]

theorem Lookup.instL : Lookup Γ i A → Lookup (Γ.map (VExpr.instL ls)) i (A.instL ls)
  | .zero => instL_liftN ▸ .zero
  | .succ h => instL_liftN ▸ .succ h.instL

def OnCtx (Γ : List VExpr) (P : List VExpr → VExpr → Prop) : Prop :=
  match Γ with
  | [] => True
  | A::Γ => OnCtx Γ P ∧ P Γ A

theorem OnCtx.lookup (h : OnCtx Γ P) (hL : Lookup Γ n A)
    (hP : ∀ {Γ A B}, P Γ A → P (B::Γ) A.lift) : P Γ A :=
  match hL, h with
  | .zero, ⟨h1, h2⟩ => hP h2
  | .succ hL, ⟨h1, h2⟩ => hP (h1.lookup hL hP)

theorem OnCtx.mono (H : ∀ {Γ A}, P Γ A → Q Γ A) : ∀ {Γ}, OnCtx Γ P → OnCtx Γ Q
  | [], h => h
  | _::_, ⟨h1, h2⟩ => ⟨mono H h1, H h2⟩

def CtxClosed : List VExpr → Prop := (OnCtx · fun Γ A => A.ClosedN Γ.length)

theorem CtxClosed.lookup (h : CtxClosed Γ) (hL : Lookup Γ n A) : A.ClosedN Γ.length :=
  match hL, h with
  | .zero, ⟨h1, h2⟩ => h2.liftN
  | .succ hL, ⟨h1, h2⟩ => (CtxClosed.lookup h1 hL).liftN

theorem Ctx.LiftN.right (h : CtxClosed Γ) (Γ') : Ctx.LiftN Γ'.length Γ.length Γ (Γ ++ Γ') :=
  match Γ, h with
  | [], _ => by simpa using LiftN.zero (Γ := []) Γ'
  | A :: Γ, ⟨h1, h2⟩ => by
    simpa [h2.liftN_eq (Nat.le_refl _)] using LiftN.succ (LiftN.right h1 Γ') (A := A)

inductive VObject where
  | const (n : Name) (oci : Option VConstant)
  | defeq (df : VDefEq)

namespace VEnv

theorem addConst_le {env env' : VEnv} (h : env.addConst n oci = some env') : env ≤ env' := by
  unfold addConst at h; split at h <;> cases h
  refine ⟨fun n ci h => ?_, fun _ => id⟩
  simp; rwa [if_neg]; rintro rfl; cases h.symm.trans ‹_ = none›

theorem addConst_self {env env' : VEnv} (h : env.addConst n oci = some env') :
    env'.constants n = some oci := by
  unfold addConst at h; split at h <;> cases h; simp

theorem addDefEq_le {env : VEnv} : env ≤ env.addDefEq df :=
  ⟨fun _ _ => id, fun df h => by simp [addDefEq, h]⟩

theorem addDefEq_self {env : VEnv} : (env.addDefEq df).defeqs df := .inl rfl

def HasObjects (env : VEnv) : List VObject → Prop
  | [] => True
  | .const n oci :: ls => env.constants n = some oci ∧ env.HasObjects ls
  | .defeq df :: ls => env.defeqs df ∧ env.HasObjects ls

theorem HasObjects.mono {env env' : VEnv} (henv : env ≤ env') :
    ∀ {ls}, HasObjects env ls → HasObjects env' ls
  | [] => id
  | .const .. :: _ => .imp (henv.1 _ _) (mono henv)
  | .defeq .. :: _ => .imp (henv.2 _) (mono henv)

theorem HasObjects.const {env env' : VEnv} (hls : env.HasObjects ls)
    (h : env.addConst n oci = some env') : env'.HasObjects (.const n oci :: ls) :=
  ⟨addConst_self h, hls.mono (addConst_le h)⟩

theorem HasObjects.defeq {env : VEnv} (hls : env.HasObjects ls) :
    (addDefEq env df).HasObjects (.defeq df :: ls) := ⟨addDefEq_self, hls.mono addDefEq_le⟩

theorem HasObjects.bind_const {env env' : VEnv} (hls : env.HasObjects ls)
    (h : env.addConst n oci >>= f = some env') :
    ∃ env1, env1.HasObjects (.const n oci :: ls) ∧ f env1 = some env' :=
  let ⟨env1, h1, henv1⟩ := Option.bind_eq_some.1 h; ⟨env1, hls.const h1, henv1⟩

theorem IsDefEq.sort (h : l.WF U) : HasType env U Γ (.sort l) (.sort (.succ l)) :=
  .sortDF h h rfl
theorem IsDefEq.const
    (h1 : env.constants c = some (some ci)) (h2 : ∀ l ∈ ls, l.WF U) (h3 : ls.length = ci.uvars) :
    HasType env U Γ (.const c ls) (ci.type.instL ls) :=
  .constDF h1 h2 h2 h3 (.rfl fun _ _ => rfl)
theorem HasType.app (h1 : HasType env U Γ f (.forallE A B)) (h2 : HasType env U Γ a A) :
    HasType env U Γ (.app f a) (B.inst a) := .appDF h1 h2
theorem HasType.lam (h1 : HasType env U Γ A (.sort u)) (h2 : HasType env U (A::Γ) body B) :
    HasType env U Γ (.lam A body) (.forallE A B) := .lamDF h1 h2
theorem IsDefEq.forallE
    (h1 : HasType env U Γ A (.sort u)) (h2 : HasType env U (A::Γ) body (.sort v)) :
    HasType env U Γ (.forallE A body) (.sort (.imax u v)) := .forallEDF h1 h2
theorem IsDefEq.defeq (h1 : IsDefEq env U Γ A B (.sort u))
    (h2 : HasType env U Γ e A) : HasType env U Γ e B := .defeqDF h1 h2
theorem IsDefEq.defeq' (h1 : IsDefEq env U Γ A B (.sort u))
    (h2 : HasType env U Γ e B) : HasType env U Γ e A := .defeq h1.symm h2

theorem IsDefEq.hasType {env : VEnv} (H : env.IsDefEq U Γ e1 e2 A) :
    env.HasType U Γ e1 A ∧ env.HasType U Γ e2 A := ⟨H.trans H.symm, H.symm.trans H⟩

theorem IsDefEqU.refl {env : VEnv} (h1 : e.WF env U Γ) : env.IsDefEqU U Γ e e := h1
theorem IsDefEqU.symm {env : VEnv} (h1 : env.IsDefEqU U Γ e₁ e₂) : env.IsDefEqU U Γ e₂ e₁ :=
  h1.imp fun _ => (·.symm)

inductive Ordered : VEnv → Prop where
  | empty : Ordered ∅
  | const :
    Ordered env → (∀ ci, oci = some ci → ci.WF env) →
    env.addConst n oci = some env' → Ordered env'
  | defeq : Ordered env → df.WF env → Ordered (env.addDefEq df)

def OnTypes (env : VEnv) (P : Nat → VExpr → VExpr → Prop) : Prop :=
  (∀ {n ci}, env.constants n = some (some ci) → ∃ u, P ci.uvars ci.type (.sort u)) ∧
  (∀ {df}, env.defeqs df → P df.uvars df.lhs df.type ∧ P df.uvars df.rhs df.type)

theorem OnTypes.mono (henv : env' ≤ env) (hP : ∀ {U e A}, P U e A → P' U e A)
    (H : OnTypes env P) : OnTypes env' P' :=
  ⟨fun hci => (H.1 (henv.1 _ _ hci)).imp fun _ => hP, fun hdf => (H.2 (henv.2 _ hdf)).imp hP hP⟩

theorem Ordered.induction (motive : VEnv → Nat → VExpr → VExpr → Prop)
    (mono : ∀ {env env' U e A}, env ≤ env' → motive env U e A → motive env' U e A)
    (type : ∀ {env U e A},
      Ordered env → OnTypes env (motive env) → HasType env U [] e A → motive env U e A)
    (H : Ordered env) : OnTypes env (motive env) := by
  induction H with
  | empty => exact ⟨nofun, nofun⟩
  | const h1 h2 h3 ih =>
    apply OnTypes.mono .rfl (mono (addConst_le h3))
    unfold addConst at h3; split at h3 <;> cases h3
    refine ⟨fun h => ?_, ih.2⟩
    simp at h; split at h
    · cases h
      let ⟨_, ht⟩ := h2 _ rfl
      exact ⟨_, type h1 ih ht⟩
    · exact ih.1 h
  | defeq h1 h2 ih =>
    apply OnTypes.mono .rfl (mono addDefEq_le)
    refine ⟨ih.1, fun hdf => ?_⟩
    simp [addDefEq] at hdf
    obtain rfl | hdf := hdf
    · let ⟨hl, hr⟩ := h2
      exact ⟨type h1 ih hl, type h1 ih hr⟩
    · exact ih.2 hdf

variable (env : VEnv) (U : Nat) (Γ₀ : List VExpr) in
inductive IsDefEqCtx : List VExpr → List VExpr → Prop
  | zero : IsDefEqCtx Γ₀ Γ₀
  | succ :  IsDefEqCtx Γ₁ Γ₂ → env.IsDefEq U Γ₁ A₁ A₂ (.sort u) → IsDefEqCtx (A₁ :: Γ₁) (A₂ :: Γ₂)

theorem IsDefEqCtx.length_eq : IsDefEqCtx env U Γ₀ Γ₁ Γ₂ → Γ₁.length = Γ₂.length
  | .zero => rfl
  | .succ h  _ => congrArg Nat.succ h.length_eq

theorem IsDefEqCtx.isSuffix : IsDefEqCtx env U Γ₀ Γ₁ Γ₂ → Γ₀ <:+ Γ₁ ∧ Γ₀ <:+ Γ₂
  | .zero => ⟨List.suffix_refl _, List.suffix_refl _⟩
  | .succ h _ =>
    let ⟨h1, h2⟩ := h.isSuffix
    ⟨h1.trans (List.suffix_cons _ _), h2.trans (List.suffix_cons _ _)⟩

theorem IsDefEqCtx.isType : IsDefEqCtx env U [] Γ₁ Γ₂ → OnCtx Γ₁ (env.IsType U)
  | .zero => ⟨⟩
  | .succ h1 h2 => ⟨h1.isType, _, h2.hasType.1⟩

variable (henv : OnTypes env fun _ e A => e.ClosedN ∧ A.ClosedN) in
theorem IsDefEq.closedN' (H : env.IsDefEq U Γ e1 e2 A) (hΓ : CtxClosed Γ) :
    e1.ClosedN Γ.length ∧ e2.ClosedN Γ.length ∧ A.ClosedN Γ.length := by
  induction H with
  | bvar h => exact ⟨h.lt, h.lt, hΓ.lookup h⟩
  | constDF h1 =>
    let ⟨_, h, _⟩ := henv.1 h1
    exact ⟨trivial, trivial, h.instL.mono (Nat.zero_le _)⟩
  | sortDF => exact ⟨trivial, trivial, trivial⟩
  | symm _ ih => let ⟨h1, h2, h3⟩ := ih hΓ; exact ⟨h2, h1, h3⟩
  | trans _ _ ih1 ih2 => exact ⟨(ih1 hΓ).1, (ih2 hΓ).2.1, (ih1 hΓ).2.2⟩
  | appDF _ _ ih1 ih2 =>
    let ⟨hf, hf', _, hB⟩ := ih1 hΓ
    let ⟨ha, ha', _⟩ := ih2 hΓ
    exact ⟨⟨hf, ha⟩, ⟨hf', ha'⟩, hB.inst ha⟩
  | lamDF _ _ ih1 ih2 =>
    let ⟨hA, hA', _⟩ := ih1 hΓ
    let ⟨hb, hb', hB⟩ := ih2 ⟨hΓ, hA⟩
    exact ⟨⟨hA, hb⟩, ⟨hA', hb'⟩, hA, hB⟩
  | forallEDF _ _ ih1 ih2 =>
    let ⟨hA, hA', _⟩ := ih1 hΓ
    let ⟨hb, hb', _⟩ := ih2 ⟨hΓ, hA⟩
    exact ⟨⟨hA, hb⟩, ⟨hA', hb'⟩, trivial⟩
  | defeqDF _ _ ih1 ih2 => exact ⟨(ih2 hΓ).1, (ih2 hΓ).2.1, (ih1 hΓ).2.1⟩
  | beta _ _ ih1 ih2 =>
    let ⟨he', _, hA⟩ := ih2 hΓ
    let ⟨he, _, hB⟩ := ih1 ⟨hΓ, hA⟩
    exact ⟨⟨⟨hA, he⟩, he'⟩, he.inst he', hB.inst he'⟩
  | eta _ ih =>
    let ⟨he, _, hA, hB⟩ := ih hΓ
    exact ⟨⟨hA, he.liftN, Nat.succ_pos _⟩, he, hA, hB⟩
  | proofIrrel _ _ _ _ ih2 ih3 =>
    let ⟨hh, _, _⟩ := ih2 hΓ
    let ⟨hh', _, hp⟩ := ih3 hΓ
    exact ⟨hh, hh', hp⟩
  | extra h1 _ _ =>
    let ⟨⟨hl, _⟩, ⟨hr, hA⟩⟩ := henv.2 h1
    exact ⟨
      hl.instL.mono (Nat.zero_le _),
      hr.instL.mono (Nat.zero_le _),
      hA.instL.mono (Nat.zero_le _)⟩

theorem Ordered.closed (H : Ordered env) : env.OnTypes fun _ e A => e.ClosedN ∧ A.ClosedN :=
  H.induction _ (fun _ => id) fun _ ih h => (IsDefEq.closedN' ih h trivial).2

theorem Ordered.closedC (H : Ordered env)
    (h : env.constants n = some (some ci)) : ci.type.ClosedN :=
  let ⟨_, h⟩ := H.closed.1 h; h.1

theorem IsDefEq.closedN {env : VEnv} (henv : env.Ordered)
    (H : env.IsDefEq U Γ e1 e2 A) (hΓ : CtxClosed Γ) : e1.ClosedN Γ.length :=
  (H.closedN' henv.closed hΓ).1

variable (henv : Ordered env) in
theorem IsDefEqCtx.closed (H : CtxClosed Γ₀) :
    IsDefEqCtx env U Γ₀ Γ₁ Γ₂ → CtxClosed Γ₁ ∧ CtxClosed Γ₂
  | .zero => ⟨H, H⟩
  | .succ h1 h2 =>
    have ⟨c1, c2⟩ := h1.closed H
    ⟨⟨c1, h2.closedN henv c1⟩, ⟨c2, by simpa [h1.length_eq] using h2.symm.closedN henv c1⟩⟩

variable {env env' : VEnv} (henv : env ≤ env') in
theorem IsDefEq.mono (H : env.IsDefEq U Γ e1 e2 A) : env'.IsDefEq U Γ e1 e2 A := by
  induction H with
  | bvar h => exact .bvar h
  | constDF h1 h2 h3 h4 h5 => exact .constDF (henv.1 _ _ h1) h2 h3 h4 h5
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | appDF _ _ ih1 ih2 => exact .appDF ih1 ih2
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ ih1 ih2 => exact .beta ih1 ih2
  | eta _ ih => exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 => exact .extra (henv.2 _ h1) h2 h3

theorem HasType.mono {env env' : VEnv} (henv : env ≤ env') :
    env.HasType U Γ e A → env'.HasType U Γ e A := IsDefEq.mono henv

theorem IsType.mono {env env' : VEnv} (henv : env ≤ env') : env.IsType U Γ A → env'.IsType U Γ A
  | ⟨u, h⟩ => ⟨u, h.mono henv⟩

end VEnv

theorem VConstant.WF.mono {env env' : VEnv} (henv : env ≤ env') {ci : VConstant} :
    ci.WF env → ci.WF env'
  | ⟨u, h⟩ => ⟨u, h.mono henv⟩

theorem VDefEq.WF.mono {env env' : VEnv} (henv : env ≤ env') {df : VDefEq} : df.WF env → df.WF env'
  | ⟨h1, h2⟩ => ⟨h1.mono henv, h2.mono henv⟩

namespace VEnv

theorem Ordered.constWF (H : Ordered env) (h : env.constants n = some (some ci)) : ci.WF env := by
  induction H with
  | empty => cases h
  | const _ h2 h3 ih =>
    refine .mono (addConst_le h3) ?_
    unfold addConst at h3; split at h3 <;> cases h3
    simp at h; split at h
    · cases h; exact h2 _ rfl
    · exact ih h
  | defeq _ _ ih => exact .mono addDefEq_le (ih h)

theorem Ordered.defEqWF (H : Ordered env) (h : env.defeqs df) : df.WF env := by
  induction H with
  | empty => cases h
  | const _ _ h3 ih =>
    refine .mono (addConst_le h3) (ih ?_)
    unfold addConst at h3; split at h3 <;> cases h3; exact h
  | defeq _ _ ih =>
    refine .mono addDefEq_le ?_
    obtain rfl | h := h
    · assumption
    · exact ih h

variable (henv : Ordered env) in
theorem CtxWF.closed (h : OnCtx Γ (IsType env U)) : CtxClosed Γ :=
  match Γ, h with
  | [], _ => trivial
  | _::_, ⟨h1, _, h2⟩ => ⟨closed h1, h2.closedN henv (closed h1)⟩

variable {env : VEnv} in
theorem IsDefEq.levelWF (H : env.IsDefEq U Γ e1 e2 A) (W : OnCtx Γ fun _ A => A.LevelWF U) :
    e1.LevelWF U ∧ e2.LevelWF U ∧ A.LevelWF U := by
  induction H with
  | bvar h =>
    refine ⟨⟨⟩, ⟨⟩, ?_⟩
    induction h with
    | zero => exact W.2.liftN
    | succ _ ih => exact (ih W.1).liftN
  | symm _ ih => let ⟨he, he', hA⟩ := ih W; exact ⟨he', he, hA⟩
  | trans _ _ ih1 ih2 => let ⟨he1, _, hA⟩ := ih1 W; let ⟨_, he3, _⟩ := ih2 W; exact ⟨he1, he3, hA⟩
  | sortDF h1 h2 => exact ⟨h1, h2, h1⟩
  | constDF _ h2 h3 => exact ⟨h2, h3, .instL h2⟩
  | appDF _ _ ih1 ih2 =>
    let ⟨hf, hf', _, hB⟩ := ih1 W; let ⟨ha, ha', _⟩ := ih2 W
    exact ⟨⟨hf, ha⟩, ⟨hf', ha'⟩, hB.inst ha⟩
  | lamDF _ _ ih1 ih2 =>
    let ⟨hA, hA', _⟩ := ih1 W; let ⟨hb, hb', hB⟩ := ih2 ⟨W, hA⟩
    exact ⟨⟨hA, hb⟩, ⟨hA', hb'⟩, hA, hB⟩
  | forallEDF _ _ ih1 ih2 =>
    let ⟨hA, hA', hu⟩ := ih1 W; let ⟨hb, hb', hv⟩ := ih2 ⟨W, hA⟩
    exact ⟨⟨hA, hb⟩, ⟨hA', hb'⟩, hu, hv⟩
  | defeqDF _ _ ih1 ih2 => let ⟨_, hB, _⟩ := ih1 W; let ⟨he1, he2, _⟩ := ih2 W; exact ⟨he1, he2, hB⟩
  | beta _ _ ih1 ih2 =>
    let ⟨he', _, hA⟩ := ih2 W; let ⟨he, _, hB⟩ := ih1 ⟨W, hA⟩
    exact ⟨⟨⟨hA, he⟩, he'⟩, he.inst he', hB.inst he'⟩
  | eta _ ih => let ⟨he, _, hA, hB⟩ := ih W; exact ⟨⟨hA, he.liftN, ⟨⟩⟩, he, hA, hB⟩
  | proofIrrel _ _ _ _ ih2 ih3 =>
    let ⟨hh, _, hp⟩ := ih2 W; let ⟨hh', _, _⟩ := ih3 W
    exact ⟨hh, hh', hp⟩
  | extra _ h2 => exact ⟨.instL h2, .instL h2, .instL h2⟩

variable (henv : Ordered env) in
theorem IsDefEq.weakN (W : Ctx.LiftN n k Γ Γ') (H : env.IsDefEq U Γ e1 e2 A) :
    env.IsDefEq U Γ' (e1.liftN n k) (e2.liftN n k) (A.liftN n k) := by
  induction H generalizing k Γ' with
  | bvar h => refine .bvar (h.weakN W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 =>
    rw [(henv.closedC h1).instL.liftN_eq (Nat.zero_le _)]
    exact .constDF h1 h2 h3 h4 h5
  | appDF _ _ ih1 ih2 => exact liftN_inst_hi .. ▸ .appDF (ih1 W) (ih2 W)
  | lamDF _ _ ih1 ih2 => exact .lamDF (ih1 W) (ih2 W.succ)
  | forallEDF _ _ ih1 ih2 => exact .forallEDF (ih1 W) (ih2 W.succ)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ ih1 ih2 =>
    exact VExpr.liftN_inst_hi .. ▸ VExpr.liftN_instN_hi .. ▸ .beta (ih1 W.succ) (ih2 W)
  | eta _ ih =>
    have := IsDefEq.eta (ih W)
    simp [liftN]; rwa [← lift_liftN']
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 h3 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
    rw [
      hA1.instL.liftN_eq (Nat.zero_le _),
      hA2.instL.liftN_eq (Nat.zero_le _),
      hA3.instL.liftN_eq (Nat.zero_le _)]
    exact .extra h1 h2 h3

variable (henv : Ordered env) in
theorem HasType.weakN (W : Ctx.LiftN n k Γ Γ') (H : env.HasType U Γ e A) :
    env.HasType U Γ' (e.liftN n k) (A.liftN n k) := IsDefEq.weakN henv W H

variable (henv : Ordered env) in
theorem IsType.weakN (W : Ctx.LiftN n k Γ Γ') (H : env.IsType U Γ A) :
    env.IsType U Γ' (A.liftN n k) := let ⟨_, h⟩ := H; ⟨_, h.weakN henv W⟩

variable (henv : Ordered env) in
theorem IsDefEq.weak (H : env.IsDefEq U Γ e1 e2 A) :
    env.IsDefEq U (B::Γ) e1.lift e2.lift A.lift := H.weakN henv .one

variable (henv : Ordered env) in
theorem IsDefEq.weakR (hΓ : CtxClosed Γ) (H : env.IsDefEq U Γ e1 e2 A) (Γ') :
    env.IsDefEq U (Γ ++ Γ') e1 e2 A := by
  have ⟨h1, h2, h3⟩ := H.closedN' henv.closed hΓ
  simpa [h1.liftN_eq, h2.liftN_eq, h3.liftN_eq] using H.weakN henv (.right hΓ Γ')

variable (henv : Ordered env) in
theorem IsDefEq.weak0 (H : env.IsDefEq U [] e1 e2 A) : env.IsDefEq U Γ e1 e2 A :=
  H.weakR henv (Γ := []) ⟨⟩ _

variable (henv : Ordered env) in
nonrec theorem HasType.weak0 (H : env.HasType U [] e A) : env.HasType U Γ e A := H.weak0 henv

variable (henv : Ordered env) in
theorem IsDefEq.weak' (W : Ctx.Lift' l Γ Γ') (H : env.IsDefEq U Γ e1 e2 A) :
    env.IsDefEq U Γ' (e1.lift' l) (e2.lift' l) (A.lift' l) := by
  generalize e : l.depth = n
  induction n generalizing l Γ' with
  | zero => simpa [lift'_depth_zero e, W.depth_zero e] using H
  | succ n ih =>
    obtain ⟨l, k, rfl, rfl⟩ := Lift.depth_succ e
    have ⟨Γ₁, W1, W2⟩ := W.of_cons_skip
    simp only [Lift.consN_skip_eq, lift'_comp, lift'_consN_skipN]
    exact (ih W1 Lift.depth_consN).weakN henv W2

theorem IsType.lookup (henv : Ordered env) (h : OnCtx Γ (IsType env U)) (hL : Lookup Γ n A) :
    env.IsType U Γ A := h.lookup hL <| .weakN henv .one

variable {env : VEnv} {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U') in
theorem IsDefEq.instL (H : env.IsDefEq U Γ e1 e2 A) :
    env.IsDefEq U' (Γ.map (VExpr.instL ls)) (e1.instL ls) (e2.instL ls) (A.instL ls) := by
  induction H with
  | bvar h => refine .bvar h.instL
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF _ _ h3 =>
    exact .sortDF (VLevel.WF.inst hls) (VLevel.WF.inst hls) (VLevel.inst_congr_l h3)
  | @constDF _ _ ls₁ ls₂ _ h1 h2 h3 h4 h5 =>
    simp [VExpr.instL, VExpr.instL_instL]
    exact .constDF h1 (by simp [h2, VLevel.WF.inst hls]) (by simp [h3, VLevel.WF.inst hls])
      (by simp [h4]) (by simpa using h5.imp fun _ _ => VLevel.inst_congr_l)
  | appDF _ _ ih1 ih2 => exact VExpr.instL_instN ▸ .appDF ih1 ih2
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ ih1 ih2 => simpa using .beta ih1 ih2
  | eta _ ih => simpa [VExpr.instL] using .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 =>
    simp [VExpr.instL, VExpr.instL_instL]
    exact .extra h1 (by simp [h2, VLevel.WF.inst hls]) (by simp [h3])

theorem HasType.instL {env : VEnv} (hls : ∀ l ∈ ls, l.WF U') (H : env.HasType U Γ e A) :
    env.HasType U' (Γ.map (VExpr.instL ls)) (e.instL ls) (A.instL ls) := IsDefEq.instL hls H

theorem IsType.instL {env : VEnv} (hls : ∀ l ∈ ls, l.WF U') (H : env.IsType U Γ A) :
    env.IsType U' (Γ.map (VExpr.instL ls)) (A.instL ls) := let ⟨_, h⟩ := H; ⟨_, h.instL hls⟩

variable (henv : Ordered env) (h₀ : env.HasType U Γ₀ e₀ A₀) in
theorem IsDefEq.instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (H : env.IsDefEq U Γ₁ e1 e2 A) :
    env.IsDefEq U Γ (e1.inst e₀ k) (e2.inst e₀ k) (A.inst e₀ k) := by
  induction H generalizing Γ k with
  | @bvar _ i ty h =>
    dsimp [inst]
    induction W generalizing i ty with
    | zero =>
      cases h with simp [inst_lift]
      | zero => exact h₀
      | succ h => exact .bvar h
    | succ _ ih =>
      cases h with (simp; rw [Nat.add_comm, ← VExpr.liftN_instN_lo (hj := Nat.zero_le _)])
      | zero => exact .bvar .zero
      | succ h => exact (ih h).weak henv
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 =>
    rw [(henv.closedC h1).instL.instN_eq (Nat.zero_le _)]
    exact .constDF h1 h2 h3 h4 h5
  | appDF _ _ ih1 ih2 => exact VExpr.inst_inst_hi .. ▸ .appDF (ih1 W) (ih2 W)
  | lamDF _ _ ih1 ih2 => exact .lamDF (ih1 W) (ih2 W.succ)
  | forallEDF _ _ ih1 ih2 => exact .forallEDF (ih1 W) (ih2 W.succ)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ ih1 ih2 =>
    exact VExpr.inst_inst_hi .. ▸ VExpr.inst_inst_hi .. ▸ .beta (ih1 W.succ) (ih2 W)
  | eta _ ih =>
    have := IsDefEq.eta (ih W)
    rw [lift, VExpr.liftN_instN_lo (hj := Nat.zero_le _), Nat.add_comm] at this
    simpa [inst]
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 h3 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
    rw [
      hA1.instL.instN_eq (Nat.zero_le _),
      hA2.instL.instN_eq (Nat.zero_le _),
      hA3.instL.instN_eq (Nat.zero_le _)]
    exact .extra h1 h2 h3

theorem HasType.instN {env : VEnv} (henv : env.Ordered) (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (H : env.HasType U Γ₁ e A) (h₀ : env.HasType U Γ₀ e₀ A₀) :
    env.HasType U Γ (e.inst e₀ k) (A.inst e₀ k) := IsDefEq.instN henv h₀ W H

theorem IsType.instN {env : VEnv} (henv : env.Ordered) (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (H : env.IsType U Γ₁ A) (h₀ : env.HasType U Γ₀ e₀ A₀) :
    env.IsType U Γ (A.inst e₀ k) := let ⟨_, h⟩ := H; ⟨_, h.instN henv W h₀⟩

theorem IsDefEq.defeqDF_l' (henv : Ordered env) (h1 : env.IsDefEq U Γ A A' (.sort u))
    (h2 : env.IsDefEq U (Δ++A::Γ) e1 e2 B) : env.IsDefEq U (Δ++A'::Γ) e1 e2 B := by
  have ⟨_, H1, H2⟩ : ∃ Γ', Ctx.LiftN 1 (Δ.length + 1) (Δ ++ A :: Γ) Γ' ∧
      Ctx.InstN (A' :: Γ) (VExpr.bvar 0) (liftN 1 A) Δ.length Γ' (Δ ++ A' :: Γ) := by
    clear h1 h2
    induction Δ with
    | nil => exact ⟨_, .succ (.one (A := A')), .zero⟩
    | cons B Δ ih =>
      have ⟨Γ', h1, h2⟩ := ih
      exact ⟨_, .succ h1, by simpa [instN_bvar0] using h2.succ (A := liftN 1 B (Δ.length + 1))⟩
  simpa [instN_bvar0] using
    instN henv (h1.weakN henv (.one (A := A')) |>.symm.defeq (.bvar .zero)) H2 (.weakN henv H1 h2)

theorem IsDefEq.defeqDF_l (henv : Ordered env) (h1 : env.IsDefEq U Γ A A' (.sort u))
    (h2 : env.IsDefEq U (A::Γ) e1 e2 B) : env.IsDefEq U (A'::Γ) e1 e2 B :=
  .defeqDF_l' (Δ := []) henv h1 h2

theorem HasType.defeq_l (henv : Ordered env) (h1 : env.IsDefEq U Γ A A' (.sort u))
    (h2 : env.HasType U (A::Γ) e B) : env.HasType U (A'::Γ) e B := h1.defeqDF_l henv h2

theorem IsDefEq.defeqDFC' (henv : Ordered env) (h1 : IsDefEqCtx env U Γ₀ Γ₁ Γ₂)
    (h2 : env.IsDefEq U (Δ ++ Γ₁) e₁ e₂ A) : env.IsDefEq U (Δ ++ Γ₂) e₁ e₂ A := by
  induction h1 generalizing e₁ e₂ A Δ with
  | zero => exact h2
  | @succ _ _ _ A₂ _ _ AA ih =>
    simpa using ih (Δ := Δ ++ [A₂]) (by simpa using AA.defeqDF_l' henv h2)

theorem IsDefEq.defeqDFC (henv : Ordered env) (h1 : IsDefEqCtx env U Γ₀ Γ₁ Γ₂)
    (h2 : env.IsDefEq U Γ₁ e₁ e₂ A) : env.IsDefEq U Γ₂ e₁ e₂ A := .defeqDFC' (Δ := []) henv h1 h2

theorem IsType.defeqDFC (henv : Ordered env) (h1 : IsDefEqCtx env U Γ₀ Γ₁ Γ₂)
    (h2 : env.IsType U Γ₁ A) : env.IsType U Γ₂ A := h2.imp fun _ => (·.defeqDFC henv h1)

theorem IsDefEqCtx.symm (henv : Ordered env) :
    IsDefEqCtx env U Γ₀ Γ₁ Γ₂ → IsDefEqCtx env U Γ₀ Γ₂ Γ₁
  | .zero => .zero
  | .succ h1 h2 => .succ (h1.symm henv) (h2.symm.defeqDFC henv h1)

variable (henv : Ordered env)
  (envIH : env.OnTypes fun U e _ => ∀ A B, e = A.forallE B →
    env.IsType U [] A ∧ env.IsType U [A] B) in
theorem IsDefEq.forallE_inv'
    (H : env.IsDefEq U Γ e1 e2 V) (eq : e1 = A.forallE B ∨ e2 = A.forallE B) :
    env.IsType U Γ A ∧ env.IsType U (A::Γ) B := by
  induction H generalizing A B with
  | symm _ ih => exact ih eq.symm
  | trans _ _ ih1 ih2
  | proofIrrel _ _ _ _ ih1 ih2 =>
    obtain eq | eq := eq
    · exact ih1 (.inl eq)
    · exact ih2 (.inr eq)
  | forallEDF h1 h2 =>
    obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq
    · exact ⟨⟨_, h1.hasType.1⟩, _, h2.hasType.1⟩
    · exact ⟨⟨_, h1.hasType.2⟩, _, h2.hasType.2.defeq_l henv h1⟩
  | defeqDF _ _ _ ih2 => exact ih2 eq
  | @beta _ _ e _ _ h1 h2 ih1 ih2 =>
    obtain ⟨⟨⟩⟩ | eq := eq
    cases e with
    | bvar i =>
      cases i with simp [inst] at eq
      | zero => exact ih2 (.inl eq)
    | forallE A B =>
      cases eq
      let ⟨A1, A2⟩ := ih1 (.inl rfl)
      exact ⟨A1.instN henv .zero h2, A2.instN henv (.succ .zero) h2⟩
    | _ => cases eq
  | eta _ ih =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih (.inl eq)
  | @extra df ls Γ h1 h2 =>
    suffices ∀ e, VExpr.instL ls e = VExpr.forallE A B →
        (∀ A B, e = VExpr.forallE A B → IsType env df.uvars [] A ∧ IsType env df.uvars [A] B) →
        IsType env U Γ A ∧ IsType env U (A :: Γ) B by
      have ⟨A1, A2⟩ := envIH.2 h1
      cases eq <;> exact this _ ‹_› ‹_›
    intro e eq IH
    cases e <;> cases eq; rename_i A B
    let ⟨⟨_, A1⟩, v, A2⟩ := IH _ _ rfl
    refine ⟨⟨_, (A1.instL h2).weak0 henv⟩, v.inst ls, ?_⟩
    have := (A2.instL h2).weakN henv (.succ (.zero Γ))
    have C1 := (A1.instL h2).closedN henv ⟨⟩
    have C2 := (A2.instL h2).closedN henv ⟨⟨⟩, C1⟩
    rw [C1.liftN_eq (Nat.zero_le _), C2.liftN_eq (by exact Nat.le_refl _)] at this
    simpa [liftN]
  | _ => nomatch eq

theorem HasType.forallE_inv (henv : Ordered env) (H : env.HasType U Γ (A.forallE B) V) :
    env.IsType U Γ A ∧ env.IsType U (A::Γ) B := by
  refine H.forallE_inv' henv ?_ (.inl rfl)
  exact henv.induction
    (fun env U e _ => ∀ A B, e = forallE A B → IsType env U [] A ∧ IsType env U [A] B)
    (fun le H A B eq => (H A B eq).imp (.mono le) (.mono le))
    (fun henv IH H A B eq => H.forallE_inv' henv IH (.inl eq))

theorem IsType.forallE_inv (henv : Ordered env) (H : env.IsType U Γ (A.forallE B)) :
    env.IsType U Γ A ∧ env.IsType U (A::Γ) B := let ⟨_, h⟩ := H; h.forallE_inv henv

variable (henv : Ordered env) in
theorem IsDefEq.sort_inv'
    (H : env.IsDefEq U Γ e1 e2 V) (eq : e1 = .sort u ∨ e2 = .sort u) : u.WF U := by
  induction H with
  | symm _ ih => exact ih eq.symm
  | trans _ _ ih1 ih2
  | proofIrrel _ _ _ _ ih1 ih2 =>
    obtain eq | eq := eq <;> [exact ih1 (.inl eq); exact ih2 (.inr eq)]
  | sortDF => obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq <;> assumption
  | defeqDF _ _ _ ih2 => exact ih2 eq
  | @beta _ _ e _ _ h1 _ ih1 ih2 =>
    obtain ⟨⟨⟩⟩ | eq := eq
    cases e with
    | bvar i =>
      cases i with simp [inst] at eq
      | zero => exact ih2 (.inl eq)
    | _ => cases eq <;> exact ih1 (.inl rfl)
  | eta _ ih =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih (.inl eq)
  | @extra df ls _ h1 h2 =>
    suffices ∀ e, VExpr.instL ls e = .sort u → HasType env df.uvars [] e df.type → u.WF U by
      have ⟨A1, A2⟩ := henv.defEqWF h1
      cases eq <;> exact this _ ‹_› ‹_›
    intro e eq IH
    cases e <;> cases eq; rename_i u
    exact VLevel.WF.inst h2
  | _ => nomatch eq

theorem IsDefEq.sort_inv_l (henv : Ordered env) (H : env.IsDefEq U Γ (.sort u) e2 V) : u.WF U :=
  H.sort_inv' henv (.inl rfl)

theorem IsDefEq.sort_inv_r (henv : Ordered env) (H : env.IsDefEq U Γ e2 (.sort u) V) : u.WF U :=
  H.sort_inv' henv (.inr rfl)

theorem HasType.sort_inv (henv : Ordered env) (H : env.HasType U Γ (.sort u) V) : u.WF U :=
  H.sort_inv_l henv

theorem IsType.sort_inv (henv : Ordered env) (H : env.IsType U Γ (.sort u)) : u.WF U :=
  let ⟨_, h⟩ := H; h.sort_inv henv

variable (henv : Ordered env)
  (envIH : env.OnTypes fun U e A => env.HasType U [] e A ∧ env.IsType U [] A) in
theorem IsDefEq.isType' (hΓ : OnCtx Γ (env.IsType U)) (H : env.IsDefEq U Γ e1 e2 A) :
    env.IsType U Γ A := by
  induction H with
  | bvar h => exact .lookup henv hΓ  h
  | proofIrrel h1 => exact ⟨_, h1⟩
  | extra h1 h2 =>
    have ⟨_, _, _, h⟩ := envIH.2 h1
    exact ⟨_, (h.instL h2).weak0 henv⟩
  | sortDF h1 => exact ⟨_, .sort h1⟩
  | constDF h1 h2 =>
    let ⟨_, h, _⟩ := envIH.1 h1
    exact ⟨_, (h.instL h2).weak0 henv⟩
  | symm _ ih => exact ih hΓ
  | trans _ _ ih1 => exact ih1 hΓ
  | appDF _ h2 ih1 => exact ((ih1 hΓ).forallE_inv henv).2.instN henv .zero h2.hasType.1
  | lamDF h1 _ _ ih2 =>
    let ⟨_, h⟩ := ih2 ⟨hΓ, _, h1.hasType.1⟩
    exact ⟨_, .forallE h1.hasType.1 h⟩
  | forallEDF h1 _ ih1 ih2 =>
    exact ⟨_, .sort ⟨(ih1 hΓ).sort_inv henv, (ih2 ⟨hΓ, _, h1.hasType.1⟩).sort_inv henv⟩⟩
  | defeqDF h1 => exact ⟨_, h1.hasType.2⟩
  | beta _ h2 ih1 ih2 =>
    have ⟨_, h⟩ := ih2 hΓ
    exact (ih1 ⟨hΓ, _, h.hasType.2⟩).instN henv .zero h2
  | eta _ ih => exact ih hΓ

theorem Ordered.isType (H : Ordered env) :
    env.OnTypes fun U e A => env.HasType U [] e A ∧ env.IsType U [] A :=
  H.induction (fun env U e A => env.HasType U [] e A ∧ env.IsType U [] A)
    (fun h1 h2 => h2.imp (.mono h1) (.mono h1))
    (fun henv ih h => ⟨h, h.isType' henv ih trivial⟩)

theorem IsDefEq.isType (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEq U Γ e1 e2 A) : env.IsType U Γ A := H.isType' henv henv.isType hΓ

theorem IsDefEq.sort_r (henv : Ordered env)
    (hΓ : OnCtx Γ (env.IsType U)) (H : env.IsDefEq U Γ e1 e2 (.sort u)) : u.WF U :=
  (H.isType henv hΓ).sort_inv henv

theorem IsDefEq.instDF
    (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.IsDefEq U (A::Γ) f f' B) (ha : env.IsDefEq U Γ a a' A) :
    env.IsDefEq U Γ (f.inst a) (f'.inst a') (B.inst a) :=
  have ⟨_, hA⟩ := ha.isType henv hΓ
  have ⟨_, hB⟩ := hf.isType henv (Γ := _::_) ⟨hΓ, _, hA⟩
  have H2 {f f' B v}
      (hf : env.IsDefEq U (A::Γ) f f' B)
      (hi : IsDefEq env U Γ (inst B a) (inst B a') (.sort v)) :
      env.IsDefEq U Γ (f.inst a) (f'.inst a') (B.inst a) :=
    (IsDefEq.beta hf.hasType.1 ha.hasType.1).symm.trans <|
      .trans (.appDF (.lamDF hA hf) ha) <|
      .defeqDF (.symm hi) (.beta hf.hasType.2 ha.hasType.2)
  H2 hf <| H2 hB (.sort (hB.sort_r henv (Γ := _::_) ⟨hΓ, _, hA⟩))
