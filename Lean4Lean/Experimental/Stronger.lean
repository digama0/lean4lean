import Lean4Lean.Theory.Typing.Lemmas

namespace Lean4Lean

open VExpr

structure VEnv'.VConstant extends Lean4Lean.VConstant where
  level : VLevel

structure VEnv'.VDefEq extends Lean4Lean.VDefEq where
  level : VLevel

@[ext] structure VEnv' where
  constants : Name → Option (Option VEnv'.VConstant)
  defeqs : VEnv'.VDefEq → Prop

namespace VEnv'

def empty : VEnv' where
  constants _ := none
  defeqs _ := False

instance : EmptyCollection VEnv' := ⟨.empty⟩

protected def out (env : VEnv') : VEnv where
  constants c := (env.constants c).map (·.map (·.toVConstant))
  defeqs df := ∃ df', env.defeqs df' ∧ df = df'.toVDefEq

@[simp] theorem empty_out : (∅ : VEnv').out = ∅ := by
  simp [VEnv'.out, EmptyCollection.emptyCollection, empty, VEnv.empty]

protected structure LE (env1 env2 : VEnv') : Prop where
  constants : env1.constants n = some a → env2.constants n = some a
  defeqs : env1.defeqs df → env2.defeqs df

instance : LE VEnv' := ⟨VEnv'.LE⟩

theorem LE.rfl {env : VEnv'} : env ≤ env := ⟨id, id⟩

theorem LE.trans {a b c : VEnv'} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  ⟨h2.1 ∘ h1.1, h2.2 ∘ h1.2⟩

section
set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:30 " : " l:30 => IsDefEqStrong Γ e e A l
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:30 " : " l:30 => IsDefEqStrong Γ e1 e2 A l
variable (env : VEnv') (uvars : Nat)

abbrev VCtx := List (VExpr × VLevel)

def VCtx.out : VCtx → List VExpr := List.map Prod.fst

inductive Lookup : VCtx → Nat → VExpr → VLevel → Prop where
  | zero : Lookup ((ty, u)::Γ) 0 ty.lift u
  | succ : Lookup Γ n ty u → Lookup ((A, v)::Γ) (n+1) ty.lift u

inductive IsDefEqStrong : VCtx → VExpr → VExpr → VExpr → VLevel → Prop where
  | bvar : Lookup Γ i A u → u.WF uvars → Γ ⊢ A : .sort u : .succ u → Γ ⊢ .bvar i : A : u
  | symm : Γ ⊢ e ≡ e' : A : u → Γ ⊢ e' ≡ e : A : u
  | trans : Γ ⊢ e₁ ≡ e₂ : A : u → Γ ⊢ e₂ ≡ e₃ : A : u → Γ ⊢ e₁ ≡ e₃ : A : u
  | sortDF :
    l.WF uvars → l'.WF uvars → l ≈ l' →
    Γ ⊢ .sort l ≡ .sort l' : .sort (.succ l) : .succ (.succ l)
  | constDF :
    env.constants c = some (some ci) →
    (∀ l ∈ ls, l.WF uvars) →
    (∀ l ∈ ls', l.WF uvars) →
    ls.length = ci.uvars →
    List.Forall₂ (· ≈ ·) ls ls' →
    u ≈ ci.level.inst ls → u.WF uvars →
    [] ⊢ ci.type.instL ls : .sort u : .succ u →
    [] ⊢ ci.type.instL ls' : .sort u : .succ u →
    Γ ⊢ ci.type.instL ls : .sort u : .succ u →
    Γ ⊢ ci.type.instL ls' : .sort u : .succ u →
    Γ ⊢ .const c ls ≡ .const c ls' : ci.type.instL ls : u
  | appDF :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A : .sort u : .succ u →
    (A,u)::Γ ⊢ B : .sort v : .succ v →
    Γ ⊢ f ≡ f' : .forallE A B : .imax u v →
    Γ ⊢ a ≡ a' : A : u →
    Γ ⊢ B.inst a ≡ B.inst a' : .sort v : .succ v →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a : v
  | lamDF :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A ≡ A' : .sort u : .succ u →
    (A, u)::Γ ⊢ B : .sort v : .succ v →
    (A', u)::Γ ⊢ B : .sort v : .succ v →
    (A, u)::Γ ⊢ body ≡ body' : B : v →
    (A', u)::Γ ⊢ body ≡ body' : B : v →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B : .imax u v
  | forallEDF :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A ≡ A' : .sort u : .succ u →
    (A, u)::Γ ⊢ body ≡ body' : .sort v : .succ v →
    (A', u)::Γ ⊢ body ≡ body' : .sort v : .succ v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort (.imax u v) : .succ (.imax u v)
  | defeqDF :
    u.WF uvars → Γ ⊢ A ≡ B : .sort u : .succ u → Γ ⊢ e1 ≡ e2 : A : u → Γ ⊢ e1 ≡ e2 : B : u
  | defeqL :
    u.WF uvars → v.WF uvars → u ≈ v → Γ ⊢ e1 ≡ e2 : A : u → Γ ⊢ e1 ≡ e2 : A : v
  | beta :
    u.WF uvars → v.WF uvars → Γ ⊢ A : .sort u : .succ u → (A, u)::Γ ⊢ B : .sort v : .succ v →
    (A, u)::Γ ⊢ e : B : v → Γ ⊢ e' : A : u →
    Γ ⊢ B.inst e' : .sort v : .succ v →
    Γ ⊢ e.inst e' : B.inst e' : v →
    Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e' : v
  | eta :
    u.WF uvars → v.WF uvars →
    Γ ⊢ A : .sort u : .succ u →
    (A, u)::Γ ⊢ B : .sort v : .succ v →
    (A.lift, u)::(A, u)::Γ ⊢ B.liftN 1 1 : .sort v : .succ v →
    Γ ⊢ e : .forallE A B : .imax u v →
    (A, u)::Γ ⊢ e.lift : .forallE A.lift (B.liftN 1 1) : .imax u v →
    Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B : .imax u v
  | proofIrrel :
    Γ ⊢ p : .sort .zero : .succ .zero → Γ ⊢ h : p : .zero → Γ ⊢ h' : p : .zero →
    Γ ⊢ h ≡ h' : p : .zero
  | extra :
    env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
    u ≈ df.level.inst ls → u.WF uvars →
    [] ⊢ df.type.instL ls : .sort u : .succ u →
    [] ⊢ df.lhs.instL ls : df.type.instL ls : u →
    [] ⊢ df.rhs.instL ls : df.type.instL ls : u →
    Γ ⊢ df.lhs.instL ls : df.type.instL ls : u →
    Γ ⊢ df.rhs.instL ls : df.type.instL ls : u →
    Γ ⊢ df.lhs.instL ls ≡ df.rhs.instL ls : df.type.instL ls : u

end

def HasType (env : VEnv') (U : Nat) (Γ : VCtx) (e A : VExpr) (u : VLevel) : Prop :=
  IsDefEqStrong env U Γ e e A u

def IsType (env : VEnv') (U : Nat) (Γ : VCtx) (A : VExpr) (u : VLevel) : Prop :=
  env.HasType U Γ A (.sort u) (.succ u)

def VConstant.WF (env : VEnv') (ci : VConstant) : Prop := env.IsType ci.uvars [] ci.type ci.level

def VDefEq.WF (env : VEnv') (df : VDefEq) : Prop :=
  env.HasType df.uvars [] df.lhs df.type df.level ∧ env.HasType df.uvars [] df.rhs df.type df.level

def addConst (env : VEnv') (name : Name) (ci : Option VConstant) : Option VEnv' :=
  match env.constants name with
  | some _ => none
  | none => some { env with constants := fun n => if name = n then some ci else env.constants n }

theorem addConst_out {env : VEnv'} (H : env.addConst n ci = some env₂) :
    env.out.addConst n (ci.map (·.toVConstant)) = some env₂.out := by
  revert H; simp [addConst, VEnv.addConst, VEnv'.out]
  cases env.constants n <;> simp
  rintro rfl; simp; ext x; split <;> simp

theorem constants_out {env : VEnv'} (H : env.constants n = some (some ci)) :
    env.out.constants n = some (some ci.toVConstant) := by simp [VEnv'.out, H]

theorem defeqs_out {env : VEnv'} (H : env.defeqs df) :
    env.out.defeqs df.toVDefEq := ⟨_, H, rfl⟩

def addDefEq (env : VEnv') (df : VDefEq) : VEnv' :=
  { env with defeqs := fun x => x = df ∨ env.defeqs x }

@[simp] theorem addDefEq_out {env : VEnv'} :
    (env.addDefEq df).out = env.out.addDefEq df.toVDefEq := by
  simp [VEnv'.out, addDefEq, VEnv.addDefEq]

theorem IsDefEqStrong.hasType {env : VEnv'}
    (H : env.IsDefEqStrong U Γ e1 e2 A u) :
    env.IsDefEqStrong U Γ e1 e1 A u ∧ env.IsDefEqStrong U Γ e2 e2 A u :=
  ⟨H.trans H.symm, H.symm.trans H⟩

inductive Ctx.LiftN (n : Nat) : Nat → VCtx → VCtx → Prop where
  | zero (As : VCtx) (h : As.length = n := by rfl) : Ctx.LiftN n 0 Γ (As ++ Γ)
  | succ : Ctx.LiftN n k Γ Γ' → Ctx.LiftN n (k+1) ((A, u)::Γ) ((A.liftN n k, u) :: Γ')

theorem Lookup.weakN (W : Ctx.LiftN n k Γ Γ') (H : Lookup Γ i A u) :
    Lookup Γ' (liftVar n i k) (A.liftN n k) u := by
  induction W generalizing i A u with
  | zero As =>
    rw [liftVar_base, Nat.add_comm]
    subst n
    induction As with simp [*]
    | cons _ _ ih => rw [liftN_succ]; exact .succ ih
  | @succ k _ _ _ _ _ ih =>
    match H with
    | .zero => rw [liftVar_zero, ← lift_liftN']; exact .zero
    | .succ H => rw [liftVar_succ, ← lift_liftN']; exact (ih H).succ

theorem Lookup.out (H : Lookup Γ n ty u) : Lean4Lean.Lookup Γ.out n ty := by
  induction H with
  | zero => exact .zero
  | succ _ ih => exact .succ ih

theorem IsDefEqStrong.out
    (H : IsDefEqStrong env U Γ e1 e2 A u) : env.out.IsDefEq U Γ.out e1 e2 A := by
  induction H with
  | bvar h => exact .bvar h.out
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF (constants_out h1) h2 h3 h4 h5
  | appDF _ _ _ _ _ _ _ _ _ ih1 ih2 => exact .appDF ih1 ih2
  | lamDF _ _ _ _ _ _ _ ih1 _ _ ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ _ _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | defeqL _ _ _ _ ih => exact ih
  | beta _ _ _ _ _ _ _ _ _ _ ih1 ih2 => exact .beta ih1 ih2
  | eta _ _ _ _ _ _ _ _ _ _ ih => exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 => exact .extra (defeqs_out h1) h2 h3

nonrec theorem HasType.out (H : HasType env U Γ e A u) : env.out.HasType U Γ.out e A := H.out

nonrec theorem IsType.out (H : IsType env U Γ A u) : env.out.IsType U Γ.out A :=
  ⟨_, H.out⟩

nonrec theorem VConstant.WF.out {ci : VConstant} (H : ci.WF env) : ci.toVConstant.WF env.out :=
  H.out

theorem VDefEq.WF.out {ci : VDefEq} (H : ci.WF env) : ci.toVDefEq.WF env.out :=
  ⟨H.1.out, H.2.out⟩

inductive Ordered : VEnv' → Prop where
  | empty : Ordered ∅
  | const :
    Ordered env → (∀ ci, oci = some ci → ci.WF env) →
    env.addConst n oci = some env' → Ordered env'
  | defeq : Ordered env → df.WF env → Ordered (env.addDefEq df)

theorem Ordered.out (H : Ordered env) : env.out.Ordered := by
  induction H with
  | empty => simp; exact .empty
  | const h1 h2 h3 ih => exact .const ih (by simp; exact fun _ h => (h2 _ h).out) (addConst_out h3)
  | defeq h1 h2 ih => exact addDefEq_out ▸ .defeq ih h2.out

def OnTypes (env : VEnv') (P : Nat → VExpr → VExpr → VLevel → Prop) : Prop :=
  (∀ {n ci}, env.constants n = some (some ci) →
    P ci.uvars ci.type (.sort ci.level) (.succ ci.level)) ∧
  (∀ {df}, env.defeqs df → P df.uvars df.lhs df.type df.level ∧ P df.uvars df.rhs df.type df.level)

variable! (henv : Ordered env) in
theorem IsDefEqStrong.weakN (W : Ctx.LiftN n k Γ Γ') (H : env.IsDefEqStrong U Γ e1 e2 A u) :
    env.IsDefEqStrong U Γ' (e1.liftN n k) (e2.liftN n k) (A.liftN n k) u := by
  induction H generalizing k Γ' with
  | bvar h1 h2 _ ih3 => refine .bvar (h1.weakN W) h2 (ih3 W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 h6 h7 h8 h9 _ _ _ _ ih3 ih4 =>
    simp [(henv.out.closedC (constants_out h1)).instL.liftN_eq (Nat.zero_le _)] at ih3 ih4 ⊢
    exact .constDF h1 h2 h3 h4 h5 h6 h7 h8 h9 (ih3 W) (ih4 W)
  | appDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    refine liftN_inst_hi .. ▸ .appDF h1 h2 (ih1 W) (ih2 W.succ) (ih3 W) (ih4 W) ?_
    exact liftN_inst_hi .. ▸ liftN_inst_hi .. ▸ ih5 W
  | lamDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact .lamDF h1 h2 (ih1 W) (ih2 W.succ) (ih3 W.succ) (ih4 W.succ) (ih5 W.succ)
  | forallEDF h1 h2 _ _ _ ih1 ih2 ih3 => exact .forallEDF h1 h2 (ih1 W) (ih2 W.succ) (ih3 W.succ)
  | defeqDF h1 _ _ ih1 ih2 => exact .defeqDF h1 (ih1 W) (ih2 W)
  | defeqL h1 h2 h3 _ ih => exact .defeqL h1 h2 h3 (ih W)
  | beta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    refine liftN_inst_hi .. ▸ liftN_instN_hi .. ▸ .beta h1 h2
      (ih1 W) (ih2 W.succ) (ih3 W.succ) (ih4 W)
      (liftN_instN_hi .. ▸ ih5 W :)
      (liftN_instN_hi .. ▸ liftN_instN_hi .. ▸ ih6 W :)
  | @eta Γ a u B v e h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    have := IsDefEqStrong.eta h1 h2 (ih1 W) (ih2 W.succ) ?_ (ih4 W) ?_
    · simp [liftN]; rwa [← lift_liftN']
    · specialize ih3 W.succ.succ
      have := liftN'_comm B n 1 (k+1) 1 (Nat.le_add_left ..)
      rw [Nat.add_comm 1] at this; rwa [← this, ← lift_liftN'] at ih3
    · have ih5 : IsDefEqStrong _ _ _ _ _ (liftN n (lift (forallE ..)) _) _ := ih5 W.succ
      rwa [← lift_liftN', ← lift_liftN'] at ih5
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ _ ih4 ih5 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.out.closed.2 (defeqs_out h1)
    simp [
      hA1.instL.liftN_eq (Nat.zero_le _),
      hA2.instL.liftN_eq (Nat.zero_le _),
      hA3.instL.liftN_eq (Nat.zero_le _)] at ih4 ih5 ⊢
    exact IsDefEqStrong.extra h1 h2 h3 h4 h5 h6 h7 h8 (ih4 W) (ih5 W)

variable! {env env' : VEnv'} (henv : env ≤ env') in
theorem IsDefEqStrong.mono
    (H : env.IsDefEqStrong U Γ e1 e2 A u) : env'.IsDefEqStrong U Γ e1 e2 A u := by
  induction H with
  | bvar h1 h2 _ ih => exact .bvar h1 h2 ih
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 h6 h7 _ _ _ _ ih1 ih2 ih3 ih4 =>
    exact .constDF (henv.1 h1) h2 h3 h4 h5 h6 h7 ih1 ih2 ih3 ih4
  | appDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 => exact .appDF h1 h2 ih1 ih2 ih3 ih4 ih5
  | lamDF h1 h2  _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 => exact .lamDF h1 h2 ih1 ih2 ih3 ih4 ih5
  | forallEDF h1 h2 _ _ _ ih1 ih2 ih3 => exact .forallEDF h1 h2 ih1 ih2 ih3
  | defeqDF h1 _ _ ih1 ih2 => exact .defeqDF h1 ih1 ih2
  | defeqL h1 h2 h3 _ ih => exact .defeqL h1 h2 h3 ih
  | beta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 => exact .beta h1 h2 ih1 ih2 ih3 ih4 ih5 ih6
  | eta h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 => exact .eta h1 h2 ih1 ih2 ih3 ih4 ih5
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 h4 h5 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact .extra (henv.2 h1) h2 h3 h4 h5 ih1 ih2 ih3 ih4 ih5

variable! (henv : Ordered env) in
theorem IsDefEqStrong.weak0 (H : env.IsDefEqStrong U [] e1 e2 A u) :
    env.IsDefEqStrong U Γ e1 e2 A u := by
  have ⟨h1, h2, h3⟩ := H.out.closedN' henv.out.closed ⟨⟩
  simpa [h1.liftN_eq (Nat.zero_le _), h2.liftN_eq (Nat.zero_le _),
    h3.liftN_eq (Nat.zero_le _)] using H.weakN henv (.zero Γ rfl)

def VCtx.instL (ls : List VLevel) : VCtx → VCtx := List.map fun (A, u) => (A.instL ls, u.inst ls)

theorem Lookup.instL : Lookup Γ i A u → Lookup (Γ.instL ls) i (A.instL ls) (u.inst ls)
  | .zero => instL_liftN ▸ .zero
  | .succ h => instL_liftN ▸ .succ h.instL

variable! {env : VEnv'} {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U') in
theorem IsDefEqStrong.instL (H : env.IsDefEqStrong U Γ e1 e2 A u) :
    env.IsDefEqStrong U' (Γ.instL ls) (e1.instL ls) (e2.instL ls) (A.instL ls) (u.inst ls) := by
  induction H with
  | bvar h _ _ ih =>
    exact .bvar h.instL (.inst hls) ih
  | constDF h1 h2 h3 h4 h5 h6 _ _ _ _ _ ih1 ih2 ih3 ih4 =>
    simp [VExpr.instL, VExpr.instL_instL] at ih1 ih2 ih3 ih4 ⊢
    exact .constDF h1
      (by simp [VLevel.WF.inst hls]) (by simp [VLevel.WF.inst hls]) (by simp [h4])
      (by simpa using h5.imp fun _ _ => VLevel.inst_congr_l)
      (VLevel.inst_inst ▸ VLevel.inst_congr_l h6) (.inst hls) ih1 ih2 ih3 ih4
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF _ _ h3 =>
    exact .sortDF (VLevel.WF.inst hls) (VLevel.WF.inst hls) (VLevel.inst_congr_l h3)
  | appDF _ _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact instL_instN ▸ .appDF (.inst hls) (.inst hls)
      ih1 ih2 ih3 ih4 (instL_instN ▸ instL_instN ▸ ih5)
  | lamDF _ _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact .lamDF (.inst hls) (.inst hls) ih1 ih2 ih3 ih4 ih5
  | forallEDF _ _ _ _ _ ih1 ih2 ih3 =>
    exact .forallEDF (.inst hls) (.inst hls) ih1 ih2 ih3
  | defeqDF _ _ _ ih1 ih2 => exact .defeqDF (.inst hls) ih1 ih2
  | defeqL _ _ h3 _ ih => exact .defeqL (.inst hls) (.inst hls) (VLevel.inst_congr_l h3) ih
  | beta _ _ _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    simpa using .beta (.inst hls) (.inst hls) ih1 ih2 ih3 ih4
      (by simpa using ih5) (by simpa using ih6)
  | eta _ _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    simpa [VExpr.instL] using .eta (.inst hls) (.inst hls) ih1 ih2
      (by simpa [VCtx.instL] using ih3) ih4 (by simpa [VExpr.instL] using ih5)
  | proofIrrel _ _ _ ih1 ih2 ih3 =>
    exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 h4 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    simp [VExpr.instL, VExpr.instL_instL] at ih1 ih2 ih3 ih4 ih5 ⊢
    exact .extra h1 (by simp [VLevel.WF.inst hls]) (by simp [h3])
      (VLevel.inst_inst ▸ VLevel.inst_congr_l h4) (.inst hls) ih1 ih2 ih3 ih4 ih5

def VCtx.On (Γ : VCtx) (P : VCtx → VExpr → VLevel → Prop) : Prop :=
  match Γ with
  | [] => True
  | (A, u)::Γ => On Γ P ∧ P Γ A u

def CtxStrong (env : VEnv') (U) (Γ : VCtx) :=
  Γ.On fun Γ A u => env.IsDefEqStrong U Γ A A (.sort u) (.succ u)

theorem VCtx.On.lookup (h : On Γ P) (hL : Lookup Γ n A u)
    (hP : ∀ {Γ A B u}, P Γ A u → P (B::Γ) A.lift u) : P Γ A u :=
  match hL, h with
  | .zero, ⟨h1, h2⟩ => hP h2
  | .succ hL, ⟨h1, h2⟩ => hP (h1.lookup hL hP)

variable! (henv : Ordered env) in
nonrec theorem CtxStrong.lookup {Γ} (H : CtxStrong env U Γ) (h : Lookup Γ i A u) :
    env.IsDefEqStrong U Γ A A (.sort u) (.succ u) :=
  H.lookup h fun h => h.weakN henv (.zero [_])

theorem VCtx.On.mono (H : ∀ {Γ A u}, P Γ A u → Q Γ A u) : ∀ {Γ}, On Γ P → On Γ Q
  | [], h => h
  | _::_, ⟨h1, h2⟩ => ⟨mono H h1, H h2⟩

theorem CtxStrong.out : ∀ {Γ}, CtxStrong env U Γ → OnCtx Γ.out (env.out.IsType U)
  | [], h => h
  | _::_, ⟨h1, h2⟩ => ⟨out h1, _, h2.out⟩

variable (Γ₀ : VCtx) (e₀ A₀ : VExpr) (u₀ : VLevel) in
inductive Ctx.InstN' : Nat → VCtx → VCtx → Prop where
  | zero : Ctx.InstN' 0 ((A₀, u₀) :: Γ₀) Γ₀
  | succ : Ctx.InstN' k Γ Γ' → Ctx.InstN' (k+1) ((A, u)::Γ) ((A.inst e₀ k, u) :: Γ')

variable! (henv : Ordered env) (h₀ : env.IsDefEqStrong U Γ₀ e₀ e₀ A₀ u₀)
  (hΓ₀ : CtxStrong env U Γ₀) in
theorem IsDefEqStrong.instN (W : Ctx.InstN' Γ₀ e₀ A₀ u₀ k Γ₁ Γ)
    (H : env.IsDefEqStrong U Γ₁ e1 e2 A u) (hΓ : CtxStrong env U Γ) :
    env.IsDefEqStrong U Γ (e1.inst e₀ k) (e2.inst e₀ k) (A.inst e₀ k) u := by
  induction H generalizing Γ k with
  | @bvar _ i ty _ h _ h2 ih =>
    dsimp [inst]; clear h2 ih
    induction W generalizing i ty with
    | zero =>
      cases h with simp [inst_lift]
      | zero => exact h₀
      | succ h =>
        have hty := hΓ₀.lookup henv h
        exact .bvar h (hty.out.sort_r henv.out hΓ₀.out) hty
    | succ _ ih =>
      cases h with (simp; rw [Nat.add_comm, ← liftN_instN_lo (hj := Nat.zero_le _)])
      | zero =>
        have hty := hΓ.lookup henv .zero
        exact .bvar .zero (hty.out.sort_r henv.out hΓ.out) hty
      | succ h => exact (ih h hΓ.1).weakN henv (.zero [_])
  | symm _ ih => exact .symm (ih W hΓ)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W hΓ) (ih2 W hΓ)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 h6 h7 h8 h9 _ _ _ _ ih3 ih4 =>
    simp [(henv.out.closedC (constants_out h1)).instL.instN_eq (Nat.zero_le _)] at ih3 ih4 ⊢
    exact .constDF h1 h2 h3 h4 h5 h6 h7 h8 h9 (ih3 W hΓ) (ih4 W hΓ)
  | appDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact inst0_inst_hi .. ▸ .appDF h1 h2
      (ih1 W hΓ) (ih2 W.succ ⟨hΓ, ih1 W hΓ⟩)
      (ih3 W hΓ) (ih4 W hΓ) (inst0_inst_hi .. ▸ inst0_inst_hi .. ▸ ih5 W hΓ)
  | lamDF h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    exact
      have hΓ' := ⟨hΓ, (ih1 W hΓ).hasType.1⟩
      have hΓ'' := ⟨hΓ, (ih1 W hΓ).hasType.2⟩
      .lamDF h1 h2 (ih1 W hΓ) (ih2 W.succ hΓ') (ih3 W.succ hΓ'') (ih4 W.succ hΓ') (ih5 W.succ hΓ'')
  | forallEDF h1 h2 _ _ _ ih1 ih2 ih3 =>
    exact .forallEDF h1 h2 (ih1 W hΓ)
      (ih2 W.succ ⟨hΓ, (ih1 W hΓ).hasType.1⟩) (ih3 W.succ ⟨hΓ, (ih1 W hΓ).hasType.2⟩)
  | defeqDF h1 _ _ ih1 ih2 => exact .defeqDF h1 (ih1 W hΓ) (ih2 W hΓ)
  | defeqL h1 h2 h3 _ ih => exact .defeqL h1 h2 h3 (ih W hΓ)
  | beta h1 h2 _ _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 ih6 =>
    rw [inst0_inst_hi, inst0_inst_hi]; exact
      have hΓ' := ⟨hΓ, ih1 W hΓ⟩
      .beta h1 h2
        (ih1 W hΓ) (ih2 W.succ hΓ') (ih3 W.succ hΓ') (ih4 W hΓ)
        (inst0_inst_hi .. ▸ ih5 W hΓ) (inst0_inst_hi .. ▸ inst0_inst_hi .. ▸ ih6 W hΓ)
  | eta h1 h2 _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    have :=
      have hΓ' := ⟨hΓ, (ih1 W hΓ).hasType.1⟩
      IsDefEqStrong.eta h1 h2 (ih1 W hΓ) (ih2 W.succ hΓ')
        (by
          have := ih3 W.succ.succ ⟨hΓ', by
            rw [← lift_instN_lo]; exact (ih1 W hΓ).hasType.1.weakN henv (.zero [_])⟩
          rwa [lift_instN_lo, liftN_instN_lo (hj := Nat.le_add_left ..), Nat.add_comm 1])
        (ih4 W hΓ)
        (by
          have := ih5 W.succ hΓ'
          simp only [inst, ← lift_instN_lo] at this
          rwa [liftN_instN_lo (hj := Nat.le_add_left ..), Nat.add_comm 1])
    rw [lift, liftN_instN_lo (hj := Nat.zero_le _), Nat.add_comm] at this
    simpa [inst]
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W hΓ) (ih2 W hΓ) (ih3 W hΓ)
  | extra h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ _ ih4 ih5 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.out.closed.2 (defeqs_out h1)
    simp [
      hA1.instL.instN_eq (Nat.zero_le _),
      hA2.instL.instN_eq (Nat.zero_le _),
      hA3.instL.instN_eq (Nat.zero_le _)] at ih4 ih5 ⊢
    exact .extra h1 h2 h3 h4 h5 h6 h7 h8 (ih4 W hΓ) (ih5 W hΓ)

theorem IsDefEqStrong.defeqDF_l (henv : Ordered env) (hΓ : CtxStrong env U Γ)
    (h1 : env.IsDefEqStrong U Γ A A' (.sort u) (.succ u))
    (h2 : env.IsDefEqStrong U ((A, u)::Γ) e1 e2 B v) :
    env.IsDefEqStrong U ((A', u)::Γ) e1 e2 B v := by
  simpa [instN_bvar0] using
    have hu := h1.out.sort_r henv.out hΓ.out
    have hΓ' := ⟨hΓ, h1.hasType.2⟩
    h1.weakN henv (.zero [(A', u)])
      |>.symm.defeqDF hu (.bvar .zero hu (h1.hasType.2.weakN henv (.zero [(A', u)])))
      |>.instN henv hΓ' .zero (h2.weakN henv (.succ (.zero [(A', u)]))) hΓ'

def EnvStrong (env : VEnv') (U : Nat) (e A : VExpr) (u : VLevel) : Prop :=
  env.IsDefEqStrong U [] e e A u ∧
  env.IsDefEqStrong U [] A A (.sort u) (.succ u) ∧
  ∀ A B, e = A.forallE B →
    ∃ u, env.IsDefEqStrong U [] A A (.sort u) (.succ u) ∧
    ∃ v, env.IsDefEqStrong U [(A, u)] B B (.sort v) (.succ v)

variable! (henv : Ordered env) (envIH : env.OnTypes (EnvStrong env)) in
theorem IsDefEqStrong.forallE_inv' (hΓ : CtxStrong env U Γ)
    (H : env.IsDefEqStrong U Γ e1 e2 V v) (eq : e1 = A.forallE B ∨ e2 = A.forallE B) :
    ∃ u, env.IsDefEqStrong U Γ A A (.sort u) (.succ u) ∧
    ∃ v, env.IsDefEqStrong U ((A, u)::Γ) B B (.sort v) (.succ v) := by
  induction H generalizing A B with
  | symm _ ih => exact ih hΓ eq.symm
  | trans _ _ ih1 ih2
  | proofIrrel _ _ _ _ ih1 ih2 =>
    obtain eq | eq := eq
    · exact ih1 hΓ (.inl eq)
    · exact ih2 hΓ (.inr eq)
  | forallEDF _ _ h1 h2 =>
    obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq
    · exact ⟨_, h1.hasType.1, _, h2.hasType.1⟩
    · exact ⟨_, h1.hasType.2, _, h1.defeqDF_l henv hΓ h2.hasType.2⟩
  | defeqDF _ _ _ _ ih | defeqL _ _ _ _ ih => exact ih hΓ eq
  | @beta _ _ _ _ _ e _ _ _ h1 _ _ h4 _ _ _ _ ih3 ih4 =>
    obtain ⟨⟨⟩⟩ | eq := eq
    cases e with
    | bvar i =>
      cases i with simp [inst] at eq
      | zero => exact ih4 hΓ (.inl eq)
    | forallE A B =>
      cases eq
      let ⟨_, A1, _, A2⟩ := ih3 ⟨hΓ, h1⟩ (.inl rfl)
      refine ⟨_, h4.instN henv hΓ .zero A1 hΓ, _, h4.instN henv hΓ (.succ .zero) A2 ?_⟩
      exact ⟨hΓ, h4.instN henv hΓ .zero A1 hΓ⟩
    | _ => cases eq
  | eta _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨⟨⟩⟩ | eq := eq
    exact ih hΓ (.inl eq)
  | @extra df ls _ Γ h1 h2 =>
    suffices ∀ e, VExpr.instL ls e = VExpr.forallE A B →
        EnvStrong env df.uvars e df.type df.level →
        ∃ u, IsDefEqStrong env U Γ A A (.sort u) (.succ u) ∧
        ∃ v, IsDefEqStrong env U ((A, u) :: Γ) B B (.sort v) (.succ v) by
      have ⟨A1, A2⟩ := envIH.2 h1
      cases eq <;> exact this _ ‹_› ‹_›
    intro e eq IH
    cases e <;> cases eq; rename_i A B
    let ⟨_, A1, v, A2⟩ := IH.2.2 _ _ rfl
    refine ⟨_, (A1.instL h2).weak0 henv, v.inst ls, ?_⟩
    have := (A2.instL h2).weakN henv (.succ (.zero Γ))
    have C1 := (A1.instL h2).out.closedN henv.out ⟨⟩
    have C2 := (A2.instL h2).out.closedN henv.out ⟨⟨⟩, C1⟩
    rw [C1.liftN_eq (Nat.zero_le _), C2.liftN_eq (by exact Nat.le_refl _)] at this
    simpa [liftN]
  | _ => nomatch eq

variable! (henv : Ordered env) in
theorem IsDefEqStrong.isType' (hΓ : CtxStrong env U Γ) (H : env.IsDefEqStrong U Γ e1 e2 A u) :
    env.IsDefEqStrong U Γ A A (.sort u) (.succ u) := by
  induction H with
  | bvar h => exact hΓ.lookup henv h
  | symm _ ih => exact ih hΓ
  | trans _ _ ih1 => exact ih1 hΓ
  | sortDF h1 => exact .sortDF h1 h1 rfl
  | constDF _ _ _ _ _ _ _ _ _ h => exact h
  | appDF _ _ _ _ _ _ h4 _ _ _ ih3 => exact h4.hasType.1
  | lamDF h1 h2 h3 h4 => exact .forallEDF h1 h2 h3.hasType.1 h4 h4
  | forallEDF h1 h2 => exact .sortDF ⟨h1, h2⟩ ⟨h1, h2⟩ rfl
  | defeqDF _ h2 => exact h2.hasType.2
  | defeqL h1 h2 h3 _ ih =>
    exact (defeqDF (by exact h1) (sortDF h1 h2 h3) (ih hΓ))
      |>.defeqL (by exact h1) (by exact h2) (VLevel.succ_congr h3)
  | beta _ _ _ h4 _ h6 => exact h6.hasType.1.instN henv hΓ .zero h4 hΓ
  | eta _ _ _ _ _ _ _ _ _ _ ih => exact ih hΓ
  | proofIrrel h1 => exact h1
  | extra _ _ _ _ _ h => exact h.weak0 henv

theorem IsDefEqStrong.sort_invL {env : VEnv'}
    (H : env.IsDefEqStrong U Γ e1 e2 A u) :
    (.sort v = e1 → u ≈ v.succ.succ) ∧
    (.sort v = e2 → u ≈ v.succ.succ) ∧
    (.sort v = A → u ≈ v.succ) := by
  induction H generalizing v with
  | bvar _ _ _ ih
  | constDF _ _ _ _ _ _ _ _ _ _ _ _ _ ih
  | appDF _ _ _ _ _ _ _ _ _ _ _ ih =>
    exact ⟨nofun, nofun, fun h => VLevel.succ_congr_iff.1 <| ih.1 h⟩
  | symm _ ih => exact ⟨ih.2.1, ih.1, ih.2.2⟩
  | trans _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2.1, ih1.2.2⟩
  | sortDF _ _ h =>
    refine ⟨by rintro ⟨⟩; rfl, ?_, by rintro ⟨⟩; rfl⟩
    rintro ⟨⟩; exact VLevel.succ_congr (VLevel.succ_congr h)
  | lamDF => exact ⟨nofun, nofun, nofun⟩
  | forallEDF => exact ⟨nofun, nofun, by rintro ⟨⟩; rfl⟩
  | defeqDF _ _ _ ih1 ih2 => exact ⟨ih2.1, ih2.2.1, fun h => VLevel.succ_congr_iff.1 <| ih1.2.1 h⟩
  | defeqL _ _ h1 _ ih =>
    exact ⟨h1.symm.trans ∘ ih.1, h1.symm.trans ∘ ih.2.1, h1.symm.trans ∘ ih.2.2⟩
  | beta _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ⟨nofun, ih.1, ih.2.2⟩
  | eta _ _ _ _ _ _ _ _ _ _ ih => exact ⟨nofun, ih.1, ih.2.2⟩
  | proofIrrel _ _ _ _ ih1 ih2
  | extra _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 => exact ⟨ih1.1, ih2.1, ih1.2.2⟩

variable {env : VEnv'} in
-- variable! (henv : Ordered env) (hΓ : CtxStrong env U Γ) in
theorem IsDefEqStrong.uniqL'
    (H1 : env.IsDefEqStrong U Γ e1 e2 A u)
    (H2 : env.IsDefEqStrong U Γ e1' e2' A' v)
    : (e1 = e1' → u ≈ v) ∧ (e1 = e2' → u ≈ v) ∧
      (e2 = e1' → u ≈ v) ∧ (e2 = e2' → u ≈ v) := by
  induction H1 generalizing e1' e2' A' v with
  | bvar H1 h1 h2 ih =>
    clear h1 h2 ih
    induction H2 with try simp
    | @bvar _ _ A' u' H2 h1 h2 ih =>
      rintro rfl; clear h1 h2 ih
      induction H1 generalizing A' u' with cases H2
      | zero => rfl
      | succ h ih => exact ih ‹_›
    | symm _ ih => let ⟨h1, h2, h3, h4⟩ := ih H1; exact ⟨h2, h1, h4, h3⟩
    | trans _ _ ih1 ih2
    | proofIrrel _ _ _ _ ih1 ih2
    | extra _ _ _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 =>
      let ⟨h1, _, h3, _⟩ := ih1 H1; let ⟨_, h2, _, h4⟩ := ih2 H1
      exact ⟨h1, h2, h3, h4⟩
    | defeqDF _ _ _ _ ih => exact ih H1
    | defeqL _ _ h _ ih => exact propext (VLevel.equiv_congr_right h) ▸ ih H1
    | beta _ _ _ _ _ _ _ _ _ _ _ _ _ ih
    | eta _ _ _ _ _ _ _ _ _ _ ih => exact (ih H1).1
  | @constDF c ci ls _ _ _ h1 _ _ _ h2 hu _ d1 d2 d3 d4 ih1 ih2 ih3 ih4 =>
    clear d1 d2 d3 d4 ih1 ih2 ih3 ih4
    induction H2 with try simp
    | @constDF c' _ ls' _ _ _ h1' _ _ _ h2' hu' =>
      by_cases h : c = c' <;> simp [h]; subst h
      cases h1.symm.trans h1'
      rw [VLevel.equiv_congr_left hu, VLevel.equiv_congr_right hu']
      have eq := VLevel.inst_congr (l := ci.level) rfl h2
      have eq' := VLevel.inst_congr (l := ci.level) rfl h2'
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;>
        [rfl; exact eq'.symm; exact eq; exact eq.trans eq'.symm]
    | symm _ ih => let ⟨h1, h2, h3, h4⟩ := ih; exact ⟨h2, h1, h4, h3⟩
    | trans _ _ ih1 ih2
    | proofIrrel _ _ _ _ ih1 ih2
    | extra _ _ _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 =>
      let ⟨h1, _, h3, _⟩ := ih1; let ⟨_, h2, _, h4⟩ := ih2
      exact ⟨h1, h2, h3, h4⟩
    | defeqDF _ _ _ _ ih => exact ih
    | defeqL _ _ h _ ih => exact propext (VLevel.equiv_congr_right h) ▸ ih
    | beta _ _ _ _ _ _ _ _ _ _ _ _ _ ih
    | eta _ _ _ _ _ _ _ _ _ _ ih => exact ⟨ih.1, ih.2.2.1⟩
  | @appDF _ _ _ _ _ f₁ f₂ a₁ a₂ _ _ d1 d2 d3 d4 d5 ih1 ih2 ih3 ih4 ih5 =>
    clear d1 d2 d3 d4 d5 ih1 ih2 ih5
    induction H2 with try simp
    | @appDF _ _ _ _ _ f₁' f₂' a₁' a₂' _ _ _ _ _ ih3' ih4' =>
      refine ⟨?_, sorry⟩
      rintro rfl rfl
      sorry -- looks like it needs unique typing :(
    | _ => sorry
  | _ => sorry
