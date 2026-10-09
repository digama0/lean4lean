import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Pattern

namespace Lean4Lean
open Lean4Lean

inductive Classification where
  | ctor (arity : Nat)
  | etaCtor (params args : Nat)
  | symb (arity : Nat)
  | indTy (arity : Nat)

def Classification.arity : Classification → Nat
  | .ctor k | .symb k | .indTy k => k
  | .etaCtor p a => p + a

def Pattern.WF (cl : Name → Option Classification) :
    Pattern → (top : Bool := true) → (extra : Nat := 0) → Prop
  | .const c, top, n => cl c = some (if top then .symb n else .ctor n)
  -- added for the elim/proj constructors of this branch
  | .elim b o, top, n => cl (.num b o) = some (if top then .symb n else .ctor n)
  | .var p, top, n => WF cl p top (n + 1)
  | .app p p', top, n => WF cl p top (n + 1) ∧ WF cl p' false

class Params where
  env : VEnv
  henv : env.Ordered
  univs : Nat
  Pat : (p : Pattern) → p.RHS × p.Check → Prop
  classify : Name → Option Classification
  pat_simple : Pat p r → ∃ sp : SimplePattern, p = sp.toPattern
  pat_wf : Pat p r → p.WF classify
  pat_uniq : Pat p₁ r → Pat p₂ r' → Subpattern p₃ p₁ → p₂.inter p₃ = some p₄ →
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r'
  -- pat_wf : Pat p r → p.Matches e m1 m2 → HasType env univs Γ e A →
  --   r.2.OK (IsDefEqU env univs Γ) m1 m2 → IsDefEqU env univs Γ e (r.1.apply m1 m2)
  -- pat_app_l : Pat p r → Subpattern (.app p₁ p₂) p → ¬Subpattern (.app p₃ p₄) p₁
  -- pat_app_l_uniq : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
  --   Subpattern (.app p₁' p₂') p' → Subpattern (.var p₃) p₁ → p₁'.inter p₃ = none
  -- pat_app_uniq : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
  --   Subpattern (.app p₁' p₂') p' → Subpattern p₃ p₁ → Subpattern p₃' p₂' → p₃.inter p₃' = none
  -- pat_app_r_arity : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
  --   Subpattern (.app p₁' p₂') p' → Arity (.const c) n p₂ → Arity (.const c) n' p₂' → n = n'
  -- extra_pat : env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
  --   ∃ p r m1 m2, Pat p r ∧ p.Matches (df.lhs.instL ls) m1 m2 ∧ r.2.OK (IsDefEqU env univs Γ) m1 m2 ∧
  --   df.rhs.instL ls = r.1.apply m1 m2
open Params
variable [Params]

/-- A semantically quotiented version of `VLevel`. This avoids the need for some congruences. -/
def SLevel := { f : List Nat → Nat // ∃ l : VLevel, l.WF univs ∧ l.eval = f }

namespace SLevel

def zero : SLevel := ⟨_, .zero, ⟨⟩, rfl⟩

def mk (l : VLevel) : SLevel := if h : l.WF univs then ⟨_, l, h, rfl⟩ else .zero

def succ (l : SLevel) : SLevel :=
  ⟨fun v => l.1 v + 1, let ⟨u, h1, h2⟩ := l.2; ⟨u.succ, h1, h2 ▸ rfl⟩⟩

def max (l₁ l₂ : SLevel) : SLevel :=
  ⟨fun v => (l₁.1 v).max (l₂.1 v),
    let ⟨u, h1, h2⟩ := l₁.2; let ⟨v, h3, h4⟩ := l₂.2; ⟨u.max v, ⟨h1, h3⟩, h2 ▸ h4 ▸ rfl⟩⟩

def imax (l₁ l₂ : SLevel) : SLevel :=
  ⟨fun v => Lean.Nat.imax (l₁.1 v) (l₂.1 v),
    let ⟨u, h1, h2⟩ := l₁.2; let ⟨v, h3, h4⟩ := l₂.2; ⟨u.imax v, ⟨h1, h3⟩, h2 ▸ h4 ▸ rfl⟩⟩

def inst (ls : List SLevel) (l : SLevel) : SLevel := by
  refine ⟨fun v => l.1 (ls.map (·.1 v)), ?_⟩
  simp [funext_iff]
  have ⟨ls', h3⟩ :
      ∃ ls' : List VLevel, ls'.Forall₂ (fun l' l => l'.WF univs ∧ l'.eval = l.1) ls := by
    induction ls with
    | nil => exact ⟨_, .nil⟩
    | cons a l ih =>
      let ⟨l', h1, h2⟩ := a.2; let ⟨ls', h3⟩ := ih
      exact ⟨l'::ls', .cons ⟨h1, h2⟩ h3⟩
  have ⟨l', h1, h2⟩ := l.2
  refine ⟨l'.inst ls', VLevel.WF.inst fun _ h => ?_, fun v => ?_⟩
  · let ⟨_, h⟩ := h3.forall_exists_l _ h; exact h.2.1
  · simp [VLevel.eval_inst, ← h2]; congr 1
    rw [← List.forall₂_eq, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact h3.imp fun _ _ h => congrFun h.2 _

end SLevel

inductive SExpr where
  | bvar (i : Nat)
  | sort (u : SLevel)
  | const (c : Name) (ls : List SLevel)
  | app (f a : SExpr)
  | lam (A e : SExpr)
  | forallE (A B : SExpr)

instance : Inhabited SExpr := ⟨.sort .zero⟩

namespace SExpr

@[simp] def lift' : SExpr → Lift → SExpr
  | .bvar i, k => .bvar (k.liftVar i)
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app fn arg, k => .app (fn.lift' k) (arg.lift' k)
  | .lam ty body, k => .lam (ty.lift' k) (body.lift' k.cons)
  | .forallE ty body, k => .forallE (ty.lift' k) (body.lift' k.cons)

abbrev lift e := lift' e (.skip .refl)

theorem lift'_comp {e : SExpr} : e.lift' (.comp l₁ l₂) = (e.lift' l₁).lift' l₂ := Eq.symm <| by
  induction e generalizing l₁ l₂ <;> simp [Lift.liftVar_comp, *]

theorem lift'_depth_zero {e : SExpr} (H : l.depth = 0) : e.lift' l = e := by
  induction e generalizing l <;> simp_all [Lift.liftVar_depth_zero]

@[simp] theorem lift'_refl {e : SExpr} : e.lift' .refl = e := lift'_depth_zero rfl

def ClosedN : SExpr → (k :_:= 0) → Prop
  | .bvar i, k => i < k
  | .sort .., _ | .const .., _ => True
  | .app fn arg, k => fn.ClosedN k ∧ arg.ClosedN k
  | .lam ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)
  | .forallE ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)

theorem ClosedN.mono (h : k ≤ k') (self : ClosedN e k) : ClosedN e k' := by
  induction e generalizing k k' with (simp [ClosedN] at self ⊢; try simp [self, *])
  | bvar i => exact Nat.lt_of_lt_of_le self h
  | app _ _ ih1 ih2 => exact ⟨ih1 h self.1, ih2 h self.2⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    exact ⟨ih1 h self.1, ih2 (Nat.succ_le_succ h) self.2⟩

theorem ClosedN.lift'_eq (self : ClosedN e k) (h : ρ.Fixes k) : lift' e ρ = e := by
  induction e generalizing k ρ with (simp [ClosedN] at self; simp [*])
  | bvar i => exact h.liftVar_eq self
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩

theorem ClosedN.lift_eq (self : ClosedN e) : lift e = e := self.lift'_eq ⟨⟩

variable (ls : List SLevel) in
def instL : SExpr → SExpr
  | .bvar i => .bvar i
  | .sort u => .sort (u.inst ls)
  | .const c us => .const c (us.map (SLevel.inst ls))
  | .app fn arg => .app fn.instL arg.instL
  | .lam ty body => .lam ty.instL body.instL
  | .forallE ty body => .forallE ty.instL body.instL

theorem ClosedN.instL : ∀ {e}, ClosedN e k → ClosedN (e.instL ls) k
  | .bvar .., h | .sort .., h | .const .., h => h
  | .app .., h | .lam .., h | .forallE .., h => ⟨h.1.instL, h.2.instL⟩

def mk : VExpr → SExpr
  | .bvar i => .bvar i
  | .sort u => .sort (.mk u)
  | .const c us => .const c (us.map .mk)
  -- added for the elim/proj constructors of this branch
  | .elim b o us => .const (.num b o) (us.map .mk)
  | .app fn arg => .app (.mk fn) (.mk arg)
  -- added for the elim/proj constructors of this branch
  | .proj n i e => .app (.const (.num n i) []) (.mk e)
  | .lam ty body => .lam (.mk ty) (.mk body)
  | .forallE ty body => .forallE (.mk ty) (.mk body)

theorem _root_.Lean4Lean.VExpr.ClosedN.mkS : ∀ {e : VExpr}, e.ClosedN k → ClosedN (.mk e) k
  | .bvar .., h | .sort .., h | .const .., h => h
  | .app .., h | .lam .., h | .forallE .., h => ⟨h.1.mkS, h.2.mkS⟩
  -- added for the elim/proj constructors of this branch
  | .elim .., h => h
  -- added for the elim/proj constructors of this branch
  | .proj _ _ e, h => ⟨trivial, VExpr.ClosedN.mkS (e := e) h⟩

@[reducible] def Subst := Nat → SExpr

def Subst.Depth (σ : Subst) (n n' : Nat) := ∀ i, σ (i + n') = .bvar (i + n)

def Subst.Fixes (σ : Subst) (n : Nat) := ∀ i < n, σ i = .bvar i

theorem Subst.Fixes.zero : Fixes σ 0 := nofun

theorem Subst.Depth.add {σ : Subst} (H : σ.Depth n n') : σ.Depth (n + k) (n' + k) :=
  fun i => cast (by congr 2 <;> omega) <| H (k + i)

def Subst.lift (σ : Subst) : Subst
  | 0 => .bvar 0
  | i+1 => (σ i).lift

theorem Subst.Depth.lift {σ : Subst} (H : σ.Depth n n') : σ.lift.Depth (n + 1) (n' + 1) :=
  fun i => by simp [Subst.lift, H i]; rfl

theorem Subst.Fixes.lift {σ : Subst} (H : σ.Fixes n) : σ.lift.Fixes (n + 1) := fun
  | 0, _ => rfl
  | n+1, h => by simp [Subst.lift, H _ (Nat.lt_of_succ_lt_succ h)]

def Subst.id : Subst := .bvar
def Subst.head (σ : Subst) : SExpr := σ 0
def Subst.tail (σ : Subst) : Subst := fun n => σ (n+1)

theorem Subst.Depth.id : Subst.id.Depth 0 0 := fun _ => rfl
theorem Subst.Depth.tail {σ : Subst} (H : σ.Depth n (n' + 1)) : σ.tail.Depth n n' := H

def Subst.cons (σ : Subst) (e : SExpr) : Subst
  | 0 => e
  | i+1 => σ i

theorem Subst.Depth.cons {σ : Subst} (H : σ.Depth n n') : (σ.cons e).Depth n (n' + 1) := H

abbrev Subst.one (e : SExpr) : Subst := .cons .id e

theorem Subst.Depth.one : (Subst.one e).Depth 0 1 := .id

def Subst.trunc (σ : Subst) (n n' : Nat) : Subst :=
  fun i => if n' ≤ i then .bvar (i - n' + n) else σ i

theorem Subst.Depth.trunc {σ : Subst} : (σ.trunc n n').Depth n n' := by
  intro i; simp [Subst.trunc]

def _root_.Lean4Lean.Lift.invS : Lift → Subst
  | .refl => .id
  | .skip ρ => ρ.invS.cons default
  | .cons ρ => ρ.invS.lift

theorem Subst.Depth.invS : ∀ (ρ : Lift), ρ.invS.Depth ρ.dom ρ.size
  | .refl => .id
  | .skip l => (invS l).cons
  | .cons l => (invS l).lift

@[simp] theorem Subst.head_cons : (cons σ e).head = e := rfl
@[simp] theorem Subst.tail_cons : (cons σ e).tail = σ := rfl

def Subst.lift_r (σ : Subst) (ρ : Lift) : Subst := fun x => (σ x).lift' ρ
def Subst.lift_l (ρ : Lift) (σ : Subst) : Subst := fun x => σ (ρ.liftVar x)

theorem Subst.tail_eq_lift_l {σ : Subst} : σ.tail = σ.lift_l Lift.refl.skip := rfl

theorem Subst.lift_l_lift {σ : Subst} {ρ} : (σ.lift_l ρ).lift = σ.lift.lift_l ρ.cons := by
  funext i; cases i <;> simp! [lift_l]

theorem Subst.lift_r_lift {σ : Subst} {ρ} : (σ.lift_r ρ).lift = σ.lift.lift_r ρ.cons := by
  funext i; cases i <;> simp! [lift_r, ← lift'_comp]

theorem lift_l_inv {ρ : Lift} : .lift_l ρ ρ.invS = Subst.id := by
  funext i; simp [Subst.lift_l, Subst.id]
  induction ρ generalizing i with
  | refl => rfl
  | skip ρ ih => simp [Lift.invS, Subst.cons, ih]
  | cons ρ ih => cases i <;> simp [Lift.invS, Subst.lift, ih]

@[simp] theorem instL_lift' : (lift' e ρ).instL ls = lift' (e.instL ls) ρ := by
  cases e <;> simp [lift', instL, instL_lift']

def _root_.Lean4Lean.Lift.toSubst (ρ : Lift) : Subst := .lift_l ρ .id

theorem _root_.Lean4Lean.Lift.toSubst_apply (ρ : Lift) (i) : ρ.toSubst i = bvar (ρ.liftVar i) := rfl

theorem Subst.Depth.toSubst (ρ : Lift) : ρ.toSubst.Depth ρ.size ρ.dom := by
  intro i; simp [Lift.toSubst_apply]
  induction ρ <;> simp! [*] <;> omega

def subst : SExpr → Subst → SExpr
  | .bvar i, σ => σ i
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app fn arg, σ => .app (fn.subst σ) (arg.subst σ)
  | .lam ty body, σ => .lam (ty.subst σ) (body.subst σ.lift)
  | .forallE ty body, σ => .forallE (ty.subst σ) (body.subst σ.lift)

@[simp] theorem id_lift : Subst.id.lift = Subst.id := by funext i; cases i <;> rfl

@[simp] theorem subst_id {e : SExpr} : e.subst .id = e := by
  induction e <;> simp! [*]; rfl

theorem subst_lift' {e : SExpr} : (e.lift' ρ).subst σ = subst e (.lift_l ρ σ) := by
  induction e generalizing ρ σ <;> simp! [*, Subst.lift_l_lift]; rfl

theorem lift'_subst {e : SExpr} : (e.subst σ).lift' ρ = subst e (.lift_r σ ρ) := by
  induction e generalizing ρ σ <;> simp! [*, Subst.lift_r, Subst.lift_r_lift]

theorem lift'_inj {e e' : SExpr} {ρ : Lift} : e.lift' ρ = e'.lift' ρ ↔ e = e' :=
  ⟨(by simpa [subst_lift', lift_l_inv] using congrArg (·.subst ρ.invS) ·), (· ▸ rfl)⟩

theorem subst_toSubst {e : SExpr} : subst e ρ.toSubst = lift' e ρ := by
  simp [Lift.toSubst, ← subst_lift']

theorem subst_lift'_inv {e : SExpr} {ρ : Lift} : (e.lift' ρ).subst ρ.invS = e := by
  rw [subst_lift', lift_l_inv, subst_id]

nonrec def Subst.instL (ls : List SLevel) (σ : Subst) : Subst := instL ls ∘ σ

theorem Subst.instL_lift {σ : Subst} : (σ.instL ls).lift = σ.lift.instL ls := by
  funext i; obtain _|i := i <;> simp [Subst.instL, lift, SExpr.instL]

@[simp] theorem instL_subst : (subst e σ).instL ls = subst (e.instL ls) (σ.instL ls) := by
  cases e <;> simp [subst, instL, instL_subst, Subst.instL_lift] <;> simp [Subst.instL]

def Subst.comp (σ σ' : Subst) : Subst := fun x => (σ x).subst σ'

theorem Subst.comp_lift {σ σ' : Subst} : (σ.comp σ').lift = σ.lift.comp σ'.lift := by
  funext i; cases i <;> simp! [comp, SExpr.lift]
  rw [SExpr.lift, SExpr.lift, lift'_subst, subst_lift']; rfl

theorem subst_subst {e : SExpr} : (e.subst σ).subst σ' = subst e (.comp σ σ') := by
  induction e generalizing σ σ' <;> simp! [*, Subst.comp, Subst.comp_lift]

theorem lift_subst {e : SExpr} : e.lift.subst σ = e.subst σ.tail := by
  rw [lift, subst_lift', ← Subst.tail_eq_lift_l]

theorem lift_subst_cons {e : SExpr} : e.lift.subst (σ.cons t) = e.subst σ := by
  rw [lift_subst, Subst.tail_cons]

theorem Subst.lift_l_eq : Subst.lift_l ρ σ = Subst.comp ρ.toSubst σ := by
  funext; simp [lift_l, comp, Lift.toSubst_apply, SExpr.subst]

theorem Subst.lift_r_eq : Subst.lift_r σ ρ = Subst.comp σ ρ.toSubst := by
  funext i; simp [lift_r, comp, subst_toSubst]

theorem Subst.Depth.comp {σ σ' : Subst}
    (H : σ.Depth n₁ n₂) (H2 : σ'.Depth n₂ n₃) : (σ'.comp σ).Depth n₁ n₃ := by
  intro i; simp [Subst.comp, subst, H2 i, H i]

theorem Subst.Depth.lift_l {σ : Subst}
    (H : σ.Depth n ρ.size) : (Subst.lift_l ρ σ).Depth n ρ.dom := by
  rw [lift_l_eq]; exact .comp H (.toSubst _)

theorem Subst.Depth.lift_r {σ : Subst}
    (H : σ.Depth ρ.dom n) : (Subst.lift_r σ ρ).Depth ρ.size n := by
  rw [lift_r_eq]; exact .comp (.toSubst _) H

theorem ClosedN.subst_eq {e : SExpr} (self : ClosedN e k) (h : σ.Fixes k) : e.subst σ = e := by
  induction e generalizing k σ with (simp [ClosedN] at self; simp [*, SExpr.subst])
  | bvar i => exact h _ self
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h.lift⟩

def inst (e a : SExpr) : SExpr := e.subst (.one a)

def Skips (e : SExpr) (ρ : Lift) : Prop := lift' (e.subst ρ.invS) ρ = e

theorem Skips.lift (e : SExpr) (ρ : Lift) : Skips (e.lift' ρ) ρ := by
  rw [Skips, subst_lift'_inv]

def Skips' : SExpr → (ρ : Lift) → Prop
  | .bvar i, ρ => ∃ j, ρ.liftVar j = i
  | .sort .., _ | .const .., _ => True
  | .app fn arg, ρ => fn.Skips' ρ ∧ arg.Skips' ρ
  | .lam ty body, ρ => ty.Skips' ρ ∧ body.Skips' ρ.cons
  | .forallE ty body, ρ => ty.Skips' ρ ∧ body.Skips' ρ.cons

theorem skips_iff {e : SExpr} {ρ : Lift} : Skips e ρ ↔ Skips' e ρ := by
  simp [Skips]; induction e generalizing ρ with simp!
  | app _ _ ih1 ih2 => exact and_congr ih1 ih2
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact and_congr ih1 (@ih2 ρ.cons)
  | bvar i =>
    constructor <;> [intro h; intro ⟨j, h⟩]
    · refine (?_ : have := (match ρ.invS i with | SExpr.bvar .. => True | _ => True); _); split
      · rename_i eq; cases eq ▸ h; exact ⟨_, rfl⟩
      · suffices ρ.invS i = default by cases this ▸ h
        clear h; rename_i h
        induction ρ generalizing i <;> simp [Lift.invS, Subst.id] at * <;>
          cases i <;> simp [Subst.cons, Subst.lift] at *
        case skip.succ ih i => exact ih _ h
        case cons.succ ih i => rw [ih i fun j h' => h _ (by rw [h']; rfl)]; rfl
    · refine .trans (?_ : _ = (bvar j).lift' ρ) (congrArg bvar h); congr 1
      rw [← h]; exact congrFun (@lift_l_inv _ ρ) j

theorem skips_inter {e : SExpr} : Skips e (ρ.inter ρ') ↔ Skips e ρ ∧ Skips e ρ' := by
  simp [skips_iff]
  induction e generalizing ρ ρ' with simp_all!
  | app => grind
  | lam _ _ _ ih2 | forallE _ _ _ ih2 => have := @ih2 ρ.cons ρ'.cons; grind [Lift.inter]
  | bvar =>
    constructor
    · rintro ⟨j, rfl⟩; constructor
      · rw [Lift.inter_comm, ← Lift.diff_comp]; exact ⟨_, Lift.liftVar_comp.symm⟩
      · rw [← Lift.diff_comp]; exact ⟨_, Lift.liftVar_comp.symm⟩
    · rintro ⟨⟨i, h⟩, ⟨j, rfl⟩⟩
      induction ρ generalizing i j ρ' with
      | refl => simp [Lift.inter]
      | skip ρ ih =>
        cases ρ' with
        | refl => simp [Lift.inter]; cases h; exact ⟨_, rfl⟩
        | skip => simp_all [Lift.inter]; exact ih _ _ h
        | cons => cases j <;> simp_all [Lift.inter, Lift.liftVar]; exact ih _ _ h
      | cons ρ ih =>
        cases i <;> simp_all [Lift.liftVar]
        · cases ρ' with
          | refl => simp [Lift.inter]; cases h; exact ⟨0, rfl⟩
          | skip => let 0 := j; simp_all
          | cons => let 0 := j; exact ⟨0, rfl⟩
        · cases ρ' with
          | refl => cases h; exact ⟨_+1, rfl⟩
          | skip => simp_all [Lift.liftVar, Lift.inter]; exact ih _ _ h
          | cons =>
            let _+1 := j; simp_all [Lift.inter]
            have ⟨_, h⟩ := ih _ _ h; exact ⟨_+1, congrArg (·+1) h⟩

theorem lift_r_inj {σ σ' : Subst} : σ.lift_r ρ = σ'.lift_r ρ ↔ σ = σ' := by
  refine ⟨fun h => funext fun i => ?_, (· ▸ rfl)⟩
  simpa [Subst.lift_r, lift'_inj] using congrFun h i

theorem Subst.lift_r_comm (σ : Subst) (ρ : Lift) (H : Subst.Depth σ 0 n) :
    σ.lift_r ρ = .lift_l (ρ.consN n) ((σ.lift_r ρ).trunc 0 n) := by
  funext i; simp [Subst.lift_l, Subst.lift_r, Subst.trunc]
  have : (ρ.consN n).liftVar i = if n ≤ i then ρ.liftVar (i-n) + n else i := by
    clear H; induction n generalizing i <;> [skip; cases i] <;> simp! [*]; split <;> rfl
  rw [this]; split <;> simp
  have := H (i - n); rw [Nat.sub_add_cancel ‹_›] at this; simp [this]

theorem lift_r_one (e : SExpr) (ρ : Lift) :
    (Subst.one e).lift_r ρ = .lift_l ρ.cons (Subst.one (e.lift' ρ)) := by
  refine (Subst.lift_r_comm (Subst.one e) ρ .one).trans ?_; congr 1
  funext i; simp [Subst.trunc]
  cases i <;> simp [Subst.one, Subst.cons, Subst.lift_r, Subst.id]

theorem lift_inst (e : SExpr) : e.lift.inst e' = e := by
  rw [inst, Subst.one, lift, subst_lift', ← Subst.tail_eq_lift_l, Subst.tail_cons, subst_id]

theorem lift'_inst_hi (e1 e2 : SExpr) (ρ : Lift) :
    lift' (e1.inst e2) ρ = (lift' e1 ρ.cons).inst (lift' e2 ρ) := by
  simp [inst, subst_lift', lift'_subst, lift_r_one]

theorem subst_inst {e : SExpr} : (e.inst a).subst σ = (e.subst σ.lift).inst (a.subst σ) := by
  rw [SExpr.inst, SExpr.inst, subst_subst, subst_subst]; congr 1
  funext i; obtain _|i := i <;> simp [Subst.comp, Subst.lift, SExpr.subst]
  · simp [Subst.one, Subst.cons]
  · rw [← SExpr.inst, lift_inst]; rfl

theorem inst_lift_cons {e : SExpr} {σ : Subst} :
    (e.subst σ.lift).inst x = e.subst (σ.cons x) := by
  rw [SExpr.inst, subst_subst, Subst.one]; congr 1
  funext i; obtain _|i := i <;>
    simp [Subst.comp, Subst.lift, SExpr.subst, Subst.cons, lift_subst_cons]

inductive Ctx.Lift' : Lift → List SExpr → List SExpr → Prop where
  | refl : Ctx.Lift' .refl Γ Γ
  | skip : Ctx.Lift' l Γ Γ' → Ctx.Lift' (.skip l) Γ (A :: Γ')
  | cons : Ctx.Lift' l Γ Γ' → Ctx.Lift' (.cons l) (A::Γ) (A.lift' l :: Γ')

theorem Ctx.Lift'.one : Ctx.Lift' (.skip .refl) Γ (A::Γ) := .skip .refl

theorem Ctx.Lift'.comp (H1 : Ctx.Lift' l Γ₀ Γ₁) (H2 : Ctx.Lift' l' Γ₁ Γ₂) : Ctx.Lift' (l.comp l') Γ₀ Γ₂ := by
  induction H2 generalizing l Γ₀ with
  | refl => exact H1
  | skip _ ih => exact (ih H1).skip
  | cons H2 ih =>
    cases H1 with
    | refl => exact .cons H2
    | skip H1 => exact .skip (ih H1)
    | cons H1 => exact SExpr.lift'_comp ▸ .cons (ih H1)

inductive Ctx.Inter : List SExpr → List SExpr → Lift → List SExpr → Lift → List SExpr → Prop where
  | refl_l : Ctx.Lift' ρ Γ Δ → Ctx.Inter Γ Δ .refl Γ ρ Δ
  | refl_r : Ctx.Lift' ρ Γ Δ → Ctx.Inter Γ Γ ρ Δ .refl Δ
  | skip_skip : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ → Ctx.Inter Γ Γ₁ (.skip ρ₁) Γ₂ (.skip ρ₂) (A::Δ)
  | skip_cons : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ →
    Ctx.Inter Γ Γ₁ (.skip ρ₁) (A :: Γ₂) (.cons ρ₂) (A.lift' ρ₂ :: Δ)
  | cons_skip : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ →
    Ctx.Inter Γ (A :: Γ₁) (.cons ρ₁) Γ₂ (.skip ρ₂) (A.lift' ρ₁ :: Δ)
  | cons_cons : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ →
    Ctx.Inter (A :: Γ) (A.lift' (ρ₂.diff ρ₁) :: Γ₁) (.cons ρ₁)
      (A.lift' (ρ₁.diff ρ₂) :: Γ₂) (.cons ρ₂) (A.lift' (ρ₁.inter ρ₂) :: Δ)

theorem lift_eq_lift {e₁ e₂ : SExpr} (H : e₁.lift' ρ₁ = e₂.lift' ρ₂) :
    ∃ e, .lift' e (ρ₂.diff ρ₁) = e₁ ∧ e.lift' (ρ₁.diff ρ₂) = e₂ := by
  have := Skips.lift e₁ ρ₁
  have h1 : _ = _ := skips_inter.2 ⟨.lift e₁ ρ₁, H ▸ Skips.lift e₂ ρ₂⟩
  have h2 := h1; conv at h1 => enter [1,2]; rw [← Lift.diff_comp]
  conv at h2 => enter [1,2]; rw [Lift.inter_comm, ← Lift.diff_comp]
  rw [lift'_comp] at h1 h2
  exact ⟨_, lift'_inj.1 h2, lift'_inj.1 (h1.trans H)⟩

theorem Ctx.Inter.mk (H1 : Ctx.Lift' l₁ Γ₁ Δ) (H2 : Ctx.Lift' l₂ Γ₂ Δ) :
    ∃ Γ, Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ := by
  induction H1 generalizing l₂ Γ₂ with
  | refl => exact ⟨_, .refl_l H2⟩
  | skip H1 ih =>
    cases H2 with
    | refl => exact ⟨_, .refl_r (.skip H1)⟩
    | skip H2 => let ⟨_, H⟩ := ih H2; exact ⟨_, .skip_skip H⟩
    | cons H2 => let ⟨_, H⟩ := ih H2; exact ⟨_, .skip_cons H⟩
  | @cons l₁ _ _ A₁ H1 ih =>
    generalize eq : A₁.lift' l₁ = A' at H2
    cases H2 with
    | refl => subst eq; exact ⟨_, .refl_r (.cons H1)⟩
    | skip H2 => subst eq; let ⟨_, H⟩ := ih H2; exact ⟨_, .cons_skip H⟩
    | @cons l₂ _ _ A₂ H2 =>
      obtain ⟨_, rfl, rfl⟩ := lift_eq_lift eq
      rw [← lift'_comp, Lift.diff_comp]
      let ⟨_, H⟩ := ih H2; exact ⟨_, .cons_cons H⟩

theorem Ctx.Inter.symm (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Inter Γ Γ₂ l₂ Γ₁ l₁ Δ := by
  induction H with
  | refl_l h => exact .refl_r h
  | refl_r h => exact .refl_l h
  | skip_skip _ ih => exact .skip_skip ih
  | skip_cons _ ih => exact .cons_skip ih
  | cons_skip _ ih => exact .skip_cons ih
  | cons_cons _ ih => rw [Lift.inter_comm]; exact .cons_cons ih

theorem Ctx.Inter.diff (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Lift' (l₁.diff l₂) Γ Γ₂ := by
  induction H with
  | refl_l h => exact .refl
  | refl_r h => simpa
  | skip_skip _ ih | cons_skip _ ih => exact ih
  | skip_cons _ ih => exact ih.skip
  | cons_cons _ ih => exact ih.cons

theorem Ctx.Inter.right (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Lift' l₂ Γ₂ Δ := by
  induction H with
  | refl_l h => exact h
  | refl_r h => exact .refl
  | skip_skip _ ih => exact ih.skip
  | cons_skip _ ih => exact ih.skip
  | skip_cons _ ih => exact ih.cons
  | cons_cons _ ih => rw [← Lift.diff_comp, SExpr.lift'_comp]; exact ih.cons

theorem Ctx.Inter.left (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Lift' l₁ Γ₁ Δ := H.symm.right

inductive _root_.Lean4Lean.Pattern.MatchesS :
    (p : Pattern) → SExpr → List SLevel → (p.Path → SExpr) → Prop
  | const : MatchesS (.const c) (.const c ls) ls nofun
  | var : MatchesS f f' f1 g1 → MatchesS (.var f) (.app f' a') f1 (·.elim a' g1)
  | app : MatchesS f f' f1 g1 → MatchesS a a' f2 g2 →
    MatchesS (.app f a) (.app f' a') f1 (Sum.elim g1 g2)

def _root_.Lean4Lean.Pattern.RHS.applyS {p : Pattern}
    (m1 : List SLevel) (m2 : p.Path → SExpr) : p.RHS → SExpr
  | .fixed c _ => .instL m1 (.mk c)
  | .var path => m2 path
  | .app f a => .app (f.applyS m1 m2) (a.applyS m1 m2)

def _root_.Lean4Lean.Pattern.RHS.Closed {p : Pattern} : p.RHS → Prop
  | .fixed c _ => c.Closed
  | .var _ => True
  | .app f a => f.Closed ∧ a.Closed

theorem _root_.Lean4Lean.Pattern.RHS.Closed.applyS {p : Pattern} {m1 m2} :
    ∀ r : p.RHS, r.Closed → (∀ a, (m2 a).ClosedN k) → (r.applyS m1 m2).ClosedN k
  | .fixed .., h1, _ => h1.mkS.instL.mono (Nat.zero_le _)
  | .var _, _, h2 => h2 _
  | .app .., h1, h2 => ⟨h1.1.applyS _ h2, h1.2.applyS _ h2⟩

def _root_.Lean4Lean.Pattern.Check.defeqsS {p : Pattern}
    (m1 : List SLevel) (m2 : p.Path → SExpr) : p.Check → List (SExpr × SExpr)
  | .true => []
  | .defeq a b rest => (a.applyS m1 m2, b.applyS m1 m2) :: rest.defeqsS m1 m2
  -- added for the elim/proj constructors of this branch
  | .nonzero _ rest => rest.defeqsS m1 m2

section
set_option hygiene false

inductive Lookup : List SExpr → Nat → SExpr → Prop where
  | zero : Lookup (ty::Γ) 0 ty.lift
  | succ : Lookup Γ n ty → Lookup (A::Γ) (n+1) ty.lift

theorem Lookup.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Lookup Γ i A) :
    Lookup Γ' (ρ.liftVar i) (A.lift' ρ) := by
  induction W generalizing i A with
  | refl => simp; exact H
  | skip W ih => have' := (ih H).succ; rwa [SExpr.lift, ← SExpr.lift'_comp] at this
  | cons W ih =>
    cases H with
    | zero => refine' cast _ Lookup.zero; congr 1; simp [SExpr.lift, ← SExpr.lift'_comp]
    | succ H => refine' cast _ (ih H).succ; congr 1; simp [SExpr.lift, ← SExpr.lift'_comp]

theorem Lookup.weakU_inv (W : Ctx.Lift' ρ Γ Γ')
    (H : Lookup Γ' (ρ.liftVar i) A') : ∃ A, A' = A.lift' ρ ∧ Lookup Γ i A := by
  induction W generalizing i A' with
  | refl => simpa using H
  | @skip ρ W _ _ _ ih =>
    simp at H; let .succ H := H
    obtain ⟨_, rfl, h2⟩ := ih H; refine ⟨_, ?_, h2⟩
    rw [SExpr.lift, ← SExpr.lift'_comp]; rfl
  | @cons ρ Γ Δ B W ih =>
    cases i with
    | zero => cases H; exact ⟨_, by simp [SExpr.lift, ← SExpr.lift'_comp], .zero⟩
    | succ i =>
      let .succ (ty := C) H := H
      obtain ⟨C, rfl, h⟩ := ih H
      refine ⟨_, ?_, .succ h⟩
      simp [SExpr.lift, ← SExpr.lift'_comp]

theorem Lookup.weak'_inv (W : Ctx.Lift' ρ Γ Γ')
    (H : Lookup Γ' (ρ.liftVar i) (A.lift' ρ)) : Lookup Γ i A := by
  let ⟨_, h1, h2⟩ := H.weakU_inv W
  exact SExpr.lift'_inj.1 h1 ▸ h2

theorem Lookup.uniq (hA : Lookup Γ i A) (hB : Lookup Γ i B) : A = B :=
  match hA, hB with
  | .zero, .zero => rfl
  | .succ hA, .succ hB => Lookup.uniq hA hB ▸ rfl

theorem Lookup.determ (H1 : Lookup Γ i A) (H2 : Lookup Γ i A') : A = A' := by
  induction H1 generalizing A' with obtain _ | r1 := H2
  | zero => rfl
  | succ _ ih => cases ih r1; rfl

scoped notation:65 Γ " ⊢ " e " : " A:36 => IsDefEq Γ e e A
scoped notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEq Γ e1 e2 A
inductive IsDefEq : List SExpr → SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  /-- Heterogeneous transitivity: middle term may be at a different sort. -/
  | trans' : Γ ⊢ A ≡ B : .sort u → Γ ⊢ B ≡ C : .sort v → Γ ⊢ A ≡ C : .sort u
  | sort : Γ ⊢ .sort l : .sort (.succ l)
  | const : env.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ .const c ls : (SExpr.mk ci.type).instL ls
  | appDF : Γ ⊢ f ≡ f' : .forallE A B → Γ ⊢ a ≡ a' : A →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | lamDF : Γ ⊢ A ≡ A' : .sort u → A::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF : Γ ⊢ A ≡ A' : .sort u → A::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta : A::Γ ⊢ e : B → Γ ⊢ e' : A → Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta : Γ ⊢ e : .forallE A B → Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ h' : p
  -- | extra : Pat p r → p.MatchesS e m1 m2 → (dfs : List _).map (·.2) = r.2.defeqsS m1 m2 →
  --   (∀ a b A, (A, a, b) ∈ dfs → Γ ⊢ a ≡ b : A) → Γ ⊢ e ≡ r.1.applyS m1 m2' : A
  | extra : env.defeqs df → ls.length = df.uvars →
    Γ ⊢ .instL ls (.mk df.lhs) ≡ .instL ls (.mk df.rhs) : .instL ls (.mk df.type)

/-- **Assumption of the abstract prototype** (formerly the global axiom `Params.extra_pat`):
every stored rule `df` of the environment, at every level instance, is an instance of a
registered pattern `Pat p r` whose checks hold, in every context `Γ`, as `IsDefEq` judgments.

This is a property of the pattern registry that `Params` abstracts over (the `VExpr` analogue
is the registry built by `NativeRegistryOfWF`/`CanonicalRegistryOfWF`). It cannot be a field of
`Params` itself because it mentions `IsDefEq`, which is defined in terms of `Params`; so it is a
separate `Prop`-valued class over a `Params` instance, and every theorem that relies on it takes
`[Params.PatternRegistry]` as an explicit instance argument. -/
class Params.PatternRegistry : Prop where
  extra_pat (Γ) : env.defeqs df → ls.length = df.uvars →
    ∃ p r m1 m2 dfs, Pat p r ∧ p.MatchesS (.instL ls (.mk df.lhs)) m1 m2 ∧
      (dfs : List _).map (·.2) = r.2.defeqsS m1 m2 ∧
      (∀ a b A, (A, a, b) ∈ dfs → Γ ⊢ a ≡ b : A) ∧
      .instL ls (.mk df.rhs) = r.1.applyS m1 m2

theorem Params.extra_pat [Params.PatternRegistry] (Γ) : env.defeqs df → ls.length = df.uvars →
    ∃ p r m1 m2 dfs, Pat p r ∧ p.MatchesS (.instL ls (.mk df.lhs)) m1 m2 ∧
      (dfs : List _).map (·.2) = r.2.defeqsS m1 m2 ∧
      (∀ a b A, (A, a, b) ∈ dfs → Γ ⊢ a ≡ b : A) ∧
      .instL ls (.mk df.rhs) = r.1.applyS m1 m2 :=
  Params.PatternRegistry.extra_pat Γ

def CtorBundle.IsCtor (c : Name) : Prop :=
  ∃ cl, Params.classify c = some cl ∧ cl matches .ctor .. | .etaCtor ..

def CtorBundle.IsCtor.cl (H : CtorBundle.IsCtor c) :
    {cl // Params.classify c = some cl ∧ cl matches .ctor .. | .etaCtor ..} := by
  dsimp [CtorBundle.IsCtor] at H
  match Params.classify c, H with
  | some cl, H => refine ⟨cl, ?_⟩; obtain ⟨_, ⟨⟩, H⟩ := H; exact ⟨rfl, H⟩

structure CtorBundle (c : Name) (cl : CtorBundle.IsCtor c) : Type where
  I : Name
  Ts : List SExpr
  args : List SExpr
  u : SLevel
  hlen : Ts.length = cl.cl.1.arity
  hclI : Params.classify I = some (.indTy args.length)
  hu0 : u ≠ .zero

def CtorBundle.rhs (H : CtorBundle c cl) (ls : List SLevel) : SExpr :=
  H.Ts.foldr .forallE (H.args.foldr (fun A acc => acc.app A) (.const H.I ls))

section
local notation:65 (priority := high) Γ " ⊢ " e1 " : " A:36 => IsDefEqStrong Γ e1 e1 A
local notation:65 (priority := high) Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEqStrong Γ e1 e2 A
inductive IsDefEqStrong : List SExpr → SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ A : .sort u → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ A : .sort u → Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  /-- Heterogeneous transitivity: middle term may be at a different sort. -/
  | trans' : Γ ⊢ A ≡ B : .sort u → Γ ⊢ B ≡ C : .sort v → Γ ⊢ A ≡ C : .sort u
  | sort : Γ ⊢ .sort l : .sort (.succ l)
  | const : env.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ (SExpr.mk ci.type).instL ls : .sort u →
    (F : ∀ cl, CtorBundle c cl) →
    (∀ cl, Γ ⊢ (SExpr.mk ci.type).instL ls ≡ (F cl).rhs ls : .sort (F cl).u) →
    Γ ⊢ .const c ls : (SExpr.mk ci.type).instL ls
  | appDF : Γ ⊢ A : .sort u →
    Γ ⊢ f ≡ f' : .forallE A B → Γ ⊢ a ≡ a' : A →
    Γ ⊢ B.inst a ≡ B.inst a' : .sort v →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | lamDF : Γ ⊢ A ≡ A' : .sort u → A::Γ ⊢ B : .sort v →
    A::Γ ⊢ body ≡ body' : B → A'::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF : Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : .sort v → A'::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta : A::Γ ⊢ e : B → Γ ⊢ e' : A →
    Γ ⊢ .app (.lam A e) e' : B.inst e' → Γ ⊢ e.inst e' : B.inst e' →
    Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta : Γ ⊢ e : .forallE A B → Γ ⊢ .lam A (.app e.lift (.bvar 0)) : .forallE A B →
    Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ h' : p
  | extra : env.defeqs df → ls.length = df.uvars →
    Γ ⊢ .instL ls (.mk df.lhs) : .instL ls (.mk df.type) →
    Γ ⊢ .instL ls (.mk df.rhs) : .instL ls (.mk df.type) →
    Γ ⊢ .instL ls (.mk df.lhs) ≡ .instL ls (.mk df.rhs) : .instL ls (.mk df.type)
end

theorem IsDefEqStrong.defeq (H : IsDefEqStrong Γ e1 e2 A) : Γ ⊢ e1 ≡ e2 : A := by
  induction H with
  | bvar h => exact .bvar h
  | symm _ ih => exact .symm ih
  | trans _ _ _ _ ih1 ih2 => exact .trans ih1 ih2
  | trans' _ _ ih1 ih2 => exact .trans' ih1 ih2
  | sort => exact .sort
  | const h1 h2 => exact .const h1 h2
  | appDF _ _ _ _ _ ih1 ih2 => exact .appDF ih1 ih2
  | lamDF _ _ _ _ ih1 _ ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ _ _ ih1 ih2 => exact .beta ih1 ih2
  | eta _ _ ih => exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 => exact .extra h1 h2

theorem IsDefEq.hasType (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ ⊢ e1 ≡ e1 : A ∧ Γ ⊢ e2 ≡ e2 : A := ⟨H.trans H.symm, H.symm.trans H⟩

section
set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A true n
local notation:65 Γ " ⊢ " e " :! " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A false n

/-- A typing derivation indexed by its tree depth `n`, used for well-founded induction on
stratification. -/
inductive HasTypeStratifiedS : List SExpr → SExpr → SExpr → Bool → Nat → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ A : .sort u !! n → Γ ⊢ .bvar i :! A !! n+1
  | sort' : Γ ⊢ .sort l :! .sort (.succ l) !! n
  | const :
    env.constants c = some ci →
    ls.length = ci.uvars →
    Γ ⊢ (mk ci.type).instL ls : .sort u !! n →
    Γ ⊢ .const c ls :! (mk ci.type).instL ls !! n+1
  | app :
    Γ ⊢ A : .sort u !! n →
    A::Γ ⊢ B : .sort v !! n →
    Γ ⊢ f : .forallE A B !! n →
    Γ ⊢ a : A !! n →
    Γ ⊢ B.inst a : .sort v !! n →
    Γ ⊢ .app f a :! B.inst a !! n+1
  | lam :
    Γ ⊢ A : .sort u !! n →
    A::Γ ⊢ B : .sort v !! n →
    A::Γ ⊢ body : B !! n →
    Γ ⊢ .forallE A B : .sort (.imax u v) !! n →
    Γ ⊢ .lam A body :! .forallE A B !! n+1
  | forallE :
    Γ ⊢ A : .sort u !! n →
    A::Γ ⊢ body : .sort v !! n →
    Γ ⊢ .forallE A body :! .sort (.imax u v) !! n+1
  | base : Γ ⊢ e :! A !! n → Γ ⊢ e : A !! n
  | defeq : Γ ⊢ A ≡ B : .sort u →
    Γ ⊢ A : .sort u !! n → Γ ⊢ B : .sort u !! n →
    Γ ⊢ e : A !! n → Γ ⊢ e : B !! n+1
end

scoped notation:65 Γ " ⊢ " e " : " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A true n
scoped notation:65 Γ " ⊢ " e " :! " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A false n

theorem HasTypeStratifiedS.mono (le : m ≤ n) (H : HasTypeStratifiedS Γ e A b m) :
    HasTypeStratifiedS Γ e A b n := by
  induction H generalizing n with
  | bvar h1 _ ih =>
    cases n with | zero => omega | succ n => exact .bvar h1 (ih (by omega))
  | sort' => exact .sort'
  | const h1 h2 _ ih =>
    cases n with | zero => omega | succ n => exact .const h1 h2 (ih (by omega))
  | app _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 =>
    cases n with
    | zero => omega
    | succ n =>
      have le := Nat.le_of_succ_le_succ le
      exact .app (ih1 le) (ih2 le) (ih3 le) (ih4 le) (ih5 le)
  | lam _ _ _ _ ih1 ih2 ih3 ih4 =>
    cases n with
    | zero => omega
    | succ n =>
      have le := Nat.le_of_succ_le_succ le
      exact .lam (ih1 le) (ih2 le) (ih3 le) (ih4 le)
  | forallE _ _ ih1 ih2 =>
    cases n with
    | zero => omega
    | succ n => have le := Nat.le_of_succ_le_succ le; exact .forallE (ih1 le) (ih2 le)
  | base _ ih => exact .base (ih le)
  | defeq h1 _ _ _ ih2 ih3 ih4 =>
    cases n with
    | zero => omega
    | succ n =>
      have le := Nat.le_of_succ_le_succ le
      exact .defeq h1 (ih2 le) (ih3 le) (ih4 le)

theorem HasTypeStratifiedS.to_core (H : Γ ⊢ e : A !! n) :
    ∃ A', Γ ⊢ e :! A' !! n := by
  generalize true = b at H
  induction H with
  | bvar h1 h2 => exact ⟨_, .bvar h1 h2⟩
  | sort' => exact ⟨_, .sort'⟩
  | const h1 h2 h3 => exact ⟨_, .const h1 h2 h3⟩
  | app h1 h2 h3 h4 h5 => exact ⟨_, .app h1 h2 h3 h4 h5⟩
  | lam h1 h2 h3 h4 => exact ⟨_, .lam h1 h2 h3 h4⟩
  | forallE h1 h2 => exact ⟨_, .forallE h1 h2⟩
  | base h => exact ⟨_, h⟩
  | defeq _ _ _ _ _ _ ih => let ⟨_, h⟩ := ih; exact ⟨_, h.mono (Nat.le_succ _)⟩

theorem HasTypeStratifiedS.isType (H : HasTypeStratifiedS Γ e A b n) :
    ∃ u, Γ ⊢ A : .sort u !! n - 1 := by
  induction H with
  | bvar _ h2 => exact ⟨_, h2⟩
  | sort' | forallE => exact ⟨_, .base .sort'⟩
  | const _ _ h3 => exact ⟨_, h3⟩
  | app _ _ _ _ h5 => exact ⟨_, h5⟩
  | lam _ _ _ h4 => exact ⟨_, h4⟩
  | base _ ih => exact ih
  | defeq _ _ h3 => exact ⟨_, h3⟩

def Ctx.WF : List SExpr → Prop
  | [] => True
  | A::Γ => WF Γ ∧ ∃ u, Γ ⊢ A : .sort u
scoped notation:65 "⊢ " Γ:36 => Ctx.WF Γ

theorem IsDefEq.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ' ⊢ e1.lift' ρ ≡ e2.lift' ρ : A.lift' ρ := by
  induction H generalizing ρ Γ' with
  | bvar h => refine .bvar (h.weak' W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | trans' _ _ ih1 ih2 => exact .trans' (ih1 W) (ih2 W)
  | sort => exact .sort
  | const h1 h2 => rw [(henv.closedC h1).mkS.instL.lift'_eq .zero]; exact .const h1 h2
  | appDF _ _ ih1 ih2 => exact SExpr.lift'_inst_hi .. ▸ .appDF (ih1 W) (ih2 W)
  | lamDF _ _ ih1 ih2 => exact .lamDF (ih1 W) (ih2 W.cons)
  | forallEDF _ _ ih1 ih2 => exact .forallEDF (ih1 W) (ih2 W.cons)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ ih1 ih2 =>
    rw [SExpr.lift'_inst_hi, SExpr.lift'_inst_hi]
    exact .beta (ih1 W.cons) (ih2 W)
  | eta _ ih => refine cast ?_ (IsDefEq.eta (ih W)); congr 1; simp [← SExpr.lift'_comp]
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
    rw [hA1.mkS.instL.lift'_eq .zero, hA2.mkS.instL.lift'_eq .zero, hA3.mkS.instL.lift'_eq .zero]
    exact .extra h1 h2

variable (HasType : List SExpr → SExpr → SExpr → Prop)
inductive Ctx.Subst (Γ : List SExpr) : SExpr.Subst → List SExpr → Prop where
  | nil : Ctx.Subst Γ σ []
  | cons : Ctx.Subst Γ σ.tail Δ → HasType Γ σ.head (A.subst σ.tail) → Ctx.Subst Γ σ (A::Δ)

variable {HasType}
theorem Ctx.Subst.head (H : Ctx.Subst HasType Γ σ (A::Δ)) : HasType Γ σ.head (A.subst σ.tail) :=
  let .cons _ H := H; H

theorem Ctx.Subst.tail (H : Ctx.Subst HasType Γ σ (A::Δ)) : Ctx.Subst HasType Γ σ.tail Δ :=
  let .cons H _ := H; H

theorem Ctx.Subst.cons' (H1 : Ctx.Subst HasType Γ σ Δ) (H2 : HasType Γ e (A.subst σ)) :
    Ctx.Subst HasType Γ (σ.cons e) (A::Δ) := .cons H1 H2

theorem Ctx.Subst.lookup (W : Ctx.Subst HasType Γ₀ σ Γ) (h : Lookup Γ i A) :
    HasType Γ₀ (σ i) (A.subst σ) := by
  induction W generalizing i A with
  | nil => nomatch h
  | cons _ h0 ih =>
    cases h with
    | zero => rw [lift_subst]; exact h0
    | succ h => rw [lift_subst]; exact ih h

/-- A variable renaming `i ↦ f i` is a substitution `Γ → Δ` as soon as it is one on the
variables, i.e. as soon as `HasType` holds at the renamed variables. -/
theorem Ctx.Subst.bvar_comp {f : Nat → Nat}
    (bvar : ∀ {i A}, Lookup Γ i A → HasType Δ (.bvar (f i)) (A.subst (.bvar ∘ f))) :
    Ctx.Subst HasType Δ (.bvar ∘ f) Γ := by
  induction Γ generalizing f with
  | nil => exact .nil
  | cons A Γ ih =>
    refine .cons (ih (f := f ∘ (· + 1)) fun h => ?_) ?_
    · have := bvar (.succ h); rwa [lift_subst] at this
    · have := bvar .zero; rwa [lift_subst] at this

/-- Weakening of a substitution. The original statement had no hypothesis on `HasType`, and is
false for an arbitrary `HasType` (take one that holds only in `Θ`); it needs `HasType` to be
stable under weakening, which is the hypothesis `weak`. -/
theorem Ctx.Subst.lift_r
    (weak : ∀ {ρ Γ Γ' e A}, Ctx.Lift' ρ Γ Γ' → HasType Γ e A → HasType Γ' (e.lift' ρ) (A.lift' ρ))
    (H1 : Ctx.Subst HasType Θ σ Γ) (H2 : Ctx.Lift' ρ Θ Δ) :
    Ctx.Subst HasType Δ (σ.lift_r ρ) Γ := by
  induction H1 with
  | nil => exact .nil
  | cons _ h ih => exact .cons ih (by have := weak H2 h; rwa [lift'_subst] at this)

theorem Ctx.Subst.lift (bvar : ∀ {Γ i A}, Lookup Γ i A → HasType Γ (bvar i) A)
    (weak : ∀ {ρ Γ Γ' e A}, Ctx.Lift' ρ Γ Γ' → HasType Γ e A → HasType Γ' (e.lift' ρ) (A.lift' ρ))
    (H : Ctx.Subst HasType Γ σ Δ) : Ctx.Subst HasType (A.subst σ :: Γ) σ.lift (A :: Δ) := by
  have : σ.lift.tail = σ.lift_r (.skip .refl) := by
    funext i; simp [SExpr.Subst.tail, SExpr.Subst.lift, SExpr.Subst.lift_r]
  refine .cons (this ▸ .lift_r weak H .one) (this ▸ bvar ?_)
  rw [← lift'_subst, ← SExpr.lift]; exact .zero

/-- The identity substitution. The original statement had no hypothesis on `HasType`, and is
false for an arbitrary `HasType` (take `fun _ _ _ => False`); it needs `HasType` to hold at the
variables of `Γ`, which is the hypothesis `bvar`. -/
theorem Ctx.Subst.id (bvar : ∀ {i A}, Lookup Γ i A → HasType Γ (.bvar i) A) :
    Ctx.Subst HasType Γ .id Γ :=
  Ctx.Subst.bvar_comp (f := fun i => i) fun h => by
    rw [show (SExpr.bvar ∘ fun i => i) = SExpr.Subst.id from rfl, subst_id]; exact bvar h

theorem Ctx.Subst.one (bvar : ∀ {i A}, Lookup Γ i A → HasType Γ (.bvar i) A)
    (H : HasType Γ e A) : Ctx.Subst HasType Γ (.one e) (A::Γ) :=
  .cons (.id bvar) (by simpa)

theorem Ctx.Subst.liftD (W : Ctx.Subst (· ⊢ · : ·) Γ₀ σ Γ) :
    Ctx.Subst (· ⊢ · : ·) (A.subst σ :: Γ₀) σ.lift (A :: Γ) :=
  W.lift .bvar fun W h => h.weak' W

/-- A weakening `ρ : Γ → Γ₀` is a substitution for `IsDefEq`. -/
theorem Ctx.Subst.ofLift (W : Ctx.Lift' ρ Γ Γ₀) : Ctx.Subst (· ⊢ · : ·) Γ₀ ρ.toSubst Γ :=
  Ctx.Subst.bvar_comp (f := ρ.liftVar) fun h => by
    rw [show (SExpr.bvar ∘ ρ.liftVar) = ρ.toSubst from rfl, subst_toSubst]
    exact .bvar (h.weak' W)

/-- Substitution of an `IsDefEq`-typed substitution into an `IsDefEq` derivation (the same
substitution on both sides). -/
theorem IsDefEq.subst' (W : Ctx.Subst (· ⊢ · : ·) Γ₀ σ Γ) (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ₀ ⊢ e1.subst σ ≡ e2.subst σ : A.subst σ := by
  induction H generalizing Γ₀ σ with
  | bvar h => exact W.lookup h
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | trans' _ _ ih1 ih2 => exact .trans' (ih1 W) (ih2 W)
  | sort => exact .sort
  | const h1 h2 => rw [(henv.closedC h1).mkS.instL.subst_eq .zero]; exact .const h1 h2
  | appDF _ _ ih1 ih2 => exact subst_inst ▸ .appDF (ih1 W) (ih2 W)
  | lamDF _ _ ih1 ih2 => exact .lamDF (ih1 W) (ih2 W.liftD)
  | forallEDF _ _ ih1 ih2 => exact .forallEDF (ih1 W) (ih2 W.liftD)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ ih1 ih2 => rw [subst_inst, subst_inst]; exact .beta (ih1 W.liftD) (ih2 W)
  | @eta _ e A' B' _ ih =>
    have : (SExpr.lift e).subst σ.lift = (e.subst σ).lift := by
      rw [lift_subst, show σ.lift.tail = σ.lift_r (.skip .refl) by
        funext i; simp [SExpr.Subst.tail, SExpr.Subst.lift, SExpr.Subst.lift_r], ← lift'_subst]
    show Γ₀ ⊢ .lam (A'.subst σ) (.app ((SExpr.lift e).subst σ.lift) (.bvar 0)) ≡ e.subst σ :
      .forallE (A'.subst σ) (B'.subst σ.lift)
    rw [this]; exact .eta (ih W)
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
    rw [hA1.mkS.instL.subst_eq .zero, hA2.mkS.instL.subst_eq .zero, hA3.mkS.instL.subst_eq .zero]
    exact .extra h1 h2

/-- A pair of pointwise definitionally equal substitutions taking `Γ` to `Γ₀`.

The base case is an arbitrary weakening `ρ : Γ → Γ₀`. (The original base case
`Ctx.SubstEq Γ₀ .id .id Γ₀` pinned the base context to `Γ₀`, which made `Ctx.SubstEq.lift`
false: lifting `Ctx.SubstEq [] (.one x) (.one x) [B]` under a binder `A` would need a
`Ctx.SubstEq [A'] _ _ []`, which no constructor produces. The identity case is now the lemma
`Ctx.SubstEq.id`.) The binder types carry strong typing derivations (`IsDefEqStrong`), from
which the two-sided substitution `IsDefEqStrong.substEq` is proved without further
assumptions. -/
inductive Ctx.SubstEq (Γ₀ : List SExpr) : SExpr.Subst → SExpr.Subst → List SExpr → Prop where
  | nil : Ctx.Lift' ρ Γ Γ₀ → Ctx.SubstEq Γ₀ ρ.toSubst ρ.toSubst Γ
  | cons : Ctx.SubstEq Γ₀ σ.tail σ'.tail Γ →
    IsDefEqStrong Γ A A (.sort u) →
    Γ₀ ⊢ σ.head ≡ σ'.head : A.subst σ.tail →
    Ctx.SubstEq Γ₀ σ σ' (A :: Γ)

theorem Ctx.SubstEq.id : Ctx.SubstEq Γ₀ .id .id Γ₀ := .nil (ρ := .refl) .refl

theorem Ctx.SubstEq.left (W : Ctx.SubstEq Γ₀ σ σ' Γ) : Ctx.Subst (· ⊢ · : ·) Γ₀ σ Γ := by
  induction W with
  | nil W => exact .ofLift W
  | cons _ _ h ih => exact .cons ih h.hasType.1

theorem Ctx.SubstEq.lookup (W : Ctx.SubstEq Γ₀ σ σ' Γ) :
    Lookup Γ i A → Γ₀ ⊢ σ i ≡ σ' i : A.subst σ := by
  intro h
  induction W generalizing i A with
  | nil W => rw [subst_toSubst]; exact .bvar (h.weak' W)
  | cons _ _ hhead ih =>
    cases h with
    | zero => rw [lift_subst]; exact hhead
    | succ h => rw [lift_subst]; exact ih h

/-- Weakening of the target context of a `Ctx.SubstEq`. -/
theorem Ctx.SubstEq.weak' (W : Ctx.SubstEq Γ₀ σ σ' Γ) (L : Ctx.Lift' ρ Γ₀ Γ₁) :
    Ctx.SubstEq Γ₁ (σ.lift_r ρ) (σ'.lift_r ρ) Γ := by
  have comp (ρ₀ : Lift) : (Lift.toSubst ρ₀).lift_r ρ = (ρ₀.comp ρ).toSubst := by
    funext i; simp [SExpr.Subst.lift_r, Lift.toSubst_apply, Lift.liftVar_comp]
  induction W with
  | nil W => rw [comp]; exact .nil (W.comp L)
  | cons _ hA hhead ih =>
    refine .cons ih hA ?_
    have := hhead.weak' L; rwa [lift'_subst] at this

/-- Extension under a binder. The original hypothesis was `Γ₀ ⊢ A.subst σ : .sort u`; the
`cons` case needs the binder type typed in the *source* context, `Γ ⊢ A : .sort u` (strongly),
which every caller has. -/
theorem Ctx.SubstEq.lift (W : Ctx.SubstEq Γ₀ σ σ' Γ) (hA : IsDefEqStrong Γ A A (.sort u)) :
    Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift σ'.lift (A :: Γ) := by
  have htail {σ : SExpr.Subst} : σ.lift.tail = σ.lift_r (.skip .refl) := by
    funext i; simp [SExpr.Subst.tail, SExpr.Subst.lift, SExpr.Subst.lift_r]
  have := W.weak' (Ctx.Lift'.one (A := A.subst σ))
  rw [← htail, ← htail] at this
  refine .cons this hA ?_
  show _ ⊢ .bvar 0 ≡ .bvar 0 : A.subst σ.lift.tail
  rw [htail, ← lift'_subst]; exact .bvar .zero

theorem IsDefEq.defeqDF_l' (h1 : Γ ⊢ A ≡ A' : .sort u)
    (h2 : Δ++A::Γ ⊢ e1 ≡ e2 : B) : Δ++A'::Γ ⊢ e1 ≡ e2 : B := by
  have bvar {Δ i B} (h : Lookup (Δ++A::Γ) i B) : Δ++A'::Γ ⊢ .bvar i : B := by
    induction Δ generalizing i B with
    | nil =>
      cases h with
      | zero => exact .defeqDF (h1.symm.weak' .one) (.bvar .zero)
      | succ h => exact .bvar (.succ h)
    | cons D Δ ih =>
      cases h with
      | zero => exact .bvar .zero
      | succ h => exact (ih h).weak' .one
  generalize eq : Δ ++ A :: Γ = Γ' at h2
  induction h2 generalizing Δ with subst eq
  | bvar h => exact bvar h
  | symm _ ih => exact .symm (ih rfl)
  | trans _ _ ih1 ih2 => exact .trans (ih1 rfl) (ih2 rfl)
  | trans' _ _ ih1 ih2 => exact .trans' (ih1 rfl) (ih2 rfl)
  | sort => exact .sort
  | const h1 h2 => exact .const h1 h2
  | appDF _ _ ih1 ih2 => exact .appDF (ih1 rfl) (ih2 rfl)
  | lamDF _ _ ih1 ih2 => exact .lamDF (ih1 rfl) (ih2 (Δ := _ :: _) rfl)
  | forallEDF _ _ ih1 ih2 => exact .forallEDF (ih1 rfl) (ih2 (Δ := _ :: _) rfl)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 rfl) (ih2 rfl)
  | beta _ _ ih1 ih2 => exact .beta (ih1 (Δ := _ :: _) rfl) (ih2 rfl)
  | eta _ ih => exact .eta (ih rfl)
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 rfl) (ih2 rfl) (ih3 rfl)
  | extra h1 h2 => exact .extra h1 h2

theorem IsDefEq.defeqDF_l (h1 : Γ ⊢ A ≡ A' : .sort u)
    (h2 : A::Γ ⊢ e1 ≡ e2 : B) : A'::Γ ⊢ e1 ≡ e2 : B :=
  .defeqDF_l' (Δ := []) h1 h2

theorem HasType.defeq_l (h1 : Γ ⊢ A ≡ A' : .sort u)
    (h2 : A::Γ ⊢ e : B) : A'::Γ ⊢ e : B := h1.defeqDF_l h2

/-! ### The strong judgment: weakening, substitution, validity

`IsDefEq.strong` turns an `IsDefEq` derivation into an `IsDefEqStrong` one, whose rules carry
typing premises. It needs a well-formed context and the typing assumptions
`Params.TypedEnv` on the environment. -/

section
local notation:65 Γ " ⊢ₛ " e " : " A:36 => IsDefEqStrong Γ e e A
local notation:65 Γ " ⊢ₛ " e1 " ≡ " e2 " : " A:36 => IsDefEqStrong Γ e1 e2 A

theorem closed_lift' {c : VExpr} (h : c.Closed) : (instL ls (mk c)).lift' ρ = instL ls (mk c) :=
  h.mkS.instL.lift'_eq .zero

theorem closed_subst {c : VExpr} (h : c.Closed) : (instL ls (mk c)).subst σ = instL ls (mk c) :=
  h.mkS.instL.subst_eq .zero

theorem Ctx.Lift'.nil : ∀ Γ, ∃ ρ, Ctx.Lift' ρ [] Γ
  | [] => ⟨_, .refl⟩
  | _::Γ => let ⟨_, h⟩ := Ctx.Lift'.nil Γ; ⟨_, h.skip⟩

theorem lift'_eta {A e : SExpr} :
    (SExpr.lam A (.app e.lift (.bvar 0))).lift' ρ = .lam (A.lift' ρ) (.app (e.lift' ρ).lift (.bvar 0)) := by
  simp [SExpr.lift, ← SExpr.lift'_comp]

theorem subst_eta {A e : SExpr} :
    (SExpr.lam A (.app e.lift (.bvar 0))).subst σ = .lam (A.subst σ) (.app (e.subst σ).lift (.bvar 0)) := by
  have : (SExpr.lift e).subst σ.lift = (e.subst σ).lift := by
    rw [lift_subst, show σ.lift.tail = σ.lift_r (.skip .refl) by
      funext i; simp [SExpr.Subst.tail, SExpr.Subst.lift, SExpr.Subst.lift_r], ← lift'_subst]
  simp only [SExpr.subst, this]; rfl

theorem inst_lift_bvar0 {B : SExpr} : (B.lift' (Lift.skip .refl).cons).inst (.bvar 0) = B := by
  rw [inst, subst_lift']
  conv => rhs; rw [← subst_id (e := B)]
  congr 1; funext i; cases i <;> rfl

theorem foldr_app_lift' {args : List SExpr} :
    (args.foldr (fun (A acc : SExpr) => acc.app A) (SExpr.const I ls)).lift' ρ =
      (args.map (·.lift' ρ)).foldr (fun (A acc : SExpr) => acc.app A) (SExpr.const I ls) := by
  induction args <;> simp_all [lift']

theorem foldr_app_subst {args : List SExpr} :
    (args.foldr (fun (A acc : SExpr) => acc.app A) (SExpr.const I ls)).subst σ =
      (args.map (·.subst σ)).foldr (fun (A acc : SExpr) => acc.app A) (SExpr.const I ls) := by
  induction args <;> simp_all [subst]

theorem foldr_forallE_lift' (Ts : List SExpr) (body : SExpr) (ρ : Lift) :
    ∃ (Ts' : List SExpr) (ρ' : Lift), Ts'.length = Ts.length ∧
      (Ts.foldr .forallE body).lift' ρ = Ts'.foldr .forallE (body.lift' ρ') := by
  induction Ts generalizing ρ with
  | nil => exact ⟨[], ρ, rfl, rfl⟩
  | cons T Ts ih =>
    obtain ⟨Ts', ρ', h1, h2⟩ := ih ρ.cons
    exact ⟨T.lift' ρ :: Ts', ρ', by simp [h1], by simp [h2]⟩

theorem foldr_forallE_subst (Ts : List SExpr) (body : SExpr) (σ : Subst) :
    ∃ (Ts' : List SExpr) (σ' : Subst), Ts'.length = Ts.length ∧
      (Ts.foldr .forallE body).subst σ = Ts'.foldr .forallE (body.subst σ') := by
  induction Ts generalizing σ with
  | nil => exact ⟨[], σ, rfl, rfl⟩
  | cons T Ts ih =>
    obtain ⟨Ts', σ', h1, h2⟩ := ih σ.lift
    exact ⟨T.subst σ :: Ts', σ', by simp [h1], by simp [subst, h2]⟩

theorem CtorBundle.lift' (H : CtorBundle c cl) (ls : List SLevel) (ρ : Lift) :
    ∃ H' : CtorBundle c cl, H'.u = H.u ∧ (H.rhs ls).lift' ρ = H'.rhs ls := by
  obtain ⟨Ts', ρ', h1, h2⟩ :=
    foldr_forallE_lift' H.Ts (H.args.foldr (fun A acc => acc.app A) (.const H.I ls)) ρ
  refine ⟨⟨H.I, Ts', H.args.map (fun x => x.lift' ρ'), H.u, h1.trans H.hlen,
    by simpa using H.hclI, H.hu0⟩, rfl, ?_⟩
  rw [CtorBundle.rhs, h2, foldr_app_lift']; rfl

theorem CtorBundle.subst (H : CtorBundle c cl) (ls : List SLevel) (σ : Subst) :
    ∃ H' : CtorBundle c cl, H'.u = H.u ∧ (H.rhs ls).subst σ = H'.rhs ls := by
  obtain ⟨Ts', σ', h1, h2⟩ :=
    foldr_forallE_subst H.Ts (H.args.foldr (fun A acc => acc.app A) (.const H.I ls)) σ
  refine ⟨⟨H.I, Ts', H.args.map (fun x => x.subst σ'), H.u, h1.trans H.hlen,
    by simpa using H.hclI, H.hu0⟩, rfl, ?_⟩
  rw [CtorBundle.rhs, h2, foldr_app_subst]; rfl

theorem IsDefEqStrong.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ₛ e1 ≡ e2 : A) :
    Γ' ⊢ₛ e1.lift' ρ ≡ e2.lift' ρ : A.lift' ρ := by
  induction H generalizing ρ Γ' with
  | bvar h _ ih => exact .bvar (h.weak' W) (ih W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ _ ihA ih1 ih2 => exact .trans (ihA W) (ih1 W) (ih2 W)
  | trans' _ _ ih1 ih2 => exact .trans' (ih1 W) (ih2 W)
  | sort => exact .sort
  | @const c ci _ ls _ h1 h2 _ F _ ih3 ih5 =>
    have hcl := henv.closedC h1
    have h3' := ih3 W; rw [closed_lift' hcl] at h3'
    rw [closed_lift' hcl]
    have ex cl : ∃ H' : CtorBundle c cl,
        Γ' ⊢ₛ (SExpr.mk ci.type).instL ls ≡ H'.rhs ls : .sort H'.u := by
      obtain ⟨H', hu, hr⟩ := (F cl).lift' ls ρ
      have := ih5 cl W; simp only [lift'] at this; rw [closed_lift' hcl, hr, ← hu] at this
      exact ⟨H', this⟩
    exact .const h1 h2 h3' (fun cl => Classical.choose (ex cl)) fun cl => Classical.choose_spec (ex cl)
  | appDF _ _ _ _ ihA ihf iha ihB =>
    have := ihB W; simp only [lift', SExpr.lift'_inst_hi] at this
    exact SExpr.lift'_inst_hi .. ▸ .appDF (ihA W) (ihf W) (iha W) this
  | lamDF _ _ _ _ ihA ihB ih1 ih2 => exact .lamDF (ihA W) (ihB W.cons) (ih1 W.cons) (ih2 W.cons)
  | forallEDF _ _ _ ihA ih1 ih2 => exact .forallEDF (ihA W) (ih1 W.cons) (ih2 W.cons)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ _ _ ih1 ih2 ih3 ih4 =>
    have h3 := ih3 W; have h4 := ih4 W
    simp only [lift', SExpr.lift'_inst_hi] at h3 h4 ⊢
    exact .beta (ih1 W.cons) (ih2 W) h3 h4
  | eta _ _ ih1 ih2 =>
    have h2 := ih2 W; rw [lift'_eta] at h2; rw [lift'_eta]; exact .eta (ih1 W) h2
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 _ _ ih1 ih2 =>
    have ⟨⟨hl, ht⟩, hr, _⟩ := henv.closed.2 h1
    have h3 := ih1 W; have h4 := ih2 W
    simp only [closed_lift' hl, closed_lift' hr, closed_lift' ht] at h3 h4 ⊢
    exact .extra h1 h2 h3 h4

theorem IsDefEqStrong.weak0 (H : [] ⊢ₛ e1 ≡ e2 : A) :
    ∃ ρ, Γ ⊢ₛ e1.lift' ρ ≡ e2.lift' ρ : A.lift' ρ :=
  let ⟨ρ, W⟩ := Ctx.Lift'.nil Γ; ⟨ρ, H.weak' W⟩

theorem IsDefEqStrong.left_sort (h : Γ ⊢ₛ X ≡ Y : .sort u) : Γ ⊢ₛ X : .sort u :=
  .trans .sort h h.symm

theorem IsDefEqStrong.right_sort (h : Γ ⊢ₛ X ≡ Y : .sort u) : Γ ⊢ₛ Y : .sort u :=
  .trans .sort h.symm h

/-- Validity for the strong judgment: the type of a strong derivation is a type. -/
theorem IsDefEqStrong.isType (H : Γ ⊢ₛ e1 ≡ e2 : A) : ∃ u, Γ ⊢ₛ A : .sort u := by
  induction H with
  | bvar _ h => exact ⟨_, h⟩
  | symm _ ih => exact ih
  | trans hA => exact ⟨_, hA⟩
  | trans' | forallEDF | sort => exact ⟨_, .sort⟩
  | const _ _ h => exact ⟨_, h⟩
  | appDF _ _ _ hB => exact ⟨_, hB.left_sort⟩
  | lamDF hA hB => exact ⟨_, .forallEDF hA.left_sort hB hB⟩
  | defeqDF hAB => exact ⟨_, hAB.right_sort⟩
  | beta _ _ _ _ _ _ ih => exact ih
  | eta _ _ ih => exact ih
  | proofIrrel h => exact ⟨_, h⟩
  | extra _ _ _ _ ih => exact ih

theorem IsDefEqStrong.left (H : Γ ⊢ₛ e1 ≡ e2 : A) : Γ ⊢ₛ e1 : A :=
  let ⟨_, h⟩ := H.isType; .trans h H H.symm

theorem IsDefEqStrong.right (H : Γ ⊢ₛ e1 ≡ e2 : A) : Γ ⊢ₛ e2 : A :=
  let ⟨_, h⟩ := H.isType; .trans h H.symm H

end

section
local notation:65 Γ " ⊢ₛ " e " : " A:36 => IsDefEqStrong Γ e e A
local notation:65 Γ " ⊢ₛ " e1 " ≡ " e2 " : " A:36 => IsDefEqStrong Γ e1 e2 A

/-- Strong typing, as a ternary relation for `Ctx.Subst`. -/
abbrev StrongHasType (Γ : List SExpr) (e A : SExpr) : Prop := Γ ⊢ₛ e : A

theorem Ctx.Subst.liftS (W : Ctx.Subst StrongHasType Γ₀ σ Γ) (hA : Γ₀ ⊢ₛ A.subst σ : .sort u) :
    Ctx.Subst StrongHasType (A.subst σ :: Γ₀) σ.lift (A :: Γ) := by
  have : σ.lift.tail = σ.lift_r (.skip .refl) := by
    funext i; simp [SExpr.Subst.tail, SExpr.Subst.lift, SExpr.Subst.lift_r]
  refine .cons (this ▸ .lift_r (fun W h => IsDefEqStrong.weak' W h) W .one) (this ▸ ?_)
  rw [← lift'_subst, ← SExpr.lift]; exact .bvar .zero (hA.weak' .one)

/-- Substitution of a strongly typed substitution into a strong derivation (the same
substitution on both sides). -/
theorem IsDefEqStrong.subst' (W : Ctx.Subst StrongHasType Γ₀ σ Γ) (H : Γ ⊢ₛ e1 ≡ e2 : A) :
    Γ₀ ⊢ₛ e1.subst σ ≡ e2.subst σ : A.subst σ := by
  induction H generalizing Γ₀ σ with
  | bvar h => exact W.lookup h
  | symm _ ih => exact .symm (ih W)
  | trans _ _ _ ihA ih1 ih2 => exact .trans (ihA W) (ih1 W) (ih2 W)
  | trans' _ _ ih1 ih2 => exact .trans' (ih1 W) (ih2 W)
  | sort => exact .sort
  | @const c ci _ ls _ h1 h2 _ F _ ih3 ih5 =>
    have hcl := henv.closedC h1
    have h3' := ih3 W; rw [closed_subst hcl] at h3'
    rw [closed_subst hcl]
    have ex cl : ∃ H' : CtorBundle c cl,
        Γ₀ ⊢ₛ (SExpr.mk ci.type).instL ls ≡ H'.rhs ls : .sort H'.u := by
      obtain ⟨H', hu, hr⟩ := (F cl).subst ls σ
      have := ih5 cl W; simp only [subst] at this; rw [closed_subst hcl, hr, ← hu] at this
      exact ⟨H', this⟩
    exact .const h1 h2 h3' (fun cl => Classical.choose (ex cl)) fun cl => Classical.choose_spec (ex cl)
  | appDF _ _ _ _ ihA ihf iha ihB =>
    have := ihB W; simp only [subst, subst_inst] at this
    exact subst_inst ▸ .appDF (ihA W) (ihf W) (iha W) this
  | lamDF _ _ _ _ ihA ihB ih1 ih2 =>
    have hA := ihA W
    exact .lamDF hA (ihB (W.liftS hA.left)) (ih1 (W.liftS hA.left)) (ih2 (W.liftS hA.right))
  | forallEDF _ _ _ ihA ih1 ih2 =>
    have hA := ihA W
    exact .forallEDF hA (ih1 (W.liftS hA.left)) (ih2 (W.liftS hA.right))
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ _ _ ih1 ih2 ih3 ih4 =>
    have h2 := ih2 W; have ⟨_, hA⟩ := h2.isType
    have h3 := ih3 W; have h4 := ih4 W
    simp only [subst, subst_inst] at h3 h4 ⊢
    exact .beta (ih1 (W.liftS hA)) h2 h3 h4
  | eta _ _ ih1 ih2 =>
    have h2 := ih2 W; rw [subst_eta] at h2; rw [subst_eta]; exact .eta (ih1 W) h2
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 _ _ ih1 ih2 =>
    have ⟨⟨hl, ht⟩, hr, _⟩ := henv.closed.2 h1
    have h3 := ih1 W; have h4 := ih2 W
    simp only [closed_subst hl, closed_subst hr, closed_subst ht] at h3 h4 ⊢
    exact .extra h1 h2 h3 h4

/-- Strong well-formedness of a context: every entry is strongly typed by a sort. -/
def CtxStrong : List SExpr → Prop
  | [] => True
  | A::Γ => CtxStrong Γ ∧ ∃ u, Γ ⊢ₛ A : .sort u

theorem CtxStrong.lookup : ∀ {Γ}, CtxStrong Γ → Lookup Γ i A → ∃ u, Γ ⊢ₛ A : .sort u
  | _::_, ⟨_, _, h⟩, .zero => ⟨_, h.weak' .one⟩
  | _::_, ⟨hΓ, _⟩, .succ l => let ⟨_, h⟩ := hΓ.lookup l; ⟨_, h.weak' .one⟩

theorem CtxStrong.bvar (hΓ : CtxStrong Γ) (h : Lookup Γ i A) : Γ ⊢ₛ .bvar i : A :=
  let ⟨_, h'⟩ := hΓ.lookup h; .bvar h h'

theorem IsDefEqStrong.inst (H : A::Γ ⊢ₛ e1 ≡ e2 : B) (hΓ : CtxStrong Γ) (H₀ : Γ ⊢ₛ a : A) :
    Γ ⊢ₛ e1.inst a ≡ e2.inst a : B.inst a := H.subst' (.one hΓ.bvar H₀)

/-- Context conversion for the strong judgment. -/
theorem IsDefEqStrong.defeqDF_l (h2 : A::Γ ⊢ₛ e1 ≡ e2 : B) (hΓ : CtxStrong Γ)
    (h1 : Γ ⊢ₛ A ≡ A' : .sort u) : A'::Γ ⊢ₛ e1 ≡ e2 : B := by
  have W : Ctx.Subst StrongHasType (A'::Γ) .id (A::Γ) := by
    refine .cons ((Ctx.Subst.id hΓ.bvar).lift_r (fun W h => IsDefEqStrong.weak' W h) .one) ?_
    show A'::Γ ⊢ₛ .bvar 0 : A.subst (SExpr.Subst.id.lift_r (.skip .refl))
    rw [← lift'_subst, subst_id]
    exact .defeqDF (h1.symm.weak' .one) (.bvar .zero (h1.right.weak' .one))
  simpa using h2.subst' W

/-- Inversion of a strongly typed `forallE`. -/
theorem IsDefEqStrong.forallE_inv' (H : Γ ⊢ₛ e1 ≡ e2 : V)
    (eq : e1 = .forallE A B ∨ e2 = .forallE A B) :
    (∃ u, Γ ⊢ₛ A : .sort u) ∧ ∃ v, A::Γ ⊢ₛ B : .sort v := by
  induction H generalizing A B with
  | symm _ ih => exact ih eq.symm
  | trans _ _ _ _ ih1 ih2 => 
    obtain eq | eq := eq
    · exact ih1 (.inl eq)
    · exact ih2 (.inr eq)
  | trans' _ _ ih1 ih2 => 
    obtain eq | eq := eq
    · exact ih1 (.inl eq)
    · exact ih2 (.inr eq)
  | proofIrrel _ _ _ _ ih2 ih3 => 
    obtain eq | eq := eq
    · exact ih2 (.inl eq)
    · exact ih3 (.inl eq)
  | forallEDF h1 h2 h3 =>
    obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq
    · exact ⟨⟨_, h1.left⟩, _, h2.left⟩
    · exact ⟨⟨_, h1.right⟩, _, h3.right⟩
  | defeqDF _ _ _ ih2 => exact ih2 eq
  | beta _ _ _ _ _ _ _ ih4 => obtain ⟨⟨⟩⟩ | eq := eq; exact ih4 (.inl eq)
  | eta _ _ ih1 _ => obtain ⟨⟨⟩⟩ | eq := eq; exact ih1 (.inl eq)
  | extra _ _ _ _ ih3 ih4 => 
    obtain eq | eq := eq
    · exact ih3 (.inl eq)
    · exact ih4 (.inl eq)
  | _ => obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq

/-- Substitution of definitionally equal arguments into a strongly typed family. -/
theorem IsDefEqStrong.instDF (hΓ : CtxStrong Γ) (hA : Γ ⊢ₛ A : .sort u)
    (hB : A::Γ ⊢ₛ B : .sort v) (ha : Γ ⊢ₛ a ≡ a' : A) : Γ ⊢ₛ B.inst a ≡ B.inst a' : .sort v := by
  have lam : Γ ⊢ₛ .lam A B : .forallE A (.sort v) := .lamDF hA .sort hB hB
  have app : Γ ⊢ₛ .app (.lam A B) a ≡ .app (.lam A B) a' : .sort v := .appDF hA lam ha .sort
  have beta {x} (hx : Γ ⊢ₛ x : A) : Γ ⊢ₛ .app (.lam A B) x ≡ B.inst x : .sort v :=
    .beta hB hx (.appDF hA lam hx .sort) (hB.inst hΓ hx)
  exact .trans .sort (beta ha.left).symm (.trans .sort app (beta ha.right))

end

/-- **Assumptions of the abstract prototype on the environment** (needed for `IsDefEq.strong`):
the `SExpr` translations of the environment's constant types and stored rules are strongly
typed in the empty context, and every constructor's type is convertible to a telescope ending in
an application of an inductive type (a `CtorBundle`).

`Params` does not relate `env` to the `SExpr` typing judgment at all, so these cannot be
derived; for the `VExpr` theory the analogues are `VEnv.Ordered.strong` and the constructor
typing of a well-formed inductive declaration. Like `Params.PatternRegistry`, this is a
separate `Prop`-valued class because it mentions `IsDefEqStrong`, which is defined from
`Params`. -/
class Params.TypedEnv : Prop where
  const_type : env.constants c = some ci → ls.length = ci.uvars →
    ∃ u, IsDefEqStrong [] ((SExpr.mk ci.type).instL ls) ((SExpr.mk ci.type).instL ls) (.sort u)
  ctor_type (cl : CtorBundle.IsCtor c) : env.constants c = some ci → ls.length = ci.uvars →
    ∃ F : CtorBundle c cl, IsDefEqStrong [] ((SExpr.mk ci.type).instL ls) (F.rhs ls) (.sort F.u)
  defeq_type : env.defeqs df → ls.length = df.uvars →
    IsDefEqStrong [] (.instL ls (.mk df.lhs)) (.instL ls (.mk df.lhs)) (.instL ls (.mk df.type)) ∧
    IsDefEqStrong [] (.instL ls (.mk df.rhs)) (.instL ls (.mk df.rhs)) (.instL ls (.mk df.type))

section
local notation:65 Γ " ⊢ₛ " e " : " A:36 => IsDefEqStrong Γ e e A
local notation:65 Γ " ⊢ₛ " e1 " ≡ " e2 " : " A:36 => IsDefEqStrong Γ e1 e2 A
variable [Params.TypedEnv]

theorem IsDefEqStrong.const_of_env (h1 : env.constants c = some ci) (h2 : ls.length = ci.uvars) :
    Γ ⊢ₛ .const c ls : (SExpr.mk ci.type).instL ls := by
  have hcl := henv.closedC h1
  obtain ⟨u, hT⟩ := Params.TypedEnv.const_type h1 h2
  obtain ⟨ρ, hT⟩ := hT.weak0 (Γ := Γ)
  simp only [lift', closed_lift' hcl] at hT
  have ex cl : ∃ F : CtorBundle c cl, Γ ⊢ₛ (SExpr.mk ci.type).instL ls ≡ F.rhs ls : .sort F.u := by
    obtain ⟨F, hF⟩ := Params.TypedEnv.ctor_type cl h1 h2
    obtain ⟨ρ, hF⟩ := hF.weak0 (Γ := Γ)
    obtain ⟨F', hu, hr⟩ := F.lift' ls ρ
    simp only [lift'] at hF; rw [closed_lift' hcl, hr, ← hu] at hF; exact ⟨F', hF⟩
  exact .const h1 h2 hT (fun cl => Classical.choose (ex cl)) fun cl => Classical.choose_spec (ex cl)

theorem IsDefEqStrong.extra_of_env (h1 : env.defeqs df) (h2 : ls.length = df.uvars) :
    Γ ⊢ₛ .instL ls (.mk df.lhs) ≡ .instL ls (.mk df.rhs) : .instL ls (.mk df.type) := by
  have ⟨⟨hl, ht⟩, hr, _⟩ := henv.closed.2 h1
  have ⟨H1, H2⟩ := Params.TypedEnv.defeq_type h1 h2
  have ⟨_, H1⟩ := H1.weak0 (Γ := Γ); have ⟨_, H2⟩ := H2.weak0 (Γ := Γ)
  simp only [closed_lift' hl, closed_lift' hr, closed_lift' ht] at H1 H2
  exact .extra h1 h2 H1 H2

/-- `IsDefEq.strong` over a strongly well-formed context. -/
theorem IsDefEq.strong' (hΓ : CtxStrong Γ) (H : Γ ⊢ e1 ≡ e2 : A) : Γ ⊢ₛ e1 ≡ e2 : A := by
  induction H with
  | bvar h => exact hΓ.bvar h
  | symm _ ih => exact .symm (ih hΓ)
  | trans _ _ ih1 ih2 =>
    have h1 := ih1 hΓ; have ⟨_, hA⟩ := h1.isType; exact .trans hA h1 (ih2 hΓ)
  | trans' _ _ ih1 ih2 => exact .trans' (ih1 hΓ) (ih2 hΓ)
  | sort => exact .sort
  | const h1 h2 => exact .const_of_env h1 h2
  | appDF _ _ ihf iha =>
    have hf := ihf hΓ; have ha := iha hΓ
    have ⟨_, hPi⟩ := hf.isType
    have ⟨⟨_, hA⟩, _, hB⟩ := hPi.forallE_inv' (.inl rfl)
    exact .appDF hA hf ha (.instDF hΓ hA hB ha)
  | lamDF _ _ ihA ihb =>
    have hA := ihA hΓ
    have hb := ihb ⟨hΓ, _, hA.left⟩
    have ⟨_, hB⟩ := hb.isType
    exact .lamDF hA hB hb (hb.defeqDF_l hΓ hA)
  | forallEDF _ _ ihA ihb =>
    have hA := ihA hΓ
    have hb := ihb ⟨hΓ, _, hA.left⟩
    exact .forallEDF hA hb (hb.defeqDF_l hΓ hA)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 hΓ) (ih2 hΓ)
  | beta _ _ ih1 ih2 =>
    have he' := ih2 hΓ
    have ⟨_, hA⟩ := he'.isType
    have he := ih1 ⟨hΓ, _, hA⟩
    have ⟨_, hB⟩ := he.isType
    have lam := IsDefEqStrong.lamDF hA hB he he
    exact .beta he he' (.appDF hA lam he' (hB.inst hΓ he')) (he.inst hΓ he')
  | @eta Γ e A B _ ih =>
    have he := ih hΓ
    have ⟨_, hPi⟩ := he.isType
    have ⟨⟨u, hA⟩, v, hB⟩ := hPi.forallE_inv' (.inl rfl)
    have hA' : A::Γ ⊢ₛ A.lift : .sort u := hA.weak' .one
    have happ : A::Γ ⊢ₛ .app e.lift (.bvar 0) : B := by
      have := IsDefEqStrong.appDF hA' (he.weak' .one) (.bvar .zero hA')
        (by rw [inst_lift_bvar0]; exact hB)
      rwa [inst_lift_bvar0] at this
    exact .eta he (.lamDF hA hB happ happ)
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 hΓ) (ih2 hΓ) (ih3 hΓ)
  | extra h1 h2 => exact .extra_of_env h1 h2

theorem Ctx.WF.strong : ∀ {Γ}, ⊢ Γ → CtxStrong Γ
  | [], _ => trivial
  | _::_, ⟨hΓ, _, h⟩ => ⟨hΓ.strong, _, h.strong' hΓ.strong⟩

/-- The strong form of a derivation. The original statement had neither the well-formedness
hypothesis `⊢ Γ` nor the environment assumptions `Params.TypedEnv`, and is false without them
(`bvar` needs the context's types to be typed, `const`/`extra` the environment's types). -/
theorem IsDefEq.strong (hΓ : ⊢ Γ) (H : Γ ⊢ e1 ≡ e2 : A) : Γ ⊢ₛ e1 ≡ e2 : A :=
  H.strong' hΓ.strong

/-- Constructor types are telescopes into an inductive type. The original statement was for an
arbitrary `Params`, where it is false (nothing relates `classify` to the environment's types);
it now follows from the assumption `Params.TypedEnv.ctor_type`. -/
theorem _root_.Lean4Lean.Params.ctor_ty
    (hcl1 : Params.classify c = some cl) (hcl2 : cl matches .ctor .. | .etaCtor ..)
    (hci : env.constants c = some ci) (h_len : ls.length = ci.uvars) :
    ∃ (I : Name) (Ts args : List SExpr) (u : SLevel),
      Ts.length = cl.arity ∧ Params.classify I = some (.indTy args.length) ∧ u ≠ .zero ∧
      Γ ⊢ (SExpr.mk ci.type).instL ls ≡
        Ts.foldr .forallE (args.foldr (fun A acc => acc.app A) (.const I ls)) : .sort u := by
  have hc : CtorBundle.IsCtor c := ⟨cl, hcl1, by revert hcl2; cases cl <;> simp⟩
  obtain ⟨F, hF⟩ := Params.TypedEnv.ctor_type hc hci h_len
  obtain ⟨ρ, hF⟩ := hF.weak0 (Γ := Γ)
  obtain ⟨F', hu, hr⟩ := F.lift' ls ρ
  simp only [lift'] at hF; rw [closed_lift' (henv.closedC hci), hr, ← hu] at hF
  have : hc.cl.1 = cl := (Option.some.inj (hcl1.symm.trans hc.cl.2.1)).symm
  exact ⟨F'.I, F'.Ts, F'.args, F'.u, this ▸ F'.hlen, F'.hclI, F'.hu0, hF.defeq⟩

end

section
local notation:65 Γ " ⊢ₛ " e " : " A:36 => IsDefEqStrong Γ e e A
local notation:65 Γ " ⊢ₛ " e1 " ≡ " e2 " : " A:36 => IsDefEqStrong Γ e1 e2 A

theorem Ctx.SubstEq.refl_left (W : Ctx.SubstEq Γ₀ σ σ' Γ) : Ctx.SubstEq Γ₀ σ σ Γ := by
  induction W with
  | nil W => exact .nil W
  | cons _ hA h ih => exact .cons ih hA h.hasType.1

/-- Simultaneous substitution of a pair of related substitutions into a strong derivation,
with the left, right and cross projections. No assumptions are needed: the typing premises of
the strong rules supply the conversions. -/
theorem IsDefEqStrong.substEq' (W : Ctx.SubstEq Γ₀ σ σ' Γ) (H : Γ ⊢ₛ e1 ≡ e2 : A) :
    Γ₀ ⊢ e1.subst σ ≡ e1.subst σ' : A.subst σ ∧
    Γ₀ ⊢ e2.subst σ ≡ e2.subst σ' : A.subst σ ∧
    Γ₀ ⊢ e1.subst σ ≡ e2.subst σ' : A.subst σ := by
  induction H generalizing Γ₀ σ σ' with
  | bvar h => have := W.lookup h; exact ⟨this, this, this⟩
  | symm _ ih => have ⟨l, r, c⟩ := ih W; exact ⟨r, l, (r.trans c.symm).trans l⟩
  | trans _ _ _ _ ih1 ih2 =>
    have ⟨l1, _, c1⟩ := ih1 W; have ⟨l2, r2, c2⟩ := ih2 W
    exact ⟨l1, r2, c1.trans (l2.symm.trans c2)⟩
  | trans' _ _ ih1 ih2 =>
    have ⟨l1, _, c1⟩ := ih1 W; have ⟨l2, r2, c2⟩ := ih2 W
    have hC := (IsDefEq.trans' (ih1 W.refl_left).2.2 (ih2 W.refl_left).2.2).hasType.2
    exact ⟨l1, .trans' hC r2, .trans' c1 (l2.symm.trans c2)⟩
  | sort => exact ⟨.sort, .sort, .sort⟩
  | const h1 h2 =>
    rw [closed_subst (henv.closedC h1)]
    have := IsDefEq.const h1 h2 (Γ := Γ₀); exact ⟨this, this, this⟩
  | appDF _ _ _ _ _ ihf iha ihB =>
    have ⟨fl, fr, fc⟩ := ihf W; have ⟨al, ar, ac⟩ := iha W
    have hB := (ihB W.refl_left).2.2
    simp only [subst, subst_inst] at fl fr fc hB ⊢
    exact ⟨.appDF fl al, .defeqDF hB.symm (.appDF fr ar), .appDF fc ac⟩
  | lamDF hA hB _ _ ihA ihB ihb ihb' =>
    have ⟨Al, Ar, Ac⟩ := ihA W
    have ⟨bl, _, bc⟩ := ihb (W.lift hA.left)
    have ⟨_, br', _⟩ := ihb' (W.lift hA.right)
    have hAA := (ihA W.refl_left).2.2
    have hBσ := (ihB (W.refl_left.lift hA.left)).2.2
    refine ⟨.lamDF Al bl, .defeqDF (.forallEDF hAA.symm (hAA.defeqDF_l hBσ)) (.lamDF Ar br'),
      .lamDF Ac bc⟩
  | forallEDF hA _ _ ihA ihb ihb' =>
    have ⟨Al, Ar, Ac⟩ := ihA W
    have ⟨bl, _, bc⟩ := ihb (W.lift hA.left)
    have ⟨_, br', _⟩ := ihb' (W.lift hA.right)
    exact ⟨.forallEDF Al bl, .forallEDF Ar br', .forallEDF Ac bc⟩
  | defeqDF _ _ ihAB ihe =>
    have hty := (ihAB W.refl_left).2.2
    have ⟨l, r, c⟩ := ihe W
    exact ⟨.defeqDF hty l, .defeqDF hty r, .defeqDF hty c⟩
  | beta he he' _ _ _ _ ihapp ihinst =>
    have hβ := (IsDefEq.beta he.defeq he'.defeq).subst' W.left
    exact ⟨(ihapp W).1, (ihinst W).1, hβ.trans (ihinst W).1⟩
  | eta he _ ihe ihlam =>
    have hη := (IsDefEq.eta he.defeq).subst' W.left
    exact ⟨(ihlam W).1, (ihe W).1, hη.trans (ihe W).1⟩
  | proofIrrel _ _ _ ihp ihh ihh' =>
    have hh := (ihh W).1; have hh' := (ihh' W).1
    exact ⟨hh, hh', .proofIrrel (ihp W).1.hasType.1 hh.hasType.1 hh'.hasType.2⟩
  | extra h1 h2 =>
    have ⟨⟨hl, ht⟩, hr, _⟩ := henv.closed.2 h1
    simp only [closed_subst hl, closed_subst hr, closed_subst ht]
    have := IsDefEq.extra h1 h2 (Γ := Γ₀)
    exact ⟨this.hasType.1, this.hasType.2, this⟩

/-- Simultaneous substitution of a pair of related substitutions into a strong derivation. -/
theorem IsDefEqStrong.substEq (W : Ctx.SubstEq Γ₀ σ σ' Γ) (H : Γ ⊢ₛ e1 ≡ e2 : A) :
    Γ₀ ⊢ e1.subst σ ≡ e2.subst σ' : A.subst σ := (H.substEq' W).2.2

theorem Ctx.SubstEq.symm (W : Ctx.SubstEq Γ₀ σ σ' Γ) : Ctx.SubstEq Γ₀ σ' σ Γ := by
  induction W with
  | nil W => exact .nil W
  | cons W hA h ih => exact .cons ih hA (.defeqDF (hA.substEq W) h.symm)

/-- Simultaneous substitution into an `IsDefEq` derivation. The original statement had neither
the well-formedness hypothesis `⊢ Γ` nor the environment assumptions `Params.TypedEnv`; it goes
through `IsDefEq.strong`, which needs both. (For a single substitution on both sides there is
the assumption-free `IsDefEq.subst'`.) -/
theorem IsDefEq.subst [Params.TypedEnv] (hΓ : ⊢ Γ) (W : Ctx.SubstEq Γ₀ σ σ' Γ)
    (H : Γ ⊢ e1 ≡ e2 : A) : Γ₀ ⊢ e1.subst σ ≡ e2.subst σ' : A.subst σ :=
  (H.strong hΓ).substEq W

end

variable (DefEq : List SExpr → SExpr → SExpr → SExpr → Prop) in
structure WithLift (Γ : List SExpr) (e1 e2 A : SExpr) : Prop where
  defeq' {{Δ ρ e1' e2' A'}} : Ctx.Lift' ρ Δ Γ →
    e1 = .lift' e1' ρ → e2 = .lift' e2' ρ → A = .lift' A' ρ → DefEq Δ e1' e2' A'
  left' {{Δ ρ e1' A'}} : Ctx.Lift' ρ Δ Γ → e1 = .lift' e1' ρ → A = .lift' A' ρ → DefEq Δ e1' e1' A'
  right' {{Δ ρ e2' A'}} : Ctx.Lift' ρ Δ Γ → e2 = .lift' e2' ρ → A = .lift' A' ρ → DefEq Δ e2' e2' A'

def IsDefEqLift := WithLift IsDefEq
scoped notation:65 Γ " ⊢ " e " :↑ " A:36 => IsDefEqLift Γ e e A
scoped notation:65 Γ " ⊢ " e1 " ≡ " e2 " :↑ " A:36 => IsDefEqLift Γ e1 e2 A

theorem WithLift.imp
    (imp : ∀ {Γ e1 e2 A}, DefEq Γ e1 e2 A → DefEq' Γ e1 e2 A)
    (H : WithLift DefEq Γ e1 e2 A) : WithLift DefEq' Γ e1 e2 A where
  defeq' _ _ _ _ _ W' h1 h2 h3 := imp (H.defeq' W' h1 h2 h3)
  left' _ _ _ _ W' h1 hA := imp (H.left' W' h1 hA)
  right' _ _ _ _ W' h1 hA := imp (H.right' W' h1 hA)

theorem WithLift.refl
    (refl : ∀ {ρ Δ e' A'}, Ctx.Lift' ρ Δ Γ →
      e = .lift' e' ρ → A = .lift' A' ρ → DefEq Δ e' e' A')
    : WithLift DefEq Γ e e A where
  defeq' _ _ _ _ _ W := by rintro rfl he rfl; cases SExpr.lift'_inj.1 he; exact refl W rfl rfl
  left' _ _ _ _ W := by rintro rfl rfl; exact refl W rfl rfl
  right' _ _ _ _ W := by rintro rfl rfl; exact refl W rfl rfl

theorem WithLift.weak'
    (weak : ∀ {ρ Γ Δ e1 e2 A}, Ctx.Lift' ρ Γ Δ → DefEq Γ e1 e2 A →
      DefEq Δ (e1.lift' ρ) (e2.lift' ρ) (A.lift' ρ))
    (W : Ctx.Lift' ρ Γ Δ) (H : WithLift DefEq Γ e1 e2 A) :
    WithLift DefEq Δ (e1.lift' ρ) (e2.lift' ρ) (A.lift' ρ) where
  defeq' Δ' ρ' e1' e2' A' W' h1 h2 hA := by
    have ⟨Δ₀, I⟩ := Ctx.Inter.mk W W'
    obtain ⟨e1, rfl, rfl⟩ := lift_eq_lift h1
    obtain ⟨e2, rfl, rfl⟩ := lift_eq_lift h2
    obtain ⟨A, rfl, rfl⟩ := lift_eq_lift hA
    exact weak I.diff (H.defeq' I.symm.diff rfl rfl rfl)
  left' Δ' ρ' e1' A' W' h1 hA := by
    have ⟨Δ₀, I⟩ := Ctx.Inter.mk W W'
    obtain ⟨e1, rfl, rfl⟩ := lift_eq_lift h1
    obtain ⟨A, rfl, rfl⟩ := lift_eq_lift hA
    exact weak I.diff (H.left' I.symm.diff rfl rfl)
  right' Δ' ρ' e1' A' W' h1 hA := by
    have ⟨Δ₀, I⟩ := Ctx.Inter.mk W W'
    obtain ⟨e1, rfl, rfl⟩ := lift_eq_lift h1
    obtain ⟨A, rfl, rfl⟩ := lift_eq_lift hA
    exact weak I.diff (H.right' I.symm.diff rfl rfl)

theorem IsDefEqLift.weak' : Ctx.Lift' ρ Γ Δ → Γ ⊢ e1 ≡ e2 :↑ A →
    Δ ⊢ e1.lift' ρ ≡ e2.lift' ρ :↑ A.lift' ρ := WithLift.weak' IsDefEq.weak'

/-- Substitution for `IsDefEqLift`. The original statement took an arbitrary `HasType` for the
substitution, and is false (with `HasType := fun _ _ _ => True` any substitution qualifies);
it now takes an `IsDefEq`-typed substitution. It remains unproved: `IsDefEqLift` quantifies
over all ways of writing the substituted terms as weakenings, so this needs a strengthening
lemma for `IsDefEq` (from `Δ ⊢ x.lift' ρ ≡ y.lift' ρ : z.lift' ρ` to `Δ' ⊢ x ≡ y : z`), which
the prototype does not have. -/
theorem IsDefEqLift.subst : Ctx.Subst (· ⊢ · : ·) Δ σ Γ → Γ ⊢ e1 ≡ e2 :↑ A →
    Δ ⊢ e1.subst σ ≡ e2.subst σ :↑ A.subst σ := sorry

theorem WithLift.weak'_inv (W : Ctx.Lift' ρ Γ Δ)
    (H : WithLift DefEq Δ (e1.lift' ρ) (e2.lift' ρ) (A.lift' ρ)) : WithLift DefEq Γ e1 e2 A where
  defeq' Δ' ρ' _ _ _ W' := by
    rintro rfl rfl rfl
    simp only [← SExpr.lift'_comp] at H
    exact H.defeq' (W'.comp W) rfl rfl rfl
  left' Δ' ρ' _ _ W' := by
    rintro rfl rfl
    simp only [← SExpr.lift'_comp] at H
    exact H.left' (W'.comp W) rfl rfl
  right' Δ' ρ' _ _ W' := by
    rintro rfl rfl
    simp only [← SExpr.lift'_comp] at H
    exact H.right' (W'.comp W) rfl rfl

nonrec theorem IsDefEqLift.weak'_inv : Ctx.Lift' ρ Γ Δ →
    Δ ⊢ e1.lift' ρ ≡ e2.lift' ρ :↑ A.lift' ρ → Γ ⊢ e1 ≡ e2 :↑ A := .weak'_inv

theorem WithLift.symm
    (symm : ∀ {Γ e1 e2 A}, DefEq Γ e1 e2 A → DefEq Γ e2 e1 A)
    (H : WithLift DefEq Γ e1 e2 A) : WithLift DefEq Γ e2 e1 A where
  defeq' _ _ _ _ _ W' h1 h2 h3 := symm (H.defeq' W' h2 h1 h3)
  left' _ _ _ _ W' h1 hA := H.right' W' h1 hA
  right' _ _ _ _ W' h1 hA := H.left' W' h1 hA

nonrec theorem IsDefEqLift.symm : Γ ⊢ e1 ≡ e2 :↑ A → Γ ⊢ e2 ≡ e1 :↑ A := .symm .symm

theorem WithLift.left (H : WithLift DefEq Γ e1 e2 A) : WithLift DefEq Γ e1 e1 A :=
  .refl (H.left' ·)

theorem WithLift.right (H : WithLift DefEq Γ e1 e2 A) : WithLift DefEq Γ e2 e2 A :=
  .refl (H.right' ·)

theorem IsDefEqLift.left (H : Γ ⊢ e1 ≡ e2 :↑ A) : Γ ⊢ e1 :↑ A where
  defeq' _ _ _ _ _ W' := by rintro rfl he hA; exact SExpr.lift'_inj.1 he ▸ H.left' W' rfl hA
  left' := H.left'
  right' := H.left'

theorem WithLift.defeq (H : WithLift DefEq Γ e1 e2 A) : DefEq Γ e1 e2 A :=
  H.defeq' .refl SExpr.lift'_refl.symm SExpr.lift'_refl.symm SExpr.lift'_refl.symm

nonrec theorem IsDefEqLift.defeq (H : Γ ⊢ e1 ≡ e2 :↑ A) : Γ ⊢ e1 ≡ e2 : A := H.defeq

variable (Γ₀ : List SExpr) in
inductive IsDefEqCtx : List SExpr → List SExpr → Prop
  | zero : IsDefEqCtx Γ₀ Γ₀
  | succ :  IsDefEqCtx Γ₁ Γ₂ → Γ₁ ⊢ A₁ ≡ A₂ : .sort u → IsDefEqCtx (A₁ :: Γ₁) (A₂ :: Γ₂)

theorem IsDefEq.defeqDFC' (h1 : IsDefEqCtx Γ₀ Γ₁ Γ₂)
    (h2 : Δ ++ Γ₁ ⊢ e₁ ≡ e₂ : A) : Δ ++ Γ₂ ⊢ e₁ ≡ e₂ : A := by
  induction h1 generalizing e₁ e₂ A Δ with
  | zero => exact h2
  | @succ _ _ _ A₂ _ _ AA ih =>
    simpa using ih (Δ := Δ ++ [A₂]) (by simpa using AA.defeqDF_l' h2)

theorem IsDefEq.defeqDFC (h1 : IsDefEqCtx Γ₀ Γ₁ Γ₂)
    (h2 : Γ₁ ⊢ e₁ ≡ e₂ : A) : Γ₂ ⊢ e₁ ≡ e₂ : A := .defeqDFC' (Δ := []) h1 h2

scoped notation:65 Γ " ⊢ " e1 " ⤳ " e2:36 => WHRed Γ e1 e2
inductive WHRed (Γ : List SExpr) : SExpr → SExpr → Prop where
  | app : Γ ⊢ f ⤳ f' → Γ ⊢ .app f a ⤳ .app f' a
  | beta : Γ ⊢ .app (.lam A e) a ⤳ e.inst a
  | extra : Pat p r → p.MatchesS e m1 m2 → (dfs : List _).map (·.2) = r.2.defeqsS m1 m2 →
    (∀ a b A, (A, a, b) ∈ dfs → Γ ⊢ a ≡ b : A) → Γ ⊢ e ⤳ r.1.applyS m1 m2

theorem _root_.Lean4Lean.Pattern.MatchesS.map {F : SExpr → SExpr} {p : Pattern} {e m1 m2}
    (happ : ∀ f a, F (.app f a) = .app (F f) (F a)) (hc : ∀ c ls, F (.const c ls) = .const c ls)
    (H : p.MatchesS e m1 m2) : p.MatchesS (F e) m1 (F ∘ m2) := by
  induction H with
  | @const c ls =>
    have : (F ∘ (nofun : Pattern.Path (.const c) → SExpr)) = nofun := funext fun x => nomatch x
    rw [hc, this]; exact .const
  | @var _ _ _ _ a' _ ih =>
    rw [happ]; refine cast ?_ (ih.var (a' := F a')); congr 1; funext x; cases x <;> rfl
  | app _ _ ih1 ih2 =>
    rw [happ]; refine cast ?_ (ih1.app ih2); congr 1; funext x; cases x <;> rfl

theorem _root_.Lean4Lean.Pattern.MatchesS.determ {p : Pattern} {e m1 m2 m1' m2'}
    (h1 : p.MatchesS e m1 m2) (h2 : p.MatchesS e m1' m2') : m1 = m1' ∧ m2 = m2' := by
  induction h1 generalizing m1' with
  | const => let .const := h2; simp
  | app l1 l2 ih1 ih2 => let .app r1 r2 := h2; simp [ih1 r1, ih2 r2]; rfl
  | var l1 ih1 => let .var r1 := h2; simp [ih1 r1]

theorem _root_.Lean4Lean.Pattern.MatchesS.inter {p q : Pattern} {e m1 m2 m3 m4}
    (hp : p.MatchesS e m1 m2) (hq : q.MatchesS e m3 m4) :
    ∃ r m1 m2, p.inter q = some r ∧ r.MatchesS e m1 m2 := by
  induction hp generalizing q m3 m4 <;> cases hq <;> simp [Pattern.inter]
  · case const.const => exact ⟨_, _, .const⟩
  · case var.var ih _ _ ih' =>
    have ⟨rf, mf1, mf2, hf1, hf2⟩ := ih ih'
    exact ⟨_, ⟨_, hf1, rfl⟩, _, _, .var hf2⟩
  · case var.app ihf _ _ _ _ _ ha2 ihf' =>
    have ⟨rf, mf1, mf2, hf1, hf2⟩ := ihf ihf'
    exact ⟨_, ⟨_, hf1, rfl⟩, _, _, .app hf2 ha2⟩
  · case app.var ha2 ihf _ _ _ ihf' =>
    have ⟨rf, mf1, mf2, hf1, hf2⟩ := ihf ihf'
    exact ⟨_, ⟨_, hf1, rfl⟩, _, _, .app hf2 ha2⟩
  · case app.app ihf iha _ _ _ _ _ iha' ihf' =>
    have ⟨rf, mf1, mf2, hf1, hf2⟩ := ihf ihf'
    have ⟨ra, ma1, ma2, ha1, ha2⟩ := iha iha'
    exact ⟨_, ⟨_, hf1, _, ha1, rfl⟩, _, _, .app hf2 ha2⟩

theorem _root_.Lean4Lean.Pattern.RHS.applyS_map {F : SExpr → SExpr} {p : Pattern} {m1 m2}
    (happ : ∀ f a, F (.app f a) = .app (F f) (F a))
    (hfix : ∀ c : VExpr, c.Closed → F (.instL m1 (.mk c)) = .instL m1 (.mk c)) (r : p.RHS) :
    F (r.applyS m1 m2) = r.applyS m1 (F ∘ m2) := by
  induction r with
  | fixed c h => exact hfix c h
  | var => rfl
  | app f a ih1 ih2 => simp only [Pattern.RHS.applyS, happ, ih1, ih2]

theorem _root_.Lean4Lean.Pattern.Check.defeqsS_map {F : SExpr → SExpr} {p : Pattern} {m1 m2}
    (happ : ∀ f a, F (.app f a) = .app (F f) (F a))
    (hfix : ∀ c : VExpr, c.Closed → F (.instL m1 (.mk c)) = .instL m1 (.mk c)) (ck : p.Check) :
    (ck.defeqsS m1 m2).map (fun x => (F x.1, F x.2)) = ck.defeqsS m1 (F ∘ m2) := by
  induction ck with
  | true => rfl
  | defeq a b rest ih =>
    simp only [Pattern.Check.defeqsS, List.map_cons, ih,
      Pattern.RHS.applyS_map happ hfix]
  | nonzero _ rest ih => exact ih

/-- Transport of the checks of a pattern step along a map `F` of expressions that commutes
with application and fixes closed constants (lifting or substitution), given that `F` maps
the defeq judgments of `Γ` to those of `Δ`. -/
theorem Pattern.Check.checks_map {F G : SExpr → SExpr} {p : Pattern} {ck : p.Check} {m1 m2}
    (happ : ∀ f a, F (.app f a) = .app (F f) (F a))
    (hfix : ∀ c : VExpr, c.Closed → ∀ ls, F (.instL ls (.mk c)) = .instL ls (.mk c))
    (hdf : ∀ {a b A}, Γ ⊢ a ≡ b : A → Δ ⊢ F a ≡ F b : G A)
    (h3 : (dfs : List _).map (·.2) = ck.defeqsS m1 m2)
    (h4 : ∀ a b A, (A, a, b) ∈ dfs → Γ ⊢ a ≡ b : A) :
    ∃ dfs' : List _, dfs'.map (·.2) = ck.defeqsS m1 (F ∘ m2) ∧
      ∀ a b A, (A, a, b) ∈ dfs' → Δ ⊢ a ≡ b : A := by
  refine ⟨dfs.map fun x => (G x.1, F x.2.1, F x.2.2), ?_, ?_⟩
  · rw [← Pattern.Check.defeqsS_map happ (hfix · · m1), ← h3, List.map_map, List.map_map]; rfl
  · intro a b A hm
    obtain ⟨⟨A', a', b'⟩, hm', eq⟩ := List.mem_map.1 hm
    cases eq; exact hdf (h4 _ _ _ hm')

/-- Transport of a pattern step along a map `F` as in `Pattern.Check.checks_map`. -/
theorem WHRed.extra_map {F G : SExpr → SExpr}
    (happ : ∀ f a, F (.app f a) = .app (F f) (F a)) (hc : ∀ c ls, F (.const c ls) = .const c ls)
    (hfix : ∀ c : VExpr, c.Closed → ∀ ls, F (.instL ls (.mk c)) = .instL ls (.mk c))
    (hdf : ∀ {a b A}, Γ ⊢ a ≡ b : A → Δ ⊢ F a ≡ F b : G A)
    (h1 : Pat p r) (h2 : p.MatchesS e m1 m2) (h3 : (dfs : List _).map (·.2) = r.2.defeqsS m1 m2)
    (h4 : ∀ a b A, (A, a, b) ∈ dfs → Γ ⊢ a ≡ b : A) :
    Δ ⊢ F e ⤳ F (r.1.applyS m1 m2) := by
  rw [Pattern.RHS.applyS_map happ (hfix · · m1)]
  have ⟨_, h3', h4'⟩ := Pattern.Check.checks_map happ hfix hdf h3 h4
  exact .extra h1 (h2.map happ hc) h3' h4'

/-- Substitution into a weak-head step. The original statement took an arbitrary `HasType` for
the substitution and is false for checked patterns (the substituted checks need not hold); it
needs an `IsDefEq`-typed substitution. -/
theorem WHRed.subst (W : Ctx.Subst (· ⊢ · : ·) Δ σ Γ) :
    Γ ⊢ e1 ⤳ e2 → Δ ⊢ e1.subst σ ⤳ e2.subst σ
  | .app h1 => .app (h1.subst W)
  | .beta => subst_inst ▸ .beta
  | .extra h1 h2 h3 h4 =>
    WHRed.extra_map (F := (·.subst σ)) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ h _ => h.mkS.instL.subst_eq .zero) (·.subst' W) h1 h2 h3 h4

theorem WHRed.weak' (W : Ctx.Lift' ρ Γ Γ') :
    Γ ⊢ e1 ⤳ e2 → Γ' ⊢ e1.lift' ρ ⤳ e2.lift' ρ
  | .app h1 => .app (h1.weak' W)
  | .beta => by rw [SExpr.lift'_inst_hi]; exact .beta
  | .extra h1 h2 h3 h4 =>
    WHRed.extra_map (F := (·.lift' ρ)) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ h _ => h.mkS.instL.lift'_eq .zero) (·.weak' W) h1 h2 h3 h4

/-- Inversion of a weak-head step out of a weakened term. The `extra` (pattern step) case is
unproved: the checks of the step hold in the larger context `Γ'` and are needed in `Γ`, which
is a strengthening property of `IsDefEq` that the prototype does not have. -/
theorem WHRed.weakU_inv (W : Ctx.Lift' ρ Γ Γ') (H : Γ' ⊢ e1.lift' ρ ⤳ e2') :
    ∃ e2, e2' = e2.lift' ρ ∧ Γ ⊢ e1 ⤳ e2 := by
  generalize he : e1.lift' ρ = e1' at H
  induction H generalizing e1 with
  | app h1 ih => let .app .. := e1; cases he; obtain ⟨_, rfl, a1⟩ := ih rfl; exact ⟨_, rfl, .app a1⟩
  | beta =>
    let .app e1 _ := e1; let .lam .. := e1; cases he
    simp [← SExpr.lift'_inst_hi, SExpr.lift'_inj]; exact .beta
  | extra => sorry

def WHNF (Γ : List SExpr) (e : SExpr) := ∀ e', ¬Γ ⊢ e ⤳ e'

theorem WHNF.lam : WHNF Γ (.lam A e) := nofun
theorem WHNF.sort : WHNF Γ (.sort A) := nofun
theorem WHNF.forallE : WHNF Γ (.forallE A B) := nofun

/-- A term matching a proper subpattern of a registered pattern is weak-head normal. -/
theorem WHNF.subpattern (h1 : Pat p r) (h2 : Subpattern q p) (h3 : q ≠ p)
    (h4 : q.MatchesS e m1 m2) : WHNF Γ e := by
  intro e' H
  induction H generalizing q m1 m2 with
  | app _ ih =>
    cases h4 with
    | var h4 =>
      refine ih (.trans (.varL .refl) h2) ?_ h4
      rintro rfl; cases h2.antisymm (.varL .refl)
    | app h4 _ =>
      refine ih (.trans (.appL .refl) h2) ?_ h4
      rintro rfl; cases h2.antisymm (.appL .refl)
  | beta => cases h4 with | var h => nomatch h | app h _ => nomatch h
  | extra r1 r2 =>
    have ⟨_, _, _, a1, _⟩ := r2.inter h4
    have h := pat_uniq h1 r1 h2 a1
    exact h3 (h.2.1.symm.trans h.1.symm)

theorem WHRed.determ (H1 : Γ ⊢ e ⤳ e₁) (H2 : Γ ⊢ e ⤳ e₂) : e₁ = e₂ := by
  induction H1 generalizing e₂ with
  | app l1 ih =>
    cases H2 with
    | app r1 => cases ih r1; rfl
    | beta => cases WHNF.lam _ l1
    | extra r1 r2 =>
      cases r2 with
      | var r3 => cases WHNF.subpattern r1 (.varL .refl) (by intro h; cases h) r3 _ l1
      | app r3 _ => cases WHNF.subpattern r1 (.appL .refl) (by intro h; cases h) r3 _ l1
  | beta =>
    cases H2 with
    | app r1 => cases WHNF.lam _ r1
    | beta => rfl
    | extra _ r2 => cases r2 with | var h => nomatch h | app h _ => nomatch h
  | extra l1 l2 =>
    cases H2 with
    | beta => cases l2 with | var h => nomatch h | app h _ => nomatch h
    | app r1 =>
      cases l2 with
      | var l3 => cases WHNF.subpattern l1 (.varL .refl) (by intro h; cases h) l3 _ r1
      | app l3 _ => cases WHNF.subpattern l1 (.appL .refl) (by intro h; cases h) l3 _ r1
    | extra r1 r2 =>
      have ⟨_, _, _, a1, _⟩ := r2.inter l2
      obtain ⟨rfl, -, ⟨⟩⟩ := pat_uniq l1 r1 .refl a1
      obtain ⟨rfl, rfl⟩ := l2.determ r2; rfl

def WHRedS (Γ : List SExpr) : SExpr → SExpr → Prop := ReflTransGen (WHRed Γ)
scoped notation:65 Γ " ⊢ " e1 " ⤳* " e2:36 => WHRedS Γ e1 e2

theorem WHRedS.subst (W : Ctx.Subst (· ⊢ · : ·) Δ σ Γ) (H : Γ ⊢ e1 ⤳* e2) :
    Δ ⊢ e1.subst σ ⤳* e2.subst σ := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.subst W)

/-- Soundness of weak-head reduction. Unproved, and not provable from the current `Params`:
pattern steps (`WHRed.extra`) range over the whole registry `Pat`, but `Params` only says that
every stored rule is an instance of a pattern (`Params.PatternRegistry`), not that every
registered pattern step is a valid `IsDefEq` (that was the commented-out `pat_wf` field); a
registry with a pattern rewriting `c` to an unrelated `d` makes it false [not formalized].
The beta case also needs typing inversion for applications and abstractions, i.e. the
validity theory behind `IsDefEq.strong`. -/
theorem WHRedS.defeq (H : Γ ⊢ e1 ⤳* e2) (he : Γ ⊢ e1 : A) : Γ ⊢ e1 ≡ e2 : A := sorry

theorem WHRedS.weak' (W : Ctx.Lift' ρ Γ Δ) (H : Γ ⊢ e1 ⤳* e2) :
    Δ ⊢ e1.lift' ρ ⤳* e2.lift' ρ := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.weak' W)

theorem WHRedS.app (H : Γ ⊢ e1 ⤳* e2) : Γ ⊢ e1.app a ⤳* e2.app a := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih h2.app

theorem WHRedS.weakU_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e1.lift' ρ ⤳* e2') :
    ∃ e2, e2' = e2.lift' ρ ∧ Γ ⊢ e1 ⤳* e2 := by
  induction H with
  | rfl => exact ⟨_, rfl, .rfl⟩
  | tail _ h2 ih =>
    obtain ⟨_, rfl, a1⟩ := ih
    obtain ⟨_, rfl, a2⟩ := h2.weakU_inv W
    exact ⟨_, rfl, .tail a1 a2⟩

theorem WHRedS.determ_l (H1 : Γ ⊢ e ⤳* e₁) (H2 : Γ ⊢ e ⤳* e₂) (W2 : WHNF Γ e₂) : Γ ⊢ e₁ ⤳* e₂ := by
  induction H1 using ReflTransGen.headIndOn generalizing e₂ with
  | rfl => exact H2
  | head l1 l2 ih =>
    cases H2 using ReflTransGen.headIndOn with
    | rfl => cases W2 _ l1
    | head r1 r2 => cases l1.determ r1; exact ih r2 W2

theorem WHNF.whRedS (W : WHNF Γ e) (H : Γ ⊢ e ⤳* e') : e = e' := by
  cases H using ReflTransGen.headIndOn with
  | rfl => rfl
  | head h1 => cases W _ h1

theorem WHRedS.determ
    (H1 : Γ ⊢ e ⤳* e₁) (W1 : WHNF Γ e₁)
    (H2 : Γ ⊢ e ⤳* e₂) (W2 : WHNF Γ e₂) : e₁ = e₂ := W1.whRedS (H1.determ_l H2 W2)

scoped notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
inductive ParRed : List SExpr → SExpr → SExpr → Prop where
  | bvar : Γ ⊢ .bvar i ≫ .bvar i
  | sort : Γ ⊢ .sort u ≫ .sort u
  | const : Γ ⊢ .const c ls ≫ .const c ls
  | app : Γ ⊢ f ≫ f' → Γ ⊢ a ≫ a' → Γ ⊢ .app f a ≫ .app f' a'
  | lam : Γ ⊢ A ≫ A' → A::Γ ⊢ body ≫ body' → Γ ⊢ .lam A body ≫ .lam A' body'
  | forallE : Γ ⊢ A ≫ A' → A::Γ ⊢ B ≫ B' → Γ ⊢ .forallE A B ≫ .forallE A' B'
  | beta : A::Γ ⊢ e₁ ≫ e₁' → Γ ⊢ e₂ ≫ e₂' → Γ ⊢ .app (.lam A e₁) e₂ ≫ e₁'.inst e₂'
  | extra : Pat p r → p.MatchesS e m1 m2 → (dfs : List _).map (·.2) = r.2.defeqsS m1 m2 →
    (∀ a b A, (A, a, b) ∈ dfs → Γ ⊢ a ≡ b : A) →
    (∀ a, Γ ⊢ m2 a ≫ m2' a) → Γ ⊢ e ≫ r.1.applyS m1 m2'

theorem ParRed.weak' (W : Ctx.Lift' ρ Γ Γ') :
    Γ ⊢ e1 ≫ e2 → Γ' ⊢ e1.lift' ρ ≫ e2.lift' ρ
  | .bvar => .bvar
  | .sort => .sort
  | .const => .const
  | .app h1 h2 => .app (h1.weak' W) (h2.weak' W)
  | .lam h1 h2 => .lam (h1.weak' W) (h2.weak' W.cons)
  | .forallE h1 h2 => .forallE (h1.weak' W) (h2.weak' W.cons)
  | .beta h1 h2 => by rw [SExpr.lift'_inst_hi]; exact (h1.weak' W.cons).beta (h2.weak' W)
  | .extra h1 h2 h3 h4 h5 => by
    rw [Pattern.RHS.applyS_map (F := (·.lift' ρ)) (fun _ _ => rfl)
      (fun _ h => h.mkS.instL.lift'_eq .zero)]
    have ⟨_, h3', h4'⟩ := Pattern.Check.checks_map (F := (·.lift' ρ)) (fun _ _ => rfl)
      (fun _ h _ => h.mkS.instL.lift'_eq .zero) (·.weak' W) h3 h4
    exact .extra h1 (h2.map (F := (·.lift' ρ)) (fun _ _ => rfl) (fun _ _ => rfl)) h3' h4'
      fun a => (h5 a).weak' W

theorem ParRed.refl : ∀ {e Γ}, Γ ⊢ e ≫ e
  | .bvar _, _ => .bvar
  | .sort _, _ => .sort
  | .const .., _ => .const
  | .app .., _ => .app .refl .refl
  | .lam .., _ => .lam .refl .refl
  | .forallE .., _ => .forallE .refl .refl

theorem WHRed.parRed : Γ ⊢ e ⤳ e' → Γ ⊢ e ≫ e'
  | .app h => .app h.parRed .refl
  | .beta => .beta .refl .refl
  | .extra h1 h2 h3 h4 => .extra h1 h2 h3 h4 fun _ => .refl

def ParRedS (Γ : List SExpr) : SExpr → SExpr → Prop := ReflTransGen (ParRed Γ)
scoped notation:65 Γ " ⊢ " e1 " ≫* " e2:36 => ParRedS Γ e1 e2

theorem ParRedS.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ≫* e2) :
    Γ' ⊢ e1.lift' ρ ≫* e2.lift' ρ := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.weak' W)

scoped notation:65 Γ " ⊢ " e1 " ▷ " e2:36 => InferType Γ e1 e2
inductive InferType : List SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ .bvar i ▷ A
  | sort : Γ ⊢ .sort u ▷ .sort (.succ u)
  | const : env.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ .const c ls ▷ (SExpr.mk ci.type).instL ls
  | app : Γ ⊢ f ▷ F → Γ ⊢ F ⤳* .forallE A B → Γ ⊢ a :↑ A → Γ ⊢ .app f a ▷ B.inst a
  | lam : Γ ⊢ A :↑ .sort u → A::Γ ⊢ body ▷ B → Γ ⊢ .lam A body ▷ .forallE A B
  | forallE : Γ ⊢ A ▷ U → Γ ⊢ U ⤳* .sort u →
    A::Γ ⊢ B ▷ V → A::Γ ⊢ V ⤳* .sort v → Γ ⊢ .forallE A B ▷ .sort (.imax u v)

/-- Soundness of type inference. Unproved: the `app` and `forallE` cases go through
`WHRedS.defeq` (see there), the `app` case also needs validity (`IsDefEq.strong`). -/
theorem InferType.hasType (H : Γ ⊢ e ▷ A) : Γ ⊢ e : A := sorry

theorem InferType.determ (H1 : Γ ⊢ e ▷ A) (H2 : Γ ⊢ e ▷ A') : A = A' := by
  induction H1 generalizing A' with
  | bvar h1 => cases H2 with | bvar h2 => exact h1.determ h2
  | sort => cases H2; rfl
  | const l1 l2 => cases H2 with | const r1 r2 => cases l1.symm.trans r1; rfl
  | app l1 l2 _ ih =>
    cases H2 with | app r1 r2 => cases ih r1; cases l2.determ .forallE r2 .forallE; rfl
  | lam _ l2 ih => cases H2 with | lam _ r2 => cases ih r2; rfl
  | forallE l1 l2 l3 l4 ih1 ih2 =>
    cases H2 with | forallE r1 r2 r3 r4
    cases ih1 r1; cases l2.determ .sort r2 .sort
    cases ih2 r3; cases l4.determ .sort r4 .sort; rfl

theorem InferType.weak' (W : Ctx.Lift' ρ Γ Δ) : Γ ⊢ e ▷ A → Δ ⊢ e.lift' ρ ▷ A.lift' ρ
  | .bvar h => .bvar (h.weak' W)
  | .sort => .sort
  | .const h1 h2 => by rw [(henv.closedC h1).mkS.instL.lift'_eq .zero]; exact .const h1 h2
  | .app h1 h2 h3 => SExpr.lift'_inst_hi .. ▸ .app (h1.weak' W) (h2.weak' W) (h3.weak' W)
  | .lam h1 h2 => .lam (h1.weak' W) (h2.weak' W.cons)
  | .forallE h1 h2 h3 h4 => .forallE (h1.weak' W) (h2.weak' W) (h3.weak' W.cons) (h4.weak' W.cons)

theorem InferType.weakU_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e.lift' ρ ▷ A') :
    ∃ A, A' = A.lift' ρ ∧ Γ ⊢ e ▷ A := by
  generalize he : e.lift' ρ = e' at H
  induction H generalizing Γ ρ e with
  | bvar h => let .bvar _ := e; cases he; let ⟨_, h1, h2⟩ := h.weakU_inv W; exact ⟨_, h1, .bvar h2⟩
  | sort => let .sort _ := e; cases he; exact ⟨_, rfl, .sort⟩
  | const h1 h2 =>
    let .const .. := e; cases he
    exact ⟨_, ((henv.closedC h1).mkS.instL.lift'_eq .zero).symm, .const h1 h2⟩
  | app h1 h2 h3 ih =>
    let .app .. := e; cases he
    obtain ⟨_, rfl, a1⟩ := ih W rfl
    obtain ⟨F, a2, a3⟩ := h2.weakU_inv W; cases F <;> cases a2
    refine ⟨_, by rw [SExpr.lift'_inst_hi], .app a1 a3 (h3.weak'_inv W)⟩
  | lam h1 h2 ih =>
    let .lam .. := e; cases he
    obtain ⟨_, rfl, a2⟩ := ih W.cons rfl
    exact ⟨_, rfl, .lam (h1.weak'_inv W) a2⟩
  | forallE h1 h2 h3 h4 ih1 ih2 =>
    let .forallE .. := e; cases he
    obtain ⟨_, rfl, a1⟩ := ih1 W rfl
    obtain ⟨U, a2, a3⟩ := h2.weakU_inv W; cases U <;> cases a2
    obtain ⟨_, rfl, b1⟩ := ih2 W.cons rfl
    obtain ⟨V, b2, b3⟩ := h4.weakU_inv W.cons; cases V <;> cases b2
    exact ⟨_, rfl, .forallE a1 a3 b1 b3⟩

theorem InferType.weak'_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e.lift' ρ ▷ A.lift' ρ) : Γ ⊢ e ▷ A := by
  obtain ⟨_, h1, h2⟩ := H.weakU_inv W
  exact SExpr.lift'_inj.1 h1 ▸ h2

/-- Substitution into type inference. Besides the `InferType`-typed substitution `W`, the
weak-head reductions in the derivation need the substitution to be `IsDefEq`-typed (`W'`), for
the checks of pattern steps (see `WHRed.subst`). -/
theorem InferType.subst (W : Ctx.Subst InferType Δ σ Γ) (W' : Ctx.Subst (· ⊢ · : ·) Δ σ Γ)
    (H : Γ ⊢ e ▷ A) : Δ ⊢ e.subst σ ▷ A.subst σ := by
  induction H generalizing Δ σ with
  | @bvar Γ i A h =>
    clear W'; simp [SExpr.subst]
    induction W generalizing i A with | nil | @cons Γ σ B W h' ih <;> cases h
    case zero => rw [SExpr.lift, SExpr.subst_lift']; exact h'
    case succ i C h => rw [SExpr.lift, SExpr.subst_lift']; exact ih h
  | sort => exact .sort
  | const h1 h2 =>
    rw [(henv.closedC h1).mkS.instL.subst_eq .zero]
    exact .const h1 h2
  | app h1 h2 h3 ih => exact subst_inst ▸ .app (ih W W') (h2.subst W') (h3.subst W')
  | lam h1 h2 ih =>
    exact .lam (h1.subst W') (ih (W.lift .bvar fun W h => h.weak' W) W'.liftD)
  | forallE h1 h2 h3 h4 ih1 ih2 =>
    exact .forallE (ih1 W W') (h2.subst W') (ih2 (W.lift .bvar fun W h => h.weak' W) W'.liftD)
      (h4.subst W'.liftD)

theorem InferType.inst (H₀ : Γ ⊢ a ▷ A₀) (H₀' : Γ ⊢ a : A₀) (H : A₀::Γ ⊢ e ▷ A) :
    Γ ⊢ e.inst a ▷ A.inst a := .subst (.one .bvar H₀) (.one .bvar H₀') H

def InferTypeS (Γ : List SExpr) (e A : SExpr) := ∃ A', Γ ⊢ e ▷ A' ∧ Γ ⊢ A' ⤳* A
scoped notation:65 Γ " ⊢ " e1 " ▷* " e2:36 => InferTypeS Γ e1 e2

/-- Unproved: needs `InferType.hasType` and `WHRedS.defeq` at the inferred type. -/
theorem InferTypeS.hasType : Γ ⊢ e ▷* A → Γ ⊢ e : A := sorry

theorem WHRedS.inferType
    (H1 : Γ ⊢ e ⤳* e₁) (W1 : WHNF Γ e₁)
    (H2 : Γ ⊢ e ⤳* e₂) (W2 : WHNF Γ e₂) : e₁ = e₂ := by
  induction H1 using ReflTransGen.headIndOn generalizing e₂ with
  | rfl =>
    cases H2 using ReflTransGen.headIndOn with
    | rfl => rfl
    | head r1 => cases W1 _ r1
  | head l1 l2 ih =>
    cases H2 using ReflTransGen.headIndOn with
    | rfl => cases W2 _ l1
    | head r1 r2 => cases l1.determ r1; exact ih r2 W2

theorem WHRedS.parRedS (H : Γ ⊢ e ⤳* e') : Γ ⊢ e ≫* e' := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih h2.parRed

theorem InferTypeS.determ
    (H1 : Γ ⊢ e ▷* A) (W1 : WHNF Γ A)
    (H2 : Γ ⊢ e ▷* A') (W2 : WHNF Γ A') : A = A' := by
  let ⟨_, h1, h2⟩ := H1; let ⟨_, h3, h4⟩ := H2
  cases h1.determ h3; exact h2.determ W1 h4 W2

theorem InferTypeS.weak' (W : Ctx.Lift' ρ Γ Δ) : Γ ⊢ e ▷* A → Δ ⊢ e.lift' ρ ▷* A.lift' ρ
  | ⟨_, h1, h2⟩ => ⟨_, h1.weak' W, h2.weak' W⟩

theorem InferTypeS.weakU_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e.lift' ρ ▷* A') :
    ∃ A, A' = A.lift' ρ ∧ Γ ⊢ e ▷* A := by
  let ⟨_, h1, h2⟩ := H
  obtain ⟨_, rfl, a1⟩ := h1.weakU_inv W
  obtain ⟨_, rfl, a2⟩ := h2.weakU_inv W
  exact ⟨_, rfl, _, a1, a2⟩

scoped notation:65 Γ " ⊢ " e1 " ≡ₚ " e2 " : " A:36 => NormalEq Γ e1 e2 A
inductive NormalEq : List SExpr → SExpr → SExpr → SExpr → Prop where
  | refl : Γ ⊢ e : A → Γ ⊢ e ≡ₚ e : A
  | appDF : Γ ⊢ f₁ ≡ₚ f₂ : .forallE A B → Γ ⊢ a₁ ≡ₚ a₂ : A →
    Γ ⊢ .app f₁ a₁ ≡ₚ .app f₂ a₂ : B.inst a₁
  | lamDF : Γ ⊢ A₁ ≡ A : .sort u → Γ ⊢ A₂ ≡ A : .sort u → A::Γ ⊢ B : .sort v →
    A::Γ ⊢ body₁ ≡ₚ body₂ : B → Γ ⊢ .lam A₁ body₁ ≡ₚ .lam A₂ body₂ : .forallE A B
  | forallEDF : Γ ⊢ A₁ ≡ A : .sort u → Γ ⊢ A₂ ≡ A : .sort u →
    Γ ⊢ A₁ ≡ₚ A₂ : .sort u → A::Γ ⊢ B₁ ≡ₚ B₂ : .sort v →
    Γ ⊢ .forallE A₁ B₁ ≡ₚ .forallE A₂ B₂ : .sort (.imax u v)
  | etaL : Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v → Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ e ≡ₚ .app e'.lift (.bvar 0) : B → Γ ⊢ .lam A e ≡ₚ e' : .forallE A B
  | etaR : Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v → Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ .app e'.lift (.bvar 0) ≡ₚ e : B → Γ ⊢ e' ≡ₚ .lam A e : .forallE A B
  | proofIrrel : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ₚ h' : p
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ₚ e2 : A → Γ ⊢ e1 ≡ₚ e2 : B

theorem NormalEq.defeqDFC (W : IsDefEqCtx Γ₀ Γ₁ Γ₂)
    (H : Γ₁ ⊢ e1 ≡ₚ e2 : A) : Γ₂ ⊢ e1 ≡ₚ e2 : A := by
  induction H generalizing Γ₂ with
  | refl h => refine .refl (h.defeqDFC W)
  | appDF h1 h2 ih1 ih2 => exact .appDF (ih1 W) (ih2 W)
  | lamDF h1 h2 h3 _ ih2 =>
    exact .lamDF (h1.defeqDFC W) (h2.defeqDFC W)
      (h3.defeqDFC (W.succ h1.hasType.2)) (ih2 (W.succ h1.hasType.2))
  | forallEDF h1 h2 _ _ ih1 ih2 =>
    exact .forallEDF (h1.defeqDFC W) (h2.defeqDFC W) (ih1 W) (ih2 (W.succ h1.hasType.2))
  | etaL h1 h2 h3 _ ih =>
    exact .etaL (h1.defeqDFC W) (h2.defeqDFC (W.succ h1)) (h3.defeqDFC W) (ih (W.succ h1))
  | etaR h1 h2 h3 _ ih =>
    exact .etaR (h1.defeqDFC W) (h2.defeqDFC (W.succ h1)) (h3.defeqDFC W) (ih (W.succ h1))
  | proofIrrel h1 h2 h3 => exact .proofIrrel (h1.defeqDFC W) (h2.defeqDFC W) (h3.defeqDFC W)
  | defeqDF h1 _ ih => exact .defeqDF (h1.defeqDFC W) (ih W)

theorem NormalEq.defeq (H : Γ ⊢ e1 ≡ₚ e2 : A) : Γ ⊢ e1 ≡ e2 : A := by
  induction H with
  | refl h => exact h
  | appDF h1 h2 ih1 ih2 => exact .appDF ih1 ih2
  | lamDF hA₁ hA₂ hB _ ihB =>
    exact have W := .succ .zero hA₁.symm
      .defeqDF (.forallEDF hA₁ (hB.defeqDFC W)) (.lamDF (hA₁.trans hA₂.symm) (ihB.defeqDFC W))
  | forallEDF hA₁ hA₂ _ _ ihA ihB =>
    exact .forallEDF (hA₁.trans hA₂.symm) (ihB.defeqDFC (.succ .zero hA₁.symm))
  | etaL hA _ h1 _ ih => exact .trans (.lamDF hA ih) (.eta h1)
  | etaR hA _ h1 _ ih => exact .trans (.symm (.eta h1)) (.lamDF hA ih)
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h2 h3
  | defeqDF h1 _ ih => exact .defeqDF h1 ih

/-- Symmetry of `NormalEq`. The `appDF` case is unproved: it must convert from `B.inst a₂` to
`B.inst a₁`, which needs the codomain `B` to be typed (validity, `IsDefEq.strong`) and a
substitution of definitionally equal arguments (`IsDefEq.subst`). -/
theorem NormalEq.symm (H : Γ ⊢ e1 ≡ₚ e2 : A) : Γ ⊢ e2 ≡ₚ e1 : A := by
  induction H with
  | refl h => exact .refl h
  | appDF h1 h2 ih1 ih2 => exact .defeqDF sorry (u := sorry) <| .appDF ih1 ih2
  | lamDF h1 h2 h3 _ ih2 => exact .lamDF h2 h1 h3 ih2
  | forallEDF h1 h2 _ _ ih1 ih2 => exact .forallEDF h2 h1 ih1 ih2
  | etaL h1 h2 h3 _ ih => exact .etaR h1 h2 h3 ih
  | etaR h1 h2 h3 _ ih => exact .etaL h1 h2 h3 ih
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h3 h2
  | defeqDF h1 _ ih => exact .defeqDF h1 ih

theorem NormalEq.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ≡ₚ e2 : A) :
    Γ' ⊢ e1.lift' ρ ≡ₚ e2.lift' ρ : A.lift' ρ := by
  induction H generalizing Γ' ρ with
  | refl h => exact .refl (h.weak' W)
  | appDF h1 h2 ih1 ih2 => exact SExpr.lift'_inst_hi .. ▸ .appDF (ih1 W) (ih2 W)
  | lamDF h1 h2 h3 _ ih2 => exact .lamDF (h1.weak' W) (h2.weak' W) (h3.weak' W.cons) (ih2 W.cons)
  | forallEDF h1 h2 _ _ ih1 ih2 => exact .forallEDF (h1.weak' W) (h2.weak' W) (ih1 W) (ih2 W.cons)
  | etaL h1 h2 h3 _ ih =>
    refine .etaL (h1.weak' W) (h2.weak' W.cons) (h3.weak' W) ?_
    simpa [← SExpr.lift'_comp] using ih W.cons
  | etaR h1 h2 h3 _ ih =>
    refine .etaR (h1.weak' W) (h2.weak' W.cons) (h3.weak' W) ?_
    simpa [← SExpr.lift'_comp] using ih W.cons
  | proofIrrel h1 h2 h3 => exact .proofIrrel (h1.weak' W) (h2.weak' W) (h3.weak' W)
  | defeqDF h1 _ ih => exact .defeqDF (h1.weak' W) (ih W)

def CRDefEq (Γ : List SExpr) (e₁ e₂ A : SExpr) : Prop :=
  Γ ⊢ e₁ ≡ e₂ : A ∧
  ∃ e₁' e₂', Γ ⊢ e₁ ≫* e₁' ∧ Γ ⊢ e₂ ≫* e₂' ∧ Γ ⊢ e₁' ≡ₚ e₂' : A
scoped notation:65 Γ " ⊢ " e1 " ≫≪ " e2 " : " A:36 => CRDefEq Γ e1 e2 A

def CRDefEqLift := WithLift CRDefEq
scoped notation:65 Γ " ⊢ " e1 " ≫≪ " e2 " :↑ " A:36 => CRDefEqLift Γ e1 e2 A

theorem CRDefEq.normalEq (H : Γ ⊢ e₁ ≡ₚ e₂ : A) : Γ ⊢ e₁ ≫≪ e₂ : A :=
  ⟨H.defeq, _, _, .rfl, .rfl, H⟩

theorem CRDefEq.refl (H : Γ ⊢ e : A) : Γ ⊢ e ≫≪ e : A :=
  .normalEq (.refl H)

theorem CRDefEq.defeq : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ e₁ ≡ e₂ : A := (·.1)

theorem CRDefEq.symm : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ e₂ ≫≪ e₁ : A
  | ⟨h1, _, _, h3, h4, h5⟩ => ⟨h1.symm, _, _, h4, h3, h5.symm⟩

/-- Transitivity of `CRDefEq`. Unproved: it needs confluence (Church-Rosser) of `ParRed`
modulo `NormalEq`, which the prototype does not have. -/
theorem CRDefEq.trans : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ e₂ ≫≪ e₃ : A → Γ ⊢ e₁ ≫≪ e₃ : A
  | ⟨l1, _, _, l3, l4, l5⟩, ⟨r1, _, _, r3, r4, r5⟩ => sorry

theorem CRDefEq.defeqDF : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ A ≡ B : .sort u → Γ ⊢ e₁ ≫≪ e₂ : B
  | ⟨l1, _, _, l3, l4, l5⟩, H => ⟨H.defeqDF l1, _, _, l3, l4, l5.defeqDF H⟩

theorem CRDefEq.weak' (W : Ctx.Lift' ρ Γ Γ') :
    Γ ⊢ e1 ≫≪ e2 : A → Γ' ⊢ e1.lift' ρ ≫≪ e2.lift' ρ : A.lift' ρ
  | ⟨h1, _, _, h3, h4, h5⟩ => ⟨h1.weak' W, _, _, h3.weak' W, h4.weak' W, h5.weak' W⟩

theorem WHRedS.crDefEq (H1 : Γ ⊢ e1 : A) (H2 : Γ ⊢ e1 ⤳* e2) : Γ ⊢ e1 ≫≪ e2 : A :=
  ⟨H2.defeq H1, _, _, H2.parRedS, .rfl, .refl (H2.defeq H1).hasType.2⟩

nonrec theorem CRDefEqLift.symm : Γ ⊢ e1 ≫≪ e2 :↑ A → Γ ⊢ e2 ≫≪ e1 :↑ A := .symm .symm

theorem CRDefEqLift.defeq (H : Γ ⊢ e1 ≫≪ e2 :↑ A) : Γ ⊢ e1 ≡ e2 :↑ A := H.imp (·.1)

theorem CRDefEqLift.left (H : Γ ⊢ e1 ≫≪ e2 :↑ A) : Γ ⊢ e1 :↑ A := H.defeq.left

nonrec theorem CRDefEqLift.refl (H : Γ ⊢ e :↑ A) : Γ ⊢ e ≫≪ e :↑ A :=
  .refl (.refl <| H.left' · · ·)

/-! The prototype stated `InferType.whRed : Γ ⊢ e ⤳ e' → Γ ⊢ e ▷ A → Γ ⊢ e' ▷ A` here, with a
placeholder proof. It is false, so it has been removed (it had no users). Inferred types are
syntactic and `InferType` is deterministic (`InferType.determ`), while a beta step can replace
a variable by an argument whose inferred type is only *convertible* to the binder type:
`(fun x : A => x) a ▷ A` (the `app` rule checks `a :↑ A`), but after the step `a ▷ A₀` for the
syntactic `A₀` inferred for `a`, e.g. `a := .sort 0` with `A₀ = .sort 1` and
`A := .app (.lam (.sort 2) (.bvar 0)) (.sort 1)`. Pattern steps have the same problem. A
correct statement needs inferred types up to conversion. -/
