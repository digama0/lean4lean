import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.Pattern

namespace Lean4Lean

namespace LogRel

class Params where
  env : VEnv
  henv : env.Ordered
  univs : Nat
  Pat : (p : Pattern) → p.RHS × p.Check → Prop
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
  ⟨fun v => (l₁.1 v).imax (l₂.1 v),
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
  /--  The `pat` annotation is true for applications that form part of a
  pattern trigger. This prevents unnecessary competition with beta and eta rules,
  which do not fire on pattern applications. -/
  | app (f a : SExpr) (pat : Bool := false)
  | lam (A e : SExpr)
  | forallE (A B : SExpr)

instance : Inhabited SExpr := ⟨.sort .zero⟩

namespace SExpr

@[simp] def lift' : SExpr → Lift → SExpr
  | .bvar i, k => .bvar (k.liftVar i)
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app fn arg pat, k => .app (fn.lift' k) (arg.lift' k) pat
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
  | .app fn arg _, k => fn.ClosedN k ∧ arg.ClosedN k
  | .lam ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)
  | .forallE ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)

theorem ClosedN.mono (h : k ≤ k') (self : ClosedN e k) : ClosedN e k' := by
  induction e generalizing k k' with (simp [ClosedN] at self ⊢; try simp [self, *])
  | bvar i => exact Nat.lt_of_lt_of_le self h
  | app _ _ _ ih1 ih2 => exact ⟨ih1 h self.1, ih2 h self.2⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    exact ⟨ih1 h self.1, ih2 (Nat.succ_le_succ h) self.2⟩

theorem ClosedN.lift'_eq (self : ClosedN e k) (h : ρ.Fixes k) : lift' e ρ = e := by
  induction e generalizing k ρ with (simp [ClosedN] at self; simp [*])
  | bvar i => exact h.liftVar_eq self
  | app _ _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩

theorem ClosedN.lift_eq (self : ClosedN e) : lift e = e := self.lift'_eq ⟨⟩

variable (ls : List SLevel) in
def instL : SExpr → SExpr
  | .bvar i => .bvar i
  | .sort u => .sort (u.inst ls)
  | .const c us => .const c (us.map (SLevel.inst ls))
  | .app fn arg pat => .app fn.instL arg.instL pat
  | .lam ty body => .lam ty.instL body.instL
  | .forallE ty body => .forallE ty.instL body.instL

theorem ClosedN.instL : ∀ {e}, ClosedN e k → ClosedN (e.instL ls) k
  | .bvar .., h | .sort .., h | .const .., h => h
  | .app .., h | .lam .., h | .forallE .., h => ⟨h.1.instL, h.2.instL⟩

def mk : VExpr → SExpr
  | .bvar i => .bvar i
  | .sort u => .sort (.mk u)
  | .const c us => .const c (us.map .mk)
  | .app fn arg => .app (.mk fn) (.mk arg)
  | .lam ty body => .lam (.mk ty) (.mk body)
  | .forallE ty body => .forallE (.mk ty) (.mk body)

theorem _root_.Lean4Lean.VExpr.ClosedN.mkS : ∀ {e : VExpr}, e.ClosedN k → ClosedN (.mk e) k
  | .bvar .., h | .sort .., h | .const .., h => h
  | .app .., h | .lam .., h | .forallE .., h => ⟨h.1.mkS, h.2.mkS⟩

def Subst := Nat → SExpr

def Subst.Depth (σ : Subst) (n n' : Nat) := ∀ i, σ (i + n') = .bvar (i + n)

theorem Subst.Depth.add {σ : Subst} (H : σ.Depth n n') : σ.Depth (n + k) (n' + k) :=
  fun i => cast (by congr 2 <;> omega) <| H (k + i)

def Subst.lift (σ : Subst) : Subst
  | 0 => .bvar 0
  | i+1 => (σ i).lift

theorem Subst.Depth.lift {σ : Subst} (H : σ.Depth n n') : σ.lift.Depth (n + 1) (n' + 1) :=
  fun i => by simp [Subst.lift, H i]; rfl

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

def _root_.Lean4Lean.Lift.inv : Lift → Subst
  | .refl => .id
  | .skip ρ => ρ.inv.cons default
  | .cons ρ => ρ.inv.lift

theorem Subst.Depth.inv : ∀ (ρ : Lift), ρ.inv.Depth ρ.dom ρ.size
  | .refl => .id
  | .skip l => (inv l).cons
  | .cons l => (inv l).lift

@[simp] theorem Subst.head_cons : (cons σ e).head = e := rfl
@[simp] theorem Subst.tail_cons : (cons σ e).tail = σ := rfl

def Subst.lift_r (σ : Subst) (ρ : Lift) : Subst := fun x => (σ x).lift' ρ
def Subst.lift_l (ρ : Lift) (σ : Subst) : Subst := fun x => σ (ρ.liftVar x)

theorem Subst.tail_eq_lift_l {σ : Subst} : σ.tail = σ.lift_l Lift.refl.skip := rfl

theorem Subst.lift_l_lift {σ : Subst} {ρ} : (σ.lift_l ρ).lift = σ.lift.lift_l ρ.cons := by
  funext i; cases i <;> simp! [lift_l]

theorem Subst.lift_r_lift {σ : Subst} {ρ} : (σ.lift_r ρ).lift = σ.lift.lift_r ρ.cons := by
  funext i; cases i <;> simp! [lift_r, ← lift'_comp]

theorem lift_l_inv {ρ : Lift} : .lift_l ρ ρ.inv = Subst.id := by
  funext i; simp [Subst.lift_l, Subst.id]
  induction ρ generalizing i with
  | refl => rfl
  | skip ρ ih => simp [Lift.inv, Subst.cons, ih]
  | cons ρ ih => cases i <;> simp [Lift.inv, Subst.lift, ih]

def _root_.Lean4Lean.Lift.toSubst (ρ : Lift) : Subst := .lift_l ρ .id

theorem _root_.Lean4Lean.Lift.toSubst_apply (ρ : Lift) (i) : ρ.toSubst i = bvar (ρ.liftVar i) := rfl

theorem Subst.Depth.toSubst (ρ : Lift) : ρ.toSubst.Depth ρ.size ρ.dom := by
  intro i; simp [Lift.toSubst_apply]
  induction ρ <;> simp! [*] <;> omega

def subst : SExpr → Subst → SExpr
  | .bvar i, σ => σ i
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app fn arg pat, σ => .app (fn.subst σ) (arg.subst σ) pat
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
  ⟨(by simpa [subst_lift', lift_l_inv] using congrArg (·.subst ρ.inv) ·), (· ▸ rfl)⟩

theorem subst_toSubst {e : SExpr} : subst e ρ.toSubst = lift' e ρ := by
  simp [Lift.toSubst, ← subst_lift']

theorem subst_lift'_inv {e : SExpr} {ρ : Lift} : (e.lift' ρ).subst ρ.inv = e := by
  rw [subst_lift', lift_l_inv, subst_id]

def Subst.comp (σ σ' : Subst) : Subst := fun x => (σ x).subst σ'

theorem Subst.comp_lift {σ σ' : Subst} : (σ.comp σ').lift = σ.lift.comp σ'.lift := by
  funext i; cases i <;> simp! [comp, SExpr.lift]
  rw [SExpr.lift, SExpr.lift, lift'_subst, subst_lift']; rfl

theorem subst_subst {e : SExpr} : (e.subst σ).subst σ' = subst e (.comp σ σ') := by
  induction e generalizing σ σ' <;> simp! [*, Subst.comp, Subst.comp_lift]

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

def inst (e a : SExpr) : SExpr := e.subst (.one a)

def Skips (e : SExpr) (ρ : Lift) : Prop := lift' (e.subst ρ.inv) ρ = e

theorem Skips.lift (e : SExpr) (ρ : Lift) : Skips (e.lift' ρ) ρ := by
  rw [Skips, subst_lift'_inv]

def Skips' : SExpr → (ρ : Lift) → Prop
  | .bvar i, ρ => ∃ j, ρ.liftVar j = i
  | .sort .., _ | .const .., _ => True
  | .app fn arg _, ρ => fn.Skips' ρ ∧ arg.Skips' ρ
  | .lam ty body, ρ => ty.Skips' ρ ∧ body.Skips' ρ.cons
  | .forallE ty body, ρ => ty.Skips' ρ ∧ body.Skips' ρ.cons

theorem skips_iff {e : SExpr} {ρ : Lift} : Skips e ρ ↔ Skips' e ρ := by
  simp [Skips]; induction e generalizing ρ with simp!
  | app _ _ _ ih1 ih2 => exact and_congr ih1 ih2
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact and_congr ih1 (@ih2 ρ.cons)
  | bvar i =>
    constructor <;> [intro h; intro ⟨j, h⟩]
    · refine (?_ : have := (match ρ.inv i with | SExpr.bvar .. => True | _ => True); _); split
      · rename_i eq; cases eq ▸ h; exact ⟨_, rfl⟩
      · suffices ρ.inv i = default by cases this ▸ h
        clear h; rename_i h
        induction ρ generalizing i <;> simp [Lift.inv, Subst.id] at * <;>
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

-- ρ : Γ ⊇ Δ
-- Δ ⊢ ρ⁻¹ : Γ
-- Δ ⊢ ρ ∘ ρ⁻¹ = 1 : Δ
-- Γ ⊢ ρ⁻¹ ∘ ρ : Γ


-- ρ : Γ ⊇ Δ
-- Δ ⊢ σ : Θ
-- Γ ⊢ σ ∘ ρ : Θ
-- Γ ⊢ ρ? ∘ ? : Θ

--   Γ       Δ        Θ
-- x,y,z => x,z => x, z, e1, e2
--             <== inv

--   Γ       Δ        Θ
-- x,y,z => x,z => x, z, e1, e2
--    lift ρ    subst σ

--   Γ           Λ                Θ
-- x,y,z => x,y,z,e1,e2 => x, z, e1, e2

--   Γ       Δ        Θ
-- x,y,z => x,z => x, z, e

--   Γ       Δ          Θ
-- x,y,z => x,z => f x z, z, x

-- Γ ⊢ σ ∘ ρ : Δ'
-- Γ ⊢ ρ!σ : A ▸ ρ :: Γ
-- ρ! : A ▸ ρ :: Γ ⊇ A::Δ
-- Γ ⊢ ρ! ∘ (1, e ▸ ρ) : A::Δ

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

end SExpr

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
  have := SExpr.Skips.lift e₁ ρ₁
  have h1 : _ = _ := SExpr.skips_inter.2 ⟨.lift e₁ ρ₁, H ▸ SExpr.Skips.lift e₂ ρ₂⟩
  have h2 := h1; conv at h1 => enter [1,2]; rw [← Lift.diff_comp]
  conv at h2 => enter [1,2]; rw [Lift.inter_comm, ← Lift.diff_comp]
  rw [SExpr.lift'_comp] at h1 h2
  exact ⟨_, SExpr.lift'_inj.1 h2, SExpr.lift'_inj.1 (h1.trans H)⟩

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
      rw [← SExpr.lift'_comp, Lift.diff_comp]
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
    (p : Pattern) → SExpr → (p.Path.1 → List SLevel) → (p.Path.2 → SExpr) → Prop
  | const : MatchesS (.const c) (.const c ls) (fun _ => ls) nofun
  | var : MatchesS f f' f1 g1 → MatchesS (.var f) (.app f' a' true) f1 (·.elim a' g1)
  | app : MatchesS f f' f1 g1 → MatchesS a a' f2 g2 →
    MatchesS (.app f a) (.app f' a' true) (Sum.elim f1 f2) (Sum.elim g1 g2)

def _root_.Lean4Lean.Pattern.RHS.applyS {p : Pattern}
    (m1 : p.Path.1 → List SLevel) (m2 : p.Path.2 → SExpr) : p.RHS → SExpr
  | .fixed path c _ => .instL (m1 path) (.mk c)
  | .var path => m2 path
  | .app f a => .app (f.applyS m1 m2) (a.applyS m1 m2)

def _root_.Lean4Lean.Pattern.RHS.Closed {p : Pattern} : p.RHS → Prop
  | .fixed _ c _ => c.Closed
  | .var _ => True
  | .app f a => f.Closed ∧ a.Closed

def _root_.Lean4Lean.Pattern.RHS.Closed.applyS {p : Pattern} {m1 m2} :
    ∀ r : p.RHS, r.Closed → (∀ a, (m2 a).ClosedN k) → (r.applyS m1 m2).ClosedN k
  | .fixed .., h1, _ => h1.mkS.instL.mono (Nat.zero_le _)
  | .var _, _, h2 => h2 _
  | .app .., h1, h2 => ⟨h1.1.applyS _ h2, h1.2.applyS _ h2⟩

def _root_.Lean4Lean.Pattern.Check.defeqsS {p : Pattern}
    (m1 : p.Path.1 → List SLevel) (m2 : p.Path.2 → SExpr) : p.Check → List (SExpr × SExpr)
  | .true => []
  | .defeq a b rest => (a.applyS m1 m2, b.applyS m1 m2) :: rest.defeqsS m1 m2

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

theorem Lookup.determ (H1 : Lookup Γ i A) (H2 : Lookup Γ i A') : A = A' := by
  induction H1 generalizing A' with obtain _ | r1 := H2
  | zero => rfl
  | succ _ ih => cases ih r1; rfl

local notation:65 Γ " ⊢ " e " : " A:36 => IsDefEq Γ e e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEq Γ e1 e2 A
inductive IsDefEq : List SExpr → SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  | sort : Γ ⊢ .sort l : .sort (.succ l)
  | const : env.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ .const c ls : (SExpr.mk ci.type).instL ls
  | appDF : Γ ⊢ f ≡ f' : .forallE A B → Γ ⊢ a ≡ a' : A →
    Γ ⊢ .app f a pat ≡ .app f' a' pat : B.inst a
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

def Ctx.WF : List SExpr → Prop
  | [] => True
  | A::Γ => WF Γ ∧ ∃ u, Γ ⊢ A : .sort u
local notation:65 "⊢ " Γ:36 => Ctx.WF Γ

variable (HasType : List SExpr → SExpr → SExpr → Prop)
inductive Ctx.Subst : List SExpr → SExpr.Subst → List SExpr → Prop where
  | nil : Ctx.Subst Γ σ []
  | cons : Ctx.Subst Γ σ.tail Δ → HasType Γ σ.head (A.subst σ.tail) → Ctx.Subst Γ σ (A::Δ)

variable {HasType}
theorem Ctx.Subst.head (H : Ctx.Subst HasType Γ σ (A::Δ)) : HasType Γ σ.head (A.subst σ.tail) :=
  let .cons _ H := H; H

theorem Ctx.Subst.tail (H : Ctx.Subst HasType Γ σ (A::Δ)) : Ctx.Subst HasType Γ σ.tail Δ :=
  let .cons H _ := H; H

theorem Ctx.Subst.cons' (H1 : Ctx.Subst HasType Γ σ Δ) (H2 : HasType Γ e (A.subst σ)) :
    Ctx.Subst HasType Γ (σ.cons e) (A::Δ) := .cons H1 H2

theorem Ctx.Subst.lift_r (H1 : Ctx.Subst HasType Γ σ Θ) (H2 : Ctx.Lift' ρ Δ Θ) :
    Ctx.Subst HasType Γ (σ.lift_r ρ) Δ := sorry

theorem Ctx.Subst.id : Ctx.Subst HasType Γ .id Γ := sorry
theorem Ctx.Subst.one (H : HasType Γ e A) : Ctx.Subst HasType Γ (.one e) (A::Γ) :=
  .cons .id (by simpa)

theorem IsDefEq.hasType (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ ⊢ e1 ≡ e1 : A ∧ Γ ⊢ e2 ≡ e2 : A := ⟨H.trans H.symm, H.symm.trans H⟩

theorem IsDefEq.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ' ⊢ e1.lift' ρ ≡ e2.lift' ρ : A.lift' ρ := by
  induction H generalizing ρ Γ' with
  | bvar h => refine .bvar (h.weak' W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
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

theorem IsDefEq.defeqDF_l' (h1 : Γ ⊢ A ≡ A' : .sort u)
    (h2 : Δ++A::Γ ⊢ e1 ≡ e2 : B) : Δ++A'::Γ ⊢ e1 ≡ e2 : B := by
  sorry

theorem IsDefEq.defeqDF_l (h1 : Γ ⊢ A ≡ A' : .sort u)
    (h2 : A::Γ ⊢ e1 ≡ e2 : B) : A'::Γ ⊢ e1 ≡ e2 : B :=
  .defeqDF_l' (Δ := []) h1 h2

theorem HasType.defeq_l (h1 : Γ ⊢ A ≡ A' : .sort u)
    (h2 : A::Γ ⊢ e : B) : A'::Γ ⊢ e : B := h1.defeqDF_l h2

variable (DefEq : List SExpr → SExpr → SExpr → SExpr → Prop) in
structure WithLift (Γ : List SExpr) (e1 e2 A : SExpr) : Prop where
  defeq' {{Δ ρ e1' e2' A'}} : Ctx.Lift' ρ Δ Γ →
    e1 = .lift' e1' ρ → e2 = .lift' e2' ρ → A = .lift' A' ρ → DefEq Δ e1' e2' A'
  left' {{Δ ρ e1' A'}} : Ctx.Lift' ρ Δ Γ → e1 = .lift' e1' ρ → A = .lift' A' ρ → DefEq Δ e1' e1' A'
  right' {{Δ ρ e2' A'}} : Ctx.Lift' ρ Δ Γ → e2 = .lift' e2' ρ → A = .lift' A' ρ → DefEq Δ e2' e2' A'

def IsDefEqLift := WithLift IsDefEq
local notation:65 Γ " ⊢ " e " :↑ " A:36 => IsDefEqLift Γ e e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " :↑ " A:36 => IsDefEqLift Γ e1 e2 A

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

local notation:65 Γ " ⊢ " e1 " ⤳ " e2:36 => WHRed Γ e1 e2
inductive WHRed (Γ : List SExpr) : SExpr → SExpr → Prop where
  | app : Γ ⊢ f ⤳ f' → Γ ⊢ .app f a ⤳ .app f' a
  | beta : Γ ⊢ .app (.lam A e) a ⤳ e.inst a
  | extra : Pat p r → p.MatchesS e m1 m2 → (dfs : List _).map (·.2) = r.2.defeqsS m1 m2 →
    (∀ a b A, (A, a, b) ∈ dfs → Γ ⊢ a ≡ b :↑ A) → Γ ⊢ e ⤳ r.1.applyS m1 m2

theorem WHRed.weak' (W : Ctx.Lift' ρ Γ Γ') :
    Γ ⊢ e1 ⤳ e2 → Γ' ⊢ e1.lift' ρ ⤳ e2.lift' ρ
  | .app h1 => .app (h1.weak' W)
  | .beta => by rw [SExpr.lift'_inst_hi]; exact .beta
  | .extra h1 h2 h3 h4 => sorry

theorem WHRed.weakU_inv (W : Ctx.Lift' ρ Γ Γ') (H : Γ' ⊢ e1.lift' ρ ⤳ e2') :
    ∃ e2, e2' = e2.lift' ρ ∧ Γ ⊢ e1 ⤳ e2 := by
  generalize he : e1.lift' ρ = e1' at H
  induction H generalizing e1 with
  | app h1 ih => let .app .. := e1; cases he; obtain ⟨_, rfl, a1⟩ := ih rfl; exact ⟨_, rfl, .app a1⟩
  | beta =>
    let .app e1 _ pat := e1; let .lam .. := e1; cases pat <;> cases he
    simp [← SExpr.lift'_inst_hi, SExpr.lift'_inj]; exact .beta
  | extra => sorry

def WHNF (Γ : List SExpr) (e : SExpr) := ∀ e', ¬Γ ⊢ e ⤳ e'

theorem WHNF.lam : WHNF Γ (.lam A e) := nofun
theorem WHNF.sort : WHNF Γ (.sort A) := nofun
theorem WHNF.forallE : WHNF Γ (.forallE A B) := nofun

theorem WHRed.determ (H1 : Γ ⊢ e ⤳ e₁) (H2 : Γ ⊢ e ⤳ e₂) : e₁ = e₂ := by
  induction H1 generalizing e₂ with
  | app l1 ih =>
    cases H2 with
    | app r1 => cases ih r1; rfl
    | beta => cases WHNF.lam _ l1
    | extra => sorry
  | beta =>
    cases H2 with
    | app r1 => cases WHNF.lam _ r1
    | beta => rfl
    | extra _ r2 => cases r2
  | extra _ l2 =>
    cases H2 with
    | beta => cases l2
    | app => sorry
    | extra _ r2 => sorry

def WHRedS (Γ : List SExpr) : SExpr → SExpr → Prop := ReflTransGen (WHRed Γ)
local notation:65 Γ " ⊢ " e1 " ⤳* " e2:36 => WHRedS Γ e1 e2

theorem WHRedS.weak' (W : Ctx.Lift' ρ Γ Δ) (H : Γ ⊢ e1 ⤳* e2) :
    Δ ⊢ e1.lift' ρ ⤳* e2.lift' ρ := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.weak' W)

theorem WHRedS.weakU_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e1.lift' ρ ⤳* e2') :
    ∃ e2, e2' = e2.lift' ρ ∧ Γ ⊢ e1 ⤳* e2 := by
  induction H with
  | rfl => exact ⟨_, rfl, .rfl⟩
  | tail _ h2 ih =>
    obtain ⟨_, rfl, a1⟩ := ih
    obtain ⟨_, rfl, a2⟩ := h2.weakU_inv W
    exact ⟨_, rfl, .tail a1 a2⟩

theorem WHRedS.determ
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

theorem WHNF.whRedS (W : WHNF Γ e) (H : Γ ⊢ e ⤳* e') : e = e' := by
  cases H using ReflTransGen.headIndOn with
  | rfl => rfl
  | head h1 => cases W _ h1

local notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
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
  | .extra h1 h2 h3 h4 h5 => sorry

def ParRedS (Γ : List SExpr) : SExpr → SExpr → Prop := ReflTransGen (ParRed Γ)
local notation:65 Γ " ⊢ " e1 " ≫* " e2:36 => ParRedS Γ e1 e2

theorem ParRedS.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ≫* e2) :
    Γ' ⊢ e1.lift' ρ ≫* e2.lift' ρ := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.weak' W)

local notation:65 Γ " ⊢ " e1 " ▷ " e2:36 => InferType Γ e1 e2
inductive InferType : List SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ .bvar i ▷ A
  | sort : Γ ⊢ .sort u ▷ .sort (.succ u)
  | const : env.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ .const c ls ▷ (SExpr.mk ci.type).instL ls
  | app : Γ ⊢ f ▷ F → Γ ⊢ F ⤳* .forallE A B → Γ ⊢ a :↑ A → Γ ⊢ .app f a ▷ B.inst a
  | lam : Γ ⊢ A :↑ .sort u → A::Γ ⊢ body ▷ B → Γ ⊢ .lam A body ▷ .forallE A B
  | forallE : Γ ⊢ A ▷ U → Γ ⊢ U ⤳* .sort u →
    A::Γ ⊢ B ▷ V → A::Γ ⊢ V ⤳* .sort v → Γ ⊢ .forallE A B ▷ .sort (.imax u v)

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

def InferTypeS (Γ : List SExpr) (e A : SExpr) := ∃ A', Γ ⊢ e ▷ A' ∧ Γ ⊢ A' ⤳* A
local notation:65 Γ " ⊢ " e1 " ▷* " e2:36 => InferTypeS Γ e1 e2

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

theorem InferType.subst (W : Ctx.Subst InferType Δ σ Γ)
    (H : Γ ⊢ e ▷ A) : Δ ⊢ e.subst σ ▷ A.subst σ := by
  induction H with
  | @bvar _ i _ h =>
    simp [SExpr.subst]
    induction W generalizing i with | nil | cons W h' ih <;> cases h
    case zero => rw [SExpr.lift, SExpr.subst_lift']; exact h'
    case succ h => stop rw [SExpr.lift, SExpr.subst_lift']; exact ih h.succ
  | sort => sorry
  | const => sorry
  | app => sorry
  | lam => sorry
  | forallE => sorry

local notation:65 Γ " ⊢ " e1 " ≡ₚ " e2 " : " A:36 => NormalEq Γ e1 e2 A
inductive NormalEq : List SExpr → SExpr → SExpr → SExpr → Prop where
  | refl : Γ ⊢ e : A → Γ ⊢ e ≡ₚ e : A
  | appDF : Γ ⊢ f₁ ≡ₚ f₂ : .forallE A B → Γ ⊢ a₁ ≡ₚ a₂ : A →
    Γ ⊢ .app f₁ a₁ pat ≡ₚ .app f₂ a₂ pat : B.inst a₁
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
  | appDF h1 h2 ih1 ih2 => exact .defeqDF sorry (u := sorry) <| .appDF (ih1 W) (ih2 W)
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
local notation:65 Γ " ⊢ " e1 " ≫≪ " e2 " : " A:36 => CRDefEq Γ e1 e2 A

def CRDefEqLift := WithLift CRDefEq
local notation:65 Γ " ⊢ " e1 " ≫≪ " e2 " :↑ " A:36 => CRDefEqLift Γ e1 e2 A

theorem CRDefEq.normalEq (H : Γ ⊢ e₁ ≡ₚ e₂ : A) : Γ ⊢ e₁ ≫≪ e₂ : A :=
  ⟨H.defeq, _, _, .rfl, .rfl, H⟩

theorem CRDefEq.refl (H : Γ ⊢ e : A) : Γ ⊢ e ≫≪ e : A :=
  .normalEq (.refl H)

theorem CRDefEq.defeq : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ e₁ ≡ e₂ : A := (·.1)

theorem CRDefEq.symm : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ e₂ ≫≪ e₁ : A
  | ⟨h1, _, _, h3, h4, h5⟩ => ⟨h1.symm, _, _, h4, h3, h5.symm⟩

theorem CRDefEq.trans : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ e₂ ≫≪ e₃ : A → Γ ⊢ e₁ ≫≪ e₃ : A
  | ⟨l1, _, _, l3, l4, l5⟩, ⟨r1, _, _, r3, r4, r5⟩ => sorry

theorem CRDefEq.weak' (W : Ctx.Lift' ρ Γ Γ') :
    Γ ⊢ e1 ≫≪ e2 : A → Γ' ⊢ e1.lift' ρ ≫≪ e2.lift' ρ : A.lift' ρ
  | ⟨h1, _, _, h3, h4, h5⟩ => ⟨h1.weak' W, _, _, h3.weak' W, h4.weak' W, h5.weak' W⟩

nonrec theorem CRDefEqLift.symm : Γ ⊢ e1 ≫≪ e2 :↑ A → Γ ⊢ e2 ≫≪ e1 :↑ A := .symm .symm

theorem CRDefEqLift.defeq (H : Γ ⊢ e1 ≫≪ e2 :↑ A) : Γ ⊢ e1 ≡ e2 :↑ A := H.imp (·.1)

theorem CRDefEqLift.left (H : Γ ⊢ e1 ≫≪ e2 :↑ A) : Γ ⊢ e1 :↑ A := H.defeq.left

nonrec theorem CRDefEqLift.refl (H : Γ ⊢ e :↑ A) : Γ ⊢ e ≫≪ e :↑ A :=
  .refl (.refl <| H.left' · · ·)

structure Classifier' where
  EqTy' : SExpr → Prop := fun _ => True
  HasTy' : SExpr → Prop := fun _ => True
  DefEq' : SExpr → SExpr → Prop := fun _ _ => True
  defEq'_symm : DefEq' a b → DefEq' b a := by exact id
  defEq'_left : DefEq' a b → DefEq' a a := by exact id
  defEq'_self : HasTy' a → DefEq' a a := by exact id
def Classifier (_Γ : List SExpr) (_A : SExpr) (_u : SLevel) := Classifier'

def Classifier.EqTy (cl : Classifier Γ A u) (B : SExpr) : Prop :=
  Γ ⊢ A ≡ B :↑ .sort u ∧ cl.EqTy' B

def Classifier.HasTy (cl : Classifier Γ A u) (a : SExpr) : Prop :=
  (Γ ⊢ a :↑ A) ∧ cl.HasTy' a

def Classifier.DefEq (cl : Classifier Γ A u) (a b : SExpr) : Prop :=
  Γ ⊢ a ≫≪ b :↑ A ∧ cl.HasTy' a ∧ cl.HasTy' b ∧ cl.DefEq' a b

theorem Classifier.DefEq.symm {cl : Classifier Γ A u} : cl.DefEq a b → cl.DefEq b a
  | ⟨h1, h2, h3, h4⟩ => ⟨h1.symm, h3, h2, cl.defEq'_symm h4⟩
theorem Classifier.DefEq.left {cl : Classifier Γ A u} : cl.DefEq a b → cl.HasTy a
  | ⟨h1, h2, _⟩ => ⟨h1.left, h2⟩

theorem Classifier.defEq_self {cl : Classifier Γ A u} : cl.DefEq a a ↔ cl.HasTy a :=
  ⟨fun h => h.left, fun ⟨h1, h2⟩ => ⟨.refl h1, h2, h2, cl.defEq'_self h2⟩⟩

theorem Classifier.DefEq.imp {Γ A u Γ' A' u'} {cl : Classifier Γ A u} {cl' : Classifier Γ' A' u'}
    {f : SExpr → SExpr}
    (H0 : ∀ {a b}, Γ ⊢ a ≫≪ b :↑ A → Γ' ⊢ f a ≫≪ f b :↑ A')
    (H1 : ∀ {a}, cl.HasTy' a → cl'.HasTy' (f a))
    (H2 : ∀ {a b}, cl.DefEq' a b → cl'.DefEq' (f a) (f b))
    {a b} : cl.DefEq a b → cl'.DefEq (f a) (f b)
  | ⟨h1, h2, h3, h4⟩ => ⟨H0 h1, H1 h2, H1 h3, H2 h4⟩

def Classifier.forallE
    (RA : ∀ {ρ Δ}, Ctx.Lift' ρ Γ Δ → Classifier Δ (A.lift' ρ) u)
    (RB : ∀ {ρ Δ} (W : Ctx.Lift' ρ Γ Δ) {a},
      (@RA ρ Δ W).HasTy a → Classifier Δ ((B.lift' ρ.cons).inst a) v) :
    Classifier Γ (.forallE A B) (.imax u v) where
  EqTy' C := ∃ A' B', Γ ⊢ C ⤳* .forallE A' B' ∧ Γ ⊢ C ≡ .forallE A' B' :↑ .sort (.imax u v) ∧
    (∀ {ρ Δ} W, (@RA ρ Δ W).EqTy (A'.lift' ρ)) ∧
    (∀ {ρ Δ} W {a} (ha : (@RA ρ Δ W).HasTy a), (RB W ha).EqTy ((B'.lift' ρ.cons).inst a))
  HasTy' f := ∀ {ρ Δ W a b} (ab : (@RA ρ Δ W).DefEq a b),
    (RB W ab.left).DefEq ((f.lift' ρ).app a) ((f.lift' ρ).app b)
  DefEq' f g := ∀ {ρ Δ W a} (ha : (@RA ρ Δ W).HasTy a),
    (RB W ha).DefEq ((f.lift' ρ).app a) ((g.lift' ρ).app a)
  defEq'_symm _ _ H {ρ Δ W a} (ha : (@RA ρ Δ W).HasTy a) := (H ha).symm
  defEq'_left _ _ H {ρ Δ W a} (ha : (@RA ρ Δ W).HasTy a) := Classifier.defEq_self.2 (H ha).left
  defEq'_self _ H {ρ Δ W a} (ha : (@RA ρ Δ W).HasTy a) := H (Classifier.defEq_self.2 ha)

def NormalType : SExpr → Prop | .sort _ | .forallE .. => True | _ => False

def NormalType.whnf : ∀ {A}, NormalType A → WHNF Γ A
  | .sort _, _ => .sort
  | .forallE .., _ => .forallE

theorem NormalType.weak' (H : NormalType A) : NormalType (A.lift' ρ) := by
  cases A <;> cases H <;> trivial

theorem NormalType.weak'_inv (H : NormalType (A.lift' ρ)) : NormalType A := by
  cases A <;> cases H <;> trivial

inductive LogRel : ∀ Γ A u, Classifier Γ A u → Type where
  | stuck :
    (∀ A', Γ ⊢ A ⤳* A' → ¬NormalType A') →
    Γ ⊢ A ▷* .sort u → Γ ⊢ A :↑ .sort u → LogRel Γ A u {}
  | sort : Γ ⊢ A ⤳* .sort l → Γ ⊢ A ▷* .sort l.succ → Γ ⊢ A ≡ .sort l :↑ .sort l.succ →
    LogRel Γ A (.succ l) { EqTy' A := Γ ⊢ A ⤳* .sort l }
  | forallE
    {RA : ∀ {ρ Δ}, Ctx.Lift' ρ Γ Δ → Classifier Δ (A.lift' ρ) u}
    {RB : ∀ {ρ Δ} (W : Ctx.Lift' ρ Γ Δ) {a},
      (@RA ρ Δ W).HasTy a → Classifier Δ ((B.lift' ρ.cons).inst a) v} :
    Γ ⊢ X ⤳* .forallE A B → Γ ⊢ X ▷* .sort (.imax u v) →
    A::Γ ⊢ B ▷* .sort v → A::Γ ⊢ B :↑ .sort v → Γ ⊢ X ≡ .forallE A B :↑ .sort (.imax u v) →
    (∀ {ρ Δ} W, LogRel Δ (A.lift' ρ) u (@RA ρ Δ W)) →
    (∀ {ρ Δ} W {a} (ha : (@RA ρ Δ W).HasTy a), LogRel Δ ((B.lift' ρ.cons).inst a) v (RB W ha)) →
    (∀ {ρ Δ} W {a b} (ab : (@RA ρ Δ W).DefEq a b), (RB W ab.left).EqTy ((B.lift' ρ.cons).inst b)) →
    LogRel Γ X (.imax u v) (.forallE @RA @RB)

theorem LogRel.hasType : LogRel Γ A u cl → Γ ⊢ A :↑ .sort u
  | .stuck _ _ h => h
  | .sort _ _ h | .forallE _ _ _ _ h .. => h.left

theorem LogRel.eqTy_refl (H : LogRel Γ A u cl) : cl.EqTy A := by
  induction H with
  | stuck _ _ h => exact ⟨h, ⟨⟩⟩
  | sort h1 _ h3 => exact ⟨h3.left, h1⟩
  | forallE h1 _ _ _ h5 _ _ h8 ih1 =>
    exact ⟨h5.left, _, _, h1, h5, fun _ => ih1 _, fun _ _ h => h8 _ (Classifier.defEq_self.2 h)⟩

def LRIsType (Γ : List SExpr) (A : SExpr) (u : SLevel) : Type := Σ cl, LogRel Γ A u cl
local notation:65 Γ " ⊩["u"] " A:36 => LRIsType Γ A u

def LREqTy {Γ A u} (B : SExpr) (H : Γ ⊩[u] A) : Prop := H.1.EqTy B
local notation:65 H " ⊩≡ " B:36 => LREqTy B H

def LRDefEq {Γ A u} (a b : SExpr) (H : Γ ⊩[u] A) : Prop := H.1.DefEq a b
local notation:65 H " ⊩ " a:36 " ≡ " b:36 => LRDefEq a b H
local notation:65 H " ⊩ " a:36 => LRDefEq a a H

theorem LRIsType.hasType (J : Γ ⊩[u] A) : Γ ⊢ A :↑ .sort u := J.2.hasType
theorem LREqTy.defeq {J : Γ ⊩[u] A} (H : J ⊩≡ B) : Γ ⊢ A ≡ B :↑ .sort u := H.1
theorem LRDefEq.defeq {J : Γ ⊩[u] A} (H : J ⊩ a ≡ b) : Γ ⊢ a ≡ b :↑ A := H.1.defeq
nonrec theorem LRDefEq.left {Γ A u a b} {J : Γ ⊩[u] A} (H : J ⊩ a ≡ b) : J ⊩ a :=
  Classifier.defEq_self.2 H.left

def LRIsType.cast (J : Γ ⊩[u] A) (eq : A = A') : Γ ⊩[u] A' := eq ▸ J
theorem LREqTy.cast {J : Γ ⊩[u] A} (eq : A = A') : J.cast eq ⊩≡ B ↔ J ⊩≡ B := by
  cases eq; rfl
theorem LRDefEq.cast {J : Γ ⊩[u] A} (eq : A = A') : J.cast eq ⊩ a ≡ b ↔ J ⊩ a ≡ b := by
  cases eq; rfl
theorem LRHasTy.cast {J : Γ ⊩[u] A} (eq : A = A') : (J.cast eq).1.HasTy a ↔ J.1.HasTy a := by
  cases eq; rfl

def LRIsType.stuck (H : ∀ A', Γ ⊢ A ⤳* A' → ¬NormalType A')
    (h1 : Γ ⊢ A ▷* .sort u) (h2 : Γ ⊢ A :↑ .sort u) : Γ ⊩[u] A := ⟨_, .stuck H h1 h2⟩
def LRIsType.sort
    (h1 : Γ ⊢ A ⤳* .sort l) (h2 : Γ ⊢ A ▷* .sort l.succ) (h3 : Γ ⊢ A ≡ .sort l :↑ .sort l.succ) :
    Γ ⊩[l.succ] A := ⟨_, .sort h1 h2 h3⟩
def LRIsType.forallE
    (ht1 : Γ ⊢ X ⤳* .forallE A B) (ht2 : Γ ⊢ X ▷* .sort (.imax u v))
    (ht3 : A::Γ ⊢ B ▷* .sort v) (ht4 : A::Γ ⊢ B :↑ .sort v)
    (ht5 : Γ ⊢ X ≡ .forallE A B :↑ .sort (.imax u v))
    (hA : ∀ {ρ Δ}, Ctx.Lift' ρ Γ Δ → Δ ⊩[u] A.lift' ρ)
    (hB : ∀ {ρ Δ} W {a}, @hA ρ Δ W ⊩ a → Δ ⊩[v] (B.lift' ρ.cons).inst a)
    (ha : ∀ {ρ Δ} W {a b} (ab : @hA ρ Δ W ⊩ a ≡ b), hB W ab.left ⊩≡ (B.lift' ρ.cons).inst b)
    : Γ ⊩[u.imax v] X :=
  ⟨_, .forallE ht1 ht2 ht3 ht4 ht5
    (fun W => (hA W).2) (fun W _ h => (hB W (Classifier.defEq_self.2 h)).2)
    (fun W _ _ => ha W)⟩

@[elab_as_elim] def LRIsType.rec
    {motive : ∀ {Γ u A}, Γ ⊩[u] A → Sort _}
    (stuck : ∀ {Γ u A} h1 h2 h3, motive (@LRIsType.stuck _ Γ u A h1 h2 h3))
    (sort : ∀ {Γ u A} h1 h2 h3, motive (@LRIsType.sort _ Γ u A h1 h2 h3))
    (forallE : ∀ {Γ X A B u v} ht1 ht2 ht3 ht4 ht5 hA hB ha,
      (∀ {ρ Δ} W, motive (@hA ρ Δ W)) →
      (∀ {ρ Δ} W {a} ha, motive (@hB ρ Δ W a ha)) →
      motive (@LRIsType.forallE _ Γ X A B u v ht1 ht2 ht3 ht4 ht5 hA hB ha))
    {Γ u A} (J : Γ ⊩[u] A) : motive J := inner J.2 where
  inner {Γ u A cl} : ∀ (J : LogRel Γ A u cl), motive ⟨cl, J⟩
    | .stuck h1 h2 h3 => stuck h1 h2 h3
    | .sort h1 h2 h3 => sort h1 h2 h3
    | .forallE ht1 ht2 ht3 ht4 ht5 hA hB ha =>
      forallE ht1 ht2 ht3 ht4 ht5 (fun W => ⟨_, hA W⟩)
        (fun W _ ha => ⟨_, hB W (Classifier.defEq_self.1 ha)⟩) ha
        (fun W => inner (hA W))
        (fun W _ ha => inner (hB W (Classifier.defEq_self.1 ha)))

theorem LRIsType.irrel' (J1 : Γ ⊩[u] A) (J2 : Γ ⊩[u'] A) : u = u' ∧ J1 ≍ J2 := by
  induction J1 using LRIsType.rec generalizing u' with
  | stuck l1 l2 =>
    cases J2 using LRIsType.rec with
    | stuck _ r2 => cases l2.determ .sort r2 .sort; exact ⟨rfl, .rfl⟩
    | sort h | forallE h => cases l1 _ h ⟨⟩
  | sort l1 =>
    cases J2 using LRIsType.rec with
    | stuck r1 => cases r1 _ l1 ⟨⟩
    | sort r1 | forallE r1 => cases l1.determ .sort r1 (NormalType.whnf ⟨⟩) <;> exact ⟨rfl, .rfl⟩
  | @forallE Γ u v X A B l1 _ l3 l4 l5 L1 L2 L3 ih1 ih2 =>
    cases J2 using LRIsType.rec with
    | stuck r1 => cases r1 _ l1 ⟨⟩
    | sort r1 => cases l1.determ .forallE r1 .sort
    | @forallE Γ' u' v' X' A' B' r1 _ r3 r4 r5 R1 R2 R3 =>
      cases l1.determ .forallE r1 .forallE
      cases l3.determ .sort r3 .sort
      have {ρ Δ} W := @ih1 ρ Δ W _ (R1 W)
      cases (this .refl).1
      obtain rfl : @L1 = @R1 := by grind
      have {ρ Δ} W {a} ha := @ih2 ρ Δ W a ha _ (R2 W ha)
      obtain rfl : @L2 = @R2 := by grind
      exact ⟨rfl, .rfl⟩

theorem LRIsType.irrel (J1 J2 : Γ ⊩[u] A) : J1 = J2 := eq_of_heq (J1.irrel' J2).2

theorem LREqTy.irrel {J J' : Γ ⊩[u] A} (H : J ⊩≡ B) : J' ⊩≡ B := by
  cases J.irrel J'; exact H

theorem LRDefEq.irrel {J J' : Γ ⊩[u] A} (H : J ⊩ a ≡ b) : J' ⊩ a ≡ b := by
  cases J.irrel J'; exact H

instance {Γ A u} : Subsingleton (Γ ⊩[u] A) := ⟨LRIsType.irrel⟩

protected def LogRel.cast (J : LogRel Γ A u cl) (eq : A = A') : Σ cl, LogRel Γ A' u cl :=
  ⟨cl, eq ▸ J⟩

theorem LogRel.cast_eqTy (J : LogRel Γ A u cl) (eq : A = A') :
    (J.cast eq).1.EqTy a ↔ cl.EqTy a :=
  ⟨fun ⟨h1, h2⟩ => ⟨eq ▸ h1, h2⟩, fun ⟨h1, h2⟩ => ⟨eq ▸ h1, h2⟩⟩

theorem LogRel.cast_hasTy (J : LogRel Γ A u cl) (eq : A = A') :
    (J.cast eq).1.HasTy a ↔ cl.HasTy a :=
  ⟨fun ⟨h1, h2⟩ => ⟨eq ▸ h1, h2⟩, fun ⟨h1, h2⟩ => ⟨eq ▸ h1, h2⟩⟩

theorem LogRel.cast_defEq (J : LogRel Γ A u cl) (eq : A = A') :
    (J.cast eq).1.DefEq a b ↔ cl.DefEq a b := and_congr_left' (eq ▸ .rfl)

variable! {ρ Γ Δ} (W : Ctx.Lift' ρ Γ Δ) in open SExpr LogRel in
def LRIsType.weak' (J : Γ ⊩[u] A) : Δ ⊩[u] A.lift' ρ := by
  induction J using LRIsType.rec with
  | stuck h1 h2 h3 =>
    refine ⟨_, .stuck (fun _ a1 a2 => ?_) (h2.weak' W) (h3.weak' W)⟩
    obtain ⟨_, rfl, b1⟩ := a1.weakU_inv W; exact h1 _ b1 a2.weak'_inv
  | sort h1 h2 h3 => exact ⟨_, .sort (h1.weak' W) (h2.weak' W) (h3.weak' W)⟩
  | @forallE _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 ih1 ih2 =>
    refine .forallE (h1.weak' W) (h2.weak' W) (h3.weak' W.cons) (h4.weak' W.cons) (h5.weak' W)
      (fun W' => (h6 (W.comp W')).cast SExpr.lift'_comp) (fun W' _ ha => ?_) (fun W' _ _ ab => ?_)
    · exact (h7 (W.comp W') ((LRDefEq.cast _).1 ha)).cast (SExpr.lift'_comp ▸ rfl)
    · exact (LREqTy.cast _).2 <| lift'_comp ▸ h8 (W.comp W') ((LRDefEq.cast _).1 ab)

open SExpr LogRel in
theorem LREqTy.weak' (W : Ctx.Lift' ρ Γ Δ) {J : Γ ⊩[u] A} (H : J ⊩≡ B) :
    J.weak' W ⊩≡ B.lift' ρ := by
  induction J using LRIsType.rec with
  | stuck => exact ⟨H.1.weak' W, ⟨⟩⟩
  | sort => exact ⟨H.1.weak' W, H.2.weak' W⟩
  | @forallE _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 ih1 ih2 =>
    let ⟨_, _, a1, a2, a3, a4⟩ := H.2
    refine ⟨H.1.weak' W, _, _, a1.weak' W, a2.weak' W, fun W' => ?_, fun W' _ ha => ?_⟩
    · refine (LREqTy.cast _).2 ?_; rw [← lift'_comp]; exact a3 (W.comp W')
    · refine (LREqTy.cast _).2 ?_; dsimp; rw [← lift'_comp]
      refine a4 (W.comp W') <| (LRHasTy.cast _).1 ha

open SExpr LogRel in
theorem LRDefEq.weak' (W : Ctx.Lift' ρ Γ Δ) {J : Γ ⊩[u] A} (H : J ⊩ a ≡ b) :
    J.weak' W ⊩ a.lift' ρ ≡ b.lift' ρ := by
  induction J using LRIsType.rec with
  | stuck | sort => exact ⟨H.1.weak' .weak' W, ⟨⟩, ⟨⟩, ⟨⟩⟩
  | @forallE _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 ih1 ih2 =>
    let ⟨a1, a2, a3⟩ := H.2
    refine ⟨H.1.weak' .weak' W, fun ab => ?_, fun ab => ?_, fun ha => ?_⟩
    · exact (LRDefEq.cast _).2 <| lift'_comp ▸ a1 ((LRDefEq.cast _).1 ab)
    · exact (LRDefEq.cast _).2 <| lift'_comp ▸ a2 ((LRDefEq.cast _).1 ab)
    · exact (LRDefEq.cast _).2 <| lift'_comp ▸ lift'_comp ▸ a3 ((LRHasTy.cast _).1 ha)

theorem LREqTy.defeq_r {J : Γ ⊩[u] A} (J' : Γ ⊩[u] B)
    (H : J ⊩≡ B) (H2 : J ⊩ a ≡ b) : J' ⊩ a ≡ b := sorry

def LREqTy.symm {J : Γ ⊩[u] A} (H : J ⊩≡ B) (J' : Γ ⊩[u] B) :
    {J' : Γ ⊩[u] B // J' ⊩≡ A} :=
  let ⟨_, J⟩ := J
  match J with
  | .stuck .. => sorry -- ⟨⟨_, .stuck _ H.1.hasType.2⟩, H.1.symm, ⟨⟩⟩
  | .sort .. => sorry -- ⟨⟨_, _⟩, _, _⟩
  | .forallE .. => sorry -- ⟨⟨_, _⟩, _, _⟩

nonrec theorem LRDefEq.symm {J : Γ ⊩[u] A} (H : J ⊩ a ≡ b) : J ⊩ b ≡ a := H.symm

open SExpr (Subst)

structure ClassifierV' where
  EqSubst : List SExpr → Subst → Subst → Prop := fun _ _ _ => True
  eqSubst_left : EqSubst Δ σ σ' → EqSubst Δ σ σ
def ClassifierV (_Γ : List SExpr) := ClassifierV'

def ClassifierV.IsTy (cl : ClassifierV Γ) (A : SExpr) (u : SLevel) : Type :=
  Γ ⊢ A : .sort u ×' ∀ {Δ σ}, cl.EqSubst Δ σ σ →
    { J : Δ ⊩[u] A.subst σ // ∀ σ', cl.EqSubst Δ σ σ' → J ⊩≡ A.subst σ' }

inductive LogRelV : ∀ Γ, ClassifierV Γ → Type where
  | nil : LogRelV [] { eqSubst_left := id }
  | cons : LogRelV Γ R → (JA : R.IsTy A u) → LogRelV (A::Γ) {
      EqSubst Δ σ σ' := ∃ hσ : R.EqSubst Δ σ.tail σ'.tail,
        (JA.2 (R.eqSubst_left hσ)).1 ⊩ σ.head ≡ σ'.head
      eqSubst_left := fun ⟨h1, h2⟩ => ⟨R.eqSubst_left h1, h2.left⟩ }

def LVIsCtx (Γ : List SExpr) := Σ R, LogRelV Γ R
local notation:65 "⊩ᵛ " Γ:36 => LVIsCtx Γ

def LVIsType {Γ : List SExpr} (J : ⊩ᵛ Γ) := J.1.IsTy
local notation:65 J " ⊩ᵛ["u"] " A:36 => LVIsType J A u

def LVEqSubst (Γ : List SExpr) (σ σ' : Subst) {Δ : List SExpr} (J : ⊩ᵛ Δ) := J.1.EqSubst Γ σ σ'
local notation:65 Γ " ⊩ˢ " σ " ≡ " σ' " : " J:36 => LVEqSubst Γ σ σ' J
local notation:65 Γ " ⊩ˢ " σ " : " J:36 => LVEqSubst Γ σ σ J

def LVIsCtx.nil : ⊩ᵛ [] := ⟨_, .nil⟩
def LVIsCtx.cons {J : ⊩ᵛ Γ} (JA : J ⊩ᵛ[u] A) : ⊩ᵛ A::Γ := ⟨_, .cons J.2 JA⟩

def LVIsType.sort : Γ ⊩ᵛ[u.succ] .sort u :=
  sorry -- ⟨.sort, fun _ => ⟨.sort _, fun _ _ => ⟨.sort, .rfl⟩⟩⟩

inductive LVIsCtxInv : ∀ {Γ}, ⊩ᵛ Γ → Prop
  | nil : LVIsCtxInv .nil
  | cons (J JA) : LVIsCtxInv (.cons (J := J) (u := u) (A := A) JA)

theorem LVIsCtx.inv (J : ⊩ᵛ Γ) : LVIsCtxInv J :=
  match Γ, J with
  | _, ⟨_, .nil⟩ => .nil
  | _, ⟨_, .cons ..⟩ => .cons ⟨_, _⟩ _

theorem LVEqSubst.left {J : ⊩ᵛ Δ} (H : Γ ⊩ˢ σ ≡ σ' : J) : Γ ⊩ˢ σ : J := J.1.eqSubst_left H

def LVIsType.subst {J : ⊩ᵛ Δ} (H : Γ ⊩ˢ σ : J) (JA : J ⊩ᵛ[u] A) :
    Γ ⊩[u] A.subst σ := (JA.2 H).1

theorem LVEqSubst.eqTy {J : ⊩ᵛ Δ} (H : Γ ⊩ˢ σ ≡ σ' : J) (JA : J ⊩ᵛ[u] A) :
    JA.subst H.left ⊩≡ A.subst σ' := (JA.2 H.left).2 _ H

def LVIsCtx.cons_inv (J : ⊩ᵛ A::Γ) : Σ' (J' : ⊩ᵛ Γ) (u:_) (JA : J' ⊩ᵛ[u] A), J = .cons JA :=
  let ⟨_, .cons J JA⟩ := J; ⟨⟨_, J⟩, _, JA, rfl⟩

theorem LVEqSubst.tail {J : ⊩ᵛ Δ} {JA : J ⊩ᵛ[u] A}
    (H : Γ ⊩ˢ σ ≡ σ' : .cons JA) : Γ ⊩ˢ σ.tail ≡ σ'.tail : J := let ⟨h, _⟩ := H; h

theorem LVEqSubst.head {J : ⊩ᵛ Δ} {JA : J ⊩ᵛ[u] A}
    (H : Γ ⊩ˢ σ ≡ σ' : .cons JA) : JA.subst H.tail.left ⊩ σ.head ≡ σ'.head := let ⟨_, h⟩ := H; h

def LVIsType.lift {J : ⊩ᵛ Γ} (JA : J ⊩ᵛ[u] A) (JB : J ⊩ᵛ[v] B) :
    J.cons JA ⊩ᵛ[v] B.lift := by
  refine ⟨JB.1.weak' .one, fun {Δ σ} (Hσ : LVEqSubst ..) => ⟨?_, fun σ' (Hσ : LVEqSubst ..) => ?_⟩⟩
  · exact (JB.subst (by exact Hσ.tail)).cast SExpr.subst_lift'.symm
  · stop
    refine .cast ?_ _; rw [SExpr.subst_lift']; exact Hσ.tail.eqTy JB

-- def LVEqSubst.lift {J : ⊩ᵛ Δ} {JA : J ⊩ᵛ[u] A} (JB : J ⊩ᵛ[v] B) :
--     Γ ⊩ˢ σ ≡ σ' : J.cons JA := by
--   refine ⟨JB.1.weak' .one, fun {Δ σ} (Hσ : LVEqSubst ..) => ⟨?_, fun σ' (Hσ : LVEqSubst ..) => ?_⟩⟩
--   · exact (JB.subst (by exact Hσ.tail)).cast SExpr.subst_lift'.symm
--   · refine .cast ?_ _; rw [SExpr.subst_lift']; exact Hσ.tail.eqTy JB

def LVEqTy {J : ⊩ᵛ Γ} (JA : J ⊩ᵛ[u] A) (B : SExpr) : Prop :=
  ∀ {Δ σ} (Jσ : Δ ⊩ˢ σ : J), JA.subst Jσ ⊩ A.subst σ ≡ B.subst σ
local notation:65 J " ⊩ᵛ≡ " B:36 => LVEqTy J B

def LVHasType {J : ⊩ᵛ Γ} (JA : J ⊩ᵛ[u] A) (a : SExpr) : Prop :=
  ∀ {Δ σ σ'} (H : Δ ⊩ˢ σ ≡ σ' : J), JA.subst H.left ⊩ a.subst σ ≡ a.subst σ'
local notation:65 J " ⊩ᵛ " a:36 => LVHasType J a

-- theorem LVEqSubst.hasType {J : ⊩ᵛ Δ} (Hσ : Γ ⊩ˢ σ ≡ σ' : J)
--     {JA : J ⊩ᵛ[u] A} (Ha : JA ⊩ᵛ a) : JA.subst Hσ.left ⊩ᵛ a.subst σ :=
--   _

-- def LVHasType.lift {J : ⊩ᵛ Γ} (JA : J ⊩ᵛ[u] A) {JB : J ⊩ᵛ[v] B} {Ha : JB ⊩ᵛ a} :
--     JA.lift JB ⊩ᵛ a.lift := by
--   refine fun Hσ => Hσ.eqTy _

def LVDefEq {J : ⊩ᵛ Γ} (JA : J ⊩ᵛ[u] A) (a b : SExpr) : Prop :=
  JA ⊩ᵛ a ∧ JA ⊩ᵛ b ∧ ∀ {Δ σ} (Jσ : Δ ⊩ˢ σ : J), JA.subst Jσ ⊩ a.subst σ ≡ b.subst σ
local notation:65 J " ⊩ᵛ " a " ≡ " b:36 => LVDefEq J a b

theorem LVDefEq.refl {J : ⊩ᵛ Γ} {JA : J ⊩ᵛ[u] A} (H : JA ⊩ᵛ a) : JA ⊩ᵛ a ≡ a := ⟨H, H, H⟩
theorem LVDefEq.symm {J : ⊩ᵛ Γ} {JA : J ⊩ᵛ[u] A} : JA ⊩ᵛ a ≡ b → JA ⊩ᵛ b ≡ a
  | ⟨h1, h2, h3⟩ => ⟨h2, h1, fun Hσ => (h3 Hσ).symm⟩

theorem fundamental (H : Γ ⊢ a ≡ b : A) (J : ⊩ᵛ Γ) :
    ∃ u, ∃ JA : J ⊩ᵛ[u] A, JA ⊩ᵛ a ≡ b := by
  induction H with
  | bvar h =>
    induction h with
    | zero =>
      let .cons _ JA := J.inv
      refine ⟨_, ⟨JA.1.weak' .one, fun (Hσ : LVEqSubst ..) => ?_⟩, .refl ?_⟩
      · stop
        exact ⟨(JA.subst Hσ.tail).cast (SExpr.subst_lift' ▸ rfl),
          fun σ' (Hσ : LVEqSubst ..) => .cast (SExpr.subst_lift' ▸ Hσ.tail.eqTy JA) _⟩
      · stop exact (·.2.cast _)
    | @succ _ n B _ h ih =>
      let .cons J JA := J.inv
      have ⟨u, JB, H⟩ := ih J
      refine ⟨_, JA.lift JB, .refl ?_⟩
      stop
      exact fun Hσ => ((H.1 Hσ.tail).cast (SExpr.subst_lift' ▸ rfl)).irrel
  | symm h ih => have ⟨u, JA, H⟩ := ih J; exact ⟨u, JA, H.symm⟩
  | trans _ _ ih1 ih2 =>
    have ⟨u, JA, H⟩ := ih1 J
    have ⟨u', JA', H⟩ := ih2 J
    sorry
  | @sort _ u =>
    stop
    exact ⟨.mk _, .sort, .refl fun _ => Classifier.defEq_self.2 ⟨.sort, ⟨⟩, ⟨⟩⟩⟩
  | _ => sorry
