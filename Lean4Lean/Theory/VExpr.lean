import Lean
import Lean4Lean.Theory.VLevel

namespace Lean4Lean
open Lean4Lean

inductive VExpr where
  | bvar (deBruijnIndex : Nat)
  | sort (u : VLevel)
  | const (declName : Name) (us : List VLevel)
  | app (fn arg : VExpr)
  | lam (binderType body : VExpr)
  | forallE (binderType body : VExpr)

instance : Inhabited VExpr := ⟨.sort .zero⟩

def liftVar (n i : Nat) (k := 0) : Nat := if i < k then i else n + i

theorem liftVar_lt (h : i < k) : liftVar n i k = i := if_pos h
theorem liftVar_le (h : k ≤ i) : liftVar n i k = n + i := if_neg (Nat.not_lt.2 h)

theorem liftVar_base : liftVar n i = n + i := liftVar_le (Nat.zero_le _)
@[simp] theorem liftVar_base' : liftVar n i = i + n := Nat.add_comm .. ▸ liftVar_le (Nat.zero_le _)

@[simp] theorem liftVar_zero : liftVar n 0 (k+1) = 0 := by simp [liftVar]
@[simp] theorem liftVar_succ : liftVar n (i+1) (k+1) = liftVar n i k + 1 := by
  simp [liftVar, Nat.succ_lt_succ_iff]; split <;> simp [Nat.add_assoc]

theorem liftVar_lt_add (self : i < k) : liftVar n i j < k + n := by
  simp [liftVar]
  split <;> rename_i h
  · exact Nat.lt_of_lt_of_le self (Nat.le_add_right ..)
  · rw [Nat.add_comm]; exact Nat.add_lt_add_right self _

namespace VExpr

variable (n : Nat) in
def liftN : VExpr → (k :_:= 0) → VExpr
  | .bvar i, k => .bvar (liftVar n i k)
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app fn arg, k => .app (fn.liftN k) (arg.liftN k)
  | .lam ty body, k => .lam (ty.liftN k) (body.liftN (k+1))
  | .forallE ty body, k => .forallE (ty.liftN k) (body.liftN (k+1))

abbrev lift := liftN 1

@[simp] theorem liftN_zero (e : VExpr) (k : Nat) : liftN 0 e k = e := by
  induction e generalizing k <;> simp [liftN, liftVar, *]

theorem liftN'_liftN' {e : VExpr} {n1 n2 k1 k2 : Nat} (h1 : k1 ≤ k2) (h2 : k2 ≤ n1 + k1) :
    liftN n2 (liftN n1 e k1) k2 = liftN (n1+n2) e k1 := by
  induction e generalizing k1 k2 with simp [liftN, liftVar, Nat.add_assoc, *]
  | bvar i =>
    split <;> rename_i h
    · rw [if_pos (Nat.lt_of_lt_of_le h h1)]
    · rw [if_neg (mt (fun h => ?_) h), Nat.add_left_comm]
      exact (Nat.add_lt_add_iff_left ..).1 (Nat.lt_of_lt_of_le h h2)
  | lam _ _ _ IH2 | forallE _ _ _ IH2 =>
    rw [IH2 (Nat.succ_le_succ h1) (Nat.succ_le_succ h2)]

theorem liftN'_liftN_lo (e : VExpr) (n k : Nat) : liftN n (liftN k e) k = liftN (n+k) e := by
  simpa [Nat.add_comm] using liftN'_liftN' (n1 := k) (n2 := n) (Nat.zero_le _) (Nat.le_refl _)

theorem liftN'_liftN_hi (e : VExpr) (n1 n2 k : Nat) :
    liftN n2 (liftN n1 e k) k = liftN (n1+n2) e k :=
  liftN'_liftN' (Nat.le_refl _) (Nat.le_add_left ..)

theorem liftN_liftN (e : VExpr) (n1 n2 : Nat) : liftN n2 (liftN n1 e) = liftN (n1+n2) e := by
  simpa using liftN'_liftN' (Nat.zero_le _) (Nat.zero_le _)

theorem liftN_succ (e : VExpr) (n : Nat) : liftN (n+1) e = lift (liftN n e) :=
  (liftN_liftN ..).symm

theorem liftN'_comm (e : VExpr) (n1 n2 k1 k2 : Nat) (h : k2 ≤ k1) :
    liftN n2 (liftN n1 e k1) k2 = liftN n1 (liftN n2 e k2) (n2+k1) := by
  induction e generalizing k1 k2 with
    simp [liftN, liftVar, Nat.add_assoc, Nat.succ_le_succ, *]
  | bvar i =>
    split <;> rename_i h'
    · rw [if_pos (c := _ < n2 + k1)]; split
      · exact Nat.lt_add_left _ h'
      · exact Nat.add_lt_add_left h' _
    · have := mt (Nat.lt_of_lt_of_le · h) h'
      rw [if_neg (mt (Nat.lt_of_le_of_lt (Nat.le_add_left _ n1)) this),
        if_neg this, if_neg (mt (Nat.add_lt_add_iff_left ..).1 h'), Nat.add_left_comm]

theorem lift_liftN' (e : VExpr) (k : Nat) : lift (liftN n e k) = liftN n (lift e) (k+1) :=
  Nat.add_comm .. ▸ liftN'_comm (h := Nat.zero_le _) ..

theorem sizeOf_liftN (e : VExpr) (k : Nat) : sizeOf e ≤ sizeOf (liftN n e k) := by
  induction e generalizing k with simp [liftN, Nat.add_assoc, Nat.add_le_add_iff_left]
  | bvar => simp [liftVar]; split <;> simp [Nat.le_add_left]
  | _ => rename_i ih1 ih2; exact Nat.add_le_add (ih1 _) (ih2 _)

@[simp] theorem liftN_default (n k : Nat) : liftN n default k = default := rfl
@[simp] theorem lift_default : lift default = default := rfl

def ClosedN : VExpr → (k :_:= 0) → Prop
  | .bvar i, k => i < k
  | .sort .., _ | .const .., _ => True
  | .app fn arg, k => fn.ClosedN k ∧ arg.ClosedN k
  | .lam ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)
  | .forallE ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)

abbrev Closed := ClosedN

instance decClosedN : ∀ (e : VExpr) (k : Nat), Decidable (e.ClosedN k)
  | .bvar _, _ => inferInstanceAs (Decidable (_ < _))
  | .sort .., _ | .const .., _ => .isTrue trivial
  | .app f a, k => @instDecidableAnd _ _ (decClosedN f k) (decClosedN a k)
  | .lam t b, k => @instDecidableAnd _ _ (decClosedN t k) (decClosedN b (k+1))
  | .forallE t b, k => @instDecidableAnd _ _ (decClosedN t k) (decClosedN b (k+1))

@[simp] theorem ClosedN.default : ClosedN default k := trivial

theorem ClosedN.mono (h : k ≤ k') (self : ClosedN e k) : ClosedN e k' := by
  induction e generalizing k k' with (simp [ClosedN] at self ⊢; try simp [self, *])
  | bvar i => exact Nat.lt_of_lt_of_le self h
  | app _ _ ih1 ih2 => exact ⟨ih1 h self.1, ih2 h self.2⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    exact ⟨ih1 h self.1, ih2 (Nat.succ_le_succ h) self.2⟩

theorem ClosedN.liftN_eq (self : ClosedN e k) (h : k ≤ j) : liftN n e j = e := by
  induction e generalizing k j with
    (simp [ClosedN] at self; simp [liftN, *])
  | bvar i => exact liftVar_lt (Nat.lt_of_lt_of_le self h)
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    exact ⟨ih1 self.1 h, ih2 self.2 (Nat.succ_le_succ h)⟩

theorem ClosedN.lift_eq (self : ClosedN e) : lift e = e := self.liftN_eq (Nat.zero_le _)

protected theorem ClosedN.liftN (self : ClosedN e k) : ClosedN (e.liftN n j) (k+n) := by
  induction e generalizing k j with
    (simp [ClosedN] at self; simp [VExpr.liftN, ClosedN, *])
  | bvar i => exact liftVar_lt_add self
  | lam _ _ _ ih2 | forallE _ _ _ ih2 => exact Nat.add_right_comm .. ▸ ih2 self.2

theorem ClosedN.liftN_eq_rev (self : ClosedN (liftN n e j) k) (h : k ≤ j) : liftN n e j = e := by
  induction e generalizing k j with
    (simp [liftN, ClosedN] at self; simp [liftN, *])
  | bvar i =>
    refine liftVar_lt (Nat.lt_of_lt_of_le ?_ h)
    unfold liftVar at self; split at self <;>
      [exact self; exact Nat.lt_of_le_of_lt (Nat.le_add_left ..) self]
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    exact ⟨ih1 self.1 h, ih2 self.2 (Nat.succ_le_succ h)⟩

variable (ls : List VLevel) in
def instL : VExpr → VExpr
  | .bvar i => .bvar i
  | .sort u => .sort (u.inst ls)
  | .const c us => .const c (us.map (VLevel.inst ls))
  | .app fn arg => .app fn.instL arg.instL
  | .lam ty body => .lam ty.instL body.instL
  | .forallE ty body => .forallE ty.instL body.instL

theorem ClosedN.instL : ∀ {e}, ClosedN e k → ClosedN (e.instL ls) k
  | .bvar .., h | .sort .., h | .const .., h => h
  | .app .., h | .lam .., h | .forallE .., h => ⟨h.1.instL, h.2.instL⟩

theorem ClosedN.instL_rev : ∀ {e}, ClosedN (e.instL ls) k → ClosedN e k
  | .bvar .., h | .sort .., h | .const .., h => h
  | .app .., h | .lam .., h | .forallE .., h => ⟨h.1.instL_rev, h.2.instL_rev⟩

@[simp] theorem instL_default : instL ls default = default := rfl

@[simp] theorem instL_liftN : (liftN n e k).instL ls = liftN n (e.instL ls) k := by
  cases e <;> simp [liftN, instL, instL_liftN]

theorem instL_instL {e : VExpr} : (e.instL ls).instL ls' = e.instL (ls.map (VLevel.inst ls')) := by
  cases e <;> simp [instL, instL_instL, Function.comp_def, VLevel.inst_inst]

def LevelWF (U : Nat) : VExpr → Prop
  | .bvar _ => True
  | .sort l => l.WF U
  | .const _ ls => ∀ l ∈ ls, l.WF U
  | .app e1 e2 | .lam e1 e2 | .forallE e1 e2 => e1.LevelWF U ∧ e2.LevelWF U

theorem LevelWF.instL_id {e : VExpr} (h : e.LevelWF U) : e.instL (VLevel.params U) = e := by
  induction e <;> simp_all [instL, LevelWF, VLevel.inst_id]
  case const => exact List.map_id''' _ fun _ h1 => VLevel.inst_id (h _ h1)

theorem levelWF_liftN : (liftN n e k).LevelWF U ↔ e.LevelWF U := by
  induction e generalizing k <;> simp [liftN, LevelWF, *]

theorem LevelWF.instL (h : ∀ l ∈ ls, l.WF U) : (instL ls e).LevelWF U := by
  induction e <;> simp [VExpr.instL, VLevel.WF.inst h, LevelWF, *]

alias ⟨LevelWF.liftN_rev, LevelWF.liftN⟩ := levelWF_liftN

def instVar (i : Nat) (e : VExpr) (k := 0) : VExpr :=
  if i < k then .bvar i else if i = k then liftN k e else .bvar (i - 1)

@[simp] theorem instVar_zero : instVar 0 e = e := liftN_zero ..
@[simp] theorem instVar_upper : instVar (i+1) e = .bvar i := rfl
@[simp] theorem instVar_lower : instVar 0 e (k+1) = .bvar 0 := by simp [instVar]
@[simp] theorem instVar_succ : instVar (i+1) e (k+1) = (instVar i e k).lift := by
  simp [instVar, Nat.succ_lt_succ_iff]; split <;> simp [lift, liftN]
  split <;> simp [liftN_liftN, liftN]
  have := Nat.lt_of_le_of_ne (Nat.not_lt.1 ‹_›) (Ne.symm ‹_›)
  let i+1 := i; rfl

theorem liftN_instVar_lo (n : Nat) (e : VExpr) (j k : Nat) (hj : k ≤ j) :
    liftN n (instVar i e j) k = instVar (liftVar n i k) e (n+j) := by
  simp [instVar]; split <;> rename_i h
  · rw [if_pos]; · rfl
    simp only [liftVar]; split <;> rename_i hk
    · exact Nat.lt_add_left _ h
    · exact Nat.add_lt_add_left h _
  split <;> rename_i h'
  · subst i
    rw [liftN'_liftN' (h1 := Nat.zero_le _) (h2 := hj), liftVar_le hj,
      if_neg (by simp), if_pos rfl, Nat.add_comm]
  · rw [Nat.not_lt] at h; rw [liftVar_le (Nat.le_trans hj h)]
    have hk := Nat.lt_of_le_of_ne h (Ne.symm h')
    let i+1 := i
    have := Nat.add_lt_add_left hk n
    rw [if_neg (Nat.lt_asymm this), if_neg (Nat.ne_of_gt this)]
    simp only [liftN]
    rw [liftVar_le (Nat.le_trans hj <| by exact Nat.le_of_lt_succ hk)]; rfl

theorem liftN_instVar_hi (i : Nat) (e2 : VExpr) (n k j : Nat) :
    liftN n (instVar i e2 j) (k+j) = instVar (liftVar n i (k+j+1)) (liftN n e2 k) j := by
  simp [instVar]; split <;> rename_i h
  · have := Nat.lt_add_left k h
    rw [liftVar_lt <| Nat.lt_succ_of_lt this, if_pos h]
    simp [liftN, liftVar_lt this]
  split <;> rename_i h'
  · subst i
    have := Nat.le_add_left j k
    simp [liftVar_lt (by exact Nat.lt_succ_of_le this)]
    rw [liftN'_comm (h := Nat.zero_le _), Nat.add_comm]
  · have hk := Nat.lt_of_le_of_ne (Nat.not_lt.1 h) (Ne.symm h')
    let i+1 := i
    simp [liftVar, Nat.succ_lt_succ_iff]; split <;> rename_i hi
    · simp [liftN, liftVar_lt hi]
    · have := Nat.lt_add_left n hk
      rw [if_neg (Nat.lt_asymm this), if_neg (Nat.ne_of_gt this)]
      simp [liftN]; rw [liftVar_le (Nat.not_lt.1 hi)]

@[simp] theorem instL_instVar : (instVar i e k).instL ls = instVar i (e.instL ls) k := by
  simp [instVar]; split <;> [skip; split] <;> simp [instL, instL_liftN]

def inst : VExpr → VExpr → (k :_:= 0) → VExpr
  | .bvar i, e, k => instVar i e k
  | .sort u, _, _ => .sort u
  | .const c us, _, _ => .const c us
  | .app fn arg, e, k => .app (fn.inst e k) (arg.inst e k)
  | .lam ty body, e, k => .lam (ty.inst e k) (body.inst e (k+1))
  | .forallE ty body, e, k => .forallE (ty.inst e k) (body.inst e (k+1))

@[simp] theorem inst_default : inst default e k = default := rfl

theorem liftN_instN_lo (n : Nat) (e1 e2 : VExpr) (j k : Nat) (hj : k ≤ j) :
    liftN n (e1.inst e2 j) k = (liftN n e1 k).inst e2 (n+j) := by
  induction e1 generalizing k j with
    simp [liftN, inst, instVar, Nat.add_le_add_iff_right, *]
  | bvar i => apply liftN_instVar_lo (hj := hj)
  | _ => rfl

theorem liftN_instN_hi (e1 e2 : VExpr) (n k j : Nat) :
    liftN n (e1.inst e2 j) (k+j) = (liftN n e1 (k+j+1)).inst (liftN n e2 k) j := by
  induction e1 generalizing j with simp [liftN, inst, instVar, *]
  | bvar i => apply liftN_instVar_hi
  | _ => rename_i IH; apply IH

theorem liftN_inst_hi (e1 e2 : VExpr) (n k : Nat) :
    liftN n (e1.inst e2) k = (liftN n e1 (k+1)).inst (liftN n e2 k) := liftN_instN_hi ..

theorem lift_instN_lo (e1 e2 : VExpr) : lift (e1.inst e2 k) = (lift e1).inst e2 (k + 1) :=
  Nat.add_comm .. ▸ liftN_instN_lo (hj := Nat.zero_le _) ..

theorem lift_inst_hi (e1 e2 : VExpr) : lift (e1.inst e2) = (liftN 1 e1 1).inst (lift e2) :=
  liftN_instN_hi ..

theorem inst_liftN (e1 e2 : VExpr) : (liftN 1 e1 k).inst e2 k = e1 := by
  induction e1 generalizing k with simp [liftN, inst, *]
  | bvar i =>
    simp only [liftVar, instVar, Nat.add_comm 1]; split <;> [rfl; rename_i h]
    rw [if_neg (mt (Nat.lt_of_le_of_lt (Nat.le_succ _)) h),
      if_neg (mt (by rintro rfl; apply Nat.lt_succ_self) h)]; rfl

theorem inst_liftN' (e1 e2 : VExpr) : (liftN (n+1) e1 k).inst e2 k = liftN n e1 k := by
  rw [← liftN'_liftN_hi, inst_liftN]

/-- Instantiating *above* a lift: the variable substituted for is one the lift introduced, so it
is consumed and the lift shrinks by one. `inst_liftN'` is the case `n = 0`, where the lift and
the instantiation sit at the same index; here the instantiation has walked `n` binders past it. -/
theorem inst_liftN_lo' (e1 e2 : VExpr) (n k : Nat) :
    (liftN (n+1) e1 k).inst e2 (n+k) = liftN n e1 k := by
  have h := liftN_instN_lo n (liftN 1 e1 k) e2 k k (Nat.le_refl _)
  rw [inst_liftN, liftN'_liftN_hi, Nat.add_comm 1 n] at h
  exact h.symm

/-- The `k = 0` case, which is the one that arises when a telescope of binders is instantiated
one at a time: the index counts down while the lift stays at the bottom. Stated separately
because `n + k` does not unify with a literal index while `k` is open. -/
theorem inst_liftN_lo (e1 e2 : VExpr) (n : Nat) :
    (liftN (n+1) e1 0).inst e2 n = liftN n e1 0 := by
  simpa using inst_liftN_lo' e1 e2 n 0

theorem inst_lift (e1 e2 : VExpr) : (lift e1).inst e2 = e1 := inst_liftN ..

/-- Eta's identity: a lift at `k+1` steps over the variable at `k`, so substituting that variable
back for itself undoes the lift. This is what makes `f.lift` applied to `bvar 0` under a binder
the same as `f`'s body -- the shape a codomain read off `whnf` has when it is closed back over
the binder it was opened at. -/
theorem inst_liftN_bvar : ∀ (e : VExpr) (k : Nat), (liftN 1 e (k+1)).inst (.bvar 0) k = e
  | .bvar i, k => by
    simp only [liftN, inst, instVar, liftVar]
    split <;> rename_i h₁
    · rcases Nat.lt_or_ge i k with h | h
      · rw [if_pos h]
      · have : i = k := by omega
        subst this; rw [if_neg (Nat.lt_irrefl _), if_pos rfl]; simp
    · rw [if_neg (by omega), if_neg (by omega)]; congr 1; omega
  | .sort .., _ | .const .., _ => rfl
  | .app .., k => by simp only [liftN, inst, inst_liftN_bvar]
  | .lam .., k | .forallE .., k => by simp only [liftN, inst, inst_liftN_bvar]

/-- Substitute a value for each of a telescope of binders, `inst` at index 0 once per binder.
The list is in telescope order -- leftmost is the *outermost* binder, the same order `appN`
applies its arguments in -- so the substitutions happen right to left, the innermost binder
(`bvar 0`) taking the last element.

This is a *substitution* rather than an abstraction applied to arguments (`mkLambda'` then
`appN`), even though the two are beta-equivalent: statements built out of substituted pieces
decompose on the nose, since substitution commutes with application syntactically, while an
applied abstraction does so only up to defeq. -/
def insts (e : VExpr) : List VExpr → VExpr
  | [] => e
  | a :: as => (e.insts as).inst a

@[simp] theorem insts_nil (e : VExpr) : e.insts [] = e := rfl

@[simp] theorem insts_cons (e a : VExpr) (as) : e.insts (a :: as) = (e.insts as).inst a := rfl

/-- Substituting a telescope is substituting its outer half after its inner half. This is what
turns an induction that peels the *innermost* binder -- the only one a list of types can be
taken apart at -- into a statement about `insts`. -/
theorem insts_append (e : VExpr) : ∀ (as bs : List VExpr),
    e.insts (as ++ bs) = (e.insts bs).insts as
  | [], _ => rfl
  | a :: as, bs => by simp [insts_append e as bs]

@[simp] theorem insts_sort (u) : ∀ as, (VExpr.sort u).insts as = .sort u
  | [] => rfl
  | _ :: as => by simp [insts_sort u as, inst]

@[simp] theorem insts_const (c us) : ∀ as, (VExpr.const c us).insts as = .const c us
  | [] => rfl
  | _ :: as => by simp [insts_const c us as, inst]

@[simp] theorem insts_app (e1 e2 : VExpr) :
    ∀ as, (e1.app e2).insts as = (e1.insts as).app (e2.insts as)
  | [] => rfl
  | _ :: as => by simp [insts_app e1 e2 as, inst]

protected theorem LevelWF.inst
    (h1 : e1.LevelWF U) (h2 : e2.LevelWF U) : (inst e1 e2 k).LevelWF U := by
  induction e1 generalizing k <;> simp_all [inst, instVar, LevelWF]
  case bvar => split <;> [trivial; split <;> [exact h2.liftN; trivial]]

def unliftN (e : VExpr) (n k : Nat) : VExpr :=
  match n with
  | 0 => e
  | n+1 => unliftN (e.inst default k) n k

@[simp] theorem unliftN_liftN : unliftN (liftN n e k) n k = e := by
  induction n <;> simp [unliftN, inst_liftN', *]

theorem unliftN_add : unliftN e (n1+n2) k = unliftN (unliftN e n1 k) n2 k := by
  induction n1 generalizing e <;> simp [unliftN, Nat.succ_add, *]

theorem unliftN_succ' : unliftN e (n+1) k = (unliftN e n k).inst default k := by
  rw [unliftN_add]; rfl

theorem liftN_unliftN_hi (h : k2 ≤ k1) :
    liftN n1 (unliftN e n2 k2) k1 = unliftN (liftN n1 e (k1+n2)) n2 k2 := by
  obtain ⟨k1, rfl⟩ := Nat.le_iff_exists_add'.1 h
  induction n2 generalizing e with simp [unliftN]
  | succ n2 ih =>
    rw [ih, Nat.add_right_comm, liftN_instN_hi e default n1 (k1+n2) k2,
      Nat.add_right_comm k1]; rfl

def Skips (e : VExpr) (n k : Nat) : Prop := liftN n (unliftN e n k) k = e

protected theorem Skips.liftN : Skips (liftN n e k) n k := by simp [Skips]

theorem skips_iff_exists : Skips e n k ↔ ∃ e', e = liftN n e' k :=
  ⟨fun h => ⟨_, h.symm⟩, fun ⟨_, h⟩ => h ▸ .liftN⟩

theorem Skips.zero : Skips e 0 k := by simp [Skips, unliftN]

theorem liftN_inj : liftN n e1 k = liftN n e2 k ↔ e1 = e2 :=
  ⟨fun H => by rw [← unliftN_liftN (e := e1), H, unliftN_liftN], (· ▸ rfl)⟩

theorem liftVar_inj : liftVar n i k = liftVar n i' k ↔ i = i' := by
  simpa [liftN] using @liftN_inj n (.bvar i) k (.bvar i')

theorem Skips.of_liftN_hi (self : (liftN n1 e k1).Skips n2 k2) (h : n2 + k2 ≤ k1) :
    e.Skips n2 k2 := by
  obtain ⟨k1, rfl⟩ := Nat.le_iff_exists_add'.1 h
  rwa [Skips, Nat.add_comm n2, ← Nat.add_assoc, ← liftN_unliftN_hi (Nat.le_add_left ..),
    liftN'_comm (h := Nat.le_add_left ..), Nat.add_comm, liftN_inj] at self

theorem skips_add : Skips e (n1+n2) k ↔ ∃ e', Skips e' n1 k ∧ e = liftN n2 e' k := by
  simp [skips_iff_exists, ← liftN'_liftN_hi]
  exact ⟨fun ⟨_, h⟩ => ⟨_, ⟨_, rfl⟩, h⟩, fun ⟨_, ⟨_, rfl⟩, h⟩ => ⟨_, h⟩⟩

def Skips' (n : Nat) : VExpr → (k :_:= 0) → Prop
  | .bvar i, k => i < k + n → i < k
  | .sort .., _ | .const .., _ => True
  | .app fn arg, k => fn.Skips' n k ∧ arg.Skips' n k
  | .lam ty body, k => ty.Skips' n k ∧ body.Skips' n (k+1)
  | .forallE ty body, k => ty.Skips' n k ∧ body.Skips' n (k+1)

theorem skips_iff : Skips e n k ↔ Skips' n e k := by
  induction n generalizing e with
  | zero => simp [Skips, unliftN]; induction e generalizing k <;> simp [Skips', *]
  | succ n ih =>
    simp [skips_add, ih]; clear ih
    induction e generalizing k with
    | bvar i =>
      refine ⟨fun ⟨e', h1, h2⟩ => ?_, fun h => ?_⟩
      · cases e' <;> cases h2; simp [Skips', liftVar]; split
        · intro; assumption
        · next h2 =>
          rw [Nat.add_comm, ← Nat.add_assoc, Nat.succ_lt_succ_iff]
          exact fun h => h2.elim (h1 h)
      · simp [Skips'] at h
        if h' : i < k + n + 1 then
          exact ⟨.bvar i, fun _ => h h', by simp [liftN, liftVar, h h']⟩
        else
          have := Nat.not_lt.1 h'
          let i+1 := i; rw [Nat.add_lt_add_iff_right] at h'
          have := mt (Nat.lt_of_lt_of_le · (Nat.le_add_right ..)) h'
          exact ⟨.bvar i, h'.elim, by simp [liftN, liftVar]; rw [if_neg this, Nat.add_comm]⟩
    | sort u =>
      refine ⟨fun ⟨e', h1, h2⟩ => ?_, fun _ => ⟨.sort u, by simp [Skips', liftN]⟩⟩
      cases e' <;> cases h2; simp [Skips']
    | const c ls =>
      refine ⟨fun ⟨e', h1, h2⟩ => ?_, fun _ => ⟨.const c ls, by simp [Skips', liftN]⟩⟩
      cases e' <;> cases h2; simp [Skips']
    | app f a fIH aIH =>
      simp [Skips', ← fIH, ← aIH]; refine ⟨fun ⟨e', h1, h2⟩ => ?_, ?_⟩
      · cases e' <;> cases h2; exact ⟨⟨_, h1.1, rfl⟩, ⟨_, h1.2, rfl⟩⟩
      · rintro ⟨⟨e1, h1, rfl⟩, ⟨e2, h2, rfl⟩⟩; exact ⟨.app .., ⟨h1, h2⟩, rfl⟩
    | forallE f a fIH aIH =>
      simp [Skips', ← fIH, ← aIH]; refine ⟨fun ⟨e', h1, h2⟩ => ?_, ?_⟩
      · cases e' <;> cases h2; exact ⟨⟨_, h1.1, rfl⟩, ⟨_, h1.2, rfl⟩⟩
      · rintro ⟨⟨e1, h1, rfl⟩, ⟨e2, h2, rfl⟩⟩; exact ⟨.forallE .., ⟨h1, h2⟩, rfl⟩
    | lam f a fIH aIH =>
      simp [Skips', ← fIH, ← aIH]; refine ⟨fun ⟨e', h1, h2⟩ => ?_, ?_⟩
      · cases e' <;> cases h2; exact ⟨⟨_, h1.1, rfl⟩, ⟨_, h1.2, rfl⟩⟩
      · rintro ⟨⟨e1, h1, rfl⟩, ⟨e2, h2, rfl⟩⟩; exact ⟨.lam .., ⟨h1, h2⟩, rfl⟩

theorem of_liftN_eq_liftN (h : liftN n1 e1 (k1+n2+k2) = liftN n2 e2 k2) :
    ∃ e', e1 = liftN n2 e' k2 ∧ e2 = liftN n1 e' (k1+k2) := by
  have : (liftN n1 e1 (k1+n2+k2)).Skips n2 k2 := h ▸ .liftN
  obtain ⟨e', rfl⟩ := skips_iff_exists.1 <|
    this.of_liftN_hi (Nat.add_assoc .. ▸ Nat.le_add_left ..)
  refine ⟨e', rfl, ?_⟩
  rw [← liftN_inj, ← h, liftN'_comm (n1 := n1) (h := Nat.le_add_left ..),
    Nat.add_left_comm, Nat.add_assoc]

@[simp] theorem instL_instN {e1 e2 : VExpr} :
    (e1.inst e2 k).instL ls = (e1.instL ls).inst (e2.instL ls) k := by
  induction e1 generalizing k <;> simp [instL, inst, *]

theorem instL_unliftN : instL ls (unliftN e n k) = unliftN (instL ls e) n k := by
  induction n generalizing e with simp [unliftN]
  | succ _ ih => rw [ih, instL_instN]; rfl

theorem Skips.of_instL (self : (instL ls e).Skips n k) : e.Skips n k := by
  rw [skips_iff] at self ⊢
  induction e generalizing k <;> simp_all [Skips', instL]

theorem of_liftN_eq_instL (h : liftN n e1 k = instL ls e2) :
    ∃ e', e1 = instL ls e' ∧ e2 = liftN n e' k := by
  have : (instL ls e2).Skips n k := h ▸ .liftN
  obtain ⟨e', rfl⟩ := skips_iff_exists.1 this.of_instL
  refine ⟨e', ?_, rfl⟩
  rw [← liftN_inj, h, instL_liftN]

theorem ClosedN.instN_eq (self : ClosedN e1 k) (h : k ≤ j) : e1.inst e2 j = e1 := by
  conv => lhs; rw [← self.liftN_eq (n := 1) h]
  rw [inst_liftN]

theorem ClosedN.instN (h1 : ClosedN e (k+j+1)) (h2 : ClosedN e2 k) : ClosedN (e.inst e2 j) (k+j) :=
  match e, h1 with
  | .bvar i, h => by
    simp [inst, instVar]; split <;> rename_i h1
    · exact Nat.lt_of_lt_of_le h1 (Nat.le_add_left ..)
    split <;> rename_i h1'
    · exact h2.liftN
    · have hk := Nat.lt_of_le_of_ne (Nat.not_lt.1 h1) (Ne.symm h1')
      let i+1 := i
      exact Nat.lt_of_succ_lt_succ h
  | .sort .., h | .const .., h => h
  | .app .., h => ⟨h.1.instN h2, h.2.instN h2⟩
  | .lam .., h | .forallE .., h => ⟨h.1.instN h2, h.2.instN (j := j+1) h2⟩

theorem ClosedN.inst (h1 : ClosedN e (k+1)) (h2 : ClosedN e2 k) : ClosedN (e.inst e2) k :=
  h1.instN (j := 0) h2

theorem inst_instVar_hi (i : Nat) (e2 e3 : VExpr) (k j : Nat) :
    inst (instVar i e2 k) e3 (j+k) = (instVar i e3 (j+k+1)).inst (e2.inst e3 j) k := by
  simp [instVar]; split <;> rename_i h
  · simp [Nat.lt_succ_of_lt, inst, instVar, h, Nat.lt_of_lt_of_le h (Nat.le_add_left k j)]
  split <;> rename_i h'
  · subst i
    simp [Nat.lt_succ_of_le, Nat.le_add_left, inst, instVar]
    rw [liftN_instN_lo k e2 e3 j _ (Nat.zero_le _), Nat.add_comm]
  · have hk := Nat.lt_of_le_of_ne (Nat.not_lt.1 h) (Ne.symm h')
    let i+1 := i
    simp [inst, instVar]; split <;> rename_i hi
    · simp [inst, instVar, h, h']
    split <;> rename_i hi'
    · subst i
      suffices liftN (j+k+1) .. = _ by rw [this]; exact (inst_liftN ..).symm
      exact (liftN'_liftN' (Nat.zero_le _) (Nat.le_add_left k j)).symm
    · have hk := Nat.lt_of_le_of_ne (Nat.not_lt.1 hi) (Ne.symm hi')
      let i+1 := i
      simp [inst, instVar]
      have := Nat.lt_of_le_of_lt (Nat.le_add_left ..) hk
      rw [if_neg (Nat.lt_asymm this), if_neg (Nat.ne_of_gt this)]

theorem inst_inst_hi (e1 e2 e3 : VExpr) (k j : Nat) :
    inst (e1.inst e2 k) e3 (j+k) = (e1.inst e3 (j+k+1)).inst (e2.inst e3 j) k := by
  induction e1 generalizing k with simp [inst, instVar, *]
  | bvar i => apply inst_instVar_hi
  | _ => rename_i IH; apply IH

theorem inst0_inst_hi (e1 e2 e3 : VExpr) (j : Nat) :
    inst (e1.inst e2) e3 j = (e1.inst e3 (j+1)).inst (e2.inst e3 j) := inst_inst_hi ..

theorem inst_instVar_lo (i : Nat) (e2 e3 : VExpr) (k j : Nat) :
    inst (instVar i e2 (k+j+1)) e3 j =
    (instVar i (e3.liftN 1 k) j).inst e2 (k+j) := by
  simp [instVar]; split <;> rename_i h
  · split <;> rename_i h1
    · simp only [inst, instVar, h1, reduceIte]
      rw [if_pos (Nat.lt_of_lt_of_le h1 (Nat.le_add_left ..))]
    split <;> rename_i h1'
    · subst i
      simp [inst, instVar]; rw [liftN'_comm (h := Nat.zero_le _), Nat.add_comm]
      exact (inst_liftN ..).symm
    · have hj := Nat.lt_of_le_of_ne (Nat.not_lt.1 h1) (Ne.symm h1')
      let i+1 := i
      simp [inst, instVar, h1, h1', Nat.lt_of_succ_lt_succ h]
  split <;> rename_i h'
  · subst i
    have := Nat.lt_succ_of_le (Nat.le_add_left j k)
    rw [if_neg (Nat.lt_asymm this), if_neg (Nat.ne_of_gt this)]
    simp [inst, instVar]
    suffices liftN (k+j+1) .. = _ by rw [this]; exact inst_liftN ..
    exact (liftN'_liftN' (Nat.zero_le _) (Nat.le_add_left j k)).symm
  · have hk := Nat.lt_of_le_of_ne (Nat.not_lt.1 h) (Ne.symm h')
    let i+1 := i
    have hk := Nat.lt_of_add_lt_add_right hk
    simp [inst, instVar]
    have := Nat.lt_of_le_of_lt (Nat.le_add_left ..) hk
    rw [if_neg (Nat.lt_asymm this), if_neg (Nat.ne_of_gt this)]
    have := Nat.lt_succ_of_lt this
    rw [if_neg (Nat.lt_asymm this), if_neg (Nat.ne_of_gt this)]
    simp [inst, instVar]
    rw [if_neg (Nat.lt_asymm hk), if_neg (Nat.ne_of_gt hk)]

theorem inst_inst_lo (e1 e2 e3 : VExpr) (k j : Nat) :
    inst (e1.inst e2 (k+j+1)) e3 j =
    (e1.inst (e3.liftN 1 k) j).inst e2 (k+j) := by
  induction e1 generalizing j with simp [inst, instVar, *]
  | bvar i => apply inst_instVar_lo
  | _ => rename_i IH; exact IH (j+1)

theorem instN_bvar0 (e : VExpr) (k : Nat) :
    inst (e.liftN 1 (k+1)) (.bvar 0) k = e := by
  induction e generalizing k with simp [liftN, inst, *]
  | bvar i => induction i generalizing k <;> cases k <;> simp [*, lift, liftN]

end VExpr

inductive Lift : Type where
  | refl : Lift
  | skip : Lift → Lift
  | cons : Lift → Lift

namespace Lift

@[simp] def skipN (l : Lift) : Nat → Lift
  | 0   => l
  | n+1 => .skip (skipN l n)

theorem skipN_one : skipN l 1 = .skip l := rfl

theorem skipN_skipN : skipN (skipN l n) k = skipN l (n + k) := by induction k <;> simp [*]

@[simp] def consN (l : Lift) : Nat → Lift
  | 0  => l
  | k+1 => .cons (consN l k)

theorem consN_consN : consN (.consN l a) b = .consN l (a + b) := by
  induction b <;> simp [*]

@[simp] def comp (l₁ l₂ : Lift) : Lift :=
  match l₂, l₁ with
  | .refl,    l₁       => l₁
  | .skip l₂, l₁       => .skip (l₁.comp l₂)
  | .cons l₂, .refl    => .cons l₂
  | .cons l₂, .skip l₁ => .skip (l₁.comp l₂)
  | .cons l₂, .cons l₁ => .cons (l₁.comp l₂)

@[simp] theorem refl_comp : comp refl l = l := by induction l <;> simp [*]

theorem consN_comp : consN (.comp l₁ l₂) n = .comp (.consN l₁ n) (.consN l₂ n) := by
  induction n <;> simp [*]

@[simp] def dom : Lift → Nat
  | .refl   => 0
  | .skip l => l.dom
  | .cons l => l.dom + 1

@[simp] def size : Lift → Nat
  | .refl   => 0
  | .skip l => l.size + 1
  | .cons l => l.size + 1

@[simp] def depth : Lift → Nat
  | .refl   => 0
  | .skip l => l.depth + 1
  | .cons l => l.depth

theorem dom_add_depth : dom l + depth l = size l := by induction l <;> simp! <;> omega

theorem depth_comp : depth (.comp l₁ l₂) = l₁.depth + l₂.depth :=
  match l₂, l₁ with
  | .refl,    _        => rfl
  | .skip _,  _        => congrArg Nat.succ depth_comp
  | .cons _,  .refl    => (Nat.zero_add _).symm
  | .cons _,  .skip _  => (congrArg Nat.succ depth_comp).trans (Nat.succ_add ..).symm
  | .cons l₂, .cons l₁ => @depth_comp l₁ l₂

@[simp] theorem depth_consN : depth (.consN l n) = l.depth := by induction n <;> simp [*]

@[simp] theorem depth_skipN : depth (.skipN l n) = l.depth + n := by
  induction n <;> simp [Nat.add_assoc, *]

theorem consN_skip_eq : consN (skip l) k = comp (consN l k) (consN (skip refl) k) := by
  rw [← consN_comp]; rfl

theorem depth_succ (H : l.depth = n + 1) :
    ∃ l' k, depth l' = n ∧ l = consN (.skip l') k := by
  match l with
  | .skip l => cases H; exact ⟨l, 0, rfl, rfl⟩
  | .cons l =>
    obtain ⟨l, k, rfl, ⟨⟩⟩ := depth_succ (l := l) H
    exact ⟨l, k+1, rfl, rfl⟩

theorem depth_succ' (H : l.depth = n + 1) :
    ∃ l' k, depth l' = n ∧ l = comp l' (.consN (.skip refl) k) := by
  let ⟨l', k, h1, h2⟩ := depth_succ H
  exact ⟨.consN l' k, k, by simp [h1], by rwa [← consN_skip_eq]⟩

theorem comp_skipN : comp l₁ (skipN l₂ k) = skipN (comp l₁ l₂) k := by
  induction k <;> simp [*]

theorem skipN_comp_consN : comp (skipN l₁ k) (consN l₂ k) = skipN (comp l₁ l₂) k := by
  induction k <;> simp [*]

@[simp] protected def liftVar : Lift → Nat → Nat
  | .refl, n => n
  | .skip l, n => l.liftVar n + 1
  | .cons _, 0 => 0
  | .cons l, n+1 => l.liftVar n + 1

theorem liftVar_comp : (comp l₁ l₂).liftVar n = l₂.liftVar (l₁.liftVar n) := by
  induction l₂ generalizing l₁ n <;> [skip; skip; cases l₁ <;> [skip; skip; cases n]] <;> simp [*]

theorem liftVar_skipN : (skipN l n).liftVar i = l.liftVar i + n := by
  induction n generalizing i with
  | zero => rfl
  | succ _ ih => simp [ih]; rfl

theorem liftVar_consN_skipN : (consN (skipN refl n) k).liftVar i = liftVar n i k := by
  induction k generalizing i with
  | zero => simp [liftVar_skipN]
  | succ k ih =>
    cases i with simp [liftVar, Nat.succ_lt_succ_iff, ih]
    | succ i => split <;> rfl

theorem liftVar_depth_zero (H : depth l = 0) : l.liftVar n = n := by
  induction l generalizing n <;> [skip; skip; cases n] <;> simp_all [depth]

theorem le_liftVar {l : Lift} : n ≤ l.liftVar n := by
  induction l generalizing n <;> [skip; skip; cases n] <;> simp_all; grind

def inter : Lift → Lift → Lift
  | refl, l | l, refl => l
  | skip l₁, skip l₂ | skip l₁, cons l₂ | cons l₁, skip l₂ => skip (l₁.inter l₂)
  | cons l₁, cons l₂ => cons (l₁.inter l₂)

theorem inter_self : inter l l = l := by induction l <;> simp! [*]

theorem inter_comm : inter l₁ l₂ = inter l₂ l₁ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp! [*]

theorem inter_assoc : inter (inter l₁ l₂) l₃ = inter l₁ (inter l₂ l₃) := by
  induction l₁ generalizing l₂ l₃ <;> cases l₂ <;> cases l₃ <;> simp! [*]

@[simp] def diff : Lift → Lift → Lift
  | refl, _ => refl
  | l, refl => l
  | skip l₁, skip l₂ | cons l₁, skip l₂ => diff l₁ l₂
  | skip l₁, cons l₂ => skip (diff l₁ l₂)
  | cons l₁, cons l₂ => cons (l₁.diff l₂)

@[simp] theorem diff_refl : diff l refl = l := by cases l <;> simp!

theorem diff_comp : comp (diff l₁ l₂) l₂ = inter l₁ l₂ := by
  induction l₁ generalizing l₂ <;> cases l₂ <;> simp! [*]

def Fixes : Nat → Lift → Prop
  | 0,   _       => True
  | _,   .refl   => True
  | _+1, .skip _ => False
  | n+1, .cons l => Fixes n l

theorem Fixes.zero : Fixes 0 ρ := by simp [Fixes]

theorem Fixes.liftVar_eq {ρ : Lift} (H : ρ.Fixes k) (h2 : i < k) : ρ.liftVar i = i := by
  induction ρ generalizing i k with
  | refl => rfl
  | skip => let k+1 := k; cases H
  | cons ρ ih =>
    let k+1 := k
    cases i with
    | zero => rfl
    | succ k => exact congrArg Nat.succ <| ih H (Nat.lt_of_succ_lt_succ h2)

end Lift

namespace VExpr

@[simp] def lift' : VExpr → Lift → VExpr
  | .bvar i, k => .bvar (k.liftVar i)
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app fn arg, k => .app (fn.lift' k) (arg.lift' k)
  | .lam ty body, k => .lam (ty.lift' k) (body.lift' k.cons)
  | .forallE ty body, k => .forallE (ty.lift' k) (body.lift' k.cons)

theorem lift'_consN_skipN : e.lift' (.consN (.skipN .refl n) k) = liftN n e k := Eq.symm <| by
  induction e generalizing k <;> simp [liftN, Lift.liftVar_consN_skipN, *]

theorem lift'_comp {e : VExpr} : e.lift' (.comp l₁ l₂) = (e.lift' l₁).lift' l₂ := Eq.symm <| by
  induction e generalizing l₁ l₂ <;> simp [Lift.liftVar_comp, *]

theorem lift'_depth_zero {e : VExpr} (H : l.depth = 0) : e.lift' l = e := by
  induction e generalizing l <;> simp_all [Lift.liftVar_depth_zero]

@[simp] theorem lift'_refl {e : VExpr} : e.lift' .refl = e := lift'_depth_zero rfl

theorem lift_eq_lift' {e : VExpr} : e.lift = e.lift' (.skip .refl) := by
  rw [lift, ← lift'_consN_skipN]; rfl

@[simp] theorem instL_lift' : (lift' e ρ).instL ls = lift' (e.instL ls) ρ := by
  cases e <;> simp [lift', instL, instL_lift']

theorem ClosedN.lift'_eq (self : ClosedN e k) (h : ρ.Fixes k) : lift' e ρ = e := by
  induction e generalizing k ρ with (simp [ClosedN] at self; simp [*])
  | bvar i => exact h.liftVar_eq self
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩

def Subst := Nat → VExpr

def Subst.Depth (σ : Subst) (n n' : Nat) := ∀ i, σ (i + n') = .bvar (i + n)

def Subst.lift (σ : Subst) : Subst
  | 0 => .bvar 0
  | i+1 => (σ i).lift

def Subst.liftN (σ : Subst) : Nat → Subst
  | 0 => σ
  | k+1 => (σ.liftN k).lift

def subst : VExpr → Subst → VExpr
  | .bvar i, σ => σ i
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app fn arg, σ => .app (fn.subst σ) (arg.subst σ)
  | .lam ty body, σ => .lam (ty.subst σ) (body.subst σ.lift)
  | .forallE ty body, σ => .forallE (ty.subst σ) (body.subst σ.lift)

@[simp] theorem subst_bvar (i) (σ : Subst) : (VExpr.bvar i).subst σ = σ i := rfl
@[simp] theorem subst_sort (u) (σ : Subst) : (VExpr.sort u).subst σ = .sort u := rfl
@[simp] theorem subst_const (c us) (σ : Subst) : (VExpr.const c us).subst σ = .const c us := rfl
@[simp] theorem subst_app (e1 e2 : VExpr) (σ : Subst) :
    (e1.app e2).subst σ = (e1.subst σ).app (e2.subst σ) := rfl

def Subst.lift_r (σ : Subst) (ρ : Lift) : Subst := fun x => (σ x).lift' ρ
def Subst.lift_l (ρ : Lift) (σ : Subst) : Subst := fun x => σ (ρ.liftVar x)

theorem Subst.lift_l_lift {σ : Subst} {ρ} : (σ.lift_l ρ).lift = σ.lift.lift_l ρ.cons := by
  funext i; cases i <;> simp! [lift_l]

theorem Subst.lift_r_lift {σ : Subst} {ρ} : (σ.lift_r ρ).lift = σ.lift.lift_r ρ.cons := by
  funext i; cases i <;> simp! [lift, lift_r, ← lift'_comp, lift_eq_lift']

theorem subst_lift' {e : VExpr} : (e.lift' ρ).subst σ = subst e (.lift_l ρ σ) := by
  induction e generalizing ρ σ <;> simp! [*, Subst.lift_l_lift]; rfl

theorem lift'_subst {e : VExpr} : (e.subst σ).lift' ρ = subst e (.lift_r σ ρ) := by
  induction e generalizing ρ σ <;> simp! [*, Subst.lift_r, Subst.lift_r_lift]

/-- Composition of substitutions; `subst_subst` says it is what running two in a row does. This
is the counterpart of `Subst.comp` in `Experimental/SExpr.lean`, where the same API is proved
out. -/
def Subst.comp (σ σ' : Subst) : Subst := fun x => (σ x).subst σ'

theorem Subst.comp_lift {σ σ' : Subst} : (σ.comp σ').lift = σ.lift.comp σ'.lift := by
  funext i; cases i <;> simp! [comp, Subst.lift]
  rw [lift_eq_lift', lift_eq_lift', lift'_subst, subst_lift']
  congr 1; funext i; simp [Subst.lift_r, Subst.lift_l, Subst.lift, lift_eq_lift']

theorem subst_subst {e : VExpr} : (e.subst σ).subst σ' = subst e (.comp σ σ') := by
  induction e generalizing σ σ' <;> simp! [*, Subst.comp, Subst.comp_lift]

/-- A substitution absorbs a lift: this is what replaces cancelling the lift against an
instantiation one binder at a time. -/
theorem liftN_subst {e : VExpr} {σ : Subst} :
    (liftN n e k).subst σ = e.subst (.lift_l (.consN (.skipN .refl n) k) σ) := by
  rw [← lift'_consN_skipN, subst_lift']

def Subst.id : Subst := .bvar
def Subst.head (σ : Subst) : VExpr := σ 0
def Subst.tail (σ : Subst) : Subst := fun n => σ (n+1)

theorem Subst.Depth.id : Subst.id.Depth 0 0 := fun _ => rfl

@[simp] theorem id_lift : Subst.id.lift = Subst.id := by
  funext i; cases i <;> simp [Subst.id, Subst.lift, liftN]

@[simp] theorem subst_id {e : VExpr} : e.subst .id = e := by
  induction e <;> simp! [*, id_lift]; rfl

def Subst.cons (σ : Subst) (e : VExpr) : Subst
  | 0 => e
  | i+1 => σ i

abbrev Subst.one (e : VExpr) : Subst := .cons .id e

@[simp] theorem Subst.cons_head (σ : Subst) (e) : (σ.cons e).head = e := rfl
@[simp] theorem Subst.cons_tail (σ : Subst) (e) : (σ.cons e).tail = σ := rfl

/-- A lift on the left of a substitution walks off it one binder at a time: `skip` drops the
substitution's head, `refl` is the end. Together these reduce the `lift_l` that `liftN_subst`
introduces, so a closing given as a `cons` chain reaches `Subst.id` by `simp`. -/
@[simp] theorem Subst.lift_l_refl {σ : Subst} : Subst.lift_l .refl σ = σ := rfl
@[simp] theorem Subst.lift_l_skip {ρ : Lift} {σ : Subst} :
    Subst.lift_l (.skip ρ) σ = Subst.lift_l ρ σ.tail := rfl

@[simp] theorem lift_subst {e : VExpr} {σ : Subst} : e.lift.subst σ = e.subst σ.tail := by
  rw [lift_eq_lift', subst_lift']; rfl

theorem Subst.Depth.one : (Subst.one e).Depth 0 1 := .id

def _root_.Lean4Lean.Lift.inv : Lift → Subst
  | .refl => .id
  | .skip ρ => ρ.inv.cons default
  | .cons ρ => ρ.inv.lift

theorem lift_l_inv {ρ : Lift} : .lift_l ρ ρ.inv = Subst.id := by
  funext i; simp [Subst.lift_l, Subst.id]
  induction ρ generalizing i with
  | refl => rfl
  | skip ρ ih => simp [Lift.inv, Subst.cons, ih]
  | cons ρ ih => cases i <;> simp [Lift.inv, Subst.lift, ih, lift_eq_lift']

theorem lift'_inj {e e' : VExpr} {ρ : Lift} : e.lift' ρ = e'.lift' ρ ↔ e = e' :=
  ⟨(by simpa [subst_lift', lift_l_inv] using congrArg (·.subst ρ.inv) ·), (· ▸ rfl)⟩

theorem instN_eq (e a : VExpr) : e.inst a k = e.subst (.liftN (.one a) k) := by
  induction e generalizing k with simp_all [inst, subst, Subst.liftN] | bvar i
  induction k generalizing i <;> cases i <;> simp [Subst.liftN, Subst.lift, Subst.cons, Subst.id, *]

theorem inst_eq (e a : VExpr) : e.inst a = e.subst (.one a) := instN_eq ..

def Subst.trunc (σ : Subst) (n n' : Nat) : Subst :=
  fun i => if n' ≤ i then .bvar (i - n' + n) else σ i

theorem Subst.lift_r_comm (σ : Subst) (ρ : Lift) (H : Subst.Depth σ 0 n) :
    σ.lift_r ρ = .lift_l (ρ.consN n) ((σ.lift_r ρ).trunc 0 n) := by
  funext i; simp [Subst.lift_l, Subst.lift_r, Subst.trunc]
  have : (ρ.consN n).liftVar i = if n ≤ i then ρ.liftVar (i-n) + n else i := by
    clear H; induction n generalizing i <;> [skip; cases i] <;> simp! [*]; split <;> rfl
  rw [this]; split <;> simp
  have := H (i - n); rw [Nat.sub_add_cancel ‹_›] at this; simp [this]

theorem lift_r_one (e : VExpr) (ρ : Lift) :
    (Subst.one e).lift_r ρ = .lift_l ρ.cons (Subst.one (e.lift' ρ)) := by
  refine (Subst.lift_r_comm (Subst.one e) ρ .one).trans ?_; congr 1
  funext i; simp [Subst.trunc]
  cases i <;> simp [Subst.one, Subst.cons, Subst.lift_r, Subst.id]

theorem lift'_inst_hi (e1 e2 : VExpr) (ρ : Lift) :
    lift' (e1.inst e2) ρ = (lift' e1 ρ.cons).inst (lift' e2 ρ) := by
  simp [subst_lift', lift'_subst, lift_r_one, inst_eq]

theorem Subst.tail_eq_lift_l {σ : Subst} : σ.tail = σ.lift_l Lift.refl.skip := rfl

theorem Subst.lift_r_tail {σ : Subst} {ρ : Lift} :
    (σ.lift_r ρ).tail = σ.tail.lift_r ρ := by funext i; rfl

def Subst.Fixes (σ : Subst) (n : Nat) := ∀ i < n, σ i = .bvar i

theorem Subst.Fixes.zero : Fixes σ 0 := nofun

theorem Subst.Fixes.lift {σ : Subst} (H : σ.Fixes n) : σ.lift.Fixes (n + 1) := fun
  | 0, _ => rfl
  | n+1, h => by simp [Subst.lift, H _ (Nat.lt_of_succ_lt_succ h), VExpr.lift, VExpr.liftN]

theorem ClosedN.subst_eq {e : VExpr} (self : ClosedN e k) (h : σ.Fixes k) : e.subst σ = e := by
  induction e generalizing k σ with (simp [ClosedN] at self; simp [*, VExpr.subst])
  | bvar i => exact h _ self
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h.lift⟩

theorem lift_subst_cons {e : VExpr} : e.lift.subst (σ.cons t) = e.subst σ := by
  rw [lift_subst, Subst.cons_tail]

theorem lift_subst_lift {e : VExpr} {σ : Subst} : e.lift.subst σ.lift = (e.subst σ).lift := by
  rw [lift_eq_lift', subst_lift', lift_eq_lift', lift'_subst]
  congr 1; funext x
  simp [Subst.lift_l, Subst.lift_r, Subst.lift, lift_eq_lift']

theorem subst_inst {e : VExpr} : (e.inst a).subst σ = (e.subst σ.lift).inst (a.subst σ) := by
  rw [inst_eq, inst_eq, subst_subst, subst_subst]; congr 1
  funext i; obtain _|i := i <;> simp [Subst.comp, Subst.lift]
  · simp [Subst.one, Subst.cons]
  · simp [Subst.one, Subst.cons, Subst.id]

theorem inst_lift_cons {e : VExpr} {σ : Subst} :
    (e.subst σ.lift).inst x = e.subst (σ.cons x) := by
  rw [inst_eq, subst_subst, Subst.one]; congr 1
  funext i; obtain _|i := i <;> simp [Subst.comp, Subst.lift, Subst.cons]

/-! ### Syntactic helpers for recursor and constructor shapes

Total functions reading the Π/λ telescope and the application spine of a `VExpr`,
with their decidability. They pin the shapes of recursor types, constructor types
and ι-rule reducts (`RecShape`, `CtorShape`, `RuleShape` in `Theory/Inductive.lean`). -/

/-- Left fold of applications: `f.mkApps [a₀, …, aₙ] = f a₀ … aₙ`. -/
def mkApps (f : VExpr) : List VExpr → VExpr := List.foldl .app f

@[simp] theorem mkApps_nil (f : VExpr) : f.mkApps [] = f := rfl
@[simp] theorem mkApps_cons (f a : VExpr) (l : List VExpr) :
    f.mkApps (a :: l) = (f.app a).mkApps l := rfl
theorem mkApps_append (f : VExpr) (l₁ l₂ : List VExpr) :
    f.mkApps (l₁ ++ l₂) = (f.mkApps l₁).mkApps l₂ := List.foldl_append ..

/-- `[bvar (lo+n-1), …, bvar (lo+1), bvar lo]`: `n` consecutive de Bruijn variables,
descending, as an argument list. -/
def bvarsDesc (lo n : Nat) : List VExpr := (List.range n).reverse.map fun i => .bvar (lo + i)

@[simp] theorem bvarsDesc_length (lo n : Nat) : (bvarsDesc lo n).length = n := by simp [bvarsDesc]

/-- Number of leading Π-binders. -/
def piArity : VExpr → Nat
  | .forallE _ B => B.piArity + 1
  | _ => 0

/-- The expression under all leading Π-binders. -/
def piBody : VExpr → VExpr
  | .forallE _ B => B.piBody
  | e => e

/-- The leading Π-binder types, outermost first (each in its own binder context). -/
def piBinders : VExpr → List VExpr
  | .forallE A B => A :: B.piBinders
  | _ => []

@[simp] theorem piBinders_length : ∀ e : VExpr, e.piBinders.length = e.piArity
  | .forallE _ B => by simp [piBinders, piArity, piBinders_length B]
  | .bvar _ | .sort _ | .const .. | .app .. | .lam .. => rfl

/-- Number of leading λ-binders. -/
def lamArity : VExpr → Nat
  | .lam _ b => b.lamArity + 1
  | _ => 0

/-- The expression under all leading λ-binders. -/
def lamBody : VExpr → VExpr
  | .lam _ b => b.lamBody
  | e => e

/-- The head of an application spine. -/
def getAppFn : VExpr → VExpr
  | .app f _ => f.getAppFn
  | e => e

/-- The arguments of an application spine, first argument first. -/
def getAppArgs : VExpr → List VExpr
  | .app f a => f.getAppArgs ++ [a]
  | _ => []

@[simp] theorem getAppFn_app (f a : VExpr) : (f.app a).getAppFn = f.getAppFn := rfl
@[simp] theorem getAppArgs_app (f a : VExpr) : (f.app a).getAppArgs = f.getAppArgs ++ [a] := rfl

@[simp] theorem getAppFn_mkApps (f : VExpr) : ∀ l : List VExpr, (f.mkApps l).getAppFn = f.getAppFn
  | [] => rfl
  | a :: l => by rw [mkApps_cons, getAppFn_mkApps (f.app a) l, getAppFn_app]

@[simp] theorem getAppArgs_mkApps (f : VExpr) :
    ∀ l : List VExpr, (f.mkApps l).getAppArgs = f.getAppArgs ++ l
  | [] => by simp
  | a :: l => by rw [mkApps_cons, getAppArgs_mkApps (f.app a) l, getAppArgs_app]; simp

@[simp] theorem mkApps_getAppFn_getAppArgs : ∀ e : VExpr, e.getAppFn.mkApps e.getAppArgs = e
  | .app f a => by
    rw [getAppFn_app, getAppArgs_app, mkApps_append, mkApps_getAppFn_getAppArgs f]; rfl
  | .bvar _ | .sort _ | .const .. | .lam .. | .forallE .. => rfl

/-- `e` is `f` applied to `pre` and then further arguments iff `e`'s spine has `f`'s
head and `f`'s arguments followed by `pre` as a prefix of its arguments. -/
theorem eq_mkApps_append_iff {e f : VExpr} {pre : List VExpr} :
    (∃ rest, e = f.mkApps (pre ++ rest)) ↔
      e.getAppFn = f.getAppFn ∧ (f.getAppArgs ++ pre) <+: e.getAppArgs := by
  constructor
  · rintro ⟨rest, rfl⟩
    exact ⟨by simp, ⟨rest, by simp [List.append_assoc]⟩⟩
  · rintro ⟨h1, rest, h2⟩
    refine ⟨rest, ?_⟩
    have h3 := mkApps_getAppFn_getAppArgs e
    rw [h1, ← h2, List.append_assoc, mkApps_append, mkApps_getAppFn_getAppArgs] at h3
    exact h3.symm

/-- `eq_mkApps_append_iff` with the number of further arguments pinned. -/
theorem eq_mkApps_append_length_iff {e f : VExpr} {pre : List VExpr} {n : Nat} :
    (∃ rest, rest.length = n ∧ e = f.mkApps (pre ++ rest)) ↔
      e.getAppFn = f.getAppFn ∧ (f.getAppArgs ++ pre) <+: e.getAppArgs ∧
        e.getAppArgs.length = f.getAppArgs.length + pre.length + n := by
  constructor
  · rintro ⟨rest, rfl, rfl⟩
    exact ⟨by simp, ⟨rest, by simp [List.append_assoc]⟩, by simp [Nat.add_assoc]⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨rest, rfl⟩ := eq_mkApps_append_iff.2 ⟨h1, h2⟩
    refine ⟨rest, ?_, rfl⟩
    simp at h3; omega

/-- Head-constructor tests, with their reflections into existentials. -/
def isSort : VExpr → Bool
  | .sort _ => true
  | _ => false
def isBvar : VExpr → Bool
  | .bvar _ => true
  | _ => false
def isConst : VExpr → Bool
  | .const .. => true
  | _ => false

theorem isSort_iff {e : VExpr} : e.isSort = true ↔ ∃ u, e = .sort u := by cases e <;> simp [isSort]
theorem isBvar_iff {e : VExpr} : e.isBvar = true ↔ ∃ k, e = .bvar k := by cases e <;> simp [isBvar]
theorem isConst_iff {e : VExpr} : e.isConst = true ↔ ∃ I us, e = .const I us := by
  cases e <;> simp [isConst]

instance {e : VExpr} : Decidable (∃ u, e = .sort u) := decidable_of_iff _ isSort_iff
instance {e : VExpr} : Decidable (∃ k, e = .bvar k) := decidable_of_iff _ isBvar_iff
instance {e : VExpr} : Decidable (∃ I us, e = .const I us) := decidable_of_iff _ isConst_iff

/-- The Π-body of `ty` is headed by a bound variable: the shape of a recursor's type and of
a minor premise, whose targets are applications of a motive binder (for the recursor's own
body `VExpr.RecShape` pins which motive; for a minor, `VExpr.MinorHeaded` pins only that the
head is one of the motives). -/
def RecHeaded (ty : VExpr) : Prop := ∃ k, ty.piBody.getAppFn = .bvar k

/-- The Π-body of `ty` is headed by a constant: the shape of a constructor's type,
whose target is a type-former application. -/
def CtorHeaded (ty : VExpr) : Prop := ∃ I us, ty.piBody.getAppFn = .const I us

instance {ty : VExpr} : Decidable ty.RecHeaded := decidable_of_iff _ isBvar_iff
instance {ty : VExpr} : Decidable ty.CtorHeaded := decidable_of_iff _ isConst_iff

/-- A bound variable is not a constant: recursors and constructors have distinct
head shapes, so the same constant cannot be both. -/
theorem RecHeaded.not_ctorHeaded {ty : VExpr} (h : ty.RecHeaded) : ¬ ty.CtorHeaded := by
  rintro ⟨I, us, h'⟩; obtain ⟨k, h⟩ := h; rw [h] at h'; cases h'

/-- The head constant of an application spine, if any. -/
def headConst? (e : VExpr) : Option Name :=
  match e.getAppFn with
  | .const I _ => some I
  | _ => none

/-- The type former a motive `∀ a::α. P a → U` ranges over: the head constant of its last
Π-binder. -/
def motiveFormer? (A : VExpr) : Option Name := A.piBinders.getLast?.bind headConst?

/-- `e.headConst?` names `c` exactly when `e`'s spine head is the constant `c`. -/
theorem headConst?_eq_some {e : VExpr} {c : Name} :
    e.headConst? = some c ↔ ∃ us, e.getAppFn = .const c us := by
  simp only [headConst?]
  cases hf : e.getAppFn <;> simp

/-- The spine data of a constant application. -/
theorem const_mkApps_spine {c : Name} {us : List VLevel} {args : List VExpr} :
    ((VExpr.const c us).mkApps args).getAppFn = .const c us ∧
      ((VExpr.const c us).mkApps args).getAppArgs = args :=
  ⟨by rw [getAppFn_mkApps]; rfl, by rw [getAppArgs_mkApps]; rfl⟩

/-- An expression is its spine head applied to its spine arguments. -/
theorem eq_const_mkApps_of_spine {e : VExpr} {c : Name} {us : List VLevel} {args : List VExpr}
    (hf : e.getAppFn = .const c us) (ha : e.getAppArgs = args) :
    e = (VExpr.const c us).mkApps args := by
  have h := mkApps_getAppFn_getAppArgs e; rw [hf, ha] at h; exact h.symm

/-- `e` is the constant `c` applied to exactly `args`. -/
theorem eq_const_mkApps_iff {e : VExpr} {c : Name} {args : List VExpr} :
    (∃ us, e = (VExpr.const c us).mkApps args) ↔
      e.headConst? = some c ∧ e.getAppArgs = args := by
  constructor
  · rintro ⟨us, rfl⟩
    exact ⟨headConst?_eq_some.2 ⟨us, const_mkApps_spine.1⟩, const_mkApps_spine.2⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨us, hf⟩ := headConst?_eq_some.1 h1
    exact ⟨us, eq_const_mkApps_of_spine hf h2⟩

/-- `e` is the constant `c` applied to `pre` and then further arguments satisfying `P`; those
further arguments are `e.getAppArgs.drop pre.length`. -/
theorem eq_const_mkApps_append_iff {e : VExpr} {c : Name} {pre : List VExpr}
    {P : List VExpr → Prop} :
    (∃ us rest, e = (VExpr.const c us).mkApps (pre ++ rest) ∧ P rest) ↔
      e.headConst? = some c ∧ pre <+: e.getAppArgs ∧ P (e.getAppArgs.drop pre.length) := by
  constructor
  · rintro ⟨us, rest, rfl, hP⟩
    refine ⟨headConst?_eq_some.2 ⟨us, const_mkApps_spine.1⟩, ?_, ?_⟩ <;>
      rw [const_mkApps_spine.2]
    · exact ⟨rest, rfl⟩
    · simpa using hP
  · rintro ⟨h1, ⟨rest, h2⟩, hP⟩
    obtain ⟨us, hf⟩ := headConst?_eq_some.1 h1
    refine ⟨us, rest, eq_const_mkApps_of_spine hf h2.symm, ?_⟩
    rw [← h2] at hP; simpa using hP

end VExpr
