import Lean
import Lean4Lean.Theory.VLevel

namespace Lean4Lean

open Lean (Name FVarId)

inductive VExpr where
  | bvar (deBruijnIndex : Nat)
  | sort (u : VLevel)
  | const (declName : Name) (us : List VLevel)
  | app (fn arg : VExpr)
  | lam (binderType body : VExpr)
  | forallE (binderType body : VExpr)

def liftVar (n i : Nat) (k := 0) : Nat := if i < k then i else n + i

theorem liftVar_lt (h : i < k) : liftVar n i k = i := if_pos h
theorem liftVar_le (h : k ≤ i) : liftVar n i k = n + i := if_neg (Nat.not_lt.2 h)

theorem liftVar_base : liftVar n i = n + i := liftVar_le (Nat.zero_le _)
@[simp] theorem liftVar_base' : liftVar n i = i + n := Nat.add_comm .. ▸ liftVar_le (Nat.zero_le _)

@[simp] theorem liftVar_zero : liftVar n 0 (k+1) = 0 := by simp [liftVar]
@[simp] theorem liftVar_succ : liftVar n (i+1) (k+1) = liftVar n i k + 1 := by
  simp [liftVar, Nat.succ_lt_succ_iff]; split <;> simp [Nat.add_assoc]

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

theorem liftN'_liftN' (e : VExpr) (n1 n2 k1 k2 : Nat) (h1 : k1 ≤ k2) (h2 : k2 ≤ n1 + k1) :
    liftN n2 (liftN n1 e k1) k2 = liftN (n1+n2) e k1 := by
  induction e generalizing k1 k2 with simp [liftN, liftVar, Nat.add_assoc, *]
  | bvar i =>
    split <;> rename_i h
    · rw [if_pos (Nat.lt_of_lt_of_le h h1)]
    · rw [if_neg (mt (fun h => ?_) h), Nat.add_left_comm]
      exact (Nat.add_lt_add_iff_left ..).1 (Nat.lt_of_lt_of_le h h2)
  | lam _ _ _ IH2 | forallE _ _ _ IH2 =>
    rw [IH2 _ _ (Nat.succ_le_succ h1) (Nat.succ_le_succ h2)]

theorem liftN'_liftN (e : VExpr) (n k : Nat) : liftN n (liftN k e) k = liftN (n+k) e := by
  simpa [Nat.add_comm] using liftN'_liftN' e k n 0 _ (Nat.zero_le _) (Nat.le_refl _)

theorem liftN_liftN (e : VExpr) (n1 n2 : Nat) : liftN n2 (liftN n1 e) = liftN (n1+n2) e := by
  simpa using liftN'_liftN' e n1 n2 0 _ (Nat.zero_le _) (Nat.zero_le _)

@[simp] theorem liftN_succ (e : VExpr) (n : Nat) : liftN (n+1) e = lift (liftN n e) :=
  (liftN_liftN ..).symm

theorem liftN'_comm (e : VExpr) (n1 n2 k1 k2 : Nat) (h : k2 ≤ k1) :
    liftN n2 (liftN n1 e k1) k2 = liftN n1 (liftN n2 e k2) (n2+k1) := by
  induction e generalizing k1 k2 with
    simp [liftN, liftVar, Nat.add_assoc, Nat.succ_le_succ, *]
  | bvar i =>
    split <;> rename_i h'
    · rw [if_pos (c := _ < n2 + k1)]; split
      · exact Nat.lt_add_left _ _ _ h'
      · exact Nat.add_lt_add_left h' _
    · have := mt (Nat.lt_of_lt_of_le · h) h'
      rw [if_neg (mt (Nat.lt_of_le_of_lt (Nat.le_add_left _ n1)) this),
        if_neg this, if_neg (mt (Nat.add_lt_add_iff_left ..).1 h'), Nat.add_left_comm]

theorem lift_liftN' (e : VExpr) (k : Nat) : lift (liftN n e k) = liftN n (lift e) (k+1) :=
  Nat.add_comm .. ▸ liftN'_comm (h := Nat.zero_le _) ..

def ClosedN : VExpr → (k :_:= 0) → Prop
  | .bvar i, k => i < k
  | .sort .., _ | .const .., _ => True
  | .app fn arg, k => fn.ClosedN k ∧ arg.ClosedN k
  | .lam ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)
  | .forallE ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)

abbrev Closed := ClosedN

theorem ClosedN.mono (h : k ≤ k') (self : ClosedN e k) : ClosedN e k' := by
  induction e generalizing k k' with (simp [ClosedN] at self ⊢; try simp [self, *])
  | bvar i => exact Nat.lt_of_lt_of_le self h
  | app _ _ ih1 ih2 => exact ⟨ih1 h self.1, ih2 h self.2⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    exact ⟨ih1 h self.1, ih2 (Nat.succ_le_succ h) self.2⟩

theorem ClosedN.liftN_eq (self : ClosedN e k) (h : k ≤ j) : liftN n e j = e := by
  induction e generalizing k j with
    (simp [ClosedN] at self; simp [self, liftN, *])
  | bvar i => exact liftVar_lt (Nat.lt_of_lt_of_le self h)
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    exact ⟨ih1 self.1 h, ih2 self.2 (Nat.succ_le_succ h)⟩

variable (ls : List VLevel) in
def instL : VExpr → VExpr
  | .bvar i => .bvar i
  | .sort u => .sort (u.inst ls)
  | .const c us => .const c (us.map (·.inst ls))
  | .app fn arg => .app fn.instL arg.instL
  | .lam ty body => .lam ty.instL body.instL
  | .forallE ty body => .forallE ty.instL body.instL

theorem ClosedN.instL : ∀ {e}, ClosedN e k → ClosedN (e.instL ls) k
  | .bvar .., h | .sort .., h | .const .., h => h
  | .app .., h | .lam .., h | .forallE .., h => ⟨h.1.instL, h.2.instL⟩

theorem liftN_instL : liftN n (e.instL ls) k = (liftN n e k).instL ls := by
  cases e <;> simp [liftN, instL, liftN_instL]

def inst : VExpr → VExpr → (k :_:= 0) → VExpr
  | .bvar i, e, k =>
    if i < k then .bvar i else if i = k then liftN k e else .bvar (i - 1)
  | .sort u, _, _ => .sort u
  | .const c us, _, _ => .const c us
  | .app fn arg, e, k => .app (fn.inst e k) (arg.inst e k)
  | .lam ty body, e, k => .lam (ty.inst e k) (body.inst e (k+1))
  | .forallE ty body, e, k => .forallE (ty.inst e k) (body.inst e (k+1))

theorem liftN_inst_lo (n : Nat) (e1 e2 : VExpr) (j k : Nat) (hj : k ≤ j) :
    liftN n (e1.inst e2 j) k = (liftN n e1 k).inst e2 (n+j) := by
  induction e1 generalizing k j with
    simp [liftN, inst, Nat.add_le_add_iff_right, *]
  | bvar i =>
    split <;> rename_i h
    · rw [if_pos]; · rfl
      simp only [liftN, liftVar]; split <;> rename_i hk
      · exact Nat.lt_add_left _ _ _ h
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
  | _ => rfl

theorem liftN_inst_hi (e1 e2 : VExpr) (n k j : Nat) :
    liftN n (e1.inst e2 j) (k+j) =
    (liftN n e1 (k+j+1)).inst (liftN n e2 k) j := by
  induction e1 generalizing j with simp [liftN, inst, *]
  | bvar i =>
    split <;> rename_i h
    · have := Nat.lt_add_left _ k _ h
      rw [liftVar_lt <| Nat.lt_succ_of_lt this, if_pos h]
      simp [liftN, liftVar_lt this]
    split <;> rename_i h'
    · subst i
      have := Nat.le_add_left j k
      simp [liftVar_lt (by exact Nat.lt_succ_of_le this)]
      rw [liftN'_comm (h := Nat.zero_le _), Nat.add_comm]
    · have hk := Nat.lt_of_le_of_ne (Nat.not_lt.1 h) (Ne.symm h')
      let i+1 := i
      simp [liftVar, h, Nat.succ_lt_succ_iff]; split <;> rename_i hi
      · simp [liftN, liftVar_lt hi]
      · have := Nat.lt_add_left _ n _ hk
        rw [if_neg (Nat.lt_asymm this), if_neg (Nat.ne_of_gt this)]
        simp [liftN]; rw [liftVar_le (Nat.not_lt.1 hi)]; rfl
  | _ => rename_i IH; apply IH

theorem lift_inst_lo (e1 e2 : VExpr) : lift (e1.inst e2) = (lift e1).inst e2 1 :=
  liftN_inst_lo (hj := Nat.zero_le _) ..

theorem lift_inst_hi (e1 e2 : VExpr) : lift (e1.inst e2) = (liftN 1 e1 1).inst (lift e2) :=
  liftN_inst_hi ..
