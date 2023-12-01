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

theorem liftN'_liftN (e : VExpr) (n k : Nat) : liftN n (liftN k e) k = liftN (n+k) e := by
  simpa [Nat.add_comm] using liftN'_liftN' (n1 := k) (n2 := n) (Nat.zero_le _) (Nat.le_refl _)

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

theorem ClosedN.lift_eq (self : ClosedN e) : lift e = e := self.liftN_eq (Nat.zero_le _)

theorem ClosedN.liftN (self : ClosedN e k) : ClosedN (e.liftN n j) (k+n) := by
  induction e generalizing k j with
    (simp [ClosedN] at self; simp [self, VExpr.liftN, ClosedN, liftVar, *])
  | bvar i =>
    split <;> rename_i h
    · exact Nat.lt_of_lt_of_le self (Nat.le_add_right ..)
    · rw [Nat.add_comm]; exact Nat.add_lt_add_right self _
  | lam _ _ _ ih2 | forallE _ _ _ ih2 => exact Nat.add_right_comm .. ▸ ih2 self.2

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

@[simp] theorem instL_liftN : (liftN n e k).instL ls = liftN n (e.instL ls) k := by
  cases e <;> simp [liftN, instL, instL_liftN]

theorem instL_instL {e : VExpr} : (e.instL ls).instL ls' = e.instL (ls.map (VLevel.inst ls')) := by
  cases e <;> simp [instL, instL_instL, Function.comp_def, VLevel.inst_inst]

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

theorem liftN_instVar_hi (i : Nat) (e2 : VExpr) (n k j : Nat) :
    liftN n (instVar i e2 j) (k+j) = instVar (liftVar n i (k+j+1)) (liftN n e2 k) j := by
  simp [instVar]; split <;> rename_i h
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

@[simp] theorem instL_instVar : (instVar i e k).instL ls = instVar i (e.instL ls) k := by
  simp [instVar]; split <;> [skip; split] <;> simp [instL, instL_liftN]

def inst : VExpr → VExpr → (k :_:= 0) → VExpr
  | .bvar i, e, k => instVar i e k
  | .sort u, _, _ => .sort u
  | .const c us, _, _ => .const c us
  | .app fn arg, e, k => .app (fn.inst e k) (arg.inst e k)
  | .lam ty body, e, k => .lam (ty.inst e k) (body.inst e (k+1))
  | .forallE ty body, e, k => .forallE (ty.inst e k) (body.inst e (k+1))

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

theorem lift_inst_lo (e1 e2 : VExpr) : lift (e1.inst e2) = (lift e1).inst e2 1 :=
  liftN_instN_lo (hj := Nat.zero_le _) ..

theorem lift_inst_hi (e1 e2 : VExpr) : lift (e1.inst e2) = (liftN 1 e1 1).inst (lift e2) :=
  liftN_instN_hi ..

theorem inst_liftN (e1 e2 : VExpr) : (liftN 1 e1 k).inst e2 k = e1 := by
  induction e1 generalizing k with simp [liftN, inst, *]
  | bvar i =>
    simp only [liftVar, instVar, Nat.add_comm 1]; split <;> [rfl; rename_i h]
    rw [if_neg (mt (Nat.lt_of_le_of_lt (Nat.le_succ _)) h),
      if_neg (mt (by rintro rfl; apply Nat.lt_succ_self) h)]; rfl

theorem inst_lift (e1 e2 : VExpr) : (lift e1).inst e2 = e1 := inst_liftN ..

@[simp] theorem instL_instN {e1 e2 : VExpr} :
    (e1.inst e2 k).instL ls = (e1.instL ls).inst (e2.instL ls) k := by
  induction e1 generalizing k <;> simp [instL, inst, *]

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
    · simp [Nat.succ_lt_succ hi, inst, instVar, h, h']
    split <;> rename_i hi'
    · subst i
      simp
      suffices liftN (j+k+1) .. = _ by rw [this]; exact (inst_liftN ..).symm
      exact (liftN'_liftN' (Nat.zero_le _) (Nat.le_add_left k j)).symm
    · have hk := Nat.lt_of_le_of_ne (Nat.not_lt.1 hi) (Ne.symm hi')
      let i+1 := i
      simp [Nat.add_lt_add_iff_right, hi, inst, instVar]
      have := Nat.lt_of_le_of_lt (Nat.le_add_left ..) hk
      rw [if_neg (Nat.lt_asymm this), if_neg (Nat.ne_of_gt this)]

theorem inst_inst_hi (e1 e2 e3 : VExpr) (k j : Nat) :
    inst (e1.inst e2 k) e3 (j+k) = (e1.inst e3 (j+k+1)).inst (e2.inst e3 j) k := by
  induction e1 generalizing k with simp [liftN, inst, instVar, *]
  | bvar i => apply inst_instVar_hi
  | _ => rename_i IH; apply IH

theorem inst_instVar_lo (i : Nat) (e2 e3 : VExpr) (k j : Nat) :
    inst (instVar i e2 (k+j+1)) e3 j =
    (instVar i (e3.liftN 1 k) j).inst e2 (k+j) := by
  simp [instVar]; split <;> rename_i h
  · split <;> rename_i h1
    · simp [inst, instVar, h1]; rw [if_pos (Nat.lt_of_lt_of_le h1 (Nat.le_add_left ..))]
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
    simp [inst, instVar, hk]
    have := Nat.lt_of_le_of_lt (Nat.le_add_left ..) hk
    rw [if_neg (Nat.lt_asymm this), if_neg (Nat.ne_of_gt this)]
    have := Nat.lt_succ_of_lt this
    rw [if_neg (Nat.lt_asymm this), if_neg (Nat.ne_of_gt this)]
    simp [inst, instVar]
    rw [if_neg (Nat.lt_asymm hk), if_neg (Nat.ne_of_gt hk)]

theorem inst_inst_lo (e1 e2 e3 : VExpr) (k j : Nat) :
    inst (e1.inst e2 (k+j+1)) e3 j =
    (e1.inst (e3.liftN 1 k) j).inst e2 (k+j) := by
  induction e1 generalizing j with simp [liftN, inst, instVar, *]
  | bvar i => apply inst_instVar_lo
  | _ => rename_i IH; exact IH (j+1)

theorem instN_bvar0 (e : VExpr) (k : Nat) :
    inst (e.liftN 1 (k+1)) (.bvar 0) k = e := by
  induction e generalizing k with simp [liftN, inst, *]
  | bvar i => induction i generalizing k <;> cases k <;> simp [*, lift, liftN]
