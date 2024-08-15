import Lean
import Lean4Lean.Theory.VLevel

namespace Lean4Lean

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

@[simp] theorem ClosedN.default : ClosedN default k := trivial

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

protected theorem ClosedN.liftN (self : ClosedN e k) : ClosedN (e.liftN n j) (k+n) := by
  induction e generalizing k j with
    (simp [ClosedN] at self; simp [self, VExpr.liftN, ClosedN, *])
  | bvar i => exact liftVar_lt_add self
  | lam _ _ _ ih2 | forallE _ _ _ ih2 => exact Nat.add_right_comm .. ▸ ih2 self.2

theorem ClosedN.liftN_eq_rev (self : ClosedN (liftN n e j) k) (h : k ≤ j) : liftN n e j = e := by
  induction e generalizing k j with
    (simp [ClosedN] at self; simp [self, liftN, *])
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

theorem LevelWF.instL_id {e : VExpr} (h : e.LevelWF U) :
    e.instL ((List.range U).map .param) = e := by
  induction e <;> simp_all [instL, LevelWF, VLevel.inst_id]
  case const => exact List.map_id''' _ fun _ h1 => VLevel.inst_id (h _ h1)

theorem levelWF_liftN : (liftN n e k).LevelWF U ↔ e.LevelWF U := by
  induction e generalizing k <;> simp [liftN, LevelWF, *]

theorem LevelWF.instL (h : ∀ l ∈ ls, l.WF U) : (instL ls e).LevelWF U := by
  induction e <;> simp [instL, VLevel.WF.inst h, LevelWF, *]

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
    simp only [liftN, liftVar]; split <;> rename_i hk
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
    simp [liftVar, h, Nat.succ_lt_succ_iff]; split <;> rename_i hi
    · simp [liftN, liftVar_lt hi]
    · have := Nat.lt_add_left n hk
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

theorem inst_lift (e1 e2 : VExpr) : (lift e1).inst e2 = e1 := inst_liftN ..

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
    simp [Nat.succ_eq_add_one, skips_add, ih]; clear ih
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
  induction e generalizing k <;> simp_all [Skips']

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

theorem inst0_inst_hi (e1 e2 e3 : VExpr) (j : Nat) :
    inst (e1.inst e2) e3 j = (e1.inst e3 (j+1)).inst (e2.inst e3 j) := inst_inst_hi ..

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

def OnVars (P : Nat → Prop) (e : VExpr) : Prop := ∀ k, e.Skips 1 k ∨ P k

theorem OnVars.mono {P Q : Nat → Prop} (H : ∀ i, P i → Q i) (h : OnVars P e) : OnVars Q e :=
  fun _ => (h _).imp_right (H _)

end VExpr

inductive Lift : Type where
  | refl : Lift
  | skip : Lift → Lift
  | cons : Lift → Lift

@[simp] def Lift.skipN : Nat → Lift
  | 0   => .refl
  | n+1 => .skip (Lift.skipN n)

@[simp] def Lift.consN (l : Lift) : Nat → Lift
  | 0  => l
  | k+1 => .cons (Lift.consN l k)

@[simp] def Lift.comp (l₁ l₂ : Lift) : Lift :=
  match l₂, l₁ with
  | .refl,    l₁       => l₁
  | .skip l₂, l₁       => .skip (l₁.comp l₂)
  | .cons l₂, .refl    => .cons l₂
  | .cons l₂, .skip l₁ => .skip (l₁.comp l₂)
  | .cons l₂, .cons l₁ => .cons (l₁.comp l₂)

@[simp] def Lift.depth : Lift → Nat
  | .refl   => 0
  | .skip l => l.depth + 1
  | .cons l => l.depth

theorem Lift.depth_comp : Lift.depth (.comp l₁ l₂) = l₁.depth + l₂.depth :=
  match l₂, l₁ with
  | .refl,    _        => rfl
  | .skip _,  _        => congrArg Nat.succ Lift.depth_comp
  | .cons _,  .refl    => (Nat.zero_add _).symm
  | .cons _,  .skip _  => (congrArg Nat.succ Lift.depth_comp).trans (Nat.succ_add ..).symm
  | .cons l₂, .cons l₁ => @Lift.depth_comp l₁ l₂

@[simp] theorem Lift.depth_consN : Lift.depth (.consN l n) = l.depth := by induction n <;> simp [*]

theorem Lift.consN_consN : Lift.consN (.consN l a) b = .consN l (a + b) := by
  induction b <;> simp [*]

theorem Lift.consN_comp : Lift.consN (.comp l₁ l₂) n = .comp (.consN l₁ n) (.consN l₂ n) := by
  induction n <;> simp [*]

@[simp] theorem Lift.depth_skipN : Lift.depth (.skipN n) = n := by induction n <;> simp [*]

theorem Lift.consN_skip_eq : consN (skip l) k = comp (consN l k) (consN (skipN 1) k) := by
  rw [← consN_comp]; rfl

theorem Lift.depth_succ (H : l.depth = n + 1) :
    ∃ l' k, Lift.depth l' = n ∧ l = Lift.consN (.skip l') k := by
  match l with
  | .skip l => cases H; exact ⟨l, 0, rfl, rfl⟩
  | .cons l =>
    obtain ⟨l, k, rfl, ⟨⟩⟩ := depth_succ (l := l) H
    exact ⟨l, k+1, rfl, rfl⟩

theorem Lift.depth_succ' (H : l.depth = n + 1) :
    ∃ l' k, Lift.depth l' = n ∧ l = Lift.comp l' (.consN (.skipN 1) k) := by
  let ⟨l', k, h1, h2⟩ := depth_succ H
  exact ⟨.consN l' k, k, by simp [h1], by rwa [← consN_skip_eq]⟩

@[simp] def Lift.liftVar : Lift → Nat → Nat
  | .refl, n => n
  | .skip l, n => l.liftVar n + 1
  | .cons _, 0 => 0
  | .cons l, n+1 => l.liftVar n + 1

theorem liftVar_comp : Lift.liftVar (.comp l₁ l₂) n = l₂.liftVar (l₁.liftVar n) := by
  induction l₂ generalizing l₁ n <;> [skip; skip; cases l₁ <;> [skip; skip; cases n]] <;> simp [*]

theorem liftVar_skipN : (Lift.skipN n).liftVar i = i + n := by
  induction n generalizing i with
  | zero => rfl
  | succ _ ih => simp [ih, Nat.add_right_comm]; rfl

theorem liftVar_consN_skipN : (Lift.consN (.skipN n) k).liftVar i = liftVar n i k := by
  induction k generalizing i with
  | zero => simp [liftVar_skipN]
  | succ k ih =>
    cases i with simp [liftVar, Nat.succ_lt_succ_iff, ih]
    | succ i => split <;> rfl

theorem liftVar_depth_zero (H : l.depth = 0) : Lift.liftVar l n = n := by
  induction l generalizing n <;> [skip; skip; cases n] <;> simp_all [Lift.depth]

namespace VExpr

@[simp] def lift' : VExpr → Lift → VExpr
  | .bvar i, k => .bvar (k.liftVar i)
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app fn arg, k => .app (fn.lift' k) (arg.lift' k)
  | .lam ty body, k => .lam (ty.lift' k) (body.lift' k.cons)
  | .forallE ty body, k => .forallE (ty.lift' k) (body.lift' k.cons)

theorem lift'_consN_skipN : e.lift' (.consN (.skipN n) k) = liftN n e k := Eq.symm <| by
  induction e generalizing k <;> simp [liftN, liftVar_consN_skipN, *]

theorem lift'_comp {e : VExpr} : e.lift' (.comp l₁ l₂) = (e.lift' l₁).lift' l₂ := Eq.symm <| by
  induction e generalizing l₁ l₂ <;> simp [liftVar_comp, *]

theorem lift'_depth_zero {e : VExpr} (H : l.depth = 0) : e.lift' l = e := by
  induction e generalizing l <;> simp_all [liftVar_depth_zero]
