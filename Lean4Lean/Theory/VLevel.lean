import Lean4Lean.Std.Basic

namespace Lean4Lean

export Lean (Name)

inductive VLevel where
  | zero  : VLevel
  | succ  : VLevel → VLevel
  | max   : VLevel → VLevel → VLevel
  | imax  : VLevel → VLevel → VLevel
  | param : Nat → VLevel

namespace VLevel

instance : Inhabited VLevel := ⟨.zero⟩

variable (n : Nat) in
def WF : VLevel → Prop
  | .zero => True
  | .succ l => l.WF
  | .max l₁ l₂ => l₁.WF ∧ l₂.WF
  | .imax l₁ l₂ => l₁.WF ∧ l₂.WF
  | .param i => i < n

instance decidable_WF : ∀ {l}, Decidable (WF n l)
  | .zero => instDecidableTrue
  | .succ l => @decidable_WF _ l
  | .max .. | .imax .. => @instDecidableAnd _ _ decidable_WF decidable_WF
  | .param _ => Nat.decLt ..

variable (ls : List Nat) in
def eval : VLevel → Nat
  | .zero => 0
  | .succ l => l.eval + 1
  | .max l₁ l₂ => l₁.eval.max l₂.eval
  | .imax l₁ l₂ => l₁.eval.imax l₂.eval
  | .param i => ls.getD i 0

protected def LE (a b : VLevel) : Prop := ∀ ls, a.eval ls ≤ b.eval ls

instance : LE VLevel := ⟨VLevel.LE⟩

theorem le_refl (a : VLevel) : a ≤ a := fun _ => Nat.le_refl _
theorem le_trans {a b c : VLevel} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  fun _ => Nat.le_trans (h1 _) (h2 _)

theorem zero_le : zero ≤ a := fun _ => Nat.zero_le _

theorem le_succ : a ≤ succ a := fun _ => Nat.le_succ _

theorem succ_le_succ (h : a ≤ b) : succ a ≤ succ b := fun _ => Nat.succ_le_succ (h _)

theorem le_max_left : a ≤ max a b := fun _ => Nat.le_max_left ..
theorem le_max_right : b ≤ max a b := fun _ => Nat.le_max_right ..

protected def Equiv (a b : VLevel) : Prop := a.eval = b.eval

instance : HasEquiv VLevel := ⟨VLevel.Equiv⟩

theorem equiv_def' {a b : VLevel} : a ≈ b ↔ a.eval = b.eval := .rfl
theorem equiv_def {a b : VLevel} : a ≈ b ↔ ∀ ls, a.eval ls = b.eval ls := funext_iff

theorem equiv_congr_left {a b c : VLevel} (h : a ≈ b) : a ≈ c ↔ b ≈ c :=
  iff_of_eq (congrArg (· = _) h)

theorem equiv_congr_right {a b c : VLevel} (h : a ≈ b) : c ≈ a ↔ c ≈ b :=
  iff_of_eq (congrArg (_ = ·) h)

theorem le_antisymm_iff {a b : VLevel} : a ≈ b ↔ a ≤ b ∧ b ≤ a :=
  equiv_def.trans <| (forall_congr' fun _ => Nat.le_antisymm_iff).trans forall_and

theorem succ_congr {a b : VLevel} (h : a ≈ b) : succ a ≈ succ b := by
  simpa [equiv_def, eval] using h

theorem succ_congr_iff {a b : VLevel} : succ a ≈ succ b ↔ a ≈ b := by
  simp [equiv_def, eval]

theorem max_congr (h₁ : a₁ ≈ b₁) (h₂ : a₂ ≈ b₂) : max a₁ a₂ ≈ max b₁ b₂ := by
  simp_all [equiv_def, eval]

theorem imax_congr (h₁ : a₁ ≈ b₁) (h₂ : a₂ ≈ b₂) : imax a₁ a₂ ≈ imax b₁ b₂ := by
  simp_all [equiv_def, eval]

theorem max_comm : max a b ≈ max b a := by simp [equiv_def, eval, Nat.max_comm]

theorem LE.max_eq_left (h : b.LE a) : max a b ≈ a := by
  simp [equiv_def, eval, Nat.max_eq_left (h _)]

theorem LE.max_eq_right (h : a.LE b) : max a b ≈ b := by
  simp [equiv_def, eval, Nat.max_eq_right (h _)]

theorem max_self : max a a ≈ a := by simp [equiv_def, eval]

theorem zero_imax : imax zero a ≈ a := by
  simp [equiv_def, eval, Nat.imax, eq_comm (b := 0)]

theorem imax_zero : imax a zero ≈ zero := by simp [equiv_def, eval, Nat.imax]

theorem imax_self : imax a a ≈ a := by
  simp [equiv_def, eval, Nat.imax, eq_comm (b := 0)]

theorem imax_eq_zero : imax a b ≈ zero ↔ b ≈ zero := by
  simp [equiv_def, eval, Nat.imax]
  refine ⟨fun H ls => ?_, fun H ls hn => nomatch hn (H ls)⟩
  exact Decidable.byContradiction fun h => h (H ls h).2

def IsNeverZero (a : VLevel) : Prop := ∀ ls, a.eval ls ≠ 0

theorem IsNeverZero.imax_eq_max (h : IsNeverZero b) : imax a b ≈ max a b := by
  simp_all [equiv_def, eval, Nat.imax, IsNeverZero]

variable (ls : List VLevel) in
def inst : VLevel → VLevel
  | .zero => .zero
  | .succ l => .succ l.inst
  | .max l₁ l₂ => .max l₁.inst l₂.inst
  | .imax l₁ l₂ => .imax l₁.inst l₂.inst
  | .param i => ls.getD i .zero

theorem inst_inst {l : VLevel} : (l.inst ls).inst ls' = l.inst (ls.map (inst ls')) := by
  induction l <;> simp [inst, *, List.getD_eq_getElem?_getD, List.getElem?_map]
  case param n => cases ls[n]? <;> simp [inst]

def params (n : Nat) : List VLevel := (List.range n).map .param

@[simp] theorem params_length {n : Nat} : (params n).length = n := by simp [params]

theorem params_wf {n : Nat} : ∀ ⦃l⦄, l ∈ params n → l.WF n := by simp [params, WF]

theorem inst_id {l : VLevel} (h : l.WF u) : l.inst (params u) = l := by
  induction l <;> simp_all [params, inst, WF, List.getD_eq_getElem?_getD]

theorem inst_map_id (h : ls.length = n) : (params n).map (inst ls) = ls := by
  subst n; simp [params]; apply List.ext_get (by simp)
  intro i _ _; simp [inst]; rw [List.getElem?_eq_getElem]; rfl

theorem eval_inst {l : VLevel} : (l.inst ls).eval ns = l.eval (ls.map (eval ns)) := by
  induction l <;> simp [eval, inst, *, List.getD_eq_getElem?_getD]
  case param n => cases ls[n]? <;> simp [eval]

theorem WF.inst {l : VLevel} (H : ∀ l ∈ ls, l.WF n) : (l.inst ls).WF n := by
  induction l with
  | zero => trivial
  | succ _ ih => exact ih
  | max _ _ ih1 ih2 | imax _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | param i =>
    simp [VLevel.inst, List.getD_eq_getElem?_getD]
    cases e : ls[i]? with
    | none => trivial
    | some => exact H _ (List.mem_of_getElem? e)

theorem id_WF : ∀ l ∈ (List.range u).map param, l.WF u := by simp [WF]

theorem inst_congr {l : VLevel} (h1 : l ≈ l') (h2 : List.Forall₂ (·≈·) ls ls') :
    l.inst ls ≈ l'.inst ls' := by
  simp [equiv_def, eval_inst, ← equiv_def.1 h1]
  intro ns; congr 1
  induction h2 with
  | nil => rfl
  | cons h2 => simp [*, equiv_def.1 h2]

theorem inst_congr_l {l : VLevel} (h1 : l ≈ l') : l.inst ls ≈ l'.inst ls :=
  inst_congr h1 <| .rfl fun _ _ => rfl

variable (ls : List Name) in
def ofLevel : Lean.Level → Option VLevel
  | .zero => return .zero
  | .succ l => return .succ (← ofLevel l)
  | .max l₁ l₂ => return .max (← ofLevel l₁) (← ofLevel l₂)
  | .imax l₁ l₂ => return .imax (← ofLevel l₁) (← ofLevel l₂)
  | .param n =>
    let i := ls.idxOf n
    if i < ls.length then some (.param i) else none
  | .mvar _ => none

theorem WF.of_ofLevel (h : ofLevel ls l = some l') : l'.WF ls.length := by
  induction l generalizing l' with simp [ofLevel, bind] at h
  | zero => cases h; trivial
  | succ _ ih => obtain ⟨l', h, ⟨⟩⟩ := h; exact @ih l' h
  | max _ _ ih1 ih2 | imax _ _ ih1 ih2 => obtain ⟨_, h1, _, h2, ⟨⟩⟩ := h; exact ⟨ih1 h1, ih2 h2⟩
  | param n => exact h.2 ▸ h.1

theorem WF.of_mapM_ofLevel (h : List.mapM (VLevel.ofLevel Us) us = some us')
    (a) (hl : a ∈ us') : VLevel.WF Us.length a := by
  rw [List.mapM_eq_some] at h
  have ⟨_, _, h⟩ := h.forall_exists_r _ hl; exact .of_ofLevel h
