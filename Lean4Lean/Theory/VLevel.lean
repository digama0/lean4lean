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

protected def Equiv (a b : VLevel) : Prop := a.eval = b.eval

instance : HasEquiv VLevel := ⟨VLevel.Equiv⟩

theorem equiv_def' {a b : VLevel} : a ≈ b ↔ a.eval = b.eval := .rfl
theorem equiv_def {a b : VLevel} : a ≈ b ↔ ∀ ls, a.eval ls = b.eval ls := funext_iff

theorem le_antisymm_iff {a b : VLevel} : a ≈ b ↔ a ≤ b ∧ b ≤ a :=
  equiv_def.trans <| (forall_congr' fun _ => Nat.le_antisymm_iff).trans forall_and

theorem succ_congr {a b : VLevel} (h : a ≈ b) : VLevel.succ a ≈ .succ b := by
  simpa [equiv_def, eval] using h

variable (ls : List VLevel) in
def inst : VLevel → VLevel
  | .zero => .zero
  | .succ l => .succ l.inst
  | .max l₁ l₂ => .max l₁.inst l₂.inst
  | .imax l₁ l₂ => .imax l₁.inst l₂.inst
  | .param i => ls.getD i .zero

theorem inst_inst {l : VLevel} : (l.inst ls).inst ls' = l.inst (ls.map (VLevel.inst ls')) := by
  induction l <;> simp [inst, *, List.getD_eq_getElem?, List.getElem?_map]
  case param n => cases ls[n]? <;> simp [inst]

theorem inst_id {l : VLevel} (h : l.WF u) : l.inst ((List.range u).map .param) = l := by
  induction l <;> simp_all [inst, WF, List.getD_eq_getElem?, List.getElem?_range]

theorem eval_inst {l : VLevel} : (l.inst ls).eval ns = l.eval (ls.map (VLevel.eval ns)) := by
  induction l <;> simp [eval, inst, *, List.getD_eq_getElem?]
  case param n => cases ls[n]? <;> simp [eval]

theorem WF.inst {l : VLevel} (H : ∀ l ∈ ls, l.WF n) : (l.inst ls).WF n := by
  induction l with
  | zero => trivial
  | succ _ ih => exact ih
  | max _ _ ih1 ih2 | imax _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | param i =>
    simp [VLevel.inst, List.getD_eq_getElem?]
    cases e : ls[i]? with
    | none => trivial
    | some => exact H _ (List.getElem?_mem e)

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
    let i := ls.indexOf n
    if i < ls.length then some (.param i) else none
  | .mvar _ => none

theorem WF.of_ofLevel (h : ofLevel ls l = some l') : l'.WF ls.length := by
  induction l generalizing l' with simp [ofLevel, bind, Option.bind_eq_some] at h
  | zero => cases h; trivial
  | succ _ ih => obtain ⟨l', h, ⟨⟩⟩ := h; exact @ih l' h
  | max _ _ ih1 ih2 | imax _ _ ih1 ih2 => obtain ⟨_, h1, _, h2, ⟨⟩⟩ := h; exact ⟨ih1 h1, ih2 h2⟩
  | param n => exact h.2 ▸ h.1
