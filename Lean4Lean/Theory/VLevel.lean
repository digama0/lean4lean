import Std
import Lean4Lean.Std.Logic

namespace Lean4Lean
open Lean

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

variable (ls : List Nat) in
def eval : VLevel → Nat
  | .zero => 0
  | .succ l => l.eval + 1
  | .max l₁ l₂ => l₁.eval.max l₂.eval
  | .imax l₁ l₂ => l₁.eval.imax l₂.eval
  | .param i => ls.getD i 0

variable (ls : List Name) in
def toLevel : VLevel → Level
  | .zero => .zero
  | .succ l => .succ l.toLevel
  | .max l₁ l₂ => .max l₁.toLevel l₂.toLevel
  | .imax l₁ l₂ => .imax l₁.toLevel l₂.toLevel
  | .param n => match ls.get? n with
    | some l => .param l
    | none => .zero

protected def LE (a b : VLevel) : Prop := ∀ ls, a.eval ls ≤ b.eval ls

instance : LE VLevel := ⟨VLevel.LE⟩

theorem le_refl (a : VLevel) : a ≤ a := fun _ => Nat.le_refl _
theorem le_trans {a b c : VLevel} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  fun _ => Nat.le_trans (h1 _) (h2 _)

protected def Equiv (a b : VLevel) : Prop := a.eval = b.eval

instance : HasEquiv VLevel := ⟨VLevel.Equiv⟩

theorem le_antisymm_iff {a b : VLevel} : a ≈ b ↔ a ≤ b ∧ b ≤ a :=
  funext_iff.trans <| (forall_congr' fun _ => Nat.le_antisymm_iff).trans forall_and

theorem toLevel_inj {ls : List Name} (d : ls.Nodup)
    {l₁ l₂ : VLevel} (eq : l₁.toLevel ls = l₂.toLevel ls) : l₁ = l₂ := sorry

variable (ls : List VLevel) in
def inst : VLevel → VLevel
  | .zero => .zero
  | .succ l => .succ l.inst
  | .max l₁ l₂ => .max l₁.inst l₂.inst
  | .imax l₁ l₂ => .imax l₁.inst l₂.inst
  | .param i => ls.getD i .zero

variable (ls : List Name) in
def ofLevel : Level → Option VLevel
  | .zero => return .zero
  | .succ l => return .succ (← ofLevel l)
  | .max l₁ l₂ => return .max (← ofLevel l₁) (← ofLevel l₂)
  | .imax l₁ l₂ => return .imax (← ofLevel l₁) (← ofLevel l₂)
  | .param n =>
    let i := ls.indexOf n
    if i < ls.length then some (.param i) else none
  | .mvar _ => none
