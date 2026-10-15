import Lean
import Init.Data.Nat.ToString

namespace Lean4Lean.AddInductive
open Lean

def freshElimName.candidate (index : Nat) : Name :=
  .str .anonymous ("u_" ++ toString index)

private def elimNameLength : Name → Nat
  | .str _ text => text.length
  | _ => 0

private def elimNameLengthBound : List Name → Nat
  | [] => 1
  | name :: names => max (elimNameLength name) (elimNameLengthBound names)

private theorem elimNameLengthBound_pos (names : List Name) :
    0 < elimNameLengthBound names := by
  induction names with
  | nil => decide
  | cons name names induction =>
    exact Nat.lt_of_lt_of_le induction (Nat.le_max_right _ _)

private theorem elimNameLength_le_bound {names : List Name} {name : Name}
    (member : name ∈ names) : elimNameLength name ≤ elimNameLengthBound names := by
  induction names with
  | nil => cases member
  | cons head names induction =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (induction member) (Nat.le_max_right _ _)

private theorem elimNameIndex_lt_bound {names : List Name} {index : Nat}
    (member : freshElimName.candidate index ∈ names) :
    index < 10 ^ elimNameLengthBound names := by
  have lengthBound := elimNameLength_le_bound member
  have reprBound : index.repr.length ≤ elimNameLengthBound names := by
    change ("u_" ++ toString index).length ≤ elimNameLengthBound names at lengthBound
    simp only [String.length_append, Nat.toString_eq_repr] at lengthBound
    omega
  exact (Nat.length_repr_le_iff (elimNameLengthBound_pos names)).mp reprBound

def freshElimName.loop (names : List Name) (index : Nat) : Name :=
  if member : freshElimName.candidate index ∈ names then
    loop names (index + 1)
  else
    freshElimName.candidate index
termination_by 10 ^ elimNameLengthBound names - index
decreasing_by
  have bound := elimNameIndex_lt_bound member
  omega

def freshElimName (names : List Name) : Name :=
  if `u ∈ names then freshElimName.loop names 1 else `u

end Lean4Lean.AddInductive
