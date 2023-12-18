import Lean4Lean.UnionFind

namespace Lean4Lean
namespace UnionFind

@[simp] theorem arr_push {m : UnionFind} : m.push.arr = m.arr.push ⟨m.arr.size, 0⟩ := rfl

@[simp] theorem parentD_push {arr : Array UFNode} :
    parentD (arr.push ⟨arr.size, 0⟩) a = parentD arr a := by
  simp [parentD]; split <;> split <;> try simp [Array.get_push, *]
  · next h1 h2 =>
    simp [Nat.lt_succ] at h1 h2
    exact Nat.le_antisymm h2 h1
  · next h1 h2 => cases h1 (Nat.lt_succ_of_lt h2)

@[simp] theorem parent_push {m : UnionFind} : m.push.parent a = m.parent a := by simp [parent]

@[simp] theorem rankD_push {arr : Array UFNode} :
    rankD (arr.push ⟨arr.size, 0⟩) a = rankD arr a := by
  simp [rankD]; split <;> split <;> try simp [Array.get_push, *]
  next h1 h2 => cases h1 (Nat.lt_succ_of_lt h2)

@[simp] theorem rank_push {m : UnionFind} : m.push.rank a = m.rank a := by simp [rank]

@[simp] theorem rankMax_push {m : UnionFind} : m.push.rankMax = m.rankMax := by simp [rankMax]

@[simp] theorem root_push {self : UnionFind} : self.push.root x = self.root x := by
  if h : self.parent x = x then
    rw [root_eq_self.2 h, root_eq_self.2]; rwa [parent_push]
  else
    have := Nat.sub_lt_sub_left (self.lt_rankMax x) (self.rank_lt h)
    rw [← root_parent, parent_push, root_push, root_parent]
termination_by _ => self.rankMax - self.rank x

def Equiv (self : UnionFind) (a b : Nat) : Prop := self.root a = self.root b

nonrec theorem Equiv.rfl : Equiv self a a := rfl
theorem Equiv.symm : Equiv self a b → Equiv self b a := .symm
theorem Equiv.trans : Equiv self a b → Equiv self b c → Equiv self a c := .trans

@[simp] theorem equiv_push : Equiv self.push a b ↔ Equiv self a b := by simp [Equiv]

-- theorem equiv_find : Equiv (self.find x).1 a b ↔ Equiv self a b := by simp [Equiv, find_root_1]
