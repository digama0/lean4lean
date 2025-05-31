import Lean4Lean.Theory.VLevel
import Lean4Lean.Level
import Lean4Lean.Verify.Axioms
import Std.Tactic.BVDecide

namespace Lean.Level
open Lean4Lean

-- variable (ls : List Name) in
-- def _root_.Lean4Lean.VLevel.toLevel : VLevel → Level
--   | .zero => .zero
--   | .succ l => .succ l.toLevel
--   | .max l₁ l₂ => .max l₁.toLevel l₂.toLevel
--   | .imax l₁ l₂ => .imax l₁.toLevel l₂.toLevel
--   | .param n => match ls.get? n with
--     | some l => .param l
--     | none => .zero

-- theorem toLevel_inj {ls : List Name} (d : ls.Nodup)
--     {l₁ l₂ : VLevel} (eq : l₁.toLevel ls = l₂.toLevel ls) : l₁ = l₂ := sorry

def realHasParam : Level → Bool
  | .param .. => true
  | .zero | .mvar .. => false
  | .succ l => l.realHasParam
  | .max l₁ l₂ | .imax l₁ l₂ => l₁.realHasParam || l₂.realHasParam

def realHasMVar : Level → Bool
  | .mvar .. => true
  | .zero | .param .. => false
  | .succ l => l.realHasMVar
  | .max l₁ l₂ | .imax l₁ l₂ => l₁.realHasMVar || l₂.realHasMVar

theorem Safe.succ : Safe (.succ u) → Safe u := by simp [Safe, realDepth]; omega
theorem Safe.max : Safe (.max u v) → Safe u ∧ Safe v := by
  simp [Safe, realDepth, Nat.max_eq_max, Nat.max_lt]; omega
theorem Safe.imax : Safe (.imax u v) → Safe u ∧ Safe v := Safe.max

theorem mkData_depth (H : d < 2 ^ 24) : (mkData h d hmv hp).depth.toNat = d := by
  rw [mkData, if_neg (Nat.not_lt.2 (Nat.le_sub_one_of_lt H)), Data.depth]
  have : d.toUInt64.toUInt32.toNat = d := by simp; omega
  refine .trans ?_ this; congr 2
  rw [← UInt64.toBitVec_inj]
  have : d.toUInt64.toNat = d := by simp; omega
  have : d.toUInt64.toBitVec ≤ 0xffffff#64 := (this ▸ Nat.le_sub_one_of_lt H :)
  have : h.toUInt32.toUInt64.toBitVec ≤ 0xffffffff#64 := Nat.le_of_lt_succ h.toUInt32.1.1.2
  have hb : ∀ (b : Bool), b.toUInt64.toBitVec ≤ 1#64 := by decide
  have := hb hmv; have := hb hp
  change (
    h.toUInt32.toUInt64.toBitVec +
    hmv.toUInt64.toBitVec <<< 32#64 +
    hp.toUInt64.toBitVec <<< 33#64 +
    d.toUInt64.toBitVec <<< 40#64) >>> 40#64 = d.toUInt64.toBitVec
  bv_decide

theorem mkData_hasParam (H : d < 2 ^ 24) : (mkData h d hmv hp).hasParam = hp := by
  rw [mkData, if_neg (Nat.not_lt.2 (Nat.le_sub_one_of_lt H))]
  simp [Data.hasParam, (· == ·), ← UInt64.toBitVec_inj]
  have : h.toUInt32.toUInt64.toBitVec ≤ 0xffffffff#64 := Nat.le_of_lt_succ h.toUInt32.1.1.2
  have hb : ∀ (b : Bool), b.toUInt64.toBitVec ≤ 1#64 := by decide
  have := hb hmv; have := hb hp
  let L := ((
    h.toUInt32.toUInt64.toBitVec +
    hmv.toUInt64.toBitVec <<< 32#64 +
    hp.toUInt64.toBitVec <<< 33#64 +
    d.toUInt64.toBitVec <<< 40#64) >>> 33#64) &&& 1#64
  change decide (L = 1#64) = hp
  rw [show L = hp.toUInt64.toBitVec by bv_decide]
  cases hp <;> decide

theorem mkData_hasMVar (H : d < 2 ^ 24) : (mkData h d hmv hp).hasMVar = hmv := by
  rw [mkData, if_neg (Nat.not_lt.2 (Nat.le_sub_one_of_lt H))]
  simp [Data.hasMVar, (· == ·), ← UInt64.toBitVec_inj]
  have : h.toUInt32.toUInt64.toBitVec ≤ 0xffffffff#64 := Nat.le_of_lt_succ h.toUInt32.1.1.2
  have hb : ∀ (b : Bool), b.toUInt64.toBitVec ≤ 1#64 := by decide
  have := hb hmv; have := hb hp
  let L := ((
    h.toUInt32.toUInt64.toBitVec +
    hmv.toUInt64.toBitVec <<< 32#64 +
    hp.toUInt64.toBitVec <<< 33#64 +
    d.toUInt64.toBitVec <<< 40#64) >>> 32#64) &&& 1#64
  change decide (L = 1#64) = hmv
  rw [show L = hmv.toUInt64.toBitVec by bv_decide]
  cases hmv <;> decide

theorem Safe.depth_eq {l : Level} (hl : l.Safe) : l.depth = l.realDepth := by
  simp [Safe] at hl
  have {n a} : n + 1 < a → n < a := by omega
  induction l <;> (try specialize this hl) <;>
    simp_all [depth, data, mkData_depth, realDepth, Nat.max_lt]

theorem Safe.hasParam_eq {l : Level} (hl : l.Safe) : l.hasParam = l.realHasParam := by
  have depth_eq := @Safe.depth_eq; simp [Safe, depth] at depth_eq
  simp [Safe] at hl
  have {n a} : n + 1 < a → n < a := by omega
  induction l <;> (try specialize this hl) <;>
    simp_all [hasParam, data, mkData_hasParam, realHasParam, realDepth, Nat.max_lt]

theorem Safe.hasMVar_eq {l : Level} (hl : l.Safe) : l.hasMVar = l.realHasMVar := by
  have depth_eq := @Safe.depth_eq; simp [Safe, depth] at depth_eq
  simp [Safe] at hl
  have {n a} : n + 1 < a → n < a := by omega
  induction l <;> (try specialize this hl) <;>
    simp_all [hasMVar, data, mkData_hasMVar, realHasMVar, realDepth, Nat.max_lt]

theorem ofLevel_of_not_realHasParam (Us) {l : Level}
    (hl : l.realHasParam = false) (hmv : l.realHasMVar = false) :
    ∃ u', VLevel.ofLevel Us l = some u' := by
  induction l <;> simp_all [realHasParam, realHasMVar, VLevel.ofLevel, exists_comm]

def getUndefParam.F (ps : List Name) (l : Level) : StateT (Option Name) Id Bool := do
  if !l.hasParam || (← get).isSome then
    return false
  if let .param n := l then
    if n ∉ ps then
      set (some n)
  return true

theorem getUndefParam_none {l : Level} (hl : l.Safe) (hmv : l.realHasMVar = false) :
    l.getUndefParam Us = none → ∃ u', VLevel.ofLevel Us l = some u' := by
  suffices ∀ s, ((l.forEach (getUndefParam.F Us)).run s).snd = none → s = none ∧ _ from
    (this _ · |>.2)
  have {l} (hl : l.Safe) (hmv : l.realHasMVar = false)
      {g} (H : ∀ {s'}, (g.run s').snd = none → s' = none ∧
       ((getUndefParam.F Us l).run none = (true, none) → ∃ u', VLevel.ofLevel Us l = some u')) (s) :
      ((do if (!(← getUndefParam.F Us l)) = true then pure PUnit.unit else g).run s).snd = none →
      s = none ∧ ∃ u', VLevel.ofLevel Us l = some u' := by
    simp; split <;> rename_i h
    · simp; revert h
      simp [getUndefParam.F]; split <;> [simp; split <;> [split <;> simp; simp]]
      rintro rfl; simp at *
      exact ofLevel_of_not_realHasParam Us (hl.hasParam_eq.symm.trans ‹_›) hmv
    · refine fun h' => let ⟨h1, h2⟩ := H h'; have := ?_; ⟨this, h2 ?_⟩
      · revert h h1
        simp [getUndefParam.F]; split <;> [simp; split <;> [split <;> simp; simp]]
      · revert h h1; subst s
        cases (getUndefParam.F Us l).run none; simp; rintro rfl rfl; rfl
  have lt {n a} : n + 1 < a → n < a := by omega
  induction l with (
    refine this hl hmv fun h => ?_; clear this
    simp [realHasMVar, VLevel.ofLevel, *] at *)
  | succ _ ih =>
    have ⟨h, _, h1⟩ := ih hl.succ hmv _ h
    exact ⟨h, fun _ => ⟨_, _, h1, rfl⟩⟩
  | max _ _ ih1 ih2 | imax _ _ ih1 ih2 =>
    have ⟨h, _, h2⟩ := ih2 hl.max.2 hmv.2 _ h
    have ⟨h, _, h1⟩ := ih1 hl.max.1 hmv.1 _ h
    exact ⟨h, fun _ => ⟨_, _, h1, _, h2, rfl⟩⟩
  | param =>
    simp [getUndefParam.F, hl.hasParam_eq, Id, realHasParam, List.idxOf_lt_length_iff, *]
    split <;> simp [*]
  | _ => simp [*]
