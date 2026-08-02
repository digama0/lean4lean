import Batteries.Tactic.OpenPrivate
import Lean4Lean.Theory.VLevel
import Lean4Lean.Verify.Axioms

open private go in Lean.Level.geq

namespace Lean.Level.Semantics

open Lean4Lean

/-!
Semantic soundness of the universe-level operations in Lean's standard library.
The semantic behavior of `normalize` remains an explicit assumption because it
is an opaque `partial def`. In contrast, the exact correspondence between
`geqCore` below and the private recursion used by `Lean.Level.geq` is proved.
-/

variable (ρ : Name → Nat) (μ : LMVarId → Nat) in
def eval : Level → Nat
  | .zero => 0
  | .param n => ρ n
  | .mvar n => μ n
  | .succ l => eval l + 1
  | .max l₁ l₂ => Nat.max (eval l₁) (eval l₂)
  | .imax l₁ l₂ => Nat.imax (eval l₁) (eval l₂)

private def offset : Level → Nat
  | .succ l => offset l + 1
  | _ => 0

private theorem getOffsetAux_eq_offset :
    l.getOffsetAux k = offset l + k := by
  induction l generalizing k with
  | succ l ih => simp only [Level.getOffsetAux, offset, ih]; omega
  | _ => simp [Level.getOffsetAux, offset]

private theorem getOffset_eq_offset : l.getOffset = offset l := by
  simp [Level.getOffset, getOffsetAux_eq_offset]

theorem eval_eq_getLevelOffset_add_getOffset :
    eval ρ μ l = eval ρ μ l.getLevelOffset + l.getOffset := by
  induction l with
  | succ l ih =>
    simp only [eval, Level.getLevelOffset, getOffset_eq_offset, offset, ih]
    omega
  | _ => rfl

theorem fallback_sound
    (h : (u.getLevelOffset = v.getLevelOffset ∨ v.getLevelOffset.isZero = true) ∧
      v.getOffset ≤ u.getOffset) :
    eval ρ μ v ≤ eval ρ μ u := by
  calc
    eval ρ μ v = eval ρ μ v.getLevelOffset + v.getOffset :=
      eval_eq_getLevelOffset_add_getOffset
    _ ≤ eval ρ μ u.getLevelOffset + u.getOffset := by
      rcases h with ⟨hv | hv, hk⟩
      · rw [← hv]; omega
      · have hv : v.getLevelOffset = .zero := by
          generalize hbase : v.getLevelOffset = base at hv
          cases base <;> simp_all [Level.isZero]
        simp [hv, eval]
        omega
    _ = eval ρ μ u := eval_eq_getLevelOffset_add_getOffset.symm

def geqCore : Level → Level → Bool
  -- Keep this in the same source-shaped form as `go`'s `u == v || ...` prefix.
  -- The apparently redundant `|| true` is therefore deliberate.
  | u, .zero => u == .zero || true
  | u, .max v₁ v₂ => u == .max v₁ v₂ || (geqCore u v₁ && geqCore u v₂)
  | .max u₁ u₂, .imax v₁ v₂ =>
    (.max u₁ u₂ : Level) == .imax v₁ v₂ ||
      (geqCore u₁ (.imax v₁ v₂) || geqCore u₂ (.imax v₁ v₂) ||
        (geqCore (.max u₁ u₂) v₁ && geqCore (.max u₁ u₂) v₂))
  | .max u₁ u₂, v =>
    let u := .max u₁ u₂
    u == v || (geqCore u₁ v || geqCore u₂ v ||
      ((u.getLevelOffset == v.getLevelOffset || v.getLevelOffset.isZero) &&
        u.getOffset ≥ v.getOffset))
  | .imax u₁ u₂, v => (.imax u₁ u₂ : Level) == v || geqCore u₂ v
  | .succ u, .succ v => (.succ u : Level) == .succ v || geqCore u v
  | u, .imax v₁ v₂ => u == .imax v₁ v₂ || (geqCore u v₁ && geqCore u v₂)
  | u, v => u == v ||
    ((u.getLevelOffset == v.getLevelOffset || v.getLevelOffset.isZero) &&
      u.getOffset ≥ v.getOffset)
  termination_by u v => (u, v)

private theorem geqCore_eq_go : geqCore u v = go u v := by
  fun_induction go
  next u v ih₁ ih₂ =>
    cases u <;> cases v <;> simp_all [geqCore, go]

theorem geqCore_sound (h : geqCore u v) : eval ρ μ v ≤ eval ρ μ u := by
  induction u, v using geqCore.induct <;>
    simp only [geqCore, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h
  case case1 => simp [eval]
  case case2 ih₂ ih₁ =>
    rcases h with rfl | ⟨h₁, h₂⟩
    · exact Nat.le_refl _
    · exact (Nat.max_le).2 ⟨ih₂ h₁, ih₁ h₂⟩
  case case3 u₁ u₂ v₁ v₂ ih₄ ih₃ ih₂ ih₁ =>
    rcases h with heq | (h | h) | ⟨h₁, h₂⟩
    · exact Nat.le_of_eq (congrArg (eval ρ μ) heq).symm
    · exact Nat.le_trans (ih₄ h) (Nat.le_max_left ..)
    · exact Nat.le_trans (ih₃ h) (Nat.le_max_right ..)
    · simp only [eval, Nat.imax]
      split
      · exact Nat.zero_le _
      · exact (Nat.max_le).2 ⟨ih₂ h₁, ih₁ h₂⟩
  case case4 u₁ u₂ v _ _ _ ih₂ ih₁ =>
    rcases h with rfl | h
    · exact Nat.le_refl _
    · rcases h with h | h
      · rcases h with h | h
        · exact Nat.le_trans (ih₂ h) (Nat.le_max_left ..)
        · exact Nat.le_trans (ih₁ h) (Nat.le_max_right ..)
      · exact fallback_sound h
  case case5 u₁ u₂ v _ _ ih =>
    rcases h with rfl | h
    · exact Nat.le_refl _
    · simp only [eval, Nat.imax]
      have hv := ih h
      split <;> rename_i hz
      · simpa [hz] using hv
      · exact Nat.le_trans hv (Nat.le_max_right ..)
  case case6 u v ih =>
    rcases h with heq | h
    · exact Nat.le_of_eq (congrArg (eval ρ μ) heq).symm
    · simpa [eval] using Nat.add_le_add_right (ih h) 1
  case case7 u v₁ v₂ _ _ ih₂ ih₁ =>
    rcases h with rfl | ⟨h₁, h₂⟩
    · exact Nat.le_refl _
    · simp only [eval, Nat.imax]
      split
      · exact Nat.zero_le _
      · exact (Nat.max_le).2 ⟨ih₂ h₁, ih₁ h₂⟩
  case case8 =>
    rcases h with heq | h
    · exact Nat.le_of_eq (congrArg (eval ρ μ) heq).symm
    · exact fallback_sound h

/-- Semantic specification for the opaque `partial def` `Lean.Level.normalize`
in [Lean 4.30's `Lean/Level.lean`](https://github.com/leanprover/lean4/blob/v4.30.0/src/Lean/Level.lean#L379-L401).

This is the sole additional trust assumption in this file and must be audited
when the pinned Lean toolchain changes. -/
axiom eval_normalize : eval ρ μ l.normalize = eval ρ μ l

theorem geq_eq_core :
    Lean.Level.geq u v = geqCore (Lean.Level.normalize u) (Lean.Level.normalize v) := by
  simp [Lean.Level.geq, geqCore_eq_go]

theorem isEquiv_sound (h : Lean.Level.isEquiv u v) : eval ρ μ u = eval ρ μ v := by
  simp only [Level.isEquiv, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · rfl
  · rw [← eval_normalize (l := u), ← eval_normalize (l := v), h]

theorem geq_sound (h : Lean.Level.geq u v) : eval ρ μ v ≤ eval ρ μ u := by
  rw [geq_eq_core] at h
  rw [← eval_normalize (l := u), ← eval_normalize (l := v)]
  exact geqCore_sound h

theorem eval_ofLevel (h : VLevel.ofLevel Us l = some l') :
    l'.eval ns = eval (fun n => ns.getD (Us.idxOf n) 0) μ l := by
  induction l generalizing l' with
  | zero => simp [VLevel.ofLevel] at h; cases h; rfl
  | succ l ih =>
    simp [VLevel.ofLevel, bind] at h
    obtain ⟨l', hl, rfl⟩ := h
    simp [VLevel.eval, eval, ih hl]
  | max l₁ l₂ ih₁ ih₂ | imax l₁ l₂ ih₁ ih₂ =>
    simp [VLevel.ofLevel, bind] at h
    obtain ⟨l₁', hl₁, l₂', hl₂, rfl⟩ := h
    simp [VLevel.eval, eval, ih₁ hl₁, ih₂ hl₂]
  | param n =>
    simp [VLevel.ofLevel] at h
    obtain ⟨hidx, rfl⟩ := h
    simp [VLevel.eval, eval]
  | mvar n => simp [VLevel.ofLevel] at h

theorem isEquiv_wf (h : Lean.Level.isEquiv u v)
    (hu : VLevel.ofLevel Us u = some u') (hv : VLevel.ofLevel Us v = some v') : u' ≈ v' := by
  rw [VLevel.equiv_def]
  intro ns
  rw [eval_ofLevel (μ := fun _ => 0) hu, eval_ofLevel (μ := fun _ => 0) hv]
  exact isEquiv_sound (μ := fun _ => 0) h

theorem geq_wf (h : Lean.Level.geq u v)
    (hu : VLevel.ofLevel Us u = some u') (hv : VLevel.ofLevel Us v = some v') : v' ≤ u' := by
  intro ns
  rw [eval_ofLevel (μ := fun _ => 0) hv, eval_ofLevel (μ := fun _ => 0) hu]
  exact geq_sound (μ := fun _ => 0) h

end Lean.Level.Semantics
