import Lean4Lean.Theory.Typing.Pattern

/-! Finite syntactic overlap facts for generated generated iota patterns. -/

namespace Lean4Lean

theorem Subpattern.constVarN (H : Subpattern pattern ((Pattern.const name).varN count)) :
    ∃ nPrefix ≤ count, pattern = (Pattern.const name).varN nPrefix := by
  induction count with
  | zero => cases H; exact ⟨0, Nat.le_refl _, rfl⟩
  | succ count ih =>
    cases H with
    | refl => exact ⟨_, Nat.le_refl _, rfl⟩
    | varL h =>
      obtain ⟨nPrefix, hp, he⟩ := ih h
      exact ⟨nPrefix, by omega, he⟩

theorem Pattern.constVarN_inter (H : ((Pattern.const left).varN n).inter
    ((Pattern.const right).varN m) = some common) : left = right ∧ n = m := by
  induction n generalizing m common with
  | zero =>
    cases m with
    | zero =>
      simp only [Pattern.varN, Pattern.inter, Option.ite_none_right_eq_some,
        Option.some.injEq] at H
      exact ⟨H.1, rfl⟩
    | succ m => contradiction
  | succ n ih =>
    cases m with
    | zero => contradiction
    | succ m =>
      simp only [Pattern.varN, Pattern.inter, bind, Option.bind_eq_some_iff] at H
      obtain ⟨pattern, hp, _⟩ := H
      obtain ⟨hl, hm⟩ := ih hp
      exact ⟨hl, by omega⟩

theorem Pattern.iota_inter_constVarN
    (H : (SimplePattern.iota recursor major ctor fields).toPattern.inter
      ((Pattern.const name).varN count) = some common) :
    recursor = name ∧ count = major + 1 := by
  cases count with
  | zero => contradiction
  | succ count =>
    simp only [SimplePattern.toPattern, Pattern.varN, Pattern.inter, bind,
      Option.bind_eq_some_iff] at H
    obtain ⟨pattern, hp, _⟩ := H
    obtain ⟨hn, hc⟩ := Pattern.constVarN_inter hp
    exact ⟨hn, by omega⟩

/-- A full iota pattern cannot overlap a proper subpattern when a recursor
fixes its major position and no recursor is a constructor head. -/
theorem SimplePattern.iota_overlap
    (hmajor : recursor' = recursor → major' = major) (hctor : recursor' ≠ ctor)
    (hs : Subpattern sub (SimplePattern.iota recursor major ctor fields).toPattern)
    (hi : (SimplePattern.iota recursor' major' ctor' fields').toPattern.inter sub = some common) :
    sub = (SimplePattern.iota recursor major ctor fields).toPattern ∧
      recursor' = recursor ∧ major' = major ∧ ctor' = ctor ∧ fields' = fields := by
  cases hs with
  | refl =>
    simp only [SimplePattern.toPattern, Pattern.inter, bind, Option.bind_eq_some_iff] at hi
    obtain ⟨left, hl, right, hr, _⟩ := hi
    obtain ⟨hn, hm⟩ := Pattern.constVarN_inter hl
    obtain ⟨hc, hf⟩ := Pattern.constVarN_inter hr
    exact ⟨rfl, hn, hm, hc, hf⟩
  | appL hs =>
    obtain ⟨nPrefix, hp, rfl⟩ := hs.constVarN
    obtain ⟨hn, hm⟩ := Pattern.iota_inter_constVarN hi
    have := hmajor hn
    omega
  | appR hs =>
    obtain ⟨nPrefix, hp, rfl⟩ := hs.constVarN
    exact (hctor (Pattern.iota_inter_constVarN hi).1).elim

/-- The only fixed application node of a simple iota pattern is its root. -/
theorem Subpattern.iota_app
    (H : Subpattern (.app fn arg) (SimplePattern.iota recursor major ctor fields).toPattern) :
    fn = (Pattern.const recursor).varN major ∧ arg = (Pattern.const ctor).varN fields := by
  cases H with
  | refl => exact ⟨rfl, rfl⟩
  | appL h | appR h =>
    obtain ⟨n, _, he⟩ := h.constVarN
    cases n <;> cases he

theorem Subpattern.constVarN_noapp
    (H : Subpattern (.app fn arg) ((Pattern.const name).varN count)) : False := by
  obtain ⟨n, _, he⟩ := H.constVarN
  cases n <;> cases he

theorem Subpattern.constVarN_var
    (H : Subpattern (.var body) ((Pattern.const name).varN count)) :
    ∃ n < count, body = (Pattern.const name).varN n := by
  obtain ⟨n, hn, he⟩ := H.constVarN
  cases n with
  | zero => cases he
  | succ n => cases he; exact ⟨n, by omega, rfl⟩

theorem Subpattern.iota_const
    (H : Subpattern (.const name) (SimplePattern.iota recursor major ctor fields).toPattern) :
    name = recursor ∨ name = ctor := by
  cases H with
  | appL h =>
    obtain ⟨n, _, he⟩ := h.constVarN
    cases n with
    | zero => exact Or.inl (Pattern.const.inj he)
    | succ n => cases he
  | appR h =>
    obtain ⟨n, _, he⟩ := h.constVarN
    cases n with
    | zero => exact Or.inr (Pattern.const.inj he)
    | succ n => cases he

/-- Fixed recursor arity excludes an overlap with an earlier argument slot. -/
theorem SimplePattern.iota_app_l_uniq
    (hmajor : recursor = recursor' → major = major')
    (h : Subpattern (.var body) ((Pattern.const recursor).varN major)) :
    ((Pattern.const recursor').varN major').inter body = none := by
  obtain ⟨n, hn, rfl⟩ := h.constVarN_var
  cases hi : ((Pattern.const recursor').varN major').inter ((Pattern.const recursor).varN n) with
  | none => rfl
  | some common =>
    obtain ⟨he, hm⟩ := Pattern.constVarN_inter hi
    have := hmajor he.symm
    omega

/-- Recursor and constructor nodes remain disjoint throughout their spines. -/
theorem SimplePattern.iota_app_uniq
    (hne : recursor ≠ ctor)
    (h : Subpattern left ((Pattern.const recursor).varN major))
    (h' : Subpattern right ((Pattern.const ctor).varN fields)) : left.inter right = none := by
  obtain ⟨n, _, rfl⟩ := h.constVarN
  obtain ⟨m, _, rfl⟩ := h'.constVarN
  cases hi : ((Pattern.const recursor).varN n).inter ((Pattern.const ctor).varN m) with
  | none => rfl
  | some common => exact (hne (Pattern.constVarN_inter hi).1).elim

end Lean4Lean
