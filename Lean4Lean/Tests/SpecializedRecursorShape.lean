import Lean4Lean.Theory.Typing.RecursorLemmas

/-! Small, proof-checked examples of specialized recursor shapes. These use
no admitted typing or inversion theorem: they test the representation itself.
Executable tests against the actual `Lean.Syntax` recursors are in
`NestedRecursorReduction`. -/

namespace Lean4Lean.Tests.SpecializedRecursorShape

private def nat : VExpr := .const ``Nat []
private def listNat : VExpr := .app (.const ``List [.zero]) nat
private def recType : VExpr := .forallE listNat nat
private def consRule : VDefEq where
  uvars := 0
  lhs := VExpr.wrapLams [nat, listNat]
    (.app (.const `specialized [])
      (VExpr.mkApps (.const ``List.cons [.zero]) [nat, .bvar 1, .bvar 0]))
  rhs := VExpr.wrapLams [nat, listNat] (.bvar 1)
  type := VExpr.wrapForalls [nat, listNat] nat

private def env : VEnv where
  constants := fun name => if name = `specialized then some ⟨0, recType⟩ else none
  defeqs := (· = consRule)

/-- No recursor parameters, one constructor parameter, supplied as an expression. -/
def specialized : VRecursorShape env `specialized 0 0 1 0 0 0 ``List [.zero] [nat] where
  ctorParams_length := rfl
  ctorParams_closed := by simp [nat, VExpr.ClosedN]
  type := recType
  const := by simp [env]
  doms := [listNat]
  result := nat
  type_eq := rfl
  doms_length := rfl
  major_eq := rfl

/-- The rule uses exactly the same specialization as the major-premise type. -/
def specializedRule :
    VIotaRuleShape env `specialized 0 0 1 0 0 0 ``List.cons [.zero] 2 consRule [nat] where
  defeq := rfl
  uvars := rfl
  doms := [nat, listNat]
  lhsBody := .app (.const `specialized [])
    (VExpr.mkApps (.const ``List.cons [.zero]) [nat, .bvar 1, .bvar 0])
  rhsBody := .bvar 1
  typeBody := nat
  lhs_eq := rfl
  rhs_eq := rfl
  type_eq := rfl
  doms_length := rfl
  indexArgs := []
  indexArgs_length := rfl
  lhs_pattern := rfl
  rec_doms := fun _ _ _ _ _ hj => absurd hj (Nat.not_lt_zero _)
  ctor_doms := fun _ _ _ hc => by simp [env] at hc

/-- Specialization expressions can depend on a recursor parameter rather than
merely selecting a prefix of those parameters. -/
example : (VExpr.app (.const ``List [.zero]) (.bvar 0)).ClosedN 1 := by
  simp [VExpr.ClosedN]

/-- A parameter cannot refer to a motive, minor, or index binder. -/
example : ¬ ∃ s : VRecursorShape env `specialized 0 0 1 0 0 0 ``List [.zero] [.bvar 0],
    True := by
  rintro ⟨s, _⟩
  have h := s.ctorParams_closed (.bvar 0) (by simp)
  exact (Nat.not_lt_zero 0) h

end Lean4Lean.Tests.SpecializedRecursorShape
