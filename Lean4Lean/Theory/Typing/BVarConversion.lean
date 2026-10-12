import Lean4Lean.Theory.Typing.Strong

/-! Transport through the explicit conversions in a variable typing.
Each conversion casts the equality directly; no equality between the sorts
of successive conversions is needed. -/

namespace Lean4Lean.VEnv

variable {env : VEnv} {U : Nat}

private theorem HasTypeStrong.bvar_type_iff
    (H : env.HasTypeStrong U Γ e A b) (he : e = .bvar i)
    (hlookup : Lookup Γ i B) :
    env.IsDefEq U Γ e₁ e₂ A ↔ env.IsDefEq U Γ e₁ e₂ B := by
  induction H generalizing i B with
  | bvar hl _ _ =>
    cases he
    cases hl.uniq hlookup
    exact Iff.rfl
  | base _ ih => exact ih he hlookup
  | defeq _ hab _ _ _ _ _ ih =>
    have ih := ih he hlookup
    exact ⟨fun h => ih.mp (.defeqDF hab.defeq.symm h),
      fun h => .defeqDF hab.defeq (ih.mpr h)⟩
  | _ => cases he

/-- Any equality can be transported between two types assigned to the same
variable. Both typings lead to its unique lookup type, and their conversion
steps can be traversed in either direction. -/
theorem IsDefEq.transport_bvar (H : env.IsDefEq U Γ e₁ e₂ A)
    (henv : env.OrderedStrong) (hΓ : OnCtx Γ (env.IsType U))
    (ha : env.HasType U Γ (.bvar i) A) (hb : env.HasType U Γ (.bvar i) B) :
    env.IsDefEq U Γ e₁ e₂ B := by
  obtain ⟨C, hC⟩ := ha.bvar_inv henv hΓ
  have sa := (ha.strong henv hΓ).hasType'.1
  have sb := (hb.strong henv hΓ).hasType'.1
  exact (sb.bvar_type_iff rfl hC).mpr ((sa.bvar_type_iff rfl hC).mp H)

end Lean4Lean.VEnv
