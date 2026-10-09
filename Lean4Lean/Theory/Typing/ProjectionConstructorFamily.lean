import Lean4Lean.Theory.Typing.EliminatorRestorationScope
import Lean4Lean.Theory.Typing.InductiveLemmas

/-! Concrete selectors for the functional environment metadata. Case entries
retain precisely the closed-header eligibility already required by `elimDF`.
No abstract schema is added to an ordinary installation. -/
namespace Lean4Lean.VEnv
open VExpr
variable {env : VEnv} {leftName rightName : Name} {leftInfo rightInfo : VProjectionInfo}
set_option Elab.async false

/-- The literal target of a constructor telescope fixes its structure family.
This uses raw constructor shape and constant lookup, not type injectivity. -/
theorem Ordered.projectionConstructor_family (ordered : env.Ordered)
    (left : env.projections leftName leftInfo) (right : env.projections rightName rightInfo)
    (same : leftInfo.ctorName = rightInfo.ctorName) :
    leftName = rightName ∧ leftInfo = rightInfo := by
  have leftLookup := ordered.projectionConstructor left
  have rightLookup := ordered.projectionConstructor right
  rw [same, rightLookup] at leftLookup
  have typeEq := congrArg VConstant.type (Option.some.inj leftLookup)
  obtain ⟨leftDecl, leftType, leftCtor, _, _, leftNameEq, _, _, _, _, _, _, leftTypeEq,
    _, _, _, leftRaw, _⟩ := ordered.projectionShape left
  obtain ⟨rightDecl, rightType, rightCtor, _, _, rightNameEq, _, _, _, _, _, _, rightTypeEq,
    _, _, _, rightRaw, _⟩ := ordered.projectionShape right
  obtain ⟨leftDomains, leftResult, leftShape, _, _, leftHead, leftArity⟩ := leftRaw.forallArity
  obtain ⟨rightDomains, rightResult, rightShape, _, _, rightHead, rightArity⟩ := rightRaw.forallArity
  have ctorEq : leftCtor.type = rightCtor.type := leftTypeEq.trans (typeEq.symm.trans rightTypeEq.symm)
  have lengthEq : leftDomains.length = rightDomains.length := by
    rw [← leftArity, ← rightArity, ctorEq]
  have leftParse := VExpr.takeForalls_wrapForalls leftDomains leftResult
  have rightParse := VExpr.takeForalls_wrapForalls rightDomains rightResult
  rw [← leftShape, ctorEq, lengthEq, rightShape, rightParse] at leftParse
  have resultEq := congrArg Prod.snd (Option.some.inj leftParse)
  have familyEq : leftName = rightName := by
    rw [← leftNameEq, ← rightNameEq]
    exact (VExpr.const.inj (leftHead.symm.trans
      ((congrArg (fun expression => expression.getAppFnArgs.1) resultEq.symm).trans rightHead))).1
  exact ⟨familyEq, ordered.projections_unique (familyEq ▸ left) right⟩

end Lean4Lean.VEnv

namespace Lean4Lean.CanonicalDataHead
open VEnv InductiveSignature
variable {env : VEnv}
set_option Elab.async false

end Lean4Lean.CanonicalDataHead
