import Lean4Lean.Theory.Typing.HeadInjectivity.Projections.Typing

/-! # Projection field types under substitution

A companion of `VEnv.proj_typed` for a projection-registered structure: the field type
`fieldType` commutes with an arbitrary substitution (`VEnv.ProjTele.fieldType_subst`), from
the closedness of the telescope's domains (`ProjTele.closedN_dom`) and the substitution of
each instantiated field domain (`ProjTele.dom_subst`). -/

namespace Lean4Lean
open VExpr

theorem VExpr.argSubst_comp_lt (as : List VExpr) (σ : VExpr.Subst) {m : Nat}
    (h : m < as.length) :
    (argSubst as m).subst σ = argSubst (as.map (·.subst σ)) m := by
  rw [argSubst_lt _ h, argSubst_lt _ (by simpa using h)]
  simp

namespace VEnv
variable {env : VEnv} {U : Nat}

theorem projsOf_subst (S : Name) (w : VExpr) (j : Nat) (σ : VExpr.Subst) :
    (projsOf S w j).map (·.subst σ) = projsOf S (w.subst σ) j := by
  simp [projsOf, VExpr.subst]


/-- The domains of a projection telescope are closed at their depth. -/
theorem ProjTele.closedN_dom (henv : env.OrderedStrong) {S : Name} {info : VProjectionInfo}
    {ls : List VLevel} {D : List VExpr} {R0 : VExpr} (T : ProjTele env U S info ls D R0)
    (k : Nat) (hk : k < D.length) : (D[k]).ClosedN k := by
  obtain ⟨u, hu⟩ := T.doms k hk
  have := hu.closedN henv (CtxWF.closed henv (T.ctx k (by omega)))
  simpa [Nat.min_eq_left (Nat.le_of_lt hk)] using this

/-- The instantiated field domain commutes with substitution. -/
theorem ProjTele.dom_subst (henv : env.OrderedStrong) {S : Name} {info : VProjectionInfo}
    {ls : List VLevel} {D : List VExpr} {R0 : VExpr} (T : ProjTele env U S info ls D R0)
    {ps : List VExpr} (hpl : ps.length = info.nparams) (w : VExpr) {j : Nat}
    (hj : info.nparams + j < D.length) (σ : VExpr.Subst) :
    ((D[info.nparams + j]).subst (VExpr.argSubst (ps ++ projsOf S w j))).subst σ =
      (D[info.nparams + j]).subst
        (VExpr.argSubst (ps.map (·.subst σ) ++ projsOf S (w.subst σ) j)) := by
  rw [VExpr.subst_subst, ← projsOf_subst, ← List.map_append]
  apply VExpr.subst_congr_closedN (T.closedN_dom henv _ hj)
  intro i hi
  exact VExpr.argSubst_comp_lt _ σ (by simp [projsOf, hpl]; omega)

/-- **`fieldType` commutes with substitution.** -/
theorem ProjTele.fieldType_subst (henv : env.OrderedStrong) {S : Name} {info : VProjectionInfo}
    {ls : List VLevel} {D : List VExpr} {R0 : VExpr} (T : ProjTele env U S info ls D R0)
    (hlen : ls.length = info.uvars) {ps : List VExpr} (hpl : ps.length = info.nparams)
    {w : VExpr} {j : Nat} (hj : info.nparams + j < D.length) (σ : VExpr.Subst) {F : VExpr}
    (hF : info.fieldType S ls ps j w = some F) :
    info.fieldType S ls (ps.map (·.subst σ)) j (w.subst σ) = some (F.subst σ) := by
  rw [T.fieldType hlen hpl w hj, Option.some.injEq] at hF
  subst hF
  rw [T.fieldType hlen (by simpa using hpl) _ hj, T.dom_subst henv hpl w hj σ]

end VEnv
end Lean4Lean
