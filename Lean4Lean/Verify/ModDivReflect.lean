import Lean4Lean.Verify.ModDivCondition

namespace Lean4Lean.Environment
open Lean VEnv

/-- The exact source expression obtained by instantiating the two binders of the
closed top-level division equation. -/
def natDivTopRhsInst (a b : Nat) : Expr :=
  ((natDivTopRhs (.bvar 1) (.bvar 0)).instantiate1'
    (.natLitToConstructor a) 1).instantiate1' (.natLitToConstructor b)

theorem natDivTopRhsInst_eq (a b : Nat) :
    natDivTopRhsInst a b =
      natDivTopRhs (.natLitToConstructor a) (.natLitToConstructor b) := by
  simp [natDivTopRhsInst, natDivTopRhs, Condition.reflectedDITE,
    Condition.natLE, Reflection.natDITE, Reflection.defn₁,
    Lean.Expr.instantiate1', Lean.Expr.liftLooseBVars', Lean.mkAppN,
    Expr.lam0, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB]
  simpa using
    (Expr.instantiate1'_liftLooseBVars
      (e := .natLitToConstructor a) (a := .natLitToConstructor b)
      (s := 0) (d := 1))

/-- Instantiate the closed top-level division equation at two concrete
naturals, retaining the translated reflected-selector RHS. -/
theorem VEnv.instantiate_natDivTop_equation
    {env : VEnv} (wf : env.WF)
    (hctors : VEnv.HasNatBoolConstructors env)
    {divFn : Expr} {divV topL topR : VExpr}
    (hdivFn : TrExprS env [] [] divFn divV)
    (hdivFnClosed : divFn.looseBVarRange' = 0)
    (hl : TrExprS env [] [] (natDivTopEquation divFn).1 topL)
    (hr : TrExprS env [] [] (natDivTopEquation divFn).2 topR)
    (heq : env.IsDefEqU 0 [] topL topR)
    (a b : Nat) :
    ∃ rhs,
      TrExprS env [] []
        (natDivTopRhsInst a b) rhs ∧
      env.IsDefEqU 0 []
        (.app (.app divV (.natLit a)) (.natLit b)) rhs := by
  have ⟨hnatS, hnatTy⟩ : TrExprS env [] [] q(Nat) .nat ∧
      env.IsType 0 [] .nat := by
    have hzT := (hctors.natZeroS (Us := []) (Δ := [])).2
    obtain ⟨u, hnatTy⟩ := hzT.isType wf trivial
    obtain ⟨ci, hci, _, hlen⟩ := hnatTy.const_inv wf trivial
    exact ⟨.const hci rfl (by simpa using hlen), ⟨u, hnatTy⟩⟩
  have haLit := hctors.natLitS a (Us := []) (Δ := [])
  have hbLit := hctors.natLitS b (Us := []) (Δ := [])
  cases haLit.1 with
  | lit _ haS =>
    cases hbLit.1 with
    | lit _ hbS =>
      simp only [natDivTopEquation] at hl hr
      obtain ⟨l₁, r₁, hl₁, hr₁, heq₁⟩ :=
        VEnv.instantiate_lam_equation wf
          (ty := q(Nat)) (by trivial) hl hr heq hnatS haS haLit.2
          (by trivial)
      obtain ⟨l₂, r₂, hl₂, hr₂, heq₂⟩ :=
        VEnv.instantiate_lam_equation wf
          (ty := q(Nat)) (by trivial) hl₁ hr₁ heq₁ hnatS hbS hbLit.2
          (by trivial)
      have hr₂' : TrExprS env [] []
          (natDivTopRhsInst a b) r₂ := by
        simpa [natDivTopRhsInst, Literal.toConstructor] using hr₂
      cases hl₂ with
      | app hinnerT hbT hinner hbLocalS =>
        cases hinner with
        | app hfnT haT hfnLocalS haLocalS =>
          have hctx : VLCtx.IsDefEq env 0 [] [] := .refl wf trivial
          have hfnLocalS' := hfnLocalS
          simp [Expr.instantiate1'_eq_self (by rw [hdivFnClosed]; omega)]
            at hfnLocalS'
          have haLocalS' := haLocalS
          have hbLocalS' := hbLocalS
          simp [Lean.Expr.instantiate1', Expr.instantiate1'_liftLooseBVars_0]
            at haLocalS' hbLocalS'
          have hfnEq := TrExprS.uniq (Us := []) wf hctx hfnLocalS' hdivFn
          have haEq := TrExprS.uniq (Us := []) wf hctx haLocalS' haS
          have hbEq := TrExprS.uniq (Us := []) wf hctx hbLocalS' hbS
          have hfnApp := hfnEq.app_same wf trivial hfnT haT
          have hdivT := (hfnEq.of_l wf trivial hfnT).hasType.2
          have haApp := haEq.app_arg wf trivial hdivT haT
          have hinnerEq := hfnApp.trans wf trivial haApp
          have hinnerEqB := hinnerEq.app_same wf trivial hinnerT hbT
          have hclosedInnerT :=
            (hinnerEq.of_l wf trivial hinnerT).hasType.2
          have hbApp := hbEq.app_arg wf trivial hclosedInnerT hbT
          exact ⟨r₂, hr₂',
            (hinnerEqB.trans wf trivial hbApp).symm.trans wf trivial heq₂⟩

end Lean4Lean.Environment
