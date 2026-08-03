import Lean4Lean.Verify.BitwiseCondition

namespace Lean4Lean.Environment
open Lean VEnv

private theorem reflectionNatDITE_true_lhs_shape
    {env : VEnv} {r : Reflection} {l : VExpr}
    (h : TrExprS env [] []
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(true)) <|
       mkApp5 r.natDITE (.bvar 3) q(true) (.bvar 0)
         (.bvar 2) (.bvar 1)) l) :
    ∃ rtype rdite, l =
      (.lam (.sort .zero) <|
       .lam (.forallE (.bvar 0) .nat) <|
       .lam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat) <|
       .lam (.app (.app rtype (.bvar 2)) .boolTrue) <|
       .app (.app (.app (.app (.app rdite (.bvar 3)) .boolTrue)
         (.bvar 0)) (.bvar 2)) (.bvar 1)) ∧
      TrExprS env []
        [(none, .vlam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat)),
          (none, .vlam (.forallE (.bvar 0) .nat)),
          (none, .vlam (.sort .zero))]
        r.type rtype ∧
      TrExprS env []
        [(none, .vlam (.app (.app rtype (.bvar 2)) .boolTrue)),
          (none, .vlam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat)),
          (none, .vlam (.forallE (.bvar 0) .nat)),
          (none, .vlam (.sort .zero))]
        r.natDITE rdite := by
  cases h with
  | lam _ hpropS hbody =>
    cases hpropS with
    | sort hlevel =>
      simp [VLevel.ofLevel] at hlevel
      subst hlevel
      cases hbody with
      | lam _ htTyS hbody =>
        cases htTyS with
        | forallE _ _ hpTyS hnatTyS =>
          cases hpTyS with
          | bvar hpTy =>
            simp [VLCtx.find?, VLCtx.next] at hpTy
            rcases hpTy with ⟨rfl, rfl⟩
            cases hnatTyS with
            | const _ hus _ =>
              simp at hus
              subst hus
              cases hbody with
              | lam _ heTyS hbody =>
                cases heTyS with
                | forallE _ _ hnotpS hnatTyS =>
                  cases hnotpS with
                  | app _ _ hnotS hpS =>
                    cases hnotS with
                    | const _ hus _ =>
                      simp at hus
                      subst hus
                      cases hpS with
                      | bvar hp =>
                        simp [VLCtx.find?, VLCtx.next] at hp
                        rcases hp with ⟨rfl, rfl⟩
                        cases hnatTyS with
                        | const _ hus _ =>
                          simp at hus
                          subst hus
                          cases hbody with
                          | lam _ hHTyS hbody =>
                            cases hHTyS with
                            | app _ _ hHFnS htrueS =>
                              cases hHFnS with
                              | app _ _ hrtypeS hpS =>
                                cases hpS with
                                | bvar hp =>
                                  simp [VLCtx.find?, VLCtx.next] at hp
                                  rcases hp with ⟨rfl, rfl⟩
                                  cases htrueS with
                                  | const _ hus _ =>
                                    simp at hus
                                    subst hus
                                    cases hbody with
                                    | app _ _ hfn heS =>
                                      cases hfn with
                                      | app _ _ hfn htS =>
                                        cases hfn with
                                        | app _ _ hfn hHS =>
                                          cases hfn with
                                          | app _ _ hfn htrueS =>
                                            cases hfn with
                                            | app _ _ hditeS hpS =>
                                              cases heS with
                                              | bvar heS =>
                                                cases htS with
                                                | bvar htS =>
                                                  cases hHS with
                                                  | bvar hHS =>
                                                    cases htrueS with
                                                    | const _ hus _ =>
                                                      simp at hus
                                                      subst hus
                                                      cases hpS with
                                              | bvar hpS =>
                                                        simp [VLCtx.find?, VLCtx.next] at heS htS hHS hpS
                                                        rcases heS with ⟨rfl, rfl⟩
                                                        rcases htS with ⟨rfl, rfl⟩
                                                        rcases hHS with ⟨rfl, rfl⟩
                                                        rcases hpS with ⟨rfl, rfl⟩
                                                        exact ⟨_, _, rfl, hrtypeS, hditeS⟩

private theorem reflectionNatDITE_true_rhs_shape
    {env : VEnv} {r : Reflection} {rr : VExpr}
    (h : TrExprS env [] []
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(true)) <|
       mkApp (.bvar 2) (mkApp2 r.ofTrue (.bvar 3) (.bvar 0))) rr) :
    ∃ rtype ofTrue, rr =
      (.lam (.sort .zero) <|
       .lam (.forallE (.bvar 0) .nat) <|
       .lam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat) <|
       .lam (.app (.app rtype (.bvar 2)) .boolTrue) <|
       .app (.bvar 2) (.app (.app ofTrue (.bvar 3)) (.bvar 0))) ∧
      TrExprS env []
        [(none, .vlam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat)),
          (none, .vlam (.forallE (.bvar 0) .nat)),
          (none, .vlam (.sort .zero))]
        r.type rtype ∧
      TrExprS env []
        [(none, .vlam (.app (.app rtype (.bvar 2)) .boolTrue)),
          (none, .vlam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat)),
          (none, .vlam (.forallE (.bvar 0) .nat)),
          (none, .vlam (.sort .zero))]
        r.ofTrue ofTrue := by
  cases h with
  | lam _ hpropS hbody =>
    cases hpropS with
    | sort hlevel =>
      simp [VLevel.ofLevel] at hlevel
      subst hlevel
      cases hbody with
      | lam _ htTyS hbody =>
        cases htTyS with
        | forallE _ _ hpTyS hnatTyS =>
          cases hpTyS with
          | bvar hpTy =>
            simp [VLCtx.find?, VLCtx.next] at hpTy
            rcases hpTy with ⟨rfl, rfl⟩
            cases hnatTyS with
            | const _ hus _ =>
              simp at hus
              subst hus
              cases hbody with
              | lam _ heTyS hbody =>
                cases heTyS with
                | forallE _ _ hnotpS hnatTyS =>
                  cases hnotpS with
                  | app _ _ hnotS hpS =>
                    cases hnotS with
                    | const _ hus _ =>
                      simp at hus
                      subst hus
                      cases hpS with
                      | bvar hp =>
                        simp [VLCtx.find?, VLCtx.next] at hp
                        rcases hp with ⟨rfl, rfl⟩
                        cases hnatTyS with
                        | const _ hus _ =>
                          simp at hus
                          subst hus
                          cases hbody with
                          | lam _ hHTyS hbody =>
                            cases hHTyS with
                            | app _ _ hHFnS htrueS =>
                              cases hHFnS with
                              | app _ _ hrtypeS hpS =>
                                cases hpS with
                                | bvar hp =>
                                  simp [VLCtx.find?, VLCtx.next] at hp
                                  rcases hp with ⟨rfl, rfl⟩
                                  cases htrueS with
                                  | const _ hus _ =>
                                    simp at hus
                                    subst hus
                                    cases hbody with
                                    | app _ _ htS hproofS =>
                                      cases htS with
                                      | bvar htS =>
                                        cases hproofS with
                                        | app _ _ hfn hHS =>
                                          cases hfn with
                                          | app _ _ hofTrueS hpS =>
                                            cases hpS with
                                            | bvar hpS =>
                                              cases hHS with
                                              | bvar hHS =>
                                                simp [VLCtx.find?, VLCtx.next] at htS hpS hHS
                                                rcases htS with ⟨rfl, rfl⟩
                                                rcases hpS with ⟨rfl, rfl⟩
                                                rcases hHS with ⟨rfl, rfl⟩
                                                exact ⟨_, _, rfl, hrtypeS, hofTrueS⟩

private theorem reflectionNatDITE_false_lhs_shape
    {env : VEnv} {r : Reflection} {l : VExpr}
    (h : TrExprS env [] []
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(false)) <|
       mkApp5 r.natDITE (.bvar 3) q(false) (.bvar 0)
         (.bvar 2) (.bvar 1)) l) :
    ∃ rtype rdite, l =
      (.lam (.sort .zero) <|
       .lam (.forallE (.bvar 0) .nat) <|
       .lam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat) <|
       .lam (.app (.app rtype (.bvar 2)) .boolFalse) <|
       .app (.app (.app (.app (.app rdite (.bvar 3)) .boolFalse)
         (.bvar 0)) (.bvar 2)) (.bvar 1)) ∧
      TrExprS env []
        [(none, .vlam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat)),
          (none, .vlam (.forallE (.bvar 0) .nat)),
          (none, .vlam (.sort .zero))]
        r.type rtype ∧
      TrExprS env []
        [(none, .vlam (.app (.app rtype (.bvar 2)) .boolFalse)),
          (none, .vlam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat)),
          (none, .vlam (.forallE (.bvar 0) .nat)),
          (none, .vlam (.sort .zero))]
        r.natDITE rdite := by
  cases h with
  | lam _ hpropS hbody =>
    cases hpropS with
    | sort hlevel =>
      simp [VLevel.ofLevel] at hlevel
      subst hlevel
      cases hbody with
      | lam _ htTyS hbody =>
        cases htTyS with
        | forallE _ _ hpTyS hnatTyS =>
          cases hpTyS with
          | bvar hpTy =>
            simp [VLCtx.find?, VLCtx.next] at hpTy
            rcases hpTy with ⟨rfl, rfl⟩
            cases hnatTyS with
            | const _ hus _ =>
              simp at hus
              subst hus
              cases hbody with
              | lam _ heTyS hbody =>
                cases heTyS with
                | forallE _ _ hnotpS hnatTyS =>
                  cases hnotpS with
                  | app _ _ hnotS hpS =>
                    cases hnotS with
                    | const _ hus _ =>
                      simp at hus
                      subst hus
                      cases hpS with
                      | bvar hp =>
                        simp [VLCtx.find?, VLCtx.next] at hp
                        rcases hp with ⟨rfl, rfl⟩
                        cases hnatTyS with
                        | const _ hus _ =>
                          simp at hus
                          subst hus
                          cases hbody with
                          | lam _ hHTyS hbody =>
                            cases hHTyS with
                            | app _ _ hHFnS hfalseS =>
                              cases hHFnS with
                              | app _ _ hrtypeS hpS =>
                                cases hpS with
                                | bvar hp =>
                                  simp [VLCtx.find?, VLCtx.next] at hp
                                  rcases hp with ⟨rfl, rfl⟩
                                  cases hfalseS with
                                  | const _ hus _ =>
                                    simp at hus
                                    subst hus
                                    cases hbody with
                                    | app _ _ hfn heS =>
                                      cases hfn with
                                      | app _ _ hfn htS =>
                                        cases hfn with
                                        | app _ _ hfn hHS =>
                                          cases hfn with
                                          | app _ _ hfn hfalseS =>
                                            cases hfn with
                                            | app _ _ hditeS hpS =>
                                              cases heS with
                                              | bvar heS =>
                                                cases htS with
                                                | bvar htS =>
                                                  cases hHS with
                                                  | bvar hHS =>
                                                    cases hfalseS with
                                                    | const _ hus _ =>
                                                      simp at hus
                                                      subst hus
                                                      cases hpS with
                                                      | bvar hpS =>
                                                        simp [VLCtx.find?, VLCtx.next] at heS htS hHS hpS
                                                        rcases heS with ⟨rfl, rfl⟩
                                                        rcases htS with ⟨rfl, rfl⟩
                                                        rcases hHS with ⟨rfl, rfl⟩
                                                        rcases hpS with ⟨rfl, rfl⟩
                                                        exact ⟨_, _, rfl, hrtypeS, hditeS⟩

private theorem reflectionNatDITE_false_rhs_shape
    {env : VEnv} {r : Reflection} {rr : VExpr}
    (h : TrExprS env [] []
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(false)) <|
       mkApp (.bvar 1) (mkApp2 r.ofFalse (.bvar 3) (.bvar 0))) rr) :
    ∃ rtype ofFalse, rr =
      (.lam (.sort .zero) <|
       .lam (.forallE (.bvar 0) .nat) <|
       .lam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat) <|
       .lam (.app (.app rtype (.bvar 2)) .boolFalse) <|
       .app (.bvar 1) (.app (.app ofFalse (.bvar 3)) (.bvar 0))) ∧
      TrExprS env []
        [(none, .vlam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat)),
          (none, .vlam (.forallE (.bvar 0) .nat)),
          (none, .vlam (.sort .zero))]
        r.type rtype ∧
      TrExprS env []
        [(none, .vlam (.app (.app rtype (.bvar 2)) .boolFalse)),
          (none, .vlam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat)),
          (none, .vlam (.forallE (.bvar 0) .nat)),
          (none, .vlam (.sort .zero))]
        r.ofFalse ofFalse := by
  cases h with
  | lam _ hpropS hbody =>
    cases hpropS with
    | sort hlevel =>
      simp [VLevel.ofLevel] at hlevel
      subst hlevel
      cases hbody with
      | lam _ htTyS hbody =>
        cases htTyS with
        | forallE _ _ hpTyS hnatTyS =>
          cases hpTyS with
          | bvar hpTy =>
            simp [VLCtx.find?, VLCtx.next] at hpTy
            rcases hpTy with ⟨rfl, rfl⟩
            cases hnatTyS with
            | const _ hus _ =>
              simp at hus
              subst hus
              cases hbody with
              | lam _ heTyS hbody =>
                cases heTyS with
                | forallE _ _ hnotpS hnatTyS =>
                  cases hnotpS with
                  | app _ _ hnotS hpS =>
                    cases hnotS with
                    | const _ hus _ =>
                      simp at hus
                      subst hus
                      cases hpS with
                      | bvar hp =>
                        simp [VLCtx.find?, VLCtx.next] at hp
                        rcases hp with ⟨rfl, rfl⟩
                        cases hnatTyS with
                        | const _ hus _ =>
                          simp at hus
                          subst hus
                          cases hbody with
                          | lam _ hHTyS hbody =>
                            cases hHTyS with
                            | app _ _ hHFnS hfalseS =>
                              cases hHFnS with
                              | app _ _ hrtypeS hpS =>
                                cases hpS with
                                | bvar hp =>
                                  simp [VLCtx.find?, VLCtx.next] at hp
                                  rcases hp with ⟨rfl, rfl⟩
                                  cases hfalseS with
                                  | const _ hus _ =>
                                    simp at hus
                                    subst hus
                                    cases hbody with
                                    | app _ _ heS hproofS =>
                                      cases heS with
                                      | bvar heS =>
                                        cases hproofS with
                                        | app _ _ hfn hHS =>
                                          cases hfn with
                                          | app _ _ hofFalseS hpS =>
                                            cases hpS with
                                            | bvar hpS =>
                                              cases hHS with
                                              | bvar hHS =>
                                                simp [VLCtx.find?, VLCtx.next] at heS hpS hHS
                                                rcases heS with ⟨rfl, rfl⟩
                                                rcases hpS with ⟨rfl, rfl⟩
                                                rcases hHS with ⟨rfl, rfl⟩
                                                exact ⟨_, _, rfl, hrtypeS, hofFalseS⟩

/-- Rewrite both equations retained by `Reflection.checkNatDITE` to chosen
global translations of the four reflection operations. -/
theorem VEnv.ReflectionNatDITEChecked.canonical
    {env : VEnv} (wf : env.WF)
    (hchecked : VEnv.ReflectionNatDITEChecked env r)
    (hrtypeUnique : TrExprS.IsUnique r.type)
    (hditeUnique : TrExprS.IsUnique r.natDITE)
    (hofTrueUnique : TrExprS.IsUnique r.ofTrue)
    (hofFalseUnique : TrExprS.IsUnique r.ofFalse)
    {rtype rdite ofTrue ofFalse : VExpr}
    (hrtype : TrExprS env [] [] r.type rtype)
    (hdite : TrExprS env [] [] r.natDITE rdite)
    (hofTrue : TrExprS env [] [] r.ofTrue ofTrue)
    (hofFalse : TrExprS env [] [] r.ofFalse ofFalse) :
    env.IsDefEqU 0 []
      (.lam (.sort .zero) <|
       .lam (.forallE (.bvar 0) .nat) <|
       .lam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat) <|
       .lam (.app (.app rtype (.bvar 2)) .boolTrue) <|
       .app (.app (.app (.app (.app rdite (.bvar 3)) .boolTrue)
         (.bvar 0)) (.bvar 2)) (.bvar 1))
      (.lam (.sort .zero) <|
       .lam (.forallE (.bvar 0) .nat) <|
       .lam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat) <|
       .lam (.app (.app rtype (.bvar 2)) .boolTrue) <|
       .app (.bvar 2) (.app (.app ofTrue (.bvar 3)) (.bvar 0))) ∧
    env.IsDefEqU 0 []
      (.lam (.sort .zero) <|
       .lam (.forallE (.bvar 0) .nat) <|
       .lam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat) <|
       .lam (.app (.app rtype (.bvar 2)) .boolFalse) <|
       .app (.app (.app (.app (.app rdite (.bvar 3)) .boolFalse)
         (.bvar 0)) (.bvar 2)) (.bvar 1))
      (.lam (.sort .zero) <|
       .lam (.forallE (.bvar 0) .nat) <|
       .lam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat) <|
       .lam (.app (.app rtype (.bvar 2)) .boolFalse) <|
       .app (.bvar 1) (.app (.app ofFalse (.bvar 3)) (.bvar 0))) := by
  rcases hchecked with
    ⟨trueL, trueR, falseL, falseR,
      htrueLS, htrueRS, htrueEq, hfalseLS, hfalseRS, hfalseEq⟩
  obtain ⟨trueRTypeL, trueDITE, rfl, htrueRTypeLS, htrueDITES⟩ :=
    reflectionNatDITE_true_lhs_shape htrueLS
  obtain ⟨trueRTypeR, trueOfTrue, rfl, htrueRTypeRS, htrueOfTrueS⟩ :=
    reflectionNatDITE_true_rhs_shape htrueRS
  obtain ⟨falseRTypeL, falseDITE, rfl, hfalseRTypeLS, hfalseDITES⟩ :=
    reflectionNatDITE_false_lhs_shape hfalseLS
  obtain ⟨falseRTypeR, falseOfFalse, rfl, hfalseRTypeRS, hfalseOfFalseS⟩ :=
    reflectionNatDITE_false_rhs_shape hfalseRS
  have hrtypeClosed : r.type.looseBVarRange' = 0 :=
    hrtype.closed.looseBVarRange_zero
  have hditeClosed : r.natDITE.looseBVarRange' = 0 :=
    hdite.closed.looseBVarRange_zero
  have hofTrueClosed : r.ofTrue.looseBVarRange' = 0 :=
    hofTrue.closed.looseBVarRange_zero
  have hofFalseClosed : r.ofFalse.looseBVarRange' = 0 :=
    hofFalse.closed.looseBVarRange_zero
  have hctx₃ : VLCtx.BVLift []
      [(none, .vlam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat)),
        (none, .vlam (.forallE (.bvar 0) .nat)),
        (none, .vlam (.sort .zero))] 3 0 3 0 :=
    .skip _ (.skip _ (.skip _ .refl))
  have htrueRTypeL : trueRTypeL = rtype :=
    TrExprS.unique_closed_weak wf hrtypeUnique hrtypeClosed hrtype
      htrueRTypeLS hctx₃
  have htrueRTypeR : trueRTypeR = rtype :=
    TrExprS.unique_closed_weak wf hrtypeUnique hrtypeClosed hrtype
      htrueRTypeRS hctx₃
  have hfalseRTypeL : falseRTypeL = rtype :=
    TrExprS.unique_closed_weak wf hrtypeUnique hrtypeClosed hrtype
      hfalseRTypeLS hctx₃
  have hfalseRTypeR : falseRTypeR = rtype :=
    TrExprS.unique_closed_weak wf hrtypeUnique hrtypeClosed hrtype
      hfalseRTypeRS hctx₃
  subst trueRTypeL
  subst trueRTypeR
  subst falseRTypeL
  subst falseRTypeR
  have htrueDITE : trueDITE = rdite :=
    TrExprS.unique_closed_weak wf hditeUnique hditeClosed hdite
      htrueDITES (.skip _ hctx₃)
  have htrueOfTrue : trueOfTrue = ofTrue :=
    TrExprS.unique_closed_weak wf hofTrueUnique hofTrueClosed hofTrue
      htrueOfTrueS (.skip _ hctx₃)
  have hfalseDITE : falseDITE = rdite :=
    TrExprS.unique_closed_weak wf hditeUnique hditeClosed hdite
      hfalseDITES (.skip _ hctx₃)
  have hfalseOfFalse : falseOfFalse = ofFalse :=
    TrExprS.unique_closed_weak wf hofFalseUnique hofFalseClosed hofFalse
      hfalseOfFalseS (.skip _ hctx₃)
  subst trueDITE
  subst trueOfTrue
  subst falseDITE
  subst falseOfFalse
  exact ⟨htrueEq, hfalseEq⟩

/-- A translated concrete `Nat.ble` call computes to the Boolean selected by
the primitive reflection invariant. -/
theorem Condition.natBLE_application_eval
    {env : VEnv} (wf : env.WF) (hprim : env.HasPrimitives)
    (hctors : VEnv.HasNatBoolConstructors env)
    (hbleC : env.contains ``Nat.ble)
    {a b : Nat} {bleV : VExpr}
    (hbleS : TrExprS env [] []
      (mkApp2 q(Nat.ble) (.lit (.natVal a)) (.lit (.natVal b))) bleV) :
    env.IsDefEqU 0 [] bleV (.boolLit (Nat.ble a b)) := by
  have ⟨haS, haT⟩ := hctors.natLitS a (Us := []) (Δ := [])
  have ⟨hbS, hbT⟩ := hctors.natLitS b (Us := []) (Δ := [])
  have ⟨hbleT, hbleEval⟩ := hprim.natBLE hbleC
  obtain ⟨ci, hci, _, hlen⟩ := (hbleT 0 []).const_inv wf trivial
  have hfnS : TrExprS env [] [] q(Nat.ble) (.const ``Nat.ble []) :=
    .const hci rfl hlen
  have hinnerS : TrExprS env [] []
      (mkApp q(Nat.ble) (.lit (.natVal a)))
      (.app (.const ``Nat.ble []) (.natLit a)) :=
    .app (hbleT 0 []) haT hfnS haS
  have hcanonS : TrExprS env [] []
      (mkApp2 q(Nat.ble) (.lit (.natVal a)) (.lit (.natVal b)))
      (.app (.app (.const ``Nat.ble []) (.natLit a)) (.natLit b)) :=
    .app (.app (hbleT 0 []) haT) hbT hinnerS hbS
  have hlocalEq := TrExprS.uniq (Us := []) wf
    (.refl wf (U := 0) (Δ := []) trivial) hbleS hcanonS
  exact hlocalEq.trans wf trivial (hbleEval a b)

/-- Replace the Boolean argument of a fully applied reflected dependent
selector.  Typing of the proof and both branches is transported through the
dependent function equality. -/
theorem VEnv.replaceNatDITECondition
    {env : VEnv} (wf : env.WF)
    {diteV propV boolV boolV' proofV thenV elseV R : VExpr}
    (houtT : env.HasType 0 []
      (.app (.app (.app (.app (.app diteV propV) boolV) proofV)
        thenV) elseV) R)
    (hbool : env.IsDefEqU 0 [] boolV boolV') :
    env.IsDefEqU 0 []
      (.app (.app (.app (.app (.app diteV propV) boolV) proofV)
        thenV) elseV)
      (.app (.app (.app (.app (.app diteV propV) boolV') proofV)
        thenV) elseV) := by
  obtain ⟨_, _, hthenAppT, helseT⟩ := houtT.app_inv wf.ordered trivial
  obtain ⟨_, _, hproofAppT, hthenT⟩ :=
    hthenAppT.app_inv wf.ordered trivial
  obtain ⟨_, _, hboolAppT, hproofT⟩ :=
    hproofAppT.app_inv wf.ordered trivial
  obtain ⟨_, _, hpropAppT, hboolT⟩ :=
    hboolAppT.app_inv wf.ordered trivial
  have h₁ := hbool.app_arg wf trivial hpropAppT hboolT
  have h₂ := h₁.app_same wf trivial hboolAppT hproofT
  have h₃ := h₂.app_same wf trivial hproofAppT hthenT
  exact h₃.app_same wf trivial hthenAppT helseT

/-- A checked dependent true-selector equation specializes to its true
branch, retaining the generated proof argument existentially. -/
theorem VEnv.reflectionNatDITE_true_select
    {env : VEnv} (wf : env.WF)
    {rtypeL rtypeR rdite ofTrue p t e H : VExpr}
    (hrtypeLClosed : rtypeL.ClosedN) (hrtypeRClosed : rtypeR.ClosedN)
    (hrditeClosed : rdite.ClosedN) (hofTrueClosed : ofTrue.ClosedN)
    (heq : env.IsDefEqU 0 []
      (.lam (.sort .zero) <|
       .lam (.forallE (.bvar 0) .nat) <|
       .lam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat) <|
       .lam (.app (.app rtypeL (.bvar 2)) .boolTrue) <|
       .app (.app (.app (.app (.app rdite (.bvar 3)) .boolTrue)
         (.bvar 0)) (.bvar 2)) (.bvar 1))
      (.lam (.sort .zero) <|
       .lam (.forallE (.bvar 0) .nat) <|
       .lam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat) <|
       .lam (.app (.app rtypeR (.bvar 2)) .boolTrue) <|
       .app (.bvar 2) (.app (.app ofTrue (.bvar 3)) (.bvar 0))))
    (hp : env.HasType 0 [] p (.sort .zero))
    (ht : env.HasType 0 [] t (.forallE p .nat))
    (he : env.HasType 0 [] e
      (.forallE (.app (.const ``Not []) p) .nat))
    (hHL : env.HasType 0 [] H (.app (.app rtypeL p) .boolTrue))
    (hHR : env.HasType 0 [] H (.app (.app rtypeR p) .boolTrue)) :
    ∃ proof,
      env.IsDefEqU 0 []
        (.app (.app (.app (.app (.app rdite p) .boolTrue) H) t) e)
        (.app t proof) := by
  have hpClosed : p.ClosedN := (hp.closedN' wf.ordered.closed trivial).1
  have htClosed : t.ClosedN := (ht.closedN' wf.ordered.closed trivial).1
  have heClosed : e.ClosedN := (he.closedN' wf.ordered.closed trivial).1
  have heq' := heq
  obtain ⟨_, hd⟩ := heq'
  obtain ⟨⟨_, hpropSort⟩, _, hleftBodyT⟩ :=
    hd.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightBodyT⟩ := hd.hasType.2.lam_inv wf trivial
  have h₁ := VEnv.IsDefEqU.lam_instU wf trivial heq hpropSort
    hleftBodyT hrightBodyT hp
  simp [VExpr.inst, hrtypeLClosed.instN_eq, hrtypeRClosed.instN_eq,
    hrditeClosed.instN_eq, hofTrueClosed.instN_eq, hpClosed.lift_eq] at h₁
  have h₁' := h₁
  obtain ⟨_, hd₁⟩ := h₁'
  obtain ⟨⟨_, htSort⟩, _, hleftTBody⟩ :=
    hd₁.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightTBody⟩ := hd₁.hasType.2.lam_inv wf trivial
  have h₂ := VEnv.IsDefEqU.lam_instU wf trivial h₁ htSort
    hleftTBody hrightTBody ht
  simp [VExpr.inst, hrtypeLClosed.instN_eq, hrtypeRClosed.instN_eq,
    hrditeClosed.instN_eq, hofTrueClosed.instN_eq, hpClosed.instN_eq] at h₂
  have h₂' := h₂
  obtain ⟨_, hd₂⟩ := h₂'
  obtain ⟨⟨_, heSort⟩, _, hleftEBody⟩ :=
    hd₂.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightEBody⟩ := hd₂.hasType.2.lam_inv wf trivial
  have h₃ := VEnv.IsDefEqU.lam_instU wf trivial h₂ heSort
    hleftEBody hrightEBody he
  simp [VExpr.inst, hrtypeLClosed.instN_eq, hrtypeRClosed.instN_eq,
    hrditeClosed.instN_eq, hofTrueClosed.instN_eq, hpClosed.instN_eq] at h₃
  have h₃' := h₃
  obtain ⟨_, hd₃⟩ := h₃'
  obtain ⟨⟨_, hHSort⟩, _, hleftHBody⟩ :=
    hd₃.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightHBody⟩ := hd₃.hasType.2.lam_inv wf trivial
  have h₄ := VEnv.IsDefEqU.lam_instU_hetero wf trivial h₃ hHSort
    hleftHBody hrightHBody hHL hHR
  simp [VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.liftN, liftVar,
    hrditeClosed.instN_eq, hofTrueClosed.instN_eq,
    hpClosed.instN_eq, htClosed.liftN_eq,
    htClosed.instN_eq, heClosed.lift_eq,
    heClosed.instN_eq] at h₄
  exact ⟨.app (.app ofTrue p) H, h₄⟩

/-- False counterpart of `reflectionNatDITE_true_select`. -/
theorem VEnv.reflectionNatDITE_false_select
    {env : VEnv} (wf : env.WF)
    {rtypeL rtypeR rdite ofFalse p t e H : VExpr}
    (hrtypeLClosed : rtypeL.ClosedN) (hrtypeRClosed : rtypeR.ClosedN)
    (hrditeClosed : rdite.ClosedN) (hofFalseClosed : ofFalse.ClosedN)
    (heq : env.IsDefEqU 0 []
      (.lam (.sort .zero) <|
       .lam (.forallE (.bvar 0) .nat) <|
       .lam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat) <|
       .lam (.app (.app rtypeL (.bvar 2)) .boolFalse) <|
       .app (.app (.app (.app (.app rdite (.bvar 3)) .boolFalse)
         (.bvar 0)) (.bvar 2)) (.bvar 1))
      (.lam (.sort .zero) <|
       .lam (.forallE (.bvar 0) .nat) <|
       .lam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat) <|
       .lam (.app (.app rtypeR (.bvar 2)) .boolFalse) <|
       .app (.bvar 1) (.app (.app ofFalse (.bvar 3)) (.bvar 0))))
    (hp : env.HasType 0 [] p (.sort .zero))
    (ht : env.HasType 0 [] t (.forallE p .nat))
    (he : env.HasType 0 [] e
      (.forallE (.app (.const ``Not []) p) .nat))
    (hHL : env.HasType 0 [] H (.app (.app rtypeL p) .boolFalse))
    (hHR : env.HasType 0 [] H (.app (.app rtypeR p) .boolFalse)) :
    ∃ proof,
      env.IsDefEqU 0 []
        (.app (.app (.app (.app (.app rdite p) .boolFalse) H) t) e)
        (.app e proof) := by
  have hpClosed : p.ClosedN := (hp.closedN' wf.ordered.closed trivial).1
  have htClosed : t.ClosedN := (ht.closedN' wf.ordered.closed trivial).1
  have heClosed : e.ClosedN := (he.closedN' wf.ordered.closed trivial).1
  have heq' := heq
  obtain ⟨_, hd⟩ := heq'
  obtain ⟨⟨_, hpropSort⟩, _, hleftBodyT⟩ :=
    hd.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightBodyT⟩ := hd.hasType.2.lam_inv wf trivial
  have h₁ := VEnv.IsDefEqU.lam_instU wf trivial heq hpropSort
    hleftBodyT hrightBodyT hp
  simp [VExpr.inst, hrtypeLClosed.instN_eq, hrtypeRClosed.instN_eq,
    hrditeClosed.instN_eq, hofFalseClosed.instN_eq, hpClosed.lift_eq] at h₁
  have h₁' := h₁
  obtain ⟨_, hd₁⟩ := h₁'
  obtain ⟨⟨_, htSort⟩, _, hleftTBody⟩ :=
    hd₁.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightTBody⟩ := hd₁.hasType.2.lam_inv wf trivial
  have h₂ := VEnv.IsDefEqU.lam_instU wf trivial h₁ htSort
    hleftTBody hrightTBody ht
  simp [VExpr.inst, hrtypeLClosed.instN_eq, hrtypeRClosed.instN_eq,
    hrditeClosed.instN_eq, hofFalseClosed.instN_eq, hpClosed.instN_eq] at h₂
  have h₂' := h₂
  obtain ⟨_, hd₂⟩ := h₂'
  obtain ⟨⟨_, heSort⟩, _, hleftEBody⟩ :=
    hd₂.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightEBody⟩ := hd₂.hasType.2.lam_inv wf trivial
  have h₃ := VEnv.IsDefEqU.lam_instU wf trivial h₂ heSort
    hleftEBody hrightEBody he
  simp [VExpr.inst, hrtypeLClosed.instN_eq, hrtypeRClosed.instN_eq,
    hrditeClosed.instN_eq, hofFalseClosed.instN_eq, hpClosed.instN_eq] at h₃
  have h₃' := h₃
  obtain ⟨_, hd₃⟩ := h₃'
  obtain ⟨⟨_, hHSort⟩, _, hleftHBody⟩ :=
    hd₃.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightHBody⟩ := hd₃.hasType.2.lam_inv wf trivial
  have h₄ := VEnv.IsDefEqU.lam_instU_hetero wf trivial h₃ hHSort
    hleftHBody hrightHBody hHL hHR
  simp [VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.liftN, liftVar,
    hrditeClosed.instN_eq, hofFalseClosed.instN_eq,
    hpClosed.instN_eq, htClosed.liftN_eq,
    htClosed.instN_eq, heClosed.lift_eq, heClosed.instN_eq] at h₄
  exact ⟨.app (.app ofFalse p) H, h₄⟩

end Lean4Lean.Environment
