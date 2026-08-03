import Lean4Lean.Verify.BitwiseCondition

namespace Lean4Lean.Environment
open Lean VEnv

private theorem reflectionITE_type_shape
    {env : VEnv} {r : Reflection} {ty : VExpr}
    (h : TrExprS env [] []
      (.arrow q(Prop) <| .arrow q(Bool) <|
       .arrow (mkApp2 r.type (.bvar 1) (.bvar 0))
         q(∀ α : Type, α → α → α)) ty) :
    ∃ rtype, ty =
      (.forallE (.sort .zero) <|
       .forallE .bool <|
       .forallE (.app (.app rtype (.bvar 1)) (.bvar 0)) <|
       .forallE (.sort (.succ .zero)) <|
       .forallE (.bvar 0) <| .forallE (.bvar 1) (.bvar 2)) ∧
      TrExprS env []
        [(none, .vlam .bool), (none, .vlam (.sort .zero))]
        r.type rtype := by
  cases h with
  | forallE _ _ hpropS hrest =>
    cases hpropS with
    | sort hlevel =>
      simp [VLevel.ofLevel] at hlevel
      subst hlevel
      cases hrest with
      | forallE _ _ hboolS hrest =>
        cases hboolS with
        | const _ hus _ =>
          simp at hus
          subst hus
          cases hrest with
          | forallE _ _ hproofTyS hrest =>
            cases hproofTyS with
            | app _ _ hfn hbS =>
              cases hfn with
              | app _ _ hrtypeS hpS =>
                cases hpS with
                | bvar hp =>
                  simp [VLCtx.find?, VLCtx.next] at hp
                  rcases hp with ⟨rfl, rfl⟩
                  cases hbS with
                  | bvar hb =>
                    simp [VLCtx.find?, VLCtx.next] at hb
                    rcases hb with ⟨rfl, rfl⟩
                    cases hrest with
                    | forallE _ _ halphaS hrest =>
                      cases halphaS with
                      | sort hlevel =>
                        simp [VLevel.ofLevel] at hlevel
                        subst hlevel
                        cases hrest with
                        | forallE _ _ htS hrest =>
                          cases htS with
                          | bvar ht =>
                            simp [VLCtx.find?, VLCtx.next] at ht
                            rcases ht with ⟨rfl, rfl⟩
                            cases hrest with
                            | forallE _ _ heS hresultS =>
                              cases heS with
                              | bvar he =>
                                simp [VLCtx.find?, VLCtx.next] at he
                                rcases he with ⟨rfl, rfl⟩
                                cases hresultS with
                                | bvar hresult =>
                                  simp [VLCtx.find?, VLCtx.next] at hresult
                                  rcases hresult with ⟨rfl, rfl⟩
                                  exact ⟨_, rfl, hrtypeS⟩

/-- Normalize the checked type of a translated nondependent reflection
selector. -/
theorem VEnv.reflectionITE_hasType_canonical
    {env : VEnv} (wf : env.WF) {r : Reflection}
    (hrtypeUnique : TrExprS.IsUnique r.type)
    {rtype rite iteTy : VExpr}
    (hrtype : TrExprS env [] [] r.type rtype)
    (hiteTy : TrExprS env [] []
      (.arrow q(Prop) <| .arrow q(Bool) <|
       .arrow (mkApp2 r.type (.bvar 1) (.bvar 0))
         q(∀ α : Type, α → α → α)) iteTy)
    (hiteHas : env.HasType 0 [] rite iteTy) :
    env.HasType 0 [] rite
      (.forallE (.sort .zero) <|
       .forallE .bool <|
       .forallE (.app (.app rtype (.bvar 1)) (.bvar 0)) <|
       .forallE (.sort (.succ .zero)) <|
       .forallE (.bvar 0) <| .forallE (.bvar 1) (.bvar 2)) := by
  obtain ⟨rtypeLocal, rfl, hrtypeLocal⟩ := reflectionITE_type_shape hiteTy
  have hrtypeClosed : r.type.looseBVarRange' = 0 :=
    hrtype.closed.looseBVarRange_zero
  have hrtypeLocalEq : rtypeLocal = rtype :=
    TrExprS.unique_closed_weak wf hrtypeUnique hrtypeClosed hrtype
      hrtypeLocal (.skip (.vlam .bool)
        (.skip (.vlam (.sort .zero)) .refl))
  subst rtypeLocal
  exact hiteHas

/-- Exact argument types forced by the normalized type of a fully applied
nondependent reflection selector. -/
theorem VEnv.reflectionITE_call_types
    {env : VEnv} (wf : env.WF)
    {rtype rite p boolV H α t e R : VExpr}
    (hrtypeClosed : rtype.ClosedN)
    (hrite : env.HasType 0 [] rite
      (.forallE (.sort .zero) <|
       .forallE .bool <|
       .forallE (.app (.app rtype (.bvar 1)) (.bvar 0)) <|
       .forallE (.sort (.succ .zero)) <|
       .forallE (.bvar 0) <| .forallE (.bvar 1) (.bvar 2)))
    (hcall : env.HasType 0 []
      (.app (.app (.app (.app (.app (.app rite p) boolV) H) α) t) e) R) :
    env.HasType 0 [] p (.sort .zero) ∧
    env.HasType 0 [] H (.app (.app rtype p) boolV) ∧
    env.HasType 0 [] α (.sort (.succ .zero)) ∧
    env.HasType 0 [] t α ∧ env.HasType 0 [] e α := by
  obtain ⟨_, _, htAppT, heRaw⟩ := hcall.app_inv wf.ordered trivial
  obtain ⟨_, _, hαAppT, htRaw⟩ := htAppT.app_inv wf.ordered trivial
  obtain ⟨_, _, hproofAppT, hαRaw⟩ := hαAppT.app_inv wf.ordered trivial
  obtain ⟨_, _, hboolAppT, hHRaw⟩ :=
    hproofAppT.app_inv wf.ordered trivial
  obtain ⟨_, _, hpropAppT, hboolRaw⟩ :=
    hboolAppT.app_inv wf.ordered trivial
  obtain ⟨_, _, hriteRaw, hpRaw⟩ := hpropAppT.app_inv wf.ordered trivial
  have hriteTyEq := hriteRaw.uniqU wf trivial hrite
  obtain ⟨_, hpTyEq⟩ := (hriteTyEq.forallE_inv wf trivial).1
  have hp := hpRaw.defeqU_r wf trivial hpTyEq.toU
  have hpClosed : p.ClosedN :=
    (hp.closedN' wf.ordered.closed trivial).1
  have hpropCanonT : env.HasType 0 [] (.app rite p)
      (.forallE .bool <|
       .forallE (.app (.app rtype p) (.bvar 0)) <|
       .forallE (.sort (.succ .zero)) <|
       .forallE (.bvar 0) <| .forallE (.bvar 1) (.bvar 2)) := by
    simpa [VExpr.inst, VExpr.bool, hrtypeClosed.instN_eq,
      hpClosed.lift_eq, hpClosed.instN_eq] using
      (VEnv.HasType.app hrite hp)
  have hpropTyEq := hpropAppT.uniqU wf trivial hpropCanonT
  obtain ⟨_, hboolTyEq⟩ := (hpropTyEq.forallE_inv wf trivial).1
  have hbool := hboolRaw.defeqU_r wf trivial hboolTyEq.toU
  have hboolClosed : boolV.ClosedN :=
    (hbool.closedN' wf.ordered.closed trivial).1
  have hboolCanonT : env.HasType 0 []
      (.app (.app rite p) boolV)
      (.forallE (.app (.app rtype p) boolV) <|
       .forallE (.sort (.succ .zero)) <|
       .forallE (.bvar 0) <| .forallE (.bvar 1) (.bvar 2)) := by
    simpa [VExpr.inst, hrtypeClosed.instN_eq,
      hpClosed.lift_eq, hpClosed.instN_eq,
      hboolClosed.lift_eq, hboolClosed.instN_eq] using
      (VEnv.HasType.app hpropCanonT hbool)
  have hboolPrefixTyEq := hboolAppT.uniqU wf trivial hboolCanonT
  obtain ⟨_, hHTyEq⟩ :=
    (hboolPrefixTyEq.forallE_inv wf trivial).1
  have hH := hHRaw.defeqU_r wf trivial hHTyEq.toU
  have hHClosed : H.ClosedN :=
    (hH.closedN' wf.ordered.closed trivial).1
  have hproofCanonT : env.HasType 0 []
      (.app (.app (.app rite p) boolV) H)
      (.forallE (.sort (.succ .zero)) <|
       .forallE (.bvar 0) <| .forallE (.bvar 1) (.bvar 2)) := by
    simpa [VExpr.inst, hHClosed.lift_eq, hHClosed.instN_eq] using
      (VEnv.HasType.app hboolCanonT hH)
  have hproofTyEq := hproofAppT.uniqU wf trivial hproofCanonT
  obtain ⟨_, hαTyEq⟩ := (hproofTyEq.forallE_inv wf trivial).1
  have hα := hαRaw.defeqU_r wf trivial hαTyEq.toU
  have hαClosed : α.ClosedN :=
    (hα.closedN' wf.ordered.closed trivial).1
  have hαCanonT : env.HasType 0 []
      (.app (.app (.app (.app rite p) boolV) H) α)
      (.forallE α <| .forallE α α) := by
    simpa [VExpr.inst, hαClosed.lift_eq, hαClosed.instN_eq] using
      (VEnv.HasType.app hproofCanonT hα)
  have hαPrefixTyEq := hαAppT.uniqU wf trivial hαCanonT
  obtain ⟨_, htTyEq⟩ := (hαPrefixTyEq.forallE_inv wf trivial).1
  have ht := htRaw.defeqU_r wf trivial htTyEq.toU
  have htClosed : t.ClosedN :=
    (ht.closedN' wf.ordered.closed trivial).1
  have htCanonT : env.HasType 0 []
      (.app (.app (.app (.app (.app rite p) boolV) H) α) t)
      (.forallE α α) := by
    simpa [VExpr.inst, hαClosed.lift_eq, hαClosed.instN_eq,
      htClosed.lift_eq, htClosed.instN_eq] using
      (VEnv.HasType.app hαCanonT ht)
  have htTyEq := htAppT.uniqU wf trivial htCanonT
  obtain ⟨_, heTyEq⟩ := (htTyEq.forallE_inv wf trivial).1
  exact ⟨hp, hH, hα, ht, heRaw.defeqU_r wf trivial heTyEq.toU⟩

private theorem reflectionNatDITE_type_shape
    {env : VEnv} {r : Reflection} {ty : VExpr}
    (h : TrExprS env [] []
      (.arrow q(Prop) <| .arrow q(Bool) <|
       .arrow (mkApp2 r.type (.bvar 1) (.bvar 0)) <|
       .arrow (.arrow (.bvar 2) q(Nat)) <|
       .arrow (.arrow (mkApp q(Not) (.bvar 3)) q(Nat)) q(Nat)) ty) :
    ∃ rtype, ty =
      (.forallE (.sort .zero) <|
       .forallE .bool <|
       .forallE (.app (.app rtype (.bvar 1)) (.bvar 0)) <|
       .forallE (.forallE (.bvar 2) .nat) <|
       .forallE (.forallE
         (.app (.const ``Not []) (.bvar 3)) .nat) .nat) ∧
      TrExprS env []
        [(none, .vlam .bool), (none, .vlam (.sort .zero))]
        r.type rtype := by
  cases h with
  | forallE _ _ hpropS hrest =>
    cases hpropS with
    | sort hlevel =>
      simp [VLevel.ofLevel] at hlevel
      subst hlevel
      cases hrest with
      | forallE _ _ hboolS hrest =>
        cases hboolS with
        | const _ hus _ =>
          simp at hus
          subst hus
          cases hrest with
          | forallE _ _ hproofTyS hrest =>
            cases hproofTyS with
            | app _ _ hfn hbS =>
              cases hfn with
              | app _ _ hrtypeS hpS =>
                cases hpS with
                | bvar hp =>
                  simp [VLCtx.find?, VLCtx.next] at hp
                  rcases hp with ⟨rfl, rfl⟩
                  cases hbS with
                  | bvar hb =>
                    simp [VLCtx.find?, VLCtx.next] at hb
                    rcases hb with ⟨rfl, rfl⟩
                    cases hrest with
                    | forallE _ _ htS hrest =>
                      cases htS with
                      | forallE _ _ hpS hnatS =>
                        cases hpS with
                        | bvar hp =>
                          simp [VLCtx.find?, VLCtx.next] at hp
                          rcases hp with ⟨rfl, rfl⟩
                          cases hnatS with
                          | const _ hus _ =>
                            simp at hus
                            subst hus
                            cases hrest with
                            | forallE _ _ heS hnatS =>
                              cases heS with
                              | forallE _ _ hnotpS hnatS₁ =>
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
                                      cases hnatS₁ with
                                      | const _ hus _ =>
                                        simp at hus
                                        subst hus
                                        cases hnatS with
                                        | const _ hus _ =>
                                          simp at hus
                                          subst hus
                                          exact ⟨_, rfl, hrtypeS⟩

/-- Normalize the checked type of a translated dependent selector to a
chosen global translation of `Reflection.type`. -/
theorem VEnv.reflectionNatDITE_hasType_canonical
    {env : VEnv} (wf : env.WF) {r : Reflection}
    (hrtypeUnique : TrExprS.IsUnique r.type)
    {rtype rdite diteTy : VExpr}
    (hrtype : TrExprS env [] [] r.type rtype)
    (hditeTy : TrExprS env [] []
      (.arrow q(Prop) <| .arrow q(Bool) <|
       .arrow (mkApp2 r.type (.bvar 1) (.bvar 0)) <|
       .arrow (.arrow (.bvar 2) q(Nat)) <|
       .arrow (.arrow (mkApp q(Not) (.bvar 3)) q(Nat)) q(Nat)) diteTy)
    (hditeHas : env.HasType 0 [] rdite diteTy) :
    env.HasType 0 [] rdite
      (.forallE (.sort .zero) <|
       .forallE .bool <|
       .forallE (.app (.app rtype (.bvar 1)) (.bvar 0)) <|
       .forallE (.forallE (.bvar 2) .nat) <|
       .forallE (.forallE
         (.app (.const ``Not []) (.bvar 3)) .nat) .nat) := by
  obtain ⟨rtypeLocal, rfl, hrtypeLocal⟩ :=
    reflectionNatDITE_type_shape hditeTy
  have hrtypeClosed : r.type.looseBVarRange' = 0 :=
    hrtype.closed.looseBVarRange_zero
  have hrtypeLocalEq : rtypeLocal = rtype :=
    TrExprS.unique_closed_weak wf hrtypeUnique hrtypeClosed hrtype
      hrtypeLocal (.skip (.vlam .bool)
        (.skip (.vlam (.sort .zero)) .refl))
  subst rtypeLocal
  exact hditeHas

/-- Exact argument types forced by the normalized type of a fully applied
reflected dependent selector. -/
theorem VEnv.reflectionNatDITE_call_types
    {env : VEnv} (wf : env.WF)
    {rtype rdite p boolV H t e R : VExpr}
    (hrtypeClosed : rtype.ClosedN)
    (hrdite : env.HasType 0 [] rdite
      (.forallE (.sort .zero) <|
       .forallE .bool <|
       .forallE (.app (.app rtype (.bvar 1)) (.bvar 0)) <|
       .forallE (.forallE (.bvar 2) .nat) <|
       .forallE (.forallE
         (.app (.const ``Not []) (.bvar 3)) .nat) .nat))
    (hcall : env.HasType 0 []
      (.app (.app (.app (.app (.app rdite p) boolV) H) t) e) R) :
    env.HasType 0 [] p (.sort .zero) ∧
    env.HasType 0 [] t (.forallE p .nat) ∧
    env.HasType 0 [] e
      (.forallE (.app (.const ``Not []) p) .nat) := by
  obtain ⟨_, _, hthenAppT, heRaw⟩ := hcall.app_inv wf.ordered trivial
  obtain ⟨_, _, hproofAppT, htRaw⟩ :=
    hthenAppT.app_inv wf.ordered trivial
  obtain ⟨_, _, hboolAppT, hHRaw⟩ :=
    hproofAppT.app_inv wf.ordered trivial
  obtain ⟨_, _, hpropAppT, hboolRaw⟩ :=
    hboolAppT.app_inv wf.ordered trivial
  obtain ⟨pTy, _, hrditeRaw, hpRaw⟩ :=
    hpropAppT.app_inv wf.ordered trivial
  have hrditeTyEq := hrditeRaw.uniqU wf trivial hrdite
  obtain ⟨_, hpTyEq⟩ := (hrditeTyEq.forallE_inv wf trivial).1
  have hp := hpRaw.defeqU_r wf trivial hpTyEq.toU
  have hpClosed : p.ClosedN :=
    (hp.closedN' wf.ordered.closed trivial).1
  have hpropCanonT : env.HasType 0 [] (.app rdite p)
      (.forallE .bool <|
       .forallE (.app (.app rtype p) (.bvar 0)) <|
       .forallE (.forallE p .nat) <|
       .forallE (.forallE
         (.app (.const ``Not []) p) .nat) .nat) := by
    simpa [VExpr.inst, VExpr.bool, VExpr.nat,
      hrtypeClosed.instN_eq, hpClosed.lift_eq, hpClosed.instN_eq] using
      (VEnv.HasType.app hrdite hp)
  have hpropTyEq := hpropAppT.uniqU wf trivial hpropCanonT
  obtain ⟨_, hboolTyEq⟩ := (hpropTyEq.forallE_inv wf trivial).1
  have hbool := hboolRaw.defeqU_r wf trivial hboolTyEq.toU
  have hboolClosed : boolV.ClosedN :=
    (hbool.closedN' wf.ordered.closed trivial).1
  have hboolCanonT : env.HasType 0 []
      (.app (.app rdite p) boolV)
      (.forallE (.app (.app rtype p) boolV) <|
       .forallE (.forallE p .nat) <|
       .forallE (.forallE
         (.app (.const ``Not []) p) .nat) .nat) := by
    simpa [VExpr.inst, VExpr.nat, hrtypeClosed.instN_eq,
      hpClosed.lift_eq, hpClosed.instN_eq,
      hboolClosed.lift_eq, hboolClosed.instN_eq] using
      (VEnv.HasType.app hpropCanonT hbool)
  have hboolPrefixTyEq := hboolAppT.uniqU wf trivial hboolCanonT
  obtain ⟨_, hHTyEq⟩ :=
    (hboolPrefixTyEq.forallE_inv wf trivial).1
  have hH := hHRaw.defeqU_r wf trivial hHTyEq.toU
  have hHClosed : H.ClosedN :=
    (hH.closedN' wf.ordered.closed trivial).1
  have hproofCanonT : env.HasType 0 []
      (.app (.app (.app rdite p) boolV) H)
      (.forallE (.forallE p .nat) <|
       .forallE (.forallE
         (.app (.const ``Not []) p) .nat) .nat) := by
    simpa [VExpr.inst, hpClosed.lift_eq, hpClosed.instN_eq,
      hboolClosed.lift_eq, hboolClosed.instN_eq,
      hHClosed.lift_eq, hHClosed.instN_eq] using
      (VEnv.HasType.app hboolCanonT hH)
  have hproofPrefixTyEq := hproofAppT.uniqU wf trivial hproofCanonT
  obtain ⟨_, htTyEq⟩ :=
    (hproofPrefixTyEq.forallE_inv wf trivial).1
  have ht := htRaw.defeqU_r wf trivial htTyEq.toU
  have htClosed : t.ClosedN :=
    (ht.closedN' wf.ordered.closed trivial).1
  have hthenCanonT : env.HasType 0 []
      (.app (.app (.app (.app rdite p) boolV) H) t)
      (.forallE (.forallE (.app (.const ``Not []) p) .nat) .nat) := by
    simpa [VExpr.inst, hpClosed.lift_eq, hpClosed.instN_eq,
      htClosed.lift_eq, htClosed.instN_eq] using
      (VEnv.HasType.app hproofCanonT ht)
  have hthenTyEq := hthenAppT.uniqU wf trivial hthenCanonT
  obtain ⟨_, heTyEq⟩ := (hthenTyEq.forallE_inv wf trivial).1
  exact ⟨hp, ht, heRaw.defeqU_r wf trivial heTyEq.toU⟩

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

/-- Canonical target operations and checker evidence exported by a successful
`Condition.natLE` check. -/
structure VEnv.NatLESelectorCertificate (env : VEnv) where
  rtype : VExpr
  rite : VExpr
  rdite : VExpr
  ofTrue : VExpr
  ofFalse : VExpr
  rtypeS : TrExprS env [] [] Reflection.defn₁.type rtype
  riteS : TrExprS env [] [] Reflection.defn₁.ite rite
  rditeS : TrExprS env [] [] Reflection.defn₁.natDITE rdite
  ofTrueS : TrExprS env [] [] Reflection.defn₁.ofTrue ofTrue
  ofFalseS : TrExprS env [] [] Reflection.defn₁.ofFalse ofFalse
  rtypeUnique : TrExprS.IsUnique Reflection.defn₁.type
  riteUnique : TrExprS.IsUnique Reflection.defn₁.ite
  rditeUnique : TrExprS.IsUnique Reflection.defn₁.natDITE
  ofTrueUnique : TrExprS.IsUnique Reflection.defn₁.ofTrue
  ofFalseUnique : TrExprS.IsUnique Reflection.defn₁.ofFalse
  riteHas : env.HasType 0 [] rite
    (.forallE (.sort .zero) <|
     .forallE .bool <|
     .forallE (.app (.app rtype (.bvar 1)) (.bvar 0)) <|
     .forallE (.sort (.succ .zero)) <|
     .forallE (.bvar 0) <| .forallE (.bvar 1) (.bvar 2))
  rditeHas : env.HasType 0 [] rdite
    (.forallE (.sort .zero) <|
     .forallE .bool <|
     .forallE (.app (.app rtype (.bvar 1)) (.bvar 0)) <|
     .forallE (.forallE (.bvar 2) .nat) <|
     .forallE (.forallE
       (.app (.const ``Not []) (.bvar 3)) .nat) .nat)
  iteChecked : VEnv.ReflectionITECertificate env Reflection.defn₁
  diteChecked : VEnv.ReflectionNatDITEChecked env Reflection.defn₁

theorem VEnv.ReflectionITECertificate.mono
    {env env' : VEnv} (hle : env ≤ env')
    (h : VEnv.ReflectionITECertificate env r) :
    VEnv.ReflectionITECertificate env' r := by
  rcases h with ⟨hrtypeUnique, hiteUnique,
    trueRTypeL, trueITE, trueRTypeR,
    htrueEq, htrueRTypeLS, htrueITES, htrueRTypeRS,
    falseRTypeL, falseITE, falseRTypeR,
    hfalseEq, hfalseRTypeLS, hfalseITES, hfalseRTypeRS⟩
  exact ⟨hrtypeUnique, hiteUnique,
    trueRTypeL, trueITE, trueRTypeR,
    htrueEq.mono hle, htrueRTypeLS.mono hle,
    htrueITES.mono hle, htrueRTypeRS.mono hle,
    falseRTypeL, falseITE, falseRTypeR,
    hfalseEq.mono hle, hfalseRTypeLS.mono hle,
    hfalseITES.mono hle, hfalseRTypeRS.mono hle⟩

def VEnv.NatLESelectorCertificate.mono
    {env env' : VEnv} (cert : VEnv.NatLESelectorCertificate env)
    (hle : env ≤ env') : VEnv.NatLESelectorCertificate env' := {
  rtype := cert.rtype
  rite := cert.rite
  rdite := cert.rdite
  ofTrue := cert.ofTrue
  ofFalse := cert.ofFalse
  rtypeS := cert.rtypeS.mono hle
  riteS := cert.riteS.mono hle
  rditeS := cert.rditeS.mono hle
  ofTrueS := cert.ofTrueS.mono hle
  ofFalseS := cert.ofFalseS.mono hle
  rtypeUnique := cert.rtypeUnique
  riteUnique := cert.riteUnique
  rditeUnique := cert.rditeUnique
  ofTrueUnique := cert.ofTrueUnique
  ofFalseUnique := cert.ofFalseUnique
  riteHas := cert.riteHas.mono hle
  rditeHas := cert.rditeHas.mono hle
  iteChecked := cert.iteChecked.mono hle
  diteChecked := cert.diteChecked.mono hle
}

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

/-- Assemble the semantic selector certificate from the raw evidence retained
by `Condition.natLE.check.WF`. -/
def VEnv.NatLESelectorCertificate.of_checked
    {env : VEnv} (wf : env.WF)
    {rtype rite rdite ofTrue ofFalse iteTy diteTy : VExpr}
    (hrtype : TrExprS env [] [] Reflection.defn₁.type rtype)
    (hrite : TrExprS env [] [] Reflection.defn₁.ite rite)
    (hrdite : TrExprS env [] [] Reflection.defn₁.natDITE rdite)
    (hofTrue : TrExprS env [] [] Reflection.defn₁.ofTrue ofTrue)
    (hofFalse : TrExprS env [] [] Reflection.defn₁.ofFalse ofFalse)
    (hrtypeUnique : TrExprS.IsUnique Reflection.defn₁.type)
    (hiteUnique : TrExprS.IsUnique Reflection.defn₁.ite)
    (hditeUnique : TrExprS.IsUnique Reflection.defn₁.natDITE)
    (hofTrueUnique : TrExprS.IsUnique Reflection.defn₁.ofTrue)
    (hofFalseUnique : TrExprS.IsUnique Reflection.defn₁.ofFalse)
    (hiteTy : TrExprS env [] []
      (.arrow q(Prop) <| .arrow q(Bool) <|
       .arrow (mkApp2 Reflection.defn₁.type (.bvar 1) (.bvar 0))
         q(∀ α : Type, α → α → α)) iteTy)
    (hditeTy : TrExprS env [] []
      (.arrow q(Prop) <| .arrow q(Bool) <|
       .arrow (mkApp2 Reflection.defn₁.type (.bvar 1) (.bvar 0)) <|
       .arrow (.arrow (.bvar 2) q(Nat)) <|
       .arrow (.arrow (mkApp q(Not) (.bvar 3)) q(Nat)) q(Nat)) diteTy)
    (hiteHas : env.HasType 0 [] rite iteTy)
    (hditeHas : env.HasType 0 [] rdite diteTy)
    (hiteChecked : VEnv.ReflectionITEChecked env Reflection.defn₁)
    (hditeChecked : VEnv.ReflectionNatDITEChecked env Reflection.defn₁) :
    VEnv.NatLESelectorCertificate env := by
  have hiteCert := hiteChecked.toCertificate
    hrtypeUnique hiteUnique
  exact {
    rtype := rtype
    rite := rite
    rdite := rdite
    ofTrue := ofTrue
    ofFalse := ofFalse
    rtypeS := hrtype
    riteS := hrite
    rditeS := hrdite
    ofTrueS := hofTrue
    ofFalseS := hofFalse
    rtypeUnique := hrtypeUnique
    riteUnique := hiteUnique
    rditeUnique := hditeUnique
    ofTrueUnique := hofTrueUnique
    ofFalseUnique := hofFalseUnique
    riteHas := VEnv.reflectionITE_hasType_canonical wf
      hrtypeUnique hrtype hiteTy hiteHas
    rditeHas := VEnv.reflectionNatDITE_hasType_canonical wf
      hrtypeUnique hrtype hditeTy hditeHas
    iteChecked := hiteCert
    diteChecked := hditeChecked }

/-- Package the raw evidence produced by `Condition.natLE.check.WF` into the
semantic selector certificate shared by the `Nat.mod` and `Nat.div`
conservation proofs. -/
theorem Condition.natLE.check.WF.selector
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {fail : ∀ {α}, TypeChecker.M α}
    {rtype rite rdite ofTrue ofFalse iteTy diteTy reflectFn dec : VExpr}
    (hlparams : c.lparams = []) (hvlctx : c.vlctx = [])
    (hrtype : c.TrExprS Reflection.defn₁.type rtype)
    (hrite : c.TrExprS Reflection.defn₁.ite rite)
    (hrdite : c.TrExprS Reflection.defn₁.natDITE rdite)
    (hofTrue : c.TrExprS Reflection.defn₁.ofTrue ofTrue)
    (hofFalse : c.TrExprS Reflection.defn₁.ofFalse ofFalse)
    (hrtypeUnique : TrExprS.IsUnique Reflection.defn₁.type)
    (hiteUnique : TrExprS.IsUnique Reflection.defn₁.ite)
    (hditeUnique : TrExprS.IsUnique Reflection.defn₁.natDITE)
    (hofTrueUnique : TrExprS.IsUnique Reflection.defn₁.ofTrue)
    (hofFalseUnique : TrExprS.IsUnique Reflection.defn₁.ofFalse)
    (hiteTy : c.TrExprS
      (.arrow q(Prop) <| .arrow q(Bool) <|
       .arrow (mkApp2 Reflection.defn₁.type (.bvar 1) (.bvar 0))
         q(∀ α : Type, α → α → α)) iteTy)
    (hditeTy : c.TrExprS
      (.arrow q(Prop) <| .arrow q(Bool) <|
       .arrow (mkApp2 Reflection.defn₁.type (.bvar 1) (.bvar 0)) <|
       .arrow (.arrow (.bvar 2) q(Nat)) <|
       .arrow (.arrow (mkApp q(Not) (.bvar 3)) q(Nat)) q(Nat)) diteTy)
    (hcheck : TypeChecker.M.WF c s
      (Condition.natLE.check fail (ite := true) (dite := true)) fun _ _ =>
        c.HasType rtype rtypeCanon ∧
        (c.HasType rite iteTy ∧
          VEnv.ReflectionITEChecked c.venv Reflection.defn₁) ∧
        (c.HasType rdite diteTy ∧
          c.HasType ofTrue ofTrueTy ∧
          c.HasType ofFalse ofFalseTy ∧
          VEnv.ReflectionNatDITEChecked c.venv Reflection.defn₁) ∧
        c.IsDefEqU reflectFn dec) :
    TypeChecker.M.WF c s
      (Condition.natLE.check fail (ite := true) (dite := true)) fun _ _ =>
        ∃ _selector : VEnv.NatLESelectorCertificate c.venv,
          c.IsDefEqU reflectFn dec := by
  refine hcheck.mono fun _ _ _
    ⟨_, ⟨hiteHas, hiteChecked⟩,
      ⟨hditeHas, hofTrueHas, hofFalseHas, hditeChecked⟩, heq⟩ => ?_
  change TrExprS c.venv c.lparams c.vlctx _ _ at hrtype hrite hrdite hofTrue hofFalse hiteTy hditeTy
  change c.venv.HasType c.lparams.length c.vlctx.toCtx _ _ at hiteHas hditeHas hofTrueHas hofFalseHas
  rw [hlparams, hvlctx] at hrtype hrite hrdite hofTrue hofFalse hiteTy hditeTy hiteHas hditeHas hofTrueHas hofFalseHas
  exact ⟨VEnv.NatLESelectorCertificate.of_checked c.Ewf
    hrtype hrite hrdite hofTrue hofFalse
    hrtypeUnique hiteUnique hditeUnique hofTrueUnique hofFalseUnique
    hiteTy hditeTy hiteHas hditeHas hiteChecked hditeChecked, heq⟩

private theorem TrExprS.target_closed
    {env : VEnv} (wf : env.WF) {e : Expr} {eV : VExpr}
    (h : TrExprS env [] [] e eV) : eV.ClosedN := by
  obtain ⟨_, heWF⟩ := h.wf wf.ordered (Us := []) (Δ := []) trivial
  exact (heWF.hasType.1.closedN' wf.ordered.closed trivial).1

def VEnv.NatLESelectorCertificate.ite_equations
    {env : VEnv} (cert : VEnv.NatLESelectorCertificate env)
    (wf : env.WF) :=
  cert.iteChecked.canonical wf cert.rtypeS cert.riteS

def VEnv.NatLESelectorCertificate.dite_equations
    {env : VEnv} (cert : VEnv.NatLESelectorCertificate env)
    (wf : env.WF) :=
  cert.diteChecked.canonical wf
    cert.rtypeUnique cert.rditeUnique
    cert.ofTrueUnique cert.ofFalseUnique
    cert.rtypeS cert.rditeS cert.ofTrueS cert.ofFalseS

/-- A translated concrete `Nat.ble` call computes to the Boolean selected by
the primitive reflection invariant. -/
theorem Condition.natBLE_application_eval
    {env : VEnv} (wf : env.WF)
    (hbleR : env.ReflectsNatNatBool ``Nat.ble Nat.ble)
    (hctors : VEnv.HasNatBoolConstructors env)
    (hbleC : env.contains ``Nat.ble)
    {a b : Nat} {bleV : VExpr}
    (hbleS : TrExprS env [] []
      (mkApp2 q(Nat.ble) (.lit (.natVal a)) (.lit (.natVal b))) bleV) :
    env.IsDefEqU 0 [] bleV (.boolLit (Nat.ble a b)) := by
  have ⟨haS, haT⟩ := hctors.natLitS a (Us := []) (Δ := [])
  have ⟨hbS, hbT⟩ := hctors.natLitS b (Us := []) (Δ := [])
  have ⟨hbleT, hbleEval⟩ := hbleR hbleC
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

/-- Constructor-syntax counterpart of `natBLE_application_eval`, matching
the expressions produced by instantiating checked lambda equations. -/
theorem Condition.natBLE_constructor_application_eval
    {env : VEnv} (wf : env.WF)
    (hbleR : env.ReflectsNatNatBool ``Nat.ble Nat.ble)
    (hctors : VEnv.HasNatBoolConstructors env)
    (hbleC : env.contains ``Nat.ble)
    {a b : Nat} {bleV : VExpr}
    (hbleS : TrExprS env [] []
      (mkApp2 q(Nat.ble) (.natLitToConstructor a)
        (.natLitToConstructor b)) bleV) :
    env.IsDefEqU 0 [] bleV (.boolLit (Nat.ble a b)) := by
  have haLit := hctors.natLitS a (Us := []) (Δ := [])
  have hbLit := hctors.natLitS b (Us := []) (Δ := [])
  cases haLit.1 with
  | lit _ haS =>
    cases hbLit.1 with
    | lit _ hbS =>
      have ⟨hbleT, hbleEval⟩ := hbleR hbleC
      obtain ⟨ci, hci, _, hlen⟩ := (hbleT 0 []).const_inv wf trivial
      have hfnS : TrExprS env [] [] q(Nat.ble) (.const ``Nat.ble []) :=
        .const hci rfl hlen
      have hinnerS : TrExprS env [] []
          (mkApp q(Nat.ble) (.natLitToConstructor a))
          (.app (.const ``Nat.ble []) (.natLit a)) :=
        .app (hbleT 0 []) haLit.2 hfnS haS
      have hcanonS : TrExprS env [] []
          (mkApp2 q(Nat.ble) (.natLitToConstructor a)
            (.natLitToConstructor b))
          (.app (.app (.const ``Nat.ble []) (.natLit a)) (.natLit b)) :=
        .app (.app (hbleT 0 []) haLit.2) hbLit.2 hinnerS hbS
      have hlocalEq := TrExprS.uniq (Us := []) wf
        (.refl wf (U := 0) (Δ := []) trivial) hbleS hcanonS
      exact hlocalEq.trans wf trivial (hbleEval a b)

/-- Evaluate a translated `Nat.ble` call from arbitrary source presentations
of two concrete naturals. -/
theorem Condition.natBLE_application_eval_of_args
    {env : VEnv} (wf : env.WF)
    (hbleR : env.ReflectsNatNatBool ``Nat.ble Nat.ble)
    (hctors : VEnv.HasNatBoolConstructors env)
    (hbleC : env.contains ``Nat.ble)
    {a b : Nat} {aS bS : Expr} {bleV : VExpr}
    (haS : TrExprS env [] [] aS (.natLit a))
    (hbS : TrExprS env [] [] bS (.natLit b))
    (hbleS : TrExprS env [] [] (mkApp2 q(Nat.ble) aS bS) bleV) :
    env.IsDefEqU 0 [] bleV (.boolLit (Nat.ble a b)) := by
  have ⟨hbleT, hbleEval⟩ := hbleR hbleC
  obtain ⟨ci, hci, _, hlen⟩ := (hbleT 0 []).const_inv wf trivial
  have hfnS : TrExprS env [] [] q(Nat.ble) (.const ``Nat.ble []) :=
    .const hci rfl hlen
  have haT := (hctors.natLitS a (Us := []) (Δ := [])).2
  have hbT := (hctors.natLitS b (Us := []) (Δ := [])).2
  have hinnerS : TrExprS env [] [] (mkApp q(Nat.ble) aS)
      (.app (.const ``Nat.ble []) (.natLit a)) :=
    .app (hbleT 0 []) haT hfnS haS
  have hcanonS : TrExprS env [] [] (mkApp2 q(Nat.ble) aS bS)
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

/-- Replace the Boolean argument of a fully applied nondependent reflection
selector. -/
theorem VEnv.replaceReflectionITECondition
    {env : VEnv} (wf : env.WF)
    {iteV propV boolV boolV' proofV α thenV elseV R : VExpr}
    (houtT : env.HasType 0 []
      (.app (.app (.app (.app (.app (.app iteV propV) boolV) proofV)
        α) thenV) elseV) R)
    (hbool : env.IsDefEqU 0 [] boolV boolV') :
    env.IsDefEqU 0 []
      (.app (.app (.app (.app (.app (.app iteV propV) boolV) proofV)
        α) thenV) elseV)
      (.app (.app (.app (.app (.app (.app iteV propV) boolV') proofV)
        α) thenV) elseV) := by
  obtain ⟨_, _, htAppT, heT⟩ := houtT.app_inv wf.ordered trivial
  obtain ⟨_, _, hαAppT, htT⟩ := htAppT.app_inv wf.ordered trivial
  obtain ⟨_, _, hproofAppT, hαT⟩ := hαAppT.app_inv wf.ordered trivial
  obtain ⟨_, _, hboolAppT, hproofT⟩ :=
    hproofAppT.app_inv wf.ordered trivial
  obtain ⟨_, _, hpropAppT, hboolT⟩ :=
    hboolAppT.app_inv wf.ordered trivial
  have h₁ := hbool.app_arg wf trivial hpropAppT hboolT
  have h₂ := h₁.app_same wf trivial hboolAppT hproofT
  have h₃ := h₂.app_same wf trivial hproofAppT hαT
  have h₄ := h₃.app_same wf trivial hαAppT htT
  exact h₄.app_same wf trivial htAppT heT

/-- Recover the exact type of a dependent proof argument from a certified
lambda equation and a closed call using that proof, then instantiate the
equation with the recovered argument. -/
private theorem VEnv.instantiate_dependent_proof_lam
    {env : VEnv} (wf : env.WF)
    {proofTyL proofTyR bodyL bodyR prefixLocal prefixCall hpV
      prefixArgTy prefixBodyTy hpTy hpBodyTy : VExpr}
    (hprefixLocalT : env.HasType 0 [proofTyL] prefixLocal
      (.forallE prefixArgTy prefixBodyTy))
    (hproofVarT : env.HasType 0 [proofTyL] (.bvar 0) prefixArgTy)
    (hprefixCallT : env.HasType 0 [] prefixCall
      (.forallE hpTy hpBodyTy))
    (hpT : env.HasType 0 [] hpV hpTy)
    (hprefixEq : env.IsDefEqU 0 [proofTyL] prefixLocal prefixCall)
    (hlamEq : env.IsDefEqU 0 []
      (.lam proofTyL bodyL) (.lam proofTyR bodyR)) :
    env.HasType 0 [] hpV proofTyR ∧
      env.IsDefEqU 0 [] (bodyL.inst hpV) (bodyR.inst hpV) := by
  have hlamEqU := hlamEq
  obtain ⟨_, hlamEqD⟩ := hlamEq
  obtain ⟨hproofTyLType, _, hbodyLEq⟩ :=
    hlamEqD.hasType.1.lam_inv wf trivial
  obtain ⟨hproofTyRType, _, hbodyREq⟩ :=
    hlamEqD.hasType.2.lam_inv wf trivial
  have hΓ : OnCtx [proofTyL] (env.IsType 0) :=
    ⟨trivial, hproofTyLType⟩
  obtain ⟨_, hproofTyLSort⟩ := hproofTyLType
  have hproofTyLClosed :=
    (hproofTyLSort.closedN' wf.ordered.closed trivial).1
  have hproofVarCanon : env.HasType 0 [proofTyL] (.bvar 0) proofTyL := by
    have hb : env.HasType 0 [proofTyL] (.bvar 0) proofTyL.lift :=
      .bvar .zero
    rw [hproofTyLClosed.lift_eq] at hb
    exact hb
  have hproofArgEq := hproofVarT.uniqU wf hΓ hproofVarCanon
  have hprefixCallLocalT :=
    (hprefixEq.of_l wf hΓ hprefixLocalT).hasType.2
  have hprefixCallWeakT := hprefixCallT.weak0 (Γ := [proofTyL]) wf
  have hforallEq := hprefixCallLocalT.uniqU wf hΓ hprefixCallWeakT
  obtain ⟨_, hdomainEq⟩ := (hforallEq.forallE_inv wf hΓ).1
  have hpProofTyEqCtx := hdomainEq.symm.toU.trans wf hΓ hproofArgEq
  have hpTyClosed := (hpT.closedN' wf.ordered.closed trivial).2.2
  have hpProofTyEq : env.IsDefEqU 0 [] hpTy proofTyL := by
    apply (VEnv.IsDefEqU.weakN_iff wf hΓ
      (Ctx.LiftN.one : Ctx.LiftN 1 0 [] [proofTyL])).1
    simpa [hpTyClosed.lift_eq, hproofTyLClosed.lift_eq] using
      hpProofTyEqCtx
  have hpTL := hpT.defeqU_r wf trivial hpProofTyEq
  have hleftLamT := VEnv.HasType.lam hproofTyLSort hbodyLEq.hasType.1
  have happ := hlamEqU.app_same wf trivial hleftLamT hpTL
  have happRightT :=
    (happ.of_l wf trivial (VEnv.HasType.app hleftLamT hpTL)).hasType.2
  obtain ⟨_, _, hrightLamT, hpTR⟩ :=
    happRightT.app_inv wf.ordered trivial
  obtain ⟨_, hproofTyRSort⟩ := hproofTyRType
  have hrightLamCanonT :=
    VEnv.HasType.lam hproofTyRSort hbodyREq.hasType.1
  have hrightForallEq := hrightLamT.uniqU wf trivial hrightLamCanonT
  obtain ⟨_, hrightDomainEq⟩ :=
    (hrightForallEq.forallE_inv wf trivial).1
  have hpTR' := hpTR.defeqU_r wf trivial hrightDomainEq.toU
  exact ⟨hpTR', VEnv.IsDefEqU.lam_instU_hetero wf trivial hlamEqU
    hproofTyLSort hbodyLEq.hasType.1 hbodyREq.hasType.1 hpTL hpTR'⟩

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

/-- The true selector equation itself recovers the exact dependent type of
an already well-typed reflection witness; callers need not provide that
transport separately. -/
private theorem VEnv.reflectionNatDITE_true_select_from_call
    {env : VEnv} (wf : env.WF)
    {rtype rdite ofTrue p H t e R : VExpr}
    (hrtypeClosed : rtype.ClosedN) (hrditeClosed : rdite.ClosedN)
    (hofTrueClosed : ofTrue.ClosedN)
    (heq : env.IsDefEqU 0 []
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
       .app (.bvar 2) (.app (.app ofTrue (.bvar 3)) (.bvar 0))))
    (hcallT : env.HasType 0 []
      (.app (.app (.app (.app (.app rdite p) .boolTrue) H) t) e) R)
    (hp : env.HasType 0 [] p (.sort .zero))
    (ht : env.HasType 0 [] t (.forallE p .nat))
    (he : env.HasType 0 [] e
      (.forallE (.app (.const ``Not []) p) .nat)) :
    ∃ proof, env.IsDefEqU 0 []
      (.app (.app (.app (.app (.app rdite p) .boolTrue) H) t) e)
      (.app t proof) := by
  have hpClosed : p.ClosedN :=
    (hp.closedN' wf.ordered.closed trivial).1
  have htClosed : t.ClosedN :=
    (ht.closedN' wf.ordered.closed trivial).1
  have heClosed : e.ClosedN :=
    (he.closedN' wf.ordered.closed trivial).1
  have heq' := heq
  obtain ⟨_, hd⟩ := heq'
  obtain ⟨⟨_, hpropSort⟩, _, hleftBodyT⟩ :=
    hd.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightBodyT⟩ := hd.hasType.2.lam_inv wf trivial
  have h₁ := VEnv.IsDefEqU.lam_instU wf trivial heq hpropSort
    hleftBodyT hrightBodyT hp
  simp [VExpr.inst, hrtypeClosed.instN_eq,
    hrditeClosed.instN_eq, hofTrueClosed.instN_eq, hpClosed.lift_eq] at h₁
  have h₁' := h₁
  obtain ⟨_, hd₁⟩ := h₁'
  obtain ⟨⟨_, htSort⟩, _, hleftTBody⟩ :=
    hd₁.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightTBody⟩ := hd₁.hasType.2.lam_inv wf trivial
  have h₂ := VEnv.IsDefEqU.lam_instU wf trivial h₁ htSort
    hleftTBody hrightTBody ht
  simp [VExpr.inst, hrtypeClosed.instN_eq,
    hrditeClosed.instN_eq, hofTrueClosed.instN_eq, hpClosed.instN_eq] at h₂
  have h₂' := h₂
  obtain ⟨_, hd₂⟩ := h₂'
  obtain ⟨⟨_, heSort⟩, _, hleftEBody⟩ :=
    hd₂.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightEBody⟩ := hd₂.hasType.2.lam_inv wf trivial
  have h₃ := VEnv.IsDefEqU.lam_instU wf trivial h₂ heSort
    hleftEBody hrightEBody he
  simp [VExpr.inst, hrtypeClosed.instN_eq,
    hrditeClosed.instN_eq, hofTrueClosed.instN_eq,
    hpClosed.instN_eq] at h₃
  have h₃' := h₃
  obtain ⟨_, hd₃⟩ := h₃'
  obtain ⟨hproofTyLType, _, hbodyLT⟩ :=
    hd₃.hasType.1.lam_inv wf trivial
  have hΓ : OnCtx [(.app (.app rtype p) .boolTrue)]
      (env.IsType 0) := ⟨trivial, hproofTyLType⟩
  obtain ⟨_, _, hprefixThenT, _⟩ :=
    hbodyLT.hasType.1.app_inv wf.ordered hΓ
  obtain ⟨_, _, hprefixProofT, _⟩ :=
    hprefixThenT.app_inv wf.ordered hΓ
  obtain ⟨prefixArgTy, prefixBodyTy, hprefixLocalT, hproofVarT⟩ :=
    hprefixProofT.app_inv wf.ordered hΓ
  obtain ⟨_, _, hcallThenT, _⟩ := hcallT.app_inv wf.ordered trivial
  obtain ⟨_, _, hcallProofT, _⟩ :=
    hcallThenT.app_inv wf.ordered trivial
  obtain ⟨hpTy, hpBodyTy, hprefixCallT, hpT⟩ :=
    hcallProofT.app_inv wf.ordered trivial
  have hprefixEq : env.IsDefEqU 0
      [(.app (.app rtype p) .boolTrue)]
      (.app (.app rdite p) .boolTrue)
      (.app (.app rdite p) .boolTrue) :=
    .refl ⟨_, hprefixLocalT⟩
  obtain ⟨_, hinst⟩ := VEnv.instantiate_dependent_proof_lam wf
    (prefixArgTy := prefixArgTy) (prefixBodyTy := prefixBodyTy)
    (hpTy := hpTy) (hpBodyTy := hpBodyTy)
    hprefixLocalT hproofVarT hprefixCallT hpT hprefixEq h₃
  refine ⟨.app (.app ofTrue p) H, ?_⟩
  simpa [VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.liftN, liftVar,
    hrditeClosed.instN_eq, hofTrueClosed.instN_eq,
    hpClosed.instN_eq, htClosed.liftN_eq, htClosed.instN_eq,
    heClosed.lift_eq, heClosed.instN_eq] using hinst

/-- False counterpart of `reflectionNatDITE_true_select_from_call`. -/
private theorem VEnv.reflectionNatDITE_false_select_from_call
    {env : VEnv} (wf : env.WF)
    {rtype rdite ofFalse p H t e R : VExpr}
    (hrtypeClosed : rtype.ClosedN) (hrditeClosed : rdite.ClosedN)
    (hofFalseClosed : ofFalse.ClosedN)
    (heq : env.IsDefEqU 0 []
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
       .app (.bvar 1) (.app (.app ofFalse (.bvar 3)) (.bvar 0))))
    (hcallT : env.HasType 0 []
      (.app (.app (.app (.app (.app rdite p) .boolFalse) H) t) e) R)
    (hp : env.HasType 0 [] p (.sort .zero))
    (ht : env.HasType 0 [] t (.forallE p .nat))
    (he : env.HasType 0 [] e
      (.forallE (.app (.const ``Not []) p) .nat)) :
    ∃ proof, env.IsDefEqU 0 []
      (.app (.app (.app (.app (.app rdite p) .boolFalse) H) t) e)
      (.app e proof) := by
  have hpClosed : p.ClosedN :=
    (hp.closedN' wf.ordered.closed trivial).1
  have htClosed : t.ClosedN :=
    (ht.closedN' wf.ordered.closed trivial).1
  have heClosed : e.ClosedN :=
    (he.closedN' wf.ordered.closed trivial).1
  have heq' := heq
  obtain ⟨_, hd⟩ := heq'
  obtain ⟨⟨_, hpropSort⟩, _, hleftBodyT⟩ :=
    hd.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightBodyT⟩ := hd.hasType.2.lam_inv wf trivial
  have h₁ := VEnv.IsDefEqU.lam_instU wf trivial heq hpropSort
    hleftBodyT hrightBodyT hp
  simp [VExpr.inst, hrtypeClosed.instN_eq,
    hrditeClosed.instN_eq, hofFalseClosed.instN_eq, hpClosed.lift_eq] at h₁
  have h₁' := h₁
  obtain ⟨_, hd₁⟩ := h₁'
  obtain ⟨⟨_, htSort⟩, _, hleftTBody⟩ :=
    hd₁.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightTBody⟩ := hd₁.hasType.2.lam_inv wf trivial
  have h₂ := VEnv.IsDefEqU.lam_instU wf trivial h₁ htSort
    hleftTBody hrightTBody ht
  simp [VExpr.inst, hrtypeClosed.instN_eq,
    hrditeClosed.instN_eq, hofFalseClosed.instN_eq, hpClosed.instN_eq] at h₂
  have h₂' := h₂
  obtain ⟨_, hd₂⟩ := h₂'
  obtain ⟨⟨_, heSort⟩, _, hleftEBody⟩ :=
    hd₂.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightEBody⟩ := hd₂.hasType.2.lam_inv wf trivial
  have h₃ := VEnv.IsDefEqU.lam_instU wf trivial h₂ heSort
    hleftEBody hrightEBody he
  simp [VExpr.inst, hrtypeClosed.instN_eq,
    hrditeClosed.instN_eq, hofFalseClosed.instN_eq, hpClosed.instN_eq] at h₃
  have h₃' := h₃
  obtain ⟨_, hd₃⟩ := h₃'
  obtain ⟨hproofTyLType, _, hbodyLT⟩ :=
    hd₃.hasType.1.lam_inv wf trivial
  have hΓ : OnCtx [(.app (.app rtype p) .boolFalse)]
      (env.IsType 0) := ⟨trivial, hproofTyLType⟩
  obtain ⟨_, _, hprefixThenT, _⟩ :=
    hbodyLT.hasType.1.app_inv wf.ordered hΓ
  obtain ⟨_, _, hprefixProofT, _⟩ :=
    hprefixThenT.app_inv wf.ordered hΓ
  obtain ⟨prefixArgTy, prefixBodyTy, hprefixLocalT, hproofVarT⟩ :=
    hprefixProofT.app_inv wf.ordered hΓ
  obtain ⟨_, _, hcallThenT, _⟩ := hcallT.app_inv wf.ordered trivial
  obtain ⟨_, _, hcallProofT, _⟩ :=
    hcallThenT.app_inv wf.ordered trivial
  obtain ⟨hpTy, hpBodyTy, hprefixCallT, hpT⟩ :=
    hcallProofT.app_inv wf.ordered trivial
  have hprefixEq : env.IsDefEqU 0
      [(.app (.app rtype p) .boolFalse)]
      (.app (.app rdite p) .boolFalse)
      (.app (.app rdite p) .boolFalse) :=
    .refl ⟨_, hprefixLocalT⟩
  obtain ⟨_, hinst⟩ := VEnv.instantiate_dependent_proof_lam wf
    (prefixArgTy := prefixArgTy) (prefixBodyTy := prefixBodyTy)
    (hpTy := hpTy) (hpBodyTy := hpBodyTy)
    hprefixLocalT hproofVarT hprefixCallT hpT hprefixEq h₃
  refine ⟨.app (.app ofFalse p) H, ?_⟩
  simpa [VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.liftN, liftVar,
    hrditeClosed.instN_eq, hofFalseClosed.instN_eq,
    hpClosed.instN_eq, htClosed.liftN_eq, htClosed.instN_eq,
    heClosed.lift_eq, heClosed.instN_eq] using hinst

/-- Select the true branch of a typed nondependent reflection selector after
its Boolean argument has evaluated to `true`. -/
theorem VEnv.reflectionITE_true_of_condition
    {env : VEnv} (wf : env.WF)
    {rtype rite p boolV H α t e R : VExpr}
    (hrtypeClosed : rtype.ClosedN) (hriteClosed : rite.ClosedN)
    (heq : env.IsDefEqU 0 []
      (.lam (.sort .zero) <|
        .lam (.app (.app rtype (.bvar 0)) .boolTrue) <|
          .app (.app (.app rite (.bvar 1)) .boolTrue) (.bvar 0))
      (.lam (.sort .zero) <|
        .lam (.app (.app rtype (.bvar 0)) .boolTrue) <|
          .lam (.sort (.succ .zero)) <|
            .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 1))
    (hriteHas : env.HasType 0 [] rite
      (.forallE (.sort .zero) <|
       .forallE .bool <|
       .forallE (.app (.app rtype (.bvar 1)) (.bvar 0)) <|
       .forallE (.sort (.succ .zero)) <|
       .forallE (.bvar 0) <| .forallE (.bvar 1) (.bvar 2)))
    (hcallT : env.HasType 0 []
      (.app (.app (.app (.app (.app (.app rite p) boolV) H) α) t) e) R)
    (hbool : env.IsDefEqU 0 [] boolV .boolTrue) :
    env.IsDefEqU 0 []
      (.app (.app (.app (.app (.app (.app rite p) boolV) H) α) t) e) t := by
  have hreplace := VEnv.replaceReflectionITECondition wf hcallT hbool
  have hcallTrueT := (hreplace.of_l wf trivial hcallT).hasType.2
  obtain ⟨hp, hH, hα, ht, he⟩ := VEnv.reflectionITE_call_types wf
    hrtypeClosed hriteHas hcallTrueT
  have hselect := VEnv.reflectionITE_true_select wf
    hrtypeClosed hrtypeClosed hriteClosed heq hp hH hH hα ht he
  exact hreplace.trans wf trivial hselect

/-- False counterpart of `reflectionITE_true_of_condition`. -/
theorem VEnv.reflectionITE_false_of_condition
    {env : VEnv} (wf : env.WF)
    {rtype rite p boolV H α t e R : VExpr}
    (hrtypeClosed : rtype.ClosedN) (hriteClosed : rite.ClosedN)
    (heq : env.IsDefEqU 0 []
      (.lam (.sort .zero) <|
        .lam (.app (.app rtype (.bvar 0)) .boolFalse) <|
          .app (.app (.app rite (.bvar 1)) .boolFalse) (.bvar 0))
      (.lam (.sort .zero) <|
        .lam (.app (.app rtype (.bvar 0)) .boolFalse) <|
          .lam (.sort (.succ .zero)) <|
            .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 0))
    (hriteHas : env.HasType 0 [] rite
      (.forallE (.sort .zero) <|
       .forallE .bool <|
       .forallE (.app (.app rtype (.bvar 1)) (.bvar 0)) <|
       .forallE (.sort (.succ .zero)) <|
       .forallE (.bvar 0) <| .forallE (.bvar 1) (.bvar 2)))
    (hcallT : env.HasType 0 []
      (.app (.app (.app (.app (.app (.app rite p) boolV) H) α) t) e) R)
    (hbool : env.IsDefEqU 0 [] boolV .boolFalse) :
    env.IsDefEqU 0 []
      (.app (.app (.app (.app (.app (.app rite p) boolV) H) α) t) e) e := by
  have hreplace := VEnv.replaceReflectionITECondition wf hcallT hbool
  have hcallFalseT := (hreplace.of_l wf trivial hcallT).hasType.2
  obtain ⟨hp, hH, hα, ht, he⟩ := VEnv.reflectionITE_call_types wf
    hrtypeClosed hriteHas hcallFalseT
  have hselect := VEnv.reflectionITE_false_select wf
    hrtypeClosed hrtypeClosed hriteClosed heq hp hH hH hα ht he
  exact hreplace.trans wf trivial hselect

/-- Select the true branch after a reflected dependent selector's Boolean
argument has been evaluated to `true`. -/
theorem VEnv.reflectionNatDITE_true_of_condition
    {env : VEnv} (wf : env.WF)
    {rtype rdite ofTrue p boolV H t e R : VExpr}
    (hrtypeClosed : rtype.ClosedN) (hrditeClosed : rdite.ClosedN)
    (hofTrueClosed : ofTrue.ClosedN)
    (heq : env.IsDefEqU 0 []
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
       .app (.bvar 2) (.app (.app ofTrue (.bvar 3)) (.bvar 0))))
    (hrditeHas : env.HasType 0 [] rdite
      (.forallE (.sort .zero) <|
       .forallE .bool <|
       .forallE (.app (.app rtype (.bvar 1)) (.bvar 0)) <|
       .forallE (.forallE (.bvar 2) .nat) <|
       .forallE (.forallE
         (.app (.const ``Not []) (.bvar 3)) .nat) .nat))
    (hcallT : env.HasType 0 []
      (.app (.app (.app (.app (.app rdite p) boolV) H) t) e) R)
    (hbool : env.IsDefEqU 0 [] boolV .boolTrue) :
    ∃ proof, env.IsDefEqU 0 []
      (.app (.app (.app (.app (.app rdite p) boolV) H) t) e)
      (.app t proof) := by
  obtain ⟨hp, ht, he⟩ := VEnv.reflectionNatDITE_call_types wf
    hrtypeClosed hrditeHas hcallT
  have hreplace := VEnv.replaceNatDITECondition wf hcallT hbool
  have hcallTrueT := (hreplace.of_l wf trivial hcallT).hasType.2
  obtain ⟨proof, hselect⟩ :=
    VEnv.reflectionNatDITE_true_select_from_call wf
      hrtypeClosed hrditeClosed hofTrueClosed heq hcallTrueT hp ht he
  exact ⟨proof, hreplace.trans wf trivial hselect⟩

/-- False counterpart of `reflectionNatDITE_true_of_condition`. -/
theorem VEnv.reflectionNatDITE_false_of_condition
    {env : VEnv} (wf : env.WF)
    {rtype rdite ofFalse p boolV H t e R : VExpr}
    (hrtypeClosed : rtype.ClosedN) (hrditeClosed : rdite.ClosedN)
    (hofFalseClosed : ofFalse.ClosedN)
    (heq : env.IsDefEqU 0 []
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
       .app (.bvar 1) (.app (.app ofFalse (.bvar 3)) (.bvar 0))))
    (hrditeHas : env.HasType 0 [] rdite
      (.forallE (.sort .zero) <|
       .forallE .bool <|
       .forallE (.app (.app rtype (.bvar 1)) (.bvar 0)) <|
       .forallE (.forallE (.bvar 2) .nat) <|
       .forallE (.forallE
         (.app (.const ``Not []) (.bvar 3)) .nat) .nat))
    (hcallT : env.HasType 0 []
      (.app (.app (.app (.app (.app rdite p) boolV) H) t) e) R)
    (hbool : env.IsDefEqU 0 [] boolV .boolFalse) :
    ∃ proof, env.IsDefEqU 0 []
      (.app (.app (.app (.app (.app rdite p) boolV) H) t) e)
      (.app e proof) := by
  obtain ⟨hp, ht, he⟩ := VEnv.reflectionNatDITE_call_types wf
    hrtypeClosed hrditeHas hcallT
  have hreplace := VEnv.replaceNatDITECondition wf hcallT hbool
  have hcallFalseT := (hreplace.of_l wf trivial hcallT).hasType.2
  obtain ⟨proof, hselect⟩ :=
    VEnv.reflectionNatDITE_false_select_from_call wf
      hrtypeClosed hrditeClosed hofFalseClosed heq hcallFalseT hp ht he
  exact ⟨proof, hreplace.trans wf trivial hselect⟩

/-- A concrete true `Nat.ble` result selects the true branch of the checked
dependent selector. -/
theorem VEnv.reflectionNatDITE_of_natBLE_true
    {env : VEnv} (wf : env.WF)
    (hbleR : env.ReflectsNatNatBool ``Nat.ble Nat.ble)
    (hctors : VEnv.HasNatBoolConstructors env)
    (hbleC : env.contains ``Nat.ble)
    {a b : Nat} {rtype rdite ofTrue p bleV H t e R : VExpr}
    (hrtypeClosed : rtype.ClosedN) (hrditeClosed : rdite.ClosedN)
    (hofTrueClosed : ofTrue.ClosedN)
    (heq : env.IsDefEqU 0 []
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
       .app (.bvar 2) (.app (.app ofTrue (.bvar 3)) (.bvar 0))))
    (hrditeHas : env.HasType 0 [] rdite
      (.forallE (.sort .zero) <|
       .forallE .bool <|
       .forallE (.app (.app rtype (.bvar 1)) (.bvar 0)) <|
       .forallE (.forallE (.bvar 2) .nat) <|
       .forallE (.forallE
         (.app (.const ``Not []) (.bvar 3)) .nat) .nat))
    (hbleS : TrExprS env [] []
      (mkApp2 q(Nat.ble) (.lit (.natVal a)) (.lit (.natVal b))) bleV)
    (hble : Nat.ble a b = true)
    (hcallT : env.HasType 0 []
      (.app (.app (.app (.app (.app rdite p) bleV) H) t) e) R) :
    ∃ proof, env.IsDefEqU 0 []
      (.app (.app (.app (.app (.app rdite p) bleV) H) t) e)
      (.app t proof) := by
  have hbleEq := Condition.natBLE_application_eval
    wf hbleR hctors hbleC hbleS
  rw [hble] at hbleEq
  exact VEnv.reflectionNatDITE_true_of_condition wf
    hrtypeClosed hrditeClosed hofTrueClosed heq hrditeHas hcallT hbleEq

/-- A concrete false `Nat.ble` result selects the false branch. -/
theorem VEnv.reflectionNatDITE_of_natBLE_false
    {env : VEnv} (wf : env.WF)
    (hbleR : env.ReflectsNatNatBool ``Nat.ble Nat.ble)
    (hctors : VEnv.HasNatBoolConstructors env)
    (hbleC : env.contains ``Nat.ble)
    {a b : Nat} {rtype rdite ofFalse p bleV H t e R : VExpr}
    (hrtypeClosed : rtype.ClosedN) (hrditeClosed : rdite.ClosedN)
    (hofFalseClosed : ofFalse.ClosedN)
    (heq : env.IsDefEqU 0 []
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
       .app (.bvar 1) (.app (.app ofFalse (.bvar 3)) (.bvar 0))))
    (hrditeHas : env.HasType 0 [] rdite
      (.forallE (.sort .zero) <|
       .forallE .bool <|
       .forallE (.app (.app rtype (.bvar 1)) (.bvar 0)) <|
       .forallE (.forallE (.bvar 2) .nat) <|
       .forallE (.forallE
         (.app (.const ``Not []) (.bvar 3)) .nat) .nat))
    (hbleS : TrExprS env [] []
      (mkApp2 q(Nat.ble) (.lit (.natVal a)) (.lit (.natVal b))) bleV)
    (hble : Nat.ble a b = false)
    (hcallT : env.HasType 0 []
      (.app (.app (.app (.app (.app rdite p) bleV) H) t) e) R) :
    ∃ proof, env.IsDefEqU 0 []
      (.app (.app (.app (.app (.app rdite p) bleV) H) t) e)
      (.app e proof) := by
  have hbleEq := Condition.natBLE_application_eval
    wf hbleR hctors hbleC hbleS
  rw [hble] at hbleEq
  exact VEnv.reflectionNatDITE_false_of_condition wf
    hrtypeClosed hrditeClosed hofFalseClosed heq hrditeHas hcallT hbleEq

theorem VEnv.NatLESelectorCertificate.selectDITETrue
    {env : VEnv} (cert : VEnv.NatLESelectorCertificate env)
    (wf : env.WF) (hbleR : env.ReflectsNatNatBool ``Nat.ble Nat.ble)
    (hctors : VEnv.HasNatBoolConstructors env)
    (hbleC : env.contains ``Nat.ble)
    {a b : Nat} {p bleV H t e R : VExpr}
    (hbleS : TrExprS env [] []
      (mkApp2 q(Nat.ble) (.lit (.natVal a)) (.lit (.natVal b))) bleV)
    (hble : Nat.ble a b = true)
    (hcallT : env.HasType 0 []
      (.app (.app (.app (.app (.app cert.rdite p) bleV) H) t) e) R) :
    ∃ proof, env.IsDefEqU 0 []
      (.app (.app (.app (.app (.app cert.rdite p) bleV) H) t) e)
      (.app t proof) := by
  have heqs := cert.dite_equations wf
  exact VEnv.reflectionNatDITE_of_natBLE_true wf hbleR hctors hbleC
    (TrExprS.target_closed wf cert.rtypeS)
    (TrExprS.target_closed wf cert.rditeS)
    (TrExprS.target_closed wf cert.ofTrueS)
    heqs.1 cert.rditeHas hbleS hble hcallT

theorem VEnv.NatLESelectorCertificate.selectDITEFalse
    {env : VEnv} (cert : VEnv.NatLESelectorCertificate env)
    (wf : env.WF) (hbleR : env.ReflectsNatNatBool ``Nat.ble Nat.ble)
    (hctors : VEnv.HasNatBoolConstructors env)
    (hbleC : env.contains ``Nat.ble)
    {a b : Nat} {p bleV H t e R : VExpr}
    (hbleS : TrExprS env [] []
      (mkApp2 q(Nat.ble) (.lit (.natVal a)) (.lit (.natVal b))) bleV)
    (hble : Nat.ble a b = false)
    (hcallT : env.HasType 0 []
      (.app (.app (.app (.app (.app cert.rdite p) bleV) H) t) e) R) :
    ∃ proof, env.IsDefEqU 0 []
      (.app (.app (.app (.app (.app cert.rdite p) bleV) H) t) e)
      (.app e proof) := by
  have heqs := cert.dite_equations wf
  exact VEnv.reflectionNatDITE_of_natBLE_false wf hbleR hctors hbleC
    (TrExprS.target_closed wf cert.rtypeS)
    (TrExprS.target_closed wf cert.rditeS)
    (TrExprS.target_closed wf cert.ofFalseS)
    heqs.2 cert.rditeHas hbleS hble hcallT

/-- Constructor-syntax form of `selectDITETrue`, for checked equations after
closed-lambda instantiation. -/
theorem VEnv.NatLESelectorCertificate.selectDITETrueConstructor
    {env : VEnv} (cert : VEnv.NatLESelectorCertificate env)
    (wf : env.WF) (hbleR : env.ReflectsNatNatBool ``Nat.ble Nat.ble)
    (hctors : VEnv.HasNatBoolConstructors env)
    (hbleC : env.contains ``Nat.ble)
    {a b : Nat} {p bleV H t e R : VExpr}
    (hbleS : TrExprS env [] []
      (mkApp2 q(Nat.ble) (.natLitToConstructor a)
        (.natLitToConstructor b)) bleV)
    (hble : Nat.ble a b = true)
    (hcallT : env.HasType 0 []
      (.app (.app (.app (.app (.app cert.rdite p) bleV) H) t) e) R) :
    ∃ proof, env.IsDefEqU 0 []
      (.app (.app (.app (.app (.app cert.rdite p) bleV) H) t) e)
      (.app t proof) := by
  have hbool := Condition.natBLE_constructor_application_eval
    wf hbleR hctors hbleC hbleS
  rw [hble] at hbool
  have heqs := cert.dite_equations wf
  exact VEnv.reflectionNatDITE_true_of_condition wf
    (TrExprS.target_closed wf cert.rtypeS)
    (TrExprS.target_closed wf cert.rditeS)
    (TrExprS.target_closed wf cert.ofTrueS)
    heqs.1 cert.rditeHas hcallT hbool

/-- Constructor-syntax form of `selectDITEFalse`. -/
theorem VEnv.NatLESelectorCertificate.selectDITEFalseConstructor
    {env : VEnv} (cert : VEnv.NatLESelectorCertificate env)
    (wf : env.WF) (hbleR : env.ReflectsNatNatBool ``Nat.ble Nat.ble)
    (hctors : VEnv.HasNatBoolConstructors env)
    (hbleC : env.contains ``Nat.ble)
    {a b : Nat} {p bleV H t e R : VExpr}
    (hbleS : TrExprS env [] []
      (mkApp2 q(Nat.ble) (.natLitToConstructor a)
        (.natLitToConstructor b)) bleV)
    (hble : Nat.ble a b = false)
    (hcallT : env.HasType 0 []
      (.app (.app (.app (.app (.app cert.rdite p) bleV) H) t) e) R) :
    ∃ proof, env.IsDefEqU 0 []
      (.app (.app (.app (.app (.app cert.rdite p) bleV) H) t) e)
      (.app e proof) := by
  have hbool := Condition.natBLE_constructor_application_eval
    wf hbleR hctors hbleC hbleS
  rw [hble] at hbool
  have heqs := cert.dite_equations wf
  exact VEnv.reflectionNatDITE_false_of_condition wf
    (TrExprS.target_closed wf cert.rtypeS)
    (TrExprS.target_closed wf cert.rditeS)
    (TrExprS.target_closed wf cert.ofFalseS)
    heqs.2 cert.rditeHas hcallT hbool

theorem VEnv.NatLESelectorCertificate.selectITETrue
    {env : VEnv} (cert : VEnv.NatLESelectorCertificate env)
    (wf : env.WF) (hbleR : env.ReflectsNatNatBool ``Nat.ble Nat.ble)
    (hctors : VEnv.HasNatBoolConstructors env)
    (hbleC : env.contains ``Nat.ble)
    {a b : Nat} {p bleV H α t e R : VExpr}
    (hbleS : TrExprS env [] []
      (mkApp2 q(Nat.ble) (.lit (.natVal a)) (.lit (.natVal b))) bleV)
    (hble : Nat.ble a b = true)
    (hcallT : env.HasType 0 []
      (.app (.app (.app (.app (.app (.app cert.rite p) bleV) H) α) t) e) R) :
    env.IsDefEqU 0 []
      (.app (.app (.app (.app (.app (.app cert.rite p) bleV) H) α) t) e) t := by
  have hbleEq := Condition.natBLE_application_eval
    wf hbleR hctors hbleC hbleS
  rw [hble] at hbleEq
  exact VEnv.reflectionITE_true_of_condition wf
    (TrExprS.target_closed wf cert.rtypeS)
    (TrExprS.target_closed wf cert.riteS)
    (cert.ite_equations wf).1 cert.riteHas hcallT hbleEq

theorem VEnv.NatLESelectorCertificate.selectITEFalse
    {env : VEnv} (cert : VEnv.NatLESelectorCertificate env)
    (wf : env.WF) (hbleR : env.ReflectsNatNatBool ``Nat.ble Nat.ble)
    (hctors : VEnv.HasNatBoolConstructors env)
    (hbleC : env.contains ``Nat.ble)
    {a b : Nat} {p bleV H α t e R : VExpr}
    (hbleS : TrExprS env [] []
      (mkApp2 q(Nat.ble) (.lit (.natVal a)) (.lit (.natVal b))) bleV)
    (hble : Nat.ble a b = false)
    (hcallT : env.HasType 0 []
      (.app (.app (.app (.app (.app (.app cert.rite p) bleV) H) α) t) e) R) :
    env.IsDefEqU 0 []
      (.app (.app (.app (.app (.app (.app cert.rite p) bleV) H) α) t) e) e := by
  have hbleEq := Condition.natBLE_application_eval
    wf hbleR hctors hbleC hbleS
  rw [hble] at hbleEq
  exact VEnv.reflectionITE_false_of_condition wf
    (TrExprS.target_closed wf cert.rtypeS)
    (TrExprS.target_closed wf cert.riteS)
    (cert.ite_equations wf).2 cert.riteHas hcallT hbleEq

end Lean4Lean.Environment
