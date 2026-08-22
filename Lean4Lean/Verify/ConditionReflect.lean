import Lean4Lean.Verify.BitwiseSupport

/-! Generic condition-reflection machinery shared by the `Nat.ble`
(mod/div) and `Nat.beq` (bitwise) condition tracks: closed-lambda
helpers, canonicalization of applied `Reflection.ite`/`Reflection.natDITE`
translations, branch-selection defeqs, and the checked-equation
certificates, all parameterized over the `Reflection` scheme. -/

namespace Lean4Lean.Environment
open Lean VEnv

/-- Replace the decision argument of a fully applied target `ite`, retaining
the surrounding type and branch applications. -/
theorem VEnv.replaceITECondition
    {env : VEnv} (wf : env.WF)
    {iteV α propV decV decV' thenV elseV R : VExpr}
    (houtT : env.HasType 0 []
      (.app (.app (.app (.app (.app iteV α) propV) decV) thenV) elseV) R)
    (hdec : env.IsDefEqU 0 [] decV decV') :
    env.IsDefEqU 0 []
      (.app (.app (.app (.app (.app iteV α) propV) decV) thenV) elseV)
      (.app (.app (.app (.app (.app iteV α) propV) decV') thenV) elseV) := by
  obtain ⟨_, _, hthenAppT, helseT⟩ := houtT.app_inv wf trivial
  obtain ⟨_, _, hdecAppT, hthenT⟩ := hthenAppT.app_inv wf trivial
  obtain ⟨_, _, hprefixT, hdecT⟩ := hdecAppT.app_inv wf trivial
  have h₁ := hdec.app_arg wf trivial hprefixT hdecT
  have h₂ := h₁.app_same wf trivial hdecAppT hthenT
  exact h₂.app_same wf trivial hthenAppT helseT

/-- Replace the source and target decision argument in a translated fully
applied `ite`.  Typing of the later applications is transported across the
target definitional equality. -/
theorem TrExprS.replaceITECondition
    {env : VEnv} (wf : env.WF)
    {iteS αS propS decS decS' thenS elseS : Expr}
    {iteV αV propV decV decV' thenV elseV : VExpr}
    (hcall : TrExprS env [] []
      (mkApp (mkApp (mkApp (mkApp (mkApp iteS αS) propS) decS)
        thenS) elseS)
      (.app (.app (.app (.app (.app iteV αV) propV) decV)
        thenV) elseV))
    (hdecS' : TrExprS env [] [] decS' decV')
    (hdecEq : env.IsDefEqU 0 [] decV decV') :
    TrExprS env [] []
      (mkApp (mkApp (mkApp (mkApp (mkApp iteS αS) propS) decS')
        thenS) elseS)
      (.app (.app (.app (.app (.app iteV αV) propV) decV')
        thenV) elseV) := by
  cases hcall with
  | app hthenAppT helseT hfn helseS =>
    cases hfn with
    | app hdecAppT hthenT hfn hthenS =>
      cases hfn with
      | app hprefixT hdecT hprefix hdecS =>
        have hdecAppEq := hdecEq.app_arg wf trivial hprefixT hdecT
        have hdecAppT' := (hdecAppEq.of_l wf trivial hdecAppT).hasType.2
        have hthenAppEq := hdecAppEq.app_same wf trivial hdecAppT hthenT
        have hthenAppT' :=
          (hthenAppEq.of_l wf trivial hthenAppT).hasType.2
        exact .app hthenAppT' helseT
          (.app hdecAppT' hthenT
            (.app hprefixT
              (hdecEq.of_l wf trivial hdecT).hasType.2
              hprefix hdecS') hthenS) helseS

/-- Instantiate a closed translated lambda and retain its target beta
equation. -/
theorem TrExprS.applyClosedLam
    {env : VEnv} (wf : env.WF)
    {name : Name} {ty body a : Expr} {bi : BinderInfo}
    {tyV bodyV aV : VExpr}
    (hlam : TrExprS env [] [] (.lam name ty body bi) (.lam tyV bodyV))
    (haS : TrExprS env [] [] a aV)
    (haT : env.HasType 0 [] aV tyV) :
    TrExprS env [] [] (body.instantiate1' a) (bodyV.inst aV) ∧
      env.IsDefEqU 0 [] (.app (.lam tyV bodyV) aV) (bodyV.inst aV) := by
  cases hlam with
  | lam htyV htyS hbodyS =>
    have hbodyInstS := TrExprS.inst (env := env) (Us := []) (Δ := [])
      wf.ordered haT hbodyS haS
    obtain ⟨_, hbodyWF⟩ := hbodyS.wf wf.ordered
      (Us := []) (Δ := [(none, .vlam tyV)])
      ⟨trivial, nofun, htyV⟩
    exact ⟨hbodyInstS, ⟨_, .beta hbodyWF.hasType.1 haT⟩⟩

theorem TrExprS.closedLam_hasType
    {env : VEnv} (wf : env.WF)
    {name : Name} {ty body : Expr} {bi : BinderInfo}
    {tyV bodyV : VExpr}
    (hlam : TrExprS env [] [] (.lam name ty body bi) (.lam tyV bodyV)) :
    ∃ bodyTy, env.HasType 0 [] (.lam tyV bodyV) (.forallE tyV bodyTy) := by
  cases hlam with
  | lam htyV htyS hbodyS =>
    obtain ⟨bodyTy, hbodyWF⟩ := hbodyS.wf wf.ordered
      (Us := []) (Δ := [(none, .vlam tyV)])
      ⟨trivial, nofun, htyV⟩
    exact ⟨bodyTy, .lam htyV.choose_spec hbodyWF.hasType.1⟩

/-- The domain used to type an application of a translated lambda is
definitionally equal to the lambda's translated binder type. -/
theorem TrExprS.closedLam_arg_hasType
    {env : VEnv} (wf : env.WF)
    {name : Name} {ty body : Expr} {bi : BinderInfo}
    {tyV bodyV aV A B : VExpr}
    (hlam : TrExprS env [] [] (.lam name ty body bi) (.lam tyV bodyV))
    (hfnT : env.HasType 0 [] (.lam tyV bodyV) (.forallE A B))
    (haT : env.HasType 0 [] aV A) :
    env.HasType 0 [] aV tyV := by
  obtain ⟨bodyTy, hcanonicalT⟩ := TrExprS.closedLam_hasType wf hlam
  have hforallEq := hfnT.uniqU wf trivial hcanonicalT
  obtain ⟨_, hdomainEq⟩ := (hforallEq.forallE_inv wf trivial).1
  exact haT.defeqU_r wf trivial ⟨_, hdomainEq⟩

/-- A closed, projection-free source expression has the same target
translation after introducing unrelated bound variables. -/
theorem TrExprS.unique_closed_weak
    {env : VEnv} (wf : env.WF)
    {e : Expr} {eV eV' : VExpr} {Δ : VLCtx} {dn n : Nat}
    (hunique : TrExprS.IsUnique e)
    (hclosed : e.looseBVarRange' = 0)
    (hglobal : TrExprS env [] [] e eV)
    (hlocal : TrExprS env [] Δ e eV')
    (W : VLCtx.BVLift [] Δ dn 0 n 0) :
    eV' = eV := by
  obtain ⟨_, hglobalWF⟩ := hglobal.wf wf.ordered
    (Us := []) (Δ := []) trivial
  have heVClosed :=
    (hglobalWF.hasType.1.closedN' wf.ordered.closed trivial).1
  have hsourceLift : e.liftLooseBVars' 0 dn = e :=
    Expr.liftLooseBVars_eq_self (by rw [hclosed]; omega)
  have htargetLift : eV.liftN n 0 = eV :=
    heVClosed.liftN_eq (Nat.zero_le _)
  have hweak := hglobal.weakBV wf.ordered W
  rw [hsourceLift, htargetLift] at hweak
  exact hlocal.unique hunique hweak

theorem TrExprS.target_closed
    {env : VEnv} (wf : env.WF) {e : Expr} {eV : VExpr}
    (h : TrExprS env [] [] e eV) : eV.ClosedN := by
  obtain ⟨_, heWF⟩ := h.wf wf.ordered (Us := []) (Δ := []) trivial
  exact (heWF.hasType.1.closedN' wf.ordered.closed trivial).1

/-- Evaluate a translated application of a reflected `Nat → Nat → Bool`
primitive at two concrete naturals, from arbitrary source presentations of
the argument literals.  Instantiated at `Nat.ble` by the mod/div condition
track and at `Nat.beq` by the bitwise condition track. -/
theorem Condition.reflectsNatNatBool_application_eval
    {env : VEnv} (wf : env.WF) {fc : Name} {f : Nat → Nat → Bool}
    (hfR : env.ReflectsNatNatBool fc f)
    (hctors : VEnv.HasNatBoolConstructors env)
    (hfC : env.contains fc)
    {a b : Nat} {aS bS : Expr} {outV : VExpr}
    (haS : TrExprS env [] [] aS (.natLit a))
    (hbS : TrExprS env [] [] bS (.natLit b))
    (houtS : TrExprS env [] [] (mkApp2 (.const fc []) aS bS) outV) :
    env.IsDefEqU 0 [] outV (.boolLit (f a b)) := by
  have ⟨hfT, hfEval⟩ := hfR hfC
  obtain ⟨ci, hci, _, hlen⟩ := (hfT 0 []).const_inv wf trivial
  have hfnS : TrExprS env [] [] (.const fc []) (.const fc []) :=
    .const hci rfl hlen
  have haT := (hctors.natLitS a (Us := []) (Δ := [])).2
  have hbT := (hctors.natLitS b (Us := []) (Δ := [])).2
  have hinnerS : TrExprS env [] [] (mkApp (.const fc []) aS)
      (.app (.const fc []) (.natLit a)) :=
    .app (hfT 0 []) haT hfnS haS
  have hcanonS : TrExprS env [] [] (mkApp2 (.const fc []) aS bS)
      (.app (.app (.const fc []) (.natLit a)) (.natLit b)) :=
    .app (.app (hfT 0 []) haT) hbT hinnerS hbS
  have hlocalEq := TrExprS.uniq (Us := []) wf
    (.refl wf (U := 0) (Δ := []) trivial) houtS hcanonS
  exact hlocalEq.trans wf trivial (hfEval a b)

/-- Instantiate a translated closed binary `Nat` function at two concrete
numerals.  Yields a translation of the doubly instantiated source body, the
target beta equation, and the beta equation transported along any
definitional equality of the translated function (used to evaluate a checked
decision function through its reflected implementation). -/
theorem TrExprS.natNatLam_instantiate
    {env : VEnv} (wf : env.WF)
    (hctors : VEnv.HasNatBoolConstructors env)
    {bodyS : Expr} {fnV : VExpr}
    (hfn : TrExprS env [] []
      (.lam0 q(Nat) <| .lam0 q(Nat) <| bodyS) fnV)
    (a b : Nat) :
    ∃ outV,
      TrExprS env [] []
        ((bodyS.instantiate1' (.lit (.natVal a)) 1).instantiate1'
          (.lit (.natVal b))) outV ∧
      env.IsDefEqU 0 []
        (.app (.app fnV (.natLit a)) (.natLit b)) outV ∧
      ∀ {gV : VExpr}, env.IsDefEqU 0 [] fnV gV →
        env.IsDefEqU 0 []
          (.app (.app gV (.natLit a)) (.natLit b)) outV := by
  have ⟨haS, haT⟩ := hctors.natLitS a (Us := []) (Δ := [])
  have ⟨hbS, hbT⟩ := hctors.natLitS b (Us := []) (Δ := [])
  cases hfn with
  | lam hnatTy₁ hnatS₁ hinnerS =>
    cases hinnerS with
    | lam hnatTy₂ hnatS₂ hbodyS =>
      rename_i natTy₁ natTy₂ body
      have hnatCanon (Δ : VLCtx) : TrExprS env [] Δ q(Nat) .nat := by
        obtain ⟨_, hnatCi, _, hnatLen⟩ :=
          (haT.isType wf trivial).choose_spec.const_inv wf trivial
        exact .const hnatCi rfl (by simpa using hnatLen)
      have hctx : VLCtx.IsDefEq env 0 [] [] := .refl wf trivial
      have hnatEq₁ := TrExprS.uniq (Us := []) wf hctx hnatS₁
        (hnatCanon [])
      have haT' := haT.defeqU_r wf trivial hnatEq₁.symm
      have hinnerInst := TrExprS.inst (env := env) (Us := []) (Δ := [])
        (e₀' := .natLit a) (A₀ := natTy₁) wf.ordered haT'
        (show TrExprS env [] [(none, .vlam natTy₁)]
          (.lam0 q(Nat) bodyS) (.lam natTy₂ body) from
          .lam hnatTy₂ hnatS₂ hbodyS) haS
      cases hinnerInst with
      | lam hnatTy₂' hnatS₂' hbodyInstS =>
        have hnatEq₂ := TrExprS.uniq (Us := []) wf hctx hnatS₂'
          (hnatCanon [])
        have hbT' := hbT.defeqU_r wf trivial hnatEq₂.symm
        have hbodyInst₂ := TrExprS.inst (env := env) (Us := []) (Δ := [])
          (e₀' := .natLit b) wf.ordered hbT' hbodyInstS hbS
        have hfnS : TrExprS env [] [] (.lam0 q(Nat) <| .lam0 q(Nat) <| bodyS)
            (.lam natTy₁ <| .lam natTy₂ body) :=
          .lam hnatTy₁ hnatS₁ (.lam hnatTy₂ hnatS₂ hbodyS)
        obtain ⟨_, hfnT⟩ := hfnS.wf wf.ordered
          (Us := []) (Δ := []) trivial
        obtain ⟨⟨_, hnatSort₁⟩, _, hinnerT⟩ :=
          hfnT.hasType.1.lam_inv wf trivial
        have hbeta₁ : env.IsDefEqU 0 []
            (.app (.lam natTy₁ <| .lam natTy₂ body) (.natLit a))
            ((VExpr.lam natTy₂ body).inst (.natLit a)) :=
          ⟨_, .beta hinnerT haT'⟩
        obtain ⟨bodyTy, hbodyInstWF⟩ := hbodyInstS.wf wf.ordered
          (Us := []) (Δ := [(none, .vlam (natTy₂.inst (.natLit a)))])
          ⟨trivial, nofun, hnatTy₂'⟩
        have hbeta₂ : env.IsDefEqU 0 []
            (.app ((VExpr.lam natTy₂ body).inst (.natLit a)) (.natLit b))
            ((body.inst (.natLit a) 1).inst (.natLit b)) :=
          ⟨_, .beta hbodyInstWF.hasType.1 hbT'⟩
        obtain ⟨_, hnatSort₂⟩ := hnatTy₂'
        have hrightPrefixT : env.HasType 0 []
            ((VExpr.lam natTy₂ body).inst (.natLit a))
            (.forallE (natTy₂.inst (.natLit a)) bodyTy) := by
          simpa [VExpr.inst] using
            VEnv.HasType.lam hnatSort₂ hbodyInstWF.hasType.1
        have hprefixT :=
          (hbeta₁.of_r wf trivial hrightPrefixT).hasType.1
        have hmain := (hbeta₁.app_same wf trivial hprefixT hbT').trans
          wf trivial hbeta₂
        refine ⟨(body.inst (.natLit a) 1).inst (.natLit b),
          hbodyInst₂, hmain, ?_⟩
        intro gV hgEq
        have hfnForallT : env.HasType 0 []
            (.lam natTy₁ <| .lam natTy₂ body)
            (.forallE natTy₁ _) :=
          VEnv.HasType.lam hnatSort₁ hinnerT
        have happ₁ := hgEq.app_same wf trivial hfnForallT haT'
        have happ₂ := happ₁.app_same wf trivial hprefixT hbT'
        exact happ₂.symm.trans wf trivial hmain

/-- Recover the canonical typing of an application argument from a
canonical dependent function type for the head and the raw typing evidence
produced by `app_inv`. -/
private theorem arg_of_canonical_fnType
    {env : VEnv} (wf : env.WF) {f x A B A' B' : VExpr}
    (hcanon : env.HasType 0 [] f (.forallE A B))
    (hfRaw : env.HasType 0 [] f (.forallE A' B'))
    (hxRaw : env.HasType 0 [] x A') :
    env.HasType 0 [] x A := by
  have hTyEq := hfRaw.uniqU wf trivial hcanon
  obtain ⟨_, hATyEq⟩ := (hTyEq.forallE_inv wf trivial).1
  exact hxRaw.defeqU_r wf trivial hATyEq.toU

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
  have hp := arg_of_canonical_fnType wf hrite hriteRaw hpRaw
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
  have hbool := arg_of_canonical_fnType wf hpropCanonT hpropAppT hboolRaw
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
  have hH := arg_of_canonical_fnType wf hboolCanonT hboolAppT hHRaw
  have hHClosed : H.ClosedN :=
    (hH.closedN' wf.ordered.closed trivial).1
  have hproofCanonT : env.HasType 0 []
      (.app (.app (.app rite p) boolV) H)
      (.forallE (.sort (.succ .zero)) <|
       .forallE (.bvar 0) <| .forallE (.bvar 1) (.bvar 2)) := by
    simpa [VExpr.inst, hHClosed.lift_eq, hHClosed.instN_eq] using
      (VEnv.HasType.app hboolCanonT hH)
  have hα := arg_of_canonical_fnType wf hproofCanonT hproofAppT hαRaw
  have hαClosed : α.ClosedN :=
    (hα.closedN' wf.ordered.closed trivial).1
  have hαCanonT : env.HasType 0 []
      (.app (.app (.app (.app rite p) boolV) H) α)
      (.forallE α <| .forallE α α) := by
    simpa [VExpr.inst, hαClosed.lift_eq, hαClosed.instN_eq] using
      (VEnv.HasType.app hproofCanonT hα)
  have ht := arg_of_canonical_fnType wf hαCanonT hαAppT htRaw
  have htClosed : t.ClosedN :=
    (ht.closedN' wf.ordered.closed trivial).1
  have htCanonT : env.HasType 0 []
      (.app (.app (.app (.app (.app rite p) boolV) H) α) t)
      (.forallE α α) := by
    simpa [VExpr.inst, hαClosed.lift_eq, hαClosed.instN_eq,
      htClosed.lift_eq, htClosed.instN_eq] using
      (VEnv.HasType.app hαCanonT ht)
  exact ⟨hp, hH, hα, ht,
    arg_of_canonical_fnType wf htCanonT htAppT heRaw⟩

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
  have hp := arg_of_canonical_fnType wf hrdite hrditeRaw hpRaw
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
  have hbool := arg_of_canonical_fnType wf hpropCanonT hpropAppT hboolRaw
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
  have hH := arg_of_canonical_fnType wf hboolCanonT hboolAppT hHRaw
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
  have ht := arg_of_canonical_fnType wf hproofCanonT hproofAppT htRaw
  have htClosed : t.ClosedN :=
    (ht.closedN' wf.ordered.closed trivial).1
  have hthenCanonT : env.HasType 0 []
      (.app (.app (.app (.app rdite p) boolV) H) t)
      (.forallE (.forallE (.app (.const ``Not []) p) .nat) .nat) := by
    simpa [VExpr.inst, hpClosed.lift_eq, hpClosed.instN_eq,
      htClosed.lift_eq, htClosed.instN_eq] using
      (VEnv.HasType.app hproofCanonT ht)
  exact ⟨hp, ht,
    arg_of_canonical_fnType wf hthenCanonT hthenAppT heRaw⟩

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

theorem VExpr.boolLit_instN {b : Bool} {e : VExpr} {k : Nat} :
    (VExpr.boolLit b).inst e k = VExpr.boolLit b := by cases b <;> rfl

theorem VExpr.boolLit_liftN {b : Bool} {n k : Nat} :
    (VExpr.boolLit b).liftN n k = VExpr.boolLit b := by cases b <;> rfl

/-- The target-level Boolean branch selector: `fun (α : Type) (t f : α) => t`
for `b = true` and `... => f` for `b = false`.  This is the normal form a
checked `Reflection.ite` application reduces to once its Boolean argument is
a literal. -/
def VExpr.boolSelector (b : Bool) : VExpr :=
  .lam (.sort (.succ .zero)) <| .lam (.bvar 0) <| .lam (.bvar 1) <|
    .bvar (bif b then 1 else 0)

theorem VExpr.boolSelector_closed {b : Bool} :
    (VExpr.boolSelector b).ClosedN := by
  cases b
  · exact ⟨trivial, Nat.zero_lt_one, Nat.one_lt_two, Nat.zero_lt_succ 2⟩
  · exact ⟨trivial, Nat.zero_lt_one, Nat.one_lt_two,
      Nat.lt_succ_of_lt Nat.one_lt_two⟩

theorem VExpr.boolSelector_instN {b : Bool} {e : VExpr} {k : Nat} :
    (VExpr.boolSelector b).inst e k = VExpr.boolSelector b :=
  VExpr.boolSelector_closed.instN_eq (Nat.zero_le _)

theorem VExpr.boolSelector_hasType {env : VEnv} {b : Bool} :
    env.HasType 0 [] (VExpr.boolSelector b)
      (.forallE (.sort (.succ .zero)) <|
        .forallE (.bvar 0) <| .forallE (.bvar 1) <| .bvar 2) := by
  cases b
  · exact .lam (.sort trivial) <| .lam (.bvar .zero) <|
      .lam (.bvar (.succ .zero)) (.bvar .zero)
  · exact .lam (.sort trivial) <| .lam (.bvar .zero) <|
      .lam (.bvar (.succ .zero)) (.bvar (.succ .zero))

/-- Applying the Boolean branch selector to a type and two branches selects
the branch named by the Boolean. -/
private theorem boolSelector_apply
    {env : VEnv} (wf : env.WF) (b : Bool) {α t e : VExpr}
    (hα : env.HasType 0 [] α (.sort (.succ .zero)))
    (ht : env.HasType 0 [] t α) (he : env.HasType 0 [] e α) :
    env.IsDefEqU 0 []
      (.app (.app (.app (VExpr.boolSelector b) α) t) e)
      (bif b then t else e) := by
  have hαClosed : α.ClosedN := (hα.closedN' wf.ordered.closed trivial).1
  have htClosed : t.ClosedN := (ht.closedN' wf.ordered.closed trivial).1
  cases b
  · have hselectorT : env.HasType 0 []
        (.lam (.sort (.succ .zero)) <|
          .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 0)
        (.forallE (.sort (.succ .zero)) <|
          .forallE (.bvar 0) <| .forallE (.bvar 1) <| .bvar 2) :=
      .lam (.sort trivial) <| .lam (.bvar .zero) <|
        .lam (.bvar (.succ .zero)) (.bvar .zero)
    obtain ⟨_, houterBodyT⟩ := (hselectorT.lam_inv wf trivial).2
    have hbetaα : env.IsDefEqU 0 []
        (.app (.lam (.sort (.succ .zero)) <|
          .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 0) α)
        (.lam α <| .lam α <| .bvar 0) := by
      simpa [VExpr.inst, hαClosed.lift_eq, hαClosed.instN_eq] using
        (show env.IsDefEqU 0 [] _ _ from ⟨_, .beta houterBodyT hα⟩)
    have hselectorαT :=
      (hbetaα.of_l wf trivial (.app hselectorT hα)).hasType.2
    have hselectorαT' : env.HasType 0 []
        (.lam α <| .lam α <| .bvar 0)
        (.forallE α <| .forallE α α) := by
      simpa [VExpr.inst, hαClosed.lift_eq, hαClosed.instN_eq] using
        hselectorαT
    obtain ⟨_, htrueBodyT⟩ := (hselectorαT'.lam_inv wf trivial).2
    have hbetaT : env.IsDefEqU 0 []
        (.app (.lam α <| .lam α <| .bvar 0) t) (.lam α <| .bvar 0) := by
      simpa [VExpr.inst, hαClosed.instN_eq, htClosed.lift_eq] using
        (show env.IsDefEqU 0 [] _ _ from ⟨_, .beta htrueBodyT ht⟩)
    have hselectorT' : env.HasType 0 []
        (.lam α <| .bvar 0) (.forallE α α) := by
      have h := (hbetaT.of_l wf trivial (.app hselectorαT' ht)).hasType.2
      simpa [VExpr.inst, hαClosed.instN_eq] using h
    obtain ⟨_, hfalseBodyT⟩ := (hselectorT'.lam_inv wf trivial).2
    have hbetaE : env.IsDefEqU 0 [] (.app (.lam α <| .bvar 0) e) e := by
      simpa [VExpr.inst] using
        (show env.IsDefEqU 0 [] _ _ from ⟨_, .beta hfalseBodyT he⟩)
    have hselectorAppT : env.HasType 0 []
        (.app (.lam α <| .lam α <| .bvar 0) t) (.forallE α α) := by
      simpa [VExpr.inst, hαClosed.instN_eq] using
        (VEnv.HasType.app hselectorαT' ht)
    have hselectorOuterAppT : env.HasType 0 []
        (.app (.lam (.sort (.succ .zero)) <|
          .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 0) α)
        (.forallE α <| .forallE α α) := by
      simpa [VExpr.inst, hαClosed.lift_eq, hαClosed.instN_eq] using
        (VEnv.HasType.app hselectorT hα)
    have hselectorOuterTt : env.HasType 0 []
        (.app (.app (.lam (.sort (.succ .zero)) <|
          .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 0) α) t)
        (.forallE α α) := by
      simpa [VExpr.inst, hαClosed.instN_eq] using
        (VEnv.HasType.app hselectorOuterAppT ht)
    have hbetaαApps :=
      (hbetaα.app_same wf trivial hselectorOuterAppT ht).app_same
        wf trivial hselectorOuterTt he
    exact hbetaαApps.trans wf trivial <|
      (hbetaT.app_same wf trivial hselectorAppT he).trans wf trivial hbetaE
  · have hselectorT : env.HasType 0 []
        (.lam (.sort (.succ .zero)) <|
          .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 1)
        (.forallE (.sort (.succ .zero)) <|
          .forallE (.bvar 0) <| .forallE (.bvar 1) <| .bvar 2) :=
      .lam (.sort trivial) <| .lam (.bvar .zero) <|
        .lam (.bvar (.succ .zero)) (.bvar (.succ .zero))
    obtain ⟨_, houterBodyT⟩ := (hselectorT.lam_inv wf trivial).2
    have hbetaα : env.IsDefEqU 0 []
        (.app (.lam (.sort (.succ .zero)) <|
          .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 1) α)
        (.lam α <| .lam α <| .bvar 1) := by
      simpa [VExpr.inst, hαClosed.lift_eq, hαClosed.instN_eq] using
        (show env.IsDefEqU 0 [] _ _ from ⟨_, .beta houterBodyT hα⟩)
    have hselectorαT :=
      (hbetaα.of_l wf trivial (.app hselectorT hα)).hasType.2
    have hselectorαT' : env.HasType 0 []
        (.lam α <| .lam α <| .bvar 1)
        (.forallE α <| .forallE α α) := by
      simpa [VExpr.inst, hαClosed.lift_eq, hαClosed.instN_eq] using
        hselectorαT
    obtain ⟨_, htrueBodyT⟩ := (hselectorαT'.lam_inv wf trivial).2
    have hbetaT : env.IsDefEqU 0 []
        (.app (.lam α <| .lam α <| .bvar 1) t) (.lam α t) := by
      simpa [VExpr.inst, hαClosed.instN_eq, htClosed.lift_eq] using
        (show env.IsDefEqU 0 [] _ _ from ⟨_, .beta htrueBodyT ht⟩)
    have hselectorT' : env.HasType 0 [] (.lam α t) (.forallE α α) := by
      have h := (hbetaT.of_l wf trivial (.app hselectorαT' ht)).hasType.2
      simpa [VExpr.inst, hαClosed.instN_eq] using h
    obtain ⟨_, hfalseBodyT⟩ := (hselectorT'.lam_inv wf trivial).2
    have hbetaE : env.IsDefEqU 0 [] (.app (.lam α t) e) t := by
      simpa [VExpr.inst, htClosed.instN_eq] using
        (show env.IsDefEqU 0 [] _ _ from ⟨_, .beta hfalseBodyT he⟩)
    have hselectorAppT : env.HasType 0 []
        (.app (.lam α <| .lam α <| .bvar 1) t) (.forallE α α) := by
      simpa [VExpr.inst, hαClosed.instN_eq] using
        (VEnv.HasType.app hselectorαT' ht)
    have hselectorOuterAppT : env.HasType 0 []
        (.app (.lam (.sort (.succ .zero)) <|
          .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 1) α)
        (.forallE α <| .forallE α α) := by
      simpa [VExpr.inst, hαClosed.lift_eq, hαClosed.instN_eq] using
        (VEnv.HasType.app hselectorT hα)
    have hselectorOuterTt : env.HasType 0 []
        (.app (.app (.lam (.sort (.succ .zero)) <|
          .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 1) α) t)
        (.forallE α α) := by
      simpa [VExpr.inst, hαClosed.instN_eq] using
        (VEnv.HasType.app hselectorOuterAppT ht)
    have hbetaαApps :=
      (hbetaα.app_same wf trivial hselectorOuterAppT ht).app_same
        wf trivial hselectorOuterTt he
    exact hbetaαApps.trans wf trivial <|
      (hbetaT.app_same wf trivial hselectorAppT he).trans wf trivial hbetaE

/-- The checked selector equation for the Boolean literal `b` selects the
branch named by `b` at an arbitrary target type.  The `true`/`false`
specializations below recover the concrete statements consumed by the
`Nat.ble` and `Nat.beq` condition tracks. -/
theorem VEnv.reflectionITE_select
    {env : VEnv} (wf : env.WF) (b : Bool)
    {rtypeL rtypeR rite p H α t e : VExpr}
    (hrtypeLClosed : rtypeL.ClosedN) (hrtypeRClosed : rtypeR.ClosedN)
    (hriteClosed : rite.ClosedN)
    (heq : env.IsDefEqU 0 []
      (.lam (.sort .zero) <|
        .lam (.app (.app rtypeL (.bvar 0)) (.boolLit b)) <|
          .app (.app (.app rite (.bvar 1)) (.boolLit b)) (.bvar 0))
      (.lam (.sort .zero) <|
        .lam (.app (.app rtypeR (.bvar 0)) (.boolLit b)) <|
          VExpr.boolSelector b))
    (hp : env.HasType 0 [] p (.sort .zero))
    (hHL : env.HasType 0 [] H (.app (.app rtypeL p) (.boolLit b)))
    (hHR : env.HasType 0 [] H (.app (.app rtypeR p) (.boolLit b)))
    (hα : env.HasType 0 [] α (.sort (.succ .zero)))
    (ht : env.HasType 0 [] t α) (he : env.HasType 0 [] e α) :
    env.IsDefEqU 0 []
      (.app (.app (.app (.app (.app (.app rite p) (.boolLit b)) H) α) t) e)
      (bif b then t else e) := by
  have heq' := heq
  obtain ⟨_, hd⟩ := heq'
  obtain ⟨⟨_, hpropSort⟩, _, hleftBodyT⟩ :=
    hd.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightBodyT⟩ := hd.hasType.2.lam_inv wf trivial
  have h₁ := VEnv.IsDefEqU.lam_instU wf trivial heq hpropSort
    hleftBodyT hrightBodyT hp
  simp [VExpr.inst, hrtypeLClosed.instN_eq, hrtypeRClosed.instN_eq,
    hriteClosed.instN_eq, VExpr.boolLit_instN, VExpr.boolSelector_instN]
    at h₁
  have h₁' := h₁
  obtain ⟨_, hd₁⟩ := h₁'
  obtain ⟨⟨_, hHSort⟩, _, hleftInnerT⟩ :=
    hd₁.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightInnerT⟩ := hd₁.hasType.2.lam_inv wf trivial
  have h₂ := VEnv.IsDefEqU.lam_instU_hetero wf trivial h₁ hHSort
    hleftInnerT hrightInnerT hHL hHR
  have hselect : env.IsDefEqU 0 []
      (.app (.app (.app rite p) (.boolLit b)) H)
      (VExpr.boolSelector b) := by
    simpa [VExpr.inst, VExpr.inst_lift, hriteClosed.instN_eq,
      VExpr.boolLit_instN, VExpr.boolSelector_instN] using h₂
  have hselectorT := VExpr.boolSelector_hasType (env := env) (b := b)
  have hprefixT := (hselect.of_r wf trivial hselectorT).hasType.1
  have h₃ := hselect.app_same wf trivial hprefixT hα
  have hprefixαT := VEnv.HasType.app hprefixT hα
  have hαClosed : α.ClosedN := (hα.closedN' wf.ordered.closed trivial).1
  have hprefixαT' : env.HasType 0 []
      (.app (.app (.app (.app rite p) (.boolLit b)) H) α)
      (.forallE α <| .forallE α α) := by
    simpa [VExpr.inst, hαClosed.lift_eq] using hprefixαT
  have h₄ := h₃.app_same wf trivial hprefixαT' ht
  have hprefixαtT := VEnv.HasType.app hprefixαT' ht
  have hprefixαtT' : env.HasType 0 []
      (.app (.app (.app (.app (.app rite p) (.boolLit b)) H) α) t)
      (.forallE α α) := by
    simpa [VExpr.inst, hαClosed.lift_eq, hαClosed.instN_eq] using
      hprefixαtT
  have h₅ := h₄.app_same wf trivial hprefixαtT' he
  exact h₅.trans wf trivial (boolSelector_apply wf b hα ht he)

/-- The checked true selector equation at an arbitrary target type. -/
theorem VEnv.reflectionITE_true_select
    {env : VEnv} (wf : env.WF) {rtypeL rtypeR rite p H α t e : VExpr}
    (hrtypeLClosed : rtypeL.ClosedN) (hrtypeRClosed : rtypeR.ClosedN)
    (hriteClosed : rite.ClosedN)
    (heq : env.IsDefEqU 0 []
      (.lam (.sort .zero) <|
        .lam (.app (.app rtypeL (.bvar 0)) .boolTrue) <|
          .app (.app (.app rite (.bvar 1)) .boolTrue) (.bvar 0))
      (.lam (.sort .zero) <|
        .lam (.app (.app rtypeR (.bvar 0)) .boolTrue) <|
          .lam (.sort (.succ .zero)) <|
            .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 1))
    (hp : env.HasType 0 [] p (.sort .zero))
    (hHL : env.HasType 0 [] H (.app (.app rtypeL p) .boolTrue))
    (hHR : env.HasType 0 [] H (.app (.app rtypeR p) .boolTrue))
    (hα : env.HasType 0 [] α (.sort (.succ .zero)))
    (ht : env.HasType 0 [] t α) (he : env.HasType 0 [] e α) :
    env.IsDefEqU 0 []
      (.app (.app (.app (.app (.app (.app rite p) .boolTrue) H) α) t) e) t :=
  VEnv.reflectionITE_select wf true hrtypeLClosed hrtypeRClosed
    hriteClosed heq hp hHL hHR hα ht he

/-- The checked false selector equation at an arbitrary target type. -/
theorem VEnv.reflectionITE_false_select
    {env : VEnv} (wf : env.WF) {rtypeL rtypeR rite p H α t e : VExpr}
    (hrtypeLClosed : rtypeL.ClosedN) (hrtypeRClosed : rtypeR.ClosedN)
    (hriteClosed : rite.ClosedN)
    (heq : env.IsDefEqU 0 []
      (.lam (.sort .zero) <|
        .lam (.app (.app rtypeL (.bvar 0)) .boolFalse) <|
          .app (.app (.app rite (.bvar 1)) .boolFalse) (.bvar 0))
      (.lam (.sort .zero) <|
        .lam (.app (.app rtypeR (.bvar 0)) .boolFalse) <|
          .lam (.sort (.succ .zero)) <|
            .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 0))
    (hp : env.HasType 0 [] p (.sort .zero))
    (hHL : env.HasType 0 [] H (.app (.app rtypeL p) .boolFalse))
    (hHR : env.HasType 0 [] H (.app (.app rtypeR p) .boolFalse))
    (hα : env.HasType 0 [] α (.sort (.succ .zero)))
    (ht : env.HasType 0 [] t α) (he : env.HasType 0 [] e α) :
    env.IsDefEqU 0 []
      (.app (.app (.app (.app (.app (.app rite p) .boolFalse) H) α) t) e) e :=
  VEnv.reflectionITE_select wf false hrtypeLClosed hrtypeRClosed
    hriteClosed heq hp hHL hHR hα ht he

/-- The checked true equation for `Reflection.ite`, specialized to its
target-calculus shape, selects the first Boolean branch. -/
theorem VEnv.reflectionITE_true
    {env : VEnv} (wf : env.WF) {rtypeL rtypeR rite p H : VExpr}
    (hrtypeLClosed : rtypeL.ClosedN) (hrtypeRClosed : rtypeR.ClosedN)
    (hriteClosed : rite.ClosedN)
    (heq : env.IsDefEqU 0 []
      (.lam (.sort .zero) <|
        .lam (.app (.app rtypeL (.bvar 0)) .boolTrue) <|
          .app (.app (.app rite (.bvar 1)) .boolTrue) (.bvar 0))
      (.lam (.sort .zero) <|
        .lam (.app (.app rtypeR (.bvar 0)) .boolTrue) <|
          .lam (.sort (.succ .zero)) <|
            .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 1))
    (hp : env.HasType 0 [] p (.sort .zero))
    (hHL : env.HasType 0 [] H (.app (.app rtypeL p) .boolTrue))
    (hHR : env.HasType 0 [] H (.app (.app rtypeR p) .boolTrue))
    (hbool : env.HasType 0 [] .bool (.sort (.succ .zero)))
    (htrue : env.HasType 0 [] .boolTrue .bool)
    (hfalse : env.HasType 0 [] .boolFalse .bool) :
    env.IsDefEqU 0 []
      (.app (.app (.app
        (.app (.app (.app rite p) .boolTrue) H) .bool) .boolTrue) .boolFalse)
      .boolTrue :=
  VEnv.reflectionITE_true_select wf hrtypeLClosed hrtypeRClosed
    hriteClosed heq hp hHL hHR hbool htrue hfalse

/-- The false counterpart of `reflectionITE_true`. -/
theorem VEnv.reflectionITE_false
    {env : VEnv} (wf : env.WF) {rtypeL rtypeR rite p H : VExpr}
    (hrtypeLClosed : rtypeL.ClosedN) (hrtypeRClosed : rtypeR.ClosedN)
    (hriteClosed : rite.ClosedN)
    (heq : env.IsDefEqU 0 []
      (.lam (.sort .zero) <|
        .lam (.app (.app rtypeL (.bvar 0)) .boolFalse) <|
          .app (.app (.app rite (.bvar 1)) .boolFalse) (.bvar 0))
      (.lam (.sort .zero) <|
        .lam (.app (.app rtypeR (.bvar 0)) .boolFalse) <|
          .lam (.sort (.succ .zero)) <|
            .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 0))
    (hp : env.HasType 0 [] p (.sort .zero))
    (hHL : env.HasType 0 [] H (.app (.app rtypeL p) .boolFalse))
    (hHR : env.HasType 0 [] H (.app (.app rtypeR p) .boolFalse))
    (hbool : env.HasType 0 [] .bool (.sort (.succ .zero)))
    (htrue : env.HasType 0 [] .boolTrue .bool)
    (hfalse : env.HasType 0 [] .boolFalse .bool) :
    env.IsDefEqU 0 []
      (.app (.app (.app
        (.app (.app (.app rite p) .boolFalse) H) .bool) .boolTrue) .boolFalse)
      .boolFalse :=
  VEnv.reflectionITE_false_select wf hrtypeLClosed hrtypeRClosed
    hriteClosed heq hp hHL hHR hbool htrue hfalse


private theorem reflectionITE_translation_shape
    {env : VEnv} {r : Reflection} {bn : Name} {l : VExpr}
    (h : TrExprS env [] []
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) (.const bn [])) <|
        mkApp3 r.ite (.bvar 1) (.const bn []) (.bvar 0)) l) :
    ∃ rtype rite, l =
      (.lam (.sort .zero) <|
        .lam (.app (.app rtype (.bvar 0)) (.const bn [])) <|
          .app (.app (.app rite (.bvar 1)) (.const bn [])) (.bvar 0)) ∧
      TrExprS env [] [(none, .vlam (.sort .zero))] r.type rtype ∧
      TrExprS env []
        [(none, .vlam (.app (.app rtype (.bvar 0)) (.const bn []))),
          (none, .vlam (.sort .zero))] r.ite rite := by
  cases h with
  | lam _ hpropS hbody =>
    cases hpropS with
    | sort hlevel =>
      simp [VLevel.ofLevel] at hlevel
      subst hlevel
      cases hbody with
      | lam _ hHTyS hbody =>
        cases hHTyS with
        | app _ _ hHFnS hcondTyS =>
          cases hHFnS with
          | app _ _ hrtypeTyS hpTyS =>
            cases hpTyS with
            | bvar hpTy =>
              simp [VLCtx.find?, VLCtx.next] at hpTy
              rcases hpTy with ⟨rfl, rfl⟩
              cases hcondTyS with
              | const _ hus _ =>
                simp at hus
                subst hus
                cases hbody with
                | app _ _ hfn harg =>
                  cases hfn with
                  | app _ _ hfn hcond =>
                    cases hfn with
                    | app _ _ hite hp =>
                      cases hp with
                      | bvar hp =>
                        simp [VLCtx.find?, VLCtx.next] at hp
                        rcases hp with ⟨rfl, rfl⟩
                        cases harg with
                        | bvar harg =>
                          simp [VLCtx.find?, VLCtx.next] at harg
                          rcases harg with ⟨rfl, rfl⟩
                          cases hcond with
                          | const _ hus _ =>
                            simp at hus
                            subst hus
                            exact ⟨_, _, rfl, hrtypeTyS, hite⟩

private theorem reflectionITE_rhs_translation_shape
    {env : VEnv} {r : Reflection} {bn : Name} {j : Nat} {rr : VExpr}
    (hj : j = 1 ∨ j = 0)
    (h : TrExprS env [] []
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) (.const bn [])) <|
        .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar j) rr) :
    ∃ rtype, rr =
      (.lam (.sort .zero) <|
        .lam (.app (.app rtype (.bvar 0)) (.const bn [])) <|
          .lam (.sort (.succ .zero)) <|
            .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar j) ∧
      TrExprS env [] [(none, .vlam (.sort .zero))] r.type rtype := by
  cases h with
  | lam _ hpropS hbody =>
    cases hpropS with
    | sort hlevel =>
      simp [VLevel.ofLevel] at hlevel
      subst hlevel
      cases hbody with
      | lam _ hHTyS hbody =>
        cases hHTyS with
        | app _ _ hHFnS hcondTyS =>
          cases hHFnS with
          | app _ _ hrtypeTyS hpTyS =>
            cases hpTyS with
            | bvar hpTy =>
              simp [VLCtx.find?, VLCtx.next] at hpTy
              rcases hpTy with ⟨rfl, rfl⟩
              cases hcondTyS with
              | const _ hus _ =>
                simp at hus
                subst hus
                cases hbody with
                | lam _ htypeS hbody =>
                  cases htypeS with
                  | sort hlevel =>
                    simp [VLevel.ofLevel] at hlevel
                    subst hlevel
                    cases hbody with
                    | lam _ htTyS hbody =>
                      cases htTyS with
                      | bvar htTy =>
                        simp [VLCtx.find?, VLCtx.next] at htTy
                        rcases htTy with ⟨rfl, rfl⟩
                        cases hbody with
                        | lam _ heTyS hbody =>
                          cases heTyS with
                          | bvar heTy =>
                            simp [VLCtx.find?, VLCtx.next] at heTy
                            rcases heTy with ⟨rfl, rfl⟩
                            cases hbody with
                            | bvar hresult =>
                              obtain rfl | rfl := hj <;>
                              · simp [VLCtx.find?, VLCtx.next] at hresult
                                rcases hresult with ⟨rfl, rfl⟩
                                exact ⟨_, rfl, hrtypeTyS⟩

/-- The target-level equations retained from a successful
`Reflection.checkITE`.  Independent translations of `Reflection.type` and
`Reflection.ite` are kept explicit; later semantic use relates them through
translation uniqueness. -/
def VEnv.ReflectionITECertificate (env : VEnv)
    (r : Reflection := Reflection.defn₂) : Prop :=
  TrExprS.IsUnique r.type ∧
  TrExprS.IsUnique r.ite ∧
  ∃ trueRTypeL trueITE trueRTypeR,
    env.IsDefEqU 0 []
      (.lam (.sort .zero) <|
        .lam (.app (.app trueRTypeL (.bvar 0)) .boolTrue) <|
          .app (.app (.app trueITE (.bvar 1)) .boolTrue) (.bvar 0))
      (.lam (.sort .zero) <|
        .lam (.app (.app trueRTypeR (.bvar 0)) .boolTrue) <|
          .lam (.sort (.succ .zero)) <|
            .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 1) ∧
    TrExprS env [] [(none, .vlam (.sort .zero))]
      r.type trueRTypeL ∧
    TrExprS env []
      [(none, .vlam (.app (.app trueRTypeL (.bvar 0)) .boolTrue)),
        (none, .vlam (.sort .zero))]
      r.ite trueITE ∧
    TrExprS env [] [(none, .vlam (.sort .zero))]
      r.type trueRTypeR ∧
  ∃ falseRTypeL falseITE falseRTypeR,
    env.IsDefEqU 0 []
      (.lam (.sort .zero) <|
        .lam (.app (.app falseRTypeL (.bvar 0)) .boolFalse) <|
          .app (.app (.app falseITE (.bvar 1)) .boolFalse) (.bvar 0))
      (.lam (.sort .zero) <|
        .lam (.app (.app falseRTypeR (.bvar 0)) .boolFalse) <|
          .lam (.sort (.succ .zero)) <|
            .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 0) ∧
    TrExprS env [] [(none, .vlam (.sort .zero))]
      r.type falseRTypeL ∧
    TrExprS env []
      [(none, .vlam (.app (.app falseRTypeL (.bvar 0)) .boolFalse)),
        (none, .vlam (.sort .zero))]
      r.ite falseITE ∧
    TrExprS env [] [(none, .vlam (.sort .zero))]
      r.type falseRTypeR

/-- Normalize the source translations accompanying `Reflection.checkITE.WF`
to the target lambda shapes consumed by the selector lemmas above. -/
theorem VEnv.ReflectionITECertificate.of_checked
    {env : VEnv} {r : Reflection} {tl tr fl fr : VExpr}
    (hrtypeUnique : TrExprS.IsUnique r.type)
    (hiteUnique : TrExprS.IsUnique r.ite)
    (htl : TrExprS env [] []
      (.lam0 q(Prop) <| .lam0
        (mkApp2 r.type (.bvar 0) q(true)) <|
        mkApp3 r.ite (.bvar 1) q(true) (.bvar 0)) tl)
    (htr : TrExprS env [] []
      (.lam0 q(Prop) <| .lam0
        (mkApp2 r.type (.bvar 0) q(true)) <|
        .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 1) tr)
    (hteq : env.IsDefEqU 0 [] tl tr)
    (hfl : TrExprS env [] []
      (.lam0 q(Prop) <| .lam0
        (mkApp2 r.type (.bvar 0) q(false)) <|
        mkApp3 r.ite (.bvar 1) q(false) (.bvar 0)) fl)
    (hfr : TrExprS env [] []
      (.lam0 q(Prop) <| .lam0
        (mkApp2 r.type (.bvar 0) q(false)) <|
        .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 0) fr)
    (hfeq : env.IsDefEqU 0 [] fl fr) :
    Lean4Lean.Environment.VEnv.ReflectionITECertificate env r := by
  obtain ⟨trueRTypeL, trueITE, rfl, htrueRTypeL, htrueITE⟩ :=
    reflectionITE_translation_shape htl
  obtain ⟨trueRTypeR, rfl, htrueRTypeR⟩ :=
    reflectionITE_rhs_translation_shape (.inl rfl) htr
  obtain ⟨falseRTypeL, falseITE, rfl, hfalseRTypeL, hfalseITE⟩ :=
    reflectionITE_translation_shape hfl
  obtain ⟨falseRTypeR, rfl, hfalseRTypeR⟩ :=
    reflectionITE_rhs_translation_shape (.inr rfl) hfr
  exact ⟨hrtypeUnique, hiteUnique,
    trueRTypeL, trueITE, trueRTypeR, hteq,
    htrueRTypeL, htrueITE, htrueRTypeR,
    falseRTypeL, falseITE, falseRTypeR, hfeq,
    hfalseRTypeL, hfalseITE, hfalseRTypeR⟩

/-- Rewrite both checked selector equations to chosen global translations of
`Reflection.type` and `Reflection.ite`.  The retained contextual translation
facts and closed-source uniqueness justify the rewrite. -/
theorem VEnv.ReflectionITECertificate.canonical
    {env : VEnv} (wf : env.WF)
    (hcert : Lean4Lean.Environment.VEnv.ReflectionITECertificate env r)
    {rtype rite : VExpr}
    (hrtype : TrExprS env [] [] r.type rtype)
    (hrite : TrExprS env [] [] r.ite rite) :
    env.IsDefEqU 0 []
      (.lam (.sort .zero) <|
        .lam (.app (.app rtype (.bvar 0)) .boolTrue) <|
          .app (.app (.app rite (.bvar 1)) .boolTrue) (.bvar 0))
      (.lam (.sort .zero) <|
        .lam (.app (.app rtype (.bvar 0)) .boolTrue) <|
          .lam (.sort (.succ .zero)) <|
            .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 1) ∧
    env.IsDefEqU 0 []
      (.lam (.sort .zero) <|
        .lam (.app (.app rtype (.bvar 0)) .boolFalse) <|
          .app (.app (.app rite (.bvar 1)) .boolFalse) (.bvar 0))
      (.lam (.sort .zero) <|
        .lam (.app (.app rtype (.bvar 0)) .boolFalse) <|
          .lam (.sort (.succ .zero)) <|
            .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 0) := by
  rcases hcert with
    ⟨hrtypeUnique, hriteUnique,
      trueRTypeL, trueITE, trueRTypeR, htrueEq,
      htrueRTypeLS, htrueITES, htrueRTypeRS,
      falseRTypeL, falseITE, falseRTypeR, hfalseEq,
    hfalseRTypeLS, hfalseITES, hfalseRTypeRS⟩

  have hrtypeClosed : r.type.looseBVarRange' = 0 := by
    exact hrtype.closed.looseBVarRange_zero
  have hriteClosed : r.ite.looseBVarRange' = 0 := by
    exact hrite.closed.looseBVarRange_zero
  have htrueRTypeL : trueRTypeL = rtype :=
    TrExprS.unique_closed_weak wf hrtypeUnique hrtypeClosed hrtype
      htrueRTypeLS (.skip (.vlam (.sort .zero)) .refl)
  have htrueRTypeR : trueRTypeR = rtype :=
    TrExprS.unique_closed_weak wf hrtypeUnique hrtypeClosed hrtype
      htrueRTypeRS (.skip (.vlam (.sort .zero)) .refl)
  have htrueITE : trueITE = rite :=
    TrExprS.unique_closed_weak wf hriteUnique hriteClosed hrite
      htrueITES
      (.skip (.vlam (.app (.app trueRTypeL (.bvar 0)) .boolTrue))
        (.skip (.vlam (.sort .zero)) .refl))
  have hfalseRTypeL : falseRTypeL = rtype :=
    TrExprS.unique_closed_weak wf hrtypeUnique hrtypeClosed hrtype
      hfalseRTypeLS (.skip (.vlam (.sort .zero)) .refl)
  have hfalseRTypeR : falseRTypeR = rtype :=
    TrExprS.unique_closed_weak wf hrtypeUnique hrtypeClosed hrtype
      hfalseRTypeRS (.skip (.vlam (.sort .zero)) .refl)
  have hfalseITE : falseITE = rite :=
    TrExprS.unique_closed_weak wf hriteUnique hriteClosed hrite
      hfalseITES
      (.skip (.vlam (.app (.app falseRTypeL (.bvar 0)) .boolFalse))
        (.skip (.vlam (.sort .zero)) .refl))
  subst trueRTypeL
  subst trueRTypeR
  subst trueITE
  subst falseRTypeL
  subst falseRTypeR
  subst falseITE
  exact ⟨htrueEq, hfalseEq⟩

theorem VEnv.ReflectionITEChecked.toCertificate
    {env : VEnv} {r : Reflection}
    (h : Lean4Lean.Environment.VEnv.ReflectionITEChecked env r)
    (hrtypeUnique : TrExprS.IsUnique r.type)
    (hiteUnique : TrExprS.IsUnique r.ite) :
    VEnv.ReflectionITECertificate env r := by
  rcases h with ⟨tl, tr, fl, fr, htl, htr, hteq, hfl, hfr, hfeq⟩
  exact VEnv.ReflectionITECertificate.of_checked hrtypeUnique hiteUnique
    htl htr hteq hfl hfr hfeq

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
/-- The checked dependent selector equation for the Boolean literal `b`
specializes a well-typed call to the branch named by `b`, recovering the
generated dependent proof argument existentially; callers need not provide
the type transport for the reflection witness separately. -/
private theorem VEnv.reflectionNatDITE_select_from_call
    {env : VEnv} (wf : env.WF) (b : Bool)
    {rtype rdite ofSel p H t e R : VExpr}
    (hrtypeClosed : rtype.ClosedN) (hrditeClosed : rdite.ClosedN)
    (hofSelClosed : ofSel.ClosedN)
    (heq : env.IsDefEqU 0 []
      (.lam (.sort .zero) <|
       .lam (.forallE (.bvar 0) .nat) <|
       .lam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat) <|
       .lam (.app (.app rtype (.bvar 2)) (.boolLit b)) <|
       .app (.app (.app (.app (.app rdite (.bvar 3)) (.boolLit b))
         (.bvar 0)) (.bvar 2)) (.bvar 1))
      (.lam (.sort .zero) <|
       .lam (.forallE (.bvar 0) .nat) <|
       .lam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat) <|
       .lam (.app (.app rtype (.bvar 2)) (.boolLit b)) <|
       .app (.bvar (bif b then 2 else 1))
         (.app (.app ofSel (.bvar 3)) (.bvar 0))))
    (hcallT : env.HasType 0 []
      (.app (.app (.app (.app (.app rdite p) (.boolLit b)) H) t) e) R)
    (hp : env.HasType 0 [] p (.sort .zero))
    (ht : env.HasType 0 [] t (.forallE p .nat))
    (he : env.HasType 0 [] e
      (.forallE (.app (.const ``Not []) p) .nat)) :
    ∃ proof, env.IsDefEqU 0 []
      (.app (.app (.app (.app (.app rdite p) (.boolLit b)) H) t) e)
      (.app (bif b then t else e) proof) := by
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
  simp [VExpr.inst, VExpr.boolLit_instN, hrtypeClosed.instN_eq,
    hrditeClosed.instN_eq, hofSelClosed.instN_eq, hpClosed.lift_eq] at h₁
  have h₁' := h₁
  obtain ⟨_, hd₁⟩ := h₁'
  obtain ⟨⟨_, htSort⟩, _, hleftTBody⟩ :=
    hd₁.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightTBody⟩ := hd₁.hasType.2.lam_inv wf trivial
  have h₂ := VEnv.IsDefEqU.lam_instU wf trivial h₁ htSort
    hleftTBody hrightTBody ht
  simp [VExpr.inst, VExpr.boolLit_instN, hrtypeClosed.instN_eq,
    hrditeClosed.instN_eq, hofSelClosed.instN_eq, hpClosed.instN_eq] at h₂
  have h₂' := h₂
  obtain ⟨_, hd₂⟩ := h₂'
  obtain ⟨⟨_, heSort⟩, _, hleftEBody⟩ :=
    hd₂.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightEBody⟩ := hd₂.hasType.2.lam_inv wf trivial
  have h₃ := VEnv.IsDefEqU.lam_instU wf trivial h₂ heSort
    hleftEBody hrightEBody he
  simp [VExpr.inst, VExpr.boolLit_instN, hrtypeClosed.instN_eq,
    hrditeClosed.instN_eq, hofSelClosed.instN_eq, hpClosed.instN_eq] at h₃
  have h₃' := h₃
  obtain ⟨_, hd₃⟩ := h₃'
  obtain ⟨hproofTyLType, _, hbodyLT⟩ :=
    hd₃.hasType.1.lam_inv wf trivial
  have hΓ : OnCtx [(.app (.app rtype p) (.boolLit b))]
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
      [(.app (.app rtype p) (.boolLit b))]
      (.app (.app rdite p) (.boolLit b))
      (.app (.app rdite p) (.boolLit b)) :=
    .refl ⟨_, hprefixLocalT⟩
  obtain ⟨_, hinst⟩ := VEnv.instantiate_dependent_proof_lam wf
    (prefixArgTy := prefixArgTy) (prefixBodyTy := prefixBodyTy)
    (hpTy := hpTy) (hpBodyTy := hpBodyTy)
    hprefixLocalT hproofVarT hprefixCallT hpT hprefixEq h₃
  refine ⟨.app (.app ofSel p) H, ?_⟩
  cases b <;>
    simpa [VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.liftN, liftVar,
      hrditeClosed.instN_eq, hofSelClosed.instN_eq,
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
    VEnv.reflectionNatDITE_select_from_call wf true
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
    VEnv.reflectionNatDITE_select_from_call wf false
      hrtypeClosed hrditeClosed hofFalseClosed heq hcallFalseT hp ht he
  exact ⟨proof, hreplace.trans wf trivial hselect⟩


private theorem reflectionNatDITE_lhs_shape
    {env : VEnv} {r : Reflection} {bn : Name} {l : VExpr}
    (h : TrExprS env [] []
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) (.const bn [])) <|
       mkApp5 r.natDITE (.bvar 3) (.const bn []) (.bvar 0)
         (.bvar 2) (.bvar 1)) l) :
    ∃ rtype rdite, l =
      (.lam (.sort .zero) <|
       .lam (.forallE (.bvar 0) .nat) <|
       .lam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat) <|
       .lam (.app (.app rtype (.bvar 2)) (.const bn [])) <|
       .app (.app (.app (.app (.app rdite (.bvar 3)) (.const bn []))
         (.bvar 0)) (.bvar 2)) (.bvar 1)) ∧
      TrExprS env []
        [(none, .vlam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat)),
          (none, .vlam (.forallE (.bvar 0) .nat)),
          (none, .vlam (.sort .zero))]
        r.type rtype ∧
      TrExprS env []
        [(none, .vlam (.app (.app rtype (.bvar 2)) (.const bn []))),
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
                            | app _ _ hHFnS hcondS =>
                              cases hHFnS with
                              | app _ _ hrtypeS hpS =>
                                cases hpS with
                                | bvar hp =>
                                  simp [VLCtx.find?, VLCtx.next] at hp
                                  rcases hp with ⟨rfl, rfl⟩
                                  cases hcondS with
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
                                          | app _ _ hfn hcondS =>
                                            cases hfn with
                                            | app _ _ hditeS hpS =>
                                              cases heS with
                                              | bvar heS =>
                                                cases htS with
                                                | bvar htS =>
                                                  cases hHS with
                                                  | bvar hHS =>
                                                    cases hcondS with
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

private theorem reflectionNatDITE_rhs_shape
    {env : VEnv} {r : Reflection} {bn : Name} {j : Nat} {ofSel : Expr}
    {rr : VExpr}
    (hj : j = 2 ∨ j = 1)
    (h : TrExprS env [] []
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) (.const bn [])) <|
       mkApp (.bvar j) (mkApp2 ofSel (.bvar 3) (.bvar 0))) rr) :
    ∃ rtype ofSelV, rr =
      (.lam (.sort .zero) <|
       .lam (.forallE (.bvar 0) .nat) <|
       .lam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat) <|
       .lam (.app (.app rtype (.bvar 2)) (.const bn [])) <|
       .app (.bvar j) (.app (.app ofSelV (.bvar 3)) (.bvar 0))) ∧
      TrExprS env []
        [(none, .vlam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat)),
          (none, .vlam (.forallE (.bvar 0) .nat)),
          (none, .vlam (.sort .zero))]
        r.type rtype ∧
      TrExprS env []
        [(none, .vlam (.app (.app rtype (.bvar 2)) (.const bn []))),
          (none, .vlam (.forallE (.app (.const ``Not []) (.bvar 1)) .nat)),
          (none, .vlam (.forallE (.bvar 0) .nat)),
          (none, .vlam (.sort .zero))]
        ofSel ofSelV := by
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
                            | app _ _ hHFnS hcondS =>
                              cases hHFnS with
                              | app _ _ hrtypeS hpS =>
                                cases hpS with
                                | bvar hp =>
                                  simp [VLCtx.find?, VLCtx.next] at hp
                                  rcases hp with ⟨rfl, rfl⟩
                                  cases hcondS with
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
                                          | app _ _ hofSelS hpS =>
                                            cases hpS with
                                            | bvar hpS =>
                                              cases hHS with
                                              | bvar hHS =>
                                                obtain rfl | rfl := hj <;>
                                                · simp [VLCtx.find?, VLCtx.next] at htS hpS hHS
                                                  rcases htS with ⟨rfl, rfl⟩
                                                  rcases hpS with ⟨rfl, rfl⟩
                                                  rcases hHS with ⟨rfl, rfl⟩
                                                  exact ⟨_, _, rfl, hrtypeS, hofSelS⟩

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
    reflectionNatDITE_lhs_shape htrueLS
  obtain ⟨trueRTypeR, trueOfTrue, rfl, htrueRTypeRS, htrueOfTrueS⟩ :=
    reflectionNatDITE_rhs_shape (.inl rfl) htrueRS
  obtain ⟨falseRTypeL, falseDITE, rfl, hfalseRTypeLS, hfalseDITES⟩ :=
    reflectionNatDITE_lhs_shape hfalseLS
  obtain ⟨falseRTypeR, falseOfFalse, rfl, hfalseRTypeRS, hfalseOfFalseS⟩ :=
    reflectionNatDITE_rhs_shape (.inr rfl) hfalseRS
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

end Lean4Lean.Environment
