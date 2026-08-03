import Lean4Lean.Verify.ModDivCondition

namespace Lean4Lean.Environment
open Lean VEnv

private theorem translated_closed
    {env : VEnv} (wf : env.WF) {e : Expr} {eV : VExpr}
    (h : TrExprS env [] [] e eV) : eV.ClosedN := by
  obtain ⟨_, heWF⟩ := h.wf wf.ordered (Us := []) (Δ := []) trivial
  exact (heWF.hasType.1.closedN' wf.ordered.closed trivial).1

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

def natDivTopPropInst (b : Nat) : Expr :=
  mkApp2 q(@LE.le Nat _) q(Nat.succ Nat.zero) (.natLitToConstructor b)

def natDivTopBleInst (b : Nat) : Expr :=
  mkApp2 q(Nat.ble) q(Nat.succ Nat.zero) (.natLitToConstructor b)

def natDivTopProofInst (b : Nat) : Expr :=
  match Condition.natLE.impl with
  | .reflectNatNat _ _ proof =>
    mkAppN proof #[q(Nat.succ Nat.zero), .natLitToConstructor b]
  | .bool => q(False.elim)

def natDivTopThenInst (a b : Nat) : Expr :=
  let x := (Expr.natLitToConstructor a).liftLooseBVars 0 1
  let y := (Expr.natLitToConstructor b).liftLooseBVars 0 1
  .lam0 (natDivTopPropInst b) <|
    mkApp5 q(Nat.div.go) y (.bvar 0) (mkApp q(Nat.succ) x) x
      (mkApp q(Nat.lt_succ_self) x)

def natDivTopElseInst (b : Nat) : Expr :=
  .lam0 (mkApp q(Not) (natDivTopPropInst b)) q(Nat.zero)

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
        (natDivTopRhs (.natLitToConstructor a)
          (.natLitToConstructor b)) rhs ∧
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
          (natDivTopRhs (.natLitToConstructor a)
            (.natLitToConstructor b)) r₂ := by
        rw [← natDivTopRhsInst_eq]
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

/-- Normalize a translated top-level division RHS to the canonical checked
dependent selector, then select the branch determined by `0 < b`. -/
theorem VEnv.select_natDivTop_rhs
    {env : VEnv} (wf : env.WF) (hprim : env.HasPrimitives)
    (hctors : VEnv.HasNatBoolConstructors env)
    (hbleC : env.contains ``Nat.ble)
    (cert : VEnv.NatLESelectorCertificate env)
    (a b : Nat) {rhs : VExpr}
    (hrhs : TrExprS env [] []
      (natDivTopRhs (.natLitToConstructor a)
        (.natLitToConstructor b)) rhs) :
    ∃ pV bleV HV tV eV,
      TrExprS env [] [] (natDivTopPropInst b) pV ∧
      TrExprS env [] [] (natDivTopBleInst b) bleV ∧
      TrExprS env [] [] (natDivTopProofInst b) HV ∧
      TrExprS env [] [] (natDivTopThenInst a b) tV ∧
      TrExprS env [] [] (natDivTopElseInst b) eV ∧
      if 0 < b then
        ∃ proof, env.IsDefEqU 0 [] rhs (.app tV proof)
      else
        ∃ proof, env.IsDefEqU 0 [] rhs (.app eV proof) := by
  simp only [natDivTopRhs, Condition.reflectedDITE, Condition.natLE,
    Reflection.natDITE, mkApp5, mkApp3, mkApp2, mkApp, mkAppB] at hrhs
  cases hrhs with
  | app h₄T heT h₄ heS =>
    rename_i A₄ B₄ eV
    cases h₄ with
    | app h₃T htT h₃ htS =>
      rename_i A₃ B₃ tV
      cases h₃ with
      | app h₂T hHT h₂ hHS =>
        rename_i A₂ B₂ HV
        cases h₂ with
        | app h₁T hbleT h₁ hbleS =>
          rename_i A₁ B₁ bleV
          cases h₁ with
          | app hditeT hpT hditeS hpS =>
            rename_i diteV A₀ B₀ pV
            have hctx : VLCtx.IsDefEq env 0 [] [] := .refl wf trivial
            have hditeEq := TrExprS.uniq (Us := []) wf hctx
              hditeS cert.rditeS
            have h₁Eq := hditeEq.app_same wf trivial hditeT hpT
            have h₂Eq := h₁Eq.app_same wf trivial h₁T hbleT
            have h₃Eq := h₂Eq.app_same wf trivial h₂T hHT
            have h₄Eq := h₃Eq.app_same wf trivial h₃T htT
            have hcallEq := h₄Eq.app_same wf trivial h₄T heT
            have hcallT := (hcallEq.of_l wf trivial
              (.app h₄T heT)).hasType.2
            have hpS' : TrExprS env [] [] (natDivTopPropInst b) pV := by
              simpa [natDivTopPropInst, Lean.mkAppN] using hpS
            have hbleS' : TrExprS env [] [] (natDivTopBleInst b) bleV := by
              simpa [natDivTopBleInst, Lean.mkAppN] using hbleS
            have hHS' : TrExprS env [] [] (natDivTopProofInst b) HV := by
              simpa [natDivTopProofInst, Condition.natLE, Lean.mkAppN] using hHS
            have htS' : TrExprS env [] [] (natDivTopThenInst a b) tV := by
              simpa only [natDivTopThenInst,
                natDivTopPropInst, Expr.lam0, Expr.liftLooseBVars_eq,
                Lean.mkAppN, mkApp5, mkApp4, mkApp2, mkApp]
                using htS
            have heS' : TrExprS env [] [] (natDivTopElseInst b) eV := by
              simpa [natDivTopElseInst, natDivTopPropInst,
                Expr.lam0, Lean.mkAppN] using heS
            refine ⟨pV, bleV, HV, tV, eV,
              hpS', hbleS', hHS', htS', heS', ?_⟩
            have honeS : TrExprS env [] [] q(Nat.succ Nat.zero)
                (.natLit 1) := by
              simpa [VExpr.natLit] using
                (TrExprS.app
                  (hctors.natSuccS (Us := []) (Δ := [])).2
                  (hctors.natZeroS (Us := []) (Δ := [])).2
                  (hctors.natSuccS (Us := []) (Δ := [])).1
                  (hctors.natZeroS (Us := []) (Δ := [])).1)
            have hbCtorS : TrExprS env [] []
                (.natLitToConstructor b) (.natLit b) := by
              have hbLit := hctors.natLitS b (Us := []) (Δ := [])
              cases hbLit.1 with
              | lit _ hbS => simpa [Literal.toConstructor] using hbS
            have hbool := Condition.natBLE_application_eval_of_args
              wf hprim hctors hbleC honeS hbCtorS
              (by simpa [natDivTopBleInst, Lean.mkAppN] using hbleS')
            have heqs := cert.dite_equations wf
            split
            · rename_i hb
              have hble : Nat.ble 1 b = true :=
                Nat.ble_eq_true_of_le hb
              rw [hble] at hbool
              obtain ⟨proof, hselect⟩ :=
                VEnv.reflectionNatDITE_true_of_condition wf
                  (translated_closed wf cert.rtypeS)
                  (translated_closed wf cert.rditeS)
                  (translated_closed wf cert.ofTrueS)
                  heqs.1 cert.rditeHas hcallT hbool
              exact ⟨proof, hcallEq.trans wf trivial hselect⟩
            · rename_i hb
              have hnle : ¬1 ≤ b := by omega
              have hble : Nat.ble 1 b = false := by
                cases h : Nat.ble 1 b <;> simp_all [Nat.ble_eq]
              rw [hble] at hbool
              obtain ⟨proof, hselect⟩ :=
                VEnv.reflectionNatDITE_false_of_condition wf
                  (translated_closed wf cert.rtypeS)
                  (translated_closed wf cert.rditeS)
                  (translated_closed wf cert.ofFalseS)
                  heqs.2 cert.rditeHas hcallT hbool
              exact ⟨proof, hcallEq.trans wf trivial hselect⟩

/-- Beta-reduce the false top-level division branch to zero. -/
theorem VEnv.natDivTopElse_beta
    {env : VEnv} (wf : env.WF) (b : Nat)
    {eV proof R : VExpr}
    (heS : TrExprS env [] [] (natDivTopElseInst b) eV)
    (happT : env.HasType 0 [] (.app eV proof) R) :
    env.IsDefEqU 0 [] (.app eV proof) .natZero := by
  have heSLam := heS
  simp only [natDivTopElseInst] at heSLam
  have heSLam' : TrExprS env [] []
      (.lam `_ (mkApp q(Not) (natDivTopPropInst b)) q(Nat.zero) .default)
      eV := by
    simpa only [Expr.lam0] using heSLam
  cases heSLam' with
  | lam hdomType hdomS hbodyS =>
    rename_i tyV bodyV
    have hlamS : TrExprS env [] []
        (.lam `_ (mkApp q(Not) (natDivTopPropInst b)) q(Nat.zero) .default)
        (.lam tyV bodyV) := .lam hdomType hdomS hbodyS
    obtain ⟨bodyTy, hlamCanonT⟩ := TrExprS.closedLam_hasType wf hlamS
    obtain ⟨_, _, hlamT, hproofT⟩ := happT.app_inv wf.ordered trivial
    have hlamTyEq := hlamT.uniqU wf trivial hlamCanonT
    obtain ⟨_, hdomEq⟩ := (hlamTyEq.forallE_inv wf trivial).1
    have hproofT' := hproofT.defeqU_r wf trivial hdomEq.toU
    obtain ⟨_, hbodyWF⟩ := hbodyS.wf wf.ordered
      (Us := []) (Δ := [(none, .vlam _)])
      ⟨trivial, nofun, hdomType⟩
    cases hbodyS with
    | const hzero hus hlen =>
      simp at hus
      subst hus
      exact ⟨_, by simpa [VExpr.inst] using
        (VEnv.IsDefEq.beta hbodyWF.hasType.1 hproofT')⟩

end Lean4Lean.Environment
