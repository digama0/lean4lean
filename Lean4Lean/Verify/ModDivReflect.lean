import Lean4Lean.Verify.ModDivCondition

namespace Lean4Lean.Environment
open Lean VEnv

private theorem translated_closed
    {env : VEnv} (wf : env.WF) {e : Expr} {eV : VExpr}
    (h : TrExprS env [] [] e eV) : eV.ClosedN := by
  obtain ⟨_, heWF⟩ := h.wf wf.ordered (Us := []) (Δ := []) trivial
  exact (heWF.hasType.1.closedN' wf.ordered.closed trivial).1

private theorem natLitToConstructor_closed (n : Nat) :
    (Expr.natLitToConstructor n).looseBVarRange' = 0 := by
  cases n <;> simp [Expr.natLitToConstructor, Expr.natZero, Expr.natSucc,
    Expr.looseBVarRange']

private theorem translated_lifted_natConstructor
    {env : VEnv} (hctors : VEnv.HasNatBoolConstructors env)
    (n : Nat) (Δ : VLCtx) :
    TrExprS env [] Δ
      ((Expr.natLitToConstructor n).liftLooseBVars 0 1) (.natLit n) := by
  have hnLit := hctors.natLitS n (Us := []) (Δ := Δ)
  cases hnLit.1 with
  | lit _ hnS =>
    have hlift : (Expr.natLitToConstructor n).liftLooseBVars 0 1 =
        Expr.natLitToConstructor n := by
      rw [Expr.liftLooseBVars_eq]
      exact Expr.liftLooseBVars_eq_self (e := Expr.natLitToConstructor n)
        (s := 0) (d := 1) (by
        rw [natLitToConstructor_closed]
        omega)
    rw [hlift]
    simpa [Literal.toConstructor] using hnS

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

def natDivTopThenBodyInst (a b : Nat) : Expr :=
  let x := (Expr.natLitToConstructor a).liftLooseBVars 0 1
  let y := (Expr.natLitToConstructor b).liftLooseBVars 0 1
  mkApp5 q(Nat.div.go) y (.bvar 0) (mkApp q(Nat.succ) x) x
    (mkApp q(Nat.lt_succ_self) x)

def natDivTopThenInst (a b : Nat) : Expr :=
  .lam0 (natDivTopPropInst b) (natDivTopThenBodyInst a b)

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
                natDivTopThenBodyInst, natDivTopPropInst, Expr.lam0,
                Expr.liftLooseBVars_eq, Lean.mkAppN, mkApp5, mkApp4,
                mkApp2, mkApp, mkAppB]
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

/-- Expose and beta-reduce the selected true top-level division branch while
retaining the translated `Nat.div.go` body. -/
theorem VEnv.natDivTopThen_beta
    {env : VEnv} (wf : env.WF) (a b : Nat)
    {tV proof R : VExpr}
    (htS : TrExprS env [] [] (natDivTopThenInst a b) tV)
    (happT : env.HasType 0 [] (.app tV proof) R) :
    ∃ propV bodyV,
      tV = .lam propV bodyV ∧
      env.IsType 0 [] propV ∧
      TrExprS env [] [(none, .vlam propV)]
        (natDivTopThenBodyInst a b) bodyV ∧
      env.HasType 0 [] proof propV ∧
      env.IsDefEqU 0 [] (.app tV proof) (bodyV.inst proof) := by
  have htSLam : TrExprS env [] []
      (.lam `_ (natDivTopPropInst b) (natDivTopThenBodyInst a b) .default)
      tV := by
    simpa only [natDivTopThenInst, Expr.lam0] using htS
  cases htSLam with
  | lam hdomType hdomS hbodyS =>
    rename_i propV bodyV
    have hlamS : TrExprS env [] []
        (.lam `_ (natDivTopPropInst b) (natDivTopThenBodyInst a b) .default)
        (.lam propV bodyV) := .lam hdomType hdomS hbodyS
    obtain ⟨bodyTy, hlamCanonT⟩ := TrExprS.closedLam_hasType wf hlamS
    obtain ⟨_, _, hlamT, hproofT⟩ := happT.app_inv wf.ordered trivial
    have hlamTyEq := hlamT.uniqU wf trivial hlamCanonT
    obtain ⟨_, hdomEq⟩ := (hlamTyEq.forallE_inv wf trivial).1
    have hproofT' := hproofT.defeqU_r wf trivial hdomEq.toU
    obtain ⟨_, hbodyWF⟩ := hbodyS.wf wf.ordered
      (Us := []) (Δ := [(none, .vlam propV)])
      ⟨trivial, nofun, hdomType⟩
    exact ⟨propV, bodyV, rfl, hdomType, hbodyS, hproofT',
      ⟨_, VEnv.IsDefEq.beta hbodyWF.hasType.1 hproofT'⟩⟩

/-- Decompose the retained true-branch body into the six translations that
form its `Nat.div.go` call. -/
theorem VEnv.natDivTopThenBody_shape
    {env : VEnv} {propV bodyV : VExpr} (a b : Nat)
    (hbodyS : TrExprS env [] [(none, .vlam propV)]
      (natDivTopThenBodyInst a b) bodyV) :
    ∃ goV yV hyV fuelV xV hfuelV,
      bodyV = .app (.app (.app (.app (.app goV yV) hyV) fuelV) xV) hfuelV ∧
      TrExprS env [] [(none, .vlam propV)] q(Nat.div.go) goV ∧
      TrExprS env [] [(none, .vlam propV)]
        ((Expr.natLitToConstructor b).liftLooseBVars 0 1) yV ∧
      TrExprS env [] [(none, .vlam propV)] (.bvar 0) hyV ∧
      TrExprS env [] [(none, .vlam propV)]
        (mkApp q(Nat.succ)
          ((Expr.natLitToConstructor a).liftLooseBVars 0 1)) fuelV ∧
      TrExprS env [] [(none, .vlam propV)]
        ((Expr.natLitToConstructor a).liftLooseBVars 0 1) xV ∧
      TrExprS env [] [(none, .vlam propV)]
        (mkApp q(Nat.lt_succ_self)
          ((Expr.natLitToConstructor a).liftLooseBVars 0 1)) hfuelV := by
  simp only [natDivTopThenBodyInst, mkApp5, mkApp4, mkApp, mkAppB] at hbodyS
  cases hbodyS with
  | app h₄T hfuelT h₄ hfuelS =>
    rename_i A₄ B₄ hfuelV
    cases h₄ with
    | app h₃T hxT h₃ hxS =>
      rename_i A₃ B₃ xV
      cases h₃ with
      | app h₂T hfuelArgT h₂ hfuelArgS =>
        rename_i A₂ B₂ fuelV
        cases h₂ with
        | app h₁T hhyT h₁ hhyS =>
          rename_i A₁ B₁ hyV
          cases h₁ with
          | app hgoT hyT hgoS hyS =>
            rename_i goV A₀ B₀ yV
            exact ⟨goV, yV, hyV, fuelV, xV, hfuelV, rfl,
              hgoS, hyS, hhyS, hfuelArgS, hxS, hfuelS⟩

/-- Normalize the non-proof components of a retained true-branch body. -/
theorem VEnv.natDivTopThenBody_components
    {env : VEnv} (wf : env.WF)
    (hctors : VEnv.HasNatBoolConstructors env)
    {propV bodyV : VExpr} (hpropType : env.IsType 0 [] propV)
    (a b : Nat)
    (hbodyS : TrExprS env [] [(none, .vlam propV)]
      (natDivTopThenBodyInst a b) bodyV) :
    ∃ yV fuelV xV hfuelV,
      bodyV = .app (.app (.app (.app (.app (.const ``Nat.div.go []) yV)
        (.bvar 0)) fuelV) xV) hfuelV ∧
      env.IsDefEqU 0 [propV] yV (.natLit b) ∧
      env.IsDefEqU 0 [propV] fuelV (.natLit (a + 1)) ∧
      env.IsDefEqU 0 [propV] xV (.natLit a) := by
  obtain ⟨goV, yV, hyV, fuelV, xV, hfuelV, rfl,
    hgoS, hyS, hhyS, hfuelS, hxS, hlastS⟩ :=
    VEnv.natDivTopThenBody_shape a b hbodyS
  have hgoV : goV = .const ``Nat.div.go [] := by
    cases hgoS with
    | const _ hus _ =>
      simp at hus
      subst hus
      rfl
  subst goV
  have hhyV : hyV = .bvar 0 := by
    cases hhyS with
    | bvar hfind =>
      simp [VLCtx.find?, VLCtx.next] at hfind
      rcases hfind with ⟨rfl, rfl⟩
      rfl
  subst hyV
  have hctx : VLCtx.IsDefEq env 0
      [(none, .vlam propV)] [(none, .vlam propV)] :=
    .refl wf ⟨trivial, nofun, hpropType⟩
  have hyCanon := translated_lifted_natConstructor hctors b
    [(none, .vlam propV)]
  have hxCanon := translated_lifted_natConstructor hctors a
    [(none, .vlam propV)]
  have hsucc := hctors.natSuccS
    (Us := []) (Δ := [(none, .vlam propV)])
  have haT := (hctors.natLitS a
    (Us := []) (Δ := [(none, .vlam propV)])).2
  have hfuelCanon : TrExprS env [] [(none, .vlam propV)]
      (mkApp q(Nat.succ)
        ((Expr.natLitToConstructor a).liftLooseBVars 0 1))
      (.natLit (a + 1)) := by
    simpa [VExpr.natLit, Nat.add_comm] using
      (TrExprS.app hsucc.2 haT hsucc.1 hxCanon)
  exact ⟨yV, fuelV, xV, hfuelV, rfl,
    TrExprS.uniq (Us := []) wf hctx hyS hyCanon,
    TrExprS.uniq (Us := []) wf hctx hfuelS hfuelCanon,
    TrExprS.uniq (Us := []) wf hctx hxS hxCanon⟩

/-- Instantiate the normalized true-branch body, retaining its translated
fuel proof as the second proof argument of `VExpr.natDivGo`. -/
theorem VEnv.natDivTopThenBody_inst
    {env : VEnv} (wf : env.WF)
    (hctors : VEnv.HasNatBoolConstructors env)
    {propV bodyV proof : VExpr}
    (hpropType : env.IsType 0 [] propV)
    (hproofT : env.HasType 0 [] proof propV)
    (a b : Nat)
    (hbodyS : TrExprS env [] [(none, .vlam propV)]
      (natDivTopThenBodyInst a b) bodyV) :
    ∃ hfuel, env.IsDefEqU 0 [] (bodyV.inst proof)
      (.natDivGo b (a + 1) a proof hfuel) := by
  obtain ⟨yV, fuelV, xV, hfuelV, hbody,
    hyEq, hfuelEq, hxEq⟩ :=
    VEnv.natDivTopThenBody_components wf hctors hpropType a b hbodyS
  subst bodyV
  obtain ⟨_, hbodyWF⟩ := hbodyS.wf wf.ordered
    (Us := []) (Δ := [(none, .vlam propV)])
    ⟨trivial, nofun, hpropType⟩
  have hΓ : OnCtx [propV] (env.IsType 0) := ⟨trivial, hpropType⟩
  obtain ⟨_, _, h₄T, hlastT⟩ := hbodyWF.hasType.1.app_inv wf.ordered hΓ
  obtain ⟨_, _, h₃T, hxT⟩ := h₄T.app_inv wf.ordered hΓ
  obtain ⟨_, _, h₂T, hfuelT⟩ := h₃T.app_inv wf.ordered hΓ
  obtain ⟨_, _, h₁T, hhyT⟩ := h₂T.app_inv wf.ordered hΓ
  obtain ⟨_, _, hgoT, hyT⟩ := h₁T.app_inv wf.ordered hΓ
  have h₁Eq := hyEq.app_arg wf hΓ hgoT hyT
  have h₂Eq := h₁Eq.app_same wf hΓ h₁T hhyT
  have h₂CanonT := (h₂Eq.of_l wf hΓ h₂T).hasType.2
  have h₃ArgEq := hfuelEq.app_arg wf hΓ h₂CanonT hfuelT
  have h₃Same := h₂Eq.app_same wf hΓ h₂T hfuelT
  have h₃Eq := h₃Same.trans wf hΓ h₃ArgEq
  have h₃CanonT := (h₃Eq.of_l wf hΓ h₃T).hasType.2
  have h₄ArgEq := hxEq.app_arg wf hΓ h₃CanonT hxT
  have h₄Same := h₃Eq.app_same wf hΓ h₃T hxT
  have h₄Eq := h₄Same.trans wf hΓ h₄ArgEq
  have hbodyEq := h₄Eq.app_same wf hΓ h₄T hlastT
  have hrightT := (hbodyEq.of_l wf hΓ hbodyWF.hasType.1).hasType.2
  obtain ⟨u, hpropSort⟩ := hpropType
  have hlamEq : env.IsDefEqU 0 []
      (.lam propV
        (.app (.app (.app (.app (.app (.const ``Nat.div.go []) yV)
          (.bvar 0)) fuelV) xV) hfuelV))
      (.lam propV
        (.app (.app (.app (.app (.app (.const ``Nat.div.go []) (.natLit b))
          (.bvar 0)) (.natLit (a + 1))) (.natLit a)) hfuelV)) := by
    obtain ⟨T, hbodyEq⟩ := hbodyEq
    exact ⟨.forallE propV T, .lamDF hpropSort hbodyEq⟩
  have hinst := VEnv.IsDefEqU.lam_instU wf trivial hlamEq hpropSort
    hbodyWF.hasType.1 hrightT hproofT
  have hbClosed : (VExpr.natLit b).ClosedN :=
    ((hctors.natLitS b (Us := []) (Δ := [])).2.closedN'
      wf.ordered.closed trivial).1
  have haClosed : (VExpr.natLit a).ClosedN :=
    ((hctors.natLitS a (Us := []) (Δ := [])).2.closedN'
      wf.ordered.closed trivial).1
  have hfuelClosed : (VExpr.natLit (a + 1)).ClosedN :=
    ((hctors.natLitS (a + 1) (Us := []) (Δ := [])).2.closedN'
      wf.ordered.closed trivial).1
  exact ⟨hfuelV.inst proof, by
    simpa [VExpr.natDivGo, VExpr.inst, VExpr.instVar,
      hbClosed.instN_eq, haClosed.instN_eq, hfuelClosed.instN_eq]
      using hinst⟩

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

/-- The checked closed top-level division equation has exactly the semantic
shape required by `ReflectsNatNatNat.of_divCore_equations`. -/
theorem VEnv.natDivTop_semantics
    {env : VEnv} (wf : env.WF) (hprim : env.HasPrimitives)
    (hctors : VEnv.HasNatBoolConstructors env)
    (hbleC : env.contains ``Nat.ble)
    (cert : VEnv.NatLESelectorCertificate env)
    {divFn : Expr} {divV topL topR : VExpr}
    (hdivFn : TrExprS env [] [] divFn divV)
    (hdivFnClosed : divFn.looseBVarRange' = 0)
    (hdivT : env.HasType 0 [] divV
      (.forallE .nat <| .forallE .nat .nat))
    (hl : TrExprS env [] [] (natDivTopEquation divFn).1 topL)
    (hr : TrExprS env [] [] (natDivTopEquation divFn).2 topR)
    (heq : env.IsDefEqU 0 [] topL topR) :
    ∀ a b,
      if 0 < b then
        ∃ hy hfuel, env.IsDefEqU 0 []
          (.app (.app divV (.natLit a)) (.natLit b))
          (.natDivGo b (a + 1) a hy hfuel)
      else
        env.IsDefEqU 0 []
          (.app (.app divV (.natLit a)) (.natLit b)) .natZero := by
  intro a b
  obtain ⟨rhs, hrhs, htop⟩ := VEnv.instantiate_natDivTop_equation
    wf hctors hdivFn hdivFnClosed hl hr heq a b
  obtain ⟨pV, bleV, HV, tV, eV, hpS, hbleS, hHS, htS, heS, hselect⟩ :=
    VEnv.select_natDivTop_rhs wf hprim hctors hbleC cert a b hrhs
  have haT := (hctors.natLitS a (Us := []) (Δ := [])).2
  have hbT := (hctors.natLitS b (Us := []) (Δ := [])).2
  have hcallT : env.HasType 0 []
      (.app (.app divV (.natLit a)) (.natLit b)) .nat :=
    .app (.app hdivT haT) hbT
  have hrhsT := (htop.of_l wf trivial hcallT).hasType.2
  split
  · rename_i hb
    rw [if_pos hb] at hselect
    obtain ⟨proof, hselect⟩ := hselect
    have hbranchT := (hselect.of_l wf trivial hrhsT).hasType.2
    obtain ⟨propV, bodyV, rfl, hpropType, hbodyS, hproofT, hbeta⟩ :=
      VEnv.natDivTopThen_beta wf a b htS hbranchT
    obtain ⟨hfuel, hbody⟩ := VEnv.natDivTopThenBody_inst
      wf hctors hpropType hproofT a b hbodyS
    exact ⟨proof, hfuel, htop.trans wf trivial hselect |>.trans wf trivial hbeta
      |>.trans wf trivial hbody⟩
  · rename_i hb
    rw [if_neg hb] at hselect
    obtain ⟨proof, hselect⟩ := hselect
    have hbranchT := (hselect.of_l wf trivial hrhsT).hasType.2
    have hzero := VEnv.natDivTopElse_beta wf b heS hbranchT
    exact htop.trans wf trivial hselect |>.trans wf trivial hzero

/-- The two translated five-binder bodies and their dependent target
contexts, extracted from the checked closed `Nat.div.go` equation. -/
inductive VEnv.NatDivGoEquationTranslation (env : VEnv) : Prop where
  | intro
      (yTyL hyTyL fuelTyL xTyL hTyL bodyL : VExpr)
      (yTyR hyTyR fuelTyR xTyR hTyR bodyR : VExpr)
      (yTyLS : TrExprS env [] [] q(Nat) yTyL)
      (hyTyLS : TrExprS env [] [(none, .vlam yTyL)]
        (mkApp2 q(@LE.le Nat _) q(Nat.succ Nat.zero) (.bvar 0)) hyTyL)
      (fuelTyLS : TrExprS env []
        [(none, .vlam hyTyL), (none, .vlam yTyL)] q(Nat) fuelTyL)
      (xTyLS : TrExprS env []
        [(none, .vlam fuelTyL), (none, .vlam hyTyL),
          (none, .vlam yTyL)] q(Nat) xTyL)
      (hTyLS : TrExprS env []
        [(none, .vlam xTyL), (none, .vlam fuelTyL),
          (none, .vlam hyTyL), (none, .vlam yTyL)]
        (mkApp2 q(@LE.le Nat _)
          (mkApp q(Nat.succ) (.bvar 0))
          (mkApp q(Nat.succ) (.bvar 1))) hTyL)
      (yTyRS : TrExprS env [] [] q(Nat) yTyR)
      (hyTyRS : TrExprS env [] [(none, .vlam yTyR)]
        (mkApp2 q(@LE.le Nat _) q(Nat.succ Nat.zero) (.bvar 0)) hyTyR)
      (fuelTyRS : TrExprS env []
        [(none, .vlam hyTyR), (none, .vlam yTyR)] q(Nat) fuelTyR)
      (xTyRS : TrExprS env []
        [(none, .vlam fuelTyR), (none, .vlam hyTyR),
          (none, .vlam yTyR)] q(Nat) xTyR)
      (hTyRS : TrExprS env []
        [(none, .vlam xTyR), (none, .vlam fuelTyR),
          (none, .vlam hyTyR), (none, .vlam yTyR)]
        (mkApp2 q(@LE.le Nat _)
          (mkApp q(Nat.succ) (.bvar 0))
          (mkApp q(Nat.succ) (.bvar 1))) hTyR)
      (yTyLType : env.IsType 0 [] yTyL)
      (hyTyLType : env.IsType 0 [yTyL] hyTyL)
      (fuelTyLType : env.IsType 0 [hyTyL, yTyL] fuelTyL)
      (xTyLType : env.IsType 0 [fuelTyL, hyTyL, yTyL] xTyL)
      (hTyLType : env.IsType 0 [xTyL, fuelTyL, hyTyL, yTyL] hTyL)
      (yTyRType : env.IsType 0 [] yTyR)
      (hyTyRType : env.IsType 0 [yTyR] hyTyR)
      (fuelTyRType : env.IsType 0 [hyTyR, yTyR] fuelTyR)
      (xTyRType : env.IsType 0 [fuelTyR, hyTyR, yTyR] xTyR)
      (hTyRType : env.IsType 0 [xTyR, fuelTyR, hyTyR, yTyR] hTyR)
      (leftS : TrExprS env []
        [(none, .vlam hTyL), (none, .vlam xTyL),
          (none, .vlam fuelTyL), (none, .vlam hyTyL),
          (none, .vlam yTyL)]
        (natDivGoLhsBody (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
        bodyL)
      (rightS : TrExprS env []
        [(none, .vlam hTyR), (none, .vlam xTyR),
          (none, .vlam fuelTyR), (none, .vlam hyTyR),
          (none, .vlam yTyR)]
        (natDivGoRhsBody (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
        bodyR)
      (eq : env.IsDefEqU 0 []
        (.lam yTyL <| .lam hyTyL <| .lam fuelTyL <| .lam xTyL <|
          .lam hTyL bodyL)
        (.lam yTyR <| .lam hyTyR <| .lam fuelTyR <| .lam xTyR <|
          .lam hTyR bodyR)) :
      VEnv.NatDivGoEquationTranslation env

/-- Parse the checked closed recursive division equation into its two local
translated bodies. -/
theorem VEnv.NatDivGoEquationTranslation.of_checked
    {env : VEnv}
    {goL goR : VExpr}
    (hl : TrExprS env [] [] natDivGoEquation.1 goL)
    (hr : TrExprS env [] [] natDivGoEquation.2 goR)
    (heq : env.IsDefEqU 0 [] goL goR) :
    VEnv.NatDivGoEquationTranslation env := by
  simp only [natDivGoEquation] at hl hr
  cases hl with
  | lam hyTyLType hyTyLS hL₁ =>
    cases hL₁ with
    | lam hhyTyLType hhyTyLS hL₂ =>
      cases hL₂ with
      | lam hfuelTyLType hfuelTyLS hL₃ =>
        cases hL₃ with
        | lam hxTyLType hxTyLS hL₄ =>
          cases hL₄ with
          | lam hhTyLType hhTyLS hbodyL =>
            rename_i yTyL hyTyL fuelTyL xTyL hTyL bodyL
            cases hr with
            | lam hyTyRType hyTyRS hR₁ =>
              cases hR₁ with
              | lam hhyTyRType hhyTyRS hR₂ =>
                cases hR₂ with
                | lam hfuelTyRType hfuelTyRS hR₃ =>
                  cases hR₃ with
                  | lam hxTyRType hxTyRS hR₄ =>
                    cases hR₄ with
                    | lam hhTyRType hhTyRS hbodyR =>
                      rename_i yTyR hyTyR fuelTyR xTyR hTyR bodyR
                      exact .intro yTyL hyTyL fuelTyL xTyL hTyL bodyL
                        yTyR hyTyR fuelTyR xTyR hTyR bodyR
                        hyTyLS hhyTyLS hfuelTyLS hxTyLS hhTyLS
                        hyTyRS hhyTyRS hfuelTyRS hxTyRS hhTyRS
                        hyTyLType hhyTyLType hfuelTyLType hxTyLType hhTyLType
                        hyTyRType hhyTyRType hfuelTyRType hxTyRType hhTyRType
                        hbodyL hbodyR heq

end Lean4Lean.Environment
