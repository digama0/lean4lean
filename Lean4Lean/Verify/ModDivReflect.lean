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

private theorem translated_nat_type_eq
    {env : VEnv} (wf : env.WF)
    (hctors : VEnv.HasNatBoolConstructors env)
    {Δ : VLCtx} (hΔ : Δ.WF env 0) {natV : VExpr}
    (hnatV : TrExprS env [] Δ q(Nat) natV) :
    env.IsDefEqU 0 Δ.toCtx natV .nat := by
  have hzT := (hctors.natZeroS (Us := []) (Δ := Δ)).2
  obtain ⟨_, hnatType⟩ := hzT.isType wf hΔ.toCtx
  obtain ⟨ci, hci, _, hlen⟩ := hnatType.const_inv wf hΔ.toCtx
  have hnatS : TrExprS env [] Δ q(Nat) .nat :=
    .const hci rfl (by simpa using hlen)
  exact TrExprS.uniq (Us := []) wf (.refl wf hΔ) hnatV hnatS

private theorem translated_bvar_target_eq
    {env : VEnv} {Δ : VLCtx} {i : Nat} {e e₀ : VExpr}
    (hcanon : ∃ A, Δ.find? (.inl i) = some (e₀, A))
    (h : TrExprS env Us Δ (.bvar i) e) : e = e₀ := by
  rcases hcanon with ⟨A₀, hcanon⟩
  cases h with
  | bvar hfind =>
    rw [hcanon] at hfind
    cases hfind
    rfl

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

/-- The translated dependent function type of `Nat.div.go`. -/
inductive VEnv.NatDivGoTypeTranslation (env : VEnv) (goTyV : VExpr) : Prop where
  | intro
      (yTy hyTy fuelTy xTy hTy resultTy : VExpr)
      (yTyS : TrExprS env [] [] q(Nat) yTy)
      (hyTyS : TrExprS env [] [(none, .vlam yTy)]
        (mkApp2 q(@LE.le Nat _) q(Nat.succ Nat.zero) (.bvar 0)) hyTy)
      (fuelTyS : TrExprS env []
        [(none, .vlam hyTy), (none, .vlam yTy)] q(Nat) fuelTy)
      (xTyS : TrExprS env []
        [(none, .vlam fuelTy), (none, .vlam hyTy),
          (none, .vlam yTy)] q(Nat) xTy)
      (hTyS : TrExprS env []
        [(none, .vlam xTy), (none, .vlam fuelTy),
          (none, .vlam hyTy), (none, .vlam yTy)]
        (mkApp2 q(@LE.le Nat _)
          (mkApp q(Nat.succ) (.bvar 0)) (.bvar 1)) hTy)
      (resultTyS : TrExprS env []
        [(none, .vlam hTy), (none, .vlam xTy),
          (none, .vlam fuelTy), (none, .vlam hyTy),
          (none, .vlam yTy)] q(Nat) resultTy)
      (yTyType : env.IsType 0 [] yTy)
      (hyTyType : env.IsType 0 [yTy] hyTy)
      (fuelTyType : env.IsType 0 [hyTy, yTy] fuelTy)
      (xTyType : env.IsType 0 [fuelTy, hyTy, yTy] xTy)
      (hTyType : env.IsType 0 [xTy, fuelTy, hyTy, yTy] hTy)
      (resultTyType : env.IsType 0 [hTy, xTy, fuelTy, hyTy, yTy] resultTy)
      (shape : goTyV = (.forallE yTy <| .forallE hyTy <|
        .forallE fuelTy <| .forallE xTy <| .forallE hTy resultTy)) :
      VEnv.NatDivGoTypeTranslation env goTyV

theorem VEnv.NatDivGoTypeTranslation.of_translation
    {env : VEnv} {goTyV : VExpr}
    (h : TrExprS env [] []
      q(∀ y, Nat.succ Nat.zero ≤ y →
        ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat) goTyV) :
    VEnv.NatDivGoTypeTranslation env goTyV := by
  cases h with
  | forallE hyTyType hrestType₁ hyTyS h₁ =>
    cases h₁ with
    | forallE hhyTyType hrestType₂ hhyTyS h₂ =>
      cases h₂ with
      | forallE hfuelTyType hrestType₃ hfuelTyS h₃ =>
        cases h₃ with
        | forallE hxTyType hrestType₄ hxTyS h₄ =>
          cases h₄ with
          | forallE hhTyType hresultTyType hhTyS hresultTyS =>
            rename_i yTy hyTy fuelTy xTy hTy resultTy
            exact .intro yTy hyTy fuelTy xTy hTy resultTy
              hyTyS hhyTyS hfuelTyS hxTyS hhTyS hresultTyS
              hyTyType hhyTyType hfuelTyType hxTyType hhTyType
              hresultTyType rfl

/-- Recover the two proof-argument typings of a concrete canonical
`Nat.div.go` call from its retained dependent function type. -/
theorem VEnv.NatDivGoTypeTranslation.call_proof_types
    {env : VEnv} (wf : env.WF)
    (hctors : VEnv.HasNatBoolConstructors env)
    {goTyV : VExpr} (cert : VEnv.NatDivGoTypeTranslation env goTyV)
    (hgoT : env.HasType 0 [] (.const ``Nat.div.go []) goTyV)
    (y fuel x : Nat) {hy hfuel : VExpr}
    (hcallT : env.HasType 0 [] (.natDivGo y fuel x hy hfuel) .nat) :
    ∃ yTy hyTy fuelTy xTy hTy resultTy : VExpr,
      env.HasType 0 [] hy (hyTy.inst (.natLit y)) ∧
      env.HasType 0 [] hfuel
        ((((hTy.inst (.natLit y) 3).inst hy 2).inst
          (.natLit fuel) 1).inst (.natLit x)) := by
  cases cert with
  | intro yTy hyTy fuelTy xTy hTy resultTy
      yTyS hyTyS fuelTyS xTyS hTyS resultTyS
      yTyType hyTyType fuelTyType xTyType hTyType resultTyType shape =>
    subst goTyV
    simp only [VExpr.natDivGo] at hcallT
    obtain ⟨_, _, h₄Raw, hhRaw⟩ := hcallT.app_inv wf.ordered trivial
    obtain ⟨_, _, h₃Raw, hxRaw⟩ := h₄Raw.app_inv wf.ordered trivial
    obtain ⟨_, _, h₂Raw, hfuelRaw⟩ := h₃Raw.app_inv wf.ordered trivial
    obtain ⟨_, _, h₁Raw, hhyRaw⟩ := h₂Raw.app_inv wf.ordered trivial
    obtain ⟨_, _, hgoRaw, hyRaw⟩ := h₁Raw.app_inv wf.ordered trivial
    have hgoTyEq := hgoRaw.uniqU wf trivial hgoT
    obtain ⟨_, hyDomEq⟩ := (hgoTyEq.forallE_inv wf trivial).1
    have hyT := hyRaw.defeqU_r wf trivial hyDomEq.toU
    have h₁Canon := VEnv.HasType.app hgoT hyT
    have h₁TyEq := h₁Raw.uniqU wf trivial h₁Canon
    obtain ⟨_, hhyDomEq⟩ := (h₁TyEq.forallE_inv wf trivial).1
    have hhyT := hhyRaw.defeqU_r wf trivial hhyDomEq.toU
    have h₂Canon := VEnv.HasType.app h₁Canon hhyT
    have h₂TyEq := h₂Raw.uniqU wf trivial h₂Canon
    obtain ⟨_, hfuelDomEq⟩ := (h₂TyEq.forallE_inv wf trivial).1
    have hfuelT := hfuelRaw.defeqU_r wf trivial hfuelDomEq.toU
    have h₃Canon := VEnv.HasType.app h₂Canon hfuelT
    have h₃TyEq := h₃Raw.uniqU wf trivial h₃Canon
    obtain ⟨_, hxDomEq⟩ := (h₃TyEq.forallE_inv wf trivial).1
    have hxT := hxRaw.defeqU_r wf trivial hxDomEq.toU
    have h₄Canon := VEnv.HasType.app h₃Canon hxT
    have h₄TyEq := h₄Raw.uniqU wf trivial h₄Canon
    obtain ⟨_, hhDomEq⟩ := (h₄TyEq.forallE_inv wf trivial).1
    have hhT := hhRaw.defeqU_r wf trivial hhDomEq.toU
    exact ⟨yTy, hyTy, fuelTy, xTy, hTy, resultTy,
      by simpa [VExpr.inst] using hhyT,
      by simpa [VExpr.inst] using hhT⟩

/-- Align the first dependent proof domain of two translations of the same
one-variable source proposition, then instantiate the shared natural. -/
theorem VEnv.align_nat_proof_domain
    {env : VEnv} (wf : env.WF)
    (hctors : VEnv.HasNatBoolConstructors env)
    {yTyL yTyR proofTyL proofTyR : VExpr} {pS : Expr}
    (hyTyL : TrExprS env [] [] q(Nat) yTyL)
    (hyTyR : TrExprS env [] [] q(Nat) yTyR)
    (hproofTyL : TrExprS env [] [(none, .vlam yTyL)] pS proofTyL)
    (hproofTyR : TrExprS env [] [(none, .vlam yTyR)] pS proofTyR)
    (y : Nat) (hyL : env.HasType 0 [] (.natLit y) yTyL) :
    env.IsDefEqU 0 [] (proofTyL.inst (.natLit y))
      (proofTyR.inst (.natLit y)) := by
  have hdomL := translated_nat_type_eq wf hctors (by trivial) hyTyL
  have hdomR := translated_nat_type_eq wf hctors (by trivial) hyTyR
  have hyTyEq := hdomL.trans wf trivial hdomR.symm
  have hzT := (hctors.natZeroS (Us := []) (Δ := [])).2
  obtain ⟨_, hnatSort⟩ := hzT.isType wf trivial
  have hyTyLT := (hdomL.of_r wf trivial hnatSort).hasType.1
  have hyTyEqD := hyTyEq.of_l wf trivial hyTyLT
  have hctx : VLCtx.IsDefEq env 0
      [(none, .vlam yTyL)] [(none, .vlam yTyR)] :=
    .cons .nil nofun (.vlam hyTyEqD)
  have hproofCtx := TrExprS.uniq (Us := []) wf hctx hproofTyL hproofTyR
  exact hproofCtx.instN wf.ordered
    (.zero : Ctx.InstN [] (.natLit y) yTyL 0 [yTyL] []) hyL

/-- Instantiate definitionally equal target lambdas when both domains have
already been normalized to `Nat`.  This is reused for the divisor, fuel, and
dividend binders of `Nat.div.go`. -/
theorem VEnv.instantiate_nat_target_lam
    {env : VEnv} (wf : env.WF)
    (hctors : VEnv.HasNatBoolConstructors env)
    {domL domR bodyL bodyR : VExpr}
    (hdomL : env.IsDefEqU 0 [] domL .nat)
    (hdomR : env.IsDefEqU 0 [] domR .nat)
    (heq : env.IsDefEqU 0 [] (.lam domL bodyL) (.lam domR bodyR))
    (n : Nat) :
    env.HasType 0 [] (.natLit n) domL ∧
    env.HasType 0 [] (.natLit n) domR ∧
    env.IsDefEqU 0 [] (bodyL.inst (.natLit n)) (bodyR.inst (.natLit n)) := by
  have hnT := (hctors.natLitS n (Us := []) (Δ := [])).2
  have hnL := hnT.defeqU_r wf trivial hdomL.symm
  have hnR := hnT.defeqU_r wf trivial hdomR.symm
  have heqU := heq
  obtain ⟨_, heqD⟩ := heq
  obtain ⟨⟨_, hdomLSort⟩, _, hbodyLT⟩ :=
    heqD.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hbodyRT⟩ := heqD.hasType.2.lam_inv wf trivial
  have hdomEq := hdomL.trans wf trivial hdomR.symm
  have hinst := VEnv.IsDefEqU.lam_instU₂ wf trivial heqU
    hdomLSort hbodyLT hbodyRT hdomEq hnL
  exact ⟨hnL, hnR, hinst⟩

/-- Target-only instantiation for a dependent proof binder.  No source
expression for the proof is required. -/
theorem VEnv.instantiate_proof_target_lam
    {env : VEnv} (wf : env.WF)
    {domL domR bodyL bodyR proof : VExpr}
    (heq : env.IsDefEqU 0 [] (.lam domL bodyL) (.lam domR bodyR))
    (hproofL : env.HasType 0 [] proof domL)
    (hproofR : env.HasType 0 [] proof domR) :
    env.IsDefEqU 0 [] (bodyL.inst proof) (bodyR.inst proof) := by
  have heqU := heq
  obtain ⟨_, heqD⟩ := heq
  obtain ⟨⟨_, hdomLSort⟩, _, hbodyLT⟩ :=
    heqD.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hbodyRT⟩ := heqD.hasType.2.lam_inv wf trivial
  exact VEnv.IsDefEqU.lam_instU_hetero wf trivial heqU
    hdomLSort hbodyLT hbodyRT hproofL hproofR

/-- Infer the right-domain typing of a proof argument from a checked lambda
equality, then instantiate both sides. -/
theorem VEnv.instantiate_proof_target_lam_from_left
    {env : VEnv} (wf : env.WF)
    {domL domR bodyL bodyR proof : VExpr}
    (heq : env.IsDefEqU 0 [] (.lam domL bodyL) (.lam domR bodyR))
    (hproofL : env.HasType 0 [] proof domL) :
    env.HasType 0 [] proof domR ∧
    env.IsDefEqU 0 [] (bodyL.inst proof) (bodyR.inst proof) := by
  have heqU := heq
  obtain ⟨_, heqD⟩ := heq
  obtain ⟨⟨_, hdomLSort⟩, _, hbodyLT⟩ :=
    heqD.hasType.1.lam_inv wf trivial
  obtain ⟨⟨_, hdomRSort⟩, _, hbodyRT⟩ :=
    heqD.hasType.2.lam_inv wf trivial
  have hleftCanonT := VEnv.HasType.lam hdomLSort hbodyLT
  have happ := heqU.app_same wf trivial hleftCanonT hproofL
  have happRightT :=
    (happ.of_l wf trivial (VEnv.HasType.app hleftCanonT hproofL)).hasType.2
  obtain ⟨_, _, hrightLamT, hproofRaw⟩ :=
    happRightT.app_inv wf.ordered trivial
  have hrightCanonT := VEnv.HasType.lam hdomRSort hbodyRT
  have hrightTyEq := hrightLamT.uniqU wf trivial hrightCanonT
  obtain ⟨_, hdomainEq⟩ := (hrightTyEq.forallE_inv wf trivial).1
  have hproofR := hproofRaw.defeqU_r wf trivial hdomainEq.toU
  exact ⟨hproofR,
    VEnv.IsDefEqU.lam_instU_hetero wf trivial heqU
      hdomLSort hbodyLT hbodyRT hproofL hproofR⟩

theorem VEnv.IsDefEqU.inst_outer2
    {env : VEnv} (wf : env.WF)
    {A B a b e₁ e₂ : VExpr}
    (ha : env.HasType 0 [] a A)
    (hb : env.HasType 0 [] b (B.inst a))
    (h : env.IsDefEqU 0 [B, A] e₁ e₂) :
    env.IsDefEqU 0 [] ((e₁.inst a 1).inst b) ((e₂.inst a 1).inst b) := by
  have h₁ := h.instN wf.ordered
    (.succ (.zero : Ctx.InstN [] a A 0 [A] [])) ha
  exact h₁.instN wf.ordered
    (.zero : Ctx.InstN [] b (B.inst a) 0 [B.inst a] []) hb

theorem VEnv.IsDefEqU.inst_outer3
    {env : VEnv} (wf : env.WF)
    {A B C a b c e₁ e₂ : VExpr}
    (ha : env.HasType 0 [] a A)
    (hb : env.HasType 0 [] b (B.inst a))
    (hc : env.HasType 0 [] c ((C.inst a 1).inst b))
    (h : env.IsDefEqU 0 [C, B, A] e₁ e₂) :
    env.IsDefEqU 0 []
      (((e₁.inst a 2).inst b 1).inst c)
      (((e₂.inst a 2).inst b 1).inst c) := by
  have h₁ := h.instN wf.ordered
    (.succ (.succ (.zero : Ctx.InstN [] a A 0 [A] []))) ha
  have h₂ := h₁.instN wf.ordered
    (.succ (.zero : Ctx.InstN [] b (B.inst a) 0 [B.inst a] [])) hb
  exact h₂.instN wf.ordered
    (.zero : Ctx.InstN [] c ((C.inst a 1).inst b) 0
      [((C.inst a 1).inst b)] []) hc

theorem VEnv.IsDefEqU.inst_outer4
    {env : VEnv} (wf : env.WF)
    {A B C D a b c d e₁ e₂ : VExpr}
    (ha : env.HasType 0 [] a A)
    (hb : env.HasType 0 [] b (B.inst a))
    (hc : env.HasType 0 [] c ((C.inst a 1).inst b))
    (hd : env.HasType 0 [] d
      (((D.inst a 2).inst b 1).inst c))
    (h : env.IsDefEqU 0 [D, C, B, A] e₁ e₂) :
    env.IsDefEqU 0 []
      ((((e₁.inst a 3).inst b 2).inst c 1).inst d)
      ((((e₂.inst a 3).inst b 2).inst c 1).inst d) := by
  have h₁ := h.instN wf.ordered
    (.succ (.succ (.succ (.zero : Ctx.InstN [] a A 0 [A] [])))) ha
  have h₂ := h₁.instN wf.ordered
    (.succ (.succ (.zero : Ctx.InstN [] b (B.inst a) 0
      [B.inst a] []))) hb
  have h₃ := h₂.instN wf.ordered
    (.succ (.zero : Ctx.InstN [] c ((C.inst a 1).inst b) 0
      [((C.inst a 1).inst b)] [])) hc
  exact h₃.instN wf.ordered
    (.zero : Ctx.InstN [] d (((D.inst a 2).inst b 1).inst c) 0
      [(((D.inst a 2).inst b 1).inst c)] []) hd

theorem VEnv.HasType.inst_outer4_keep_head
    {env : VEnv} (wf : env.WF)
    {A B C D E a b c d e T : VExpr}
    (ha : env.HasType 0 [] a A)
    (hb : env.HasType 0 [] b (B.inst a))
    (hc : env.HasType 0 [] c ((C.inst a 1).inst b))
    (hd : env.HasType 0 [] d
      (((D.inst a 2).inst b 1).inst c))
    (h : env.HasType 0 [E, D, C, B, A] e T) :
    env.HasType 0
      [((((E.inst a 3).inst b 2).inst c 1).inst d)]
      ((((e.inst a 4).inst b 3).inst c 2).inst d 1)
      ((((T.inst a 4).inst b 3).inst c 2).inst d 1) := by
  have h₁ := h.instN wf.ordered
    (.succ (.succ (.succ (.succ
      (.zero : Ctx.InstN [] a A 0 [A] []))))) ha
  have h₂ := h₁.instN wf.ordered
    (.succ (.succ (.succ
      (.zero : Ctx.InstN [] b (B.inst a) 0 [B.inst a] [])))) hb
  have h₃ := h₂.instN wf.ordered
    (.succ (.succ
      (.zero : Ctx.InstN [] c ((C.inst a 1).inst b) 0
        [((C.inst a 1).inst b)] []))) hc
  exact h₃.instN wf.ordered
    (.succ (.zero : Ctx.InstN [] d
      (((D.inst a 2).inst b 1).inst c) 0
      [(((D.inst a 2).inst b 1).inst c)] [])) hd

/-- Semantically instantiate all five binders of the retained recursive
division equation.  The two proof arguments need only target-level typing. -/
theorem VEnv.instantiate_natDivGo_target_binders
    {env : VEnv} (wf : env.WF)
    (hctors : VEnv.HasNatBoolConstructors env)
    {yTyL hyTyL fuelTyL xTyL hTyL bodyL : VExpr}
    {yTyR hyTyR fuelTyR xTyR hTyR bodyR : VExpr}
    (yTyLS : TrExprS env [] [] q(Nat) yTyL)
    (fuelTyLS : TrExprS env []
      [(none, .vlam hyTyL), (none, .vlam yTyL)] q(Nat) fuelTyL)
    (xTyLS : TrExprS env []
      [(none, .vlam fuelTyL), (none, .vlam hyTyL),
        (none, .vlam yTyL)] q(Nat) xTyL)
    (yTyRS : TrExprS env [] [] q(Nat) yTyR)
    (fuelTyRS : TrExprS env []
      [(none, .vlam hyTyR), (none, .vlam yTyR)] q(Nat) fuelTyR)
    (xTyRS : TrExprS env []
      [(none, .vlam fuelTyR), (none, .vlam hyTyR),
        (none, .vlam yTyR)] q(Nat) xTyR)
    (yTyLType : env.IsType 0 [] yTyL)
    (hyTyLType : env.IsType 0 [yTyL] hyTyL)
    (fuelTyLType : env.IsType 0 [hyTyL, yTyL] fuelTyL)
    (xTyLType : env.IsType 0 [fuelTyL, hyTyL, yTyL] xTyL)
    (yTyRType : env.IsType 0 [] yTyR)
    (hyTyRType : env.IsType 0 [yTyR] hyTyR)
    (fuelTyRType : env.IsType 0 [hyTyR, yTyR] fuelTyR)
    (xTyRType : env.IsType 0 [fuelTyR, hyTyR, yTyR] xTyR)
    (heq : env.IsDefEqU 0 []
      (.lam yTyL <| .lam hyTyL <| .lam fuelTyL <| .lam xTyL <|
        .lam hTyL bodyL)
      (.lam yTyR <| .lam hyTyR <| .lam fuelTyR <| .lam xTyR <|
        .lam hTyR bodyR))
    (y fuel x : Nat) {hy hfuel : VExpr}
    (hhyL : env.HasType 0 [] hy (hyTyL.inst (.natLit y)))
    (hhfuelL : env.HasType 0 [] hfuel
      ((((hTyL.inst (.natLit y) 3).inst hy 2).inst (.natLit fuel) 1).inst
        (.natLit x))) :
    env.IsDefEqU 0 []
      (((((bodyL.inst (.natLit y) 4).inst hy 3).inst
        (.natLit fuel) 2).inst (.natLit x) 1).inst hfuel)
      (((((bodyR.inst (.natLit y) 4).inst hy 3).inst
        (.natLit fuel) 2).inst (.natLit x) 1).inst hfuel) := by
  have hyDomL := translated_nat_type_eq wf hctors (by trivial) yTyLS
  have hyDomR := translated_nat_type_eq wf hctors (by trivial) yTyRS
  obtain ⟨hyLT, hyRT, h₁⟩ := VEnv.instantiate_nat_target_lam
    wf hctors hyDomL hyDomR heq y
  simp only [VExpr.inst] at h₁
  obtain ⟨hhyR, h₂⟩ :=
    VEnv.instantiate_proof_target_lam_from_left wf h₁ hhyL
  simp only [VExpr.inst] at h₂
  have hΔL₂ : VLCtx.WF env 0
      [(none, .vlam hyTyL), (none, .vlam yTyL)] :=
    ⟨⟨trivial, nofun, yTyLType⟩, nofun, hyTyLType⟩
  have hΔR₂ : VLCtx.WF env 0
      [(none, .vlam hyTyR), (none, .vlam yTyR)] :=
    ⟨⟨trivial, nofun, yTyRType⟩, nofun, hyTyRType⟩
  have hfuelDomLCtx := translated_nat_type_eq wf hctors hΔL₂ fuelTyLS
  have hfuelDomRCtx := translated_nat_type_eq wf hctors hΔR₂ fuelTyRS
  have hfuelDomL := VEnv.IsDefEqU.inst_outer2 wf hyLT hhyL hfuelDomLCtx
  have hfuelDomR := VEnv.IsDefEqU.inst_outer2 wf hyRT hhyR hfuelDomRCtx
  obtain ⟨hfuelLT, hfuelRT, h₃⟩ := VEnv.instantiate_nat_target_lam
    wf hctors hfuelDomL hfuelDomR h₂ fuel
  simp only [VExpr.inst] at h₃
  have hΔL₃ : VLCtx.WF env 0
      [(none, .vlam fuelTyL), (none, .vlam hyTyL),
        (none, .vlam yTyL)] :=
    ⟨hΔL₂, nofun, fuelTyLType⟩
  have hΔR₃ : VLCtx.WF env 0
      [(none, .vlam fuelTyR), (none, .vlam hyTyR),
        (none, .vlam yTyR)] :=
    ⟨hΔR₂, nofun, fuelTyRType⟩
  have hxDomLCtx := translated_nat_type_eq wf hctors hΔL₃ xTyLS
  have hxDomRCtx := translated_nat_type_eq wf hctors hΔR₃ xTyRS
  have hxDomL := VEnv.IsDefEqU.inst_outer3 wf hyLT hhyL hfuelLT hxDomLCtx
  have hxDomR := VEnv.IsDefEqU.inst_outer3 wf hyRT hhyR hfuelRT hxDomRCtx
  obtain ⟨hxLT, hxRT, h₄⟩ := VEnv.instantiate_nat_target_lam
    wf hctors hxDomL hxDomR h₃ x
  simp only [VExpr.inst] at h₄
  obtain ⟨hhfuelR, h₅⟩ :=
    VEnv.instantiate_proof_target_lam_from_left wf h₄ hhfuelL
  simpa only [VExpr.inst] using h₅

/-- The translated left recursive body is syntactically the expected local
`Nat.div.go` call once unique constants and bound variables are normalized. -/
theorem VEnv.natDivGoLhsBody_canonical
    {env : VEnv} (hctors : VEnv.HasNatBoolConstructors env)
    {yTy hyTy fuelTy xTy hTy bodyV : VExpr}
    (hbodyS : TrExprS env []
      [(none, .vlam hTy), (none, .vlam xTy),
        (none, .vlam fuelTy), (none, .vlam hyTy),
        (none, .vlam yTy)]
      (natDivGoLhsBody (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
      bodyV) :
    bodyV = .app (.app (.app (.app (.app (.const ``Nat.div.go [])
      (.bvar 4)) (.bvar 3)) (.app .natSucc (.bvar 2)))
      (.bvar 1)) (.bvar 0) := by
  let Δ : VLCtx :=
    [(none, .vlam hTy), (none, .vlam xTy),
      (none, .vlam fuelTy), (none, .vlam hyTy),
      (none, .vlam yTy)]
  change TrExprS env [] Δ _ bodyV at hbodyS
  simp only [natDivGoLhsBody, mkApp5, mkApp4, mkApp, mkAppB] at hbodyS
  cases hbodyS with
  | app h₄T hhT h₄ hhS =>
    rename_i A₄ B₄ hhV
    cases h₄ with
    | app h₃T hxT h₃ hxS =>
      rename_i A₃ B₃ hxV
      cases h₃ with
      | app h₂T hfuelT h₂ hfuelS =>
        rename_i A₂ B₂ hfuelV
        cases h₂ with
        | app h₁T hhyT h₁ hhyS =>
          rename_i A₁ B₁ hhyV
          cases h₁ with
          | app hgoT hyT hgoS hyS =>
            rename_i goV A₀ B₀ hyV
            cases hfuelS with
            | app hsuccT hfuelArgT hsuccS hfuelArgS =>
              rename_i succV AS BS fuelArgV
              have hyEq : hyV = .bvar 4 := translated_bvar_target_eq
                (by simp [Δ, VLCtx.find?, VLCtx.next,
                  VLocalDecl.value, VLocalDecl.type, VLocalDecl.depth,
                  VExpr.liftN, VExpr.lift, liftVar]) hyS
              have hhyEq : hhyV = .bvar 3 := translated_bvar_target_eq
                (by simp [Δ, VLCtx.find?, VLCtx.next,
                  VLocalDecl.value, VLocalDecl.type, VLocalDecl.depth,
                  VExpr.liftN, VExpr.lift, liftVar]) hhyS
              have hfuelEq : fuelArgV = .bvar 2 := translated_bvar_target_eq
                (by simp [Δ, VLCtx.find?, VLCtx.next,
                  VLocalDecl.value, VLocalDecl.type, VLocalDecl.depth,
                  VExpr.liftN, VExpr.lift, liftVar]) hfuelArgS
              have hxEq : hxV = .bvar 1 := translated_bvar_target_eq
                (by simp [Δ, VLCtx.find?, VLCtx.next,
                  VLocalDecl.value, VLocalDecl.type, VLocalDecl.depth,
                  VExpr.liftN, VExpr.lift, liftVar]) hxS
              have hhEq : hhV = .bvar 0 := translated_bvar_target_eq
                (by simp [Δ, VLCtx.find?, VLCtx.next,
                  VLocalDecl.value, VLocalDecl.type, VLocalDecl.depth,
                  VExpr.liftN, VExpr.lift, liftVar]) hhS
              subst hyV
              subst hhyV
              subst fuelArgV
              subst hxV
              subst hhV
              have hsuccCanon := (hctors.natSuccS (Us := [])
                (Δ := Δ)).1
              cases hsuccS.unique (by trivial) hsuccCanon
              cases hgoS with
              | const _ hus _ =>
                simp at hus
                subst hus
                rfl

end Lean4Lean.Environment
