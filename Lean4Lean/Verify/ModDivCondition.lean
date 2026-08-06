import Lean4Lean.Verify.ConditionReflect

namespace Lean4Lean.Environment
open Lean VEnv

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

/-- The evidence-retaining source wrapper discovers every translation needed
to turn a successful Nat-≤ condition check into a semantic selector. -/
theorem Condition.natLE.checkForPrimitive.WF.selector
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {fail : ∀ {α}, TypeChecker.M α}
    (hlparams : c.lparams = []) (hvlctx : c.vlctx = [])
    (hfail : ∀ {α} {s'}, TypeChecker.M.WF c s'
      (fail : TypeChecker.M α) fun _ _ => False) :
    TypeChecker.M.WF c s (Condition.natLE.checkForPrimitive fail)
      fun _ _ => ∃ _selector : VEnv.NatLESelectorCertificate c.venv, True := by
  unfold Condition.natLE.checkForPrimitive
  have hevidence : ∀ e ∈ Condition.natLEEvidenceExpressions,
      e.FVarsIn (· ∈ c.vlctx.fvars) := by
    intro e he
    have hclosed : ∀ e ∈ Condition.natLEEvidenceExpressions,
        e.hasFVar = false ∧ e.hasMVar = false := by
      simp [Condition.natLEEvidenceExpressions, Condition.natLE,
        Condition.natLEReflectProof, Condition.natLEReflectedFn,
        Condition.natLEDecideFn, Reflection.defn₁, Reflection.ite,
        Reflection.natDITE]
      native_decide
    exact Expr.closed_fvarsIn (hclosed e he).1 (hclosed e he).2
  refine (checkTypeList.WF (es :=
    Condition.natLEEvidenceExpressions) hevidence).bind
      fun _ s' _ htypes => ?_
  let r := Reflection.defn₁
  let iteTy : Expr := .arrow q(Prop) <| .arrow q(Bool) <|
    .arrow (mkApp2 r.type (.bvar 1) (.bvar 0))
      q(∀ α : Type, α → α → α)
  let iteTrueL : Expr := .lam0 q(Prop) <|
    .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
      mkApp3 r.ite (.bvar 1) q(true) (.bvar 0)
  let iteTrueR : Expr := .lam0 q(Prop) <|
    .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
      .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 1
  let iteFalseL : Expr := .lam0 q(Prop) <|
    .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
      mkApp3 r.ite (.bvar 1) q(false) (.bvar 0)
  let iteFalseR : Expr := .lam0 q(Prop) <|
    .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
      .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 0
  let diteTy : Expr := .arrow q(Prop) <| .arrow q(Bool) <|
    .arrow (mkApp2 r.type (.bvar 1) (.bvar 0)) <|
    .arrow (.arrow (.bvar 2) q(Nat)) <|
    .arrow (.arrow (mkApp q(Not) (.bvar 3)) q(Nat)) q(Nat)
  let ofTrueTy : Expr := .arrow q(Prop) <|
    .arrow (mkApp2 r.type (.bvar 0) q(true)) (.bvar 1)
  let ofFalseTy : Expr := .arrow q(Prop) <|
    .arrow (mkApp2 r.type (.bvar 0) q(false)) (mkApp q(Not) (.bvar 1))
  let close (truth : Expr) (body : Expr) : Expr :=
    .lam0 q(Prop) <|
    .lam0 (.arrow (.bvar 0) q(Nat)) <|
    .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
    .lam0 (mkApp2 r.type (.bvar 2) truth) body
  let diteTrueL : Expr := close q(true) <|
    mkApp5 r.natDITE (.bvar 3) q(true) (.bvar 0) (.bvar 2) (.bvar 1)
  let diteTrueR : Expr := close q(true) <|
    mkApp (.bvar 2) (mkApp2 r.ofTrue (.bvar 3) (.bvar 0))
  let diteFalseL : Expr := close q(false) <|
    mkApp5 r.natDITE (.bvar 3) q(false) (.bvar 0) (.bvar 2) (.bvar 1)
  let diteFalseR : Expr := close q(false) <|
    mkApp (.bvar 1) (mkApp2 r.ofFalse (.bvar 3) (.bvar 0))
  have mem (e) (h : e ∈ Condition.natLEEvidenceExpressions) := htypes e h
  obtain ⟨dec', _, hdec, _⟩ := mem Condition.natLE.dec (by simp [Condition.natLEEvidenceExpressions])
  obtain ⟨prop', _, hprop, _⟩ := mem Condition.natLE.prop (by simp [Condition.natLEEvidenceExpressions])
  obtain ⟨propTy', _, hpropTy, _⟩ := mem q(Nat → Nat → Prop) (by simp [Condition.natLEEvidenceExpressions])
  obtain ⟨rtype', _, hrtype, _⟩ := mem r.type (by simp [Condition.natLEEvidenceExpressions, r])
  obtain ⟨rtypeCanon', _, hrtypeCanon, _⟩ := mem q(Prop → Bool → Prop) (by simp [Condition.natLEEvidenceExpressions])
  obtain ⟨ite', _, hite, _⟩ := mem r.ite (by simp [Condition.natLEEvidenceExpressions, r])
  obtain ⟨iteTy', _, hiteTy, _⟩ := mem iteTy (by simp [Condition.natLEEvidenceExpressions, iteTy, r])
  obtain ⟨iteTrueL', _, hiteTrueL, _⟩ := mem iteTrueL (by simp [Condition.natLEEvidenceExpressions, iteTrueL, r])
  obtain ⟨iteTrueR', _, hiteTrueR, _⟩ := mem iteTrueR (by simp [Condition.natLEEvidenceExpressions, iteTrueR, r])
  obtain ⟨iteFalseL', _, hiteFalseL, _⟩ := mem iteFalseL (by simp [Condition.natLEEvidenceExpressions, iteFalseL, r])
  obtain ⟨iteFalseR', _, hiteFalseR, _⟩ := mem iteFalseR (by simp [Condition.natLEEvidenceExpressions, iteFalseR, r])
  obtain ⟨not', _, hnot, _⟩ := mem q(Not) (by simp [Condition.natLEEvidenceExpressions])
  obtain ⟨notTy', _, hnotTy, _⟩ := mem q(Prop → Prop) (by simp [Condition.natLEEvidenceExpressions])
  obtain ⟨dite', _, hdite, _⟩ := mem r.natDITE (by simp [Condition.natLEEvidenceExpressions, r])
  obtain ⟨diteTy', _, hditeTy, _⟩ := mem diteTy (by simp [Condition.natLEEvidenceExpressions, diteTy, r])
  obtain ⟨ofTrue', _, hofTrue, _⟩ := mem r.ofTrue (by simp [Condition.natLEEvidenceExpressions, r])
  obtain ⟨ofTrueTy', _, hofTrueTy, _⟩ := mem ofTrueTy (by simp [Condition.natLEEvidenceExpressions, ofTrueTy, r])
  obtain ⟨ofFalse', _, hofFalse, _⟩ := mem r.ofFalse (by simp [Condition.natLEEvidenceExpressions, r])
  obtain ⟨ofFalseTy', _, hofFalseTy, _⟩ := mem ofFalseTy (by simp [Condition.natLEEvidenceExpressions, ofFalseTy, r])
  obtain ⟨diteTrueL', _, hditeTrueL, _⟩ := mem diteTrueL (by simp [Condition.natLEEvidenceExpressions, diteTrueL, close, r])
  obtain ⟨diteTrueR', _, hditeTrueR, _⟩ := mem diteTrueR (by simp [Condition.natLEEvidenceExpressions, diteTrueR, close, r])
  obtain ⟨diteFalseL', _, hditeFalseL, _⟩ := mem diteFalseL (by simp [Condition.natLEEvidenceExpressions, diteFalseL, close, r])
  obtain ⟨diteFalseR', _, hditeFalseR, _⟩ := mem diteFalseR (by simp [Condition.natLEEvidenceExpressions, diteFalseR, close, r])
  obtain ⟨reflectFn', _, hreflect, _⟩ :=
    mem Condition.natLEReflectedFn (by simp [Condition.natLEEvidenceExpressions])
  obtain ⟨decide', _, hdecide, _⟩ :=
    mem Condition.natLEDecideFn (by simp [Condition.natLEEvidenceExpressions])
  obtain ⟨decideTy', _, hdecideTy, _⟩ :=
    mem q(Nat → Nat → Bool) (by simp [Condition.natLEEvidenceExpressions])
  obtain ⟨asBool', _, hasBool, _⟩ := mem q(Nat.ble) (by simp [Condition.natLEEvidenceExpressions])
  obtain ⟨proof', _, hproof, _⟩ :=
    mem Condition.natLEReflectProof (by simp [Condition.natLEEvidenceExpressions])
  have hrtypeUnique : TrExprS.IsUnique Reflection.defn₁.type := by
    simp [TrExprS.IsUnique, Reflection.defn₁, Expr.lam0, Expr.arrow,
      mkApp5, mkApp4, mkApp3, mkApp2, mkApp]
  have hiteUnique : TrExprS.IsUnique Reflection.defn₁.ite := by
    simp [TrExprS.IsUnique, Reflection.defn₁, Reflection.ite,
      Expr.lam0, Expr.arrow, mkApp5, mkApp4, mkApp3, mkApp2, mkApp]
  have hnotUnique : TrExprS.IsUnique q(Not) := by trivial
  have hditeUnique : TrExprS.IsUnique Reflection.defn₁.natDITE := by
    simp [TrExprS.IsUnique, Reflection.defn₁, Reflection.natDITE,
      Expr.lam0, Expr.arrow, mkApp5, mkApp4, mkApp3, mkApp2, mkApp]
  have hofTrueUnique : TrExprS.IsUnique Reflection.defn₁.ofTrue := by
    simp [TrExprS.IsUnique, Reflection.defn₁, Expr.lam0, Expr.arrow,
      mkApp5, mkApp4, mkApp3, mkApp2, mkApp]
  have hofFalseUnique : TrExprS.IsUnique Reflection.defn₁.ofFalse := by
    simp [TrExprS.IsUnique, Reflection.defn₁, Expr.lam0, Expr.arrow,
      mkApp5, mkApp4, mkApp3, mkApp2, mkApp]
  have hraw := Condition.natLE.check.WF (s := s') (fail := fail)
    hlparams hvlctx
    hdec hprop hpropTy hrtype hrtypeUnique hrtypeCanon
    hite hiteUnique hiteTy hiteTrueL hiteTrueR hiteFalseL hiteFalseR
    hnot hnotUnique hnotTy hdite hditeUnique hditeTy
    hofTrue hofTrueUnique hofTrueTy hofFalse hofFalseUnique hofFalseTy
    hditeTrueL hditeTrueR hditeFalseL hditeFalseR hreflect hdecide
    hdecideTy hasBool hdecideTy hproof hfail
  exact (Condition.natLE.check.WF.selector hlparams hvlctx
    hrtype hite hdite hofTrue hofFalse
    hrtypeUnique hiteUnique hditeUnique hofTrueUnique hofFalseUnique
    hiteTy hditeTy hraw).mono
      fun _ _ _ ⟨selector, _⟩ => ⟨selector, trivial⟩

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
    env.IsDefEqU 0 [] bleV (.boolLit (Nat.ble a b)) :=
  Condition.reflectsNatNatBool_application_eval wf hbleR hctors hbleC
    (hctors.natLitS a (Us := []) (Δ := [])).1
    (hctors.natLitS b (Us := []) (Δ := [])).1 hbleS

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
  cases (hctors.natLitS a (Us := []) (Δ := [])).1 with
  | lit _ haS =>
    cases (hctors.natLitS b (Us := []) (Δ := [])).1 with
    | lit _ hbS =>
      exact Condition.reflectsNatNatBool_application_eval wf hbleR hctors
        hbleC haS hbS hbleS

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
    env.IsDefEqU 0 [] bleV (.boolLit (Nat.ble a b)) :=
  Condition.reflectsNatNatBool_application_eval wf hbleR hctors hbleC
    haS hbS hbleS

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
  have hbool := Condition.natBLE_application_eval wf hbleR hctors hbleC hbleS
  rw [hble] at hbool
  exact VEnv.reflectionNatDITE_true_of_condition wf
    (TrExprS.target_closed wf cert.rtypeS)
    (TrExprS.target_closed wf cert.rditeS)
    (TrExprS.target_closed wf cert.ofTrueS)
    (cert.dite_equations wf).1 cert.rditeHas hcallT hbool

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
  have hbool := Condition.natBLE_application_eval wf hbleR hctors hbleC hbleS
  rw [hble] at hbool
  exact VEnv.reflectionNatDITE_false_of_condition wf
    (TrExprS.target_closed wf cert.rtypeS)
    (TrExprS.target_closed wf cert.rditeS)
    (TrExprS.target_closed wf cert.ofFalseS)
    (cert.dite_equations wf).2 cert.rditeHas hcallT hbool

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
