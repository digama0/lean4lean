import Lean4Lean.Verify.BitwiseTransitions

namespace Lean4Lean.Environment
open Lean VEnv

@[simp] private theorem Nat.decide_eq_beq (a b : Nat) :
    decide (a = b) = (a == b) := rfl

/-- The recursive-call subterm of the expected successor right-hand side,
under the five equation binders. -/
private def succRecCall (r : NatBitwiseFixCertificate) : Expr :=
  mkAppN r.callFn #[.bvar 4, .bvar 3,
    mkApp2 q(Nat.div) (mkApp q(Nat.succ) (.bvar 2))
      (mkApp q(Nat.succ) (mkApp q(Nat.succ) q(Nat.zero))),
    mkApp2 q(Nat.div) (mkApp q(Nat.succ) (.bvar 1))
      (mkApp q(Nat.succ) (mkApp q(Nat.succ) q(Nat.zero))),
    r.succProof]

/-- The body of the expected successor right-hand side under its five
binders: a `boolNatITE` selection between the doubled recursive result and
its successor, conditioned on the two bit tests. -/
private def succRhsBody (r : NatBitwiseFixCertificate) : Expr :=
  mkApp3 Condition.bool.boolNatITE
    (mkApp2 (.bvar 4)
      (Condition.natEq.decide #[mkApp2 q(Nat.mod)
        (mkApp q(Nat.succ) (.bvar 2))
        (mkApp q(Nat.succ) (mkApp q(Nat.succ) q(Nat.zero))),
        mkApp q(Nat.succ) q(Nat.zero)])
      (Condition.natEq.decide #[mkApp2 q(Nat.mod)
        (mkApp q(Nat.succ) (.bvar 1))
        (mkApp q(Nat.succ) (mkApp q(Nat.succ) q(Nat.zero))),
        mkApp q(Nat.succ) q(Nat.zero)]))
    (mkApp2 q(Nat.add)
      (mkApp2 q(Nat.add) (succRecCall r) (succRecCall r))
      (mkApp q(Nat.succ) q(Nat.zero)))
    (mkApp2 q(Nat.add) (succRecCall r) (succRecCall r))

set_option linter.unusedSimpArgs false in
/-- Process the left side of a certified successor equation: relate the
translated call spine to the closed certificate call at successor
literals, evaluate the three successor applications, and discharge the
trailing dependent proof binder, converting the checked equation into a
root-level equality between the candidate expression and the instantiated
right-hand body. -/
private theorem succ_lhs_equation {env : VEnv} (wf : env.WF)
    (hctors : Lean4Lean.Environment.VEnv.HasNatBoolConstructors env)
    {r : NatBitwiseFixCertificate}
    {funTyL natTyL₁ natTyL₂ natTyL₃ proofTyL bodyLFinal : VExpr}
    {proofTyR bodyRFinal : VExpr}
    {op callV fuelV hpV e A : VExpr} {fuel a b : Nat}
    (hfunTyL : env.IsType 0 [] funTyL)
    (hnatTyL₁ : env.IsType 0 [funTyL] natTyL₁)
    (hnatTyL₂ : env.IsType 0 [natTyL₁, funTyL] natTyL₂)
    (hnatTyL₃ : env.IsType 0 [natTyL₂, natTyL₁, funTyL] natTyL₃)
    (hproofTyL : env.IsType 0 [natTyL₃, natTyL₂, natTyL₁, funTyL] proofTyL)
    (hopL : env.HasType 0 [] op funTyL)
    (hfL : env.HasType 0 [] (.natLit fuel) (natTyL₁.inst op))
    (haL : env.HasType 0 [] (.natLit a)
      ((natTyL₂.inst op 1).inst (.natLit fuel)))
    (hbL : env.HasType 0 [] (.natLit b)
      (((natTyL₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a)))
    (hfT : env.HasType 0 [] (.natLit fuel) .nat)
    (haT : env.HasType 0 [] (.natLit a) .nat)
    (hbT : env.HasType 0 [] (.natLit b) .nat)
    (hbodyL : TrExprS env []
      [(none, .vlam proofTyL), (none, .vlam natTyL₃),
        (none, .vlam natTyL₂), (none, .vlam natTyL₁),
        (none, .vlam funTyL)]
      (mkAppN r.callFn #[.bvar 4, mkApp q(Nat.succ) (.bvar 3),
        mkApp q(Nat.succ) (.bvar 2), mkApp q(Nat.succ) (.bvar 1),
        .bvar 0])
      bodyLFinal)
    (hprefixEq : env.IsDefEqU 0 []
      (.lam ((((proofTyL.inst op 3).inst (.natLit fuel) 2).inst
        (.natLit a) 1).inst (.natLit b))
        ((((bodyLFinal.inst op 4).inst (.natLit fuel) 3).inst
          (.natLit a) 2).inst (.natLit b) 1))
      (.lam ((((proofTyR.inst op 3).inst (.natLit fuel) 2).inst
        (.natLit a) 1).inst (.natLit b))
        ((((bodyRFinal.inst op 4).inst (.natLit fuel) 3).inst
          (.natLit a) 2).inst (.natLit b) 1)))
    (hcallS : TrExprS env [] [] r.callFn callV)
    (hfuelEq : env.IsDefEqU 0 [] fuelV (.natLit (fuel + 1)))
    (heCall : env.IsDefEqU 0 [] e
      (.app (.app (.app (.app (.app callV op) fuelV)
        (.natLit (a + 1))) (.natLit (b + 1))) hpV))
    (heT : env.HasType 0 [] e A) :
    env.HasType 0 [] hpV
      ((((proofTyR.inst op 3).inst (.natLit fuel) 2).inst
        (.natLit a) 1).inst (.natLit b)) ∧
    env.IsDefEqU 0 [] e
      (((((bodyRFinal.inst op 4).inst (.natLit fuel) 3).inst
        (.natLit a) 2).inst (.natLit b) 1).inst hpV) := by
  have hcallExprT := (heCall.of_l wf trivial heT).hasType.2
  obtain ⟨hpType, _, hprefixCallT, hpT⟩ :=
    hcallExprT.app_inv wf.ordered trivial
  obtain ⟨_, _, hprefixBT, hbArgT⟩ :=
    hprefixCallT.app_inv wf.ordered trivial
  obtain ⟨_, _, hprefixAT, haArgT⟩ :=
    hprefixBT.app_inv wf.ordered trivial
  obtain ⟨_, _, hprefixFuelT, hfuelT⟩ :=
    hprefixAT.app_inv wf.ordered trivial
  obtain ⟨_, _, hcallVT, hopArgT⟩ :=
    hprefixFuelT.app_inv wf.ordered trivial
  have hcallVClosed : callV.ClosedN :=
    (hcallVT.closedN' wf.ordered.closed trivial).1
  have hbodyLS := hbodyL
  cases hbodyL with
  | @app prefixLocal _ _ hpLocal _ _ _ _ _ hprefixLocalS hpLocalS =>
    cases hprefixLocalS with
    | @app prefixB _ _ succB _ _ _ _ _ hprefixBS hsuccBS =>
      cases hsuccBS with
      | @app succLocalB _ _ bLocal _ _ _ _ _ hsuccLocalBS hbLocalS =>
        cases hprefixBS with
        | @app prefixA _ _ succA _ _ _ _ _ hprefixAS hsuccAS =>
          cases hsuccAS with
          | @app succLocalA _ _ aLocal _ _ _ _ _ hsuccLocalAS haLocalS =>
            cases hprefixAS with
            | @app prefixFuel _ _ succFuel _ _ _ _ _ hprefixFuelS hsuccFuelS =>
              cases hsuccFuelS with
              | @app succLocalF _ _ fuelLocal _ _ _ _ _
                  hsuccLocalFS hfuelLocalS =>
                cases hprefixFuelS with
                | @app callLocal _ _ opLocal _ _ _ _ _ hcallLocalS hopLocalS =>
                  let ΔL : VLCtx :=
                    [(none, .vlam proofTyL), (none, .vlam natTyL₃),
                      (none, .vlam natTyL₂), (none, .vlam natTyL₁),
                      (none, .vlam funTyL)]
                  have hopCanon : TrExprS env [] ΔL (.bvar 4) (.bvar 4) :=
                    .bvar (by rfl)
                  have hfuelCanon : TrExprS env [] ΔL (.bvar 3) (.bvar 3) :=
                    .bvar (by rfl)
                  have haCanon : TrExprS env [] ΔL (.bvar 2) (.bvar 2) :=
                    .bvar (by rfl)
                  have hbCanon : TrExprS env [] ΔL (.bvar 1) (.bvar 1) :=
                    .bvar (by rfl)
                  have hpCanon : TrExprS env [] ΔL (.bvar 0) (.bvar 0) :=
                    .bvar (by rfl)
                  have hsuccCanon :=
                    (hctors.natSuccS (Us := []) (Δ := ΔL)).1
                  cases hopLocalS.unique (by trivial) hopCanon
                  cases hfuelLocalS.unique (by trivial) hfuelCanon
                  cases haLocalS.unique (by trivial) haCanon
                  cases hbLocalS.unique (by trivial) hbCanon
                  cases hpLocalS.unique (by trivial) hpCanon
                  have hctxL : VLCtx.IsDefEq env 0 ΔL ΔL :=
                    .refl wf ⟨⟨⟨⟨⟨trivial, nofun, hfunTyL⟩,
                      nofun, hnatTyL₁⟩, nofun, hnatTyL₂⟩,
                      nofun, hnatTyL₃⟩, nofun, hproofTyL⟩
                  have hcallEqCtx := TrExprS.uniq (Us := []) wf hctxL
                    hcallLocalS (bitwise_weak5 wf hcallS)
                  have hsuccBEqCtx := TrExprS.uniq (Us := []) wf hctxL
                    hsuccLocalBS hsuccCanon
                  have hsuccAEqCtx := TrExprS.uniq (Us := []) wf hctxL
                    hsuccLocalAS hsuccCanon
                  have hsuccFEqCtx := TrExprS.uniq (Us := []) wf hctxL
                    hsuccLocalFS hsuccCanon
                  have hsuccT :=
                    (hctors.natSuccS (Us := []) (Δ := [])).2
                  have hsuccClosed : VExpr.natSucc.ClosedN :=
                    (hsuccT.closedN' wf.ordered.closed trivial).1
                  let proofTyLF :=
                    (((proofTyL.inst op 3).inst (.natLit fuel) 2).inst
                      (.natLit a) 1).inst (.natLit b)
                  let callFinal :=
                    (((callLocal.inst op 4).inst (.natLit fuel) 3).inst
                      (.natLit a) 2).inst (.natLit b) 1
                  let succBFinal :=
                    (((succLocalB.inst op 4).inst (.natLit fuel) 3).inst
                      (.natLit a) 2).inst (.natLit b) 1
                  let succAFinal :=
                    (((succLocalA.inst op 4).inst (.natLit fuel) 3).inst
                      (.natLit a) 2).inst (.natLit b) 1
                  let succFFinal :=
                    (((succLocalF.inst op 4).inst (.natLit fuel) 3).inst
                      (.natLit a) 2).inst (.natLit b) 1
                  have hcallEqFinal : env.IsDefEqU 0 [proofTyLF]
                      callFinal callV := by
                    simpa [proofTyLF, callFinal] using
                      bitwise_local_closed_eq4 wf hopL hfL haL hbL
                        hcallVClosed (by simpa [ΔL] using hcallEqCtx)
                  have hsuccBEqFinal : env.IsDefEqU 0 [proofTyLF]
                      succBFinal .natSucc := by
                    simpa [proofTyLF, succBFinal] using
                      bitwise_local_closed_eq4 wf hopL hfL haL hbL
                        hsuccClosed (by simpa [ΔL] using hsuccBEqCtx)
                  have hsuccAEqFinal : env.IsDefEqU 0 [proofTyLF]
                      succAFinal .natSucc := by
                    simpa [proofTyLF, succAFinal] using
                      bitwise_local_closed_eq4 wf hopL hfL haL hbL
                        hsuccClosed (by simpa [ΔL] using hsuccAEqCtx)
                  have hsuccFEqFinal : env.IsDefEqU 0 [proofTyLF]
                      succFFinal .natSucc := by
                    simpa [proofTyLF, succFFinal] using
                      bitwise_local_closed_eq4 wf hopL hfL haL hbL
                        hsuccClosed (by simpa [ΔL] using hsuccFEqCtx)
                  obtain ⟨_, hbodyLT⟩ := hbodyLS.wf wf.ordered
                    (Us := []) (Δ := ΔL) hctxL.wf
                  have hbodyLocalFinalT₀ :=
                    VEnv.HasType.inst_bitwise_outer4 wf hopL hfL haL hbL
                      (by simpa [ΔL] using hbodyLT.hasType.1)
                  have hopClosed : op.ClosedN :=
                    (hopL.closedN' wf.ordered.closed trivial).1
                  have hfClosed : (VExpr.natLit fuel).ClosedN :=
                    (hfT.closedN' wf.ordered.closed trivial).1
                  have haClosed : (VExpr.natLit a).ClosedN :=
                    (haT.closedN' wf.ordered.closed trivial).1
                  have hbClosed : (VExpr.natLit b).ClosedN :=
                    (hbT.closedN' wf.ordered.closed trivial).1
                  have hbodyLocalFinalT := hbodyLocalFinalT₀
                  simp [proofTyLF, callFinal, succBFinal, succAFinal,
                    succFFinal, hopClosed.liftN_eq, hopClosed.instN_eq,
                    hfClosed.liftN_eq, hfClosed.instN_eq,
                    haClosed.liftN_eq, haClosed.instN_eq,
                    hbClosed.liftN_eq, hbClosed.instN_eq,
                    VExpr.inst] at hbodyLocalFinalT
                  have hΓ : OnCtx [proofTyLF] (env.IsType 0) := by
                    obtain ⟨_, hEqD⟩ := hprefixEq
                    exact ⟨trivial, (hEqD.hasType.1.lam_inv wf trivial).1⟩
                  obtain ⟨prefixArgTy, prefixBodyTy,
                      hprefixLocalFinalT, hproofVarFinalT⟩ :=
                    VEnv.HasType.app_inv wf.ordered hΓ hbodyLocalFinalT
                  obtain ⟨_, _, hprefixBeforeBT, hsuccBLocalT⟩ :=
                    hprefixLocalFinalT.app_inv wf.ordered hΓ
                  obtain ⟨_, _, hprefixBeforeAT, hsuccALocalT⟩ :=
                    hprefixBeforeBT.app_inv wf.ordered hΓ
                  obtain ⟨_, _, hprefixBeforeFuelT, hsuccFLocalT⟩ :=
                    hprefixBeforeAT.app_inv wf.ordered hΓ
                  obtain ⟨_, _, hcallFinalT, hopLocalT⟩ :=
                    hprefixBeforeFuelT.app_inv wf.ordered hΓ
                  have hcallAppEq := hcallEqFinal.app_same wf hΓ
                    hcallFinalT hopLocalT
                  have hsuccBAppEq := hsuccBEqFinal.app_same wf hΓ
                    ((hsuccBEqFinal.of_r wf hΓ
                      (hsuccT.weak0 wf)).hasType.1) (hbT.weak0 wf)
                  have hsuccAAppEq := hsuccAEqFinal.app_same wf hΓ
                    ((hsuccAEqFinal.of_r wf hΓ
                      (hsuccT.weak0 wf)).hasType.1) (haT.weak0 wf)
                  have hsuccFAppEq := hsuccFEqFinal.app_same wf hΓ
                    ((hsuccFEqFinal.of_r wf hΓ
                      (hsuccT.weak0 wf)).hasType.1) (hfT.weak0 wf)
                  have hsuccBEval : env.IsDefEqU 0 [proofTyLF]
                      (.app succBFinal (.natLit b)) (.natLit (b + 1)) := by
                    simpa [VExpr.natLit] using hsuccBAppEq
                  have hsuccAEval : env.IsDefEqU 0 [proofTyLF]
                      (.app succAFinal (.natLit a)) (.natLit (a + 1)) := by
                    simpa [VExpr.natLit] using hsuccAAppEq
                  have hsuccFEval : env.IsDefEqU 0 [proofTyLF]
                      (.app succFFinal (.natLit fuel))
                      (.natLit (fuel + 1)) := by
                    simpa [VExpr.natLit] using hsuccFAppEq
                  have hprefixLocalFinalT' := hprefixLocalFinalT
                  have hprefixBeforeBT' := hprefixBeforeBT
                  have hprefixBeforeAT' := hprefixBeforeAT
                  have hprefixBeforeFuelT' := hprefixBeforeFuelT
                  have hsuccBLocalT' := hsuccBLocalT
                  have hsuccALocalT' := hsuccALocalT
                  have hsuccFLocalT' := hsuccFLocalT
                  simp [callFinal, succBFinal, succAFinal, succFFinal,
                    VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.liftN,
                    liftVar, hfClosed.liftN_eq, hfClosed.instN_eq,
                    haClosed.liftN_eq, haClosed.instN_eq,
                    hbClosed.liftN_eq, hbClosed.instN_eq] at hprefixLocalFinalT' hprefixBeforeBT' hprefixBeforeAT' hprefixBeforeFuelT' hsuccBLocalT' hsuccALocalT' hsuccFLocalT'
                  have hprefixFuelEq := hcallAppEq.app_both wf hΓ
                    hsuccFEval hprefixBeforeFuelT' hsuccFLocalT'
                  have hprefixAEq := hprefixFuelEq.app_both wf hΓ
                    hsuccAEval hprefixBeforeAT' hsuccALocalT'
                  have hprefixLocalEq := hprefixAEq.app_both wf hΓ
                    hsuccBEval hprefixBeforeBT' hsuccBLocalT'
                  have hrelFuelEq := hfuelEq.app_arg wf trivial
                    hprefixFuelT hfuelT
                  have hrelAEq := hrelFuelEq.app_same wf trivial
                    hprefixAT haArgT
                  have hrelPrefixEq := hrelAEq.app_same wf trivial
                    hprefixBT hbArgT
                  have hlocalRelEq := hprefixLocalEq.trans wf hΓ
                    (hrelPrefixEq.weak0 (Γ := [proofTyLF]) wf).symm
                  have hlamEq : env.IsDefEqU 0 []
                      (.lam proofTyLF
                        (.app
                          (.app (.app (.app (callFinal.app op)
                            (succFFinal.app (.natLit fuel)))
                            (succAFinal.app (.natLit a)))
                            (succBFinal.app (.natLit b)))
                          (.bvar 0)))
                      (.lam
                        ((((proofTyR.inst op 3).inst (.natLit fuel) 2).inst
                          (.natLit a) 1).inst (.natLit b))
                        ((((bodyRFinal.inst op 4).inst (.natLit fuel) 3).inst
                          (.natLit a) 2).inst (.natLit b) 1)) := by
                    simpa [proofTyLF, callFinal, succBFinal, succAFinal,
                      succFFinal, VExpr.inst, VExpr.instVar,
                      hopClosed.liftN_eq, hopClosed.instN_eq,
                      hfClosed.liftN_eq, hfClosed.instN_eq,
                      haClosed.liftN_eq, haClosed.instN_eq,
                      hbClosed.liftN_eq, hbClosed.instN_eq] using hprefixEq
                  obtain ⟨hpTR, hfinish⟩ :=
                    VEnv.finish_bitwise_proof_equation wf
                      (hproofTyL := hΓ.2)
                      hprefixLocalFinalT' hproofVarFinalT
                      hprefixCallT hpT hlocalRelEq hlamEq
                  exact ⟨hpTR, heCall.trans wf trivial hfinish⟩

set_option linter.unusedSimpArgs false in
/-- Process the right side of a certified successor equation: evaluate the
two bit tests through the reflected decision function and `Nat.mod`,
canonicalize the recursive call at evaluated `Nat.div` arguments, and
derive the successor transition's continuation from the reflected
`boolNatITE` structure and the reflected `Nat.add` reassembly. -/
private theorem succ_rhs_semantics {env : VEnv} (wf : env.WF)
    (hctors : Lean4Lean.Environment.VEnv.HasNatBoolConstructors env)
    {r : NatBitwiseFixCertificate}
    (haddC : env.contains ``Nat.add)
    (hmodC : env.contains ``Nat.mod)
    (hdivC : env.contains ``Nat.div)
    (hadd : env.ReflectsNatNatNat ``Nat.add Nat.add)
    (hmod : env.ReflectsNatNatNat ``Nat.mod Nat.mod)
    (hdiv : env.ReflectsNatNatNat ``Nat.div Nat.div)
    {decide ite : VExpr}
    (hdecideS : TrExprS env [] [] Condition.natEqDecideFn decide)
    (hdecide : Lean4Lean.Environment.VEnv.ReflectsNatEqDecide env decide)
    (hiteS : TrExprS env [] [] Condition.bool.boolNatITE ite)
    (hite : env.ReflectsBoolNatITE ite)
    {op : VExpr} {f : Bool → Bool → Bool}
    (hop : env.ReflectsBoolBin op f)
    {funTyR natTyR₁ natTyR₂ natTyR₃ proofTyR bodyRFinal : VExpr}
    {callV hpV e A : VExpr} {fuel a b : Nat}
    (hfunTyR : env.IsType 0 [] funTyR)
    (hnatTyR₁ : env.IsType 0 [funTyR] natTyR₁)
    (hnatTyR₂ : env.IsType 0 [natTyR₁, funTyR] natTyR₂)
    (hnatTyR₃ : env.IsType 0 [natTyR₂, natTyR₁, funTyR] natTyR₃)
    (hproofTyR : env.IsType 0 [natTyR₃, natTyR₂, natTyR₁, funTyR] proofTyR)
    (hnatEqR₂ : env.IsDefEqU 0 [natTyR₁, funTyR] natTyR₂ .nat)
    (hnatEqR₃ : env.IsDefEqU 0 [natTyR₂, natTyR₁, funTyR] natTyR₃ .nat)
    (hopR : env.HasType 0 [] op funTyR)
    (hfR : env.HasType 0 [] (.natLit fuel) (natTyR₁.inst op))
    (haR : env.HasType 0 [] (.natLit a)
      ((natTyR₂.inst op 1).inst (.natLit fuel)))
    (hbR : env.HasType 0 [] (.natLit b)
      (((natTyR₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a)))
    (hfT : env.HasType 0 [] (.natLit fuel) .nat)
    (hbodyR : TrExprS env []
      [(none, .vlam proofTyR), (none, .vlam natTyR₃),
        (none, .vlam natTyR₂), (none, .vlam natTyR₁),
        (none, .vlam funTyR)]
      (succRhsBody r) bodyRFinal)
    (hcallS : TrExprS env [] [] r.callFn callV)
    (hpTR : env.HasType 0 [] hpV
      ((((proofTyR.inst op 3).inst (.natLit fuel) 2).inst
        (.natLit a) 1).inst (.natLit b)))
    (hcallToRight : env.IsDefEqU 0 [] e
      (((((bodyRFinal.inst op 4).inst (.natLit fuel) 3).inst
        (.natLit a) 2).inst (.natLit b) 1).inst hpV))
    (heT : env.HasType 0 [] e A) :
    ∃ e', VEnv.BitwiseGoCall env r op fuel
        ((a + 1) / 2) ((b + 1) / 2) e' ∧
      env.IsDefEqU 0 [] e' e' ∧
      ∀ q, env.IsDefEqU 0 [] e' (.natLit q) →
        env.IsDefEqU 0 []
          e (.natLit (if f ((a + 1) % 2 = 1) ((b + 1) % 2 = 1)
            then q + q + 1 else q + q)) := by
  cases hbodyR with
  | @app iteTwo _ _ elseLocal _ _ _ _ _ hiteTwoS helseLocalS =>
    cases hiteTwoS with
    | @app iteOne _ _ thenLocal _ _ _ _ _ hiteOneS hthenLocalS =>
      cases hiteOneS with
      | @app iteLocal _ _ condLocal _ _ _ _ _ hiteLocalS hcondLocalS =>
        cases hcondLocalS with
        | @app opBitOne _ _ bitTwoLocal _ _ _ _ _ hopBitOneS hbitTwoLocalS =>
          cases hopBitOneS with
          | @app opLocalR _ _ bitOneLocal _ _ _ _ _ hopLocalRS hbitOneLocalS =>
            let ΔR : VLCtx :=
              [(none, .vlam proofTyR), (none, .vlam natTyR₃),
                (none, .vlam natTyR₂), (none, .vlam natTyR₁),
                (none, .vlam funTyR)]
            have hctxR : VLCtx.IsDefEq env 0 ΔR ΔR :=
              .refl wf ⟨⟨⟨⟨⟨trivial, nofun, hfunTyR⟩,
                nofun, hnatTyR₁⟩, nofun, hnatTyR₂⟩,
                nofun, hnatTyR₃⟩, nofun, hproofTyR⟩
            have hopCanonR : TrExprS env [] ΔR (.bvar 4) (.bvar 4) :=
              .bvar (by rfl)
            cases hopLocalRS.unique (by trivial) hopCanonR
            -- `Nat` typing for the two state bound variables.
            have hnatEqAR : env.IsDefEqU 0 ΔR.toCtx
                natTyR₂.lift.lift.lift .nat := by
              have h := (VEnv.IsDefEqU.weakN_iff wf
                hctxR.wf.toCtx
                (.zero [proofTyR, natTyR₃, natTyR₂] :
                  Ctx.LiftN 3 0 [natTyR₁, funTyR] ΔR.toCtx)).2 hnatEqR₂
              rw [VExpr.liftN_succ, VExpr.liftN_succ,
                VExpr.liftN_succ] at h
              simpa only [ΔR, VExpr.lift, VExpr.liftN_zero,
                VExpr.liftN_nat] using h
            have hnatEqBR : env.IsDefEqU 0 ΔR.toCtx
                natTyR₃.lift.lift .nat := by
              have h := (VEnv.IsDefEqU.weakN_iff wf
                hctxR.wf.toCtx
                (.zero [proofTyR, natTyR₃] :
                  Ctx.LiftN 2 0 [natTyR₂, natTyR₁, funTyR] ΔR.toCtx)).2
                hnatEqR₃
              rw [VExpr.liftN_succ, VExpr.liftN_succ] at h
              simpa only [ΔR, VExpr.lift, VExpr.liftN_zero,
                VExpr.liftN_nat] using h
            have haVarT : env.HasType 0 ΔR.toCtx (.bvar 2) .nat := by
              have hv : env.HasType 0 ΔR.toCtx (.bvar 2)
                  natTyR₂.lift.lift.lift := .bvar (.succ (.succ .zero))
              exact hv.defeqU_r wf hctxR.wf.toCtx hnatEqAR
            have hbVarT : env.HasType 0 ΔR.toCtx (.bvar 1) .nat := by
              have hv : env.HasType 0 ΔR.toCtx (.bvar 1)
                  natTyR₃.lift.lift := .bvar (.succ .zero)
              exact hv.defeqU_r wf hctxR.wf.toCtx hnatEqBR
            have haVarS : TrExprS env [] ΔR (.bvar 2) (.bvar 2) :=
              .bvar (by rfl)
            have hbVarS : TrExprS env [] ΔR (.bvar 1) (.bvar 1) :=
              .bvar (by rfl)
            -- Evaluate the two bit tests.
            have honeSR : TrExprS env [] ΔR
                (mkApp q(Nat.succ) q(Nat.zero)) (.natLit 1) :=
              .app (hctors.natSuccS (Us := []) (Δ := ΔR)).2
                (hctors.natZeroS (Us := []) (Δ := ΔR)).2
                (hctors.natSuccS (Us := []) (Δ := ΔR)).1
                (hctors.natZeroS (Us := []) (Δ := ΔR)).1
            have honeTR := (hctors.natLitS 1 (Us := []) (Δ := ΔR)).2
            obtain ⟨hmodAS, hmodAT⟩ :=
              VEnv.ReflectsNatNatNat.succ_two_canonS wf hctors hmod hmodC
                haVarS haVarT
            obtain ⟨hmodBS, hmodBT⟩ :=
              VEnv.ReflectsNatNatNat.succ_two_canonS wf hctors hmod hmodC
                hbVarS hbVarT
            have hdecideWeak' : TrExprS env [] ΔR
                Condition.natEqDecideFn (decide.liftN 5) :=
              bitwise_weak5 wf hdecideS
            have hbitOneCallEqCtx :=
              Condition.natEqDecideFn.call_eq wf hctxR.wf
                hdecideWeak' hmodAS honeSR hmodAT honeTR hbitOneLocalS
            have hbitTwoCallEqCtx :=
              Condition.natEqDecideFn.call_eq wf hctxR.wf
                hdecideWeak' hmodBS honeSR hmodBT honeTR hbitTwoLocalS
            have hiteEqCtx := TrExprS.uniq (Us := []) wf hctxR
              hiteLocalS (bitwise_weak5 wf hiteS)
            have hiteClosed : ite.ClosedN :=
              (hite.1.closedN' wf.ordered.closed trivial).1
            have hopClosed : op.ClosedN :=
              (hopR.closedN' wf.ordered.closed trivial).1
            have hfClosed : (VExpr.natLit fuel).ClosedN :=
              (hfT.closedN' wf.ordered.closed trivial).1
            let closeOuter (x : VExpr) : VExpr :=
              ((((x.inst op 4).inst (.natLit fuel) 3).inst
                (.natLit a) 2).inst (.natLit b) 1).inst hpV
            let iteFinal := closeOuter iteLocal
            let bitOneFinal := closeOuter bitOneLocal
            let bitTwoFinal := closeOuter bitTwoLocal
            let thenFinal := closeOuter thenLocal
            let elseFinal := closeOuter elseLocal
            have hiteEqRoot : env.IsDefEqU 0 [] iteFinal ite :=
              bitwise_root_closed_eq wf hopR hfR haR hbR hpTR
                hiteClosed (by simpa [ΔR] using hiteEqCtx)
            have hdecideClosed : decide.ClosedN :=
              (hdecide.1.closedN' wf.ordered.closed trivial).1
            have hbitOneCallEqRoot₀ := bitwise_root_eq wf hopR hfR haR
              hbR hpTR (by simpa [ΔR] using hbitOneCallEqCtx)
            have hbitTwoCallEqRoot₀ := bitwise_root_eq wf hopR hfR haR
              hbR hpTR (by simpa [ΔR] using hbitTwoCallEqCtx)
            have hbitOneCallEqRoot : env.IsDefEqU 0 [] bitOneFinal
                (.app (.app decide
                  (.app (.app (.const ``Nat.mod [])
                    (.natLit (a + 1))) (.natLit 2)))
                  (.natLit 1)) := by
              simpa [bitOneFinal, closeOuter, VExpr.inst, VExpr.instVar,
                VExpr.natLit, hdecideClosed.liftN_eq,
                hdecideClosed.instN_eq] using hbitOneCallEqRoot₀
            have hbitTwoCallEqRoot : env.IsDefEqU 0 [] bitTwoFinal
                (.app (.app decide
                  (.app (.app (.const ``Nat.mod [])
                    (.natLit (b + 1))) (.natLit 2)))
                  (.natLit 1)) := by
              simpa [bitTwoFinal, closeOuter, VExpr.inst, VExpr.instVar,
                VExpr.natLit, hdecideClosed.liftN_eq,
                hdecideClosed.instN_eq] using hbitTwoCallEqRoot₀
            have honeRootT := (hctors.natLitS 1 (Us := []) (Δ := [])).2
            have htwoRootT := (hctors.natLitS 2 (Us := []) (Δ := [])).2
            have ⟨hmodT, hmodEval⟩ := hmod hmodC
            have hmodACallT : env.HasType 0 []
                (.app (.app (.const ``Nat.mod []) (.natLit (a + 1)))
                  (.natLit 2)) .nat :=
              .app (.app (hmodT 0 [])
                (hctors.natLitS (a + 1) (Us := []) (Δ := [])).2) htwoRootT
            have hmodBCallT : env.HasType 0 []
                (.app (.app (.const ``Nat.mod []) (.natLit (b + 1)))
                  (.natLit 2)) .nat :=
              .app (.app (hmodT 0 [])
                (hctors.natLitS (b + 1) (Us := []) (Δ := [])).2) htwoRootT
            have hdecideAArgsEq := ((hmodEval (a + 1) 2).app_arg wf
              trivial hdecide.1 hmodACallT).app_same wf trivial
              (.app hdecide.1 hmodACallT) honeRootT
            have hdecideBArgsEq := ((hmodEval (b + 1) 2).app_arg wf
              trivial hdecide.1 hmodBCallT).app_same wf trivial
              (.app hdecide.1 hmodBCallT) honeRootT
            have hbitOneEval : env.IsDefEqU 0 [] bitOneFinal
                (.boolLit (((a + 1) % 2) == 1)) :=
              hbitOneCallEqRoot.trans wf trivial <|
                hdecideAArgsEq.trans wf trivial <|
                  hdecide.2 ((a + 1) % 2) 1
            have hbitTwoEval : env.IsDefEqU 0 [] bitTwoFinal
                (.boolLit (((b + 1) % 2) == 1)) :=
              hbitTwoCallEqRoot.trans wf trivial <|
                hdecideBArgsEq.trans wf trivial <|
                  hdecide.2 ((b + 1) % 2) 1
            -- The `Nat.add` reflection and the canonical then/else forms.
            have ⟨haddT, haddEval⟩ := hadd haddC
            obtain ⟨_, haddCi, _, haddLen⟩ :=
              (haddT 0 []).const_inv wf trivial
            have haddS : TrExprS env [] ΔR q(Nat.add)
                (.const ``Nat.add []) :=
              .const haddCi rfl (by simpa using haddLen)
            have helseLocalS₀ := helseLocalS
            cases helseLocalS with
            | @app elsePrefix _ _ recTwo _ _ _ _ _ helsePrefixS hrecTwoS =>
              have helsePrefixS₀ := helsePrefixS
              cases helsePrefixS with
              | @app addLocalElse _ _ recOne _ _ _ _ _
                  haddLocalElseS hrecOneS =>
                have haddEqCtx := TrExprS.uniq (Us := []) wf hctxR
                  haddLocalElseS haddS
                have haddLocalCanonT :=
                  (haddEqCtx.of_r wf hctxR.wf.toCtx
                    (haddT 0 ΔR.toCtx)).hasType.1
                obtain ⟨_, helsePrefixT⟩ := helsePrefixS₀.wf wf.ordered
                  (Us := []) (Δ := ΔR) hctxR.wf
                obtain ⟨_, _, haddLocalT, hrecOneT⟩ :=
                  helsePrefixT.hasType.1.app_inv wf.ordered hctxR.wf.toCtx
                have haddTypeEq := haddLocalT.uniqU wf hctxR.wf.toCtx
                  haddLocalCanonT
                obtain ⟨_, hrecTypeEq⟩ :=
                  (haddTypeEq.forallE_inv wf hctxR.wf.toCtx).1
                have hrecT := hrecOneT.defeqU_r wf hctxR.wf.toCtx
                  hrecTypeEq.toU
                have haddRecS : TrExprS env [] ΔR
                    (mkApp q(Nat.add) (succRecCall r))
                    (.app (.const ``Nat.add []) recOne) :=
                  .app (haddT 0 ΔR.toCtx) hrecT haddS hrecOneS
                have helseCanonS : TrExprS env [] ΔR
                    (mkApp2 q(Nat.add) (succRecCall r) (succRecCall r))
                    (.app (.app (.const ``Nat.add []) recOne) recOne) :=
                  .app (VEnv.HasType.app (haddT 0 ΔR.toCtx) hrecT) hrecT
                    haddRecS hrecOneS
                have helseEqCtx := TrExprS.uniq (Us := []) wf hctxR
                  helseLocalS₀ helseCanonS
                have hdoubleT : env.HasType 0 ΔR.toCtx
                    (.app (.app (.const ``Nat.add []) recOne) recOne)
                    .nat :=
                  .app (.app (haddT 0 ΔR.toCtx) hrecT) hrecT
                have haddDoubleS : TrExprS env [] ΔR
                    (mkApp q(Nat.add)
                      (mkApp2 q(Nat.add) (succRecCall r) (succRecCall r)))
                    (.app (.const ``Nat.add [])
                      (.app (.app (.const ``Nat.add []) recOne)
                        recOne)) :=
                  .app (haddT 0 ΔR.toCtx) hdoubleT haddS helseCanonS
                have hthenCanonS : TrExprS env [] ΔR
                    (mkApp2 q(Nat.add)
                      (mkApp2 q(Nat.add) (succRecCall r) (succRecCall r))
                      (mkApp q(Nat.succ) q(Nat.zero)))
                    (.app (.app (.const ``Nat.add [])
                      (.app (.app (.const ``Nat.add []) recOne) recOne))
                      (.natLit 1)) :=
                  .app (VEnv.HasType.app (haddT 0 ΔR.toCtx) hdoubleT)
                    honeTR haddDoubleS honeSR
                have hthenEqCtx := TrExprS.uniq (Us := []) wf hctxR
                  hthenLocalS hthenCanonS
                let recFinal := closeOuter recOne
                have helseEqRoot₀ := bitwise_root_eq wf hopR hfR haR hbR
                  hpTR helseEqCtx
                have hthenEqRoot₀ := bitwise_root_eq wf hopR hfR haR hbR
                  hpTR hthenEqCtx
                have helseEqRoot : env.IsDefEqU 0 [] elseFinal
                    (.app (.app (.const ``Nat.add []) recFinal)
                      recFinal) := by
                  simpa [elseFinal, recFinal, closeOuter, VExpr.inst,
                    VExpr.instVar] using helseEqRoot₀
                have hthenEqRoot : env.IsDefEqU 0 [] thenFinal
                    (.app (.app (.const ``Nat.add [])
                      (.app (.app (.const ``Nat.add []) recFinal)
                        recFinal)) (.natLit 1)) := by
                  simpa [thenFinal, recFinal, closeOuter, VExpr.inst,
                    VExpr.instVar] using hthenEqRoot₀
                -- Decompose the recursive call and evaluate its
                -- `Nat.div` arguments.
                have hrecOneS₀ := hrecOneS
                cases hrecOneS with
                | @app recPrefix _ _ proofLocal _ _ _ _ _
                    hrecPrefixS hproofLocalS =>
                  cases hrecPrefixS with
                  | @app recPrefixB _ _ divBLocal _ _ _ _ _
                      hrecPrefixBS hdivBLocalS =>
                    cases hrecPrefixBS with
                    | @app recPrefixA _ _ divALocal _ _ _ _ _
                        hrecPrefixAS hdivALocalS =>
                      cases hrecPrefixAS with
                      | @app recPrefixFuel _ _ fuelLocalR _ _ _ _ _
                          hrecPrefixFuelS hfuelLocalRS =>
                        cases hrecPrefixFuelS with
                        | @app callLocalR _ _ opLocalR₂ _ _ _ _ _
                            hcallLocalRS hopLocalR₂S =>
                          have hfuelCanonR : TrExprS env [] ΔR
                              (.bvar 3) (.bvar 3) := .bvar (by rfl)
                          cases hopLocalR₂S.unique (by trivial) hopCanonR
                          cases hfuelLocalRS.unique (by trivial) hfuelCanonR
                          have hcallEqCtxR := TrExprS.uniq (Us := []) wf
                            hctxR hcallLocalRS (bitwise_weak5 wf hcallS)
                          obtain ⟨_, hcallWF⟩ := hcallS.wf wf.ordered
                            (Us := []) (Δ := []) trivial
                          have hcallVClosed : callV.ClosedN :=
                            (hcallWF.hasType.1.closedN'
                              wf.ordered.closed trivial).1
                          have hcallEqRoot : env.IsDefEqU 0 []
                              (closeOuter callLocalR) callV :=
                            bitwise_root_closed_eq wf hopR hfR haR hbR
                              hpTR hcallVClosed
                              (by simpa [ΔR] using hcallEqCtxR)
                          obtain ⟨hdivAS, hdivAT⟩ :=
                            VEnv.ReflectsNatNatNat.succ_two_canonS wf
                              hctors hdiv hdivC haVarS haVarT
                          obtain ⟨hdivBS, hdivBT⟩ :=
                            VEnv.ReflectsNatNatNat.succ_two_canonS wf
                              hctors hdiv hdivC hbVarS hbVarT
                          have hdivAEqCtx := TrExprS.uniq (Us := []) wf
                            hctxR hdivALocalS hdivAS
                          have hdivBEqCtx := TrExprS.uniq (Us := []) wf
                            hctxR hdivBLocalS hdivBS
                          have ⟨hdivT, hdivEval⟩ := hdiv hdivC
                          have hdivAEqRoot₀ := bitwise_root_eq wf hopR
                            hfR haR hbR hpTR hdivAEqCtx
                          have hdivBEqRoot₀ := bitwise_root_eq wf hopR
                            hfR haR hbR hpTR hdivBEqCtx
                          have hdivAFinalEq : env.IsDefEqU 0 []
                              (closeOuter divALocal)
                              (.app (.app (.const ``Nat.div [])
                                (.natLit (a + 1))) (.natLit 2)) := by
                            simpa [closeOuter, VExpr.inst, VExpr.instVar,
                              VExpr.natLit] using hdivAEqRoot₀
                          have hdivBFinalEq : env.IsDefEqU 0 []
                              (closeOuter divBLocal)
                              (.app (.app (.const ``Nat.div [])
                                (.natLit (b + 1))) (.natLit 2)) := by
                            simpa [closeOuter, VExpr.inst, VExpr.instVar,
                              VExpr.natLit] using hdivBEqRoot₀
                          have hdivAEval := hdivAFinalEq.trans wf trivial
                            (hdivEval (a + 1) 2)
                          have hdivBEval := hdivBFinalEq.trans wf trivial
                            (hdivEval (b + 1) 2)
                          -- Reassemble the recursive call at the
                          -- evaluated arguments.
                          obtain ⟨_, hrecCtxWF⟩ := hrecOneS₀.wf wf.ordered
                            (Us := []) (Δ := ΔR) hctxR.wf
                          have hrecRootT :=
                            (VEnv.HasType.inst_bitwise_outer4 wf hopR hfR
                              haR hbR (by simpa [ΔR] using
                                hrecCtxWF.hasType.1)).instN wf.ordered
                              (.zero : Ctx.InstN [] hpV
                                ((((proofTyR.inst op 3).inst
                                  (.natLit fuel) 2).inst
                                  (.natLit a) 1).inst (.natLit b)) 0
                                [(((proofTyR.inst op 3).inst
                                  (.natLit fuel) 2).inst
                                  (.natLit a) 1).inst (.natLit b)] [])
                              hpTR
                          change env.HasType 0 [] recFinal _ at hrecRootT
                          obtain ⟨_, _, hrecPrefixBT, hproofFinalT⟩ :=
                            hrecRootT.app_inv wf.ordered trivial
                          obtain ⟨_, _, hrecPrefixAT, hdivBFinalT⟩ :=
                            hrecPrefixBT.app_inv wf.ordered trivial
                          obtain ⟨_, _, hrecPrefixFuelT, hdivAFinalT⟩ :=
                            hrecPrefixAT.app_inv wf.ordered trivial
                          obtain ⟨_, _, hrecPrefixOpT, hfuelFinalT⟩ :=
                            hrecPrefixFuelT.app_inv wf.ordered trivial
                          obtain ⟨_, _, hcallHeadT, hopFinalT⟩ :=
                            hrecPrefixOpT.app_inv wf.ordered trivial
                          simp [closeOuter, VExpr.inst, VExpr.instVar,
                            hopClosed.liftN_eq, hopClosed.instN_eq,
                            hfClosed.liftN_eq, hfClosed.instN_eq] at hrecPrefixOpT hrecPrefixFuelT hrecPrefixAT hrecPrefixBT hopFinalT hfuelFinalT
                          have hrecFuelEq := (hcallEqRoot.app_same wf
                            trivial hcallHeadT hopFinalT).app_same wf
                            trivial hrecPrefixOpT hfuelFinalT
                          have hrecAEq := hrecFuelEq.app_both wf trivial
                            hdivAEval hrecPrefixFuelT hdivAFinalT
                          have hrecBEq := hrecAEq.app_both wf trivial
                            hdivBEval hrecPrefixAT hdivBFinalT
                          have hrecCallEq := hrecBEq.app_same wf trivial
                            hrecPrefixBT hproofFinalT
                          let proofFinal := closeOuter proofLocal
                          have hrecCallEq' : env.IsDefEqU 0 [] recFinal
                              (((((callV.app op).app (.natLit fuel)).app
                                (.natLit ((a + 1) / 2))).app
                                (.natLit ((b + 1) / 2))).app
                                proofFinal) := by
                            simpa [recFinal, proofFinal, closeOuter,
                              VExpr.inst, VExpr.instVar,
                              hopClosed.liftN_eq, hopClosed.instN_eq,
                              hfClosed.liftN_eq, hfClosed.instN_eq]
                              using hrecCallEq
                          refine ⟨recFinal,
                            ⟨callV, .natLit fuel, proofFinal, hcallS,
                              ⟨_, hfT⟩, hrecCallEq'⟩,
                            hrecCallEq'.trans wf trivial
                              hrecCallEq'.symm, ?_⟩
                          intro q hrecQ
                          -- Evaluate the selection structure.
                          have hcallToRightS : env.IsDefEqU 0 [] e
                              (.app (.app (.app iteFinal
                                (.app (.app op bitOneFinal) bitTwoFinal))
                                thenFinal) elseFinal) := by
                            simpa [iteFinal, bitOneFinal, bitTwoFinal,
                              thenFinal, elseFinal, closeOuter,
                              VExpr.inst, VExpr.instVar,
                              hopClosed.liftN_eq (Nat.zero_le _),
                              hopClosed.instN_eq] using hcallToRight
                          have hbitOneFinalT :=
                            (hbitOneEval.of_r wf trivial
                              (hctors.boolLitS (((a + 1) % 2) == 1)
                                (Us := []) (Δ := [])).2).hasType.1
                          have hbitTwoFinalT :=
                            (hbitTwoEval.of_r wf trivial
                              (hctors.boolLitS (((b + 1) % 2) == 1)
                                (Us := []) (Δ := [])).2).hasType.1
                          have hcondEval : env.IsDefEqU 0 []
                              (.app (.app op bitOneFinal) bitTwoFinal)
                              (.boolLit (f (((a + 1) % 2) == 1)
                                (((b + 1) % 2) == 1))) :=
                            ((hbitOneEval.app_arg wf trivial hop.1
                              hbitOneFinalT).app_both wf trivial
                              hbitTwoEval (.app hop.1 hbitOneFinalT)
                              hbitTwoFinalT).trans wf trivial
                              (hop.2 _ _)
                          have hqT :=
                            (hctors.natLitS q (Us := []) (Δ := [])).2
                          have hrecNatT :=
                            (hrecQ.of_r wf trivial hqT).hasType.1
                          have hdoubleEval : env.IsDefEqU 0 []
                              (.app (.app (.const ``Nat.add []) recFinal)
                                recFinal) (.natLit (q + q)) :=
                            ((hrecQ.app_arg wf trivial (haddT 0 [])
                              hrecNatT).app_both wf trivial hrecQ
                              (VEnv.HasType.app (haddT 0 []) hrecNatT)
                              hrecNatT).trans wf trivial (haddEval q q)
                          have helseEval := helseEqRoot.trans wf trivial
                            hdoubleEval
                          have hdoubleT :=
                            (hdoubleEval.of_r wf trivial
                              (hctors.natLitS (q + q)
                                (Us := []) (Δ := [])).2).hasType.1
                          have hthenEval := hthenEqRoot.trans wf trivial <|
                            ((hdoubleEval.app_arg wf trivial (haddT 0 [])
                              hdoubleT).app_same wf trivial
                              (VEnv.HasType.app (haddT 0 []) hdoubleT)
                              honeRootT).trans wf trivial
                              (haddEval (q + q) 1)
                          simpa using bitwise_struct_eval wf hite heT
                            hcallToRightS hiteEqRoot hcondEval hthenEval
                            helseEval

set_option linter.unusedSimpArgs false in
theorem NatBitwiseFixCertificate.succ_semantics {env : VEnv}
    (wf : env.WF)
    (hctors : Lean4Lean.Environment.VEnv.HasNatBoolConstructors env)
    (haddC : env.contains ``Nat.add)
    (hmodC : env.contains ``Nat.mod)
    (hdivC : env.contains ``Nat.div)
    (hadd : env.ReflectsNatNatNat ``Nat.add Nat.add)
    (hmod : env.ReflectsNatNatNat ``Nat.mod Nat.mod)
    (hdiv : env.ReflectsNatNatNat ``Nat.div Nat.div)
    {decide : VExpr}
    (hdecideS : TrExprS env [] [] Condition.natEqDecideFn decide)
    (hdecide : Lean4Lean.Environment.VEnv.ReflectsNatEqDecide env decide)
    {r : NatBitwiseFixCertificate} {l rr ite : VExpr}
    (hl : TrExprS env [] [] r.expectedSuccLhs l)
    (hr : TrExprS env [] [] r.expectedSuccRhs rr)
    (heq : env.IsDefEqU 0 [] l rr)
    (hiteS : TrExprS env [] [] Condition.bool.boolNatITE ite)
    (hite : env.ReflectsBoolNatITE ite) :
    ∀ op f, env.ReflectsBoolBin op f → ∀ fuel a b e,
      VEnv.BitwiseGoCall env r op (fuel + 1) (a + 1) (b + 1) e →
      env.IsDefEqU 0 [] e e →
      ∃ e', VEnv.BitwiseGoCall env r op fuel
          ((a + 1) / 2) ((b + 1) / 2) e' ∧
        env.IsDefEqU 0 [] e' e' ∧
        ∀ q, env.IsDefEqU 0 [] e' (.natLit q) →
          env.IsDefEqU 0 [] e
            (.natLit (if f ((a + 1) % 2 = 1) ((b + 1) % 2 = 1)
              then q + q + 1 else q + q)) := by
  intro op f hop fuel a b e hG heSelf
  unfold NatBitwiseFixCertificate.expectedSuccLhs at hl
  unfold NatBitwiseFixCertificate.expectedSuccRhs at hr
  have hprefix := VEnv.instantiate_bitwise_lam4_equation wf hctors
    (fuel := fuel) (a := a) (b := b) hl hr heq hop.1
  cases hprefix with
  | intro funTyL natTyL₁ natTyL₂ natTyL₃ bodyL
      funTyR natTyR₁ natTyR₂ natTyR₃ bodyR
      hfunTyL hnatTyL₁ hnatTyL₂ hnatTyL₃
      hfunTyR hnatTyR₁ hnatTyR₂ hnatTyR₃
      hnatEqL₁ hnatEqL₂ hnatEqL₃ hnatEqR₁ hnatEqR₂ hnatEqR₃
      hopL hopR hfT haT hbT hfL hfR haL haR hbL hbR
      hleftS hrightS hprefixEq =>
    cases hleftS with
    | lam hproofTyL _ hbodyL =>
      cases hrightS with
      | lam hproofTyR _ hbodyR =>
        rename_i proofTyL bodyLFinal proofTyR bodyRFinal
        simp only [VExpr.inst] at hprefixEq
        rcases hG with ⟨callV, fuelV, hpV, hcallS, hfuelEq, heCall⟩
        obtain ⟨_, heSelfD⟩ := heSelf
        have heT := heSelfD.hasType.1
        obtain ⟨hpTR, hcallToRight⟩ := succ_lhs_equation wf hctors
          hfunTyL hnatTyL₁ hnatTyL₂ hnatTyL₃ hproofTyL
          hopL hfL haL hbL hfT haT hbT hbodyL hprefixEq
          hcallS hfuelEq heCall heT
        exact succ_rhs_semantics wf hctors haddC hmodC hdivC
          hadd hmod hdiv hdecideS hdecide hiteS hite hop
          hfunTyR hnatTyR₁ hnatTyR₂ hnatTyR₃ hproofTyR
          hnatEqR₂ hnatEqR₃ hopR hfR haR hbR hfT
          hbodyR hcallS hpTR hcallToRight heT

end Lean4Lean.Environment
