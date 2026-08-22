import Lean4Lean.Verify.BitwiseSupport

namespace Lean4Lean.Environment
open Lean VEnv

set_option linter.unusedSimpArgs false in
theorem NatBitwiseFixCertificate.zero_semantics {env : VEnv}
    (wf : env.WF)
    (hctors : Lean4Lean.Environment.VEnv.HasNatBoolConstructors env)
    {r : NatBitwiseFixCertificate}
    {l rr ite : VExpr}
    (hl : TrExprS env [] [] r.expectedZeroLhs l)
    (hr : TrExprS env [] [] r.expectedZeroRhs rr)
    (heq : env.IsDefEqU 0 [] l rr)
    (hiteS : TrExprS env [] [] Condition.bool.boolNatITE ite)
    (hite : env.ReflectsBoolNatITE ite) :
    ∀ op f, env.ReflectsBoolBin op f →
      ∀ fuel b e, VEnv.BitwiseGoCall env r op (fuel + 1) 0 b e →
        env.IsDefEqU 0 [] e e →
        env.IsDefEqU 0 [] e
          (.natLit (if f false true then b else 0)) := by
  intro op f hop fuel b e hG heSelf
  unfold NatBitwiseFixCertificate.expectedZeroLhs at hl
  unfold NatBitwiseFixCertificate.expectedZeroRhs at hr
  have hprefix := VEnv.instantiate_bitwise_lam3_equation wf hctors
    (a := fuel) (b := b) hl hr heq hop.1
  cases hprefix with
  | intro funTyL natTyL₁ natTyL₂ bodyL
      funTyR natTyR₁ natTyR₂ bodyR
      hfunTyL hnatTyL₁ hnatTyL₂ hfunTyR hnatTyR₁ hnatTyR₂
      _hnatEqL₁ _hnatEqL₂ _hnatEqR₁ _hnatEqR₂
      hopL hopR hfT hbT hfL hfR hbL hbR hleftS hrightS hprefixEq =>
    cases hleftS with
    | lam hproofTyL hproofTySL hbodyL =>
      cases hrightS with
      | lam hproofTyR hproofTySR hbodyR =>
        rename_i proofTyL bodyLFinal proofTyR bodyRFinal
        simp only [VExpr.inst] at hprefixEq
        rcases hG with ⟨callV, fuelV, hpV, hcallS, hfuelEq, heCall⟩
        obtain ⟨_, heSelfD⟩ := heSelf
        have heT := heSelfD.hasType.1
        have hcallExprT := (heCall.of_l wf trivial heT).hasType.2
        obtain ⟨hpType, _, hprefixCallT, hpT⟩ :=
          hcallExprT.app_inv wf.ordered trivial
        have hbodyLS := hbodyL
        cases hbodyL with
        | @app prefixLocal _ _ hpLocal _ _ _ _ _ hprefixLocalS hpLocalS =>
          cases hprefixLocalS with
          | @app prefixB _ _ bLocal _ _ _ _ _ hprefixBS hbLocalS =>
            cases hprefixBS with
            | @app prefixZero _ _ zeroLocal _ _ _ _ _ hprefixZeroS hzeroLocalS =>
              cases hprefixZeroS with
              | @app prefixFuel _ _ fuelLocal _ _ _ _ _ hprefixFuelS hfuelLocalS =>
                cases hfuelLocalS with
                | @app succLocal _ _ fuelArgLocal _ _ _ _ _
                    hsuccLocalS hfuelArgLocalS =>
                  cases hprefixFuelS with
                  | @app callLocal _ _ opLocal _ _ _ _ _ hcallLocalS hopLocalS =>
                    let ΔL : VLCtx :=
                      [(none, .vlam proofTyL), (none, .vlam natTyL₂),
                        (none, .vlam natTyL₁), (none, .vlam funTyL)]
                    have hopCanon : TrExprS env [] ΔL (.bvar 3) (.bvar 3) :=
                      .bvar (by rfl)
                    have hfuelArgCanon : TrExprS env [] ΔL (.bvar 2) (.bvar 2) :=
                      .bvar (by rfl)
                    have hbCanon : TrExprS env [] ΔL (.bvar 1) (.bvar 1) :=
                      .bvar (by rfl)
                    have hpCanon : TrExprS env [] ΔL (.bvar 0) (.bvar 0) :=
                      .bvar (by rfl)
                    have hzeroCanon :=
                      (hctors.natZeroS (Us := []) (Δ := ΔL)).1
                    have hsuccCanon :=
                      (hctors.natSuccS (Us := []) (Δ := ΔL)).1
                    cases hopLocalS.unique (by trivial) hopCanon
                    cases hfuelArgLocalS.unique (by trivial) hfuelArgCanon
                    cases hbLocalS.unique (by trivial) hbCanon
                    cases hpLocalS.unique (by trivial) hpCanon
                    cases hzeroLocalS.unique (by trivial) hzeroCanon
                    have hctxL : VLCtx.IsDefEq env 0 ΔL ΔL :=
                      .refl wf ⟨⟨⟨⟨trivial, nofun, hfunTyL⟩,
                        nofun, hnatTyL₁⟩, nofun, hnatTyL₂⟩,
                        nofun, hproofTyL⟩
                    have hcallEqCtx := TrExprS.uniq (Us := []) wf hctxL
                      hcallLocalS (bitwise_weak4 wf hcallS)
                    have hsuccEqCtx := TrExprS.uniq (Us := []) wf hctxL
                      hsuccLocalS hsuccCanon
                    obtain ⟨_, _, hprefixZeroT, hbArgT⟩ :=
                      hprefixCallT.app_inv wf.ordered trivial
                    obtain ⟨_, _, hprefixFuelT, hzeroArgT⟩ :=
                      hprefixZeroT.app_inv wf.ordered trivial
                    obtain ⟨_, _, hprefixOpT, hfuelT⟩ :=
                      hprefixFuelT.app_inv wf.ordered trivial
                    obtain ⟨_, _, hcallVT, hopArgT⟩ :=
                      hprefixOpT.app_inv wf.ordered trivial
                    have hcallVClosed : callV.ClosedN :=
                      (hcallVT.closedN' wf.ordered.closed trivial).1
                    have hsuccT :=
                      (hctors.natSuccS (Us := []) (Δ := [])).2
                    have hsuccClosed : VExpr.natSucc.ClosedN :=
                      (hsuccT.closedN' wf.ordered.closed trivial).1
                    let proofTyLF :=
                      ((proofTyL.inst op 2).inst (.natLit fuel) 1).inst
                        (.natLit b)
                    let callFinal :=
                      ((callLocal.inst op 3).inst (.natLit fuel) 2).inst
                        (.natLit b) 1
                    let succFinal :=
                      ((succLocal.inst op 3).inst (.natLit fuel) 2).inst
                        (.natLit b) 1
                    have hcallEqFinal : env.IsDefEqU 0 [proofTyLF]
                        callFinal callV := by
                      simpa [proofTyLF, callFinal] using
                        bitwise_local_closed_eq wf hopL hfL hbL
                          hcallVClosed (by simpa [ΔL] using hcallEqCtx)
                    have hsuccEqFinal : env.IsDefEqU 0 [proofTyLF]
                        succFinal .natSucc := by
                      simpa [proofTyLF, succFinal] using
                        bitwise_local_closed_eq wf hopL hfL hbL
                          hsuccClosed (by simpa [ΔL] using hsuccEqCtx)
                    obtain ⟨_, hbodyLT⟩ := hbodyLS.wf wf.ordered
                      (Us := []) (Δ := ΔL) hctxL.wf
                    have hbodyLocalFinalT₀ :=
                      VEnv.HasType.inst_bitwise_outer3 wf hopL hfL hbL
                        (by simpa [ΔL] using hbodyLT.hasType.1)
                    have hopClosed : op.ClosedN :=
                      (hop.1.closedN' wf.ordered.closed trivial).1
                    have hfClosed : (VExpr.natLit fuel).ClosedN :=
                      (hfT.closedN' wf.ordered.closed trivial).1
                    have hbClosed : (VExpr.natLit b).ClosedN :=
                      (hbT.closedN' wf.ordered.closed trivial).1
                    have hzT :=
                      (hctors.natZeroS (Us := []) (Δ := [])).2
                    have hzClosed : VExpr.natZero.ClosedN :=
                      (hzT.closedN' wf.ordered.closed trivial).1
                    have hbodyLocalFinalT := hbodyLocalFinalT₀
                    simp [proofTyLF, callFinal, succFinal,
                      hopClosed.liftN_eq, hopClosed.instN_eq,
                      hfClosed.liftN_eq, hfClosed.instN_eq,
                      hbClosed.liftN_eq, hbClosed.instN_eq,
                      hzClosed.instN_eq, VExpr.inst] at hbodyLocalFinalT
                    have hΓ : OnCtx [proofTyLF] (env.IsType 0) := by
                      obtain ⟨_, hEqD⟩ := hprefixEq
                      exact ⟨trivial, (hEqD.hasType.1.lam_inv wf trivial).1⟩
                    obtain ⟨prefixArgTy, prefixBodyTy,
                        hprefixLocalFinalT, hproofVarFinalT⟩ :=
                      VEnv.HasType.app_inv wf.ordered hΓ hbodyLocalFinalT
                    obtain ⟨_, _, hprefixBeforeBT, hbLocalT⟩ :=
                      hprefixLocalFinalT.app_inv wf.ordered hΓ
                    obtain ⟨_, _, hprefixBeforeZeroT, hzeroLocalT⟩ :=
                      hprefixBeforeBT.app_inv wf.ordered hΓ
                    obtain ⟨_, _, hprefixBeforeFuelT, hsuccFuelLocalT⟩ :=
                      hprefixBeforeZeroT.app_inv wf.ordered hΓ
                    obtain ⟨_, _, hcallFinalT, hopLocalT⟩ :=
                      hprefixBeforeFuelT.app_inv wf.ordered hΓ
                    have hcallAppEq := hcallEqFinal.app_same wf hΓ
                      hcallFinalT hopLocalT
                    have hsuccAppEq := hsuccEqFinal.app_same wf hΓ
                      ((hsuccEqFinal.of_r wf hΓ (hsuccT.weak0 wf)).hasType.1)
                      (hfT.weak0 wf)
                    have hsuccEval : env.IsDefEqU 0 [proofTyLF]
                        (.app succFinal (.natLit fuel))
                        (.natLit (fuel + 1)) := by
                      simpa [succFinal, VExpr.natLit] using hsuccAppEq
                    have hprefixBeforeBT' := hprefixBeforeBT
                    have hprefixBeforeZeroT' := hprefixBeforeZeroT
                    have hprefixBeforeFuelT' := hprefixBeforeFuelT
                    have hprefixLocalFinalT' := hprefixLocalFinalT
                    have hsuccFuelLocalT' := hsuccFuelLocalT
                    have hzeroLocalT' := hzeroLocalT
                    have hbLocalT' := hbLocalT
                    simp [callFinal, succFinal,
                      VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.liftN,
                      liftVar, hfClosed.liftN_eq, hfClosed.instN_eq,
                      hbClosed.liftN_eq, hbClosed.instN_eq] at hprefixLocalFinalT' hprefixBeforeBT' hprefixBeforeZeroT' hprefixBeforeFuelT' hsuccFuelLocalT' hzeroLocalT' hbLocalT'
                    have hprefixFuelEq := hcallAppEq.app_both wf hΓ
                      hsuccEval hprefixBeforeFuelT' hsuccFuelLocalT'
                    have hprefixZeroEq := hprefixFuelEq.app_same wf hΓ
                      hprefixBeforeZeroT' hzeroLocalT'
                    have hprefixLocalEq := hprefixZeroEq.app_same wf hΓ
                      hprefixBeforeBT' hbLocalT'
                    have hrelFuelEq := hfuelEq.app_arg wf trivial
                      hprefixOpT hfuelT
                    have hrelZeroEq := hrelFuelEq.app_same wf trivial
                      hprefixFuelT hzeroArgT
                    have hrelPrefixEq := hrelZeroEq.app_same wf trivial
                      hprefixZeroT hbArgT
                    have hlocalRelEq := hprefixLocalEq.trans wf hΓ
                      (hrelPrefixEq.weak0 (Γ := [proofTyLF]) wf).symm
                    have hlamEq : env.IsDefEqU 0 []
                        (.lam proofTyLF
                          (.app
                            (.app
                              (.app
                                (.app (.app callFinal op)
                                  (.app succFinal (.natLit fuel)))
                                .natZero)
                              (.natLit b))
                            (.bvar 0)))
                        (.lam
                          (((proofTyR.inst op 2).inst (.natLit fuel) 1).inst
                            (.natLit b))
                          (((bodyRFinal.inst op 3).inst (.natLit fuel) 2).inst
                            (.natLit b) 1)) := by
                      simpa [proofTyLF, callFinal, succFinal,
                        VExpr.inst, VExpr.instVar,
                        hopClosed.liftN_eq, hopClosed.instN_eq,
                        hfClosed.liftN_eq, hfClosed.instN_eq,
                        hbClosed.liftN_eq, hbClosed.instN_eq,
                        hzClosed.instN_eq] using hprefixEq
                    obtain ⟨hpTR, hfinish⟩ :=
                      VEnv.finish_bitwise_proof_equation wf
                        (hproofTyL := hΓ.2)
                        hprefixLocalFinalT' hproofVarFinalT hprefixCallT hpT
                        hlocalRelEq hlamEq
                    have hcallToRight := heCall.trans wf trivial hfinish
                    cases hbodyR with
                    | @app iteTwo _ _ zeroLocalR _ _ _ _ _ hiteTwoS hzeroLocalRS =>
                      cases hiteTwoS with
                      | @app iteOne _ _ bLocalR _ _ _ _ _ hiteOneS hbLocalRS =>
                        cases hiteOneS with
                        | @app iteLocal _ _ condLocal _ _ _ _ _ hiteLocalS hcondLocalS =>
                          cases hcondLocalS with
                          | @app opFalse _ _ trueLocal _ _ _ _ _ hopFalseS htrueLocalS =>
                            cases hopFalseS with
                            | @app opLocalR _ _ falseLocal _ _ _ _ _ hopLocalRS hfalseLocalS =>
                              let ΔR : VLCtx :=
                                [(none, .vlam proofTyR),
                                  (none, .vlam natTyR₂),
                                  (none, .vlam natTyR₁),
                                  (none, .vlam funTyR)]
                              have hctxR : VLCtx.IsDefEq env 0 ΔR ΔR :=
                                .refl wf ⟨⟨⟨⟨trivial, nofun, hfunTyR⟩,
                                  nofun, hnatTyR₁⟩, nofun, hnatTyR₂⟩,
                                  nofun, hproofTyR⟩
                              have hopCanonR : TrExprS env [] ΔR
                                  (.bvar 3) (.bvar 3) := .bvar (by rfl)
                              have hbCanonR : TrExprS env [] ΔR
                                  (.bvar 1) (.bvar 1) := .bvar (by rfl)
                              have hzeroCanonR :=
                                (hctors.natZeroS
                                  (Us := []) (Δ := ΔR)).1
                              have hfalseCanon :=
                                (hctors.boolFalseS
                                  (Us := []) (Δ := ΔR)).1
                              have htrueCanon :=
                                (hctors.boolTrueS
                                  (Us := []) (Δ := ΔR)).1
                              cases hopLocalRS.unique (by trivial) hopCanonR
                              cases hbLocalRS.unique (by trivial) hbCanonR
                              cases hzeroLocalRS.unique (by trivial) hzeroCanonR
                              cases hfalseLocalS.unique (by trivial) hfalseCanon
                              cases htrueLocalS.unique (by trivial) htrueCanon
                              have hiteEqCtx := TrExprS.uniq (Us := []) wf hctxR
                                hiteLocalS (bitwise_weak4 wf hiteS)
                              have hiteClosed : ite.ClosedN :=
                                (hite.1.closedN' wf.ordered.closed trivial).1
                              have hiteEqFinal : env.IsDefEqU 0
                                  [((proofTyR.inst op 2).inst (.natLit fuel) 1).inst
                                    (.natLit b)]
                                  (((iteLocal.inst op 3).inst (.natLit fuel) 2).inst
                                    (.natLit b) 1) ite :=
                                bitwise_local_closed_eq wf hopR hfR hbR
                                  hiteClosed (by simpa [ΔR] using hiteEqCtx)
                              have hiteEqRoot₀ := hiteEqFinal.instN wf.ordered
                                (.zero : Ctx.InstN [] hpV
                                  ((proofTyR.inst op 2).inst (.natLit fuel) 1 |>.inst
                                    (.natLit b)) 0
                                  [((proofTyR.inst op 2).inst (.natLit fuel) 1 |>.inst
                                    (.natLit b))] []) hpTR
                              have hiteEqRoot : env.IsDefEqU 0 []
                                  (((((iteLocal.inst op 3).inst (.natLit fuel) 2).inst
                                    (.natLit b) 1).inst hpV)) ite := by
                                simpa [hiteClosed.instN_eq] using hiteEqRoot₀
                              have hcallToRightS := hcallToRight
                              simp [VExpr.natLit, VExpr.boolFalse,
                                VExpr.boolTrue, VExpr.inst, VExpr.instVar,
                                VExpr.lift, VExpr.liftN, liftVar,
                                hopClosed.liftN_eq (Nat.zero_le _),
                                hopClosed.instN_eq,
                                hbClosed.liftN_eq (Nat.zero_le _),
                                hbClosed.instN_eq,
                                hzClosed.instN_eq] at hcallToRightS
                              exact bitwise_struct_eval wf hite heT
                                hcallToRightS hiteEqRoot (hop.2 false true)
                                (.refl ⟨_, hbT⟩) (.refl ⟨_, hzT⟩)

set_option linter.unusedSimpArgs false in
theorem NatBitwiseFixCertificate.zero_right_semantics {env : VEnv}
    (wf : env.WF)
    (hctors : Lean4Lean.Environment.VEnv.HasNatBoolConstructors env)
    {r : NatBitwiseFixCertificate}
    {l rr ite : VExpr}
    (hl : TrExprS env [] [] r.expectedZeroRightLhs l)
    (hr : TrExprS env [] [] r.expectedZeroRightRhs rr)
    (heq : env.IsDefEqU 0 [] l rr)
    (hiteS : TrExprS env [] [] Condition.bool.boolNatITE ite)
    (hite : env.ReflectsBoolNatITE ite) :
    ∀ op f, env.ReflectsBoolBin op f →
      ∀ fuel a e, VEnv.BitwiseGoCall env r op (fuel + 1) (a + 1) 0 e →
        env.IsDefEqU 0 [] e e →
        env.IsDefEqU 0 [] e
          (.natLit (if f true false then a + 1 else 0)) := by
  intro op f hop fuel a e hG heSelf
  unfold NatBitwiseFixCertificate.expectedZeroRightLhs at hl
  unfold NatBitwiseFixCertificate.expectedZeroRightRhs at hr
  have hprefix := VEnv.instantiate_bitwise_lam3_equation wf hctors
    (a := fuel) (b := a) hl hr heq hop.1
  cases hprefix with
  | intro funTyL natTyL₁ natTyL₂ bodyL
      funTyR natTyR₁ natTyR₂ bodyR
      hfunTyL hnatTyL₁ hnatTyL₂ hfunTyR hnatTyR₁ hnatTyR₂
      _hnatEqL₁ _hnatEqL₂ _hnatEqR₁ _hnatEqR₂
      hopL hopR hfT haT hfL hfR haL haR hleftS hrightS hprefixEq =>
    cases hleftS with
    | lam hproofTyL hproofTySL hbodyL =>
      cases hrightS with
      | lam hproofTyR hproofTySR hbodyR =>
        rename_i proofTyL bodyLFinal proofTyR bodyRFinal
        simp only [VExpr.inst] at hprefixEq
        rcases hG with ⟨callV, fuelV, hpV, hcallS, hfuelEq, heCall⟩
        obtain ⟨_, heSelfD⟩ := heSelf
        have heT := heSelfD.hasType.1
        have hcallExprT := (heCall.of_l wf trivial heT).hasType.2
        obtain ⟨hpType, _, hprefixCallT, hpT⟩ :=
          hcallExprT.app_inv wf.ordered trivial
        have hbodyLS := hbodyL
        cases hbodyL with
        | @app prefixLocal _ _ hpLocal _ _ _ _ _ hprefixLocalS hpLocalS =>
          cases hprefixLocalS with
          | @app prefixZero _ _ zeroLocal _ _ _ _ _ hprefixZeroS hzeroLocalS =>
            cases hprefixZeroS with
            | @app prefixA _ _ succA _ _ _ _ _ hprefixAS hsuccAS =>
              cases hsuccAS with
              | @app succLocalA _ _ aLocal _ _ _ _ _ hsuccLocalAS haLocalS =>
                cases hprefixAS with
                | @app prefixFuel _ _ succFuel _ _ _ _ _ hprefixFuelS hsuccFuelS =>
                  cases hsuccFuelS with
                  | @app succLocalF _ _ fuelLocal _ _ _ _ _ hsuccLocalFS hfuelLocalS =>
                    cases hprefixFuelS with
                    | @app callLocal _ _ opLocal _ _ _ _ _ hcallLocalS hopLocalS =>
                      let ΔL : VLCtx :=
                        [(none, .vlam proofTyL), (none, .vlam natTyL₂),
                          (none, .vlam natTyL₁), (none, .vlam funTyL)]
                      have hopCanon : TrExprS env [] ΔL (.bvar 3) (.bvar 3) :=
                        .bvar (by rfl)
                      have hfuelCanon : TrExprS env [] ΔL (.bvar 2) (.bvar 2) :=
                        .bvar (by rfl)
                      have haCanon : TrExprS env [] ΔL (.bvar 1) (.bvar 1) :=
                        .bvar (by rfl)
                      have hpCanon : TrExprS env [] ΔL (.bvar 0) (.bvar 0) :=
                        .bvar (by rfl)
                      have hzeroCanon :=
                        (hctors.natZeroS (Us := []) (Δ := ΔL)).1
                      have hsuccCanon :=
                        (hctors.natSuccS (Us := []) (Δ := ΔL)).1
                      cases hopLocalS.unique (by trivial) hopCanon
                      cases hfuelLocalS.unique (by trivial) hfuelCanon
                      cases haLocalS.unique (by trivial) haCanon
                      cases hpLocalS.unique (by trivial) hpCanon
                      cases hzeroLocalS.unique (by trivial) hzeroCanon
                      have hctxL : VLCtx.IsDefEq env 0 ΔL ΔL :=
                        .refl wf ⟨⟨⟨⟨trivial, nofun, hfunTyL⟩,
                          nofun, hnatTyL₁⟩, nofun, hnatTyL₂⟩,
                          nofun, hproofTyL⟩
                      have hcallEqCtx := TrExprS.uniq (Us := []) wf hctxL
                        hcallLocalS (bitwise_weak4 wf hcallS)
                      have hsuccAEqCtx := TrExprS.uniq (Us := []) wf hctxL
                        hsuccLocalAS hsuccCanon
                      have hsuccFEqCtx := TrExprS.uniq (Us := []) wf hctxL
                        hsuccLocalFS hsuccCanon
                      obtain ⟨_, _, hprefixZeroT, hzeroArgT⟩ :=
                        hprefixCallT.app_inv wf.ordered trivial
                      obtain ⟨_, _, hprefixAT, haArgT⟩ :=
                        hprefixZeroT.app_inv wf.ordered trivial
                      obtain ⟨_, _, hprefixFuelT, hfuelT⟩ :=
                        hprefixAT.app_inv wf.ordered trivial
                      obtain ⟨_, _, hprefixOpT, hopArgT⟩ :=
                        hprefixFuelT.app_inv wf.ordered trivial
                      have hcallVT := hprefixOpT
                      have hcallVClosed : callV.ClosedN := by
                        exact (hcallVT.closedN' wf.ordered.closed trivial).1
                      have hsuccT :=
                        (hctors.natSuccS (Us := []) (Δ := [])).2
                      have hsuccClosed : VExpr.natSucc.ClosedN :=
                        (hsuccT.closedN' wf.ordered.closed trivial).1
                      let proofTyLF :=
                        ((proofTyL.inst op 2).inst (.natLit fuel) 1).inst
                          (.natLit a)
                      let callFinal :=
                        ((callLocal.inst op 3).inst (.natLit fuel) 2).inst
                          (.natLit a) 1
                      let succAFinal :=
                        ((succLocalA.inst op 3).inst (.natLit fuel) 2).inst
                          (.natLit a) 1
                      let succFFinal :=
                        ((succLocalF.inst op 3).inst (.natLit fuel) 2).inst
                          (.natLit a) 1
                      have hcallEqFinal : env.IsDefEqU 0 [proofTyLF]
                          callFinal callV := by
                        simpa [proofTyLF, callFinal] using
                          bitwise_local_closed_eq wf hopL hfL haL
                            hcallVClosed (by simpa [ΔL] using hcallEqCtx)
                      have hsuccAEqFinal : env.IsDefEqU 0 [proofTyLF]
                          succAFinal .natSucc := by
                        simpa [proofTyLF, succAFinal] using
                          bitwise_local_closed_eq wf hopL hfL haL
                            hsuccClosed (by simpa [ΔL] using hsuccAEqCtx)
                      have hsuccFEqFinal : env.IsDefEqU 0 [proofTyLF]
                          succFFinal .natSucc := by
                        simpa [proofTyLF, succFFinal] using
                          bitwise_local_closed_eq wf hopL hfL haL
                            hsuccClosed (by simpa [ΔL] using hsuccFEqCtx)
                      obtain ⟨_, hbodyLT⟩ := hbodyLS.wf wf.ordered
                        (Us := []) (Δ := ΔL) hctxL.wf
                      have hbodyLocalFinalT₀ :=
                        VEnv.HasType.inst_bitwise_outer3 wf hopL hfL haL
                          (by simpa [ΔL] using hbodyLT.hasType.1)
                      have hopClosed : op.ClosedN :=
                        (hop.1.closedN' wf.ordered.closed trivial).1
                      have hfClosed : (VExpr.natLit fuel).ClosedN :=
                        (hfT.closedN' wf.ordered.closed trivial).1
                      have haClosed : (VExpr.natLit a).ClosedN :=
                        (haT.closedN' wf.ordered.closed trivial).1
                      have hzT :=
                        (hctors.natZeroS (Us := []) (Δ := [])).2
                      have hzClosed : VExpr.natZero.ClosedN :=
                        (hzT.closedN' wf.ordered.closed trivial).1
                      have hbodyLocalFinalT := hbodyLocalFinalT₀
                      simp [proofTyLF, callFinal, succAFinal, succFFinal,
                        hopClosed.liftN_eq, hopClosed.instN_eq,
                        hfClosed.liftN_eq, hfClosed.instN_eq,
                        haClosed.liftN_eq, haClosed.instN_eq,
                        hzClosed.instN_eq, VExpr.inst] at hbodyLocalFinalT
                      have hΓ : OnCtx [proofTyLF] (env.IsType 0) := by
                        obtain ⟨_, hEqD⟩ := hprefixEq
                        exact ⟨trivial, (hEqD.hasType.1.lam_inv wf trivial).1⟩
                      obtain ⟨prefixArgTy, prefixBodyTy,
                          hprefixLocalFinalT, hproofVarFinalT⟩ :=
                        VEnv.HasType.app_inv wf.ordered hΓ hbodyLocalFinalT
                      obtain ⟨_, _, hprefixBeforeZeroT, hzeroLocalT⟩ :=
                        hprefixLocalFinalT.app_inv wf.ordered hΓ
                      obtain ⟨_, _, hprefixBeforeAT, hsuccALocalT⟩ :=
                        hprefixBeforeZeroT.app_inv wf.ordered hΓ
                      obtain ⟨_, _, hprefixBeforeFuelT, hsuccFLocalT⟩ :=
                        hprefixBeforeAT.app_inv wf.ordered hΓ
                      obtain ⟨_, _, hcallFinalT, hopLocalT⟩ :=
                        hprefixBeforeFuelT.app_inv wf.ordered hΓ
                      have hcallAppEq := hcallEqFinal.app_same wf hΓ
                        hcallFinalT hopLocalT
                      have hsuccAAppEq := hsuccAEqFinal.app_same wf hΓ
                        ((hsuccAEqFinal.of_r wf hΓ (hsuccT.weak0 wf)).hasType.1)
                        (haT.weak0 wf)
                      have hsuccFAppEq := hsuccFEqFinal.app_same wf hΓ
                        ((hsuccFEqFinal.of_r wf hΓ (hsuccT.weak0 wf)).hasType.1)
                        (hfT.weak0 wf)
                      have hsuccAEval : env.IsDefEqU 0 [proofTyLF]
                          (.app succAFinal (.natLit a)) (.natLit (a + 1)) := by
                        simpa [VExpr.natLit] using hsuccAAppEq
                      have hsuccFEval : env.IsDefEqU 0 [proofTyLF]
                          (.app succFFinal (.natLit fuel))
                          (.natLit (fuel + 1)) := by
                        simpa [VExpr.natLit] using hsuccFAppEq
                      have hprefixBeforeZeroT' := hprefixBeforeZeroT
                      have hprefixBeforeAT' := hprefixBeforeAT
                      have hprefixBeforeFuelT' := hprefixBeforeFuelT
                      have hprefixLocalFinalT' := hprefixLocalFinalT
                      have hsuccALocalT' := hsuccALocalT
                      have hsuccFLocalT' := hsuccFLocalT
                      have hzeroLocalT' := hzeroLocalT
                      simp [callFinal, succAFinal, succFFinal,
                        VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.liftN,
                        liftVar, hfClosed.liftN_eq, hfClosed.instN_eq,
                        haClosed.liftN_eq, haClosed.instN_eq] at hprefixLocalFinalT' hprefixBeforeZeroT' hprefixBeforeAT' hprefixBeforeFuelT' hsuccALocalT' hsuccFLocalT' hzeroLocalT'
                      have hprefixFuelEq := hcallAppEq.app_both wf hΓ
                        hsuccFEval hprefixBeforeFuelT' hsuccFLocalT'
                      have hprefixAEq := hprefixFuelEq.app_both wf hΓ
                        hsuccAEval hprefixBeforeAT' hsuccALocalT'
                      have hprefixLocalEq := hprefixAEq.app_same wf hΓ
                        hprefixBeforeZeroT' hzeroLocalT'
                      have hrelFuelEq := hfuelEq.app_arg wf trivial
                        hprefixFuelT hfuelT
                      have hrelAEq := hrelFuelEq.app_same wf trivial
                        hprefixAT haArgT
                      have hrelPrefixEq := hrelAEq.app_same wf trivial
                        hprefixZeroT hzeroArgT
                      have hlocalRelEq := hprefixLocalEq.trans wf hΓ
                        (hrelPrefixEq.weak0 (Γ := [proofTyLF]) wf).symm
                      have hlamEq : env.IsDefEqU 0 []
                          (.lam proofTyLF
                            (.app
                              (.app (.app (.app (callFinal.app op)
                                (succFFinal.app (.natLit fuel)))
                                (succAFinal.app (.natLit a))) .natZero)
                              (.bvar 0)))
                          (.lam
                            (((proofTyR.inst op 2).inst (.natLit fuel) 1).inst
                              (.natLit a))
                            (((bodyRFinal.inst op 3).inst (.natLit fuel) 2).inst
                              (.natLit a) 1)) := by
                        simpa [proofTyLF, callFinal, succAFinal, succFFinal,
                          VExpr.inst, VExpr.instVar,
                          hopClosed.liftN_eq, hopClosed.instN_eq,
                          hfClosed.liftN_eq, hfClosed.instN_eq,
                          haClosed.liftN_eq, haClosed.instN_eq,
                          hzClosed.instN_eq] using hprefixEq
                      obtain ⟨hpTR, hfinish⟩ :=
                        VEnv.finish_bitwise_proof_equation wf
                        (hproofTyL := hΓ.2)
                        hprefixLocalFinalT' hproofVarFinalT hprefixCallT hpT
                        hlocalRelEq hlamEq
                      have hcallToRight := heCall.trans wf trivial hfinish
                      cases hbodyR with
                      | @app iteTwo _ _ zeroLocalR _ _ _ _ _ hiteTwoS hzeroLocalRS =>
                        cases hiteTwoS with
                        | @app iteOne _ _ thenLocal _ _ _ _ _ hiteOneS hthenLocalS =>
                          cases hthenLocalS with
                          | @app succLocalR _ _ aLocalR _ _ _ _ _ hsuccLocalRS haLocalRS =>
                            cases hiteOneS with
                            | @app iteLocal _ _ condLocal _ _ _ _ _ hiteLocalS hcondLocalS =>
                              cases hcondLocalS with
                              | @app opTrue _ _ falseLocal _ _ _ _ _ hopTrueS hfalseLocalS =>
                                cases hopTrueS with
                                | @app opLocalR _ _ trueLocal _ _ _ _ _ hopLocalRS htrueLocalS =>
                                  let ΔR : VLCtx :=
                                    [(none, .vlam proofTyR),
                                      (none, .vlam natTyR₂),
                                      (none, .vlam natTyR₁),
                                      (none, .vlam funTyR)]
                                  have hctxR : VLCtx.IsDefEq env 0 ΔR ΔR :=
                                    .refl wf ⟨⟨⟨⟨trivial, nofun, hfunTyR⟩,
                                      nofun, hnatTyR₁⟩, nofun, hnatTyR₂⟩,
                                      nofun, hproofTyR⟩
                                  have hopCanonR : TrExprS env [] ΔR
                                      (.bvar 3) (.bvar 3) := .bvar (by rfl)
                                  have haCanonR : TrExprS env [] ΔR
                                      (.bvar 1) (.bvar 1) := .bvar (by rfl)
                                  have hzeroCanonR :=
                                    (hctors.natZeroS
                                      (Us := []) (Δ := ΔR)).1
                                  have hsuccCanonR :=
                                    (hctors.natSuccS
                                      (Us := []) (Δ := ΔR)).1
                                  obtain ⟨_, hopSort⟩ := hop.1.isType wf trivial
                                  obtain ⟨hboolTy, _⟩ :=
                                    hopSort.forallE_inv wf
                                  obtain ⟨_, hboolSort⟩ := hboolTy
                                  obtain ⟨_, hboolCi, _, _⟩ :=
                                    hboolSort.const_inv wf trivial
                                  have hbool : env.contains ``Bool :=
                                    ⟨_, hboolCi⟩
                                  have hfalseCanon :=
                                    (hctors.boolFalseS
                                      (Us := []) (Δ := ΔR)).1
                                  have htrueCanon :=
                                    (hctors.boolTrueS
                                      (Us := []) (Δ := ΔR)).1
                                  cases hopLocalRS.unique (by trivial) hopCanonR
                                  cases haLocalRS.unique (by trivial) haCanonR
                                  cases hzeroLocalRS.unique (by trivial) hzeroCanonR
                                  cases htrueLocalS.unique (by trivial) htrueCanon
                                  cases hfalseLocalS.unique (by trivial) hfalseCanon
                                  have hiteEqCtx := TrExprS.uniq (Us := []) wf
                                    hctxR hiteLocalS (bitwise_weak4 wf hiteS)
                                  have hsuccEqCtx := TrExprS.uniq (Us := []) wf
                                    hctxR hsuccLocalRS hsuccCanonR
                                  have hiteClosed : ite.ClosedN :=
                                    (hite.1.closedN' wf.ordered.closed trivial).1
                                  have hiteEqFinal : env.IsDefEqU 0
                                      [((proofTyR.inst op 2).inst (.natLit fuel) 1).inst
                                        (.natLit a)]
                                      (((iteLocal.inst op 3).inst (.natLit fuel) 2).inst
                                        (.natLit a) 1) ite :=
                                    bitwise_local_closed_eq wf hopR hfR haR
                                      hiteClosed (by simpa [ΔR] using hiteEqCtx)
                                  have hsuccEqFinal : env.IsDefEqU 0
                                      [((proofTyR.inst op 2).inst (.natLit fuel) 1).inst
                                        (.natLit a)]
                                      (((succLocalR.inst op 3).inst (.natLit fuel) 2).inst
                                        (.natLit a) 1) .natSucc :=
                                    bitwise_local_closed_eq wf hopR hfR haR
                                      hsuccClosed (by simpa [ΔR] using hsuccEqCtx)
                                  have hiteEqRoot₀ := hiteEqFinal.instN wf.ordered
                                    (.zero : Ctx.InstN [] hpV
                                      ((proofTyR.inst op 2).inst (.natLit fuel) 1 |>.inst
                                        (.natLit a)) 0
                                      [((proofTyR.inst op 2).inst (.natLit fuel) 1 |>.inst
                                        (.natLit a))] []) hpTR
                                  have hsuccEqRoot₀ := hsuccEqFinal.instN wf.ordered
                                    (.zero : Ctx.InstN [] hpV
                                      ((proofTyR.inst op 2).inst (.natLit fuel) 1 |>.inst
                                        (.natLit a)) 0
                                      [((proofTyR.inst op 2).inst (.natLit fuel) 1 |>.inst
                                        (.natLit a))] []) hpTR
                                  have hiteEqRoot : env.IsDefEqU 0 []
                                      (((((iteLocal.inst op 3).inst (.natLit fuel) 2).inst
                                        (.natLit a) 1).inst hpV)) ite := by
                                    simpa [hiteClosed.instN_eq] using hiteEqRoot₀
                                  let succRFinal :=
                                    ((((succLocalR.inst op 3).inst (.natLit fuel) 2).inst
                                      (.natLit a) 1).inst hpV)
                                  have hsuccEqRoot : env.IsDefEqU 0 []
                                      succRFinal .natSucc := by
                                    simpa [succRFinal, hsuccClosed.instN_eq] using
                                      hsuccEqRoot₀
                                  have hcallToRightS := hcallToRight
                                  simp [succRFinal, VExpr.natLit, VExpr.boolFalse,
                                    VExpr.boolTrue, VExpr.inst, VExpr.instVar,
                                    VExpr.lift, VExpr.liftN, liftVar,
                                    hopClosed.liftN_eq (Nat.zero_le _),
                                    hopClosed.instN_eq,
                                    haClosed.liftN_eq (Nat.zero_le _),
                                    haClosed.instN_eq,
                                    hzClosed.instN_eq] at hcallToRightS
                                  have hsuccRFinalT :=
                                    (hsuccEqRoot.of_r wf trivial hsuccT).hasType.1
                                  have hsuccAppEq := hsuccEqRoot.app_same wf trivial
                                    hsuccRFinalT haT
                                  have hsuccEval : env.IsDefEqU 0 []
                                      (.app succRFinal (.natLit a))
                                      (.natLit (a + 1)) := by
                                    simpa [VExpr.natLit] using hsuccAppEq
                                  exact bitwise_struct_eval wf hite heT
                                    hcallToRightS hiteEqRoot (hop.2 true false)
                                    hsuccEval (.refl ⟨_, hzT⟩)

end Lean4Lean.Environment
