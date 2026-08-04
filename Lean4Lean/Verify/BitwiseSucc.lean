import Lean4Lean.Verify.BitwiseTransitions

namespace Lean4Lean.Environment
open Lean VEnv

@[simp] private theorem Nat.decide_eq_beq (a b : Nat) :
    decide (a = b) = (a == b) := rfl

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
                    | @app succLocalF _ _ fuelLocal _ _ _ _ _ hsuccLocalFS hfuelLocalS =>
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
                        have hcallWeak := hcallS.weakBV wf.ordered
                          (.skip (.vlam proofTyL) <| .skip (.vlam natTyL₃) <|
                            .skip (.vlam natTyL₂) <| .skip (.vlam natTyL₁) <|
                              .skip (.vlam funTyL) <|
                                (.refl : VLCtx.BVLift [] [] 0 0 0 0))
                        have hcallSourceLift :
                            r.callFn.liftLooseBVars' 0 5 = r.callFn :=
                          Expr.liftLooseBVars_eq_self
                            hcallS.closed.looseBVarRange_le
                        have hcallWeak' : TrExprS env [] ΔL r.callFn
                            (callV.liftN 5) := by
                          simpa [ΔL, VLocalDecl.depth, hcallSourceLift] using hcallWeak
                        have hcallEqCtx := TrExprS.uniq (Us := []) wf hctxL
                          hcallLocalS hcallWeak'
                        have hsuccBEqCtx := TrExprS.uniq (Us := []) wf hctxL
                          hsuccLocalBS hsuccCanon
                        have hsuccAEqCtx := TrExprS.uniq (Us := []) wf hctxL
                          hsuccLocalAS hsuccCanon
                        have hsuccFEqCtx := TrExprS.uniq (Us := []) wf hctxL
                          hsuccLocalFS hsuccCanon
                        have hcallEqFinal₀ := VEnv.IsDefEqU.inst_bitwise_outer4 wf
                          hopL hfL haL hbL (by simpa [ΔL] using hcallEqCtx)
                        have hsuccBEqFinal₀ := VEnv.IsDefEqU.inst_bitwise_outer4 wf
                          hopL hfL haL hbL (by simpa [ΔL] using hsuccBEqCtx)
                        have hsuccAEqFinal₀ := VEnv.IsDefEqU.inst_bitwise_outer4 wf
                          hopL hfL haL hbL (by simpa [ΔL] using hsuccAEqCtx)
                        have hsuccFEqFinal₀ := VEnv.IsDefEqU.inst_bitwise_outer4 wf
                          hopL hfL haL hbL (by simpa [ΔL] using hsuccFEqCtx)
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
                          simpa [proofTyLF, callFinal, hcallVClosed.liftN_eq,
                            hcallVClosed.instN_eq] using hcallEqFinal₀
                        have hsuccBEqFinal : env.IsDefEqU 0 [proofTyLF]
                            succBFinal .natSucc := by
                          simpa [proofTyLF, succBFinal, hsuccClosed.instN_eq] using
                            hsuccBEqFinal₀
                        have hsuccAEqFinal : env.IsDefEqU 0 [proofTyLF]
                            succAFinal .natSucc := by
                          simpa [proofTyLF, succAFinal, hsuccClosed.instN_eq] using
                            hsuccAEqFinal₀
                        have hsuccFEqFinal : env.IsDefEqU 0 [proofTyLF]
                            succFFinal .natSucc := by
                          simpa [proofTyLF, succFFinal, hsuccClosed.instN_eq] using
                            hsuccFEqFinal₀
                        obtain ⟨_, hbodyLT⟩ := hbodyLS.wf wf.ordered
                          (Us := []) (Δ := ΔL) hctxL.wf
                        have hbodyLocalFinalT₀ :=
                          VEnv.HasType.inst_bitwise_outer4 wf hopL hfL haL hbL
                            (by simpa [ΔL] using hbodyLT.hasType.1)
                        have hopClosed : op.ClosedN :=
                          (hop.1.closedN' wf.ordered.closed trivial).1
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
                        have hcallToRight := heCall.trans wf trivial hfinish
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
                                    [(none, .vlam proofTyR),
                                      (none, .vlam natTyR₃),
                                      (none, .vlam natTyR₂),
                                      (none, .vlam natTyR₁),
                                      (none, .vlam funTyR)]
                                  have hctxR : VLCtx.IsDefEq env 0 ΔR ΔR :=
                                    .refl wf ⟨⟨⟨⟨⟨trivial, nofun, hfunTyR⟩,
                                      nofun, hnatTyR₁⟩, nofun, hnatTyR₂⟩,
                                      nofun, hnatTyR₃⟩, nofun, hproofTyR⟩
                                  have hnatEqAR : env.IsDefEqU 0 ΔR.toCtx
                                      natTyR₂.lift.lift.lift .nat := by
                                    have h := (VEnv.IsDefEqU.weakN_iff wf
                                      hctxR.wf.toCtx
                                      (.zero [proofTyR, natTyR₃, natTyR₂] :
                                        Ctx.LiftN 3 0
                                          [natTyR₁, funTyR] ΔR.toCtx)).2
                                      hnatEqR₂
                                    rw [VExpr.liftN_succ, VExpr.liftN_succ,
                                      VExpr.liftN_succ] at h
                                    simpa only [ΔR, VExpr.lift,
                                      VExpr.liftN_zero, VExpr.liftN_nat] using h
                                  have hnatEqBR : env.IsDefEqU 0 ΔR.toCtx
                                      natTyR₃.lift.lift .nat := by
                                    have h := (VEnv.IsDefEqU.weakN_iff wf
                                      hctxR.wf.toCtx
                                      (.zero [proofTyR, natTyR₃] :
                                        Ctx.LiftN 2 0
                                          [natTyR₂, natTyR₁, funTyR]
                                          ΔR.toCtx)).2 hnatEqR₃
                                    rw [VExpr.liftN_succ, VExpr.liftN_succ] at h
                                    simpa only [ΔR, VExpr.lift,
                                      VExpr.liftN_zero, VExpr.liftN_nat] using h
                                  have haVarT : env.HasType 0 ΔR.toCtx
                                      (.bvar 2) .nat := by
                                    have hv : env.HasType 0 ΔR.toCtx
                                        (.bvar 2) natTyR₂.lift.lift.lift :=
                                      .bvar (.succ (.succ .zero))
                                    exact hv.defeqU_r wf hctxR.wf.toCtx hnatEqAR
                                  have hbVarT : env.HasType 0 ΔR.toCtx
                                      (.bvar 1) .nat := by
                                    have hv : env.HasType 0 ΔR.toCtx
                                        (.bvar 1) natTyR₃.lift.lift :=
                                      .bvar (.succ .zero)
                                    exact hv.defeqU_r wf hctxR.wf.toCtx hnatEqBR
                                  have ⟨hmodT, hmodEval⟩ := hmod hmodC
                                  obtain ⟨_, hmodCi, _, hmodLen⟩ :=
                                    (hmodT 0 []).const_inv wf trivial
                                  have hmodS : TrExprS env [] ΔR q(Nat.mod)
                                      (.const ``Nat.mod []) :=
                                    .const hmodCi rfl (by simpa using hmodLen)
                                  have hsuccSR :=
                                    (hctors.natSuccS
                                      (Us := []) (Δ := ΔR)).1
                                  have hsuccTR :=
                                    (hctors.natSuccS
                                      (Us := []) (Δ := ΔR)).2
                                  have hzeroSR :=
                                    (hctors.natZeroS
                                      (Us := []) (Δ := ΔR)).1
                                  have hzeroTR :=
                                    (hctors.natZeroS
                                      (Us := []) (Δ := ΔR)).2
                                  have haVarS : TrExprS env [] ΔR
                                      (.bvar 2) (.bvar 2) := .bvar (by rfl)
                                  have hbVarS : TrExprS env [] ΔR
                                      (.bvar 1) (.bvar 1) := .bvar (by rfl)
                                  have hsaT := VEnv.HasType.app hsuccTR haVarT
                                  have hsbT := VEnv.HasType.app hsuccTR hbVarT
                                  have hsaS : TrExprS env [] ΔR
                                      (mkApp q(Nat.succ) (.bvar 2))
                                      (.app .natSucc (.bvar 2)) :=
                                    .app hsuccTR haVarT hsuccSR haVarS
                                  have hsbS : TrExprS env [] ΔR
                                      (mkApp q(Nat.succ) (.bvar 1))
                                      (.app .natSucc (.bvar 1)) :=
                                    .app hsuccTR hbVarT hsuccSR hbVarS
                                  have honeSR : TrExprS env [] ΔR
                                      (mkApp q(Nat.succ) q(Nat.zero))
                                      (.natLit 1) :=
                                    .app hsuccTR hzeroTR hsuccSR hzeroSR
                                  have honeTR :=
                                    (hctors.natLitS 1
                                      (Us := []) (Δ := ΔR)).2
                                  have htwoSR : TrExprS env [] ΔR
                                      (mkApp q(Nat.succ)
                                        (mkApp q(Nat.succ) q(Nat.zero)))
                                      (.natLit 2) :=
                                    .app hsuccTR
                                      (VEnv.HasType.app hsuccTR hzeroTR)
                                      hsuccSR honeSR
                                  have htwoTR :=
                                    (hctors.natLitS 2
                                      (Us := []) (Δ := ΔR)).2
                                  let modA := VExpr.app
                                    (VExpr.app (.const ``Nat.mod [])
                                      (VExpr.app .natSucc (.bvar 2))) (.natLit 2)
                                  let modB := VExpr.app
                                    (VExpr.app (.const ``Nat.mod [])
                                      (VExpr.app .natSucc (.bvar 1))) (.natLit 2)
                                  have hmodAS : TrExprS env [] ΔR
                                      (mkApp2 q(Nat.mod)
                                        (mkApp q(Nat.succ) (.bvar 2))
                                        (mkApp q(Nat.succ)
                                          (mkApp q(Nat.succ) q(Nat.zero))))
                                      modA :=
                                    TrExprS.app
                                      (VEnv.HasType.app (hmodT 0 ΔR.toCtx) hsaT)
                                      htwoTR
                                      (TrExprS.app (hmodT 0 ΔR.toCtx) hsaT
                                        hmodS hsaS) htwoSR
                                  have hmodBS : TrExprS env [] ΔR
                                      (mkApp2 q(Nat.mod)
                                        (mkApp q(Nat.succ) (.bvar 1))
                                        (mkApp q(Nat.succ)
                                          (mkApp q(Nat.succ) q(Nat.zero))))
                                      modB :=
                                    TrExprS.app
                                      (VEnv.HasType.app (hmodT 0 ΔR.toCtx) hsbT)
                                      htwoTR
                                      (TrExprS.app (hmodT 0 ΔR.toCtx) hsbT
                                        hmodS hsbS) htwoSR
                                  have hmodAT : env.HasType 0 ΔR.toCtx modA .nat :=
                                    .app (.app (hmodT 0 ΔR.toCtx) hsaT) htwoTR
                                  have hmodBT : env.HasType 0 ΔR.toCtx modB .nat :=
                                    .app (.app (hmodT 0 ΔR.toCtx) hsbT) htwoTR
                                  have hdecideWeak := hdecideS.weakBV wf.ordered
                                    (.skip (.vlam proofTyR) <|
                                      .skip (.vlam natTyR₃) <|
                                        .skip (.vlam natTyR₂) <|
                                          .skip (.vlam natTyR₁) <|
                                            .skip (.vlam funTyR) <|
                                              (.refl : VLCtx.BVLift [] [] 0 0 0 0))
                                  have hdecideSourceLift :
                                      Condition.natEqDecideFn.liftLooseBVars' 0 5 =
                                        Condition.natEqDecideFn :=
                                    Expr.liftLooseBVars_eq_self
                                      hdecideS.closed.looseBVarRange_le
                                  have hdecideWeak' : TrExprS env [] ΔR
                                      Condition.natEqDecideFn
                                      (decide.liftN 5) := by
                                    simpa [ΔR, VLocalDecl.depth,
                                      hdecideSourceLift] using hdecideWeak
                                  have hbitOneCallEqCtx :=
                                    Condition.natEqDecideFn.call_eq wf hctxR.wf
                                      hdecideWeak' hmodAS honeSR hmodAT honeTR
                                      hbitOneLocalS
                                  have hbitTwoCallEqCtx :=
                                    Condition.natEqDecideFn.call_eq wf hctxR.wf
                                      hdecideWeak' hmodBS honeSR hmodBT honeTR
                                      hbitTwoLocalS
                                  have hopCanonR : TrExprS env [] ΔR
                                      (.bvar 4) (.bvar 4) := .bvar (by rfl)
                                  cases hopLocalRS.unique (by trivial) hopCanonR
                                  have hiteWeak := hiteS.weakBV wf.ordered
                                    (.skip (.vlam proofTyR) <|
                                      .skip (.vlam natTyR₃) <|
                                        .skip (.vlam natTyR₂) <|
                                          .skip (.vlam natTyR₁) <|
                                            .skip (.vlam funTyR) <|
                                              (.refl : VLCtx.BVLift [] [] 0 0 0 0))
                                  have hiteSourceLift :
                                      Condition.bool.boolNatITE.liftLooseBVars' 0 5 =
                                        Condition.bool.boolNatITE :=
                                    Expr.liftLooseBVars_eq_self
                                      hiteS.closed.looseBVarRange_le
                                  have hiteWeak' : TrExprS env [] ΔR
                                      Condition.bool.boolNatITE (ite.liftN 5) := by
                                    simpa [ΔR, VLocalDecl.depth, hiteSourceLift] using
                                      hiteWeak
                                  have hiteEqCtx := TrExprS.uniq (Us := []) wf hctxR
                                    hiteLocalS hiteWeak'
                                  have hiteEqFinal₀ :=
                                    VEnv.IsDefEqU.inst_bitwise_outer4 wf
                                      hopR hfR haR hbR
                                      (by simpa [ΔR] using hiteEqCtx)
                                  have hiteClosed : ite.ClosedN :=
                                    (hite.1.closedN' wf.ordered.closed trivial).1
                                  let proofTyRF :=
                                    (((proofTyR.inst op 3).inst (.natLit fuel) 2).inst
                                      (.natLit a) 1).inst (.natLit b)
                                  have hiteEqFinal : env.IsDefEqU 0 [proofTyRF]
                                      ((((iteLocal.inst op 4).inst (.natLit fuel) 3).inst
                                        (.natLit a) 2).inst (.natLit b) 1) ite := by
                                    simpa [proofTyRF, hiteClosed.liftN_eq,
                                      hiteClosed.instN_eq] using hiteEqFinal₀
                                  have hiteEqRoot₀ := hiteEqFinal.instN wf.ordered
                                    (.zero : Ctx.InstN [] hpV proofTyRF 0
                                      [proofTyRF] []) hpTR
                                  have hiteEqRoot : env.IsDefEqU 0 []
                                      (((((iteLocal.inst op 4).inst (.natLit fuel) 3).inst
                                        (.natLit a) 2).inst (.natLit b) 1).inst hpV)
                                      ite := by
                                    simpa [hiteClosed.instN_eq] using hiteEqRoot₀
                                  let bitOneFinal :=
                                    (((((bitOneLocal.inst op 4).inst
                                      (.natLit fuel) 3).inst (.natLit a) 2).inst
                                      (.natLit b) 1).inst hpV)
                                  let bitTwoFinal :=
                                    (((((bitTwoLocal.inst op 4).inst
                                      (.natLit fuel) 3).inst (.natLit a) 2).inst
                                      (.natLit b) 1).inst hpV)
                                  let thenFinal :=
                                    (((((thenLocal.inst op 4).inst
                                      (.natLit fuel) 3).inst (.natLit a) 2).inst
                                      (.natLit b) 1).inst hpV)
                                  let elseFinal :=
                                    (((((elseLocal.inst op 4).inst
                                      (.natLit fuel) 3).inst (.natLit a) 2).inst
                                      (.natLit b) 1).inst hpV)
                                  have hbitOneCallEqFinal :=
                                    VEnv.IsDefEqU.inst_bitwise_outer4 wf
                                      hopR hfR haR hbR
                                      (by simpa [ΔR] using hbitOneCallEqCtx)
                                  have hbitTwoCallEqFinal :=
                                    VEnv.IsDefEqU.inst_bitwise_outer4 wf
                                      hopR hfR haR hbR
                                      (by simpa [ΔR] using hbitTwoCallEqCtx)
                                  have hbitOneCallEqRoot₀ :=
                                    hbitOneCallEqFinal.instN wf.ordered
                                      (.zero : Ctx.InstN [] hpV proofTyRF 0
                                        [proofTyRF] []) hpTR
                                  have hbitTwoCallEqRoot₀ :=
                                    hbitTwoCallEqFinal.instN wf.ordered
                                      (.zero : Ctx.InstN [] hpV proofTyRF 0
                                        [proofTyRF] []) hpTR
                                  have hdecideClosed : decide.ClosedN :=
                                    (hdecide.1.closedN' wf.ordered.closed
                                      trivial).1
                                  have hbitOneCallEqRoot : env.IsDefEqU 0 []
                                      bitOneFinal
                                      (.app (.app decide
                                        (.app (.app (.const ``Nat.mod [])
                                          (.natLit (a + 1))) (.natLit 2)))
                                        (.natLit 1)) := by
                                    simpa [bitOneFinal, modA, VExpr.inst,
                                      VExpr.instVar, VExpr.natLit,
                                      hdecideClosed.liftN_eq,
                                      hdecideClosed.instN_eq,
                                      haClosed.liftN_eq,
                                      haClosed.instN_eq] using
                                        hbitOneCallEqRoot₀
                                  have hbitTwoCallEqRoot : env.IsDefEqU 0 []
                                      bitTwoFinal
                                      (.app (.app decide
                                        (.app (.app (.const ``Nat.mod [])
                                          (.natLit (b + 1))) (.natLit 2)))
                                        (.natLit 1)) := by
                                    simpa [bitTwoFinal, modB, VExpr.inst,
                                      VExpr.instVar, VExpr.natLit,
                                      hdecideClosed.liftN_eq,
                                      hdecideClosed.instN_eq,
                                      hbClosed.liftN_eq,
                                      hbClosed.instN_eq] using
                                        hbitTwoCallEqRoot₀
                                  have honeRootT :=
                                    (hctors.natLitS 1
                                      (Us := []) (Δ := [])).2
                                  have htwoRootT :=
                                    (hctors.natLitS 2
                                      (Us := []) (Δ := [])).2
                                  have hmodACallT : env.HasType 0 []
                                      (.app (.app (.const ``Nat.mod [])
                                        (.natLit (a + 1))) (.natLit 2)) .nat :=
                                    .app (.app (hmodT 0 [])
                                      (hctors.natLitS (a + 1)
                                        (Us := []) (Δ := [])).2) htwoRootT
                                  have hmodBCallT : env.HasType 0 []
                                      (.app (.app (.const ``Nat.mod [])
                                        (.natLit (b + 1))) (.natLit 2)) .nat :=
                                    .app (.app (hmodT 0 [])
                                      (hctors.natLitS (b + 1)
                                        (Us := []) (Δ := [])).2) htwoRootT
                                  have hdecideAEq :=
                                    (hmodEval (a + 1) 2).app_arg wf trivial
                                      hdecide.1 hmodACallT
                                  have hdecideBEq :=
                                    (hmodEval (b + 1) 2).app_arg wf trivial
                                      hdecide.1 hmodBCallT
                                  have hdecideAArgsEq := hdecideAEq.app_same
                                    wf trivial
                                    (.app hdecide.1 hmodACallT) honeRootT
                                  have hdecideBArgsEq := hdecideBEq.app_same
                                    wf trivial
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
                                  have hcallToRightS := hcallToRight
                                  simp [bitOneFinal, bitTwoFinal, thenFinal, elseFinal,
                                    VExpr.inst, VExpr.instVar,
                                    hopClosed.liftN_eq (Nat.zero_le _),
                                    hopClosed.instN_eq] at hcallToRightS
                                  have ⟨haddT, haddEval⟩ := hadd haddC
                                  obtain ⟨_, haddCi, _, haddLen⟩ :=
                                    (haddT 0 []).const_inv wf trivial
                                  have haddS (Δ : VLCtx) : TrExprS env [] Δ
                                      q(Nat.add) (.const ``Nat.add []) :=
                                    .const haddCi rfl (by simpa using haddLen)
                                  have helseLocalS₀ := helseLocalS
                                  cases helseLocalS with
                                  | @app elsePrefix _ _ recTwo _ _ _ _ _ helsePrefixS hrecTwoS =>
                                    have helsePrefixS₀ := helsePrefixS
                                    cases helsePrefixS with
                                    | @app addLocalElse _ _ recOne _ _ _ _ _ haddLocalElseS hrecOneS =>
                                      have haddEqCtx := TrExprS.uniq (Us := []) wf
                                        hctxR haddLocalElseS (haddS ΔR)
                                      have haddLocalCanonT :=
                                        (haddEqCtx.of_r wf hctxR.wf.toCtx
                                          (haddT 0 ΔR.toCtx)).hasType.1
                                      obtain ⟨_, helsePrefixT⟩ := helsePrefixS₀.wf
                                        wf.ordered (Us := []) (Δ := ΔR) hctxR.wf
                                      obtain ⟨_, _, haddLocalT, hrecOneT⟩ :=
                                        helsePrefixT.hasType.1.app_inv wf.ordered
                                          hctxR.wf.toCtx
                                      have haddTypeEq := haddLocalT.uniqU wf
                                        hctxR.wf.toCtx haddLocalCanonT
                                      obtain ⟨_, hrecTypeEq⟩ :=
                                        (haddTypeEq.forallE_inv wf hctxR.wf.toCtx).1
                                      have hrecT := hrecOneT.defeqU_r wf
                                        hctxR.wf.toCtx hrecTypeEq.toU
                                      have haddRecS : TrExprS env [] ΔR
                                          (mkApp q(Nat.add)
                                            (mkAppN r.callFn #[.bvar 4, .bvar 3,
                                              mkApp2 q(Nat.div)
                                                (mkApp q(Nat.succ) (.bvar 2))
                                                (mkApp q(Nat.succ)
                                                  (mkApp q(Nat.succ) q(Nat.zero))),
                                              mkApp2 q(Nat.div)
                                                (mkApp q(Nat.succ) (.bvar 1))
                                                (mkApp q(Nat.succ)
                                                  (mkApp q(Nat.succ) q(Nat.zero))),
                                              r.succProof]))
                                          (.app (.const ``Nat.add [])
                                            recOne) :=
                                        .app (haddT 0 ΔR.toCtx) hrecT
                                          (haddS ΔR) hrecOneS
                                      have helseCanonS : TrExprS env [] ΔR
                                          (mkApp2 q(Nat.add)
                                            (mkAppN r.callFn #[.bvar 4, .bvar 3,
                                              mkApp2 q(Nat.div)
                                                (mkApp q(Nat.succ) (.bvar 2))
                                                (mkApp q(Nat.succ)
                                                  (mkApp q(Nat.succ) q(Nat.zero))),
                                              mkApp2 q(Nat.div)
                                                (mkApp q(Nat.succ) (.bvar 1))
                                                (mkApp q(Nat.succ)
                                                  (mkApp q(Nat.succ) q(Nat.zero))),
                                              r.succProof])
                                            (mkAppN r.callFn #[.bvar 4, .bvar 3,
                                              mkApp2 q(Nat.div)
                                                (mkApp q(Nat.succ) (.bvar 2))
                                                (mkApp q(Nat.succ)
                                                  (mkApp q(Nat.succ) q(Nat.zero))),
                                              mkApp2 q(Nat.div)
                                                (mkApp q(Nat.succ) (.bvar 1))
                                                (mkApp q(Nat.succ)
                                                  (mkApp q(Nat.succ) q(Nat.zero))),
                                              r.succProof]))
                                          (.app (.app (.const ``Nat.add [])
                                            recOne) recOne) :=
                                        .app (VEnv.HasType.app (haddT 0 ΔR.toCtx)
                                            hrecT) hrecT haddRecS hrecOneS
                                      have helseEqCtx := TrExprS.uniq (Us := []) wf
                                        hctxR helseLocalS₀ helseCanonS
                                      have honeCtorS : TrExprS env [] ΔR
                                          (mkApp q(Nat.succ) q(Nat.zero))
                                          (.natLit 1) := by
                                        exact .app
                                          (hctors.natSuccS
                                            (Us := []) (Δ := ΔR)).2
                                          (hctors.natZeroS
                                            (Us := []) (Δ := ΔR)).2
                                          (hctors.natSuccS
                                            (Us := []) (Δ := ΔR)).1
                                          (hctors.natZeroS
                                            (Us := []) (Δ := ΔR)).1
                                      have hdoubleT : env.HasType 0 ΔR.toCtx
                                          (.app (.app (.const ``Nat.add []) recOne)
                                            recOne) .nat :=
                                        .app (.app (haddT 0 ΔR.toCtx) hrecT) hrecT
                                      have haddDoubleS : TrExprS env [] ΔR
                                          (mkApp q(Nat.add)
                                            (mkApp2 q(Nat.add)
                                              (mkAppN r.callFn #[.bvar 4, .bvar 3,
                                                mkApp2 q(Nat.div)
                                                  (mkApp q(Nat.succ) (.bvar 2))
                                                  (mkApp q(Nat.succ)
                                                    (mkApp q(Nat.succ) q(Nat.zero))),
                                                mkApp2 q(Nat.div)
                                                  (mkApp q(Nat.succ) (.bvar 1))
                                                  (mkApp q(Nat.succ)
                                                    (mkApp q(Nat.succ) q(Nat.zero))),
                                                r.succProof])
                                              (mkAppN r.callFn #[.bvar 4, .bvar 3,
                                                mkApp2 q(Nat.div)
                                                  (mkApp q(Nat.succ) (.bvar 2))
                                                  (mkApp q(Nat.succ)
                                                    (mkApp q(Nat.succ) q(Nat.zero))),
                                                mkApp2 q(Nat.div)
                                                  (mkApp q(Nat.succ) (.bvar 1))
                                                  (mkApp q(Nat.succ)
                                                    (mkApp q(Nat.succ) q(Nat.zero))),
                                                r.succProof])))
                                          (.app (.const ``Nat.add [])
                                            (.app (.app (.const ``Nat.add [])
                                              recOne) recOne)) :=
                                        .app (haddT 0 ΔR.toCtx) hdoubleT
                                          (haddS ΔR) helseCanonS
                                      have hthenCanonS : TrExprS env [] ΔR
                                          (mkApp2 q(Nat.add)
                                            (mkApp2 q(Nat.add)
                                              (mkAppN r.callFn #[.bvar 4, .bvar 3,
                                                mkApp2 q(Nat.div)
                                                  (mkApp q(Nat.succ) (.bvar 2))
                                                  (mkApp q(Nat.succ)
                                                    (mkApp q(Nat.succ) q(Nat.zero))),
                                                mkApp2 q(Nat.div)
                                                  (mkApp q(Nat.succ) (.bvar 1))
                                                  (mkApp q(Nat.succ)
                                                    (mkApp q(Nat.succ) q(Nat.zero))),
                                                r.succProof])
                                              (mkAppN r.callFn #[.bvar 4, .bvar 3,
                                                mkApp2 q(Nat.div)
                                                  (mkApp q(Nat.succ) (.bvar 2))
                                                  (mkApp q(Nat.succ)
                                                    (mkApp q(Nat.succ) q(Nat.zero))),
                                                mkApp2 q(Nat.div)
                                                  (mkApp q(Nat.succ) (.bvar 1))
                                                  (mkApp q(Nat.succ)
                                                    (mkApp q(Nat.succ) q(Nat.zero))),
                                                r.succProof]))
                                            (mkApp q(Nat.succ) q(Nat.zero)))
                                          (.app (.app (.const ``Nat.add [])
                                            (.app (.app (.const ``Nat.add [])
                                              recOne) recOne)) (.natLit 1)) :=
                                        .app (VEnv.HasType.app (haddT 0 ΔR.toCtx)
                                            hdoubleT)
                                          (hctors.natLitS 1
                                            (Us := []) (Δ := ΔR)).2
                                          haddDoubleS honeCtorS
                                      have hthenEqCtx := TrExprS.uniq (Us := []) wf
                                        hctxR hthenLocalS hthenCanonS
                                      have helseEqFinal₀ :=
                                        VEnv.IsDefEqU.inst_bitwise_outer4 wf
                                          hopR hfR haR hbR helseEqCtx
                                      have hthenEqFinal₀ :=
                                        VEnv.IsDefEqU.inst_bitwise_outer4 wf
                                          hopR hfR haR hbR hthenEqCtx
                                      have helseEqRoot₀ := helseEqFinal₀.instN wf.ordered
                                        (.zero : Ctx.InstN [] hpV proofTyRF 0
                                          [proofTyRF] []) hpTR
                                      have hthenEqRoot₀ := hthenEqFinal₀.instN wf.ordered
                                        (.zero : Ctx.InstN [] hpV proofTyRF 0
                                          [proofTyRF] []) hpTR
                                      let recFinal :=
                                        (((((recOne.inst op 4).inst
                                          (.natLit fuel) 3).inst (.natLit a) 2).inst
                                          (.natLit b) 1).inst hpV)
                                      have helseEqRoot : env.IsDefEqU 0 [] elseFinal
                                          (.app (.app (.const ``Nat.add []) recFinal)
                                            recFinal) := by
                                        simpa [elseFinal, recFinal, VExpr.inst,
                                          VExpr.instVar] using helseEqRoot₀
                                      have hthenEqRoot : env.IsDefEqU 0 [] thenFinal
                                          (.app (.app (.const ``Nat.add [])
                                            (.app (.app (.const ``Nat.add []) recFinal)
                                              recFinal)) (.natLit 1)) := by
                                        simpa [thenFinal, recFinal, VExpr.inst,
                                          VExpr.instVar] using hthenEqRoot₀
                                      have hrecOneS₀ := hrecOneS
                                      cases hrecOneS with
                                      | @app recPrefix _ _ proofLocal _ _ _ _ _ hrecPrefixS hproofLocalS =>
                                        cases hrecPrefixS with
                                        | @app recPrefixB _ _ divBLocal _ _ _ _ _ hrecPrefixBS hdivBLocalS =>
                                          cases hrecPrefixBS with
                                          | @app recPrefixA _ _ divALocal _ _ _ _ _ hrecPrefixAS hdivALocalS =>
                                            cases hrecPrefixAS with
                                            | @app recPrefixFuel _ _ fuelLocalR _ _ _ _ _ hrecPrefixFuelS hfuelLocalRS =>
                                              cases hrecPrefixFuelS with
                                              | @app callLocalR _ _ opLocalR₂ _ _ _ _ _ hcallLocalRS hopLocalR₂S =>
                                                have hopCanonR₂ : TrExprS env [] ΔR
                                                    (.bvar 4) (.bvar 4) := .bvar (by rfl)
                                                have hfuelCanonR : TrExprS env [] ΔR
                                                    (.bvar 3) (.bvar 3) := .bvar (by rfl)
                                                cases hopLocalR₂S.unique (by trivial) hopCanonR₂
                                                cases hfuelLocalRS.unique (by trivial) hfuelCanonR
                                                have hcallWeakR := hcallS.weakBV wf.ordered
                                                  (.skip (.vlam proofTyR) <|
                                                    .skip (.vlam natTyR₃) <|
                                                      .skip (.vlam natTyR₂) <|
                                                        .skip (.vlam natTyR₁) <|
                                                          .skip (.vlam funTyR) <|
                                                            (.refl : VLCtx.BVLift [] [] 0 0 0 0))
                                                have hcallWeakR' : TrExprS env [] ΔR
                                                    r.callFn (callV.liftN 5) := by
                                                  simpa [ΔR, VLocalDecl.depth,
                                                    hcallSourceLift] using hcallWeakR
                                                have hcallEqCtxR := TrExprS.uniq
                                                  (Us := []) wf hctxR hcallLocalRS hcallWeakR'
                                                have ⟨hdivT, hdivEval⟩ := hdiv hdivC
                                                obtain ⟨_, hdivCi, _, hdivLen⟩ :=
                                                  (hdivT 0 []).const_inv wf trivial
                                                have hdivS (Δ : VLCtx) : TrExprS env [] Δ
                                                    q(Nat.div) (.const ``Nat.div []) :=
                                                  .const hdivCi rfl (by simpa using hdivLen)
                                                have hsuccS :=
                                                  (hctors.natSuccS
                                                    (Us := []) (Δ := ΔR)).1
                                                have hsuccTR :=
                                                  (hctors.natSuccS
                                                    (Us := []) (Δ := ΔR)).2
                                                have hzeroSR :=
                                                  (hctors.natZeroS
                                                    (Us := []) (Δ := ΔR)).1
                                                have hzeroTR :=
                                                  (hctors.natZeroS
                                                    (Us := []) (Δ := ΔR)).2
                                                have haBvarS : TrExprS env [] ΔR
                                                    (.bvar 2) (.bvar 2) := .bvar (by rfl)
                                                have hbBvarS : TrExprS env [] ΔR
                                                    (.bvar 1) (.bvar 1) := .bvar (by rfl)
                                                have honeSR : TrExprS env [] ΔR
                                                    (mkApp q(Nat.succ) q(Nat.zero))
                                                    (.natLit 1) :=
                                                  .app hsuccTR hzeroTR hsuccS hzeroSR
                                                have htwoSR : TrExprS env [] ΔR
                                                    (mkApp q(Nat.succ)
                                                      (mkApp q(Nat.succ) q(Nat.zero)))
                                                    (.natLit 2) :=
                                                  .app hsuccTR
                                                    (VEnv.HasType.app hsuccTR hzeroTR)
                                                    hsuccS honeSR
                                                cases hdivALocalS with
                                                | @app divAPrefix _ _ twoALocal _ _ _ _ _ hdivAPrefixS htwoALocalS =>
                                                  cases hdivAPrefixS with
                                                  | @app divLocalA _ _ succALocalR _ _ _ _ _ hdivLocalAS hsuccALocalRS =>
                                                    cases hsuccALocalRS with
                                                    | @app succLocalRA _ _ aBvarLocal _ _ _ _ _ hsuccLocalRAS haBvarLocalS =>
                                                      cases hdivBLocalS with
                                                      | @app divBPrefix _ _ twoBLocal _ _ _ _ _ hdivBPrefixS htwoBLocalS =>
                                                        cases hdivBPrefixS with
                                                        | @app divLocalB _ _ succBLocalR _ _ _ _ _ hdivLocalBS hsuccBLocalRS =>
                                                          cases hsuccBLocalRS with
                                                          | @app succLocalRB _ _ bBvarLocal _ _ _ _ _ hsuccLocalRBS hbBvarLocalS =>
                                                            cases haBvarLocalS.unique (by trivial) haBvarS
                                                            cases hbBvarLocalS.unique (by trivial) hbBvarS
                                                            have hdivAEqCtx := TrExprS.uniq
                                                              (Us := []) wf hctxR
                                                              hdivLocalAS (hdivS ΔR)
                                                            have hdivBEqCtx := TrExprS.uniq
                                                              (Us := []) wf hctxR
                                                              hdivLocalBS (hdivS ΔR)
                                                            have hsuccRAEqCtx := TrExprS.uniq
                                                              (Us := []) wf hctxR
                                                              hsuccLocalRAS hsuccS
                                                            have hsuccRBEqCtx := TrExprS.uniq
                                                              (Us := []) wf hctxR
                                                              hsuccLocalRBS hsuccS
                                                            have htwoAEqCtx := TrExprS.uniq
                                                              (Us := []) wf hctxR
                                                              htwoALocalS htwoSR
                                                            have htwoBEqCtx := TrExprS.uniq
                                                              (Us := []) wf hctxR
                                                              htwoBLocalS htwoSR
                                                            have liftOuter
                                                                {x y : VExpr}
                                                                (hxy : env.IsDefEqU 0
                                                                  ΔR.toCtx x y) := by
                                                              have hxy' :=
                                                                VEnv.IsDefEqU.inst_bitwise_outer4
                                                                  wf hopR hfR haR hbR
                                                                  (by simpa [ΔR] using hxy)
                                                              exact hxy'.instN wf.ordered
                                                                (.zero : Ctx.InstN [] hpV
                                                                  proofTyRF 0
                                                                  [proofTyRF] []) hpTR
                                                            let closeOuter (x : VExpr) :=
                                                              (((((x.inst op 4).inst
                                                                (.natLit fuel) 3).inst
                                                                (.natLit a) 2).inst
                                                                (.natLit b) 1).inst hpV)
                                                            have hdivAEqRoot := liftOuter hdivAEqCtx
                                                            have hdivBEqRoot := liftOuter hdivBEqCtx
                                                            have hsuccRAEqRoot := liftOuter hsuccRAEqCtx
                                                            have hsuccRBEqRoot := liftOuter hsuccRBEqCtx
                                                            have htwoAEqRoot := liftOuter htwoAEqCtx
                                                            have htwoBEqRoot := liftOuter htwoBEqCtx
                                                            have hcallEqRoot := liftOuter hcallEqCtxR
                                                            have htwoTR :=
                                                              (hctors.natLitS 2
                                                                (Us := []) (Δ := [])).2
                                                            have htwoClosed :
                                                                (VExpr.natLit 2).ClosedN :=
                                                              (htwoTR.closedN' wf.ordered.closed
                                                                trivial).1
                                                            simp [VExpr.inst, VExpr.instVar, hsuccClosed.instN_eq, htwoClosed.instN_eq, hcallVClosed.liftN_eq, hcallVClosed.instN_eq] at hdivAEqRoot hdivBEqRoot hsuccRAEqRoot hsuccRBEqRoot htwoAEqRoot htwoBEqRoot hcallEqRoot
                                                            let divAHead := closeOuter divLocalA
                                                            let divBHead := closeOuter divLocalB
                                                            let succAHead := closeOuter succLocalRA
                                                            let succBHead := closeOuter succLocalRB
                                                            let twoA := closeOuter twoALocal
                                                            let twoB := closeOuter twoBLocal
                                                            let divAFinal :=
                                                              VExpr.app (VExpr.app divAHead
                                                                (VExpr.app succAHead (.natLit a))) twoA
                                                            let divBFinal :=
                                                              VExpr.app (VExpr.app divBHead
                                                                (VExpr.app succBHead (.natLit b))) twoB
                                                            change env.IsDefEqU 0 [] divAHead
                                                              (.const ``Nat.div []) at hdivAEqRoot
                                                            change env.IsDefEqU 0 [] divBHead
                                                              (.const ``Nat.div []) at hdivBEqRoot
                                                            change env.IsDefEqU 0 [] succAHead
                                                              .natSucc at hsuccRAEqRoot
                                                            change env.IsDefEqU 0 [] succBHead
                                                              .natSucc at hsuccRBEqRoot
                                                            change env.IsDefEqU 0 [] twoA
                                                              (.natLit 2) at htwoAEqRoot
                                                            change env.IsDefEqU 0 [] twoB
                                                              (.natLit 2) at htwoBEqRoot
                                                            have hsuccRootT :=
                                                              (hctors.natSuccS
                                                                (Us := []) (Δ := [])).2
                                                            have hsuccAHeadT :=
                                                              (hsuccRAEqRoot.of_r wf trivial
                                                                hsuccRootT).hasType.1
                                                            have hsuccBHeadT :=
                                                              (hsuccRBEqRoot.of_r wf trivial
                                                                hsuccRootT).hasType.1
                                                            have hsuccAEval : env.IsDefEqU 0 []
                                                                (.app succAHead (.natLit a))
                                                                (.natLit (a + 1)) := by
                                                              simpa [VExpr.natLit] using
                                                                hsuccRAEqRoot.app_same wf trivial
                                                                  hsuccAHeadT haT
                                                            have hsuccBEval : env.IsDefEqU 0 []
                                                                (.app succBHead (.natLit b))
                                                                (.natLit (b + 1)) := by
                                                              simpa [VExpr.natLit] using
                                                                hsuccRBEqRoot.app_same wf trivial
                                                                  hsuccBHeadT hbT
                                                            have hdivAHeadT :=
                                                              (hdivAEqRoot.of_r wf trivial
                                                                (hdivT 0 [])).hasType.1
                                                            have hdivBHeadT :=
                                                              (hdivBEqRoot.of_r wf trivial
                                                                (hdivT 0 [])).hasType.1
                                                            have hdivAPrefixEq :=
                                                              hdivAEqRoot.app_both wf trivial
                                                                hsuccAEval hdivAHeadT
                                                                (hsuccAEval.of_r wf trivial
                                                                  (hctors.natLitS
                                                                    (a + 1) (Us := [])
                                                                    (Δ := [])).2).hasType.1
                                                            have hdivBPrefixEq :=
                                                              hdivBEqRoot.app_both wf trivial
                                                                hsuccBEval hdivBHeadT
                                                                (hsuccBEval.of_r wf trivial
                                                                  (hctors.natLitS
                                                                    (b + 1) (Us := [])
                                                                    (Δ := [])).2).hasType.1
                                                            have htwoAT :=
                                                              (htwoAEqRoot.of_r wf trivial
                                                                htwoTR).hasType.1
                                                            have htwoBT :=
                                                              (htwoBEqRoot.of_r wf trivial
                                                                htwoTR).hasType.1
                                                            have hdivAEval : env.IsDefEqU 0 []
                                                                divAFinal
                                                                (.natLit ((a + 1) / 2)) := by
                                                              have hprefixT :=
                                                                (hdivAPrefixEq.of_r wf trivial
                                                                  (.app (hdivT 0 [])
                                                                    (hctors.natLitS
                                                                      (a + 1) (Us := [])
                                                                      (Δ := [])).2)).hasType.1
                                                              exact (hdivAPrefixEq.app_both wf trivial
                                                                htwoAEqRoot
                                                                hprefixT htwoAT).trans
                                                                  wf trivial (hdivEval (a + 1) 2)
                                                            have hdivBEval : env.IsDefEqU 0 []
                                                                divBFinal
                                                                (.natLit ((b + 1) / 2)) := by
                                                              have hprefixT :=
                                                                (hdivBPrefixEq.of_r wf trivial
                                                                  (.app (hdivT 0 [])
                                                                    (hctors.natLitS
                                                                      (b + 1) (Us := [])
                                                                      (Δ := [])).2)).hasType.1
                                                              exact (hdivBPrefixEq.app_both wf trivial
                                                                htwoBEqRoot
                                                                hprefixT htwoBT).trans
                                                                  wf trivial (hdivEval (b + 1) 2)
                                                            obtain ⟨_, hrecCtxWF⟩ :=
                                                              hrecOneS₀.wf wf.ordered
                                                                (Us := []) (Δ := ΔR) hctxR.wf
                                                            have hrecOuterT :=
                                                              VEnv.HasType.inst_bitwise_outer4 wf
                                                                hopR hfR haR hbR
                                                                (by simpa [ΔR] using
                                                                  hrecCtxWF.hasType.1)
                                                            have hrecRootT := hrecOuterT.instN
                                                              wf.ordered
                                                              (.zero : Ctx.InstN [] hpV
                                                                proofTyRF 0 [proofTyRF] []) hpTR
                                                            change env.HasType 0 [] recFinal _ at hrecRootT
                                                            obtain ⟨_, _, hrecPrefixBT,
                                                                hproofFinalT⟩ :=
                                                              hrecRootT.app_inv wf.ordered trivial
                                                            obtain ⟨_, _, hrecPrefixAT,
                                                                hdivBFinalT⟩ :=
                                                              hrecPrefixBT.app_inv wf.ordered trivial
                                                            obtain ⟨_, _, hrecPrefixFuelT,
                                                                hdivAFinalT⟩ :=
                                                              hrecPrefixAT.app_inv wf.ordered trivial
                                                            obtain ⟨_, _, hrecPrefixOpT,
                                                                hfuelFinalT⟩ :=
                                                              hrecPrefixFuelT.app_inv wf.ordered trivial
                                                            obtain ⟨_, _, hcallHeadT,
                                                                hopFinalT⟩ :=
                                                              hrecPrefixOpT.app_inv wf.ordered trivial
                                                            let callHead := closeOuter callLocalR
                                                            let proofFinal := closeOuter proofLocal
                                                            change env.IsDefEqU 0 [] callHead callV at hcallEqRoot
                                                            simp [divAFinal, divBFinal, divAHead,
                                                              divBHead, succAHead, succBHead,
                                                              twoA, twoB, closeOuter, VExpr.inst,
                                                              VExpr.instVar,
                                                              haClosed.liftN_eq,
                                                              haClosed.instN_eq,
                                                              hbClosed.liftN_eq,
                                                              hbClosed.instN_eq] at hdivAFinalT hdivBFinalT
                                                            change env.HasType 0 [] divAFinal _ at hdivAFinalT
                                                            change env.HasType 0 [] divBFinal _ at hdivBFinalT
                                                            simp [callHead, proofFinal, divAFinal,
                                                              divBFinal, divAHead, divBHead,
                                                              succAHead, succBHead, twoA, twoB,
                                                              closeOuter, VExpr.inst, VExpr.instVar,
                                                              hopClosed.liftN_eq,
                                                              hopClosed.instN_eq,
                                                              hfClosed.liftN_eq,
                                                              hfClosed.instN_eq,
                                                              haClosed.liftN_eq,
                                                              haClosed.instN_eq,
                                                              hbClosed.liftN_eq,
                                                              hbClosed.instN_eq] at hrecPrefixBT hrecPrefixAT hrecPrefixFuelT hrecPrefixOpT hcallHeadT hopFinalT hfuelFinalT hproofFinalT
                                                            have hrecOpEq := hcallEqRoot.app_same wf
                                                              trivial hcallHeadT hopFinalT
                                                            have hrecFuelEq := hrecOpEq.app_same wf
                                                              trivial hrecPrefixOpT hfuelFinalT
                                                            have hrecAEq := hrecFuelEq.app_both wf
                                                              trivial hdivAEval hrecPrefixFuelT
                                                              hdivAFinalT
                                                            have hrecBEq := hrecAEq.app_both wf
                                                              trivial hdivBEval hrecPrefixAT
                                                              hdivBFinalT
                                                            have hrecCallEq := hrecBEq.app_same wf
                                                              trivial hrecPrefixBT hproofFinalT
                                                            have hrecCallEq' : env.IsDefEqU 0 [] recFinal
                                                                (((((callV.app op).app (.natLit fuel)).app
                                                                  (.natLit ((a + 1) / 2))).app
                                                                  (.natLit ((b + 1) / 2))).app proofFinal) := by
                                                              simpa [recFinal, callHead, proofFinal,
                                                                divAFinal, divBFinal, divAHead,
                                                                divBHead, succAHead, succBHead,
                                                                twoA, twoB, closeOuter, VExpr.inst,
                                                                VExpr.instVar, hopClosed.liftN_eq,
                                                                hopClosed.instN_eq,
                                                                hfClosed.liftN_eq,
                                                                hfClosed.instN_eq,
                                                                haClosed.liftN_eq,
                                                                haClosed.instN_eq,
                                                                hbClosed.liftN_eq,
                                                                hbClosed.instN_eq] using hrecCallEq
                                                            have hrecSelf := hrecCallEq'.trans
                                                              wf trivial hrecCallEq'.symm
                                                            refine ⟨recFinal,
                                                              ⟨callV, .natLit fuel,
                                                                proofFinal, hcallS, ⟨_, hfT⟩,
                                                                hrecCallEq'⟩,
                                                              hrecSelf, ?_⟩
                                                            intro q hrecQ
                                                            change env.IsDefEqU 0 [] e
                                                              (.app (.app (.app
                                                                (((((iteLocal.inst op 4).inst
                                                                  (.natLit fuel) 3).inst
                                                                  (.natLit a) 2).inst
                                                                  (.natLit b) 1).inst hpV)
                                                                (.app (.app op bitOneFinal)
                                                                  bitTwoFinal)) thenFinal)
                                                                elseFinal) at hcallToRightS
                                                            have hrightStructT :=
                                                              (hcallToRightS.of_l wf trivial
                                                                heT).hasType.2
                                                            obtain ⟨_, _, hrightTwoT,
                                                                helseFinalT⟩ :=
                                                              hrightStructT.app_inv
                                                                wf.ordered trivial
                                                            obtain ⟨_, _, hrightOneT,
                                                                hthenFinalT⟩ :=
                                                              hrightTwoT.app_inv
                                                                wf.ordered trivial
                                                            obtain ⟨_, _, hiteFinalT,
                                                                hcondFinalT⟩ :=
                                                              hrightOneT.app_inv
                                                                wf.ordered trivial
                                                            obtain ⟨_, _, hopBitOneT,
                                                                hbitTwoFinalT⟩ :=
                                                              hcondFinalT.app_inv
                                                                wf.ordered trivial
                                                            have hbool : env.contains ``Bool := by
                                                              obtain ⟨_, hopSort⟩ :=
                                                                hop.1.isType wf trivial
                                                              obtain ⟨hboolTy, _⟩ :=
                                                                hopSort.forallE_inv wf
                                                              obtain ⟨_, hboolSort⟩ := hboolTy
                                                              obtain ⟨_, hboolCi, _, _⟩ :=
                                                                hboolSort.const_inv wf trivial
                                                              exact ⟨_, hboolCi⟩
                                                            have hbitOneCanonT :=
                                                              (hctors.boolLitS
                                                                (((a + 1) % 2) == 1)
                                                                (Us := []) (Δ := [])).2
                                                            have hbitTwoCanonT :=
                                                              (hctors.boolLitS
                                                                (((b + 1) % 2) == 1)
                                                                (Us := []) (Δ := [])).2
                                                            have hbitOneFinalT :=
                                                              (hbitOneEval.of_r wf trivial
                                                                hbitOneCanonT).hasType.1
                                                            have hopOneEq := hbitOneEval.app_arg
                                                              wf trivial hop.1 hbitOneFinalT
                                                            have hopArgsEq := hopOneEq.app_both
                                                              wf trivial hbitTwoEval
                                                              hopBitOneT hbitTwoFinalT
                                                            have hcondEval := hopArgsEq.trans wf trivial
                                                              (hop.2 (((a + 1) % 2) == 1)
                                                                (((b + 1) % 2) == 1))
                                                            have hiteCondEq := hiteEqRoot.app_both
                                                              wf trivial hcondEval
                                                              hiteFinalT hcondFinalT
                                                            have hqT :=
                                                              (hctors.natLitS q
                                                                (Us := []) (Δ := [])).2
                                                            have hrecNatT :=
                                                              (hrecQ.of_r wf trivial hqT).hasType.1
                                                            have haddRecEq := hrecQ.app_arg
                                                              wf trivial (haddT 0 []) hrecNatT
                                                            have haddRecT :=
                                                              VEnv.HasType.app (haddT 0 []) hrecNatT
                                                            have hdoubleArgsEq := haddRecEq.app_both
                                                              wf trivial hrecQ haddRecT hrecNatT
                                                            have hdoubleEval :=
                                                              hdoubleArgsEq.trans wf trivial
                                                                (haddEval q q)
                                                            have helseEval := helseEqRoot.trans
                                                              wf trivial hdoubleEval
                                                            have hdoubleLitT :=
                                                              (hctors.natLitS (q + q)
                                                                (Us := []) (Δ := [])).2
                                                            have hdoubleT :=
                                                              (hdoubleEval.of_r wf trivial
                                                                hdoubleLitT).hasType.1
                                                            have haddDoubleEq :=
                                                              hdoubleEval.app_arg wf trivial
                                                                (haddT 0 []) hdoubleT
                                                            have haddDoubleT :=
                                                              VEnv.HasType.app (haddT 0 []) hdoubleT
                                                            have hthenArgsEq :=
                                                              haddDoubleEq.app_same wf trivial
                                                                haddDoubleT honeRootT
                                                            have hthenEval := hthenEqRoot.trans
                                                              wf trivial <| hthenArgsEq.trans
                                                                wf trivial (haddEval (q + q) 1)
                                                            have hiteThenEq := hiteCondEq.app_both
                                                              wf trivial hthenEval
                                                              hrightOneT hthenFinalT
                                                            have hiteBranchesEq :=
                                                              hiteThenEq.app_both wf trivial
                                                                helseEval hrightTwoT helseFinalT
                                                            have hselect := hite.2
                                                              (f (((a + 1) % 2) == 1)
                                                                (((b + 1) % 2) == 1))
                                                              (q + q + 1) (q + q)
                                                            simpa using hcallToRightS.trans wf trivial
                                                              (hiteBranchesEq.trans wf trivial hselect)

end Lean4Lean.Environment
