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
                cases hprefixFuelS with
                | @app callLocal _ _ opLocal _ _ _ _ _ hcallLocalS hopLocalS =>
                  let ΔL : VLCtx :=
                    [(none, .vlam proofTyL), (none, .vlam natTyL₂),
                      (none, .vlam natTyL₁), (none, .vlam funTyL)]
                  have hopCanon : TrExprS env [] ΔL (.bvar 3) (.bvar 3) :=
                    .bvar (by rfl)
                  have hbCanon : TrExprS env [] ΔL (.bvar 1) (.bvar 1) :=
                    .bvar (by rfl)
                  have hpCanon : TrExprS env [] ΔL (.bvar 0) (.bvar 0) :=
                    .bvar (by rfl)
                  have hzeroCanon :=
                    (hctors.natZeroS (Us := []) (Δ := ΔL)).1
                  cases hopLocalS.unique (by trivial) hopCanon
                  cases hbLocalS.unique (by trivial) hbCanon
                  cases hpLocalS.unique (by trivial) hpCanon
                  cases hzeroLocalS.unique (by trivial) hzeroCanon
                  cases hfuelLocalS with
                  | @app succLocal _ _ fuelArgLocal _ _ _ _ _
                      hsuccLocalS hfuelArgLocalS =>
                    have hfuelArgCanon : TrExprS env [] ΔL
                        (.bvar 2) (.bvar 2) := .bvar (by rfl)
                    have hsuccCanon :=
                      (hctors.natSuccS (Us := []) (Δ := ΔL)).1
                    cases hfuelArgLocalS.unique (by trivial) hfuelArgCanon
                    have hctxL : VLCtx.IsDefEq env 0 ΔL ΔL :=
                      .refl wf ⟨⟨⟨⟨trivial, nofun, hfunTyL⟩,
                        nofun, hnatTyL₁⟩, nofun, hnatTyL₂⟩,
                        nofun, hproofTyL⟩
                    have hcallWeak := hcallS.weakBV wf.ordered
                      (.skip (.vlam proofTyL) <| .skip (.vlam natTyL₂) <|
                        .skip (.vlam natTyL₁) <| .skip (.vlam funTyL) <|
                          (.refl : VLCtx.BVLift [] [] 0 0 0 0))
                    have hcallSourceLift :
                        r.callFn.liftLooseBVars' 0 4 = r.callFn :=
                      Expr.liftLooseBVars_eq_self
                        hcallS.closed.looseBVarRange_le
                    have hcallWeak' : TrExprS env [] ΔL r.callFn
                        (callV.liftN 4) := by
                      simpa [ΔL, VLocalDecl.depth, hcallSourceLift] using
                        hcallWeak
                    have hcallEqCtx := TrExprS.uniq (Us := []) wf hctxL
                      hcallLocalS hcallWeak'
                    have hsuccEqCtx := TrExprS.uniq (Us := []) wf hctxL
                      hsuccLocalS hsuccCanon
                    have hcallEqFinal₀ :=
                      VEnv.IsDefEqU.inst_bitwise_outer3 wf hopL hfL hbL
                        (by simpa [ΔL] using hcallEqCtx)
                    have hsuccEqFinal₀ :=
                      VEnv.IsDefEqU.inst_bitwise_outer3 wf hopL hfL hbL
                        (by simpa [ΔL] using hsuccEqCtx)
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
                    have hcallEqFinal : env.IsDefEqU 0
                        [((proofTyL.inst op 2).inst (.natLit fuel) 1).inst
                          (.natLit b)]
                        (((callLocal.inst op 3).inst (.natLit fuel) 2).inst
                          (.natLit b) 1) callV := by
                      simpa [hcallVClosed.liftN_eq,
                        hcallVClosed.instN_eq] using hcallEqFinal₀
                    have hsuccEqFinal : env.IsDefEqU 0
                        [((proofTyL.inst op 2).inst (.natLit fuel) 1).inst
                          (.natLit b)]
                        (((succLocal.inst op 3).inst (.natLit fuel) 2).inst
                          (.natLit b) 1) .natSucc := by
                      simpa [hsuccClosed.instN_eq] using hsuccEqFinal₀
                    let proofTyLF :=
                      ((proofTyL.inst op 2).inst (.natLit fuel) 1).inst
                        (.natLit b)
                    have hprefixEqU := hprefixEq
                    obtain ⟨_, hprefixEqD⟩ := hprefixEq
                    obtain ⟨hproofTyLFType, _, hbodyEqFinal⟩ :=
                      hprefixEqD.hasType.1.lam_inv wf trivial
                    have hΓ : OnCtx [proofTyLF] (env.IsType 0) :=
                      ⟨trivial, hproofTyLFType⟩
                    obtain ⟨_, hbodyLT⟩ := hbodyLS.wf wf.ordered
                      (Us := []) (Δ := ΔL) hctxL.wf
                    obtain ⟨_, _, hprefixLocalT, _⟩ :=
                      hbodyLT.hasType.1.app_inv wf.ordered hctxL.wf.toCtx
                    have hprefixLocalFinalT₀ :=
                      VEnv.HasType.inst_bitwise_outer3 wf hopL hfL hbL
                        (by simpa [ΔL] using hprefixLocalT)
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
                    let callFinal :=
                      ((callLocal.inst op 3).inst (.natLit fuel) 2).inst
                        (.natLit b) 1
                    let succFinal :=
                      ((succLocal.inst op 3).inst (.natLit fuel) 2).inst
                        (.natLit b) 1
                    let prefixFinal := VExpr.app (VExpr.app (VExpr.app
                      (VExpr.app callFinal op)
                      (VExpr.app succFinal (.natLit fuel))) .natZero) (.natLit b)
                    have hprefixLocalFinalT := hprefixLocalFinalT₀
                    simp [proofTyLF, callFinal, succFinal, prefixFinal,
                        hopClosed.liftN_eq, hopClosed.instN_eq,
                        hfClosed.liftN_eq, hfClosed.instN_eq,
                        hbClosed.liftN_eq, hbClosed.instN_eq,
                        hzClosed.instN_eq, VExpr.inst] at hprefixLocalFinalT
                    obtain ⟨_, _, hprefixZeroLocalT, hbLocalFinalT⟩ :=
                      VEnv.HasType.app_inv wf.ordered hΓ hprefixLocalFinalT
                    obtain ⟨_, _, hprefixFuelLocalT, hzLocalFinalT⟩ :=
                      hprefixZeroLocalT.app_inv wf.ordered hΓ
                    obtain ⟨_, _, hprefixOpLocalT, hfuelLocalFinalT⟩ :=
                      hprefixFuelLocalT.app_inv wf.ordered hΓ
                    obtain ⟨_, _, hcallFinalT, hopLocalFinalT⟩ :=
                      hprefixOpLocalT.app_inv wf.ordered hΓ
                    have hcallAppEq := hcallEqFinal.app_same wf hΓ
                      hcallFinalT hopLocalFinalT
                    have hsuccFinalT :=
                      (hsuccEqFinal.of_r wf hΓ (hsuccT.weak0 wf)).hasType.1
                    have hsuccAppEq := hsuccEqFinal.app_same wf hΓ
                      hsuccFinalT (hfT.weak0 wf)
                    have hsuccEval : env.IsDefEqU 0 [proofTyLF]
                        (.app succFinal (.natLit fuel)) (.natLit (fuel + 1)) := by
                      simpa [succFinal, VExpr.natLit] using hsuccAppEq
                    have hfuelLocalFinalT' := hfuelLocalFinalT
                    simp [succFinal, VExpr.inst, VExpr.instVar,
                      VExpr.lift, VExpr.liftN, liftVar,
                      hfClosed.liftN_eq, hfClosed.instN_eq] at hfuelLocalFinalT'
                    have hprefixFuelEq := hcallAppEq.app_both wf hΓ
                      hsuccEval
                      hprefixOpLocalT hfuelLocalFinalT'
                    have hprefixFuelLocalT' := hprefixFuelLocalT
                    have hprefixZeroLocalT' := hprefixZeroLocalT
                    have hbLocalFinalT' := hbLocalFinalT
                    simp [VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.liftN,
                      liftVar, hfClosed.liftN_eq, hfClosed.instN_eq,
                      hbClosed.liftN_eq, hbClosed.instN_eq] at hprefixFuelLocalT' hprefixZeroLocalT' hbLocalFinalT'
                    have hprefixZeroEq := hprefixFuelEq.app_same wf hΓ
                      hprefixFuelLocalT' hzLocalFinalT
                    have hprefixLocalEq := hprefixZeroEq.app_same wf hΓ
                      hprefixZeroLocalT' hbLocalFinalT'
                    have hcanonFuelT :=
                      (hfuelEq.of_l wf trivial hfuelT).hasType.2
                    have hrelFuelEq := hfuelEq.app_arg wf trivial
                      hprefixOpT hfuelT
                    have hcanonFuelPrefixT :=
                      (hrelFuelEq.of_l wf trivial hprefixFuelT).hasType.2
                    have hrelZeroEq := hrelFuelEq.app_same wf trivial
                      hprefixFuelT hzeroArgT
                    have hcanonZeroT :=
                      (hrelZeroEq.of_l wf trivial hprefixZeroT).hasType.2
                    have hrelPrefixEq := hrelZeroEq.app_same wf trivial
                      hprefixZeroT hbArgT
                    have hrelPrefixEqW := hrelPrefixEq.weak0
                      (Γ := [proofTyLF]) wf
                    have hlocalRelEq := hprefixLocalEq.trans wf hΓ
                      hrelPrefixEqW.symm
                    have hprefixLocalFinalT' := hprefixLocalFinalT
                    have hrelPrefixLocalT :=
                      (hlocalRelEq.of_l wf hΓ hprefixLocalFinalT').hasType.2
                    have hrelPrefixWeakT := hprefixCallT.weak0
                      (Γ := [proofTyLF]) wf
                    have hforallEq := hrelPrefixLocalT.uniqU wf hΓ
                      hrelPrefixWeakT
                    obtain ⟨_, hdomainEq⟩ :=
                      (hforallEq.forallE_inv wf hΓ).1
                    have hbodyFinalT := hbodyEqFinal.hasType.1
                    simp [VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.liftN,
                      liftVar, hopClosed.liftN_eq, hopClosed.instN_eq,
                      hfClosed.liftN_eq, hfClosed.instN_eq,
                      hbClosed.liftN_eq, hbClosed.instN_eq,
                      hzClosed.instN_eq] at hbodyFinalT
                    obtain ⟨proofArgTy, _, hbodyPrefixT, hproofVarT⟩ :=
                      VEnv.HasType.app_inv wf.ordered hΓ hbodyFinalT
                    obtain ⟨proofSort, hproofTyLFSort⟩ := hproofTyLFType
                    have hproofTyLFClosed :=
                      (hproofTyLFSort.closedN' wf.ordered.closed trivial).1
                    have hproofVarCanon : env.HasType 0 [proofTyLF]
                        (.bvar 0) proofTyLF := by
                      have hb : env.HasType 0 [proofTyLF] (.bvar 0)
                          proofTyLF.lift := .bvar .zero
                      rw [hproofTyLFClosed.lift_eq] at hb
                      exact hb
                    have hproofArgEq := hproofVarT.uniqU wf hΓ hproofVarCanon
                    have hlocalForallEq := hprefixLocalFinalT'.uniqU wf hΓ
                      hbodyPrefixT
                    obtain ⟨_, hlocalDomainEq⟩ :=
                      (hlocalForallEq.forallE_inv wf hΓ).1
                    have hrelProofTyEqCtx := hdomainEq.symm.toU.trans wf hΓ
                      hlocalDomainEq.toU |>.trans wf hΓ hproofArgEq
                    have hpTypeClosed :=
                      (hpT.closedN' wf.ordered.closed trivial).2.2
                    have hproofTyLFLift : proofTyLF.liftN 1 = proofTyLF :=
                      hproofTyLFClosed.liftN_eq (Nat.zero_le _)
                    have hrelProofTyEq : env.IsDefEqU 0 [] hpType proofTyLF := by
                      apply (VEnv.IsDefEqU.weakN_iff wf hΓ
                        (Ctx.LiftN.one : Ctx.LiftN 1 0 [] [proofTyLF])).1
                      rw [hproofTyLFLift]
                      simpa [hpTypeClosed.liftN_eq (Nat.zero_le _)] using
                        hrelProofTyEqCtx
                    have hpTL := hpT.defeqU_r wf trivial hrelProofTyEq
                    obtain ⟨hproofTyRFType, _, hbodyEqRightFinal⟩ :=
                      hprefixEqD.hasType.2.lam_inv wf trivial
                    obtain ⟨_, hproofTyRFSort⟩ := hproofTyRFType
                    have hbodyRightFinalT := hbodyEqRightFinal.hasType.1
                    have hleftLamT := VEnv.HasType.lam hproofTyLFSort
                      hbodyFinalT
                    have hprefixEqUS := hprefixEqU
                    simp [VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.liftN,
                      liftVar, hopClosed.liftN_eq, hopClosed.instN_eq,
                      hfClosed.liftN_eq, hfClosed.instN_eq,
                      hbClosed.liftN_eq, hbClosed.instN_eq,
                      hzClosed.instN_eq] at hprefixEqUS
                    have happ := hprefixEqUS.app_same wf trivial hleftLamT hpTL
                    have happRightT :=
                      (happ.of_l wf trivial (VEnv.HasType.app hleftLamT hpTL)).hasType.2
                    obtain ⟨_, _, hrightLamT, hpTR⟩ :=
                      happRightT.app_inv wf.ordered trivial
                    have hrightLamCanonT := VEnv.HasType.lam hproofTyRFSort
                      hbodyRightFinalT
                    have hrightForallEq := hrightLamT.uniqU wf trivial
                      hrightLamCanonT
                    obtain ⟨_, hrightDomainEq⟩ :=
                      (hrightForallEq.forallE_inv wf trivial).1
                    have hpTR' := hpTR.defeqU_r wf trivial
                      hrightDomainEq.toU
                    have hinstEq := VEnv.IsDefEqU.lam_instU_hetero wf trivial
                      hprefixEqUS hproofTyLFSort hbodyFinalT hbodyRightFinalT
                      hpTL hpTR'
                    have hproofVarLocal := hproofVarT.defeqU_r wf hΓ
                      hlocalDomainEq.symm.toU
                    have hprefixAppEqCtx := hlocalRelEq.app_same wf hΓ
                      hprefixLocalFinalT' hproofVarLocal
                    have hprefixAppEq := hprefixAppEqCtx.instN wf.ordered
                      (.zero : Ctx.InstN [] hpV proofTyLF 0 [proofTyLF] [])
                      hpTL
                    have hfuelVClosed : fuelV.ClosedN :=
                      (hfuelT.closedN' wf.ordered.closed trivial).1
                    have hleftEq := hprefixAppEq
                    simp [succFinal, VExpr.natLit, VLocalDecl.value,
                      VExpr.inst, VExpr.instVar,
                      hcallVClosed.instN_eq, hopClosed.instN_eq,
                      hfuelVClosed.instN_eq,
                      hfClosed.instN_eq, hbClosed.instN_eq,
                      hzClosed.instN_eq] at hleftEq
                    have hinstEqS := hinstEq
                    simp [VExpr.natLit, VExpr.inst, VExpr.instVar,
                      hcallVClosed.instN_eq, hopClosed.instN_eq,
                      hfuelVClosed.instN_eq, hfClosed.instN_eq,
                      hbClosed.instN_eq, hzClosed.instN_eq] at hinstEqS
                    have hcallToRight := heCall.trans wf trivial hleftEq.symm
                      |>.trans wf trivial hinstEqS
                    cases hbodyR with
                    | @app iteTwo _ _ zeroLocal _ _ _ _ _ hiteTwoS hzeroLocalS =>
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
                              cases hbLocalRS.unique (by trivial) hbCanonR
                              cases hzeroLocalS.unique (by trivial) hzeroCanonR
                              cases hfalseLocalS.unique (by trivial) hfalseCanon
                              cases htrueLocalS.unique (by trivial) htrueCanon
                              have hiteWeak := hiteS.weakBV wf.ordered
                                (.skip (.vlam proofTyR) <|
                                  .skip (.vlam natTyR₂) <|
                                    .skip (.vlam natTyR₁) <|
                                      .skip (.vlam funTyR) <|
                                        (.refl : VLCtx.BVLift [] [] 0 0 0 0))
                              have hiteSourceLift :
                                  Condition.bool.boolNatITE.liftLooseBVars' 0 4 =
                                    Condition.bool.boolNatITE :=
                                Expr.liftLooseBVars_eq_self
                                  hiteS.closed.looseBVarRange_le
                              have hiteWeak' : TrExprS env [] ΔR
                                  Condition.bool.boolNatITE (ite.liftN 4) := by
                                simpa [ΔR, VLocalDecl.depth, hiteSourceLift] using
                                  hiteWeak
                              have hiteEqCtx := TrExprS.uniq (Us := []) wf hctxR
                                hiteLocalS hiteWeak'
                              have hiteEqFinal₀ :=
                                VEnv.IsDefEqU.inst_bitwise_outer3 wf hopR hfR hbR
                                  (by simpa [ΔR] using hiteEqCtx)
                              have hiteClosed : ite.ClosedN :=
                                (hite.1.closedN' wf.ordered.closed trivial).1
                              have hiteEqFinal : env.IsDefEqU 0
                                  [((proofTyR.inst op 2).inst (.natLit fuel) 1).inst
                                    (.natLit b)]
                                  (((iteLocal.inst op 3).inst (.natLit fuel) 2).inst
                                    (.natLit b) 1) ite := by
                                simpa [hiteClosed.liftN_eq,
                                  hiteClosed.instN_eq] using hiteEqFinal₀
                              have hiteEqRoot₀ := hiteEqFinal.instN wf.ordered
                                (.zero : Ctx.InstN [] hpV
                                  ((proofTyR.inst op 2).inst (.natLit fuel) 1 |>.inst
                                    (.natLit b)) 0
                                  [((proofTyR.inst op 2).inst (.natLit fuel) 1 |>.inst
                                    (.natLit b))] []) hpTR'
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
                              have hrightStructT :=
                                (hcallToRightS.of_l wf trivial heT).hasType.2
                              obtain ⟨_, _, hrightTwoT, hzeroFinalT⟩ :=
                                hrightStructT.app_inv wf.ordered trivial
                              obtain ⟨_, _, hrightOneT, hbFinalT⟩ :=
                                hrightTwoT.app_inv wf.ordered trivial
                              obtain ⟨_, _, hiteFinalT, hcondFinalT⟩ :=
                                hrightOneT.app_inv wf.ordered trivial
                              have hcondEval := hop.2 false true
                              have hiteCondEq := hiteEqRoot.app_both wf trivial
                                hcondEval hiteFinalT hcondFinalT
                              have hiteThenEq := hiteCondEq.app_same wf trivial
                                hrightOneT hbFinalT
                              have hstructEval := hiteThenEq.app_same wf trivial
                                hrightTwoT hzeroFinalT
                              have hselect := hite.2 (f false true) b 0
                              have hrightEval := hstructEval.trans wf trivial hselect
                              exact hcallToRightS.trans wf trivial hrightEval

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
                      have hcallWeak := hcallS.weakBV wf.ordered
                        (.skip (.vlam proofTyL) <| .skip (.vlam natTyL₂) <|
                          .skip (.vlam natTyL₁) <| .skip (.vlam funTyL) <|
                            (.refl : VLCtx.BVLift [] [] 0 0 0 0))
                      have hcallSourceLift :
                          r.callFn.liftLooseBVars' 0 4 = r.callFn :=
                        Expr.liftLooseBVars_eq_self
                          hcallS.closed.looseBVarRange_le
                      have hcallWeak' : TrExprS env [] ΔL r.callFn
                          (callV.liftN 4) := by
                        simpa [ΔL, VLocalDecl.depth, hcallSourceLift] using hcallWeak
                      have hcallEqCtx := TrExprS.uniq (Us := []) wf hctxL
                        hcallLocalS hcallWeak'
                      have hsuccAEqCtx := TrExprS.uniq (Us := []) wf hctxL
                        hsuccLocalAS hsuccCanon
                      have hsuccFEqCtx := TrExprS.uniq (Us := []) wf hctxL
                        hsuccLocalFS hsuccCanon
                      have hcallEqFinal₀ := VEnv.IsDefEqU.inst_bitwise_outer3 wf
                        hopL hfL haL (by simpa [ΔL] using hcallEqCtx)
                      have hsuccAEqFinal₀ := VEnv.IsDefEqU.inst_bitwise_outer3 wf
                        hopL hfL haL (by simpa [ΔL] using hsuccAEqCtx)
                      have hsuccFEqFinal₀ := VEnv.IsDefEqU.inst_bitwise_outer3 wf
                        hopL hfL haL (by simpa [ΔL] using hsuccFEqCtx)
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
                        simpa [proofTyLF, callFinal, hcallVClosed.liftN_eq,
                          hcallVClosed.instN_eq] using hcallEqFinal₀
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
                                  have hiteWeak := hiteS.weakBV wf.ordered
                                    (.skip (.vlam proofTyR) <|
                                      .skip (.vlam natTyR₂) <|
                                        .skip (.vlam natTyR₁) <|
                                          .skip (.vlam funTyR) <|
                                            (.refl : VLCtx.BVLift [] [] 0 0 0 0))
                                  have hiteSourceLift :
                                      Condition.bool.boolNatITE.liftLooseBVars' 0 4 =
                                        Condition.bool.boolNatITE :=
                                    Expr.liftLooseBVars_eq_self
                                      hiteS.closed.looseBVarRange_le
                                  have hiteWeak' : TrExprS env [] ΔR
                                      Condition.bool.boolNatITE (ite.liftN 4) := by
                                    simpa [ΔR, VLocalDecl.depth, hiteSourceLift] using
                                      hiteWeak
                                  have hiteEqCtx := TrExprS.uniq (Us := []) wf
                                    hctxR hiteLocalS hiteWeak'
                                  have hsuccEqCtx := TrExprS.uniq (Us := []) wf
                                    hctxR hsuccLocalRS hsuccCanonR
                                  have hiteEqFinal₀ :=
                                    VEnv.IsDefEqU.inst_bitwise_outer3 wf hopR hfR haR
                                      (by simpa [ΔR] using hiteEqCtx)
                                  have hsuccEqFinal₀ :=
                                    VEnv.IsDefEqU.inst_bitwise_outer3 wf hopR hfR haR
                                      (by simpa [ΔR] using hsuccEqCtx)
                                  have hiteClosed : ite.ClosedN :=
                                    (hite.1.closedN' wf.ordered.closed trivial).1
                                  have hiteEqFinal : env.IsDefEqU 0
                                      [((proofTyR.inst op 2).inst (.natLit fuel) 1).inst
                                        (.natLit a)]
                                      (((iteLocal.inst op 3).inst (.natLit fuel) 2).inst
                                        (.natLit a) 1) ite := by
                                    simpa [hiteClosed.liftN_eq,
                                      hiteClosed.instN_eq] using hiteEqFinal₀
                                  have hsuccEqFinal : env.IsDefEqU 0
                                      [((proofTyR.inst op 2).inst (.natLit fuel) 1).inst
                                        (.natLit a)]
                                      (((succLocalR.inst op 3).inst (.natLit fuel) 2).inst
                                        (.natLit a) 1) .natSucc := by
                                    simpa [hsuccClosed.instN_eq] using hsuccEqFinal₀
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
                                  have hrightStructT :=
                                    (hcallToRightS.of_l wf trivial heT).hasType.2
                                  obtain ⟨_, _, hrightTwoT, hzeroFinalT⟩ :=
                                    hrightStructT.app_inv wf.ordered trivial
                                  obtain ⟨_, _, hrightOneT, hthenFinalT⟩ :=
                                    hrightTwoT.app_inv wf.ordered trivial
                                  obtain ⟨_, _, hiteFinalT, hcondFinalT⟩ :=
                                    hrightOneT.app_inv wf.ordered trivial
                                  have hsuccRFinalT :=
                                    (hsuccEqRoot.of_r wf trivial hsuccT).hasType.1
                                  have hsuccAppEq := hsuccEqRoot.app_same wf trivial
                                    hsuccRFinalT haT
                                  have hsuccEval : env.IsDefEqU 0 []
                                      (.app succRFinal (.natLit a))
                                      (.natLit (a + 1)) := by
                                    simpa [VExpr.natLit] using hsuccAppEq
                                  have hcondEval := hop.2 true false
                                  have hiteCondEq := hiteEqRoot.app_both wf trivial
                                    hcondEval hiteFinalT hcondFinalT
                                  have hiteThenEq := hiteCondEq.app_both wf trivial
                                    hsuccEval hrightOneT hthenFinalT
                                  have hstructEval := hiteThenEq.app_same wf trivial
                                    hrightTwoT hzeroFinalT
                                  have hselect := hite.2 (f true false) (a + 1) 0
                                  have hrightEval :=
                                    hstructEval.trans wf trivial hselect
                                  exact hcallToRightS.trans wf trivial hrightEval

end Lean4Lean.Environment
