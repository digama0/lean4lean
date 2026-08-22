import Lean4Lean.Verify.BitwiseSupport

namespace Lean4Lean.Environment
open Lean VEnv

/-- The normalized top equation places every semantic bitwise operation in
the retained certified call relation at fuel `a + 1`. -/
theorem NatBitwiseFixCertificate.top_semantics {env : VEnv}
    (wf : env.WF)
    (hctors : Lean4Lean.Environment.VEnv.HasNatBoolConstructors env)
    {r : NatBitwiseFixCertificate}
    {bitwise : Expr} {l rr g callV : VExpr}
    (hl : TrExprS env [] [] (r.expectedTopLhs bitwise) l)
    (hr : TrExprS env [] [] r.expectedTopRhs rr)
    (heq : env.IsDefEqU 0 [] l rr)
    (hbitwise : TrExprS env [] [] bitwise g)
    (hgT : env.HasType 0 [] g
      (.forallE (.forallE .bool <| .forallE .bool .bool) <|
        .forallE .nat <| .forallE .nat .nat))
    (hcallS : TrExprS env [] [] r.callFn callV)
    (hcallT : env.HasType 0 [] callV callTy)
    (heager : ∀ n, ∃ eager,
      TrExprS env [] [] q(WellFounded.Nat.eager) eager ∧
      env.IsDefEqU 0 [] (.app eager (.natLit n)) (.natLit n)) :
    ∀ op, env.HasType 0 [] op
      (.forallE .bool <| .forallE .bool .bool) →
      ∀ a b, ∃ e, VEnv.BitwiseGoCall env r op (a+1) a b e ∧
        env.IsDefEqU 0 []
          (.app (.app (.app g op) (.natLit a)) (.natLit b)) e := by
  unfold NatBitwiseFixCertificate.expectedTopLhs at hl
  unfold NatBitwiseFixCertificate.expectedTopRhs at hr
  cases hl with
  | lam hfunTyL hfunSL hl₁ =>
    cases hl₁ with
    | lam hnatTyL₁ hnatSL₁ hl₂ =>
      cases hl₂ with
      | lam hnatTyL₂ hnatSL₂ hl₃ =>
        cases hr with
        | lam hfunTyR hfunSR hr₁ =>
          cases hr₁ with
          | lam hnatTyR₁ hnatSR₁ hr₂ =>
            cases hr₂ with
            | lam hnatTyR₂ hnatSR₂ hr₃ =>
              rename_i funTyL natTyL₁ natTyL₂ bodyL
                funTyR natTyR₁ natTyR₂ bodyR
              intro op hop a b
              obtain ⟨_, hopSort⟩ := hop.isType wf trivial
              obtain ⟨hboolTy, hboolRestTy⟩ := hopSort.forallE_inv wf
              obtain ⟨hboolTy₁, hboolTy₂⟩ :=
                hboolRestTy.forallE_inv wf
              let ⟨uBool, hboolSort⟩ := hboolTy
              obtain ⟨boolCi, hboolCi, _, hboolLen⟩ :=
                hboolSort.const_inv wf trivial
              have hboolS (Δ : VLCtx) : TrExprS env [] Δ q(Bool) .bool :=
                .const hboolCi rfl (by simpa using hboolLen)
              have hboolBinS : TrExprS env [] []
                  q(Bool → Bool → Bool)
                  (.forallE .bool <| .forallE .bool .bool) :=
                .forallE hboolTy hboolRestTy (hboolS []) <|
                  .forallE hboolTy₁ hboolTy₂
                    (hboolS [(none, .vlam .bool)])
                    (hboolS [(none, .vlam .bool), (none, .vlam .bool)])
              have hfunEqL := hfunSL.uniq wf
                (.refl wf (U := 0) (Δ := []) (by trivial)) hboolBinS
              have hfunEqR := hfunSR.uniq wf
                (.refl wf (U := 0) (Δ := []) (by trivial)) hboolBinS
              have hopL := hop.defeqU_r wf trivial hfunEqL.symm
              have hopR := hop.defeqU_r wf trivial hfunEqR.symm
              have hlBody : TrExprS env [] [(none, .vlam funTyL)]
                  (.lam0 q(Nat) <| .lam0 q(Nat) <|
                    mkApp3 bitwise (.bvar 2) (.bvar 1) (.bvar 0))
                  (.lam natTyL₁ <| .lam natTyL₂ bodyL) :=
                .lam hnatTyL₁ hnatSL₁ (.lam hnatTyL₂ hnatSL₂ hl₃)
              have hrBody : TrExprS env [] [(none, .vlam funTyR)]
                  (.lam0 q(Nat) <| .lam0 q(Nat) <|
                    mkAppN r.callFn #[.bvar 2,
                      mkApp q(WellFounded.Nat.eager)
                        (mkApp q(Nat.succ) (.bvar 1)),
                      .bvar 1, .bvar 0, r.topProof])
                  (.lam natTyR₁ <| .lam natTyR₂ bodyR) :=
                .lam hnatTyR₁ hnatSR₁ (.lam hnatTyR₂ hnatSR₂ hr₃)
              obtain ⟨BL, hbodyLT⟩ := hlBody.wf wf.ordered
                (Us := []) (Δ := [(none, .vlam funTyL)])
                ⟨trivial, nofun, hfunTyL⟩
              obtain ⟨BR, hbodyRT⟩ := hrBody.wf wf.ordered
                (Us := []) (Δ := [(none, .vlam funTyR)])
                ⟨trivial, nofun, hfunTyR⟩
              let ⟨uFun, hfunSortL⟩ := hfunTyL
              have hfunEqLR := hfunEqL.trans wf trivial hfunEqR.symm
              have houter := VEnv.IsDefEqU.lam_instU₂ wf trivial heq
                hfunSortL hbodyLT hbodyRT hfunEqLR hopL
              simp only [VExpr.inst] at houter
              have hzT :=
                (hctors.natZeroS (Us := []) (Δ := [])).2
              obtain ⟨uNat, hnatSort⟩ := hzT.isType wf trivial
              obtain ⟨natCi, hnatCi, _, hnatLen⟩ :=
                hnatSort.const_inv wf trivial
              have hnatS (Δ : VLCtx) : TrExprS env [] Δ q(Nat) .nat :=
                .const hnatCi rfl (by simpa using hnatLen)
              have hctxL : VLCtx.IsDefEq env 0
                  [(none, .vlam funTyL)] [(none, .vlam funTyL)] :=
                .refl wf ⟨trivial, nofun, hfunTyL⟩
              have hctxR : VLCtx.IsDefEq env 0
                  [(none, .vlam funTyR)] [(none, .vlam funTyR)] :=
                .refl wf ⟨trivial, nofun, hfunTyR⟩
              have hnatEqLCtx := TrExprS.uniq (Us := []) wf hctxL hnatSL₁
                (hnatS [(none, .vlam funTyL)])
              have hnatEqRCtx := TrExprS.uniq (Us := []) wf hctxR hnatSR₁
                (hnatS [(none, .vlam funTyR)])
              have hnatEqL := hnatEqLCtx.instN wf.ordered
                (.zero : Ctx.InstN [] op funTyL 0 [funTyL] []) hopL
              have hnatEqR := hnatEqRCtx.instN wf.ordered
                (.zero : Ctx.InstN [] op funTyR 0 [funTyR] []) hopR
              have hnatEqL' : env.IsDefEqU 0 [] (natTyL₁.inst op) .nat := by
                simpa [VExpr.nat, VExpr.inst] using hnatEqL
              have hnatEqR' : env.IsDefEqU 0 [] (natTyR₁.inst op) .nat := by
                simpa [VExpr.nat, VExpr.inst] using hnatEqR
              have houterU := houter
              obtain ⟨_, houterD⟩ := houter
              have hleftOuterT := houterD.hasType.1
              have hrightOuterT := houterD.hasType.2
              obtain ⟨⟨_, hnatOuterSortL⟩, _, hinnerLT⟩ :=
                hleftOuterT.lam_inv wf trivial
              obtain ⟨_, _, hinnerRT⟩ :=
                hrightOuterT.lam_inv wf trivial
              have haT :=
                (hctors.natLitS a (Us := []) (Δ := [])).2
              have haL := haT.defeqU_r wf trivial hnatEqL'.symm
              have hnatEqLR := hnatEqL'.trans wf trivial hnatEqR'.symm
              have hmiddle := VEnv.IsDefEqU.lam_instU₂ wf trivial houterU
                hnatOuterSortL hinnerLT hinnerRT hnatEqLR haL
              simp only [VExpr.inst] at hmiddle
              have hctxL₂ : VLCtx.IsDefEq env 0
                  [(none, .vlam natTyL₁), (none, .vlam funTyL)]
                  [(none, .vlam natTyL₁), (none, .vlam funTyL)] :=
                .refl wf ⟨⟨trivial, nofun, hfunTyL⟩, nofun, hnatTyL₁⟩
              have hctxR₂ : VLCtx.IsDefEq env 0
                  [(none, .vlam natTyR₁), (none, .vlam funTyR)]
                  [(none, .vlam natTyR₁), (none, .vlam funTyR)] :=
                .refl wf ⟨⟨trivial, nofun, hfunTyR⟩, nofun, hnatTyR₁⟩
              have hnatEqL₂Ctx := TrExprS.uniq (Us := []) wf hctxL₂
                hnatSL₂ (hnatS [(none, .vlam natTyL₁),
                  (none, .vlam funTyL)])
              have hnatEqR₂Ctx := TrExprS.uniq (Us := []) wf hctxR₂
                hnatSR₂ (hnatS [(none, .vlam natTyR₁),
                  (none, .vlam funTyR)])
              have hnatEqL₂Op := hnatEqL₂Ctx.instN wf.ordered
                (.succ (.zero : Ctx.InstN [] op funTyL 0 [funTyL] [])) hopL
              have hnatEqR₂Op := hnatEqR₂Ctx.instN wf.ordered
                (.succ (.zero : Ctx.InstN [] op funTyR 0 [funTyR] [])) hopR
              have hnatEqL₂ := hnatEqL₂Op.instN wf.ordered
                (.zero : Ctx.InstN [] (.natLit a) (natTyL₁.inst op) 0
                  [natTyL₁.inst op] []) haL
              have haR := haT.defeqU_r wf trivial hnatEqR'.symm
              have hnatEqR₂ := hnatEqR₂Op.instN wf.ordered
                (.zero : Ctx.InstN [] (.natLit a) (natTyR₁.inst op) 0
                  [natTyR₁.inst op] []) haR
              have hnatEqL₂' : env.IsDefEqU 0 []
                  ((natTyL₂.inst op 1).inst (.natLit a)) .nat := by
                simpa [VExpr.nat, VExpr.inst] using hnatEqL₂
              have hnatEqR₂' : env.IsDefEqU 0 []
                  ((natTyR₂.inst op 1).inst (.natLit a)) .nat := by
                simpa [VExpr.nat, VExpr.inst] using hnatEqR₂
              have hmiddleU := hmiddle
              obtain ⟨_, hmiddleD⟩ := hmiddle
              have hleftMiddleT := hmiddleD.hasType.1
              have hrightMiddleT := hmiddleD.hasType.2
              obtain ⟨⟨_, hnatMiddleSortL⟩, _, hfinalLT⟩ :=
                hleftMiddleT.lam_inv wf trivial
              obtain ⟨_, _, hfinalRT⟩ :=
                hrightMiddleT.lam_inv wf trivial
              have hbT :=
                (hctors.natLitS b (Us := []) (Δ := [])).2
              have hbL := hbT.defeqU_r wf trivial hnatEqL₂'.symm
              have hnatEq₂LR :=
                hnatEqL₂'.trans wf trivial hnatEqR₂'.symm
              have hfinal := VEnv.IsDefEqU.lam_instU₂ wf trivial hmiddleU
                hnatMiddleSortL hfinalLT hfinalRT hnatEq₂LR hbL
              cases hl₃ with
              | @app l₂V _ _ bV _ _ _ _ _ hl₂' hbS' =>
                cases hl₂' with
                | @app l₁V _ _ aV _ _ _ _ _ hl₁' haS' =>
                  cases hl₁' with
                  | @app gV _ _ opV _ _ _ _ _ hgS' hopS' =>
                    cases hr₃ with
                    | @app r₄V _ _ hpV _ _ _ _ _ hr₄' hpS' =>
                      cases hr₄' with
                      | @app r₃V _ _ bRV _ _ _ _ _ hr₃' hbRS' =>
                        cases hr₃' with
                        | @app r₂V _ _ aRV _ _ _ _ _ hr₂' haRS' =>
                          cases hr₂' with
                          | @app r₁V _ _ fuelV _ _ _ _ _ hr₁' hfuelS' =>
                            cases hr₁' with
                            | @app callLocalV _ _ opRV _ _ _ _ _ hcallS' hopRS' =>
                              have hopCanonL : TrExprS env []
                                  [(none, .vlam natTyL₂),
                                    (none, .vlam natTyL₁),
                                    (none, .vlam funTyL)]
                                  (.bvar 2) (.bvar 2) := .bvar (by rfl)
                              have haCanonL : TrExprS env []
                                  [(none, .vlam natTyL₂),
                                    (none, .vlam natTyL₁),
                                    (none, .vlam funTyL)]
                                  (.bvar 1) (.bvar 1) := .bvar (by rfl)
                              have hbCanonL : TrExprS env []
                                  [(none, .vlam natTyL₂),
                                    (none, .vlam natTyL₁),
                                    (none, .vlam funTyL)]
                                  (.bvar 0) (.bvar 0) := .bvar (by rfl)
                              cases hopS'.unique (by trivial) hopCanonL
                              cases haS'.unique (by trivial) haCanonL
                              cases hbS'.unique (by trivial) hbCanonL
                              have hopCanonR : TrExprS env []
                                  [(none, .vlam natTyR₂),
                                    (none, .vlam natTyR₁),
                                    (none, .vlam funTyR)]
                                  (.bvar 2) (.bvar 2) := .bvar (by rfl)
                              have haCanonR : TrExprS env []
                                  [(none, .vlam natTyR₂),
                                    (none, .vlam natTyR₁),
                                    (none, .vlam funTyR)]
                                  (.bvar 1) (.bvar 1) := .bvar (by rfl)
                              have hbCanonR : TrExprS env []
                                  [(none, .vlam natTyR₂),
                                    (none, .vlam natTyR₁),
                                    (none, .vlam funTyR)]
                                  (.bvar 0) (.bvar 0) := .bvar (by rfl)
                              cases hopRS'.unique (by trivial) hopCanonR
                              cases haRS'.unique (by trivial) haCanonR
                              cases hbRS'.unique (by trivial) hbCanonR
                              have hgWeak := hbitwise.weakBV wf.ordered
                                (.skip (.vlam natTyL₂) <|
                                  .skip (.vlam natTyL₁) <|
                                    .skip (.vlam funTyL) <|
                                      (.refl : VLCtx.BVLift [] [] 0 0 0 0))
                              have hcallWeak := hcallS.weakBV wf.ordered
                                (.skip (.vlam natTyR₂) <|
                                  .skip (.vlam natTyR₁) <|
                                    .skip (.vlam funTyR) <|
                                      (.refl : VLCtx.BVLift [] [] 0 0 0 0))
                              have hgSourceLift :
                                  bitwise.liftLooseBVars' 0 3 = bitwise :=
                                Expr.liftLooseBVars_eq_self
                                  hbitwise.closed.looseBVarRange_le
                              have hcallSourceLift :
                                  r.callFn.liftLooseBVars' 0 3 = r.callFn :=
                                Expr.liftLooseBVars_eq_self
                                  hcallS.closed.looseBVarRange_le
                              have hgWeak' : TrExprS env []
                                  [(none, .vlam natTyL₂),
                                    (none, .vlam natTyL₁),
                                    (none, .vlam funTyL)] bitwise
                                  (g.liftN 3) := by
                                simpa [VLocalDecl.depth, hgSourceLift] using hgWeak
                              have hcallWeak' : TrExprS env []
                                  [(none, .vlam natTyR₂),
                                    (none, .vlam natTyR₁),
                                    (none, .vlam funTyR)] r.callFn
                                  (callV.liftN 3) := by
                                simpa [VLocalDecl.depth, hcallSourceLift] using
                                  hcallWeak
                              have hctxL₃ : VLCtx.IsDefEq env 0
                                  [(none, .vlam natTyL₂),
                                    (none, .vlam natTyL₁),
                                    (none, .vlam funTyL)]
                                  [(none, .vlam natTyL₂),
                                    (none, .vlam natTyL₁),
                                    (none, .vlam funTyL)] :=
                                .refl wf ⟨⟨⟨trivial, nofun, hfunTyL⟩,
                                  nofun, hnatTyL₁⟩, nofun, hnatTyL₂⟩
                              have hctxR₃ : VLCtx.IsDefEq env 0
                                  [(none, .vlam natTyR₂),
                                    (none, .vlam natTyR₁),
                                    (none, .vlam funTyR)]
                                  [(none, .vlam natTyR₂),
                                    (none, .vlam natTyR₁),
                                    (none, .vlam funTyR)] :=
                                .refl wf ⟨⟨⟨trivial, nofun, hfunTyR⟩,
                                  nofun, hnatTyR₁⟩, nofun, hnatTyR₂⟩
                              have hgEqCtx := TrExprS.uniq (Us := []) wf hctxL₃
                                hgS' hgWeak'
                              have hcallEqCtx :=
                                TrExprS.uniq (Us := []) wf hctxR₃
                                  hcallS' hcallWeak'
                              have hgEqOp := hgEqCtx.instN wf.ordered
                                (.succ (.succ (.zero : Ctx.InstN [] op funTyL 0
                                  [funTyL] []))) hopL
                              have hcallEqOp := hcallEqCtx.instN wf.ordered
                                (.succ (.succ (.zero : Ctx.InstN [] op funTyR 0
                                  [funTyR] []))) hopR
                              have hgEqA := hgEqOp.instN wf.ordered
                                (.succ (.zero : Ctx.InstN [] (.natLit a)
                                  (natTyL₁.inst op) 0 [natTyL₁.inst op] [])) haL
                              have hcallEqA := hcallEqOp.instN wf.ordered
                                (.succ (.zero : Ctx.InstN [] (.natLit a)
                                  (natTyR₁.inst op) 0 [natTyR₁.inst op] [])) haR
                              have hgEqFinal := hgEqA.instN wf.ordered
                                (.zero : Ctx.InstN [] (.natLit b)
                                  ((natTyL₂.inst op 1).inst (.natLit a)) 0
                                  [((natTyL₂.inst op 1).inst (.natLit a))] []) hbL
                              have hbR := hbT.defeqU_r wf trivial
                                hnatEqR₂'.symm
                              have hcallEqFinal := hcallEqA.instN wf.ordered
                                (.zero : Ctx.InstN [] (.natLit b)
                                  ((natTyR₂.inst op 1).inst (.natLit a)) 0
                                  [((natTyR₂.inst op 1).inst (.natLit a))] []) hbR
                              have hgEqFinal' : env.IsDefEqU 0 []
                                  (((gV.inst op 2).inst (.natLit a) 1).inst
                                    (.natLit b)) g := by
                                have hgClosed : g.ClosedN :=
                                  (hgT.closedN' wf.ordered.closed trivial).1
                                simpa [hgClosed.liftN_eq,
                                  hgClosed.instN_eq] using hgEqFinal
                              have hcallEqFinal' : env.IsDefEqU 0 []
                                  (((callLocalV.inst op 2).inst (.natLit a) 1).inst
                                    (.natLit b)) callV := by
                                have hcallClosed : callV.ClosedN :=
                                  (hcallT.closedN' wf.ordered.closed trivial).1
                                simpa [hcallClosed.liftN_eq,
                                  hcallClosed.instN_eq] using hcallEqFinal
                              have hfinal' := hfinal
                              simp [VExpr.inst, VExpr.instVar] at hfinal'
                              cases hfuelS' with
                              | @app eagerLocal _ _ succAppV _ _ _ _ _
                                  heagerLocalS hsuccAppS =>
                                cases hsuccAppS with
                                | @app succLocal _ _ aFuelV _ _ _ _ _
                                    hsuccLocalS haFuelS =>
                                  cases haFuelS.unique (by trivial) haCanonR
                                  obtain ⟨eager, heagerS, heagerEval⟩ :=
                                    heager (a + 1)
                                  have heagerWeak := heagerS.weakBV wf.ordered
                                    (.skip (.vlam natTyR₂) <|
                                      .skip (.vlam natTyR₁) <|
                                        .skip (.vlam funTyR) <|
                                          (.refl : VLCtx.BVLift [] [] 0 0 0 0))
                                  have heagerSourceLift :
                                      q(WellFounded.Nat.eager).liftLooseBVars'
                                        0 3 = q(WellFounded.Nat.eager) :=
                                    Expr.liftLooseBVars_eq_self
                                      heagerS.closed.looseBVarRange_le
                                  have heagerWeak' : TrExprS env []
                                      [(none, .vlam natTyR₂),
                                        (none, .vlam natTyR₁),
                                        (none, .vlam funTyR)]
                                      q(WellFounded.Nat.eager)
                                      (eager.liftN 3) := by
                                    simpa [VLocalDecl.depth, heagerSourceLift] using
                                      heagerWeak
                                  have hsuccCanon :=
                                    (hctors.natSuccS (Us := [])
                                      (Δ := [(none, .vlam natTyR₂),
                                        (none, .vlam natTyR₁),
                                        (none, .vlam funTyR)])).1
                                  have heagerEqCtx := TrExprS.uniq (Us := []) wf
                                    hctxR₃ heagerLocalS heagerWeak'
                                  have hsuccEqCtx := TrExprS.uniq (Us := []) wf
                                    hctxR₃ hsuccLocalS hsuccCanon
                                  have instClosedR {x y : VExpr}
                                      (hxy : env.IsDefEqU 0
                                        [natTyR₂, natTyR₁, funTyR] x y) :
                                      env.IsDefEqU 0 []
                                        (((x.inst op 2).inst (.natLit a) 1).inst
                                          (.natLit b))
                                        (((y.inst op 2).inst (.natLit a) 1).inst
                                          (.natLit b)) := by
                                    have h₁ := hxy.instN wf.ordered
                                      (.succ (.succ (.zero : Ctx.InstN [] op
                                        funTyR 0 [funTyR] []))) hopR
                                    have h₂ := h₁.instN wf.ordered
                                      (.succ (.zero : Ctx.InstN [] (.natLit a)
                                        (natTyR₁.inst op) 0
                                        [natTyR₁.inst op] [])) haR
                                    exact h₂.instN wf.ordered
                                      (.zero : Ctx.InstN [] (.natLit b)
                                        ((natTyR₂.inst op 1).inst (.natLit a)) 0
                                        [((natTyR₂.inst op 1).inst (.natLit a))]
                                        []) hbR
                                  have heagerEqFinal₀ := instClosedR heagerEqCtx
                                  have hsuccEqFinal := instClosedR hsuccEqCtx
                                  have heagerEvalU := heagerEval
                                  obtain ⟨_, heagerD⟩ := heagerEval
                                  obtain ⟨_, _, heagerT, heagerArgT⟩ :=
                                    heagerD.hasType.1.app_inv wf.ordered trivial
                                  have eagerClosed : eager.ClosedN :=
                                    (heagerT.closedN' wf.ordered.closed trivial).1
                                  have hsuccT :=
                                    (hctors.natSuccS (Us := [])
                                      (Δ := [])).2
                                  have hsuccClosed : VExpr.natSucc.ClosedN :=
                                    (hsuccT.closedN' wf.ordered.closed trivial).1
                                  have heagerEqFinal : env.IsDefEqU 0 []
                                      (((eagerLocal.inst op 2).inst (.natLit a) 1).inst
                                        (.natLit b)) eager := by
                                    simpa [eagerClosed.liftN_eq,
                                      eagerClosed.instN_eq] using heagerEqFinal₀
                                  have hsuccEqFinal' : env.IsDefEqU 0 []
                                      (((succLocal.inst op 2).inst (.natLit a) 1).inst
                                        (.natLit b)) .natSucc := by
                                    simpa [hsuccClosed.instN_eq] using hsuccEqFinal
                                  have hopClosed : op.ClosedN :=
                                    (hop.closedN' wf.ordered.closed trivial).1
                                  have haClosed : (VExpr.natLit a).ClosedN :=
                                    (haT.closedN' wf.ordered.closed trivial).1
                                  have hfinal'' := hfinal'
                                  simp [hopClosed.liftN_eq, haClosed.liftN_eq,
                                    hopClosed.instN_eq, haClosed.instN_eq] at hfinal''
                                  let eagerFinal :=
                                    ((eagerLocal.inst op 2).inst (.natLit a) 1).inst
                                      (.natLit b)
                                  let succFinal :=
                                    ((succLocal.inst op 2).inst (.natLit a) 1).inst
                                      (.natLit b)
                                  let fuelFinal := eagerFinal.app
                                    (succFinal.app (.natLit a))
                                  let hpFinal :=
                                    ((hpV.inst op 2).inst (.natLit a) 1).inst
                                      (.natLit b)
                                  let gFinal :=
                                    ((gV.inst op 2).inst (.natLit a) 1).inst
                                      (.natLit b)
                                  let callFinal :=
                                    ((callLocalV.inst op 2).inst (.natLit a) 1).inst
                                      (.natLit b)
                                  have hfinalClean : env.IsDefEqU 0 []
                                      (.app (.app (.app gFinal op) (.natLit a))
                                        (.natLit b))
                                      (.app (.app (.app (.app (.app callFinal op)
                                        fuelFinal) (.natLit a)) (.natLit b))
                                        hpFinal) := by
                                    simpa [gFinal, callFinal, fuelFinal,
                                      eagerFinal, succFinal, hpFinal,
                                      hopClosed.instN_eq, haClosed.instN_eq,
                                      haClosed.liftN_eq,
                                      VExpr.inst, VExpr.instVar, VExpr.lift,
                                      VExpr.liftN] using hfinal''
                                  have hsuccLocalT :=
                                    (hsuccEqFinal'.of_r wf trivial hsuccT).hasType.1
                                  have hsuccAppEq := hsuccEqFinal'.app_same wf trivial
                                    hsuccLocalT haT
                                  have hsuccEval : env.IsDefEqU 0 []
                                      (succFinal.app (.natLit a)) (.natLit (a + 1)) := by
                                    simpa [succFinal, VExpr.natLit] using hsuccAppEq
                                  have heagerLocalT :=
                                    (heagerEqFinal.of_r wf trivial heagerT).hasType.1
                                  have hnatSuccResultT :=
                                    VEnv.HasType.app hsuccLocalT haT
                                  have hnatA1T :=
                                    (hctors.natLitS (a + 1)
                                      (Us := []) (Δ := [])).2
                                  have heagerDomainEq :=
                                    heagerArgT.uniqU wf trivial hnatA1T
                                  have hnatSuccResultT' := hnatSuccResultT.defeqU_r
                                    wf trivial heagerDomainEq.symm
                                  have heagerFuelEq := heagerEqFinal.app_both wf trivial
                                    hsuccEval heagerLocalT
                                    hnatSuccResultT'
                                  have hfuelEval : env.IsDefEqU 0 [] fuelFinal
                                      (.natLit (a + 1)) :=
                                    heagerFuelEq.trans wf trivial heagerEvalU
                                  have hgFinalEq : env.IsDefEqU 0 [] gFinal g := by
                                    simpa [gFinal] using hgEqFinal'
                                  have hgFinalT :=
                                    (hgFinalEq.of_r wf trivial hgT).hasType.1
                                  have hgApp₁ := hgFinalEq.app_same wf trivial
                                    hgFinalT hop
                                  have hgApp₂ := hgApp₁.app_same wf trivial
                                    (.app hgFinalT hop) haT
                                  have hgApp₃ := hgApp₂.app_same wf trivial
                                    (.app (.app hgFinalT hop) haT) hbT
                                  have hcallFinalEq : env.IsDefEqU 0 []
                                      callFinal callV := by
                                    simpa [callFinal] using hcallEqFinal'
                                  have hfinalCleanU := hfinalClean
                                  obtain ⟨_, hcleanD⟩ := hfinalClean
                                  have hrightT := hcleanD.hasType.2
                                  obtain ⟨_, _, hprefix₄T, hpFinalT⟩ :=
                                    hrightT.app_inv wf.ordered trivial
                                  obtain ⟨_, _, hprefix₃T, hbFinalT⟩ :=
                                    hprefix₄T.app_inv wf.ordered trivial
                                  obtain ⟨_, _, hprefix₂T, haFinalT⟩ :=
                                    hprefix₃T.app_inv wf.ordered trivial
                                  obtain ⟨_, _, hprefix₁T, hfuelFinalT⟩ :=
                                    hprefix₂T.app_inv wf.ordered trivial
                                  obtain ⟨_, _, hcallFinalT, hopFinalT⟩ :=
                                    hprefix₁T.app_inv wf.ordered trivial
                                  have hcallApp₁ := hcallFinalEq.app_same wf trivial
                                    hcallFinalT hopFinalT
                                  have hcallApp₂ := hcallApp₁.app_same wf trivial
                                    hprefix₁T hfuelFinalT
                                  have hcallApp₃ := hcallApp₂.app_same wf trivial
                                    hprefix₂T haFinalT
                                  have hcallApp₄ := hcallApp₃.app_same wf trivial
                                    hprefix₃T hbFinalT
                                  have hcallApp₅ := hcallApp₄.app_same wf trivial
                                    hprefix₄T hpFinalT
                                  let e := VExpr.app (VExpr.app (VExpr.app
                                    (VExpr.app (VExpr.app callFinal op) fuelFinal)
                                    (.natLit a)) (.natLit b)) hpFinal
                                  refine ⟨e, ?_, ?_⟩
                                  · exact ⟨callV, fuelFinal, hpFinal, hcallS,
                                      hfuelEval, hcallApp₅⟩
                                  · exact hgApp₃.symm.trans wf trivial hfinalCleanU

end Lean4Lean.Environment
