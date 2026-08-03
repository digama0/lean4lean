import Lean4Lean.Verify.BitwiseSupport

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

/-- Four beta steps connect a translated `Reflection.ite` application to a
translation of its instantiated root-`ite` body. -/
theorem Reflection.defn₂.ite_apply4
    {env : VEnv} (wf : env.WF)
    {pS bS HS αS : Expr} {pV bV HV αV iteV prefixV : VExpr}
    {pTyV bTyV HTyV αTyV : VExpr}
    (hite : TrExprS env [] [] Reflection.defn₂.ite iteV)
    (hpTyS : TrExprS env [] [] q(Prop) pTyV)
    (hbTyS : TrExprS env [] [] q(Bool) bTyV)
    (hHTyS : TrExprS env [] []
      (mkApp2 Reflection.defn₂.type pS bS) HTyV)
    (hαTyS : TrExprS env [] [] q(Type) αTyV)
    (hpS : TrExprS env [] [] pS pV)
    (hbS : TrExprS env [] [] bS bV)
    (hHS : TrExprS env [] [] HS HV)
    (hαS : TrExprS env [] [] αS αV)
    (hpT : env.HasType 0 [] pV pTyV)
    (hbT : env.HasType 0 [] bV bTyV)
    (hHT : env.HasType 0 [] HV HTyV)
    (hαT : env.HasType 0 [] αV αTyV)
    (hprefix : TrExprS env [] []
      (mkApp3 q(@_root_.ite.{1}) αS pS
        (mkApp3 Reflection.defn₂.toDec pS bS HS)) prefixV) :
    env.IsDefEqU 0 []
      (.app (.app (.app (.app iteV pV) bV) HV) αV) prefixV := by
  unfold Reflection.ite at hite
  cases hite with
  | lam hpTy hpTyLocalS hrest =>
    rename_i pTyLocal restV
    have hctx : VLCtx.IsDefEq env 0 [] [] := .refl wf trivial
    have hpTyEq := TrExprS.uniq (Us := []) wf hctx hpTyLocalS hpTyS
    have hpT' := hpT.defeqU_r wf trivial hpTyEq.symm
    have hpClosed := hpS.closed.looseBVarRange_zero
    have hpLift (s d : Nat) : pS.liftLooseBVars' s d = pS :=
      Expr.liftLooseBVars_eq_self (by rw [hpClosed]; omega)
    have hpInst (a : Expr) (k : Nat) : pS.instantiate1' a k = pS :=
      Expr.instantiate1'_eq_self (by rw [hpClosed]; omega)
    have hrtypeClosed : Reflection.defn₂.type.looseBVarRange' = 0 := by
      native_decide
    have htoDecClosed : Reflection.defn₂.toDec.looseBVarRange' = 0 := by
      native_decide
    have hrtypeInst (a : Expr) (k : Nat) :
        Reflection.defn₂.type.instantiate1' a k = Reflection.defn₂.type :=
      Expr.instantiate1'_eq_self (by rw [hrtypeClosed]; omega)
    have htoDecInst (a : Expr) (k : Nat) :
        Reflection.defn₂.toDec.instantiate1' a k = Reflection.defn₂.toDec :=
      Expr.instantiate1'_eq_self (by rw [htoDecClosed]; omega)
    obtain ⟨bTyOrig, rest₂Orig, rfl, hbTyOrig, hbTyOrigS, hrest₂Orig⟩ :
        ∃ bTyOrig rest₂Orig,
          restV = .lam bTyOrig rest₂Orig ∧
          env.IsType 0 [pTyLocal] bTyOrig ∧
          TrExprS env [] [(none, .vlam pTyLocal)] q(Bool) bTyOrig ∧
          TrExprS env []
            [(none, .vlam bTyOrig), (none, .vlam pTyLocal)]
            (.lam0 (mkApp2 Reflection.defn₂.type (.bvar 1) (.bvar 0)) <|
              .lam0 q(Type) <| mkApp3 q(@_root_.ite.{1}) (.bvar 0) (.bvar 3)
                (mkApp3 Reflection.defn₂.toDec
                  (.bvar 3) (.bvar 2) (.bvar 1))) rest₂Orig := by
      cases hrest with
      | lam hbTyOrig hbTyOrigS hrest₂Orig =>
        exact ⟨_, _, rfl, hbTyOrig, hbTyOrigS, hrest₂Orig⟩
    obtain ⟨HTyPre, rest₃Pre, rfl, hHTyPre, hHTyPreS, hrest₃Pre⟩ :
        ∃ HTyPre rest₃Pre,
          rest₂Orig = .lam HTyPre rest₃Pre ∧
          env.IsType 0 [bTyOrig, pTyLocal] HTyPre ∧
          TrExprS env []
            [(none, .vlam bTyOrig), (none, .vlam pTyLocal)]
            (mkApp2 Reflection.defn₂.type (.bvar 1) (.bvar 0)) HTyPre ∧
          TrExprS env []
            [(none, .vlam HTyPre), (none, .vlam bTyOrig),
              (none, .vlam pTyLocal)]
            (.lam0 q(Type) <| mkApp3 q(@_root_.ite.{1}) (.bvar 0) (.bvar 3)
              (mkApp3 Reflection.defn₂.toDec
                (.bvar 3) (.bvar 2) (.bvar 1))) rest₃Pre := by
      cases hrest₂Orig with
      | lam hHTyPre hHTyPreS hrest₃Pre =>
        exact ⟨_, _, rfl, hHTyPre, hHTyPreS, hrest₃Pre⟩
    obtain ⟨αTyPre, bodyPre, rfl, hαTyPre, hαTyPreS, hbodyPre⟩ :
        ∃ αTyPre bodyPre,
          rest₃Pre = .lam αTyPre bodyPre ∧
          env.IsType 0 [HTyPre, bTyOrig, pTyLocal] αTyPre ∧
          TrExprS env []
            [(none, .vlam HTyPre), (none, .vlam bTyOrig),
              (none, .vlam pTyLocal)] q(Type) αTyPre ∧
          TrExprS env []
            [(none, .vlam αTyPre), (none, .vlam HTyPre),
              (none, .vlam bTyOrig), (none, .vlam pTyLocal)]
            (mkApp3 q(@_root_.ite.{1}) (.bvar 0) (.bvar 3)
              (mkApp3 Reflection.defn₂.toDec
                (.bvar 3) (.bvar 2) (.bvar 1))) bodyPre := by
      cases hrest₃Pre with
      | lam hαTyPre hαTyPreS hbodyPre =>
        exact ⟨_, _, rfl, hαTyPre, hαTyPreS, hbodyPre⟩
    have houter : TrExprS env [] [] Reflection.defn₂.ite
        (.lam pTyLocal <| .lam bTyOrig <| .lam HTyPre <|
          .lam αTyPre bodyPre) := by
      unfold Reflection.ite
      exact .lam hpTy hpTyLocalS <| .lam hbTyOrig hbTyOrigS <|
        .lam hHTyPre hHTyPreS <| .lam hαTyPre hαTyPreS hbodyPre
    obtain ⟨h₁S, hβ₁⟩ := TrExprS.applyClosedLam wf houter hpS hpT'
    have hsrc₁ :
        ((Expr.lam0 q(Bool) <|
          .lam0 (mkApp2 Reflection.defn₂.type (.bvar 1) (.bvar 0)) <|
            .lam0 q(Type) <| mkApp3 q(@_root_.ite.{1}) (.bvar 0) (.bvar 3)
              (mkApp3 Reflection.defn₂.toDec (.bvar 3) (.bvar 2) (.bvar 1))).instantiate1' pS) =
        (Expr.lam0 q(Bool) <|
          .lam0 (mkApp2 Reflection.defn₂.type pS (.bvar 0)) <|
            .lam0 q(Type) <| mkApp3 q(@_root_.ite.{1}) (.bvar 0) pS
              (mkApp3 Reflection.defn₂.toDec pS (.bvar 2) (.bvar 1))) := by
      simp [Lean.Expr.instantiate1', Expr.lam0, mkApp3, mkApp2, mkApp,
        mkAppB, hpLift, hrtypeInst, htoDecInst]
    have h₁S' : TrExprS env [] []
        (.lam0 q(Bool) <|
          .lam0 (mkApp2 Reflection.defn₂.type pS (.bvar 0)) <|
            .lam0 q(Type) <| mkApp3 q(@_root_.ite.{1}) (.bvar 0) pS
              (mkApp3 Reflection.defn₂.toDec pS (.bvar 2) (.bvar 1)))
        (.lam (bTyOrig.inst pV) <|
          .lam (HTyPre.inst pV 1) <|
            .lam (αTyPre.inst pV 2) (bodyPre.inst pV 3)) := by
      rw [← hsrc₁]
      simpa [VExpr.inst] using h₁S
    cases h₁S' with
    | lam hbTy hbTyLocalS hrest₂ =>
      have hbTyEq := TrExprS.uniq (Us := []) wf hctx
        hbTyLocalS hbTyS
      have hbT' := hbT.defeqU_r wf trivial hbTyEq.symm
      obtain ⟨h₁Ty, h₁T⟩ := TrExprS.closedLam_hasType wf
        (show TrExprS env [] []
          (.lam0 q(Bool) <|
            .lam0 (mkApp2 Reflection.defn₂.type pS (.bvar 0)) <|
              .lam0 q(Type) <| mkApp3 q(@_root_.ite.{1}) (.bvar 0) pS
                (mkApp3 Reflection.defn₂.toDec pS (.bvar 2) (.bvar 1)))
          (.lam (bTyOrig.inst pV) <|
            .lam (HTyPre.inst pV 1) <|
              .lam (αTyPre.inst pV 2) (bodyPre.inst pV 3)) from
            .lam hbTy hbTyLocalS hrest₂)
      have hβ₁b := hβ₁.app_same wf trivial
        (hβ₁.of_r wf trivial h₁T).hasType.1 hbT'
      obtain ⟨h₂S, hβ₂⟩ := TrExprS.applyClosedLam wf
        (show TrExprS env [] []
          (.lam0 q(Bool) <|
            .lam0 (mkApp2 Reflection.defn₂.type pS (.bvar 0)) <|
              .lam0 q(Type) <| mkApp3 q(@_root_.ite.{1}) (.bvar 0) pS
                (mkApp3 Reflection.defn₂.toDec pS (.bvar 2) (.bvar 1)))
          (.lam (bTyOrig.inst pV) <|
            .lam (HTyPre.inst pV 1) <|
              .lam (αTyPre.inst pV 2) (bodyPre.inst pV 3)) from
            .lam hbTy hbTyLocalS hrest₂) hbS hbT'
      have hbClosed := hbS.closed.looseBVarRange_zero
      have hbLift (s d : Nat) : bS.liftLooseBVars' s d = bS :=
        Expr.liftLooseBVars_eq_self (by rw [hbClosed]; omega)
      have hbInst (a : Expr) (k : Nat) : bS.instantiate1' a k = bS :=
        Expr.instantiate1'_eq_self (by rw [hbClosed]; omega)
      have hsrc₂ :
          ((Expr.lam0 (mkApp2 Reflection.defn₂.type pS (.bvar 0)) <|
            .lam0 q(Type) <| mkApp3 q(@_root_.ite.{1}) (.bvar 0) pS
              (mkApp3 Reflection.defn₂.toDec pS (.bvar 2) (.bvar 1))).instantiate1' bS) =
          (Expr.lam0 (mkApp2 Reflection.defn₂.type pS bS) <|
            .lam0 q(Type) <| mkApp3 q(@_root_.ite.{1}) (.bvar 0) pS
              (mkApp3 Reflection.defn₂.toDec pS bS (.bvar 1))) := by
        simp [Lean.Expr.instantiate1', Expr.lam0, mkApp3, mkApp2, mkApp,
          mkAppB, hbLift, hpInst, hrtypeInst, htoDecInst]
      have h₂S' : TrExprS env [] []
          (.lam0 (mkApp2 Reflection.defn₂.type pS bS) <|
            .lam0 q(Type) <| mkApp3 q(@_root_.ite.{1}) (.bvar 0) pS
              (mkApp3 Reflection.defn₂.toDec pS bS (.bvar 1)))
          (.lam ((HTyPre.inst pV 1).inst bV) <|
            .lam ((αTyPre.inst pV 2).inst bV 1)
              ((bodyPre.inst pV 3).inst bV 2)) := by
        rw [← hsrc₂]
        simpa [VExpr.inst] using h₂S
      have hβ₁₂ := hβ₁b.trans wf trivial hβ₂
      cases h₂S' with
      | lam hHTy hHTyLocalS hrest₃ =>
        have hHTyEq := TrExprS.uniq (Us := []) wf hctx
          hHTyLocalS hHTyS
        have hHT' := hHT.defeqU_r wf trivial hHTyEq.symm
        obtain ⟨_, h₂T⟩ := TrExprS.closedLam_hasType wf
          (show TrExprS env [] []
            (.lam0 (mkApp2 Reflection.defn₂.type pS bS) <|
              .lam0 q(Type) <| mkApp3 q(@_root_.ite.{1}) (.bvar 0) pS
                (mkApp3 Reflection.defn₂.toDec pS bS (.bvar 1)))
            (.lam ((HTyPre.inst pV 1).inst bV) <|
              .lam ((αTyPre.inst pV 2).inst bV 1)
                ((bodyPre.inst pV 3).inst bV 2)) from
              .lam hHTy hHTyLocalS hrest₃)
        have hβ₁₂H := hβ₁₂.app_same wf trivial
          (hβ₁₂.of_r wf trivial h₂T).hasType.1 hHT'
        obtain ⟨h₃S, hβ₃⟩ := TrExprS.applyClosedLam wf
          (show TrExprS env [] []
            (.lam0 (mkApp2 Reflection.defn₂.type pS bS) <|
              .lam0 q(Type) <| mkApp3 q(@_root_.ite.{1}) (.bvar 0) pS
                (mkApp3 Reflection.defn₂.toDec pS bS (.bvar 1)))
            (.lam ((HTyPre.inst pV 1).inst bV) <|
              .lam ((αTyPre.inst pV 2).inst bV 1)
                ((bodyPre.inst pV 3).inst bV 2)) from
              .lam hHTy hHTyLocalS hrest₃) hHS hHT'
        have hHClosed := hHS.closed.looseBVarRange_zero
        have hHLift (s d : Nat) : HS.liftLooseBVars' s d = HS :=
          Expr.liftLooseBVars_eq_self (by rw [hHClosed]; omega)
        have hHInst (a : Expr) (k : Nat) : HS.instantiate1' a k = HS :=
          Expr.instantiate1'_eq_self (by rw [hHClosed]; omega)
        have hsrc₃ :
            ((Expr.lam0 q(Type) <|
              mkApp3 q(@_root_.ite.{1}) (.bvar 0) pS
                (mkApp3 Reflection.defn₂.toDec pS bS (.bvar 1))).instantiate1' HS) =
            (Expr.lam0 q(Type) <|
              mkApp3 q(@_root_.ite.{1}) (.bvar 0) pS
                (mkApp3 Reflection.defn₂.toDec pS bS HS)) := by
          simp [Lean.Expr.instantiate1', Expr.lam0, mkApp3, mkApp,
            mkAppB, hHLift, hpInst, hbInst, htoDecInst]
        have h₃S' : TrExprS env [] []
            (.lam0 q(Type) <| mkApp3 q(@_root_.ite.{1}) (.bvar 0) pS
              (mkApp3 Reflection.defn₂.toDec pS bS HS))
            (.lam (((αTyPre.inst pV 2).inst bV 1).inst HV)
              (((bodyPre.inst pV 3).inst bV 2).inst HV 1)) := by
          rw [← hsrc₃]
          simpa [VExpr.inst] using h₃S
        have hβ₁₂₃ := hβ₁₂H.trans wf trivial hβ₃
        cases h₃S' with
        | lam hαTy hαTyLocalS hbody =>
          have hαTyEq := TrExprS.uniq (Us := []) wf hctx
            hαTyLocalS hαTyS
          have hαT' := hαT.defeqU_r wf trivial hαTyEq.symm
          obtain ⟨_, h₃T⟩ := TrExprS.closedLam_hasType wf
            (show TrExprS env [] []
              (.lam0 q(Type) <| mkApp3 q(@_root_.ite.{1}) (.bvar 0) pS
                (mkApp3 Reflection.defn₂.toDec pS bS HS))
              (.lam (((αTyPre.inst pV 2).inst bV 1).inst HV)
                (((bodyPre.inst pV 3).inst bV 2).inst HV 1)) from
                .lam hαTy hαTyLocalS hbody)
          have hβ₁₂₃α := hβ₁₂₃.app_same wf trivial
            (hβ₁₂₃.of_r wf trivial h₃T).hasType.1 hαT'
          obtain ⟨h₄S, hβ₄⟩ := TrExprS.applyClosedLam wf
            (show TrExprS env [] []
              (.lam0 q(Type) <| mkApp3 q(@_root_.ite.{1}) (.bvar 0) pS
                (mkApp3 Reflection.defn₂.toDec pS bS HS))
              (.lam (((αTyPre.inst pV 2).inst bV 1).inst HV)
                (((bodyPre.inst pV 3).inst bV 2).inst HV 1)) from
                .lam hαTy hαTyLocalS hbody) hαS hαT'
          have hαClosed := hαS.closed.looseBVarRange_zero
          have hαLift (s d : Nat) : αS.liftLooseBVars' s d = αS :=
            Expr.liftLooseBVars_eq_self (by rw [hαClosed]; omega)
          have hsrc₄ :
              (mkApp3 q(@_root_.ite.{1}) (.bvar 0) pS
                (mkApp3 Reflection.defn₂.toDec pS bS HS)).instantiate1' αS =
              mkApp3 q(@_root_.ite.{1}) αS pS
                (mkApp3 Reflection.defn₂.toDec pS bS HS) := by
            simp [Lean.Expr.instantiate1', mkApp3, mkApp, mkAppB, hαLift,
              hpInst, hbInst, hHInst, htoDecInst]
          rw [hsrc₄] at h₄S
          have hbodyEq := TrExprS.uniq (Us := []) wf hctx h₄S hprefix
          exact hβ₁₂₃α.trans wf trivial <| hβ₄.trans wf trivial hbodyEq

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
      .boolTrue := by
  have heq₁ := heq
  obtain ⟨_, hd⟩ := heq₁
  obtain ⟨⟨_, hpropSort⟩, _, hleftBodyT⟩ :=
    hd.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightBodyT⟩ := hd.hasType.2.lam_inv wf trivial
  have h₁ := VEnv.IsDefEqU.lam_instU wf trivial heq hpropSort
    hleftBodyT hrightBodyT hp
  simp [VExpr.inst, hrtypeLClosed.instN_eq, hrtypeRClosed.instN_eq,
    hriteClosed.instN_eq] at h₁
  have h₁' := h₁
  obtain ⟨_, hd₁⟩ := h₁'
  obtain ⟨⟨_, hHSort⟩, _, hleftInnerT⟩ :=
    hd₁.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightInnerT⟩ := hd₁.hasType.2.lam_inv wf trivial
  have h₂ := VEnv.IsDefEqU.lam_instU_hetero wf trivial h₁ hHSort
    hleftInnerT hrightInnerT hHL hHR
  simp [VExpr.inst, VExpr.inst_lift, hriteClosed.instN_eq] at h₂
  obtain ⟨_, hd₂⟩ := h₂
  have h₂U : env.IsDefEqU 0 []
      (.app (.app (.app rite p) .boolTrue) H)
      (.lam (.sort (.succ .zero)) <|
        .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 1) := by
    simpa [VExpr.boolTrue, VExpr.inst, VExpr.lift, VExpr.liftN, liftVar]
      using (show env.IsDefEqU 0 [] _ _ from ⟨_, hd₂⟩)
  obtain ⟨_, hd₂U⟩ := h₂U
  have h₂U' : env.IsDefEqU 0 []
      (.app (.app (.app rite p) .boolTrue) H)
      (.lam (.sort (.succ .zero)) <|
        .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 1) := ⟨_, hd₂U⟩
  have hselectorCanonical : env.HasType 0 []
      (.lam (.sort (.succ .zero)) <|
        .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 1)
      (.forallE (.sort (.succ .zero)) <|
        .forallE (.bvar 0) <| .forallE (.bvar 1) <| .bvar 2) := by
    exact .lam (.sort trivial) <| .lam (.bvar .zero) <|
      .lam (.bvar (.succ .zero)) (.bvar (.succ .zero))
  have hprefixT := (h₂U'.of_r wf trivial hselectorCanonical).hasType.1
  have h₃ := h₂U'.app_same wf trivial hprefixT hbool
  have hprefixBoolT := VEnv.HasType.app hprefixT hbool
  have h₄ := h₃.app_same wf trivial hprefixBoolT htrue
  have hprefixBoolTrueT := VEnv.HasType.app hprefixBoolT htrue
  have h₅ := h₄.app_same wf trivial hprefixBoolTrueT hfalse
  obtain ⟨_, hselectorOuterBodyT⟩ :=
    (hselectorCanonical.lam_inv wf trivial).2
  have hbetaType : env.IsDefEqU 0 []
      (.app
        (.lam (.sort (.succ .zero)) <|
          .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 1)
        .bool)
      (.lam .bool <| .lam .bool <| .bvar 1) :=
    ⟨_, .beta hselectorOuterBodyT hbool⟩
  have hselectorBodyT := hselectorCanonical
  have hselectorBoolT :=
    (hbetaType.of_l wf trivial (.app hselectorBodyT hbool)).hasType.2
  obtain ⟨_, hselectorBoolBodyT⟩ :=
    (hselectorBoolT.lam_inv wf trivial).2
  have hbetaTrue : env.IsDefEqU 0 []
      (.app (.lam .bool <| .lam .bool <| .bvar 1) .boolTrue)
      (.lam .bool .boolTrue) :=
    ⟨_, .beta hselectorBoolBodyT htrue⟩
  have hselectorTrueT :=
    (hbetaTrue.of_l wf trivial (.app hselectorBoolT htrue)).hasType.2
  obtain ⟨_, hselectorTrueBodyT⟩ :=
    (hselectorTrueT.lam_inv wf trivial).2
  have hbetaFalse : env.IsDefEqU 0 []
      (.app (.lam .bool .boolTrue) .boolFalse) .boolTrue :=
    ⟨_, .beta hselectorTrueBodyT hfalse⟩
  have hbetaTypeApp := hbetaType.app_same wf trivial
    (.app hselectorBodyT hbool) htrue
  have hbetaTypeApps := hbetaTypeApp.app_same wf trivial
    (.app (.app hselectorBodyT hbool) htrue) hfalse
  have hbetaTrueApp := hbetaTrue.app_same wf trivial
    (.app hselectorBoolT htrue) hfalse
  exact h₅.trans wf trivial <|
    hbetaTypeApps.trans wf trivial <|
      hbetaTrueApp.trans wf trivial hbetaFalse

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
      .boolFalse := by
  have heq₁ := heq
  obtain ⟨_, hd⟩ := heq₁
  obtain ⟨⟨_, hpropSort⟩, _, hleftBodyT⟩ :=
    hd.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightBodyT⟩ := hd.hasType.2.lam_inv wf trivial
  have h₁ := VEnv.IsDefEqU.lam_instU wf trivial heq hpropSort
    hleftBodyT hrightBodyT hp
  simp [VExpr.inst, hrtypeLClosed.instN_eq, hrtypeRClosed.instN_eq,
    hriteClosed.instN_eq] at h₁
  have h₁' := h₁
  obtain ⟨_, hd₁⟩ := h₁'
  obtain ⟨⟨_, hHSort⟩, _, hleftInnerT⟩ :=
    hd₁.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightInnerT⟩ := hd₁.hasType.2.lam_inv wf trivial
  have h₂ := VEnv.IsDefEqU.lam_instU_hetero wf trivial h₁ hHSort
    hleftInnerT hrightInnerT hHL hHR
  simp [VExpr.inst, VExpr.inst_lift, hriteClosed.instN_eq] at h₂
  obtain ⟨_, hd₂⟩ := h₂
  have h₂U : env.IsDefEqU 0 []
      (.app (.app (.app rite p) .boolFalse) H)
      (.lam (.sort (.succ .zero)) <|
        .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 0) := by
    simpa [VExpr.boolFalse, VExpr.inst, VExpr.lift, VExpr.liftN, liftVar]
      using (show env.IsDefEqU 0 [] _ _ from ⟨_, hd₂⟩)
  obtain ⟨_, hd₂U⟩ := h₂U
  have h₂U' : env.IsDefEqU 0 []
      (.app (.app (.app rite p) .boolFalse) H)
      (.lam (.sort (.succ .zero)) <|
        .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 0) := ⟨_, hd₂U⟩
  have hselectorCanonical : env.HasType 0 []
      (.lam (.sort (.succ .zero)) <|
        .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 0)
      (.forallE (.sort (.succ .zero)) <|
        .forallE (.bvar 0) <| .forallE (.bvar 1) <| .bvar 2) := by
    exact .lam (.sort trivial) <| .lam (.bvar .zero) <|
      .lam (.bvar (.succ .zero)) (.bvar .zero)
  have hprefixT := (h₂U'.of_r wf trivial hselectorCanonical).hasType.1
  have h₃ := h₂U'.app_same wf trivial hprefixT hbool
  have hprefixBoolT := VEnv.HasType.app hprefixT hbool
  have h₄ := h₃.app_same wf trivial hprefixBoolT htrue
  have hprefixBoolTrueT := VEnv.HasType.app hprefixBoolT htrue
  have h₅ := h₄.app_same wf trivial hprefixBoolTrueT hfalse
  obtain ⟨_, hselectorOuterBodyT⟩ :=
    (hselectorCanonical.lam_inv wf trivial).2
  have hbetaType : env.IsDefEqU 0 []
      (.app
        (.lam (.sort (.succ .zero)) <|
          .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 0)
        .bool)
      (.lam .bool <| .lam .bool <| .bvar 0) :=
    ⟨_, .beta hselectorOuterBodyT hbool⟩
  have hselectorBodyT := hselectorCanonical
  have hselectorBoolT :=
    (hbetaType.of_l wf trivial (.app hselectorBodyT hbool)).hasType.2
  obtain ⟨_, hselectorBoolBodyT⟩ :=
    (hselectorBoolT.lam_inv wf trivial).2
  have hbetaTrue : env.IsDefEqU 0 []
      (.app (.lam .bool <| .lam .bool <| .bvar 0) .boolTrue)
      (.lam .bool <| .bvar 0) :=
    ⟨_, .beta hselectorBoolBodyT htrue⟩
  have hselectorTrueT :=
    (hbetaTrue.of_l wf trivial (.app hselectorBoolT htrue)).hasType.2
  obtain ⟨_, hselectorTrueBodyT⟩ :=
    (hselectorTrueT.lam_inv wf trivial).2
  have hbetaFalse : env.IsDefEqU 0 []
      (.app (.lam .bool <| .bvar 0) .boolFalse) .boolFalse :=
    ⟨_, .beta hselectorTrueBodyT hfalse⟩
  have hbetaTypeApp := hbetaType.app_same wf trivial
    (.app hselectorBodyT hbool) htrue
  have hbetaTypeApps := hbetaTypeApp.app_same wf trivial
    (.app (.app hselectorBodyT hbool) htrue) hfalse
  have hbetaTrueApp := hbetaTrue.app_same wf trivial
    (.app hselectorBoolT htrue) hfalse
  exact h₅.trans wf trivial <|
    hbetaTypeApps.trans wf trivial <|
      hbetaTrueApp.trans wf trivial hbetaFalse

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
      (.app (.app (.app (.app (.app (.app rite p) .boolTrue) H) α) t) e) t := by
  have heq' := heq
  obtain ⟨_, hd⟩ := heq'
  obtain ⟨⟨_, hpropSort⟩, _, hleftBodyT⟩ :=
    hd.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightBodyT⟩ := hd.hasType.2.lam_inv wf trivial
  have h₁ := VEnv.IsDefEqU.lam_instU wf trivial heq hpropSort
    hleftBodyT hrightBodyT hp
  simp [VExpr.inst, hrtypeLClosed.instN_eq, hrtypeRClosed.instN_eq,
    hriteClosed.instN_eq] at h₁
  have h₁' := h₁
  obtain ⟨_, hd₁⟩ := h₁'
  obtain ⟨⟨_, hHSort⟩, _, hleftInnerT⟩ :=
    hd₁.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightInnerT⟩ := hd₁.hasType.2.lam_inv wf trivial
  have h₂ := VEnv.IsDefEqU.lam_instU_hetero wf trivial h₁ hHSort
    hleftInnerT hrightInnerT hHL hHR
  simp [VExpr.inst, VExpr.inst_lift, hriteClosed.instN_eq] at h₂
  have hselect : env.IsDefEqU 0 []
      (.app (.app (.app rite p) .boolTrue) H)
      (.lam (.sort (.succ .zero)) <|
        .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 1) := by
    simpa [VExpr.boolTrue, VExpr.inst, VExpr.lift, VExpr.liftN, liftVar]
      using h₂
  have hselectorT : env.HasType 0 []
      (.lam (.sort (.succ .zero)) <|
        .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 1)
      (.forallE (.sort (.succ .zero)) <|
        .forallE (.bvar 0) <| .forallE (.bvar 1) <| .bvar 2) :=
    .lam (.sort trivial) <| .lam (.bvar .zero) <|
      .lam (.bvar (.succ .zero)) (.bvar (.succ .zero))
  have hprefixT := (hselect.of_r wf trivial hselectorT).hasType.1
  have h₃ := hselect.app_same wf trivial hprefixT hα
  have hprefixαT := VEnv.HasType.app hprefixT hα
  have hαClosed : α.ClosedN := (hα.closedN' wf.ordered.closed trivial).1
  have hprefixαT' : env.HasType 0 []
      (.app (.app (.app (.app rite p) .boolTrue) H) α)
      (.forallE α <| .forallE α α) := by
    simpa [VExpr.inst, hαClosed.lift_eq] using hprefixαT
  have h₄ := h₃.app_same wf trivial hprefixαT' ht
  have hprefixαtT := VEnv.HasType.app hprefixαT' ht
  have hprefixαtT' : env.HasType 0 []
      (.app (.app (.app (.app (.app rite p) .boolTrue) H) α) t)
      (.forallE α α) := by
    simpa [VExpr.inst, hαClosed.lift_eq, hαClosed.instN_eq] using
      hprefixαtT
  have h₅ := h₄.app_same wf trivial hprefixαtT' he
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
  have htClosed : t.ClosedN := (ht.closedN' wf.ordered.closed trivial).1
  have hbetaT : env.IsDefEqU 0 []
      (.app (.lam α <| .lam α <| .bvar 1) t) (.lam α t) :=
    by
      simpa [VExpr.inst, hαClosed.instN_eq, htClosed.lift_eq] using
        (show env.IsDefEqU 0 [] _ _ from ⟨_, .beta htrueBodyT ht⟩)
  have hselectorT' : env.HasType 0 [] (.lam α t) (.forallE α α) := by
    have h := (hbetaT.of_l wf trivial (.app hselectorαT' ht)).hasType.2
    simpa [VExpr.inst, hαClosed.instN_eq] using h
  obtain ⟨_, hfalseBodyT⟩ := (hselectorT'.lam_inv wf trivial).2
  have hbetaE : env.IsDefEqU 0 [] (.app (.lam α t) e) t :=
    by
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
  exact h₅.trans wf trivial <|
    hbetaαApps.trans wf trivial <|
      (hbetaT.app_same wf trivial hselectorAppT he).trans
        wf trivial hbetaE

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
      (.app (.app (.app (.app (.app (.app rite p) .boolFalse) H) α) t) e) e := by
  have heq' := heq
  obtain ⟨_, hd⟩ := heq'
  obtain ⟨⟨_, hpropSort⟩, _, hleftBodyT⟩ :=
    hd.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightBodyT⟩ := hd.hasType.2.lam_inv wf trivial
  have h₁ := VEnv.IsDefEqU.lam_instU wf trivial heq hpropSort
    hleftBodyT hrightBodyT hp
  simp [VExpr.inst, hrtypeLClosed.instN_eq, hrtypeRClosed.instN_eq,
    hriteClosed.instN_eq] at h₁
  have h₁' := h₁
  obtain ⟨_, hd₁⟩ := h₁'
  obtain ⟨⟨_, hHSort⟩, _, hleftInnerT⟩ :=
    hd₁.hasType.1.lam_inv wf trivial
  obtain ⟨_, _, hrightInnerT⟩ := hd₁.hasType.2.lam_inv wf trivial
  have h₂ := VEnv.IsDefEqU.lam_instU_hetero wf trivial h₁ hHSort
    hleftInnerT hrightInnerT hHL hHR
  simp [VExpr.inst, VExpr.inst_lift, hriteClosed.instN_eq] at h₂
  have hselect : env.IsDefEqU 0 []
      (.app (.app (.app rite p) .boolFalse) H)
      (.lam (.sort (.succ .zero)) <|
        .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 0) := by
    simpa [VExpr.boolFalse, VExpr.inst, VExpr.lift, VExpr.liftN, liftVar]
      using h₂
  have hselectorT : env.HasType 0 []
      (.lam (.sort (.succ .zero)) <|
        .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 0)
      (.forallE (.sort (.succ .zero)) <|
        .forallE (.bvar 0) <| .forallE (.bvar 1) <| .bvar 2) :=
    .lam (.sort trivial) <| .lam (.bvar .zero) <|
      .lam (.bvar (.succ .zero)) (.bvar .zero)
  have hprefixT := (hselect.of_r wf trivial hselectorT).hasType.1
  have h₃ := hselect.app_same wf trivial hprefixT hα
  have hprefixαT := VEnv.HasType.app hprefixT hα
  have hαClosed : α.ClosedN := (hα.closedN' wf.ordered.closed trivial).1
  have hprefixαT' : env.HasType 0 []
      (.app (.app (.app (.app rite p) .boolFalse) H) α)
      (.forallE α <| .forallE α α) := by
    simpa [VExpr.inst, hαClosed.lift_eq] using hprefixαT
  have h₄ := h₃.app_same wf trivial hprefixαT' ht
  have hprefixαtT := VEnv.HasType.app hprefixαT' ht
  have hprefixαtT' : env.HasType 0 []
      (.app (.app (.app (.app (.app rite p) .boolFalse) H) α) t)
      (.forallE α α) := by
    simpa [VExpr.inst, hαClosed.lift_eq, hαClosed.instN_eq] using
      hprefixαtT
  have h₅ := h₄.app_same wf trivial hprefixαtT' he
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
  have htClosed : t.ClosedN := (ht.closedN' wf.ordered.closed trivial).1
  have hbetaT : env.IsDefEqU 0 []
      (.app (.lam α <| .lam α <| .bvar 0) t) (.lam α <| .bvar 0) := by
    simpa [VExpr.inst, hαClosed.instN_eq, htClosed.lift_eq] using
      (show env.IsDefEqU 0 [] _ _ from ⟨_, .beta htrueBodyT ht⟩)
  have hselectorT' : env.HasType 0 [] (.lam α <| .bvar 0) (.forallE α α) := by
    have h := (hbetaT.of_l wf trivial (.app hselectorαT' ht)).hasType.2
    simpa [VExpr.inst, hαClosed.instN_eq] using h
  obtain ⟨_, hfalseBodyT⟩ := (hselectorT'.lam_inv wf trivial).2
  have hbetaE : env.IsDefEqU 0 [] (.app (.lam α <| .bvar 0) e) e :=
    by
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
  exact h₅.trans wf trivial <| hbetaαApps.trans wf trivial <|
    (hbetaT.app_same wf trivial hselectorAppT he).trans wf trivial hbetaE

private theorem reflectionITE_true_translation_shape
    {env : VEnv} {r : Reflection} {l : VExpr}
    (h : TrExprS env [] []
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
        mkApp3 r.ite (.bvar 1) q(true) (.bvar 0)) l) :
    ∃ rtype rite, l =
      (.lam (.sort .zero) <|
        .lam (.app (.app rtype (.bvar 0)) .boolTrue) <|
          .app (.app (.app rite (.bvar 1)) .boolTrue) (.bvar 0)) ∧
      TrExprS env [] [(none, .vlam (.sort .zero))] r.type rtype ∧
      TrExprS env []
        [(none, .vlam (.app (.app rtype (.bvar 0)) .boolTrue)),
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
        | app _ _ hHFnS htrueTyS =>
          cases hHFnS with
          | app _ _ hrtypeTyS hpTyS =>
            cases hpTyS with
            | bvar hpTy =>
              simp [VLCtx.find?, VLCtx.next] at hpTy
              rcases hpTy with ⟨rfl, rfl⟩
              cases htrueTyS with
              | const _ hus _ =>
                simp at hus
                subst hus
                cases hbody with
                | app _ _ hfn harg =>
                  cases hfn with
                  | app _ _ hfn htrue =>
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
                          cases htrue with
                          | const _ hus _ =>
                            simp at hus
                            subst hus
                            exact ⟨_, _, rfl, hrtypeTyS, hite⟩

private theorem reflectionITE_true_rhs_translation_shape
    {env : VEnv} {r : Reflection} {rr : VExpr}
    (h : TrExprS env [] []
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
        .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 1) rr) :
    ∃ rtype, rr =
      (.lam (.sort .zero) <|
        .lam (.app (.app rtype (.bvar 0)) .boolTrue) <|
          .lam (.sort (.succ .zero)) <|
            .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 1) ∧
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
        | app _ _ hHFnS htrueTyS =>
          cases hHFnS with
          | app _ _ hrtypeTyS hpTyS =>
            cases hpTyS with
            | bvar hpTy =>
              simp [VLCtx.find?, VLCtx.next] at hpTy
              rcases hpTy with ⟨rfl, rfl⟩
              cases htrueTyS with
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
                              simp [VLCtx.find?, VLCtx.next] at hresult
                              rcases hresult with ⟨rfl, rfl⟩
                              exact ⟨_, rfl, hrtypeTyS⟩

private theorem reflectionITE_false_translation_shape
    {env : VEnv} {r : Reflection} {l : VExpr}
    (h : TrExprS env [] []
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
        mkApp3 r.ite (.bvar 1) q(false) (.bvar 0)) l) :
    ∃ rtype rite, l =
      (.lam (.sort .zero) <|
        .lam (.app (.app rtype (.bvar 0)) .boolFalse) <|
          .app (.app (.app rite (.bvar 1)) .boolFalse) (.bvar 0)) ∧
      TrExprS env [] [(none, .vlam (.sort .zero))] r.type rtype ∧
      TrExprS env []
        [(none, .vlam (.app (.app rtype (.bvar 0)) .boolFalse)),
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
        | app _ _ hHFnS hfalseTyS =>
          cases hHFnS with
          | app _ _ hrtypeTyS hpTyS =>
            cases hpTyS with
            | bvar hpTy =>
              simp [VLCtx.find?, VLCtx.next] at hpTy
              rcases hpTy with ⟨rfl, rfl⟩
              cases hfalseTyS with
              | const _ hus _ =>
                simp at hus
                subst hus
                cases hbody with
                | app _ _ hfn harg =>
                  cases hfn with
                  | app _ _ hfn hfalse =>
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
                          cases hfalse with
                          | const _ hus _ =>
                            simp at hus
                            subst hus
                            exact ⟨_, _, rfl, hrtypeTyS, hite⟩

private theorem reflectionITE_false_rhs_translation_shape
    {env : VEnv} {r : Reflection} {rr : VExpr}
    (h : TrExprS env [] []
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
        .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 0) rr) :
    ∃ rtype, rr =
      (.lam (.sort .zero) <|
        .lam (.app (.app rtype (.bvar 0)) .boolFalse) <|
          .lam (.sort (.succ .zero)) <|
            .lam (.bvar 0) <| .lam (.bvar 1) <| .bvar 0) ∧
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
        | app _ _ hHFnS hfalseTyS =>
          cases hHFnS with
          | app _ _ hrtypeTyS hpTyS =>
            cases hpTyS with
            | bvar hpTy =>
              simp [VLCtx.find?, VLCtx.next] at hpTy
              rcases hpTy with ⟨rfl, rfl⟩
              cases hfalseTyS with
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
                              simp [VLCtx.find?, VLCtx.next] at hresult
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
    reflectionITE_true_translation_shape htl
  obtain ⟨trueRTypeR, rfl, htrueRTypeR⟩ :=
    reflectionITE_true_rhs_translation_shape htr
  obtain ⟨falseRTypeL, falseITE, rfl, hfalseRTypeL, hfalseITE⟩ :=
    reflectionITE_false_translation_shape hfl
  obtain ⟨falseRTypeR, rfl, hfalseRTypeR⟩ :=
    reflectionITE_false_rhs_translation_shape hfr
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

/-- A successful check of the fixed natural-number equality condition exports
both the normalized Boolean-selector equations and the checked equality
between `Nat.decEq` and its reflected `Nat.beq` implementation. -/
theorem Condition.natEq.check.WF
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {fail : ∀ {α}, TypeChecker.M α}
    (hlparams : c.lparams = []) (hvlctx : c.vlctx = [])
    (hdec : c.TrExprS Condition.natEq.dec dec')
    (hprop : c.TrExprS Condition.natEq.prop prop')
    (hpropTy : c.TrExprS q(Nat → Nat → Prop) propTy')
    (hrtype : c.TrExprS Reflection.defn₂.type rtype')
    (hrtypeUnique : TrExprS.IsUnique Reflection.defn₂.type)
    (hrtypeCanon : c.TrExprS q(Prop → Bool → Prop) rtypeCanon')
    (hite : c.TrExprS Reflection.defn₂.ite ite')
    (hiteUnique : TrExprS.IsUnique Reflection.defn₂.ite)
    (hiteTy : c.TrExprS (.arrow q(Prop) <| .arrow q(Bool) <|
      .arrow (mkApp2 Reflection.defn₂.type (.bvar 1) (.bvar 0))
        q(∀ α : Type, α → α → α)) iteTy')
    (htrueL : c.TrExprS
      (.lam0 q(Prop) <|
        .lam0 (mkApp2 Reflection.defn₂.type (.bvar 0) q(true)) <|
          mkApp3 Reflection.defn₂.ite (.bvar 1) q(true) (.bvar 0)) trueL')
    (htrueR : c.TrExprS
      (.lam0 q(Prop) <|
        .lam0 (mkApp2 Reflection.defn₂.type (.bvar 0) q(true)) <|
          .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <|
            .bvar 1) trueR')
    (hfalseL : c.TrExprS
      (.lam0 q(Prop) <|
        .lam0 (mkApp2 Reflection.defn₂.type (.bvar 0) q(false)) <|
          mkApp3 Reflection.defn₂.ite (.bvar 1) q(false) (.bvar 0)) falseL')
    (hfalseR : c.TrExprS
      (.lam0 q(Prop) <|
        .lam0 (mkApp2 Reflection.defn₂.type (.bvar 0) q(false)) <|
          .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <|
            .bvar 0) falseR')
    (he : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <| mkApp3 Reflection.defn₂.toDec
        (mkApp2 Condition.natEq.prop (.bvar 1) (.bvar 0))
        (mkApp2 q(Nat.beq) (.bvar 1) (.bvar 0))
        (mkApp2
          q(fun n m {q : Prop} (H : _ → _ → q) =>
            H (@Nat.eq_of_beq_eq_true n m) (@Nat.ne_of_beq_eq_false n m))
          (.bvar 1) (.bvar 0))) e')
    (hdecide : c.TrExprS Condition.natEqDecideFn decide')
    (hdecideTy : c.TrExprS q(Nat → Nat → Bool) decideTy')
    (hasBool : c.TrExprS q(Nat.beq) asBool')
    (hasBoolTy : c.TrExprS q(Nat → Nat → Bool) asBoolTy')
    (hproof : c.TrExprS
      q(fun n m {q : Prop} (H : _ → _ → q) =>
        H (@Nat.eq_of_beq_eq_true n m) (@Nat.ne_of_beq_eq_false n m)) proof')
    (hfail : ∀ {α} {s'}, TypeChecker.M.WF c s'
      (fail : TypeChecker.M α) fun _ _ => False) :
    TypeChecker.M.WF c s (Condition.natEq.check fail (ite := true))
      fun _ _ =>
        Lean4Lean.Environment.VEnv.ReflectionITECertificate c.venv ∧
          c.HasType rtype' rtypeCanon' ∧
          c.HasType ite' iteTy' ∧
          c.HasType prop' propTy' ∧
          c.HasType decide' decideTy' ∧
          c.HasType asBool' asBoolTy' ∧
          (∃ proofTy', c.HasType proof' proofTy' ∧
            c.HasType proofTy' (.sort .zero)) ∧
          c.IsDefEqU e' dec' := by
  have htrueL0 := htrueL
  have htrueR0 := htrueR
  have hfalseL0 := hfalseL
  have hfalseR0 := hfalseR
  change TrExprS c.venv c.lparams c.vlctx _ _ at htrueL0 htrueR0 hfalseL0 hfalseR0
  rw [hlparams, hvlctx] at htrueL0 htrueR0 hfalseL0 hfalseR0
  have himpl : Condition.natEq.impl = .reflectNatNat q(Nat.beq)
      Reflection.defn₂
      q(fun n m {q : Prop} (H : _ → _ → q) =>
        H (@Nat.eq_of_beq_eq_true n m) (@Nat.ne_of_beq_eq_false n m)) := rfl
  simp [Condition.check, himpl]
  refine checkTypeDiscard.bind_WF hdec.fvarsIn fun _ => ?_
  refine inferTypeIsDefEqGuard.bind_WF
    hprop hpropTy hfail fun _ hpropHas => ?_
  change TypeChecker.M.WF c _ (do
    Reflection.defn₂.check fail
    Reflection.defn₂.checkITE fail
    let _ ← TypeChecker.checkType _
    unless ← TypeChecker.isDefEq
        (← TypeChecker.inferType Condition.natEqDecideFn)
        q(Nat → Nat → Bool) do fail
    unless ← TypeChecker.isDefEq (← TypeChecker.inferType q(Nat.beq))
        q(Nat → Nat → Bool) do fail
    unless ← TypeChecker.isProp (← TypeChecker.inferType
        q(fun n m {q : Prop} (H : _ → _ → q) =>
          H (@Nat.eq_of_beq_eq_true n m)
            (@Nat.ne_of_beq_eq_false n m))) do fail
    unless ← TypeChecker.isDefEq _ Condition.natEq.dec do fail) _
  refine (Reflection.check.WF hrtype hrtypeUnique hrtypeCanon
    (fun _ => hfail)).bind fun _ _ _ hrtypeHas => ?_
  refine (Reflection.checkITE.WF hite hiteUnique hiteTy htrueL htrueR
    hfalseL hfalseR (fun _ => hfail)).bind fun _ _ _ hiteCert => ?_
  refine checkTypeDiscard.bind_WF he.fvarsIn fun _ => ?_
  refine inferTypeIsDefEqGuard.bind_WF
    hdecide hdecideTy hfail fun _ hdecideHas => ?_
  refine inferTypeIsDefEqGuard.bind_WF
    hasBool hasBoolTy hfail fun _ hasBoolHas => ?_
  refine inferTypeIsPropGuard.bind_WF
    hproof hfail fun _ hproofHas => ?_
  refine (isDefEqGuard.WF he hdec hfail).mono fun _ _ _ heq => ?_
  have htrueEq0 := hiteCert.2.1
  have hfalseEq0 := hiteCert.2.2
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx _ _ at htrueEq0 hfalseEq0
  rw [hlparams, hvlctx] at htrueEq0 hfalseEq0
  have hselectorCert := VEnv.ReflectionITECertificate.of_checked
    hrtypeUnique hiteUnique htrueL0 htrueR0 htrueEq0
    hfalseL0 hfalseR0 hfalseEq0
  exact ⟨hselectorCert, hrtypeHas, hiteCert.1, hpropHas,
    hdecideHas, hasBoolHas, hproofHas, heq⟩

/-- Instantiate the translated closed equality-decision function at two
concrete numerals while retaining a translation of its source body. -/
theorem Condition.natEqDecideFn.instantiate
    {env : VEnv} (wf : env.WF)
    (hctors : Lean4Lean.Environment.VEnv.HasNatBoolConstructors env)
    {decide : VExpr}
    (hdecide : TrExprS env [] [] Condition.natEqDecideFn decide)
    (a b : Nat) :
    ∃ out,
      TrExprS env [] []
        (Condition.natEq.decide
          #[.lit (.natVal a), .lit (.natVal b)]) out ∧
      env.IsDefEqU 0 []
        (.app (.app decide (.natLit a)) (.natLit b)) out := by
  have ⟨haS, haT⟩ := hctors.natLitS a (Us := []) (Δ := [])
  have ⟨hbS, hbT⟩ := hctors.natLitS b (Us := []) (Δ := [])
  unfold Condition.natEqDecideFn at hdecide
  cases hdecide with
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
      have hinnerS' : TrExprS env [] [(none, .vlam natTy₁)]
          (.lam0 q(Nat) <|
            Condition.natEq.decide #[.bvar 1, .bvar 0])
          (.lam natTy₂ body) := .lam hnatTy₂ hnatS₂ hbodyS
      have hinnerInst := TrExprS.inst (env := env) (Us := []) (Δ := [])
        (e₀' := .natLit a) (A₀ := natTy₁) wf.ordered haT'
        hinnerS' haS
      cases hinnerInst with
      | lam hnatTy₂' hnatS₂' hbodyInstS =>
        have hnatEq₂ := TrExprS.uniq (Us := []) wf hctx hnatS₂'
          (hnatCanon [])
        have hbT' := hbT.defeqU_r wf trivial hnatEq₂.symm
        have hbodyInst₂ := TrExprS.inst (env := env) (Us := []) (Δ := [])
          (e₀' := .natLit b) wf.ordered hbT' hbodyInstS hbS
        refine ⟨(body.inst (.natLit a) 1).inst (.natLit b), ?_, ?_⟩
        · simpa [Condition.natEqDecideFn, Condition.decide,
            Expr.instantiate1', Expr.instantiate1'_instantiate1'] using
            hbodyInst₂
        · have hcall : TrExprS env [] []
              (Condition.natEq.decide
                #[.lit (.natVal a), .lit (.natVal b)])
              ((body.inst (.natLit a) 1).inst (.natLit b)) := by
            simpa [Condition.natEqDecideFn, Condition.decide,
              Expr.instantiate1', Expr.instantiate1'_instantiate1'] using
              hbodyInst₂
          have hdecideFull : TrExprS env [] []
              Condition.natEqDecideFn
              (.lam natTy₁ <| .lam natTy₂ body) := by
            unfold Condition.natEqDecideFn
            exact .lam hnatTy₁ hnatS₁ (.lam hnatTy₂ hnatS₂ hbodyS)
          exact (Condition.natEqDecideFn.call_eq (Δ := []) wf trivial hdecideFull
            haS hbS haT hbT hcall).symm

/-- Expose the translated proposition and `Nat.decEq` argument inside a
concrete equality-decision body. -/
theorem Condition.natEqDecide_call_shape
    {env : VEnv} {a b : Nat} {out : VExpr}
    (h : TrExprS env [] []
      (Condition.natEq.decide
        #[.lit (.natVal a), .lit (.natVal b)]) out) :
    ∃ iteV propV decV,
      out = .app (.app (.app (.app (.app iteV .bool) propV) decV)
        .boolTrue) .boolFalse ∧
      TrExprS env [] [] q(@_root_.ite.{1}) iteV ∧
      TrExprS env [] []
        (mkApp2 Condition.natEq.prop
          (.lit (.natVal a)) (.lit (.natVal b))) propV ∧
      TrExprS env [] []
        (mkApp2 Condition.natEq.dec
          (.lit (.natVal a)) (.lit (.natVal b))) decV := by
  simp only [Condition.decide, Condition.ite] at h
  cases h with
  | app _ _ hfn hfalse =>
    cases hfn with
    | app _ _ hfn htrue =>
      cases hfn with
      | app _ _ hfn hdec =>
        cases hfn with
        | app _ _ hfn hprop =>
          cases hfn with
          | app _ _ hite hbool =>
            cases hbool with
            | const _ hus _ =>
              simp at hus
              subst hus
              cases htrue with
              | const _ hus _ =>
                simp at hus
                subst hus
                cases hfalse with
                | const _ hus _ =>
                  simp at hus
                  subst hus
                  exact ⟨_, _, _, rfl, hite, hprop, hdec⟩

theorem Condition.natEqDec_application_shape
    {env : VEnv} {a b : Nat} {decV : VExpr}
    (h : TrExprS env [] []
      (mkApp2 Condition.natEq.dec
        (.lit (.natVal a)) (.lit (.natVal b))) decV) :
    ∃ decFn aV bV,
      decV = .app (.app decFn aV) bV ∧
      TrExprS env [] [] Condition.natEq.dec decFn ∧
      TrExprS env [] [] (.lit (.natVal a)) aV ∧
      TrExprS env [] [] (.lit (.natVal b)) bV := by
  cases h with
  | app _ _ hfn hb =>
    cases hfn with
    | app _ _ hdec ha =>
      exact ⟨_, _, _, rfl, hdec, ha, hb⟩

theorem Condition.natEqDec_application_eq_closed
    {env : VEnv} (wf : env.WF)
    (hctors : Lean4Lean.Environment.VEnv.HasNatBoolConstructors env)
    {a b : Nat} {decFn decV : VExpr}
    (hdecFn : TrExprS env [] [] Condition.natEq.dec decFn)
    (hdecV : TrExprS env [] []
      (mkApp2 Condition.natEq.dec
        (.lit (.natVal a)) (.lit (.natVal b))) decV) :
    env.IsDefEqU 0 [] decV
      (.app (.app decFn (.natLit a)) (.natLit b)) := by
  have ⟨haCanon, haT⟩ := hctors.natLitS a (Us := []) (Δ := [])
  have ⟨hbCanon, hbT⟩ := hctors.natLitS b (Us := []) (Δ := [])
  cases hdecV with
  | app hinnerT hbVT hinner hbS =>
    cases hinner with
    | app hlocalT haVT hlocal haS =>
      rename_i _ _ bV decLocal _ _ aV
      have hctx : VLCtx.IsDefEq env 0 [] [] := .refl wf trivial
      have hfnEq := TrExprS.uniq (Us := []) wf hctx hlocal hdecFn
      have haEq := TrExprS.uniq (Us := []) wf hctx haS haCanon
      have hbEq := TrExprS.uniq (Us := []) wf hctx hbS hbCanon
      have hfnApp := hfnEq.app_same wf trivial hlocalT haVT
      have hdecFnT := (hfnEq.of_l wf trivial hlocalT).hasType.2
      have hargApp := haEq.app_arg wf trivial hdecFnT haVT
      have hinnerEq := hfnApp.trans wf trivial hargApp
      have hinnerEqB := hinnerEq.app_same wf trivial hinnerT hbVT
      have hclosedInnerT :=
        (hinnerEq.of_l wf trivial hinnerT).hasType.2
      have hbApp := hbEq.app_arg wf trivial hclosedInnerT hbVT
      exact hinnerEqB.trans wf trivial hbApp

/-- Instantiate the reflected implementation that `Condition.natEq.check`
proves definitionally equal to `Nat.decEq`. -/
theorem Condition.natEqReflectedFn.instantiate
    {env : VEnv} (wf : env.WF)
    (hctors : Lean4Lean.Environment.VEnv.HasNatBoolConstructors env)
    {reflectFn : VExpr}
    (hreflect : TrExprS env [] [] Condition.natEqReflectedFn reflectFn)
    (a b : Nat) :
    ∃ out,
      TrExprS env [] []
        (mkApp3 Reflection.defn₂.toDec
          (mkApp2 Condition.natEq.prop
            (.lit (.natVal a)) (.lit (.natVal b)))
          (mkApp2 q(Nat.beq)
            (.lit (.natVal a)) (.lit (.natVal b)))
          (mkApp2 Condition.natEqReflectProof
            (.lit (.natVal a)) (.lit (.natVal b)))) out ∧
      env.IsDefEqU 0 []
        (.app (.app reflectFn (.natLit a)) (.natLit b)) out := by
  have ⟨haS, haT⟩ := hctors.natLitS a (Us := []) (Δ := [])
  have ⟨hbS, hbT⟩ := hctors.natLitS b (Us := []) (Δ := [])
  unfold Condition.natEqReflectedFn at hreflect
  cases hreflect with
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
          (.lam0 q(Nat) <| mkApp3 Reflection.defn₂.toDec
            (mkApp2 Condition.natEq.prop (.bvar 1) (.bvar 0))
            (mkApp2 q(Nat.beq) (.bvar 1) (.bvar 0))
            (mkApp2 Condition.natEqReflectProof (.bvar 1) (.bvar 0)))
          (.lam natTy₂ body) from .lam hnatTy₂ hnatS₂ hbodyS) haS
      cases hinnerInst with
      | lam hnatTy₂' hnatS₂' hbodyInstS =>
        have hnatEq₂ := TrExprS.uniq (Us := []) wf hctx hnatS₂'
          (hnatCanon [])
        have hbT' := hbT.defeqU_r wf trivial hnatEq₂.symm
        have hbodyInst₂ := TrExprS.inst (env := env) (Us := []) (Δ := [])
          (e₀' := .natLit b) wf.ordered hbT' hbodyInstS hbS
        refine ⟨(body.inst (.natLit a) 1).inst (.natLit b), ?_, ?_⟩
        · simpa [Condition.natEqReflectedFn, Expr.instantiate1',
            Expr.instantiate1'_instantiate1'] using hbodyInst₂
        · have hfnFull : TrExprS env [] [] Condition.natEqReflectedFn
              (.lam natTy₁ <| .lam natTy₂ body) := by
            unfold Condition.natEqReflectedFn
            exact .lam hnatTy₁ hnatS₁ (.lam hnatTy₂ hnatS₂ hbodyS)
          obtain ⟨_, hfnT⟩ := hfnFull.wf wf.ordered
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
              (.forallE (natTy₂.inst (.natLit a))
                bodyTy) := by
            simpa [VExpr.inst] using
              VEnv.HasType.lam hnatSort₂ hbodyInstWF.hasType.1
          have hprefixT :=
            (hbeta₁.of_r wf trivial hrightPrefixT).hasType.1
          exact (hbeta₁.app_same wf trivial hprefixT hbT').trans
            wf trivial hbeta₂

/-- Expose the translated reflection function, proposition, Boolean test,
and reflection witness in an instantiated reflected equality decision. -/
theorem Condition.natEqReflected_call_shape
    {env : VEnv} {a b : Nat} {out : VExpr}
    (h : TrExprS env [] []
      (mkApp3 Reflection.defn₂.toDec
        (mkApp2 Condition.natEq.prop
          (.lit (.natVal a)) (.lit (.natVal b)))
        (mkApp2 q(Nat.beq)
          (.lit (.natVal a)) (.lit (.natVal b)))
        (mkApp2 Condition.natEqReflectProof
          (.lit (.natVal a)) (.lit (.natVal b)))) out) :
    ∃ toDecV propV beqV proofV,
      out = .app (.app (.app toDecV propV) beqV) proofV ∧
      TrExprS env [] [] Reflection.defn₂.toDec toDecV ∧
      TrExprS env [] []
        (mkApp2 Condition.natEq.prop
          (.lit (.natVal a)) (.lit (.natVal b))) propV ∧
      TrExprS env [] []
        (mkApp2 q(Nat.beq)
          (.lit (.natVal a)) (.lit (.natVal b))) beqV ∧
      TrExprS env [] []
        (mkApp2 Condition.natEqReflectProof
          (.lit (.natVal a)) (.lit (.natVal b))) proofV := by
  cases h with
  | app _ _ hfn hproof =>
    cases hfn with
    | app _ _ hfn hbeq =>
      cases hfn with
      | app _ _ htoDec hprop =>
        exact ⟨_, _, _, _, rfl, htoDec, hprop, hbeq, hproof⟩

/-- The same reflected-call decomposition, retaining the three application
domains needed to recover the exact types of `p`, `b`, and the reflection
witness. -/
theorem Condition.natEqReflected_call_typed_shape
    {env : VEnv} {a b : Nat} {out : VExpr}
    (h : TrExprS env [] []
      (mkApp3 Reflection.defn₂.toDec
        (mkApp2 Condition.natEq.prop
          (.lit (.natVal a)) (.lit (.natVal b)))
        (mkApp2 q(Nat.beq)
          (.lit (.natVal a)) (.lit (.natVal b)))
        (mkApp2 Condition.natEqReflectProof
          (.lit (.natVal a)) (.lit (.natVal b)))) out) :
    ∃ toDecV propV beqV proofV pTy pRest bTy bRest HTy HRest,
      out = .app (.app (.app toDecV propV) beqV) proofV ∧
      TrExprS env [] [] Reflection.defn₂.toDec toDecV ∧
      TrExprS env [] []
        (mkApp2 Condition.natEq.prop
          (.lit (.natVal a)) (.lit (.natVal b))) propV ∧
      TrExprS env [] []
        (mkApp2 q(Nat.beq)
          (.lit (.natVal a)) (.lit (.natVal b))) beqV ∧
      TrExprS env [] []
        (mkApp2 Condition.natEqReflectProof
          (.lit (.natVal a)) (.lit (.natVal b))) proofV ∧
      env.HasType 0 [] toDecV (.forallE pTy pRest) ∧
      env.HasType 0 [] propV pTy ∧
      env.HasType 0 [] (.app toDecV propV) (.forallE bTy bRest) ∧
      env.HasType 0 [] beqV bTy ∧
      env.HasType 0 [] (.app (.app toDecV propV) beqV)
        (.forallE HTy HRest) ∧
      env.HasType 0 [] proofV HTy := by
  cases h with
  | app hHFnT hproofT hfn hproof =>
    cases hfn with
    | app hbFnT hbeqT hfn hbeq =>
      cases hfn with
      | app hpFnT hpropT htoDec hprop =>
        exact ⟨_, _, _, _, _, _, _, _, _, _, rfl,
          htoDec, hprop, hbeq, hproof,
          hpFnT, hpropT, hbFnT, hbeqT, hHFnT, hproofT⟩

/-- The first argument accepted by a translated `Reflection.toDec` is a
proposition.  This extracts that fact from the translated lambda and the
application typing retained above. -/
theorem Reflection.defn₂.toDec_prop_hasType
    {env : VEnv} (wf : env.WF)
    {toDecV pV pTy pRest : VExpr}
    (htoDec : TrExprS env [] [] Reflection.defn₂.toDec toDecV)
    (hfnT : env.HasType 0 [] toDecV (.forallE pTy pRest))
    (hpT : env.HasType 0 [] pV pTy) :
    env.HasType 0 [] pV (.sort .zero) := by
  unfold Reflection.defn₂ at htoDec
  cases htoDec with
  | lam hpTy hpTyS hbody =>
    rename_i bodyV
    have hpTyCanon : TrExprS env [] [] q(Prop) (.sort .zero) :=
      .sort rfl
    have hpTyEq := TrExprS.unique (by trivial) hpTyS hpTyCanon
    subst hpTyEq
    obtain ⟨bodyTy, hbodyWF⟩ := hbody.wf wf.ordered
      (Us := []) (Δ := [(none, .vlam (.sort .zero))])
      ⟨trivial, nofun, hpTy⟩
    have hcanonicalT : env.HasType 0 []
        (.lam (.sort .zero) bodyV)
        (.forallE (.sort .zero) bodyTy) :=
      .lam hpTy.choose_spec hbodyWF.hasType.1
    have hforallEq := hfnT.uniqU wf trivial hcanonicalT
    obtain ⟨_, hdomainEq⟩ := (hforallEq.forallE_inv wf trivial).1
    exact hpT.defeqU_r wf trivial ⟨_, hdomainEq⟩

/-- The third argument accepted by a translated `Reflection.toDec` has the
type computed by the translated `Reflection.type` at the same proposition
and Boolean arguments. -/
theorem Reflection.defn₂.toDec_proof_hasType
    {env : VEnv} (wf : env.WF)
    {pS bS : Expr}
    {rtype toDecV pV bV proofV : VExpr}
    {pTy pRest bTy bRest HTy HRest : VExpr}
    (hrtype : TrExprS env [] [] Reflection.defn₂.type rtype)
    (htoDec : TrExprS env [] [] Reflection.defn₂.toDec toDecV)
    (hpS : TrExprS env [] [] pS pV)
    (hbS : TrExprS env [] [] bS bV)
    (hpFnT : env.HasType 0 [] toDecV (.forallE pTy pRest))
    (hpT : env.HasType 0 [] pV pTy)
    (hbFnT : env.HasType 0 [] (.app toDecV pV) (.forallE bTy bRest))
    (hbT : env.HasType 0 [] bV bTy)
    (hHFnT : env.HasType 0 [] (.app (.app toDecV pV) bV)
      (.forallE HTy HRest))
    (hproofT : env.HasType 0 [] proofV HTy)
    (hbCanonT : env.HasType 0 [] bV .bool) :
    env.HasType 0 [] proofV (.app (.app rtype pV) bV) := by
  have hpCanonT := Reflection.defn₂.toDec_prop_hasType
    wf htoDec hpFnT hpT
  have htoDecFull := htoDec
  unfold Reflection.defn₂ at htoDec
  cases htoDec with
  | lam hpTyLocal hpTyLocalS hrest =>
    rename_i pTyLocalV restV
    cases hrest with
    | lam hbTyLocal hbTyLocalS hrest₂ =>
      rename_i bTyLocalV rest₂V
      cases hrest₂ with
      | lam hHTyLocal hHTyLocalS hbody =>
        rename_i HTyLocalV bodyV
        have hpTyCanon : TrExprS env [] [] q(Prop) (.sort .zero) :=
          .sort rfl
        have hpTyEq := TrExprS.unique (by trivial) hpTyLocalS hpTyCanon
        subst pTyLocalV
        have htoDecLams : TrExprS env [] [] Reflection.defn₂.toDec
            (.lam (.sort .zero) <| .lam bTyLocalV <|
              .lam HTyLocalV bodyV) := by
          unfold Reflection.defn₂
          exact .lam hpTyLocal hpTyLocalS <|
            .lam hbTyLocal hbTyLocalS <|
              .lam hHTyLocal hHTyLocalS hbody
        obtain ⟨h₁S, hβ₁⟩ := TrExprS.applyClosedLam
          wf htoDecLams hpS hpCanonT
        cases h₁S with
        | lam hbTyInst hbTyInstS hrest₂Inst =>
          have hbTyCanonS : TrExprS env [] [] q(Bool) .bool := by
            cases hbS.wf wf.ordered (Us := []) (Δ := []) trivial with
            | intro _ hbWF =>
              obtain ⟨_, hboolCi, _, hboolLen⟩ :=
                hbCanonT.isType wf trivial |>.choose_spec.const_inv wf trivial
              exact .const hboolCi rfl (by simpa using hboolLen)
          have hbTyEq := TrExprS.uniq (Us := []) wf
            (.refl wf (U := 0) (Δ := []) trivial) hbTyInstS hbTyCanonS
          have hbT' := hbCanonT.defeqU_r wf trivial hbTyEq.symm
          have h₂S := TrExprS.inst (env := env) (Us := []) (Δ := [])
            wf.ordered hbT' hrest₂Inst hbS
          obtain ⟨_, hrest₂WF⟩ := hrest₂Inst.wf wf.ordered
            (Us := []) (Δ := [(none, .vlam (bTyLocalV.inst pV))])
            ⟨trivial, nofun, hbTyInst⟩
          have hβ₂ : env.IsDefEqU 0 []
              (.app (.lam (bTyLocalV.inst pV)
                ((VExpr.lam HTyLocalV bodyV).inst pV 1)) bV)
              (((VExpr.lam HTyLocalV bodyV).inst pV 1).inst bV) :=
            ⟨_, .beta hrest₂WF.hasType.1 hbT'⟩
          have hβ₁b := hβ₁.app_same wf trivial hbFnT hbT
          have hβ₁₂ := hβ₁b.trans wf trivial hβ₂
          let HTyInstV := (HTyLocalV.inst pV 1).inst bV
          let bodyInstV := (bodyV.inst pV 2).inst bV 1
          cases h₂S with
          | lam hHTyInst hHTyInstS hbodyInst =>
            obtain ⟨bodyTy, hbodyWF⟩ := hbodyInst.wf wf.ordered
              (Us := []) (Δ := [(none, .vlam HTyInstV)])
              ⟨trivial, nofun, hHTyInst⟩
            have hcanonicalLamT : env.HasType 0 []
                (.lam HTyInstV bodyInstV)
                (.forallE HTyInstV bodyTy) :=
              .lam hHTyInst.choose_spec hbodyWF.hasType.1
            have hrightFnT :=
              (hβ₁₂.of_l wf trivial hHFnT).hasType.2
            have hcanonicalLamT' : env.HasType 0 []
                (((VExpr.lam HTyLocalV bodyV).inst pV 1).inst bV)
                (.forallE HTyInstV bodyTy) := by
              simpa [VExpr.inst, HTyInstV, bodyInstV] using hcanonicalLamT
            have hforallEq := hrightFnT.uniqU wf trivial hcanonicalLamT'
            obtain ⟨_, hdomainEq⟩ :=
              (hforallEq.forallE_inv wf trivial).1
            have hproofLocalT :=
              hproofT.defeqU_r wf trivial ⟨_, hdomainEq⟩
            unfold Reflection.defn₂ at hrtype
            cases hrtype with
            | lam hrpTy hrpTyS hrrest =>
              rename_i rpTyV rrestV
              have hrrestFull := hrrest
              cases hrrest with
              | lam hrbTy hrbTyS hrbodyTy =>
                rename_i rbTyV rbodyTyV
                have hrpTyEq := TrExprS.unique (by trivial) hrpTyS
                  (show TrExprS env [] [] q(Prop) (.sort .zero) from
                    .sort rfl)
                subst rpTyV
                have hrrestInst := TrExprS.inst (env := env)
                  (Us := []) (Δ := []) wf.ordered hpCanonT hrrestFull hpS
                obtain ⟨_, hrrestWF⟩ := hrrestFull.wf wf.ordered
                  (Us := []) (Δ := [(none, .vlam (.sort .zero))])
                  ⟨trivial, nofun, hrpTy⟩
                have hrβ₁ : env.IsDefEqU 0 []
                    (.app (.lam (.sort .zero) <| .lam rbTyV rbodyTyV) pV)
                    ((VExpr.lam rbTyV rbodyTyV).inst pV) :=
                  ⟨_, .beta hrrestWF.hasType.1 hpCanonT⟩
                cases hrrestInst with
                | lam hrbTyInst hrbTyInstS hrbodyTyInst =>
                  have hrbTyEq := TrExprS.uniq (Us := []) wf
                    (.refl wf (U := 0) (Δ := []) trivial)
                    hrbTyInstS hbTyCanonS
                  have hbRT := hbCanonT.defeqU_r wf trivial hrbTyEq.symm
                  obtain ⟨rbodyTySort, hrbodyTyWF⟩ :=
                    hrbodyTyInst.wf wf.ordered
                      (Us := [])
                      (Δ := [(none, .vlam (rbTyV.inst pV))])
                      ⟨trivial, nofun, hrbTyInst⟩
                  have hrLamT : env.HasType 0 []
                      (.lam (rbTyV.inst pV) (rbodyTyV.inst pV 1))
                      (.forallE (rbTyV.inst pV) rbodyTySort) :=
                    .lam hrbTyInst.choose_spec hrbodyTyWF.hasType.1
                  have hrAppT :=
                    (hrβ₁.of_r wf trivial hrLamT).hasType.1
                  have hrβ₁b := hrβ₁.app_same wf trivial hrAppT hbRT
                  have hrbodyInst := TrExprS.inst (env := env)
                    (Us := []) (Δ := []) wf.ordered hbRT
                    hrbodyTyInst hbS
                  have hrβ₂ : env.IsDefEqU 0 []
                      (.app (.lam (rbTyV.inst pV) (rbodyTyV.inst pV 1)) bV)
                      ((rbodyTyV.inst pV 1).inst bV) :=
                    ⟨_, .beta hrbodyTyWF.hasType.1 hbRT⟩
                  have hrβ := hrβ₁b.trans wf trivial hrβ₂
                  have htypeEq := TrExprS.uniq (Us := []) wf
                    (.refl wf (U := 0) (Δ := []) trivial)
                    hHTyInstS hrbodyInst
                  have hlocalToRType := htypeEq.trans wf trivial hrβ.symm
                  exact hproofLocalT.defeqU_r wf trivial hlocalToRType

/-- Instantiate the checked function equality between the reflected
implementation and `Nat.decEq` at two concrete numerals. -/
theorem Condition.natEq_dec_application_eq_reflected
    {env : VEnv} (wf : env.WF)
    (hctors : Lean4Lean.Environment.VEnv.HasNatBoolConstructors env)
    {reflectFn decFn : VExpr}
    (hreflect : TrExprS env [] [] Condition.natEqReflectedFn reflectFn)
    (heq : env.IsDefEqU 0 [] reflectFn decFn)
    (a b : Nat) :
    ∃ out,
      TrExprS env [] []
        (mkApp3 Reflection.defn₂.toDec
          (mkApp2 Condition.natEq.prop
            (.lit (.natVal a)) (.lit (.natVal b)))
          (mkApp2 q(Nat.beq)
            (.lit (.natVal a)) (.lit (.natVal b)))
          (mkApp2 Condition.natEqReflectProof
            (.lit (.natVal a)) (.lit (.natVal b)))) out ∧
      env.IsDefEqU 0 []
        (.app (.app decFn (.natLit a)) (.natLit b)) out := by
  have hreflectFull := hreflect
  unfold Condition.natEqReflectedFn at hreflect
  cases hreflect with
  | lam hnatTy₁ hnatS₁ hinnerS =>
    cases hinnerS with
    | lam hnatTy₂ hnatS₂ hbodyS =>
      rename_i natTy₁ natTy₂ body
      have ⟨haS, haT⟩ := hctors.natLitS a (Us := []) (Δ := [])
      have ⟨hbS, hbT⟩ := hctors.natLitS b (Us := []) (Δ := [])
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
          (.lam0 q(Nat) <| mkApp3 Reflection.defn₂.toDec
            (mkApp2 Condition.natEq.prop (.bvar 1) (.bvar 0))
            (mkApp2 q(Nat.beq) (.bvar 1) (.bvar 0))
            (mkApp2 Condition.natEqReflectProof (.bvar 1) (.bvar 0)))
          (.lam natTy₂ body) from .lam hnatTy₂ hnatS₂ hbodyS) haS
      cases hinnerInst with
      | lam hnatTy₂' hnatS₂' hbodyInstS =>
        have hnatEq₂ := TrExprS.uniq (Us := []) wf hctx hnatS₂'
          (hnatCanon [])
        have hbT' := hbT.defeqU_r wf trivial hnatEq₂.symm
        obtain ⟨out, houtS, hreflectEval⟩ :=
          Condition.natEqReflectedFn.instantiate wf hctors hreflectFull a b
        obtain ⟨bodyTy, hbodyWF⟩ := hbodyS.wf wf.ordered
          (Us := [])
          (Δ := [(none, .vlam natTy₂), (none, .vlam natTy₁)])
          ⟨⟨trivial, nofun, hnatTy₁⟩, nofun, hnatTy₂⟩
        obtain ⟨_, hnatSort₁⟩ := hnatTy₁
        obtain ⟨_, hnatSort₂⟩ := hnatTy₂
        have hfnT : env.HasType 0 []
            (.lam natTy₁ <| .lam natTy₂ body)
            (.forallE natTy₁ <| .forallE natTy₂ bodyTy) :=
          .lam hnatSort₁ (.lam hnatSort₂ hbodyWF.hasType.1)
        have h₁ := heq.app_same wf trivial hfnT haT'
        have hprefixT := VEnv.HasType.app hfnT haT'
        have h₂ := h₁.app_same wf trivial hprefixT hbT'
        exact ⟨out, houtS,
          h₂.symm.trans wf trivial hreflectEval⟩

/-- Rewrite an instantiated equality-decision function application so its
`ite` uses the reflected `Nat.beq`-based decision produced by the checked
condition equation. -/
theorem Condition.natEqDecideFn.to_reflected_ite
    {env : VEnv} (wf : env.WF)
    (hctors : Lean4Lean.Environment.VEnv.HasNatBoolConstructors env)
    {decide reflectFn decFn : VExpr}
    (hdecide : TrExprS env [] [] Condition.natEqDecideFn decide)
    (hreflect : TrExprS env [] [] Condition.natEqReflectedFn reflectFn)
    (hdecFn : TrExprS env [] [] Condition.natEq.dec decFn)
    (heq : env.IsDefEqU 0 [] reflectFn decFn)
    (a b : Nat) :
    ∃ iteV propV reflectedV,
      TrExprS env [] [] q(@_root_.ite.{1}) iteV ∧
      TrExprS env [] []
        (mkApp2 Condition.natEq.prop
          (.lit (.natVal a)) (.lit (.natVal b))) propV ∧
      TrExprS env [] []
        (mkApp3 Reflection.defn₂.toDec
          (mkApp2 Condition.natEq.prop
            (.lit (.natVal a)) (.lit (.natVal b)))
          (mkApp2 q(Nat.beq)
            (.lit (.natVal a)) (.lit (.natVal b)))
          (mkApp2 Condition.natEqReflectProof
            (.lit (.natVal a)) (.lit (.natVal b)))) reflectedV ∧
      TrExprS env [] []
        (mkApp (mkApp (mkApp (mkApp (mkApp q(@_root_.ite.{1}) q(Bool))
          (mkApp2 Condition.natEq.prop
            (.lit (.natVal a)) (.lit (.natVal b))))
          (mkApp3 Reflection.defn₂.toDec
            (mkApp2 Condition.natEq.prop
              (.lit (.natVal a)) (.lit (.natVal b)))
            (mkApp2 q(Nat.beq)
              (.lit (.natVal a)) (.lit (.natVal b)))
            (mkApp2 Condition.natEqReflectProof
              (.lit (.natVal a)) (.lit (.natVal b)))))
          q(true)) q(false))
        (.app (.app (.app (.app (.app iteV .bool) propV) reflectedV)
          .boolTrue) .boolFalse) ∧
      env.IsDefEqU 0 []
        (.app (.app decide (.natLit a)) (.natLit b))
        (.app (.app (.app (.app (.app iteV .bool) propV) reflectedV)
          .boolTrue) .boolFalse) := by
  obtain ⟨out, hcallS, hdecideEval⟩ :=
    Condition.natEqDecideFn.instantiate wf hctors hdecide a b
  obtain ⟨iteV, propV, decV, rfl, hiteS, hpropS, hdecVS⟩ :=
    Condition.natEqDecide_call_shape hcallS
  have hlocalClosed := Condition.natEqDec_application_eq_closed
    wf hctors hdecFn hdecVS
  obtain ⟨reflectedV, hreflectedS, hclosedReflected⟩ :=
    Condition.natEq_dec_application_eq_reflected
      wf hctors hreflect heq a b
  have hlocalReflected :=
    hlocalClosed.trans wf trivial hclosedReflected
  have hcallExpanded : TrExprS env [] []
      (mkApp (mkApp (mkApp (mkApp (mkApp q(@_root_.ite.{1}) q(Bool))
        (mkApp2 Condition.natEq.prop
          (.lit (.natVal a)) (.lit (.natVal b))))
        (mkApp2 Condition.natEq.dec
          (.lit (.natVal a)) (.lit (.natVal b)))) q(true)) q(false))
      (.app (.app (.app (.app (.app iteV .bool) propV) decV)
        .boolTrue) .boolFalse) := by
    simpa [Condition.decide, Condition.ite] using hcallS
  have hreflectedCall := TrExprS.replaceITECondition wf hcallExpanded
    hreflectedS hlocalReflected
  obtain ⟨_, houtWF⟩ := hcallS.wf wf.ordered
    (Us := []) (Δ := []) trivial
  have hreplace := VEnv.replaceITECondition wf houtWF.hasType.1
    hlocalReflected
  exact ⟨iteV, propV, reflectedV, hiteS, hpropS, hreflectedS,
    hreflectedCall,
    hdecideEval.trans wf trivial hreplace⟩

/-- A translated concrete `Nat.beq` call agrees with the Boolean value
provided by the primitive reflection invariant. -/
theorem Condition.natBEq_application_eval
    {env : VEnv} (wf : env.WF) (hprim : env.HasPrimitives)
    (hctors : Lean4Lean.Environment.VEnv.HasNatBoolConstructors env)
    (hbeqC : env.contains ``Nat.beq)
    {a b : Nat} {beqV : VExpr}
    (hbeqS : TrExprS env [] []
      (mkApp2 q(Nat.beq) (.lit (.natVal a)) (.lit (.natVal b))) beqV) :
    env.IsDefEqU 0 [] beqV (.boolLit (a == b)) := by
  have ⟨haS, haT⟩ := hctors.natLitS a (Us := []) (Δ := [])
  have ⟨hbS, hbT⟩ := hctors.natLitS b (Us := []) (Δ := [])
  have ⟨hbeqT, hbeqEval⟩ := hprim.natBEq hbeqC
  obtain ⟨ci, hci, _, hlen⟩ := (hbeqT 0 []).const_inv wf trivial
  have hfnS : TrExprS env [] [] q(Nat.beq) (.const ``Nat.beq []) :=
    .const hci rfl hlen
  have hinnerS : TrExprS env [] []
      (mkApp q(Nat.beq) (.lit (.natVal a)))
      (.app (.const ``Nat.beq []) (.natLit a)) :=
    .app (hbeqT 0 []) haT hfnS haS
  have hcanonS : TrExprS env [] []
      (mkApp2 q(Nat.beq) (.lit (.natVal a)) (.lit (.natVal b)))
      (.app (.app (.const ``Nat.beq []) (.natLit a)) (.natLit b)) :=
    .app (.app (hbeqT 0 []) haT) hbT hinnerS hbS
  have hlocalEq := TrExprS.uniq (Us := []) wf
    (.refl wf (U := 0) (Δ := []) trivial) hbeqS hcanonS
  have hab : Nat.beq a b = (a == b) := by
    apply Bool.eq_iff_iff.2
    simp [Nat.beq_eq]
  rw [← hab]
  exact hlocalEq.trans wf trivial (hbeqEval a b)

/-- The checked equality-condition certificate, together with the primitive
`Nat.beq` semantics, makes the closed decision function compute the expected
Boolean equality test. -/
theorem Condition.natEqDecideFn.reflects
    {env : VEnv} (wf : env.WF) (hprim : env.HasPrimitives)
    (hctors : Lean4Lean.Environment.VEnv.HasNatBoolConstructors env)
    (hbeqC : env.contains ``Nat.beq)
    (hcert : Lean4Lean.Environment.VEnv.ReflectionITECertificate env)
    {rtype rite decide reflectFn decFn : VExpr}
    (hrtype : TrExprS env [] [] Reflection.defn₂.type rtype)
    (hrite : TrExprS env [] [] Reflection.defn₂.ite rite)
    (hrtypeT : env.HasType 0 [] rtype
      (.forallE (.sort .zero) <| .forallE .bool (.sort .zero)))
    (hdecide : TrExprS env [] [] Condition.natEqDecideFn decide)
    (hdecideT : env.HasType 0 [] decide
      (.forallE .nat <| .forallE .nat .bool))
    (hreflect : TrExprS env [] [] Condition.natEqReflectedFn reflectFn)
    (hdecFn : TrExprS env [] [] Condition.natEq.dec decFn)
    (heq : env.IsDefEqU 0 [] reflectFn decFn) :
    Lean4Lean.Environment.VEnv.ReflectsNatEqDecide env decide := by
  have hboolT := hprim.bool_hasType hctors.bool
  refine ⟨hdecideT, fun a b => ?_⟩
  obtain ⟨iteV, propV, reflectedV, hrootIteS, hpropS,
      hreflectedS, hreflectedCallS, hcallEq⟩ :=
    Condition.natEqDecideFn.to_reflected_ite
      wf hctors hdecide hreflect hdecFn heq a b
  rcases Condition.natEqReflected_call_typed_shape hreflectedS with
    ⟨toDecV, propV', beqV, proofV, pTy, pRest, bTy, bRest,
      HTy, HRest, hreflectedShape, htoDecS, hpropS', hbeqS,
      hproofS, hpFnT, hpT, hbFnT, hbT, hHFnT, hproofT⟩
  cases hreflectedShape
  have hctx : VLCtx.IsDefEq env 0 [] [] := .refl wf trivial
  have hpropEq := TrExprS.unique
    (by simp [Condition.natEq, TrExprS.IsUnique]) hpropS' hpropS
  subst propV'
  have hbeqEq := Condition.natBEq_application_eval
    wf hprim hctors hbeqC hbeqS
  have hboolLitT := hctors.boolLitS (a == b) (Us := []) (Δ := []) |>.2
  have hbeqCanonT := (hbeqEq.of_r wf trivial hboolLitT).hasType.1
  have hpropT := Reflection.defn₂.toDec_prop_hasType
    wf htoDecS hpFnT hpT
  have hproofRTypeT := Reflection.defn₂.toDec_proof_hasType
    wf hrtype htoDecS hpropS hbeqS hpFnT hpT hbFnT hbT
      hHFnT hproofT hbeqCanonT
  have hrtypePropT : env.HasType 0 [] (.app rtype propV)
      (.forallE .bool (.sort .zero)) := .app hrtypeT hpropT
  have hRTypeBeqEq := hbeqEq.app_arg wf trivial hrtypePropT hbeqCanonT
  have hproofLitT := hproofRTypeT.defeqU_r wf trivial hRTypeBeqEq
  have hHTyS : TrExprS env [] []
      (mkApp2 Reflection.defn₂.type
        (mkApp2 Condition.natEq.prop
          (.lit (.natVal a)) (.lit (.natVal b)))
        (mkApp2 q(Nat.beq)
          (.lit (.natVal a)) (.lit (.natVal b))))
      (.app (.app rtype propV) beqV) := by
    exact .app hrtypePropT hbeqCanonT
      (.app hrtypeT hpropT hrtype hpropS) hbeqS
  have hpTyS : TrExprS env [] [] q(Prop) (.sort .zero) := .sort rfl
  have hαTyS : TrExprS env [] [] q(Type) (.sort (.succ .zero)) := .sort rfl
  have htrueT := hctors.boolTrueS (Us := []) (Δ := []) |>.2
  have hfalseT := hctors.boolFalseS (Us := []) (Δ := []) |>.2
  have hcertCanon := hcert.canonical wf hrtype hrite
  obtain ⟨_, hriteWF⟩ := hrite.wf wf.ordered
    (Us := []) (Δ := []) trivial
  have hriteClosed :=
    (hriteWF.hasType.1.closedN' wf.ordered.closed trivial).1
  have hrtypeClosed :=
    (hrtypeT.closedN' wf.ordered.closed trivial).1
  cases hreflectedCallS with
  | app hthenAppT hfalseArgT hfn hfalseS =>
    cases hfn with
    | app hprefixT htrueArgT hprefixApp htrueS =>
      cases hprefixApp with
      | app hbeforeDecT hreflectedArgT hprefix hreflectedS' =>
        cases hprefix with
        | app hrootBoolT hpropArgT hprefix hpropS'' =>
          cases hprefix with
          | app hrootIteT hboolArgT hrootIteS' hboolS =>
            have hreflectedPrefixS : TrExprS env [] []
                (mkApp3 q(@_root_.ite.{1}) q(Bool)
                  (mkApp2 Condition.natEq.prop
                    (.lit (.natVal a)) (.lit (.natVal b)))
                  (mkApp3 Reflection.defn₂.toDec
                    (mkApp2 Condition.natEq.prop
                      (.lit (.natVal a)) (.lit (.natVal b)))
                    (mkApp2 q(Nat.beq)
                      (.lit (.natVal a)) (.lit (.natVal b)))
                    (mkApp2 Condition.natEqReflectProof
                      (.lit (.natVal a)) (.lit (.natVal b)))))
                (.app (.app (.app iteV .bool) propV)
                  (.app (.app (.app toDecV propV) beqV) proofV)) :=
              .app hbeforeDecT hreflectedArgT
                (.app hrootBoolT hpropArgT
                  (.app hrootIteT hboolArgT hrootIteS' hboolS)
                  hpropS'') hreflectedS'
            have hprefixBeta := Reflection.defn₂.ite_apply4 wf
              hrite hpTyS hboolS hHTyS hαTyS
              hpropS hbeqS hproofS hboolS
              hpropT hbeqCanonT hproofRTypeT hboolT
              hreflectedPrefixS
            have hleftPrefixT :=
              (hprefixBeta.of_r wf trivial hprefixT).hasType.1
            have hbetaTrue := hprefixBeta.app_same wf trivial
              hleftPrefixT htrueArgT
            have hleftTrueT :=
              (hbetaTrue.of_r wf trivial hthenAppT).hasType.1
            have hbetaBranches := hbetaTrue.app_same wf trivial
              hleftTrueT hfalseArgT
            have hrawFullT := VEnv.HasType.app hthenAppT hfalseArgT
            have hselectorBeqT :=
              (hbetaBranches.of_r wf trivial hrawFullT).hasType.1
            obtain ⟨_, _, hbeforeFalseT, hfalseT'⟩ :=
              hselectorBeqT.app_inv wf trivial
            obtain ⟨_, _, hbeforeTrueT, htrueT'⟩ :=
              hbeforeFalseT.app_inv wf trivial
            obtain ⟨_, _, hbeforeBoolT, hboolT'⟩ :=
              hbeforeTrueT.app_inv wf trivial
            obtain ⟨_, _, hbeforeProofT, hproofT'⟩ :=
              hbeforeBoolT.app_inv wf trivial
            obtain ⟨_, _, hritePropT, hbeqT'⟩ :=
              hbeforeProofT.app_inv wf trivial
            have hcondEq₀ := hbeqEq.app_arg wf trivial hritePropT hbeqT'
            have hcondEq₁ := hcondEq₀.app_same wf trivial
              hbeforeProofT hproofT'
            have hcondEq₂ := hcondEq₁.app_same wf trivial
              hbeforeBoolT hboolT'
            have hcondEq₃ := hcondEq₂.app_same wf trivial
              hbeforeTrueT htrueT'
            have hselectorCondEq := hcondEq₃.app_same wf trivial
              hbeforeFalseT hfalseT'
            have hselector : env.IsDefEqU 0 []
                (.app (.app (.app
                  (.app (.app (.app rite propV) (.boolLit (a == b))) proofV)
                    .bool) .boolTrue) .boolFalse)
                (.boolLit (a == b)) := by
              cases hab : (a == b) with
              | false =>
                simpa [hab] using VEnv.reflectionITE_false wf
                  hrtypeClosed hrtypeClosed hriteClosed hcertCanon.2
                  hpropT (by simpa [hab] using hproofLitT)
                  (by simpa [hab] using hproofLitT)
                  hboolT htrueT hfalseT
              | true =>
                simpa [hab] using VEnv.reflectionITE_true wf
                  hrtypeClosed hrtypeClosed hriteClosed hcertCanon.1
                  hpropT (by simpa [hab] using hproofLitT)
                  (by simpa [hab] using hproofLitT)
                  hboolT htrueT hfalseT
            exact hcallEq.trans wf trivial <|
              hbetaBranches.symm.trans wf trivial <|
                hselectorCondEq.trans wf trivial hselector

/-- Package the typing and equality facts exported by the condition checker
as the semantic equality-decision interface consumed by bitwise reflection. -/
theorem Condition.natEq.check.WF.reflects
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {fail : ∀ {α}, TypeChecker.M α}
    {rtype rite decide reflectFn decFn : VExpr}
    (hlparams : c.lparams = []) (hvlctx : c.vlctx = [])
    (hbool : c.venv.contains ``Bool) (hnat : c.venv.contains ``Nat)
    (hbeqC : c.venv.contains ``Nat.beq)
    (hrtype : c.TrExprS Reflection.defn₂.type rtype)
    (hrite : c.TrExprS Reflection.defn₂.ite rite)
    (hdecide : c.TrExprS Condition.natEqDecideFn decide)
    (hreflect : c.TrExprS Condition.natEqReflectedFn reflectFn)
    (hdecFn : c.TrExprS Condition.natEq.dec decFn)
    (hcheck : TypeChecker.M.WF c s
      (Condition.natEq.check fail (ite := true)) fun _ _ =>
        VEnv.ReflectionITECertificate c.venv ∧
        c.HasType rtype
          (.forallE (.sort .zero) <| .forallE .bool (.sort .zero)) ∧
        c.HasType decide (.forallE .nat <| .forallE .nat .bool) ∧
        c.IsDefEqU reflectFn decFn) :
    TypeChecker.M.WF c s (Condition.natEq.check fail (ite := true))
      fun _ _ =>
        VEnv.ReflectionITECertificate c.venv ∧
        VEnv.ReflectsNatEqDecide c.venv decide := by
  refine hcheck.mono fun _ _ _ ⟨hcert, hrtypeT, hdecideT, heq⟩ => ?_
  change TrExprS c.venv c.lparams c.vlctx _ _ at hrtype hrite hdecide hreflect hdecFn
  change c.venv.HasType c.lparams.length c.vlctx.toCtx _ _ at hrtypeT hdecideT
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx _ _ at heq
  rw [hlparams, hvlctx] at hrtype hrite hdecide hreflect hdecFn hrtypeT hdecideT heq
  have hctors := VEnv.HasNatBoolConstructors.of_primitives
    c.hasPrimitives hbool hnat
  exact ⟨hcert, Condition.natEqDecideFn.reflects c.Ewf
    c.hasPrimitives hctors hbeqC hcert hrtype hrite hrtypeT
    hdecide hdecideT hreflect hdecFn heq⟩

theorem Condition.natEq.check.WF.semantic
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {fail : ∀ {α}, TypeChecker.M α}
    {rtype rite decide reflectFn decFn beq : VExpr}
    (hlparams : c.lparams = []) (hvlctx : c.vlctx = [])
    (hbool : c.venv.contains ``Bool) (hnat : c.venv.contains ``Nat)
    (hbeqC : c.venv.contains ``Nat.beq)
    (hdec : c.TrExprS Condition.natEq.dec decFn)
    (hprop : c.TrExprS Condition.natEq.prop prop')
    (hpropTy : c.TrExprS q(Nat → Nat → Prop) propTy')
    (hrtype : c.TrExprS Reflection.defn₂.type rtype)
    (hrtypeUnique : TrExprS.IsUnique Reflection.defn₂.type)
    (hrtypeCanon : c.TrExprS q(Prop → Bool → Prop)
      (.forallE (.sort .zero) <| .forallE .bool (.sort .zero)))
    (hite : c.TrExprS Reflection.defn₂.ite rite)
    (hiteUnique : TrExprS.IsUnique Reflection.defn₂.ite)
    (hiteTy : c.TrExprS (.arrow q(Prop) <| .arrow q(Bool) <|
      .arrow (mkApp2 Reflection.defn₂.type (.bvar 1) (.bvar 0))
        q(∀ α : Type, α → α → α)) iteTy')
    (htrueL : c.TrExprS
      (.lam0 q(Prop) <|
        .lam0 (mkApp2 Reflection.defn₂.type (.bvar 0) q(true)) <|
          mkApp3 Reflection.defn₂.ite (.bvar 1) q(true) (.bvar 0)) trueL')
    (htrueR : c.TrExprS
      (.lam0 q(Prop) <|
        .lam0 (mkApp2 Reflection.defn₂.type (.bvar 0) q(true)) <|
          .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <|
            .bvar 1) trueR')
    (hfalseL : c.TrExprS
      (.lam0 q(Prop) <|
        .lam0 (mkApp2 Reflection.defn₂.type (.bvar 0) q(false)) <|
          mkApp3 Reflection.defn₂.ite (.bvar 1) q(false) (.bvar 0)) falseL')
    (hfalseR : c.TrExprS
      (.lam0 q(Prop) <|
        .lam0 (mkApp2 Reflection.defn₂.type (.bvar 0) q(false)) <|
          .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <|
            .bvar 0) falseR')
    (hreflect : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <| mkApp3 Reflection.defn₂.toDec
        (mkApp2 Condition.natEq.prop (.bvar 1) (.bvar 0))
        (mkApp2 q(Nat.beq) (.bvar 1) (.bvar 0))
        (mkApp2
          q(fun n m {q : Prop} (H : _ → _ → q) =>
            H (@Nat.eq_of_beq_eq_true n m) (@Nat.ne_of_beq_eq_false n m))
          (.bvar 1) (.bvar 0))) reflectFn)
    (hdecide : c.TrExprS Condition.natEqDecideFn decide)
    (hdecideTy : c.TrExprS q(Nat → Nat → Bool)
      (.forallE .nat <| .forallE .nat .bool))
    (hasBool : c.TrExprS q(Nat.beq) beq)
    (hasBoolTy : c.TrExprS q(Nat → Nat → Bool)
      (.forallE .nat <| .forallE .nat .bool))
    (hproof : c.TrExprS
      q(fun n m {q : Prop} (H : _ → _ → q) =>
        H (@Nat.eq_of_beq_eq_true n m) (@Nat.ne_of_beq_eq_false n m)) proof')
    (hfail : ∀ {α} {s'}, TypeChecker.M.WF c s'
      (fail : TypeChecker.M α) fun _ _ => False) :
    TypeChecker.M.WF c s (Condition.natEq.check fail (ite := true))
      fun _ _ => VEnv.ReflectionITECertificate c.venv ∧
        VEnv.ReflectsNatEqDecide c.venv decide := by
  apply Condition.natEq.check.WF.reflects hlparams hvlctx hbool hnat
    hbeqC hrtype hite hdecide hreflect hdec
  refine (Condition.natEq.check.WF hlparams hvlctx hdec hprop hpropTy
    hrtype hrtypeUnique hrtypeCanon hite hiteUnique hiteTy htrueL htrueR
    hfalseL hfalseR hreflect hdecide hdecideTy hasBool hasBoolTy hproof
    hfail).mono ?_
  rintro _ _ _ ⟨hcert, hrtypeT, _, _, hdecideT, _, _, heq⟩
  exact ⟨hcert, hrtypeT, hdecideT, heq⟩

/-- Evidence-retaining wrapper for the Nat-equality selector used by the
`Nat.bitwise` primitive checker. -/
theorem Condition.natEq.checkForPrimitive.WF.semantic
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {fail : ∀ {α}, TypeChecker.M α}
    (hlparams : c.lparams = []) (hvlctx : c.vlctx = [])
    (hbool : c.venv.contains ``Bool) (hnat : c.venv.contains ``Nat)
    (hbeqC : c.venv.contains ``Nat.beq)
    (hfail : ∀ {α} {s'}, TypeChecker.M.WF c s'
      (fail : TypeChecker.M α) fun _ _ => False) :
    TypeChecker.M.WF c s (Condition.natEq.checkForPrimitive fail)
      fun _ _ => ∃ decide,
        c.TrExprS Condition.natEqDecideFn decide ∧
        VEnv.ReflectionITECertificate c.venv ∧
        VEnv.ReflectsNatEqDecide c.venv decide := by
  unfold Condition.natEq.checkForPrimitive
  have hevidence : ∀ e ∈ Condition.natEqEvidenceExpressions,
      e.FVarsIn (· ∈ c.vlctx.fvars) := by
    intro e he
    have hclosed : ∀ e ∈ Condition.natEqEvidenceExpressions,
        e.hasFVar = false ∧ e.hasMVar = false := by
      simp [Condition.natEqEvidenceExpressions, Condition.natEq,
        Condition.natEqReflectProof, Condition.natEqReflectedFn,
        Condition.natEqDecideFn, Reflection.defn₂, Reflection.ite]
      native_decide
    exact Expr.closed_fvarsIn (hclosed e he).1 (hclosed e he).2
  refine (checkTypeList.WF (es := Condition.natEqEvidenceExpressions)
    hevidence).bind fun _ s' _ htypes => ?_
  let r := Reflection.defn₂
  let iteTy : Expr := .arrow q(Prop) <| .arrow q(Bool) <|
    .arrow (mkApp2 r.type (.bvar 1) (.bvar 0))
      q(∀ α : Type, α → α → α)
  let trueL : Expr := .lam0 q(Prop) <|
    .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
      mkApp3 r.ite (.bvar 1) q(true) (.bvar 0)
  let trueR : Expr := .lam0 q(Prop) <|
    .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
      .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 1
  let falseL : Expr := .lam0 q(Prop) <|
    .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
      mkApp3 r.ite (.bvar 1) q(false) (.bvar 0)
  let falseR : Expr := .lam0 q(Prop) <|
    .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
      .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 0
  have mem (e) (h : e ∈ Condition.natEqEvidenceExpressions) := htypes e h
  obtain ⟨dec', _, hdec, _⟩ := mem Condition.natEq.dec
    (by simp [Condition.natEqEvidenceExpressions])
  obtain ⟨prop', _, hprop, _⟩ := mem Condition.natEq.prop
    (by simp [Condition.natEqEvidenceExpressions])
  obtain ⟨propTy', _, hpropTy, _⟩ := mem q(Nat → Nat → Prop)
    (by simp [Condition.natEqEvidenceExpressions])
  obtain ⟨rtype', _, hrtype, _⟩ := mem r.type
    (by simp [Condition.natEqEvidenceExpressions, r])
  obtain ⟨_, _, hrtypeCanon, _⟩ := mem q(Prop → Bool → Prop)
    (by simp [Condition.natEqEvidenceExpressions])
  obtain ⟨ite', _, hite, _⟩ := mem r.ite
    (by simp [Condition.natEqEvidenceExpressions, r])
  obtain ⟨iteTy', _, hiteTy, _⟩ := mem iteTy
    (by simp [Condition.natEqEvidenceExpressions, iteTy, r])
  obtain ⟨trueL', _, htrueL, _⟩ := mem trueL
    (by simp [Condition.natEqEvidenceExpressions, trueL, r])
  obtain ⟨trueR', _, htrueR, _⟩ := mem trueR
    (by simp [Condition.natEqEvidenceExpressions, trueR, r])
  obtain ⟨falseL', _, hfalseL, _⟩ := mem falseL
    (by simp [Condition.natEqEvidenceExpressions, falseL, r])
  obtain ⟨falseR', _, hfalseR, _⟩ := mem falseR
    (by simp [Condition.natEqEvidenceExpressions, falseR, r])
  obtain ⟨reflectFn', _, hreflect, _⟩ :=
    mem Condition.natEqReflectedFn
      (by simp [Condition.natEqEvidenceExpressions])
  obtain ⟨decide', _, hdecide, _⟩ := mem Condition.natEqDecideFn
    (by simp [Condition.natEqEvidenceExpressions])
  obtain ⟨_, _, hdecideTy, _⟩ := mem q(Nat → Nat → Bool)
    (by simp [Condition.natEqEvidenceExpressions])
  obtain ⟨beq', _, hbeq, _⟩ := mem q(Nat.beq)
    (by simp [Condition.natEqEvidenceExpressions])
  obtain ⟨proof', _, hproof, _⟩ := mem Condition.natEqReflectProof
    (by simp [Condition.natEqEvidenceExpressions])
  have hrtypeUnique : TrExprS.IsUnique Reflection.defn₂.type := by
    simp [TrExprS.IsUnique, Reflection.defn₂, Expr.lam0, Expr.arrow,
      mkApp5, mkApp4, mkApp3, mkApp2, mkApp]
  have hiteUnique : TrExprS.IsUnique Reflection.defn₂.ite := by
    simp [TrExprS.IsUnique, Reflection.defn₂, Reflection.ite,
      Expr.lam0, Expr.arrow, mkApp5, mkApp4, mkApp3, mkApp2, mkApp]
  have hrtypeCanon' : c.TrExprS q(Prop → Bool → Prop)
      (.forallE (.sort .zero) <| .forallE .bool (.sort .zero)) := by
    change TrExprS c.venv c.lparams c.vlctx _ _
    rw [hvlctx]
    exact TrExprS.propBoolPropType_of_contains
      c.hasPrimitives hbool c.lparams []
  cases hrtypeCanon.unique (by simp [TrExprS.IsUnique]) hrtypeCanon'
  have hdecideTy' : c.TrExprS q(Nat → Nat → Bool)
      (.forallE .nat <| .forallE .nat .bool) := by
    change TrExprS c.venv c.lparams c.vlctx _ _
    rw [hvlctx]
    exact TrExprS.natBinaryBoolType_of_contains
      c.hasPrimitives hnat hbool c.lparams []
  cases hdecideTy.unique (by simp [TrExprS.IsUnique]) hdecideTy'
  have hraw := Condition.natEq.check.WF.semantic
    (s := s') (fail := fail) hlparams hvlctx hbool hnat hbeqC
    hdec hprop hpropTy hrtype hrtypeUnique hrtypeCanon
    hite hiteUnique hiteTy htrueL htrueR hfalseL hfalseR
    hreflect hdecide hdecideTy hbeq hdecideTy hproof hfail
  exact hraw.mono fun _ _ _ h => ⟨decide', hdecide, h.1, h.2⟩

/-- Evidence-retaining wrapper for the Boolean Nat selector used by the
`Nat.bitwise` primitive checker. -/
theorem Condition.bool.checkForPrimitive.WF.semantic
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {fail : ∀ {α}, TypeChecker.M α}
    (hlparams : c.lparams = []) (hvlctx : c.vlctx = [])
    (hbool : c.venv.contains ``Bool) (hnat : c.venv.contains ``Nat)
    (hfail : ∀ {α} {s'}, TypeChecker.M.WF c s'
      (fail : TypeChecker.M α) fun _ _ => False) :
    TypeChecker.M.WF c s (Condition.bool.checkForPrimitive fail)
      fun _ _ => ∃ ite,
        c.TrExprS Condition.bool.boolNatITE ite ∧
        c.venv.ReflectsBoolNatITE ite := by
  unfold Condition.bool.checkForPrimitive
  have hevidence : ∀ e ∈ Condition.boolEvidenceExpressions,
      e.FVarsIn (· ∈ c.vlctx.fvars) := by
    intro e he
    have hclosed : ∀ e ∈ Condition.boolEvidenceExpressions,
        e.hasFVar = false ∧ e.hasMVar = false := by
      simp [Condition.boolEvidenceExpressions, Condition.bool,
        Condition.boolNatITE]
      native_decide
    exact Expr.closed_fvarsIn (hclosed e he).1 (hclosed e he).2
  refine (checkTypeList.WF (es := Condition.boolEvidenceExpressions)
    hevidence).bind fun _ s' _ htypes => ?_
  let ite := Condition.bool.boolNatITE
  let tr : Expr := .lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 1
  let fr : Expr := .lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 0
  have mem (e) (h : e ∈ Condition.boolEvidenceExpressions) := htypes e h
  obtain ⟨dec', _, hdec, _⟩ := mem Condition.bool.dec
    (by simp [Condition.boolEvidenceExpressions])
  obtain ⟨prop', _, hprop, _⟩ := mem Condition.bool.prop
    (by simp [Condition.boolEvidenceExpressions])
  obtain ⟨propTy', _, hpropTy, _⟩ := mem q(Bool → Prop)
    (by simp [Condition.boolEvidenceExpressions])
  obtain ⟨ite', _, hite, _⟩ := mem ite
    (by simp [Condition.boolEvidenceExpressions, ite])
  obtain ⟨_, _, hiteTy, _⟩ := mem q(Bool → Nat → Nat → Nat)
    (by simp [Condition.boolEvidenceExpressions])
  obtain ⟨tl', _, htl, _⟩ := mem (mkApp ite q(true))
    (by simp [Condition.boolEvidenceExpressions, ite])
  obtain ⟨tr', _, htr, _⟩ := mem tr
    (by simp [Condition.boolEvidenceExpressions, tr])
  obtain ⟨fl', _, hfl, _⟩ := mem (mkApp ite q(false))
    (by simp [Condition.boolEvidenceExpressions, ite])
  obtain ⟨fr', _, hfr, _⟩ := mem fr
    (by simp [Condition.boolEvidenceExpressions, fr])
  have hiteUnique : TrExprS.IsUnique Condition.bool.boolNatITE := by
    simp [TrExprS.IsUnique, Condition.bool, Condition.boolNatITE,
      Expr.lam0, mkApp3, mkApp2, mkApp]
  have hiteTy' : c.TrExprS q(Bool → Nat → Nat → Nat)
      (.forallE .bool <| .forallE .nat <| .forallE .nat .nat) := by
    change TrExprS c.venv c.lparams c.vlctx _ _
    rw [hvlctx]
    exact TrExprS.boolNatBinaryType_of_contains
      c.hasPrimitives hbool hnat c.lparams []
  cases hiteTy.unique (by simp [TrExprS.IsUnique]) hiteTy'
  have hraw := Condition.bool.check.WF.semantic
    (s := s') (fail := fail) hlparams hvlctx hbool hnat
    hdec hprop hpropTy hite hiteUnique hiteTy
    htl htr hfl hfr hfail
  exact hraw.mono fun _ _ _ h => ⟨ite', hite, h⟩

abbrev NatBitwisePrimitiveEvidence
    (c : TypeChecker.VContext) (src : DefinitionVal) (ty' : VExpr) : Prop :=
  ∃ cert : NatBitwiseFixCertificate, ∃ ite decide,
    src.levelParams = [] ∧
    c.venv.contains ``Bool ∧ c.venv.contains ``Nat ∧
    c.venv.contains ``Nat.beq ∧ c.venv.contains ``Nat.add ∧
    c.venv.contains ``Nat.mod ∧ c.venv.contains ``Nat.div ∧
    c.venv.IsDefEqU c.lparams.length [] ty'
      (.forallE (.forallE .bool <| .forallE .bool .bool) <|
        .forallE .nat <| .forallE .nat .nat) ∧
    cert.NormalizedValid c src.value ∧
    c.TrExprS Condition.bool.boolNatITE ite ∧
    c.venv.ReflectsBoolNatITE ite ∧
    c.TrExprS Condition.natEqDecideFn decide ∧
    VEnv.ReflectsNatEqDecide c.venv decide

theorem checkPrimitiveDef.natBitwise.WF_typed
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {src : DefinitionVal} {ty' : VExpr}
    (hname : src.name = ``Nat.bitwise)
    (hcparams : c.lparams = src.levelParams) (hvlctx : c.vlctx = [])
    (hty : c.TrExprS src.type ty') :
    TypeChecker.M.WF c s (checkPrimitiveDef src) fun b _ => b →
      NatBitwisePrimitiveEvidence c src ty' := by
  have hcore := checkPrimitiveDef.natBitwise.WF_typedCore
    (c := c) (s := s) (v := src) (ty' := ty')
    hname hcparams hvlctx hty
    (fun hl hb hn heq hfail =>
      Condition.natEq.checkForPrimitive.WF.semantic
        hl hvlctx hb hn heq hfail)
    (fun hl hb hn hfail =>
      Condition.bool.checkForPrimitive.WF.semantic
        hl hvlctx hb hn hfail)
  refine hcore.mono fun _ _ _ h b => ?_
  rcases h b with
    ⟨cert, hlevels, hbool, hnat, hbeq, hadd, hmod, hdiv,
      htyEq, hcert, hnatEvidence, hboolEvidence⟩
  rcases hnatEvidence with ⟨decide, hdecideS, _, hdecide⟩
  rcases hboolEvidence with ⟨ite, hiteS, hite⟩
  exact ⟨cert, ite, decide, hlevels, hbool, hnat, hbeq,
    hadd, hmod, hdiv, htyEq, hcert, hiteS, hite,
    hdecideS, hdecide⟩

end Lean4Lean.Environment
