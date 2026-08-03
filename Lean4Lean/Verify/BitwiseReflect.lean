import Lean4Lean.Verify.BitwiseTop
import Lean4Lean.Verify.BitwiseSucc

namespace Lean4Lean.Environment
open Lean VEnv

/-- A normalized checked fixpoint certificate, together with the checked
condition helpers used by its successor equation, reflects `Nat.bitwise` in
all future well-formed environments. -/
theorem NatBitwiseFixCertificate.NormalizedValid.reflects
    {c : TypeChecker.VContext} {r : NatBitwiseFixCertificate}
    {bitwise : Expr} {g ite decide : VExpr}
    (hv : r.NormalizedValid c bitwise)
    (hlparams : c.lparams = []) (hvlctx : c.vlctx = [])
    (hbool : c.venv.contains ``Bool) (hnat : c.venv.contains ``Nat)
    (hbeqC : c.venv.contains ``Nat.beq)
    (haddC : c.venv.contains ``Nat.add)
    (hmodC : c.venv.contains ``Nat.mod)
    (hdivC : c.venv.contains ``Nat.div)
    (hadd : c.venv.ReflectsNatNatNat ``Nat.add Nat.add)
    (hmod : c.venv.ReflectsNatNatNat ``Nat.mod Nat.mod)
    (hdiv : c.venv.ReflectsNatNatNat ``Nat.div Nat.div)
    (hbitwise : TrExprS c.venv [] [] bitwise g)
    (hf : ∀ U Γ, c.venv.HasType U Γ (.const ``Nat.bitwise [])
      (.forallE (.forallE .bool <| .forallE .bool .bool) <|
        .forallE .nat <| .forallE .nat .nat))
    (hcf : c.venv.IsDefEqU 0 [] (.const ``Nat.bitwise []) g)
    (hiteS : TrExprS c.venv [] [] Condition.bool.boolNatITE ite)
    (hite : c.venv.ReflectsBoolNatITE ite)
    (hdecideS : TrExprS c.venv [] [] Condition.natEqDecideFn decide)
    (hdecide : Lean4Lean.Environment.VEnv.ReflectsNatEqDecide
      c.venv decide) :
    c.venv.ReflectsNatBitwise ``Nat.bitwise := by
  rcases hv with
    ⟨hcore, htop, hzero, hzeroRight, hsucc, hcall⟩
  rcases hcore.normalizeAux with ⟨heager, htrue, _hfalse⟩
  rcases heager with ⟨el, er, hel, her, heeq⟩
  rcases htrue with ⟨tl, tr, htl, htr, hteq⟩
  rcases htop with ⟨topL, topR, htopL, htopR, htopEq⟩
  rcases hzero with ⟨zeroL, zeroR, hzeroL, hzeroR, hzeroEq⟩
  rcases hzeroRight with
    ⟨zeroRightL, zeroRightR, hzeroRightL, hzeroRightR, hzeroRightEq⟩
  rcases hsucc with ⟨succL, succR, hsuccL, hsuccR, hsuccEq⟩
  rcases hcall with ⟨callV, callTy, hcallS, hcallT⟩
  change TrExprS c.venv c.lparams c.vlctx
    r.core.expectedEagerLhs el at hel
  change TrExprS c.venv c.lparams c.vlctx
    r.core.expectedEagerRhs er at her
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx el er at heeq
  change TrExprS c.venv c.lparams c.vlctx
    r.core.expectedBoolTrueLhs tl at htl
  change TrExprS c.venv c.lparams c.vlctx
    r.core.expectedBoolTrueRhs tr at htr
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx tl tr at hteq
  change TrExprS c.venv c.lparams c.vlctx
    (r.expectedTopLhs bitwise) topL at htopL
  change TrExprS c.venv c.lparams c.vlctx r.expectedTopRhs topR at htopR
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx
    topL topR at htopEq
  change TrExprS c.venv c.lparams c.vlctx
    r.expectedZeroLhs zeroL at hzeroL
  change TrExprS c.venv c.lparams c.vlctx
    r.expectedZeroRhs zeroR at hzeroR
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx
    zeroL zeroR at hzeroEq
  change TrExprS c.venv c.lparams c.vlctx
    r.expectedZeroRightLhs zeroRightL at hzeroRightL
  change TrExprS c.venv c.lparams c.vlctx
    r.expectedZeroRightRhs zeroRightR at hzeroRightR
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx
    zeroRightL zeroRightR at hzeroRightEq
  change TrExprS c.venv c.lparams c.vlctx
    r.expectedSuccLhs succL at hsuccL
  change TrExprS c.venv c.lparams c.vlctx
    r.expectedSuccRhs succR at hsuccR
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx
    succL succR at hsuccEq
  change TrExprS c.venv c.lparams c.vlctx r.callFn callV at hcallS
  change c.venv.HasType c.lparams.length c.vlctx.toCtx
    callV callTy at hcallT
  rw [hlparams, hvlctx] at hel her heeq htl htr hteq htopL htopR htopEq hzeroL hzeroR hzeroEq hzeroRightL hzeroRightR hzeroRightEq hsuccL hsuccR hsuccEq hcallS hcallT
  have wf := c.Ewf
  have hprim := c.hasPrimitives
  have hctors :=
    Lean4Lean.Environment.VEnv.HasNatBoolConstructors.of_primitives
      hprim hbool hnat
  have heagerBase (n) : ∃ eager,
      TrExprS c.venv [] [] q(WellFounded.Nat.eager) eager ∧
      c.venv.IsDefEqU 0 [] (.app eager (.natLit n)) (.natLit n) := by
    simpa [hcore.eagerFn_eq, Expr.instantiate1'] using
      (VEnv.eager_natLit_of_aux_equations wf hprim hnat
        hbeqC hel her heeq htl htr hteq (n := n))
  have hgT := (hcf.of_l wf trivial (hf 0 [])).hasType.2
  intro _
  refine ⟨hf, ?_⟩
  intro env' le wf' op f hop a b
  have hctors' := hctors.mono le
  have hite' : env'.ReflectsBoolNatITE ite :=
    ⟨hite.1.mono le, fun x y z => (hite.2 x y z).mono le⟩
  have hdecide' : Lean4Lean.Environment.VEnv.ReflectsNatEqDecide
      env' decide := hdecide.mono le
  have haddC' : env'.contains ``Nat.add :=
    let ⟨ci, hci⟩ := haddC; ⟨ci, le.constants hci⟩
  have hmodC' : env'.contains ``Nat.mod :=
    let ⟨ci, hci⟩ := hmodC; ⟨ci, le.constants hci⟩
  have hdivC' : env'.contains ``Nat.div :=
    let ⟨ci, hci⟩ := hdivC; ⟨ci, le.constants hci⟩
  have hadd' : env'.ReflectsNatNatNat ``Nat.add Nat.add := by
    intro _
    exact ⟨fun U Γ => ((hadd haddC).1 U Γ).mono le,
      fun x y => ((hadd haddC).2 x y).mono le⟩
  have hmod' : env'.ReflectsNatNatNat ``Nat.mod Nat.mod := by
    intro _
    exact ⟨fun U Γ => ((hmod hmodC).1 U Γ).mono le,
      fun x y => ((hmod hmodC).2 x y).mono le⟩
  have hdiv' : env'.ReflectsNatNatNat ``Nat.div Nat.div := by
    intro _
    exact ⟨fun U Γ => ((hdiv hdivC).1 U Γ).mono le,
      fun x y => ((hdiv hdivC).2 x y).mono le⟩
  have heager' (n) : ∃ eager,
      TrExprS env' [] [] q(WellFounded.Nat.eager) eager ∧
      env'.IsDefEqU 0 [] (.app eager (.natLit n)) (.natLit n) := by
    rcases heagerBase n with ⟨eager, hs, he⟩
    exact ⟨eager, hs.mono le, he.mono le⟩
  have htop' := NatBitwiseFixCertificate.top_semantics wf' hctors'
    (r := r) (callV := callV) (callTy := callTy)
    (htopL.mono le) (htopR.mono le) (htopEq.mono le)
    (hbitwise.mono le) (hgT.mono le) (hcallS.mono le)
    (hcallT.mono le) heager'
  have hzero' := NatBitwiseFixCertificate.zero_semantics wf' hctors'
    (hzeroL.mono le) (hzeroR.mono le) (hzeroEq.mono le)
    (hiteS.mono le) hite'
  have hzeroRight' :=
    NatBitwiseFixCertificate.zero_right_semantics wf' hctors'
      (hzeroRightL.mono le) (hzeroRightR.mono le)
      (hzeroRightEq.mono le) (hiteS.mono le) hite'
  have hsucc' := NatBitwiseFixCertificate.succ_semantics wf' hctors'
    haddC' hmodC' hdivC' hadd' hmod' hdiv'
    (hdecideS.mono le) hdecide'
    (hsuccL.mono le) (hsuccR.mono le) (hsuccEq.mono le)
    (hiteS.mono le) hite'
  have hfix := VEnv.evalNatBitwise_of_fix_relation wf'
    (VEnv.BitwiseGoCall env' r op) (g := g) (op := op) (f := f)
    (htop' op hop.1)
    (by
      intro fuel x y e hG he
      cases x with
      | zero => simpa using hzero' op f hop fuel y e hG he
      | succ x =>
        cases y with
        | zero =>
          simpa using hzeroRight' op f hop fuel x e hG he
        | succ y =>
          simpa using hsucc' op f hop fuel x y e hG he)
    a b
  have hcf' := hcf.mono le
  have hf' := (hf 0 []).mono le
  have h₁ := hcf'.app_same wf' trivial hf' hop.1
  have haT := hctors'.natLitS a (Us := []) (Δ := []) |>.2
  have hbT := hctors'.natLitS b (Us := []) (Δ := []) |>.2
  have h₂ := h₁.app_same wf' trivial (.app hf' hop.1) haT
  have h₃ := h₂.app_same wf' trivial (.app (.app hf' hop.1) haT) hbT
  exact h₃.trans wf' trivial hfix

end Lean4Lean.Environment
