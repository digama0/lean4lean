import Lean4Lean.Verify.BitwiseTop
import Lean4Lean.Verify.BitwiseSucc

namespace Lean4Lean.Environment
open Lean VEnv

/-- A normalized checked fixpoint certificate, together with the checked
condition helpers used by its successor equation, reflects `Nat.bitwise` in
all future well-formed environments. -/
theorem NatBitwiseFixCertificate.NormalizedValid.reflects
    {c : TypeChecker.VContext} {env : VEnv} {r : NatBitwiseFixCertificate}
    {bitwise : Expr} {g ite decide : VExpr}
    (hv : r.NormalizedValid c bitwise)
    (hlparams : c.lparams = []) (hvlctx : c.vlctx = [])
    (hle : c.venv ≤ env) (hwf : env.WF)
    (hbool : c.venv.contains ``Bool) (hnat : c.venv.contains ``Nat)
    (hbeqC : c.venv.contains ``Nat.beq)
    (haddC : c.venv.contains ``Nat.add)
    (hmodC : c.venv.contains ``Nat.mod)
    (hdivC : c.venv.contains ``Nat.div)
    (hadd : c.venv.ReflectsNatNatNat ``Nat.add Nat.add)
    (hmod : c.venv.ReflectsNatNatNat ``Nat.mod Nat.mod)
    (hdiv : c.venv.ReflectsNatNatNat ``Nat.div Nat.div)
    (hbitwise : TrExprS env [] [] bitwise g)
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.bitwise [])
      (.forallE (.forallE .bool <| .forallE .bool .bool) <|
        .forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.bitwise []) g)
    (hiteS : TrExprS c.venv [] [] Condition.bool.boolNatITE ite)
    (hite : c.venv.ReflectsBoolNatITE ite)
    (hdecideS : TrExprS c.venv [] [] Condition.natEqDecideFn decide)
    (hdecide : Lean4Lean.Environment.VEnv.ReflectsNatEqDecide
      c.venv decide) :
    env.ReflectsNatBitwise ``Nat.bitwise := by
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
  have baseWf := c.Ewf
  have hprim := c.hasPrimitives
  have hctors :=
    Lean4Lean.Environment.VEnv.HasNatBoolConstructors.of_primitives
      hprim hbool hnat
  have heagerBase (n) : ∃ eager,
      TrExprS c.venv [] [] q(WellFounded.Nat.eager) eager ∧
      c.venv.IsDefEqU 0 [] (.app eager (.natLit n)) (.natLit n) := by
    simpa [hcore.eagerFn_eq, Expr.instantiate1'] using
      (VEnv.eager_natLit_of_aux_equations baseWf hprim hnat
        hbeqC hel her heeq htl htr hteq (n := n))
  have hgT := (hcf.of_l hwf trivial (hf 0 [])).hasType.2
  intro _
  refine ⟨hf, ?_⟩
  intro env' le wf' op f hop a b
  have baseLe : c.venv ≤ env' := hle.trans le
  have hctors' := hctors.mono baseLe
  have hite' : env'.ReflectsBoolNatITE ite :=
    ⟨hite.1.mono baseLe, fun x y z => (hite.2 x y z).mono baseLe⟩
  have hdecide' : Lean4Lean.Environment.VEnv.ReflectsNatEqDecide
      env' decide := hdecide.mono baseLe
  have haddC' : env'.contains ``Nat.add :=
    let ⟨ci, hci⟩ := haddC; ⟨ci, baseLe.constants hci⟩
  have hmodC' : env'.contains ``Nat.mod :=
    let ⟨ci, hci⟩ := hmodC; ⟨ci, baseLe.constants hci⟩
  have hdivC' : env'.contains ``Nat.div :=
    let ⟨ci, hci⟩ := hdivC; ⟨ci, baseLe.constants hci⟩
  have hadd' : env'.ReflectsNatNatNat ``Nat.add Nat.add := by
    intro _
    exact ⟨fun U Γ => ((hadd haddC).1 U Γ).mono baseLe,
      fun x y => ((hadd haddC).2 x y).mono baseLe⟩
  have hmod' : env'.ReflectsNatNatNat ``Nat.mod Nat.mod := by
    intro _
    exact ⟨fun U Γ => ((hmod hmodC).1 U Γ).mono baseLe,
      fun x y => ((hmod hmodC).2 x y).mono baseLe⟩
  have hdiv' : env'.ReflectsNatNatNat ``Nat.div Nat.div := by
    intro _
    exact ⟨fun U Γ => ((hdiv hdivC).1 U Γ).mono baseLe,
      fun x y => ((hdiv hdivC).2 x y).mono baseLe⟩
  have heager' (n) : ∃ eager,
      TrExprS env' [] [] q(WellFounded.Nat.eager) eager ∧
      env'.IsDefEqU 0 [] (.app eager (.natLit n)) (.natLit n) := by
    rcases heagerBase n with ⟨eager, hs, he⟩
    exact ⟨eager, hs.mono baseLe, he.mono baseLe⟩
  have htop' := NatBitwiseFixCertificate.top_semantics wf' hctors'
    (r := r) (callV := callV) (callTy := callTy)
    (htopL.mono baseLe) (htopR.mono baseLe) (htopEq.mono baseLe)
    (hbitwise.mono le) (hgT.mono le) (hcallS.mono baseLe)
    (hcallT.mono baseLe) heager'
  have hzero' := NatBitwiseFixCertificate.zero_semantics wf' hctors'
    (hzeroL.mono baseLe) (hzeroR.mono baseLe) (hzeroEq.mono baseLe)
    (hiteS.mono baseLe) hite'
  have hzeroRight' :=
    NatBitwiseFixCertificate.zero_right_semantics wf' hctors'
      (hzeroRightL.mono baseLe) (hzeroRightR.mono baseLe)
      (hzeroRightEq.mono baseLe) (hiteS.mono baseLe) hite'
  have hsucc' := NatBitwiseFixCertificate.succ_semantics wf' hctors'
    haddC' hmodC' hdivC' hadd' hmod' hdiv'
    (hdecideS.mono baseLe) hdecide'
    (hsuccL.mono baseLe) (hsuccR.mono baseLe) (hsuccEq.mono baseLe)
    (hiteS.mono baseLe) hite'
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

/-- Install the semantic result of a checked `Nat.bitwise` certificate into
the primitive invariant after adding the definition and its reduction rule. -/
theorem NatBitwiseFixCertificate.NormalizedValid.conservesHasPrimitives
    {c : TypeChecker.VContext} {env' : VEnv}
    {r : NatBitwiseFixCertificate} {bitwise : Expr}
    {v : VDefVal} {ite decide : VExpr}
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
    (hbitwise : TrExprS c.venv [] [] bitwise v.value)
    (hiteS : TrExprS c.venv [] [] Condition.bool.boolNatITE ite)
    (hite : c.venv.ReflectsBoolNatITE ite)
    (hdecideS : TrExprS c.venv [] [] Condition.natEqDecideFn decide)
    (hdecide : VEnv.ReflectsNatEqDecide c.venv decide)
    (hname : v.name = ``Nat.bitwise)
    (haddConst : c.venv.addConst ``Nat.bitwise v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hu : v.uvars = 0)
    (hty : c.venv.IsDefEqU 0 [] v.type
      (.forallE (.forallE .bool <| .forallE .bool .bool) <|
        .forallE .nat <| .forallE .nat .nat)) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  let env'' := env'.addDefEq v.toDefEq
  have hle : c.venv ≤ env'' :=
    (VEnv.addConst_le haddConst).trans VEnv.addDefEq_le
  have hf (U Γ) : env''.HasType U Γ (.const ``Nat.bitwise [])
      (.forallE (.forallE .bool <| .forallE .bool .bool) <|
        .forallE .nat <| .forallE .nat .nat) :=
    VEnv.HasType.const_of_type_defeq hwf (by
      change env'.constants ``Nat.bitwise = some v.toVConstant
      exact VEnv.addConst_self haddConst) hu (hty.mono hle) U Γ
  have hcf := VDefVal.const_defeq_value hwf hu
  rw [hname] at hcf
  have href : env''.ReflectsNatBitwise ``Nat.bitwise :=
    hv.reflects hlparams hvlctx hle hwf hbool hnat hbeqC
      haddC hmodC hdivC hadd hmod hdiv (hbitwise.mono hle) hf hcf
      hiteS hite hdecideS hdecide
  exact c.hasPrimitives.addNatBitwiseDef haddConst href

/-- Turn the semantic postcondition of the `Nat.bitwise` primitive checker
into conservation of `HasPrimitives` for the translated definition. -/
theorem checkPrimitiveDef.natBitwise.WF.conservesHasPrimitives
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {src : DefinitionVal} {v : VDefVal} {env' : VEnv}
    {ite decide : VExpr} {P : Prop}
    {R : NatBitwiseFixCertificate → Prop}
    (hcparams : c.lparams = src.levelParams) (hvlctx : c.vlctx = [])
    (hbool : c.venv.contains ``Bool) (hnat : c.venv.contains ``Nat)
    (hbeqC : c.venv.contains ``Nat.beq)
    (haddC : c.venv.contains ``Nat.add)
    (hmodC : c.venv.contains ``Nat.mod)
    (hdivC : c.venv.contains ``Nat.div)
    (hadd : c.venv.ReflectsNatNatNat ``Nat.add Nat.add)
    (hmod : c.venv.ReflectsNatNatNat ``Nat.mod Nat.mod)
    (hdiv : c.venv.ReflectsNatNatNat ``Nat.div Nat.div)
    (hbitwise : c.TrExprS src.value v.value)
    (hiteS : c.TrExprS Condition.bool.boolNatITE ite)
    (hdecideS : c.TrExprS Condition.natEqDecideFn decide)
    (hname : v.name = ``Nat.bitwise)
    (huvars : src.levelParams.length = v.uvars)
    (haddConst : c.venv.addConst ``Nat.bitwise v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hcheck : TypeChecker.M.WF c s (checkPrimitiveDef src) fun b _ => b →
      src.levelParams = [] ∧
      c.IsDefEqU v.type
        (.forallE (.forallE .bool <| .forallE .bool .bool) <|
          .forallE .nat <| .forallE .nat .nat) ∧
      ∃ cert : NatBitwiseFixCertificate,
        cert.NormalizedValid c src.value ∧
        (P ∧ VEnv.ReflectsNatEqDecide c.venv decide) ∧
        c.venv.ReflectsBoolNatITE ite ∧ R cert) :
    TypeChecker.M.WF c s (checkPrimitiveDef src) fun b _ => b →
      (env'.addDefEq v.toDefEq).HasPrimitives := by
  refine hcheck.mono fun _ _ _ h b => ?_
  rcases h b with ⟨hsrcParams, hty, cert, hcert, hnatCert,
    hboolCert, _⟩
  have hclparams : c.lparams = [] := hcparams.trans hsrcParams
  have hvuvars : v.uvars = 0 := by
    rw [← huvars, hsrcParams]
    rfl
  change TrExprS c.venv c.lparams c.vlctx _ _ at hbitwise hiteS hdecideS
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx _ _ at hty
  rw [hclparams, hvlctx] at hbitwise hiteS hdecideS hty
  exact hcert.conservesHasPrimitives hclparams hvlctx hbool hnat hbeqC
    haddC hmodC hdivC hadd hmod hdiv hbitwise hiteS hboolCert
    hdecideS hnatCert.2 hname haddConst hwf hvuvars hty

end Lean4Lean.Environment
