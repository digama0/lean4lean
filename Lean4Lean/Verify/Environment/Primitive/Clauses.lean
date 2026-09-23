import Lean4Lean.Verify.Environment.Primitive.Condition

/-!
One theorem per clause of the recognizer, over the vocabulary they share.
-/

namespace Lean4Lean
open Lean4Lean TypeChecker
open Lean hiding Environment Exception
open Kernel

namespace Primitive

/-! ### The clauses

One theorem per clause of the recognizer, each about the definition `checkDef` dispatches to. A
clause is handed the definition and the translations `addDefinition` established for it -- that is
`Data` -- and its name, which is what pins down the spec entry it has to produce. -/

/-- `Nat.add`: two probes, `add x 0 ≡ x` and `add x (succ y) ≡ succ (add x y)`, and the reflection
follows by induction on the second argument.

The context is a `let` here for the same reason it is one in `checkDef.WF`: the probes' facts
arrive at `ctx.vlctx.toCtx`, and only a context that reduces to `.mk' wf .safe v.levelParams`
makes that the empty context on the nose. Over an abstract `VContext` the same proof needs a
rewrite per equation. -/

theorem checkNatAdd.WF {ves : VEnvs} (wf : ves.WF env)
    (hname : v.name = ``Nat.add) :
    let c := .mk' wf .safe v.levelParams; Data v ci' c →
    (checkNatAdd v).WF c state fun _ _ => PrimitiveResult (ves.venv .safe) v ci' := by
  intro ctx P; rw [← ctx.withMLC_self]; unfold checkNatAdd
  have hnat : ctx.env.contains ``Nat → (ves.venv .safe).contains ``Nat :=
    P.contains (by simp [Environment.primitives, NameSet.contains, NameSet.ofList])
  refine .getEnv <| elseFail fun h1 => elseFail fun h2 => ?_
  simp at h1; specialize hnat h1.1
  have tyeq := P.mkTyEq hnat (by simp [TrExprS.IsUnique]) (natCod hnat) h2
  refine .withNatProbe wf.hasPrimitives hnat .rfl ?_; intro idx m _ _ _ hres hx
  -- the first probe: `v.value x 0 ≡ x`
  refine .bind (isDefEq.WF (TrTerm.natBinApp (P.hv tyeq m) hx (zerob hnat)).trS hx.trS)
    fun _ _ _ hb => elseFail ((fun hb' => ?_) ∘ hb)
  refine .withNatProbe wf.hasPrimitives hnat .rfl ?_; intro idy m cwf _ _ hres' hy
  let hx := hx.wk ctx.Ewf cwf.wf.tr.wf
  -- the second probe, one binder deeper: `v.value x (succ y) ≡ succ (v.value x y)`;
  -- `hx` comes from the outer binder, so it weakens past this one
  refine .bind (isDefEq.WF
    (TrTerm.natBinApp (P.hv tyeq m) hx (.natUnApp (succb hnat) hy)).trS
    (TrTerm.natUnApp (succb hnat) (.natBinApp (P.hv tyeq m) hx hy)).trS)
    fun _ _ _ hb2 => elseFail ((fun hb2' => ?_) ∘ hb2)
  exact .pure <| P.mkResult (hok h1.2) hnat (by simp [primSpecs, hname]) tyeq fun hvT =>
    .of_unary_step_equations (F := Nat.add) (congrArg List.length (hok h1.2).2)
      ctx.Ewf wf.hasPrimitives hnat Nat.succ
      (wf.hasPrimitives.natSuccT ctx.Ewf.orderedStrong hnat []) trivial
      (fun k => ⟨_, wf.hasPrimitives.natLitT ctx.Ewf.orderedStrong hnat (k + 1) []⟩)
      (fun _ => rfl) (fun _ _ => rfl) hvT hb' hb2'

/-- `Nat.pred`: `pred 0 ≡ 0`, checked outright, and `pred (succ x) ≡ x` under one probe. -/
theorem checkNatPred.WF {ves : VEnvs} (wf : ves.WF env)
    (hname : v.name = ``Nat.pred) :
    let c := .mk' wf .safe v.levelParams; Data v ci' c →
    (checkNatPred v).WF c state fun _ _ => PrimitiveResult (ves.venv .safe) v ci' := by
  intro ctx P; rw [← ctx.withMLC_self]; unfold checkNatPred
  have hnat : ctx.env.contains ``Nat → (ves.venv .safe).contains ``Nat :=
    P.contains (by simp [Environment.primitives, NameSet.contains, NameSet.ofList])
  refine .getEnv <| elseFail fun h1 => elseFail fun h2 => ?_
  simp at h1; specialize hnat h1.1
  have tyeq := P.mkTyEq1 hnat (by simp [TrExprS.IsUnique]) (natCod1 hnat) h2
  -- the first probe: `v.value 0 ≡ 0`
  refine .bind (isDefEq.WF (TrTerm.natUnApp (P.hv tyeq ctx.mlctx) (zerob hnat)).trS
      (zerob hnat).trS) fun _ _ _ hb => elseFail ((fun hb' => ?_) ∘ hb)
  refine .withNatProbe wf.hasPrimitives hnat .rfl ?_; intro idx m _ _ _ hres hx
  -- the second probe: `v.value (succ x) ≡ x`
  refine .bind (isDefEq.WF (TrTerm.natUnApp (P.hv tyeq m) (.natUnApp (succb hnat) hx)).trS hx.trS)
    fun _ _ _ hb2 => elseFail ((fun hb2' => ?_) ∘ hb2)
  exact .pure <| P.mkResult1 (hok h1.2) hnat (by simp [primSpecs, hname]) tyeq fun hvT =>
    .of_pred_equations (congrArg List.length (hok h1.2).2)
      ctx.Ewf wf.hasPrimitives hnat hvT hb' hb2'

/-- `Nat.sub`: `sub x 0 ≡ x` and `sub x (succ y) ≡ Nat.pred (sub x y)`. The guard names
`Nat.pred` rather than `Nat`, so `Nat` itself comes from `Nat.pred`'s recorded type. -/
theorem checkNatSub.WF {ves : VEnvs} (wf : ves.WF env)
    (hname : v.name = ``Nat.sub) :
    let c := .mk' wf .safe v.levelParams; Data v ci' c →
    (checkNatSub v).WF c state fun _ _ => PrimitiveResult (ves.venv .safe) v ci' := by
  intro ctx P; rw [← ctx.withMLC_self]; unfold checkNatSub
  refine .getEnv <| elseFail fun h1 => elseFail fun h2 => ?_
  simp at h1
  have hpred := VContext.contains_primitive rfl h1.1
  have hnat := wf.hasPrimitives.natOfPred ctx.Ewf.orderedStrong hpred
  have tyeq := P.mkTyEq hnat (by simp [TrExprS.IsUnique]) (natCod hnat) h2
  refine .withNatProbe wf.hasPrimitives hnat .rfl ?_; intro idx m _ _ _ hres hx
  -- the first probe: `v.value x 0 ≡ x`
  refine .bind (isDefEq.WF (TrTerm.natBinApp (P.hv tyeq m) hx (zerob hnat)).trS hx.trS)
    fun _ _ _ hb => elseFail ((fun hb' => ?_) ∘ hb)
  refine .withNatProbe wf.hasPrimitives hnat .rfl ?_; intro idy m cwf _ _ hres' hy
  let hx := hx.wk ctx.Ewf cwf.wf.tr.wf
  -- the second probe: `v.value x (succ y) ≡ Nat.pred (v.value x y)`.
  refine .bind (isDefEq.WF
    (TrTerm.natBinApp (P.hv tyeq m) hx (.natUnApp (succb hnat) hy)).trS
    (TrTerm.natUnApp (predb hpred) (.natBinApp (P.hv tyeq m) hx hy)).trS)
    fun _ _ _ hb2 => elseFail ((fun hb2' => ?_) ∘ hb2)
  exact .pure <| P.mkResult (hok h1.2) hnat (by simp [primSpecs, hname]) tyeq fun hvT =>
    .of_unary_step_equations (F := Nat.sub) (congrArg List.length (hok h1.2).2)
      ctx.Ewf wf.hasPrimitives hnat Nat.pred
      (wf.hasPrimitives.natPredT ctx.Ewf.orderedStrong hpred []) trivial
      (wf.hasPrimitives.natPred hpred).2 (fun _ => rfl) (fun _ _ => rfl) hvT hb' hb2'

/-- `Nat.mul`: `mul x 0 ≡ 0` and `mul x (succ y) ≡ Nat.add (mul x y) x`. The guard names
`Nat.add`, whose reflection supplies both the operator and `Nat`. -/
theorem checkNatMul.WF {ves : VEnvs} (wf : ves.WF env)
    (hname : v.name = ``Nat.mul) :
    let c := .mk' wf .safe v.levelParams; Data v ci' c →
    (checkNatMul v).WF c state fun _ _ => PrimitiveResult (ves.venv .safe) v ci' := by
  intro ctx P; rw [← ctx.withMLC_self]; unfold checkNatMul
  refine .getEnv <| elseFail fun h1 => elseFail fun h2 => ?_
  simp at h1
  have hadd := VContext.contains_primitive rfl h1.1
  have hnat := wf.hasPrimitives.natOfAdd ctx.Ewf.orderedStrong hadd
  have tyeq := P.mkTyEq hnat (by simp [TrExprS.IsUnique]) (natCod hnat) h2
  refine .withNatProbe wf.hasPrimitives hnat .rfl ?_; intro idx m _ _ _ hres hx
  -- the first probe: `v.value x 0 ≡ 0` -- a literal base, not `x`
  refine .bind (isDefEq.WF (TrTerm.natBinApp (P.hv tyeq m) hx (zerob hnat)).trS (zerob hnat).trS)
    fun _ _ _ hb => elseFail ((fun hb' => ?_) ∘ hb)
  refine .withNatProbe wf.hasPrimitives hnat .rfl ?_; intro idy m cwf _ _ hres' hy
  let hx1 := hx.wk ctx.Ewf cwf.wf.tr.wf
  -- the second probe: `v.value x (succ y) ≡ Nat.add (v.value x y) x`
  refine .bind (isDefEq.WF
    (TrTerm.natBinApp (P.hv tyeq m) hx1 (.natUnApp (succb hnat) hy)).trS
    (TrTerm.natBinApp (addb hadd) (.natBinApp (P.hv tyeq m) hx1 hy) hx1).trS)
    fun _ _ _ hb2 => elseFail ((fun hb2' => ?_) ∘ hb2)
  refine .pure <| P.mkResult (hok h1.2) hnat (by simp [primSpecs, hname]) tyeq fun hvT =>
    .of_binary_step_equations (F := Nat.mul) (congrArg List.length (hok h1.2).2)
      ctx.Ewf wf.hasPrimitives hnat Nat.add (fun _ => 0) id (wf.hasPrimitives.natAdd hadd)
      (fun _ => rfl) (fun _ _ => ?_) (fun _ => rfl) (fun _ _ => rfl) hvT hb' hb2'
  simp [hx1, hx, TrTerm.wk, TrTerm.fvar, VExpr.inst, VExpr.lift, VExpr.liftN]

/-- `Nat.pow`: `pow x 0 ≡ 1` and `pow x (succ y) ≡ Nat.mul (pow x y) x`, over the `Nat.mul`
guard. The base is spelled as a constructor application, which is `.natLit 1` on the model side. -/
theorem checkNatPow.WF {ves : VEnvs} (wf : ves.WF env)
    (hname : v.name = ``Nat.pow) :
    let c := .mk' wf .safe v.levelParams; Data v ci' c →
    (checkNatPow v).WF c state fun _ _ => PrimitiveResult (ves.venv .safe) v ci' := by
  intro ctx P; rw [← ctx.withMLC_self]; unfold checkNatPow
  refine .getEnv ?_
  refine elseFail fun h1 => elseFail fun h2 => ?_
  simp at h1
  have hmul := VContext.contains_primitive rfl h1.1
  have hnat := wf.hasPrimitives.natOfMul ctx.Ewf.orderedStrong hmul
  have tyeq := P.mkTyEq hnat (by simp [TrExprS.IsUnique]) (natCod hnat) h2
  refine .withNatProbe wf.hasPrimitives hnat .rfl ?_; intro idx m _ _ _ hres hx
  -- the first probe: `v.value x 0 ≡ succ 0`; the base is `one`, spelled as a constructor
  -- application rather than a numeral, which is `.natLit 1` on the model side
  refine .bind (isDefEq.WF (TrTerm.natBinApp (P.hv tyeq m) hx (zerob hnat)).trS (oneb hnat).trS)
    fun _ _ _ hb => elseFail ((fun hb' => ?_) ∘ hb)
  refine .withNatProbe wf.hasPrimitives hnat .rfl ?_; intro idy m cwf _ _ hres' hy
  let hx1 := hx.wk ctx.Ewf cwf.wf.tr.wf
  -- the second probe: `v.value x (succ y) ≡ Nat.mul (v.value x y) x`
  refine .bind (isDefEq.WF
    (TrTerm.natBinApp (P.hv tyeq m) hx1 (.natUnApp (succb hnat) hy)).trS
    (TrTerm.natBinApp (mulb hmul) (.natBinApp (P.hv tyeq m) hx1 hy) hx1).trS)
    fun _ _ _ hb2 => elseFail ((fun hb2' => ?_) ∘ hb2)
  refine .pure <| P.mkResult (hok h1.2) hnat (by simp [primSpecs, hname]) tyeq fun hvT =>
    .of_binary_step_equations (F := Nat.pow) (congrArg List.length (hok h1.2).2)
      ctx.Ewf wf.hasPrimitives hnat Nat.mul (fun _ => 1) id (wf.hasPrimitives.natMul hmul)
      (fun _ => rfl) (fun _ _ => ?_) (fun _ => rfl) (fun _ _ => rfl) hvT hb' hb2'
  simp [hx1, hx, TrTerm.wk, TrTerm.fvar, VExpr.inst, VExpr.lift, VExpr.liftN]

/-- The four constructor cases, for whichever `F` the caller's `0 (succ x)` case selects:
`true` on `0 0`, `false` on `(succ x) 0`, and the diagonal `F (succ x) (succ y) = F x y`. -/
theorem checkNatBoolCases.WF {ves : VEnvs} (wf : ves.WF env) {F} (b0s : Bool)
    (hmem : (v.name, .reflectsNatNatBool F) ∈ primSpecs)
    (hF00 : F 0 0 = true) (hF0s : ∀ b, F 0 (b + 1) = b0s) (hFs0 : ∀ a, F (a + 1) 0 = false)
    (hFss : ∀ a b, F (a + 1) (b + 1) = F a b) :
    let c := .mk' wf .safe v.levelParams; Data v ci' c →
    (checkNatBoolCases v (Lean.toExpr b0s)).WF c state fun _ _ =>
      PrimitiveResult (ves.venv .safe) v ci' := by
  intro ctx P; rw [← ctx.withMLC_self]; unfold checkNatBoolCases
  have hnat : ctx.env.contains ``Nat → (ves.venv .safe).contains ``Nat :=
    P.contains (by simp [Environment.primitives, NameSet.contains, NameSet.ofList])
  refine .getEnv <| elseFail fun h1 => elseFail fun h2 => ?_
  simp at h1; specialize hnat h1.1.1
  have hbool := VContext.contains_primitive rfl h1.1.2
  have tyeq := P.mkTyEq hnat (by simp [TrExprS.IsUnique]) (boolCod hnat hbool) h2
  -- `v.value 0 0 ≡ true`
  refine .bind (isDefEq.WF
    (TrTerm.natBinApp (P.hv tyeq ctx.mlctx) (zerob hnat) (zerob hnat)).trS
    (boolb hbool true).trS) fun _ _ _ hb => elseFail ((fun h00 => ?_) ∘ hb)
  refine .withNatProbe wf.hasPrimitives hnat .rfl ?_; intro idx m _ _ _ hres hx
  -- the two off-diagonal probes share the binder `x`
  refine .bind (isDefEq.WF
    (TrTerm.natBinApp (P.hv tyeq m) (zerob hnat) (.natUnApp (succb hnat) hx)).trS
    (boolb hbool b0s).trS) fun _ _ _ hb => elseFail ((fun h0s => ?_) ∘ hb)
  refine .bind (isDefEq.WF
    (TrTerm.natBinApp (P.hv tyeq m) (.natUnApp (succb hnat) hx) (zerob hnat)).trS
    (boolb hbool false).trS) fun _ _ _ hb => elseFail ((fun hs0 => ?_) ∘ hb)
  refine .withNatProbe wf.hasPrimitives hnat .rfl ?_; intro idy m cwf _ _ hres' hy
  let hx := hx.wk ctx.Ewf cwf.wf.tr.wf
  -- the diagonal probe: `v.value (succ x) (succ y) ≡ v.value x y`
  refine .bind (isDefEq.WF
    (TrTerm.natBinApp (P.hv tyeq m) (.natUnApp (succb hnat) hx) (.natUnApp (succb hnat) hy)).trS
    (TrTerm.natBinApp (P.hv tyeq m) hx hy).trS) fun _ _ _ hb => elseFail ((fun hss => ?_) ∘ hb)
  exact .pure <| P.mkResultBool (hok h1.2) hnat hmem tyeq fun hvT =>
    .of_constructor_cases (congrArg List.length (hok h1.2).2)
      ctx.Ewf wf.hasPrimitives hnat true b0s false hF00 hF0s hFs0 hFss hvT h00 h0s hs0 hss

/-- `Nat.beq`: the four constructor cases -- `true` on `0 0`, `false` on `0 (succ x)` and on
`(succ x) 0`, and the diagonal `beq (succ x) (succ y) ≡ beq x y`. -/
theorem checkNatBEq.WF {ves : VEnvs} (wf : ves.WF env)
    (hname : v.name = ``Nat.beq) :
    let c := .mk' wf .safe v.levelParams; Data v ci' c →
    (checkNatBEq v).WF c state fun _ _ => PrimitiveResult (ves.venv .safe) v ci' :=
  checkNatBoolCases.WF wf (F := Nat.beq) false (by simp [primSpecs, hname])
    rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

/-- `Nat.ble`: the same four cases as `Nat.beq`, with `ble 0 (succ x)` true rather than false. -/
theorem checkNatBLE.WF {ves : VEnvs} (wf : ves.WF env)
    (hname : v.name = ``Nat.ble) :
    let c := .mk' wf .safe v.levelParams; Data v ci' c →
    (checkNatBLE v).WF c state fun _ _ => PrimitiveResult (ves.venv .safe) v ci' :=
  checkNatBoolCases.WF wf (F := Nat.ble) true (by simp [primSpecs, hname])
    rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

/-- `Nat.land`: the value is `Nat.bitwise` at an operand, and two probes pin that operand to
`Bool.and`: `op false x ≡ false` and `op true x ≡ x`. -/
theorem checkNatLAnd.WF {ves : VEnvs} (wf : ves.WF env)
    (hname : v.name = ``Nat.land) :
    let c := .mk' wf .safe v.levelParams; Data v ci' c →
    (checkNatLAnd v).WF c state fun _ _ => PrimitiveResult (ves.venv .safe) v ci' := by
  intro ctx P; rw [← ctx.withMLC_self]; unfold checkNatLAnd
  refine .getEnv <| elseFail fun h1 => elseFail fun h2 => ?_; simp at h1
  have hbw := VContext.contains_primitive rfl h1.1
  have hnat := TrExprS.contains_nat_of_natArrow2 (P.htype.eqv h2)
  have hbool := wf.hasPrimitives.boolOfBitwise ctx.Ewf.orderedStrong hbw
  have tyeq := P.mkTyEq hnat (by simp [TrExprS.IsUnique]) (natCod hnat) h2
  split <;> [rename_i opSrc heq; exact .throw]
  obtain ⟨op, hVeq, hop, hopT⟩ := TrExprS.bitwiseOperand ctx.Ewf wf.hasPrimitives (heq ▸ P.hvalue)
  let opb (m : MLCtx) [cwf : ctx.MLCWF m] := TrTerm.of_nil' ctx.Ewf m.noBV cwf.wf.tr.wf hop hopT
  refine .withBoolProbe wf.hasPrimitives hbool .rfl ?_; intro idx m _ _ _ hres hx
  refine .bind (isDefEq.WF (TrTerm.boolBinApp (opb m) (boolb hbool false) hx).trS
    (boolb hbool false).trS) fun _ _ _ hb => elseFail ((fun h0 => ?_) ∘ hb)
  refine .bind (isDefEq.WF (TrTerm.boolBinApp (opb m) (boolb hbool true) hx).trS hx.trS)
    fun _ _ _ hb => elseFail ((fun h1' => ?_) ∘ hb)
  refine .pure <| P.mkResult (F := Nat.land) (hok h1.2) hnat ?_ tyeq fun _ => hVeq ▸ ?_
  · simp [primSpecs, hname]
  refine (wf.hasPrimitives.natBitwise hbw).2 _ .rfl ctx.Ewf op Bool.and ?_
  refine .of_left_cases (congrArg List.length (hok h1.2).2) ctx.Ewf wf.hasPrimitives hbool
    (hopT.closedN' ctx.Ewf.ordered.closed trivial).1 hopT h0 h1' (fun _ => rfl) (fun _ => ?_)
  simp [hx, TrTerm.fvar, VExpr.inst]

/-- `Nat.lor`: `Nat.bitwise` at an operand pinned to `Bool.or` by `op false x ≡ x` and
`op true x ≡ true`. -/
theorem checkNatLOr.WF {ves : VEnvs} (wf : ves.WF env)
    (hname : v.name = ``Nat.lor) :
    let c := .mk' wf .safe v.levelParams; Data v ci' c →
    (checkNatLOr v).WF c state fun _ _ => PrimitiveResult (ves.venv .safe) v ci' := by
  intro ctx P; rw [← ctx.withMLC_self]; unfold checkNatLOr
  refine .getEnv <| elseFail fun h1 => elseFail fun h2 => ?_; simp at h1
  have hbw := VContext.contains_primitive rfl h1.1
  have hnat := TrExprS.contains_nat_of_natArrow2 (P.htype.eqv h2)
  have hbool := wf.hasPrimitives.boolOfBitwise ctx.Ewf.orderedStrong hbw
  have tyeq := P.mkTyEq hnat (by simp [TrExprS.IsUnique]) (natCod hnat) h2
  split <;> [rename_i opSrc heq; exact .throw]
  obtain ⟨op, hVeq, hop, hopT⟩ := (heq ▸ P.hvalue).bitwiseOperand ctx.Ewf wf.hasPrimitives
  let opb (m : MLCtx) [cwf : ctx.MLCWF m] := TrTerm.of_nil' ctx.Ewf m.noBV cwf.wf.tr.wf hop hopT
  refine .withBoolProbe wf.hasPrimitives hbool .rfl ?_; intro idx m _ _ _ hres hx
  refine .bind (isDefEq.WF (TrTerm.boolBinApp (opb m) (boolb hbool false) hx).trS hx.trS)
    fun _ _ _ hb => elseFail ((fun h0 => ?_) ∘ hb)
  refine .bind (isDefEq.WF
    (TrTerm.boolBinApp (opb m) (boolb hbool true) hx).trS
    (boolb hbool true).trS) fun _ _ _ hb => elseFail ((fun h1' => ?_) ∘ hb)
  refine .pure <| P.mkResult (F := Nat.lor) (hok h1.2) hnat ?_ tyeq fun _ => hVeq ▸ ?_
  · simp [primSpecs, hname]
  refine (wf.hasPrimitives.natBitwise hbw).2 _ .rfl ctx.Ewf op Bool.or ?_
  refine .of_left_cases (congrArg List.length (hok h1.2).2) ctx.Ewf wf.hasPrimitives hbool
    (hopT.closedN' ctx.Ewf.ordered.closed trivial).1 hopT h0 h1' (fun _ => ?_) (fun _ => rfl)
  simp [hx, TrTerm.fvar, VExpr.inst]

/-- `Nat.xor`: `Nat.bitwise` at an operand pinned to `Bool.xor`. Both arguments are closed
here, so the four cases are checked outright rather than under a probe. -/
theorem checkNatXor.WF {ves : VEnvs} (wf : ves.WF env)
    (hname : v.name = ``Nat.xor) :
    let c := .mk' wf .safe v.levelParams; Data v ci' c →
    (checkNatXor v).WF c state fun _ _ => PrimitiveResult (ves.venv .safe) v ci' := by
  intro ctx P; rw [← ctx.withMLC_self]; unfold checkNatXor
  refine .getEnv <| elseFail fun h1 => elseFail fun h2 => ?_; simp at h1
  have hbw := VContext.contains_primitive rfl h1.1
  have hnat := TrExprS.contains_nat_of_natArrow2 (P.htype.eqv h2)
  have hbool := wf.hasPrimitives.boolOfBitwise ctx.Ewf.orderedStrong hbw
  have tyeq := P.mkTyEq hnat (by simp [TrExprS.IsUnique]) (natCod hnat) h2
  split <;> [rename_i opSrc heq; exact .throw]
  obtain ⟨op, hVeq, hop, hopT⟩ := TrExprS.bitwiseOperand ctx.Ewf wf.hasPrimitives (heq ▸ P.hvalue)
  let opb (m : MLCtx) [cwf : ctx.MLCWF m] := TrTerm.of_nil' ctx.Ewf m.noBV cwf.wf.tr.wf hop hopT
  refine .bind (isDefEq.WF
    (TrTerm.boolBinApp (opb ctx.mlctx) (boolb hbool false) (boolb hbool false)).trS
    (boolb hbool false).trS) fun _ _ _ hb => elseFail ((fun h00 => ?_) ∘ hb)
  refine .bind (isDefEq.WF
    (TrTerm.boolBinApp (opb ctx.mlctx) (boolb hbool true) (boolb hbool false)).trS
    (boolb hbool true).trS) fun _ _ _ hb => elseFail ((fun h10 => ?_) ∘ hb)
  refine .bind (isDefEq.WF
    (TrTerm.boolBinApp (opb ctx.mlctx) (boolb hbool false) (boolb hbool true)).trS
    (boolb hbool true).trS) fun _ _ _ hb => elseFail ((fun h01 => ?_) ∘ hb)
  refine .bind (isDefEq.WF
    (TrTerm.boolBinApp (opb ctx.mlctx) (boolb hbool true) (boolb hbool true)).trS
    (boolb hbool false).trS) fun _ _ _ hb => elseFail ((fun h11 => ?_) ∘ hb)
  refine .pure <| P.mkResult (F := Nat.xor) (hok h1.2) hnat (by simp [primSpecs, hname]) tyeq
    fun _ => hVeq ▸ (wf.hasPrimitives.natBitwise hbw).2 _ .rfl ctx.Ewf op Bool.xor ?_
  exact .of_closed_cases (congrArg List.length (hok h1.2).2) hopT fun
    | false, false => h00 | true, false => h10
    | false, true => h01 | true, true => h11

/-- `Nat.shiftLeft`: `x <<< 0 ≡ x` and `x <<< succ y ≡ (2 * x) <<< y` -- a step on the
*first* argument, over the `Nat.mul` guard. -/
theorem checkNatShiftLeft.WF {ves : VEnvs} (wf : ves.WF env)
    (hname : v.name = ``Nat.shiftLeft) :
    let c := .mk' wf .safe v.levelParams; Data v ci' c →
    (checkNatShiftLeft v).WF c state fun _ _ => PrimitiveResult (ves.venv .safe) v ci' := by
  intro ctx P; rw [← ctx.withMLC_self]; unfold checkNatShiftLeft
  refine .getEnv <| elseFail fun h1 => elseFail fun h2 => ?_
  simp at h1
  have hmul := VContext.contains_primitive rfl h1.1
  have hnat := wf.hasPrimitives.natOfMul ctx.Ewf.orderedStrong hmul
  have tyeq := P.mkTyEq hnat (by simp [TrExprS.IsUnique]) (natCod hnat) h2
  refine .withNatProbe wf.hasPrimitives hnat .rfl ?_; intro idx m _ _ _ hres hx
  refine .bind (isDefEq.WF (TrTerm.natBinApp (P.hv tyeq m) hx (zerob hnat)).trS hx.trS)
    fun _ _ _ hb => elseFail ((fun hb' => ?_) ∘ hb)
  refine .withNatProbe wf.hasPrimitives hnat .rfl ?_; intro idy m cwf _ _ hres' hy
  let hx1 := hx.wk ctx.Ewf cwf.wf.tr.wf
  -- the second probe: `v.value x (succ y) ≡ v.value (2 * x) y`
  refine .bind (isDefEq.WF
    (TrTerm.natBinApp (P.hv tyeq m) hx1 (.natUnApp (succb hnat) hy)).trS
    (TrTerm.natBinApp (P.hv tyeq m) (.natBinApp (mulb hmul) (twob hnat) hx1) hy).trS)
    fun _ _ _ hb2 => elseFail ((fun hb2' => ?_) ∘ hb2)
  refine .pure <| P.mkResult (F := Nat.shiftLeft) (hok h1.2) hnat ?_ tyeq fun hvT => ?_
  · simp [primSpecs, hname]
  exact .of_first_arg_step_equations (congrArg List.length (hok h1.2).2)
    ctx.Ewf wf.hasPrimitives hnat Nat.mul 2 (wf.hasPrimitives.natMul hmul)
    (fun _ => rfl) (fun _ _ => rfl) hvT hb' hb2'

/-- `Nat.shiftRight`: `x >>> 0 ≡ x` and `x >>> succ y ≡ (x >>> y) / 2`, a binary step
whose second operand is a literal rather than the first argument. The guard names `Nat.div`. -/
theorem checkNatShiftRight.WF {ves : VEnvs} (wf : ves.WF env)
    (hname : v.name = ``Nat.shiftRight) :
    let c := .mk' wf .safe v.levelParams; Data v ci' c →
    (checkNatShiftRight v).WF c state fun _ _ => PrimitiveResult (ves.venv .safe) v ci' := by
  intro ctx P; rw [← ctx.withMLC_self]; unfold checkNatShiftRight
  refine .getEnv <| elseFail fun h1 => elseFail fun h2 => ?_
  simp at h1
  have hdiv := VContext.contains_primitive rfl h1.1
  have hnat := wf.hasPrimitives.natOfDiv ctx.Ewf.orderedStrong hdiv
  have tyeq := P.mkTyEq hnat (by simp [TrExprS.IsUnique]) (natCod hnat) h2
  refine .withNatProbe wf.hasPrimitives hnat .rfl ?_; intro idx m _ _ _ hres hx
  refine .bind (isDefEq.WF (TrTerm.natBinApp (P.hv tyeq m) hx (zerob hnat)).trS hx.trS)
    fun _ _ _ hb => elseFail ((fun hb' => ?_) ∘ hb)
  refine .withNatProbe wf.hasPrimitives hnat .rfl ?_; intro idy m cwf _ _ hres' hy
  let hx1 := hx.wk ctx.Ewf cwf.wf.tr.wf
  -- `v.value x (succ y) ≡ (v.value x y) / 2`: a binary step whose second operand is a
  -- literal rather than the first argument, over an identity base
  refine .bind (isDefEq.WF
    (TrTerm.natBinApp (P.hv tyeq m) hx1 (.natUnApp (succb hnat) hy)).trS
    (TrTerm.natBinApp (divb hdiv) (.natBinApp (P.hv tyeq m) hx1 hy) (twob hnat)).trS)
    fun _ _ _ hb2 => elseFail ((fun hb2' => ?_) ∘ hb2)
  refine .pure <| P.mkResult (F := Nat.shiftRight) (hok h1.2) hnat ?_ tyeq fun hvT => ?_
  · simp [primSpecs, hname]
  refine .of_binary_step_equations (congrArg List.length (hok h1.2).2)
    ctx.Ewf wf.hasPrimitives hnat Nat.div id (fun _ => 2) (wf.hasPrimitives.natDiv hdiv)
    (fun _ => ?_) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) hvT hb' hb2'
  simp [hx, TrTerm.fvar, VExpr.inst]

/-- `Char.ofNat`: no probes -- the branch only pins the recorded type to `Nat → Char`. The
`ensureType` call runs at `inferOnly := false`, so it produces `Char`'s translation rather than
assuming it; nothing else in the branch mentions `Char`. -/
theorem checkCharOfNat.WF {ves : VEnvs} (wf : ves.WF env)
    (hname : v.name = ``Char.ofNat) :
    let c := .mk' wf .safe v.levelParams; Data v ci' c →
    (checkCharOfNat v).WF c state fun _ _ => PrimitiveResult (ves.venv .safe) v ci' := by
  intro ctx P; rw [← ctx.withMLC_self]; unfold checkCharOfNat
  have hnat : ctx.env.contains ``Nat → (ves.venv .safe).contains ``Nat :=
    P.contains (by simp [Environment.primitives, NameSet.contains, NameSet.ofList])
  refine .getEnv <| elseFail fun h1 => ?_
  simp at h1; specialize hnat h1.1
  -- the `ensureType` call runs at `inferOnly := false`, so it *produces* `Char`'s translation
  -- and the fact that it is a type; nothing else in this branch mentions `Char`
  refine .bind (ensureType.WF' nofun nofun) fun _ _ _ ⟨ch, hch, _, _, _, _, hchT⟩ => ?_
  obtain ⟨rfl, hchAny⟩ := hch.const0_inv (Us' := v.levelParams) (Δ' := [(none, .vlam .nat)])
  refine elseFail fun h2 => .pure ?_
  refine P.mkResultTypeEq (T := .forallE .nat .char) (hok h1.2) (by simp [primSpecs, hname]) ?_
  exact TrExprS.unique (by simp [TrExprS.IsUnique]) (P.htype.eqv h2)
    (TrTy.forallE
      (.of (wf.hasPrimitives.trNat ctx.Ewf.orderedStrong hnat) (hNatT hnat (Δ := []) trivial))
      (.of hchAny ⟨_, hchT.weak0 ctx.Ewf.ordered⟩)).trS

/-- `String.ofList`: the recorded type is `List Char → String`, and the two `checkType`
calls settle `List.nil` and `List.cons` at `Char` -- the spec's other two clauses. -/
theorem checkStringOfList.WF {ves : VEnvs} (wf : ves.WF env)
    (hname : v.name = ``String.ofList) :
    let c := .mk' wf .safe v.levelParams; Data v ci' c →
    (checkStringOfList v).WF c state fun _ _ => PrimitiveResult (ves.venv .safe) v ci' := by
  intro ctx P; rw [← ctx.withMLC_self]; unfold checkStringOfList
  refine elseFail fun h1 => ?_
  -- checking `List Char` at `inferOnly := false` also settles `Char`, so the second
  -- `ensureType` can stay in the cheap mode: its obligation is discharged from this one
  refine .bind (ensureType.WF' (by simp [FVarsIn, Level.hasMVar']) nofun)
    fun _ _ _ ⟨lc, hlc, _, _, _, _, hlcT⟩ => ?_
  cases hlc.appChar_inv' (Δ' := []) ctx.Ewf.orderedStrong |>.1
  have hchAny {Δ} := (hlc.appChar_inv' (Δ' := Δ) ctx.Ewf.orderedStrong).2
  refine .bind (ensureType.WF' nofun fun _ => ⟨_, hchAny.2⟩)
    fun _ _ _ ⟨ch, hch, _, _, _, _, hchT⟩ => ?_
  cases hch.const0_inv (Us' := v.levelParams) (Δ' := []) |>.1
  let charTy {Δ} : TrTy ctx.venv v.levelParams Δ q(Char) :=
    .of hchAny.2 ⟨_, hchT.weak0 ctx.Ewf.ordered⟩
  let lcTy {Δ} : TrTy ctx.venv v.levelParams Δ q(List Char) :=
    .of hchAny.1 ⟨_, hlcT.weak0 ctx.Ewf.ordered⟩
  -- `List.nil` and `List.cons` at `Char`, whose typings the spec records
  refine .bind (checkType.WF (by simp [FVarsIn, Level.hasMVar']))
    fun _ _ _ ⟨_, _, _, hnil, hnilty, hnilT⟩ => ?_
  cases hnil.appChar_inv
  refine .bind (isDefEq.WF hnilty hchAny.1) fun _ _ _ hb => elseFail ((fun hb' => ?_) ∘ hb)
  refine .bind (checkType.WF (by simp [FVarsIn, Level.hasMVar']))
    fun _ _ _ ⟨_, _, _, hcons, hconsty, hconsT⟩ => ?_
  cases hcons.appChar_inv
  refine .bind (isDefEq.WF hconsty (TrTy.forallE charTy (TrTy.forallE lcTy lcTy)).trS)
    fun _ _ _ hb => elseFail ((fun hb2' => ?_) ∘ hb)
  refine elseFail fun h2 => .pure ?_
  -- the spec's three clauses: the recorded type from `v.type`, and the two constructor
  -- typings from the `checkType` calls, retyped along their `isDefEq` results. All are
  -- monotone, so they transfer to the extension.
  have tyeq := TrExprS.listCharStringArrow_inv (P.htype.eqv h2)
  have hmem : (v.name, .stringOfList) ∈ primSpecs := by simp [primSpecs, hname]
  refine ⟨(hok h1).1, (hok h1).2, fun hle hwf hprim htr hciv hadd => ?_⟩
  have hnm : v.name = ci'.name := htr.1.2
  have huv : ci'.uvars = 0 := P.uvars_eq (hok h1)
  have hlen : v.levelParams.length = 0 := congrArg List.length (hok h1).2
  have le := hle.trans <| (VEnv.addConst_le hadd).trans (VEnv.addDefEq_le (df := ci'.toDefEq))
  refine hprim.addPrimitiveDefEq hadd (s₀ := .stringOfList) (hnm ▸ hmem) fun ci hci => ?_
  simp [VEnv.addDefEq] at hci; rw [VEnv.addConst_self hadd] at hci; cases hci
  exact ⟨by rw [← huv, ← tyeq],
    (hlen ▸ hnilT.defeqU_r ctx.Ewf ctx.Δwf hb').mono le,
    (hlen ▸ hconsT.defeqU_r ctx.Ewf ctx.Δwf hb2').mono le⟩
