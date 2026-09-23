import Lean4Lean.Verify.Environment.Primitive.Recursion

namespace Lean4Lean
open Lean4Lean TypeChecker
open Lean hiding Environment Exception
open Kernel

namespace Primitive

/-- An operator that reflects `g`, at two arguments that are worth boolean literals: the
application is a `Bool`, and it is worth `g` at those literals.

`Nat.bitwise`'s operator is a *variable* of the recognizer's context, so a reflection is the only
thing its equation body knows about it -- and the equation body applies it to decisions, which
are worth literals rather than being them. -/
theorem boolOp2_apply (henv : env.WF) {g : Bool → Bool → Bool}
    (hfT : env.HasType U [] f .boolOp2)
    (hfg : ∀ p q, env.IsDefEqU U [] ((f.app (.boolLit p)).app (.boolLit q)) (.boolLit (g p q)))
    (ha : env.IsDefEqU U [] a (.boolLit ba))
    (hb : env.IsDefEqU U [] b (.boolLit bb)) (hwf : VExpr.WF env U [] ((f.app a).app b)) :
    env.HasType U [] ((f.app a).app b) .bool ∧
    env.IsDefEqU U [] ((f.app a).app b) (.boolLit (g ba bb)) := by
  obtain ⟨-, hfa⟩ := VExpr.WF.app_inv' henv trivial hfT (hwf.app_inv₂ henv trivial).1
  have hfa : env.HasType U [] (f.app a) (.forallE .bool .bool) := by
    simpa [VExpr.inst, VExpr.bool] using hfa
  obtain ⟨-, hab⟩ := VExpr.WF.app_inv' henv trivial hfa hwf
  refine ⟨by simpa [VExpr.inst, VExpr.bool] using hab, .trans henv trivial ?_ (hfg ba bb)⟩
  exact (VEnv.IsDefEqU.appN' henv trivial (xs := [a, b]) (ys := [VExpr.boolLit ba, .boolLit bb])
    ⟨_, hfT⟩ (.cons ha (.cons hb .nil)) (by simpa [VExpr.appN] using hwf) :)

theorem checkNatBitwise.WF {ves : VEnvs} (wf : ves.WF env)
    (hname : v.name = ``Nat.bitwise) :
    let c := .mk' wf .safe v.levelParams; Data v ci' c →
    (checkNatBitwise v).WF c state fun _ _ => PrimitiveResult (ves.venv .safe) v ci' := by
  intro ctx P; rw [← ctx.withMLC_self]; unfold checkNatBitwise
  have hnat : ctx.env.contains ``Nat → (ves.venv .safe).contains ``Nat :=
    P.contains (by simp [Environment.primitives, NameSet.contains, NameSet.ofList])
  refine .getEnv <| elseFail fun h1 => elseFail fun h2 => ?_
  simp at h1; specialize hnat h1.1.1
  have hbool : (ves.venv .safe).contains ``Bool := VContext.contains_primitive rfl h1.1.2
  have hE := ctx.Ewf.orderedStrong
  have hlp : ctx.lparams.length = 0 := congrArg List.length (hok h1.2).2
  have tyeq := P.mkTyEqBitwise hnat hbool h2
  -- the two conditions the equation body is built out of: `n = 0`/`m = 0` on the one hand, and
  -- the operator's own boolean decisions on the other
  refine Condition.check.WF hnat hbool rfl .throw |>.bind fun _ _ _ ⟨wc, hcite, hcdite⟩ => ?_
  refine Condition.check.WF hnat hbool rfl .throw |>.bind fun _ _ _ ⟨wb, hbite, _⟩ => ?_
  -- the operator binder: everything past here runs one binder deep, which is what the
  -- recognizer's base-context form is for
  refine M.WF.withLocalDecl (m := ctx.mlctx) (boolOp2Ty hbool).trS (boolOp2Ty hbool).isType
    .rfl fun idf => let mf := _; fun (cwff : (ctx.withMLC ctx.mlctx).MLCWF mf) s' hs hres => ?_
  have trNatS {Δ} := wf.hasPrimitives.trNat (Us := ctx.lparams) hE hnat (Δ := Δ)
  -- the operator variable, as a bundle: its type is closed, so the binder's lift is the identity
  have hfT : (ctx.withMLC _ (wf := cwff)).HasType (.bvar 0) .boolOp2 := .bvar .zero
  -- the value at the operator variable. Naming its translation is what lets the reflection at
  -- the end be read as one about `ci'.value` applied.
  have hev : (ctx.withMLC mf (wf := cwff)).TrExprS (v.value.app (.fvar idf))
      (ci'.value.app (.bvar 0)) :=
    ((P.hv tyeq mf (cwf := cwff)).app' (⟨.bvar 0, .fvar VLCtx.find?_vlam_self, hfT⟩ :
      TrTerm ctx.venv ctx.lparams _ (.fvar idf) .boolOp2)).trS
  refine unfoldNatWellFounded.WF₂ (c := ctx.withMLC ctx.mlctx) (m₀ := mf) hev
      hnat rfl (hbite rfl).1 (hbite rfl).2 .throw |>.bind fun _ _ _ ⟨PB, hpr, hplen, hdone⟩ => ?_
  subst hpr
  -- the two recursion variables
  refine .withNatProbe (m := mf) wf.hasPrimitives hnat .rfl ?_; intro idn mn cwfn _ _ _ hn
  refine .withNatProbe wf.hasPrimitives hnat .rfl ?_; intro idm mnm cwfm _ _ _ hm
  let hn1 := hn.wk ctx.Ewf cwfm.wf.tr.wf
  -- the probe. `R` is what the equation body is worth: at literals, and at an operator that
  -- reflects `g`, it is `Nat.bitwise g` -- given the recursive call at the halves, which is what
  -- `Done` will supply.
  refine .mono (ProbeBundle.probe.WF (c := ctx.withMLC ctx.mlctx) (m := mf) (mp := mnm) (P := PB)
    (R := fun E γ ih vv => ∀ (g : Bool → Bool → Bool) (x y : Nat),
      γ 1 = .natLit x → γ 0 = .natLit y →
      E.venv.ReflectsBoolBoolBool' (γ 2) g →
      (x ≠ 0 → ∀ arg hy, E.IsDefEqU₀ arg
          ((PB.pack'.subst γ.tail.tail).appN [.natLit (x/2), .natLit (y/2)]) →
        E.WF₀ ((ih.app arg).app hy) →
        E.IsDefEqU₀ ((ih.app arg).app hy) (.natLit (Nat.bitwise g (x/2) (y/2)))) →
      E.IsDefEqU₀ vv (.natLit (Nat.bitwise g x y)))
    (.skip_fvar _ _ (.skip_fvar _ _ .refl)) .throw
    (.cons hn1.trS (.cons hm.trS .nil)) hnat (by simp [hplen])
    (List.forall_mem_pair hn1.hasType hm.hasType) (fun id => ?_)) fun _ _ _ heq => ?_
  · intro m' cwf2; refine ⟨?_, fun hcl rhsv hrhs E γ ih hγ hihT g x y hx hy hfg IH => ?_⟩
    · -- the equation body mentions only the probe's own variables and the packer, so unfolding
      -- the conditional builders leaves nothing but those memberships
      have hpk := PB.hpack.weakFV hE.ordered
        (.skip_fvar _ _ (.skip_fvar _ _ (.skip_fvar _ _ .refl))) cwf2.wf.tr.wf |>.fvarsIn
      simp only [Condition.dite, Condition.ite, Condition.decide, Condition.natEq, Condition.bool,
        mkApp4, mkAppN, Expr.lam0, add, div, mod, one, two, zero, succ]
      simp [FVarsIn, mkAppB, Level.hasMVar', mnm, mn, mf, MLCtx.vlctx, VLCtx.fvars] at hpk ⊢
      exact hpk
    -- the equation body: one `dite` on `n = 0`, then three `ite`s on the operator's decisions
    have ⟨P0, D0, t0', e0', hP0, hD0, ht0, he0, hshape0⟩ := Condition.dite_tr_inv
      (by simp [Condition.natEq, Expr.mkAppN_eq, Expr.appN, noProj, zero]) hrhs
    -- the probe's variables, at the `ih` context
    let hnΔ := hn1.wk ctx.Ewf cwf2.wf.tr.wf
    let hmΔ := hm.wk ctx.Ewf cwf2.wf.tr.wf
    let hfb : TrTerm ctx.venv ctx.lparams mf.vlctx (Expr.fvar idf) .boolOp2 :=
      ⟨.bvar 0, .fvar VLCtx.find?_vlam_self, hfT⟩
    let hfΔ := ((hfb.wk ctx.Ewf cwfn.wf.tr.wf).wk ctx.Ewf cwfm.wf.tr.wf).wk ctx.Ewf cwf2.wf.tr.wf
    have hiΔ : TrExprS ctx.venv ctx.lparams m'.vlctx (Expr.fvar id) (.bvar 0) :=
      .fvar VLCtx.find?_vlam_self
    have hlitT {k Γ} : ctx.venv.HasType ctx.lparams.length Γ (.natLit k) .nat :=
      wf.hasPrimitives.natLitT hE hnat k Γ
    have hlitR k : E.IsDefEqU₀ (.natLit k) (.natLit k) := ⟨_, E.monoT hlitT⟩
    have hlit0 {σ} k : E.IsDefEqU₀ (.subst (.natLit k) σ) (.natLit k) := by
      rw [VExpr.subst_natLit]; exact hlitR k
    have hboolT b : E.venv.HasType ctx.lparams.length [] (.boolLit b) .bool :=
      E.monoT (TrExprS.boolLit (Us := ctx.lparams) (Δ := []) wf.hasPrimitives hbool b).2
    have hbeq {σ} b : E.IsDefEqU₀ (.subst (.boolLit b) σ) (.boolLit b) := by
      rw [VExpr.subst_boolLit]; exact ⟨_, hboolT b⟩
    have htwo {Y pf B'} (hB : TrExprS ctx.venv ctx.lparams ((none, .vlam Y) :: m'.vlctx) two B') :
        E.IsDefEqU₀ (B'.subst ((γ.cons ih).cons pf)) (.natLit 2) :=
      TrExprS.unique (by simp [TrExprS.IsUnique, two, one, zero, succ]) hB (twob hnat).trS ▸ hlit0 2
    have hone {Y pf B'} (hB : TrExprS ctx.venv ctx.lparams ((none, .vlam Y) :: m'.vlctx) one B') :
        E.IsDefEqU₀ (B'.subst ((γ.cons ih).cons pf)) (.natLit 1) :=
      TrExprS.unique (by simp [TrExprS.IsUnique, one, succ, zero]) hB (oneb hnat).trS ▸ hlit0 1
    -- peeling a ground application: how the well-formedness of every piece of the equation body
    -- is read off the conditional's own
    have pk {f a : VExpr} (h : (f.app a).WF E.venv ctx.lparams.length []) := h.app_inv₂ E.wf trivial
    -- a translation at the recognizer's context, moved under a branch's own binder
    have hunder {Y e e'} (h : TrExprS ctx.venv ctx.lparams m'.vlctx e e') :
        TrExprS ctx.venv ctx.lparams ((none, .vlam Y) :: m'.vlctx) e e'.lift :=
      .underBV hE m'.noBV h
    -- what the operator is worth at the closing: `hfg` at the level count the branch runs in
    have hfgT : E.venv.HasType ctx.lparams.length [] (γ 2) .boolOp2 := by
      rw [hlp]; exact hfg.1
    have hfgE : ∀ p q, E.venv.IsDefEqU ctx.lparams.length []
        (((γ 2).app (.boolLit p)).app (.boolLit q)) (.boolLit (g p q)) := by
      rw [hlp]; exact hfg.2
    -- one of the operator's own conditionals, at a closing: the operator reflects `g`, so the
    -- conditional is worth the branch `g` selects at its two decisions. All three of them sit one
    -- binder inside the outer `dite`, which is what `Y` and `pf` stand for.
    have hboolStep {Y pf a b α' Pb Db a' b' t' e'} (ba bb : Bool)
        (hua : noProj a) (hub : noProj b)
        (hα : TrExprS ctx.venv ctx.lparams ((none, .vlam Y) :: m'.vlctx) q(Nat) α')
        (hPb : TrExprS ctx.venv ctx.lparams ((none, .vlam Y) :: m'.vlctx)
          (mkAppN Condition.bool.prop #[mkApp2 (.fvar idf) a b]) Pb)
        (hDb : TrExprS ctx.venv ctx.lparams ((none, .vlam Y) :: m'.vlctx)
          (mkAppN Condition.bool.dec #[mkApp2 (.fvar idf) a b]) Db)
        (ha' : TrExprS ctx.venv ctx.lparams ((none, .vlam Y) :: m'.vlctx) a a')
        (hb' : TrExprS ctx.venv ctx.lparams ((none, .vlam Y) :: m'.vlctx) b b')
        (hea : E.IsDefEqU₀ (a'.subst ((γ.cons ih).cons pf)) (.boolLit ba))
        (heb : E.IsDefEqU₀ (b'.subst ((γ.cons ih).cons pf)) (.boolLit bb))
        (hwf : E.WF₀ ((iteApp α' Pb Db t' e').subst ((γ.cons ih).cons pf))) :
        E.IsDefEqU₀ ((iteApp α' Pb Db t' e').subst ((γ.cons ih).cons pf)) <|
          if g ba bb then t'.subst ((γ.cons ih).cons pf) else e'.subst ((γ.cons ih).cons pf) := by
      cases TrExprS.unique (by simp [TrExprS.IsUnique]) hα trNatS
      obtain ⟨_, hPa, rfl⟩ :=
        TrExprS.app1_nil_inv hE.ordered (by simp [Condition.bool, noProj]) wb.hprop0 hPb
      obtain ⟨_, hDa, rfl⟩ :=
        TrExprS.app1_nil_inv hE.ordered (by simp [Condition.bool, noProj]) wb.hdec0 hDb
      cases TrExprS.unique (noProj.isUnique (by simp [noProj, hua, hub])) hDa hPa
      obtain ⟨_, _, _, hf, ha2, hb2, rfl⟩ := hPa.app2_inv
      cases TrExprS.fvar_lift_uniq hfΔ.trS hf
      cases (TrExprS.unique (noProj.isUnique hua) ha2 ha').symm
      cases (TrExprS.unique (noProj.isUnique hub) hb2 hb').symm
      -- the operator variable is three binders down, so the closing sends it to `γ 2`
      have hfeq : (hfΔ.tgt.lift).subst ((γ.cons ih).cons pf) = γ 2 := by
        simp [hfΔ, hfb, TrTerm.wk, VExpr.lift, VExpr.liftN, liftVar, VExpr.Subst.cons]
      -- the conditional's own pieces are closed, so the closing only reaches the decision
      simp only [iteApp, VExpr.subst, wb.propC.subst_eq', wb.decC.subst_eq', hfeq] at hwf ⊢
      -- the decision: the operator at the two boolean values it is applied to
      obtain ⟨hbeT, hbeeq⟩ := boolOp2_apply E.wf hfgT hfgE hea heb
        (pk (pk (pk (pk (pk hwf).1).1).1).2).2
      exact (hbite rfl).2 E.cast (Γ := []) (args' := [_])
        (g ba bb) (fun _ => rfl) trivial (.cons hbeT .nil) rfl hbeeq hwf
    -- the closing of the `ih` context, and where the two recursion variables land under it
    have hclS := hcl E γ ih hγ hihT
    have hxs : hnΔ.tgt.subst (γ.cons ih) = .natLit x := by
      simp [hnΔ, hn1, hn, TrTerm.wk, TrTerm.fvar, VExpr.liftN, VExpr.Subst.cons, hx]
    have hys : hmΔ.tgt.subst (γ.cons ih) = .natLit y := by
      simp [hmΔ, hm, TrTerm.wk, TrTerm.fvar, VExpr.liftN, VExpr.Subst.cons, hy]
    -- the outer condition is `natEq` at the first recursion variable and `0`
    obtain ⟨_, _, hP0n, hP0z, rfl⟩ := wc.prop_app2_inv hP0
    obtain ⟨_, _, hD0n, hD0z, rfl⟩ := wc.dec_app2_inv hD0
    cases TrExprS.unique (by simp [TrExprS.IsUnique]) hP0n hnΔ.trS
    cases TrExprS.unique (by simp [TrExprS.IsUnique]) hD0n hnΔ.trS
    cases TrExprS.unique (by simp [TrExprS.IsUnique, zero]) hP0z (zerob hnat).trS
    cases TrExprS.unique (by simp [TrExprS.IsUnique, zero]) hD0z (zerob hnat).trS
    subst hshape0
    have hwfr0 : E.WF₀ _ := E.monoW (hrhs.wf hE.ordered cwf2.wf.tr.wf) |>.subst E.wf hclS
    simp only [diteApp, VExpr.subst, wc.propC.subst_eq', wc.decC.subst_eq', hxs, zerob,
      TrTerm.natZero, TrTerm.of] at hwfr0 ⊢
    obtain ⟨pf0, hev0⟩ := wc.natEq_diteEval (hcdite rfl).2.1 wf.hasPrimitives hnat E.cast
      (hlitR x) (hlitR 0) (by simpa [VExpr.WF, diteApp, VExpr.natLit] using hwfr0)
    refine hev0.trans E.wf trivial ?_
    have hwfif : E.WF₀ _ := ⟨_, hev0.choose_spec.hasType.2⟩
    -- selecting a branch instantiates its binder, which is closing one more variable
    have hbeta {A e : VExpr} (h : E.WF₀ (.app (.lam A (e.subst (γ.cons ih).lift)) pf0)) :
        E.IsDefEqU₀ (.app (.lam A (e.subst (γ.cons ih).lift)) pf0)
          (e.subst ((γ.cons ih).cons pf0)) := by
      have := (h.betaU E.wf trivial).2
      rwa [VExpr.inst_eq, VExpr.subst_subst, VExpr.Subst.lift_comp_one] at this
    -- the operator applied to two decisions, inside the `bool` condition's proposition
    have hbargs {Y a b r}
        (h : TrExprS ctx.venv ctx.lparams ((none, .vlam Y) :: m'.vlctx)
          (mkAppN Condition.bool.prop #[mkApp2 (.fvar idf) a b]) r) :
        ∃ f' a' b' : VExpr,
          TrExprS ctx.venv ctx.lparams ((none, .vlam Y) :: m'.vlctx) a a' ∧
          TrExprS ctx.venv ctx.lparams ((none, .vlam Y) :: m'.vlctx) b b' ∧
          r = wb.prop'.app ((f'.app a').app b') := by
      obtain ⟨_, hab, rfl⟩ := TrExprS.app1_nil_inv hE.ordered (by simp [Condition.bool, noProj]) wb.hprop0 h
      obtain ⟨_, _, _, _, ha, hb, rfl⟩ := hab.app2_inv
      exact ⟨_, _, _, ha, hb, rfl⟩
    -- `natEq.decide #[mod v two, one]` at a closing: the `Nat.mod` evaluates and the reflected
    -- equality decides. `Nat.mod` is not guarded by the branch -- its containment comes from the
    -- translation, which is `natBinLitTr`'s business.
    have hdecide {Y pf v v' r} (a : Nat) (hv : noProj v)
        (hvt : TrExprS ctx.venv ctx.lparams ((none, .vlam Y) :: m'.vlctx) v v')
        (hva : E.IsDefEqU₀ (v'.subst ((γ.cons ih).cons pf)) (.natLit a))
        (hr : TrExprS ctx.venv ctx.lparams ((none, .vlam Y) :: m'.vlctx)
          (Condition.natEq.decide #[mod v two, one]) r)
        (hwfr : E.WF₀ (r.subst ((γ.cons ih).cons pf))) :
        E.IsDefEqU₀ (r.subst ((γ.cons ih).cons pf)) (.boolLit (Nat.beq (a % 2) 1)) := by
      refine wc.natEq_decideTr (hcite rfl).2 wf.hasPrimitives hnat hbool E.cast (a % 2) 1
        ?_ ?_ (fun hB _ => hone hB) hr hwfr (hA := fun hA hW =>
          E.natBinLitTr a 2 wf.hasPrimitives.natMod (fun hA2 _ => ?_) (fun hB _ => htwo hB) hA hW)
      · simp [two, one, zero, succ, noProj, mkApp, hv]
      · simp [one, zero, succ, noProj]
      · exact TrExprS.unique (noProj.isUnique hv) hA2 hvt ▸ hva
    cases hb0 : Nat.beq x 0 with
    | true =>
      let 0 := x
      refine hbeta hwfif |>.trans E.wf trivial ?_
      -- `bitwise g 0 y = if g false true then y else 0`
      obtain ⟨α1', P1, D1, t1', e1', hα1, hP1, hD1, ht1, he1, rfl⟩ := Condition.ite_tr_inv' ht0
      have hwft0 : E.WF₀ _ := ⟨_, (hbeta hwfif).choose_spec.hasType.2⟩
      refine hboolStep false true (by decide) (by decide) hα1 hP1 hD1
        (TrExprS.boolLit wf.hasPrimitives hbool false).1
        (TrExprS.boolLit wf.hasPrimitives hbool true).1
        (hbeq false) (hbeq true) hwft0 |>.trans E.wf trivial ?_
      cases TrExprS.fvar_lift_uniq hmΔ.trS ht1
      cases TrExprS.unique (by simp [TrExprS.IsUnique, zero]) he1
        (TrExprS.natZero wf.hasPrimitives hnat).1
      rw [show Nat.bitwise g 0 y = if g false true then y else 0 by rw [Nat.bitwise]; simp]
      simp only [VExpr.lift_subst, VExpr.Subst.cons_tail, hys, VExpr.natZero, VExpr.subst]
      cases g false true <;> simp <;> first | exact hlitR 0 | exact hlitR y
    | false =>
      simp only [hb0, Bool.false_eq_true, if_false] at hwfif ⊢
      refine hbeta hwfif |>.trans E.wf trivial ?_
      have hx0 : x ≠ 0 := by rintro rfl; simp at hb0
      -- the second condition, `m = 0`, at the same closing
      obtain ⟨α2', P2, D2, t2', e2', hα2, hP2, hD2, ht2, he2, rfl⟩ := Condition.ite_tr_inv' he0
      have hwfe0 : E.WF₀ _ := ⟨_, (hbeta hwfif).choose_spec.hasType.2⟩
      obtain ⟨_, _, hP2n, hP2z, rfl⟩ := wc.prop_app2_inv hP2
      obtain ⟨_, _, hD2n, hD2z, rfl⟩ := wc.dec_app2_inv hD2
      cases TrExprS.fvar_lift_uniq hmΔ.trS hP2n
      cases TrExprS.fvar_lift_uniq hmΔ.trS hD2n
      cases TrExprS.unique (by simp [TrExprS.IsUnique, zero]) hP2z
        (TrExprS.natZero wf.hasPrimitives hnat).1
      cases TrExprS.unique (by simp [TrExprS.IsUnique, zero]) hD2z
        (TrExprS.natZero wf.hasPrimitives hnat).1
      cases TrExprS.unique (by simp [TrExprS.IsUnique]) hα2 trNatS
      simp only [iteApp, VExpr.subst, VExpr.lift_subst, VExpr.Subst.cons_tail,
        wc.propC.subst_eq', wc.decC.subst_eq', hys, VExpr.natZero] at hwfe0 ⊢
      have hev2 := wc.natEq_iteEval (hcite rfl).2 wf.hasPrimitives hnat E.cast
        (hlitR y) (hlitR 0) (by simpa [VExpr.WF, iteApp, VExpr.natLit, VExpr.natZero] using hwfe0)
      refine hev2.trans E.wf trivial ?_
      have hwfif2 : E.WF₀ _ := ⟨_, hev2.choose_spec.hasType.2⟩
      cases hb2 : Nat.beq y 0 with
      | true =>
        let 0 := y
        -- `bitwise g x 0 = if g true false then x else 0`
        obtain ⟨α3', P3, D3, t3', e3', hα3, hP3, hD3, ht3, he3, rfl⟩ := Condition.ite_tr_inv' ht2
        refine hboolStep true false (by decide) (by decide) hα3 hP3 hD3
          (TrExprS.boolLit wf.hasPrimitives hbool true).1
          (TrExprS.boolLit wf.hasPrimitives hbool false).1
          (hbeq true) (hbeq false) hwfif2 |>.trans E.wf trivial ?_
        cases TrExprS.fvar_lift_uniq hnΔ.trS ht3
        cases TrExprS.unique (by simp [TrExprS.IsUnique, zero]) he3
          (TrExprS.natZero wf.hasPrimitives hnat).1
        rw [show Nat.bitwise g x 0 = if g true false then x else 0 by
          rw [Nat.bitwise]; simp [hx0]]
        simp only [VExpr.lift_subst, VExpr.Subst.cons_tail, hxs, VExpr.natZero, VExpr.subst]
        cases g true false <;> simp <;> [exact hlitR 0; exact hlitR x]
      | false =>
        simp only [hb2, Bool.false_eq_true, if_false] at hwfif2 ⊢
        have hy0 : y ≠ 0 := by rintro rfl; simp at hb2
        -- the last conditional: the operator at the two low bits
        obtain ⟨α4', P4, D4, t4', e4', hα4, hP4, hD4, ht4, he4, rfl⟩ := Condition.ite_tr_inv' he2
        obtain ⟨_, b1v, b2v, hb1, hb2', rfl⟩ := hbargs hP4
        -- the branch binder's type, and the closing extended by its proof
        cases hrhs with | app _ _ _ helam
        cases helam with | lam hYT _ _
        refine let Y := _
          have hΔ1WF : VLCtx.WF ctx.venv ctx.lparams.length ((none, .vlam Y) :: m'.vlctx) :=
            ⟨cwf2.wf.tr.wf, nofun, hYT⟩; ?_
        have hS1 := VEnv.Ctx.SubstEq.cons (σ := (γ.cons ih).cons pf0) (σ' := (γ.cons ih).cons pf0)
            hclS (E.monoT hYT.choose_spec) <| by
          simpa only [VExpr.Subst.cons_tail, VExpr.Subst.cons_head, VExpr.subst, wc.propC.subst_eq',
            wc.decC.subst_eq', hxs, zerob, TrTerm.natZero, TrTerm.of, VExpr.natZero,
            VContext.withMLC, VEnv.HasType] using (VExpr.WF.betaU E.wf trivial hwfif).1
        -- the well-formedness of every piece, read off the conditional's own
        have hwfit := by
          simpa only [iteApp, VExpr.subst, VContext.Ext.WF₀, VContext.withMLC] using hwfif2
        have hwfP4 := (pk (pk (pk (pk hwfit).1).1).1).2
        have hwfbe := (pk hwfP4).2
        have hwfb2 := (pk hwfbe).2
        have hwfb1 := (pk (pk hwfbe).1).2
        have hxs' : E.IsDefEqU₀ ((hnΔ.tgt.lift).subst ((γ.cons ih).cons pf0)) (.natLit x) := by
          rw [VExpr.lift_subst, VExpr.Subst.cons_tail, hxs]; exact hlitR x
        have hys' : E.IsDefEqU₀ ((hmΔ.tgt.lift).subst ((γ.cons ih).cons pf0)) (.natLit y) := by
          rw [VExpr.lift_subst, VExpr.Subst.cons_tail, hys]; exact hlitR y
        have hval1 := hdecide x (by simp [noProj]) (hunder hnΔ.trS) hxs' hb1 hwfb1
        have hval2 := hdecide y (by simp [noProj]) (hunder hmΔ.trS) hys' hb2' hwfb2
        have hunoProj {w} (hw : noProj w) : noProj (Condition.natEq.decide #[mod w two, one]) := by
          simp [Condition.decide, Condition.ite, Condition.natEq, mkApp5, mkApp4, mkApp2, mkApp,
            mkAppN, mkAppB, noProj, mod, two, one, zero, succ, hw]
        refine hboolStep (Nat.beq (x % 2) 1) (Nat.beq (y % 2) 1)
          (hunoProj (by simp [noProj])) (hunoProj (by simp [noProj]))
          hα4 hP4 hD4 hb1 hb2' hval1 hval2 hwfif2 |>.trans E.wf trivial ?_
        -- the recursive call: `ih` at the packer's value on the two halves
        have hpk := PB.hpack.weakFV hE.ordered
          (.skip_fvar _ _ (.skip_fvar _ _ (.skip_fvar _ _ .refl))) cwf2.wf.tr.wf
        have hrval {pfe r'}
            (hr' : TrExprS ctx.venv ctx.lparams ((none, .vlam Y) :: m'.vlctx)
              (mkApp2 (.fvar id)
                (mkApp2 PB.pack (div (.fvar idn) two) (div (.fvar idm) two)) pfe) r')
            (hwfr' : E.WF₀ (r'.subst ((γ.cons ih).cons pf0))) :
            E.IsDefEqU₀ (r'.subst ((γ.cons ih).cons pf0))
              (.natLit (Nat.bitwise g (x / 2) (y / 2))) := by
          obtain ⟨ihv, packv, pfv, hihv, hpackv, hpfv, rfl⟩ := hr'.app2_inv
          cases TrExprS.fvar_lift_uniq hiΔ hihv
          obtain ⟨pkv, d1v, d2v, hpkv, hd1, hd2, rfl⟩ := hpackv.app2_inv
          have hwfpack := (pk (pk hwfr').1).2
          have ⟨hwfd1, hwfd2⟩ := pk hwfpack
          have ⟨hwfpk, hwfd1⟩ := pk hwfd1
          have hd1val := E.natBinLitTr x 2 wf.hasPrimitives.natDiv
            (fun hA _ => TrExprS.unique (by simp [TrExprS.IsUnique]) hA (hunder hnΔ.trS) ▸ hxs')
            (fun hB _ => htwo hB) hd1 hwfd1
          have hd2val := E.natBinLitTr y 2 wf.hasPrimitives.natDiv
            (fun hA _ => TrExprS.unique (by simp [TrExprS.IsUnique]) hA (hunder hmΔ.trS) ▸ hys')
            (fun hB _ => htwo hB) hd2 hwfd2
          -- the packer's head is only a *translation* of `pack`, so it is `pack'` up to defeq
          have hpkeq : E.IsDefEqU₀ (pkv.subst ((γ.cons ih).cons pf0))
              (PB.pack'.subst γ.tail.tail) := by
            have h := TrExprS.uniq ctx.Ewf (VLCtx.IsDefEq.refl hE hΔ1WF) hpkv (hunder hpk)
            have h2 := (E.mono h).subst E.wf hS1
            simpa [VExpr.lift, VExpr.liftN_subst, VExpr.Subst.cons_tail, VLocalDecl.depth,
              Lift.skipN, VContext.Ext.IsDefEqU₀, VContext.withMLC] using h2
          have hpackeq := hpkeq.appN' E.wf trivial
            (xs := [d1v.subst ((γ.cons ih).cons pf0), d2v.subst ((γ.cons ih).cons pf0)])
            (ys := [.natLit (x / 2), .natLit (y / 2)])
            (.cons hd1val (.cons hd2val .nil)) (by simpa [VExpr.appN] using hwfpack)
          refine IH hx0 _ _ ?_ ?_
          · simpa [VExpr.appN, VContext.Ext.IsDefEqU₀, VContext.withMLC] using hpackeq
          · simpa [VExpr.subst, VExpr.Subst.cons] using hwfr'
        have hdd := pk (pk hwfit).1
        have hval4 := E.natBinLitTr _ 1 wf.hasPrimitives.natAdd
          (E.natBinLitTr _ _ wf.hasPrimitives.natAdd hrval hrval)
          (fun hB _ => hone hB) ht4 hdd.2
        have hval4' := E.natBinLitTr _ _ wf.hasPrimitives.natAdd hrval hrval he4 (pk hwfit).2
        rw [Nat.bitwise]; simp [hx0, hy0, ← Nat.beq_eq]
        split <;> [exact hval4; exact hval4']
  refine P.mkResultBitwise (hok h1.2) hnat ?_ tyeq fun env' hle hwf'' fv g hfg => ?_
  · simp [primSpecs, hname]
  have hlp : ctx.lparams.length = 0 := congrArg List.length (hok h1.2).2
  have hvalT : env'.HasType 0 [] ci'.value (.forallE .boolOp2 .natOp2) := by
    rw [← tyeq, ← P.uvars_eq (hok h1.2)]; exact P.hci.mono hle
  have hvalC : ci'.value.ClosedN := (P.hci.closedN' hE.ordered.closed trivial).1
  refine ⟨by simpa [VExpr.natOp2, VExpr.inst] using VEnv.HasType.app hvalT hfg.1, fun x y => ?_⟩
  -- the closing that instantiates the operator, and the recursion read at it
  have hγ : (VContext.Ext.cast (⟨env', hle, hwf''⟩ : (ctx.withMLC mf (wf := cwff)).Ext)).Closing
      (.cons .id fv) := by
    obtain ⟨u, hu⟩ := (boolOp2Ty (c := ctx) hbool).isType
    refine .cons .nil (hu.mono hle) ?_
    simp only [VContext.withMLC, hlp, VExpr.Subst.head, VExpr.Subst.cons, VExpr.Subst.id,
      VExpr.subst, boolOp2Ty, VExpr.boolOp2, VExpr.bool]
    exact hfg.1
  have hDone : PB.Done ⟨env', hle, hwf''⟩ (.cons .id fv)
      (fun (n, m) => [.natLit n, .natLit m]) (·.1) (fun (n, m) => Nat.bitwise g n m) := by
    rintro ⟨x', y'⟩ ih hihT IH
    simp only [ProbeBundle.arg, ProbeBundle.ihTy, ProbeBundle.Fc, ProbeBundle.packc,
      ProbeBundle.domc] at IH hihT ⊢
    -- the probe's own closing: the operator, then the two recursion arguments
    have hlit {k : Nat} {Γ} : env'.HasType ctx.lparams.length Γ (.natLit k) .nat := by
      rw [hlp]; exact (wf.hasPrimitives.natLitT hE hnat k Γ).mono hle
    have hnatTy {Γ} (h : OnCtx Γ (env'.IsType ctx.lparams.length)) :
        env'.IsType ctx.lparams.length Γ .nat := (hlit (k := 0)).isType hwf'' h
    have hbo : env'.IsType ctx.lparams.length [] .boolOp2 := by
      obtain ⟨u, hu⟩ := (boolOp2Ty (c := ctx) hbool).isType
      exact ⟨u, hu.mono hle⟩
    have hΓ1 : OnCtx [.boolOp2] (env'.IsType ctx.lparams.length) := ⟨trivial, hbo⟩
    obtain ⟨_, hnatT1⟩ := hnatTy hΓ1
    obtain ⟨_, hnatT2⟩ := hnatTy (Γ := [.nat, .boolOp2]) ⟨hΓ1, hnatTy hΓ1⟩
    have hγ1 : VEnv.Ctx.SubstEq env' ctx.lparams.length []
        ((VExpr.Subst.id.cons fv).cons (.natLit x'))
        ((VExpr.Subst.id.cons fv).cons (.natLit x')) [.nat, .boolOp2] := hγ.cons hnatT1 hlit
    have hγ2 : VEnv.Ctx.SubstEq env' ctx.lparams.length []
        (((VExpr.Subst.id.cons fv).cons (.natLit x')).cons (.natLit y'))
        (((VExpr.Subst.id.cons fv).cons (.natLit x')).cons (.natLit y'))
        [.nat, .nat, .boolOp2] := hγ1.cons hnatT2 hlit
    obtain ⟨vv, hRv, hlhs⟩ := heq ⟨env', hle, hwf''⟩ _ ih hγ2 <| by
      simpa [ProbeBundle.pihTy, ProbeBundle.parg, ProbeBundle.pγ, VLocalDecl.depth,
        VExpr.natLit, VExpr.Subst.cons, hn1, hm, hn, TrTerm.of, TrTerm.fvar, TrTerm.wk] using hihT
    refine .trans hwf'' trivial ?_ <| hRv g x' y' rfl rfl hfg fun hx0 arg hy harg hwfa => ?_
    · simpa [VContext.Ext.IsDefEqU₀, VContext.withMLC, ProbeBundle.plhs, ProbeBundle.parg,
        ProbeBundle.pγ, VLocalDecl.depth, VExpr.natLit, VExpr.Subst.cons, hn1, hm, hn,
        TrTerm.of, TrTerm.fvar, TrTerm.wk] using hlhs
    · exact IH (x'/2, y'/2) arg hy (Nat.div_lt_self (Nat.pos_of_ne_zero hx0) (by decide))
        (by simpa using harg) hwfa
  simpa [VContext.Ext.IsDefEqU₀, VContext.withMLC, hlp, VExpr.appN, VExpr.subst, hvalC.subst_eq',
    VExpr.Subst.cons] using hdone ⟨env', hle, hwf''⟩ (.cons .id fv) hγ _ hDone (x, y)
