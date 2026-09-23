import Lean4Lean.Verify.Environment.Primitive.Condition

namespace Lean4Lean
open Lean4Lean TypeChecker
open Lean hiding Environment Exception
open Kernel

namespace Primitive

/-- `Nat.mod`'s and `Nat.div`'s shared fuel recursion, verified once: the `≤` they are stated
with and the `go` they recurse through are checked, the condition their conditionals test is
checked, and then the two equations at the recursion's own variables.

What the caller gets back is its own top equation, untouched -- what that equation *is* differs
between the two, and taking it apart is the caller's business -- and `hfuel`, the recursion run
to the end: at literals, a well formed `go` call is worth `F x bb`.

The checker's parameters come back here at the level of the model: `lhsB` bundles what the top
equation applies the definition to, `H'` is what the step does to the recursive call and `E` what
the recursion returns when it stops. `F` and `hF` are what those are worth arithmetically, which
is `natFuelRec`'s business. -/
theorem checkNatFuelRec.WF {c : VContext} {ite : Bool}
    {F : Nat → Nat → Nat} {hF : Nat → Nat} {H' : VExpr → VExpr} {E : Nat → Nat}
    (hprim : c.venv.HasPrimitives) (hnat : c.venv.contains ``Nat)
    (hbool : c.venv.contains ``Bool) (hsub : c.venv.contains ``Nat.sub)
    (hnil : c.vlctx = []) (hlp : c.lparams.length = 0)
    (hv : ∀ m [c.MLCWF m],
      TrTerm c.venv c.lparams (c.withMLC m).vlctx v.value (.forallE .nat (.forallE .nat .nat)))
    (lhsB : ∀ {Δ e}, TrTerm c.venv c.lparams Δ e .nat → TrTerm c.venv c.lparams Δ (lhs e) .nat)
    -- the equation bodies mention only the variables the block introduced
    (htopFV : ∀ {P x y}, FVarsIn P x → FVarsIn P y →
      FVarsIn P (top (mkApp5 (.const goName [])) x y))
    (hHFV : ∀ {P e}, FVarsIn P e → FVarsIn P (H e))
    (helsFV : ∀ {P x}, FVarsIn P x → FVarsIn P (els x))
    -- the step, at the level of the model: it translates as itself, commutes with a closing,
    -- and is a congruence that computes at literals
    (hHtr : ∀ {Δ e X}, TrExprS c.venv c.lparams Δ (H e) X →
      ∃ X', TrExprS c.venv c.lparams Δ e X' ∧ X = H' X')
    (hHsubst : ∀ {e σ}, (H' e).subst σ = H' (e.subst σ))
    (hHinst : ∀ {e u}, (H' e).inst u = H' (e.inst u))
    (hHwf : ∀ {e}, c.WF₀ (H' e) → c.WF₀ e)
    (hHcong : ∀ {a b}, c.HasType₀ a .nat → c.IsDefEqU₀ a b → c.IsDefEqU₀ (H' a) (H' b))
    (hHlit : ∀ n, H' (.natLit n) = .natLit (hF n))
    -- and what the recursion returns when it stops, which is worth `E` at the dividend
    (hels : ∀ {Δ fv X v'},
      TrExprS c.venv c.lparams Δ (els (.fvar fv)) X →
      TrExprS c.venv c.lparams Δ (.fvar fv) v' →
      ∀ {σ xx}, v'.subst σ = .natLit xx →
      c.IsDefEqU₀ (X.subst σ) (.natLit (E xx)))
    (hFlt : ∀ bb x, x < bb → F x bb = E x)
    (hFstep : ∀ bb x, 0 < bb → bb ≤ x → F x bb = hF (F (x - bb) bb))
    (hbody : ∀ {m2} [c.MLCWF m2] {idx idy}
      (hx : TrTerm c.venv c.lparams (c.withMLC m2).vlctx (.fvar idx) .nat)
      (hy : TrTerm c.venv c.lparams (c.withMLC m2).vlctx (.fvar idy) .nat)
      {le' go'} (w : Condition.WF c Condition.natLE),
      (ite → w.WF_ite ∧ w.IteEval) → (w.WF_dite ∧ w.DiteEval ∧ w.DecT) →
      le'.ClosedN → go'.ClosedN →
      (∀ {Γ}, c.venv.HasType c.lparams.length Γ le' vexpr(Nat → Nat → Prop)) →
      (∀ {Δ}, TrExprS c.venv c.lparams Δ (.const goName []) go') →
      (∀ {Γ}, c.venv.HasType c.lparams.length Γ go' (natGoType le')) →
      (∀ a b, (c.withMLC m2).Closing ((VExpr.Subst.id.cons (.natLit a)).cons (.natLit b))) →
      hx.tgt = .bvar 1 → hy.tgt = .bvar 0 →
      ∀ {e1' e1Ty'},
        (c.withMLC m2).TrExprS (top (mkApp5 (.const goName [])) (.fvar idx) (.fvar idy)) e1' →
        (c.withMLC m2).HasType e1' e1Ty' →
        (c.withMLC m2).IsDefEqU (((hv m2).tgt.app (lhsB hx).tgt).app hy.tgt) e1' →
        (∀ f bb x pf pf', 0 < bb → x < f →
          let e := natGoCall go' (.natLit bb) pf (.natLit f) (.natLit x) pf'
          e.WF c.venv c.lparams.length [] → c.IsDefEqU₀ e (.natLit (F x bb))) → Q) :
    (checkNatFuelRec v goName ite lhs H els top).WF c s fun _ _ => Q := by
  -- `≤` on `Nat`, and the fuel-driven `go` the recursion runs through
  refine .bind (checkType.WF (.of_hasFVar rfl rfl rfl))
    fun _ _ _ ⟨le', leTy', _, hleTr, hleTyTr, hleT⟩ => ?_
  refine .bind (isDefEq.WF hleTyTr (TrExprS.natNatProp c.Ewf hprim hnat c.Δwf.toCtx))
    fun _ _ _ hb => elseFail ((fun hle => ?_) ∘ hb)
  have hleT' : c.venv.HasType c.lparams.length c.vlctx.toCtx le' vexpr(Nat → Nat → Prop) :=
    VEnv.HasType.defeqU_r c.Ewf c.Δwf.toCtx hle hleT
  rw [hnil] at hleT'
  have hleTrΓ {Δ} : TrExprS c.venv c.lparams Δ _ le' :=
    TrExprS.of_nil_any c.Ewf (by simp [noProj]) (hnil ▸ hleTr)
  have hleTΓ {Γ} : c.venv.HasType c.lparams.length Γ le' vexpr(Nat → Nat → Prop) :=
    .weak0 c.Ewf hleT'
  have hleC : le'.ClosedN := (hleT'.closedN' c.Ewf.ordered.closed trivial).1
  refine .bind (checkType.WF (.of_hasFVar rfl rfl rfl))
    fun _ _ _ ⟨go', goTy', _, hgoTr, hgoTyTr, hgoT⟩ => ?_
  refine .bind (isDefEq.WF hgoTyTr
    (TrExprS.divGoType c.Ewf hprim hnat (le' := le') hleTrΓ hleTΓ c.Δwf.toCtx))
    fun _ _ _ hb2 => elseFail ((fun hgo => ?_) ∘ hb2)
  have hgoT' : c.venv.HasType c.lparams.length c.vlctx.toCtx go' (natGoType le') :=
    VEnv.HasType.defeqU_r c.Ewf c.Δwf.toCtx hgo hgoT
  rw [hnil] at hgoT'
  have hgoTrΓ {Δ} : TrExprS c.venv c.lparams Δ _ go' :=
    TrExprS.of_nil_any c.Ewf (by simp [noProj]) (hnil ▸ hgoTr)
  have hgoTΓ {Γ} : c.venv.HasType c.lparams.length Γ go' (natGoType le') :=
    VEnv.HasType.weak0 c.Ewf hgoT'
  have hgoC : go'.ClosedN := (hgoT'.closedN' c.Ewf.ordered.closed trivial).1
  -- the condition, in both its `ite` and its `dite` form
  refine Condition.check.WF hnat hbool hnil .throw |>.bind fun _ _ _ ⟨w, hite, hdite⟩ => ?_
  have hdecC' : w.dec'.ClosedN := w.decC
  have hpropC' : w.prop'.ClosedN := w.propC
  obtain ⟨natU, hnatTy⟩ : c.venv.IsType c.lparams.length [] .nat :=
    hprim.natIsType' c.Ewf hnat trivial
  have hlitT k Γ : c.venv.HasType c.lparams.length Γ (.natLit k) .nat :=
    hprim.natLitT c.Ewf hnat k Γ
  have hnatTyΓ {Γ} : c.venv.HasType c.lparams.length Γ VExpr.nat (.sort natU) :=
    .weak0 c.Ewf hnatTy
  -- the check ran before any binder, so the identity closes what there is of the context
  have hγ0 : c.Closing VExpr.Subst.id := by
    show VEnv.Ctx.SubstEq _ _ _ _ _ (VLCtx.toCtx c.vlctx)
    rw [hnil]; exact .nil
  -- the two recursion variables, and the caller's top equation at them
  refine M.WF.withMLC_self ?_
  refine .withNatProbe (m := c.mlctx) hprim hnat .rfl ?_; intro idx m1 _ _ _ _ hx
  refine .withNatProbe hprim hnat .rfl ?_; intro idy m2 cwf2 _ _ _ hy
  let hx2 := hx.wk c.Ewf cwf2.wf.tr.wf
  refine .bind (checkType.WF (htopFV hx2.trS.fvarsIn hy.trS.fvarsIn))
    fun _ _ _ ⟨e1', e1Ty', _, he1Tr, _, he1T⟩ => ?_
  refine .bind (isDefEq.WF (TrTerm.natBinApp (hv m2) (lhsB hx2) hy).trS he1Tr)
    fun _ _ _ hb => elseFail ((fun heq1 => ?_) ∘ hb)
  have hγ2 a b : (c.withMLC m2).Closing ((VExpr.Subst.id.cons (.natLit a)).cons (.natLit b)) :=
    .cons (.cons hγ0 hnatTyΓ (hlitT a [])) hnatTyΓ (hlitT b [])
  -- `go`'s own equation, under `hy : 1 ≤ y`, `fuel` and `h : succ x ≤ succ fuel`
  let leb2 : TrTerm c.venv c.lparams (c.withMLC m2).vlctx _ vexpr(Nat → Nat → Prop) :=
    .of hleTrΓ hleTΓ
  let oneb2 : TrTerm c.venv c.lparams (c.withMLC m2).vlctx _ .nat :=
    .natUnApp (succb hnat) (zerob hnat)
  let hyTy := TrTerm.natBinApp leb2 oneb2 hy
  refine .withLocalDecl hyTy.trS ⟨_, hyTy.hasType⟩ .rfl ?_
  intro idhy cwf3 _ _ _
  let hhy3 : TrTerm c.venv c.lparams (c.withMLC _ (wf := cwf3)).vlctx (.fvar idhy) _ :=
    .fvar VLCtx.find?_vlam_self (.bvar .zero)
  let hx3 := hx2.wk c.Ewf cwf3.wf.tr.wf
  let hy3 := hy.wk c.Ewf cwf3.wf.tr.wf
  refine .withNatProbe hprim hnat .rfl ?_; intro idf m4 cwf4 _ _ _ hf
  let hx4 := hx3.wk c.Ewf cwf4.wf.tr.wf
  let hy4 := hy3.wk c.Ewf cwf4.wf.tr.wf
  let leb4 : TrTerm c.venv c.lparams (c.withMLC m4).vlctx _ vexpr(Nat → Nat → Prop) :=
    .of hleTrΓ hleTΓ
  let hhTy := TrTerm.natBinApp leb4 (.natUnApp (succb hnat) hx4) (.natUnApp (succb hnat) hf)
  refine .withLocalDecl hhTy.trS ⟨_, hhTy.hasType⟩ .rfl ?_
  intro idh cwf5 _ _ _
  let hhh5 : TrTerm c.venv c.lparams (c.withMLC _ (wf := cwf5)).vlctx (.fvar idh) _ :=
    .fvar VLCtx.find?_vlam_self (.bvar .zero)
  let hx5 := hx4.wk c.Ewf cwf5.wf.tr.wf
  let hy5 := hy4.wk c.Ewf cwf5.wf.tr.wf
  let hf5 := hf.wk c.Ewf cwf5.wf.tr.wf
  let hhy5 := (hhy3.wk c.Ewf cwf4.wf.tr.wf).wk c.Ewf cwf5.wf.tr.wf
  let gob5 : TrTerm c.venv c.lparams (c.withMLC _ (wf := cwf5)).vlctx _ _ := .of hgoTrΓ hgoTΓ
  -- `go` at the five binders, which is the equation's left-hand side
  let lhs5 := by
    refine gob5.app hy5 |>.app (hhy5.cast ?_) |>.app (TrTerm.natUnApp (succb hnat) hf5)
      |>.app hx5 |>.app (hhh5.cast ?_) <;>
    simp [hyTy, leb2, oneb2, hy5, hy4, hy3, hhTy, leb4, hx5, hx4, hx3, hf5,
      TrTerm.natBinApp, TrTerm.app', TrTerm.of, TrTerm.natUnApp, TrTerm.wk, TrTerm.natZero,
      TrTerm.natSucc, succb, zerob, VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.liftN,
      VExpr.natLit, VExpr.inst_lift, hleC.liftN_eq (Nat.zero_le _), hleC.instN_eq (Nat.zero_le _)]
  refine .bind (checkType.WF ?_) fun _ _ _ ⟨e2', e2Ty', _, he2Tr, _, he2T⟩ => ?_
  · have hxf : Expr.FVarsIn (· ∈ _) (.fvar idx) := hx5.trS.fvarsIn
    have hyf : Expr.FVarsIn (· ∈ _) (.fvar idy) := hy5.trS.fvarsIn
    have hyy : Expr.FVarsIn (· ∈ _) (.fvar idhy) := hhy5.trS.fvarsIn
    have hff : Expr.FVarsIn (· ∈ _) (.fvar idf) := hf5.trS.fvarsIn
    have hhf : Expr.FVarsIn (· ∈ _) (.fvar idh) := hhh5.trS.fvarsIn
    refine Condition.fvarsIn_dite ?_ (hHFV ?_) (helsFV hxf)
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      obtain rfl | rfl := ha
      exacts [hyf, hxf]
    · simp [FVarsIn, sub, mkApp2, mkApp]
      simp_all [FVarsIn]
  refine .bind (isDefEq.WF lhs5.trS he2Tr) fun _ _ _ hb3 => elseFail ((fun heq2 => ?_) ∘ hb3)
  -- the fuel equation, taken apart: the condition at `y` and `x`, the step at a `go` call, and
  -- the caller's own stopping value
  obtain ⟨P2, D2, t2', e2'', hP2, hD2, ht2, he2, hshape2⟩ :=
    Condition.dite_tr_inv (cnd := Condition.natLE) (m := _)
      (by simp [Condition.natLE, Expr.mkAppN_eq, Expr.appN, noProj]) he2Tr
  obtain ⟨_, _, hP2a, hP2b, hP2eq⟩ := w.prop_app2_inv hP2
  cases TrExprS.unique (by simp [TrExprS.IsUnique]) hP2a hy5.trS
  cases TrExprS.unique (by simp [TrExprS.IsUnique]) hP2b hx5.trS
  obtain ⟨_, _, hD2a, hD2b, hD2eq⟩ := w.dec_app2_inv hD2
  cases TrExprS.unique (by simp [TrExprS.IsUnique]) hD2a hy5.trS
  cases TrExprS.unique (by simp [TrExprS.IsUnique]) hD2b hx5.trS
  obtain ⟨t2g, ht2g, rfl⟩ := hHtr ht2
  cases ht2g with | app hgo5T2 hlem2T ht2f ht2lem
  cases ht2f with | app _ hsub2T ht2f2 ht2sub
  cases ht2f2 with | app _ hfuel2T ht2f3 ht2fuel
  cases ht2f3 with | app _ hpf2T ht2f4 ht2pf
  cases ht2f4 with | app _ hy2T ht2go ht2y
  have hgo2 : _ = go' := TrExprS.unique (noProj.isUnique (by simp [noProj])) ht2go hgoTrΓ
  rw [hgo2] at hshape2
  cases ht2sub with | app _ _ ht2sf ht2sy
  cases ht2sf with | app _ _ ht2sc ht2sx
  obtain ⟨rfl, -⟩ := ht2sc.const0_inv (Us' := c.lparams) (Δ' := c.vlctx)
  rw [TrExprS.fvar_lift_uniq hy5.trS ht2y, TrExprS.fvar_lift_uniq hhy5.trS ht2pf,
    TrExprS.fvar_lift_uniq hf5.trS ht2fuel, TrExprS.fvar_lift_uniq hx5.trS ht2sx,
    TrExprS.fvar_lift_uniq hy5.trS ht2sy] at hshape2
  -- closing the five binders at literals. `Nat`'s sort is existential -- the checker never pins
  -- it, and `SubstEq.cons` does not need it pinned
  have hγ5 (xx bb f' : Nat) (pf pf' : VExpr)
      (hpfT : c.HasType₀ pf ((le'.app (.natLit 1)).app (.natLit bb)))
      (hpf'T : c.HasType₀ pf' ((le'.app (VExpr.natSucc.app (.natLit xx))).app (.natLit (f'+1)))) :
      (c.withMLC _ (wf := cwf5)).Closing
        (((((VExpr.Subst.id.cons (.natLit xx)).cons (.natLit bb)).cons pf).cons
          (.natLit f')).cons pf') := by
    refine .cons (.cons (.cons (.cons (.cons hγ0 hnatTyΓ (hlitT xx [])) hnatTyΓ (hlitT bb []))
      hyTy.hasType ?_) hnatTyΓ (hlitT f' [])) hhTy.hasType ?_
    · simp only [hyTy, leb2, oneb2, hy, TrTerm.natBinApp, TrTerm.app', TrTerm.of,
        TrTerm.natUnApp, TrTerm.natZero, TrTerm.natSucc, succb, zerob, TrTerm.fvar,
        VExpr.subst, VExpr.Subst.id, VExpr.natSucc, VExpr.natZero, hleC.subst_eq']; exact hpfT
    · simp only [hhTy, leb4, hx4, hx3, hx2, hx, hf, TrTerm.natBinApp, TrTerm.app', TrTerm.of,
        TrTerm.natUnApp, TrTerm.wk, TrTerm.natSucc, succb, TrTerm.fvar, VExpr.subst,
        VExpr.Subst.id, VExpr.lift, VExpr.liftN, VExpr.natSucc, hleC.subst_eq']; exact hpf'T
  -- where the dividend lands under that closing, which is what the stopping value is read at
  have hx5s (xx bb f' : Nat) (pf pf' : VExpr) :
      hx5.tgt.subst (((((VExpr.Subst.id.cons (.natLit xx)).cons (.natLit bb)).cons pf).cons
        (.natLit f')).cons pf') = .natLit xx := by
    simp [hx5, hx4, hx3, hx2, hx, TrTerm.wk, TrTerm.fvar, VExpr.lift, VExpr.liftN, liftVar,
      VExpr.Subst.cons, VExpr.Subst.id]
  -- the fuel recursion at literals. The induction is `natFuelRec`; what is left here is the
  -- branch's own equation, closed off and evaluated, which is that lemma's `hstep`
  have hxs : hx2.tgt = .bvar 1 := by
    simp [hx2, hx, TrTerm.wk, TrTerm.fvar, VExpr.lift, VExpr.liftN, liftVar]
  have hys : hy.tgt = .bvar 0 := by simp [hy, TrTerm.fvar]
  refine .pure (hbody (m2 := m2) hx2 hy w hite (hdite rfl) hleC hgoC hleTΓ hgoTrΓ hgoTΓ hγ2
    hxs hys he1Tr he1T heq1 ?_)
  refine natFuelRec (F := F) (h := hF) (H := H') (E := E) hgoTΓ hleC hFlt hFstep hHwf
    (fun hT h => (hHlit _) ▸ hHcong hT h) fun bb x f' pf pf' hbb hwf => ?_
  have hga := goArgs hgoTΓ hleC hwf
  have hpfT := hga.2.1
  have hpf'T := hga.2.2.2.2.1
  have hc2 := heq2.subst c.Ewf.orderedStrong (hγ5 x bb f' pf pf' hpfT hpf'T)
  rw [hshape2] at hc2 he2T
  have hwf2 := he2T.subst c.Ewf.orderedStrong (hγ5 x bb f' pf pf' hpfT hpf'T)
  simp [diteApp, VExpr.subst, VExpr.Subst.cons, VExpr.Subst.lift, TrTerm.app,
    hP2eq, hD2eq, hHsubst, hdecC'.subst_eq', hgoC.subst_eq', hpropC'.subst_eq',
    hy5, hy4, hy3, hy, hx5, hx4, hx3, hx2, hx, hf5, hf, hhy5, hhy3, hhh5, gob5, lhs5,
    TrTerm.of, TrTerm.wk, TrTerm.fvar, VExpr.liftN] at hc2 hwf2
  -- evaluate it: at literals the decision is `Nat.ble bb x`
  obtain ⟨pf2, hev2⟩ := (hdite rfl).2.1 c.self (Γ := []) (args' := [.natLit bb, .natLit x])
    (Nat.ble bb x) trivial (.cons (hlitT bb []) (.cons (hlitT x []) .nil)) rfl
    (w.natLE_apply₀ hprim c.self bb x rfl) ⟨_, hwf2⟩
  simp only [VExpr.appN, diteApp] at hev2
  have hstep2 := hc2.trans c.Ewf trivial hev2
  have hwfr2 : c.WF₀ _ := ⟨_, hstep2.choose_spec.hasType.2⟩
  split <;> rename_i hle2
  · -- `bb ≤ x`: the recursive call is at `x - bb`, which the `Nat.sub` reflection turns into a
    -- literal
    simp only [Nat.ble_eq_true_of_le hle2, if_true] at hstep2 hwfr2
    have hbeta := (VExpr.WF.betaU c.Ewf trivial hwfr2).2
    simp only [VExpr.inst, hHinst, VExpr.inst_lift, hgoC.instN_eq (Nat.zero_le _),
      VExpr.closedN_natLit.instN_eq (Nat.zero_le _)] at hbeta
    have hwfgo2 := hHwf ⟨_, VEnv.HasType.defeqU_l c.Ewf trivial hbeta hwfr2.choose_spec⟩
    have hga2 := goArgs hgoTΓ hleC hwfgo2
    have hpf3T := hga2.2.2.2.2.1
    have hsubEq : c.venv.IsDefEqU c.lparams.length []
        ((vexpr(Nat.sub).app (.natLit x)).app (.natLit bb)) (.natLit (x - bb)) := by
      rw [hlp]; exact (hprim.natSub hsub).2 x bb
    have hcong := VEnv.IsDefEqU.appN' c.Ewf trivial
      (xs := [.natLit bb, pf, .natLit f', (vexpr(Nat.sub).app (.natLit x)).app (.natLit bb), _])
      (ys := [.natLit bb, pf, .natLit f', .natLit (x - bb), _]) (f := go') (f' := go') ⟨_, hgoTΓ⟩
      (.cons ⟨_, hlitT bb []⟩ <| .cons ⟨_, hpfT⟩ <| .cons ⟨_, hlitT f' []⟩ <|
        .cons hsubEq <| .cons ⟨_, hpf3T⟩ .nil) (by simpa [VExpr.appN] using hwfgo2)
    simp only [VExpr.appN] at hcong
    exact ⟨_, (hstep2.trans c.Ewf trivial hbeta).trans c.Ewf trivial (hHcong hga2.2.2.2.2.2 hcong)⟩
  · -- `x < bb`: the recursion stops at the caller's own value
    rw [if_neg (mt Nat.le_of_ble_eq_true hle2)] at hstep2 hwfr2
    refine hstep2.trans c.Ewf trivial ?_
    have hbeta := (VExpr.WF.betaU c.Ewf trivial hwfr2).2
    rw [VExpr.inst_eq, VExpr.subst_subst, VExpr.Subst.lift_comp_one] at hbeta
    refine hbeta.trans c.Ewf trivial <|
      hels he2 (TrExprS.underBV c.Ewf (MLCtx.noBV _) hx5.trS) ?_
    rw [VExpr.lift_subst, VExpr.Subst.cons_tail]; exact hx5s x bb f' pf pf'

/-- `Nat.mod`: a fuel-driven recursion through `Nat.modCore.go`. Three equations: the base
`mod 0 x ≡ 0` at its own probe, which is discharged where it is proved because that probe is gone
by the time the rest of the checks run; the top equation `mod (succ x) y ≡ if y ≤ succ x then …`
`else succ x`, with a conditional inside its `then`; and `go`'s own equation, which is the shared
recursion's business. The step does nothing to the recursive call, and the recursion returns the
dividend when it stops. -/
theorem checkNatMod.WF {ves : VEnvs} (wf : ves.WF env)
    (hname : v.name = ``Nat.mod) :
    let c := .mk' wf .safe v.levelParams; Data v ci' c →
    (checkNatMod v).WF c state fun _ _ => PrimitiveResult (ves.venv .safe) v ci' := by
  intro ctx P; rw [← ctx.withMLC_self]
  refine elseFail fun h1 => elseFail fun h2 => ?_
  simp at h1
  -- the guard names `Nat.sub`, whose recorded typing supplies `Nat`, and `Bool`, which is what
  -- the condition's decision procedure evaluates through
  have hsub := VContext.contains_primitive rfl h1.1.1
  have hbool := VContext.contains_primitive rfl h1.1.2
  have hnat := VEnv.contains_nat_of_hasType ctx.Ewf.orderedStrong (wf.hasPrimitives.natSub hsub).1
  have tyeq := P.mkTyEq hnat (by simp [TrExprS.IsUnique]) (natCod hnat) h2
  have hlp : ctx.lparams.length = 0 := congrArg List.length (hok h1.2).2
  obtain ⟨natU, hnatTy⟩ : ctx.venv.IsType ctx.lparams.length [] .nat :=
    wf.hasPrimitives.natIsType' ctx.Ewf.orderedStrong hnat trivial
  have hlitT (k : Nat) (Γ : List VExpr) : ctx.venv.HasType ctx.lparams.length Γ (.natLit k) .nat :=
    wf.hasPrimitives.natLitT ctx.Ewf.orderedStrong hnat k Γ
  -- the base equation `mod 0 x ≡ 0`. Its probe is gone by the time the rest of the checks run,
  -- so it is closed off here rather than carried
  refine .bind ?_ fun _ _ _ (hbase : ∀ a : Nat,
      ctx.IsDefEqU₀ ((ci'.value.app (.natLit 0)).app (.natLit a)) (.natLit 0)) => ?_
  · refine .withNatProbe (m := ctx.mlctx) wf.hasPrimitives hnat .rfl ?_
    intro idx0 m0 _ _ _ _ hx0
    refine .bind (isDefEq.WF (TrTerm.natBinApp (P.hv tyeq m0) (zerob hnat) hx0).trS
      (zerob hnat).trS) fun _ _ _ hb => elseFail ((fun heq0 => ?_) ∘ hb)
    refine .pure fun a => ?_
    have hγ0 : (ctx.withMLC m0).Closing (VExpr.Subst.id.cons (.natLit a)) :=
      .cons .nil hnatTy (hlitT a [])
    have h := heq0.subst ctx.Ewf.orderedStrong hγ0
    have hvalC : ci'.value.ClosedN := (P.hci.closedN' ctx.Ewf.ordered.closed trivial).1
    simpa [TrTerm.natBinApp, TrTerm.app', TrTerm.of, TrTerm.of_nil', TrTerm.wk, TrTerm.fvar,
      TrTerm.natZero, zerob, hx0, Data.hv, VExpr.subst, VExpr.Subst.cons, VExpr.Subst.id,
      VExpr.instVar, VExpr.natLit, VExpr.natZero, hvalC.subst_eq'] using h
  -- the recursion itself, which `Nat.div` runs too
  refine checkNatFuelRec.WF (F := (· % ·)) (hF := id)
    (lhsB := .natUnApp (succb hnat)) (hHFV := id) (helsFV := id) (hHtr := (⟨_, ·, rfl⟩))
    (hHsubst := rfl) (hHinst := rfl) (hHwf := id) (hHcong := fun _ => id)
    (hHlit := fun _ => rfl) (hFlt := fun _ _ => Nat.mod_eq_of_lt)
    wf.hasPrimitives hnat hbool hsub rfl hlp (fun m [ctx.MLCWF m] => P.hv tyeq m)
    (htopFV := fun hx hy => ?_) (hels := ?_) (hFstep := fun bb x hbb hle => ?_) ?_
  · simp [Condition.ite, Condition.dite, Condition.natLE, Expr.lam0, mkApp5, mkApp4, mkApp,
      mkAppB, mkAppN, succ, one, zero, FVarsIn, Level.hasMVar']
    refine ⟨?_, ?_⟩ <;> simp_all
  · intro _ _ _ _ hX hfv _ _ heq; cases TrExprS.fvar_uniq hX hfv; rw [heq]; exact ⟨_, hlitT _ []⟩
  · rw [id, Nat.mod_eq x bb, if_pos ⟨hbb, hle⟩]
  intro m2 cwf2 idx idy hx2 hy le' go' w hite hdite hleC hgoC hleTΓ hgoTrΓ hgoTΓ hγ2 hxs hys
    e1' e1Ty' he1Tr he1T heq1 hfuel
  haveI : ctx.MLCWF m2 := cwf2
  refine P.mkResult (F := Nat.mod) (hok h1.2) hnat (by simp [primSpecs, hname]) tyeq fun hvT => ?_
  -- the top equation's two conditionals, taken apart
  have ⟨α1', Pi1, Di1, ti1', ei1', hα1, hPi1, hDi1, hti1, hei1, hshapei1⟩ :=
    Condition.ite_tr_inv he1Tr
  have ⟨P1, D1, t1', e1'', hP1, hD1, ht1, he1, hshape1⟩ := Condition.dite_tr_inv (H := hti1) <| by
    simp [Condition.natLE, Expr.mkAppN_eq, Expr.appN, noProj, one, zero, succ]
  let oneb2 : TrTerm ctx.venv ctx.lparams (ctx.withMLC m2).vlctx _ .nat :=
    .natUnApp (succb hnat) (zerob hnat)
  let sxb2 : TrTerm ctx.venv ctx.lparams (ctx.withMLC m2).vlctx _ .nat := .natUnApp (succb hnat) hx2
  -- each conditional's condition, at the arguments the checker built it from: the head is the
  -- condition's own `prop` or `dec`, which translates the one way it can, so all that is left is
  -- to pin the two arguments
  obtain ⟨_, _, hP1a, hP1b, hP1eq⟩ := w.prop_app2_inv hP1
  cases TrExprS.unique (by simp [TrExprS.IsUnique, one, zero, succ]) hP1a oneb2.trS
  cases TrExprS.unique (by simp [TrExprS.IsUnique]) hP1b hy.trS
  obtain ⟨_, _, hD1a, hD1b, hD1eq⟩ := w.dec_app2_inv hD1
  cases TrExprS.unique (by simp [TrExprS.IsUnique, one, zero, succ]) hD1a oneb2.trS
  cases TrExprS.unique (by simp [TrExprS.IsUnique]) hD1b hy.trS
  cases hα1.const0_inv (Us' := ctx.lparams) (Δ' := ctx.vlctx) |>.1
  obtain ⟨_, _, hPi1a, hPi1b, hPi1eq⟩ := w.prop_app2_inv hPi1
  cases TrExprS.unique (by simp [TrExprS.IsUnique]) hPi1a hy.trS
  cases TrExprS.unique (by simp [TrExprS.IsUnique, succ]) hPi1b sxb2.trS
  obtain ⟨_, _, hDi1a, hDi1b, hDi1eq⟩ := w.dec_app2_inv hDi1
  cases TrExprS.unique (by simp [TrExprS.IsUnique]) hDi1a hy.trS
  cases TrExprS.unique (by simp [TrExprS.IsUnique, succ]) hDi1b sxb2.trS
  -- the branches: both of the top equation's `else`s are `succ x`, and its `then` is a `go` call
  -- whose guard proof is the one the conditional itself produces
  cases TrExprS.unique (noProj.isUnique <| by simp [noProj, succ]) hei1 sxb2.trS
  let .app _ _ he1c he1a := he1
  have he1xeq := TrExprS.fvar_lift_uniq hx2.trS he1a
  cases he1c.const0_inv (Us' := ctx.lparams) (Δ' := ctx.vlctx) |>.1
  let .app hgo5T1 hpf1T ht1f ht1pf := ht1
  let .app _ hsx1T ht1f2 ht1sx := ht1f
  let .app _ hssx1T ht1f3 ht1ssx := ht1f2
  let .app _ hbv1T ht1f4 ht1bv := ht1f3
  let .app _ hy1T ht1go ht1y := ht1f4
  cases TrExprS.unique (noProj.isUnique <| by simp [noProj]) ht1go hgoTrΓ
  -- the `go` call's arguments: `y`, the conditional's own proof, `succ (succ x)`, `succ x`
  have hy1eq := TrExprS.fvar_lift_uniq hy.trS ht1y
  let .app _ _ ht1sxc ht1sxa := ht1sx
  have hsx1eq := TrExprS.fvar_lift_uniq hx2.trS ht1sxa
  cases ht1sxc.const0_inv (Us' := ctx.lparams) (Δ' := ctx.vlctx) |>.1
  let .app _ _ ht1ssxc ht1ssxa := ht1ssx
  let .app _ _ ht1ssxc2 ht1ssxa2 := ht1ssxa
  have hssx1eq := TrExprS.fvar_lift_uniq hx2.trS ht1ssxa2
  cases ht1ssxc.const0_inv (Us' := ctx.lparams) (Δ' := ctx.vlctx) |>.1
  cases ht1ssxc2.const0_inv (Us' := ctx.lparams) (Δ' := ctx.vlctx) |>.1
  cases ht1bv with | bvar hbv1
  simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type,
    Option.some.injEq, Prod.mk.injEq] at hbv1
  rw [hy1eq, hsx1eq, hssx1eq, he1xeq, ← hbv1.1] at hshape1
  -- the pieces are closed, so the closing leaves them alone
  have hvalC : ci'.value.ClosedN := (hvT.closedN' ctx.Ewf.ordered.closed trivial).1
  have hdecC' : w.dec'.ClosedN := w.decC
  have hpropC' : w.prop'.ClosedN := w.propC
  refine ⟨hlp ▸ hvT, fun a b => hlp ▸ ?_⟩
  cases a with
  | zero =>
    rw [show Nat.mod 0 b = 0 from Nat.zero_mod b]
    simpa [VExpr.natLit, VExpr.natZero] using hbase b
  | succ k
  -- the top equation at `x := k`, `y := b`, closed off at literals
  have hc1 := heq1.subst ctx.Ewf.orderedStrong (hγ2 k b)
  rw [hshapei1, hshape1] at hc1 he1T
  have hwf1 := he1T.subst ctx.Ewf.orderedStrong (hγ2 k b)
  simp [iteApp, diteApp, VExpr.subst, VExpr.Subst.cons, VExpr.Subst.lift, TrTerm.app', TrTerm.of,
    TrTerm.natUnApp, TrTerm.of_nil', Data.hv, VExpr.liftN, sxb2, hxs, hys, hPi1eq, hDi1eq,
    hP1eq, hD1eq, hdecC'.subst_eq', hgoC.subst_eq', hvalC.subst_eq', hpropC'.subst_eq'] at hc1 hwf1
  -- evaluate the outer conditional: at literals the decision is `Nat.ble b (succ k)`
  have hev1 := (hite rfl).2 ctx.self (Γ := []) (args' := [.natLit b, .natLit (k+1)])
    (Nat.ble b (k+1)) nofun trivial (.cons (hlitT b []) (.cons (hlitT (k+1) []) .nil)) rfl
    (w.natLE_apply₀ wf.hasPrimitives ctx.self b (k+1) rfl) ⟨_, hwf1⟩
  simp only [VExpr.appN, iteApp, VExpr.natLit, VExpr.natSucc] at hev1
  have hstep1 := hc1.trans ctx.Ewf trivial hev1
  have hwfr1 : ctx.WF₀ _ := ⟨_, hstep1.choose_spec.hasType.2⟩
  cases hb1 : Nat.ble b (k+1) with
  | false =>
    -- `succ k < b`, so the answer is `succ k` itself
    simp only [hb1, Bool.false_eq_true, if_false] at hstep1
    rcases Nat.lt_or_ge (k+1) b with h | h
    · rwa [show Nat.mod (k+1) b = k+1 from Nat.mod_eq_of_lt h]
    · rw [Nat.ble_eq_true_of_le h] at hb1; cases hb1
  | true
  simp only [hb1, if_true] at hstep1 hwfr1
  refine hstep1.trans ctx.Ewf trivial ?_
  -- the inner conditional, at `1` and `b`
  obtain ⟨pf1, hev2⟩ := hdite.2.1 ctx.self (Γ := []) (args' := [.natLit 1, .natLit b])
    (Nat.ble 1 b) trivial (.cons (hlitT 1 []) (.cons (hlitT b []) .nil)) rfl
    (w.natLE_apply₀ wf.hasPrimitives ctx.self 1 b rfl) hwfr1
  simp only [VExpr.appN, diteApp, VExpr.natLit, VExpr.natSucc, VExpr.natZero] at hev2
  refine hev2.trans ctx.Ewf trivial ?_
  have hwfr2 : ctx.WF₀ _ := ⟨_, hev2.choose_spec.hasType.2⟩
  cases hb2 : Nat.ble 1 b with
  | false =>
    -- `b = 0`, and `succ k % 0 = succ k`
    let 0 := b
    simp only [Bool.false_eq_true, if_false] at hwfr2 ⊢
    have hbeta := (hwfr2.betaU ctx.Ewf trivial).2
    simp only [VExpr.inst, VExpr.closedN_natLit.instN_eq (Nat.zero_le _)] at hbeta
    rw [show Nat.mod (k+1) 0 = k+1 from Nat.mod_zero _]
    exact hbeta
  | true =>
    simp only [hb2, if_true] at hwfr2 ⊢
    have hbeta := (hwfr2.betaU ctx.Ewf trivial).2
    simp only [VExpr.inst, VExpr.instVar, hgoC.instN_eq (Nat.zero_le _), VExpr.liftN_zero,
      VExpr.closedN_natLit.instN_eq (Nat.zero_le _), Nat.lt_irrefl, if_false, if_true] at hbeta
    have hwfgo : ctx.WF₀ _ :=
      ⟨_, VEnv.HasType.defeqU_l ctx.Ewf trivial hbeta hwfr2.choose_spec⟩
    refine hbeta.trans ctx.Ewf trivial ?_
    exact hfuel (k+2) b (k+1) pf1 _ (Nat.le_of_ble_eq_true hb2) (Nat.lt_succ_self _) hwfgo

/-- `Nat.div`: the same fuel recursion, through `Nat.div.go`, and one equation fewer -- `div 0 y`
is covered by the top equation `div x y ≡ if 1 ≤ y then go y _ (succ x) x _ else 0`. The step
counts, so the recursive call is wrapped in a `succ`, and the recursion returns `0` when it
stops. -/
theorem checkNatDiv.WF {ves : VEnvs} (wf : ves.WF env)
    (hname : v.name = ``Nat.div) :
    let c := .mk' wf .safe v.levelParams; Data v ci' c →
    (checkNatDiv v).WF c state fun _ _ => PrimitiveResult (ves.venv .safe) v ci' := by
  intro ctx P; rw [← ctx.withMLC_self]
  refine elseFail fun h1 => elseFail fun h2 => ?_
  simp at h1
  have hsub := VContext.contains_primitive rfl h1.1.1
  have hbool := VContext.contains_primitive rfl h1.1.2
  have hnat := VEnv.contains_nat_of_hasType ctx.Ewf.orderedStrong (wf.hasPrimitives.natSub hsub).1
  have tyeq := P.mkTyEq hnat (by simp [TrExprS.IsUnique]) (natCod hnat) h2
  have hlp : ctx.lparams.length = 0 := congrArg List.length (hok h1.2).2
  have hlitT (k : Nat) (Γ : List VExpr) : ctx.venv.HasType ctx.lparams.length Γ (.natLit k) .nat :=
    wf.hasPrimitives.natLitT ctx.Ewf.orderedStrong hnat k Γ
  refine checkNatFuelRec.WF (F := fun x bb => x / bb) (hF := (· + 1)) (lhsB := id)
    (H' := fun e => VExpr.natSucc.app e) (E := fun _ => 0) (hFlt := fun _ _ => Nat.div_eq_of_lt)
    (hHFV := (⟨nofun, ·⟩)) (helsFV := fun _ => nofun) (hHlit := fun _ => rfl)
    (hHsubst := rfl) (hHinst := rfl) wf.hasPrimitives hnat hbool hsub rfl hlp
    (fun m inst => haveI : ctx.MLCWF m := ⟨inst.wf⟩; P.hv tyeq m)
    (hHwf := fun hwf => have ⟨_, _, _, ha⟩ := hwf.app_inv ctx.Ewf.orderedStrong trivial; ⟨_, ha⟩)
    (hHcong := fun hT h => .app_arg ctx.Ewf trivial (succb (Δ := []) hnat).hasType hT h)
    (htopFV := fun hx hy => ?_) (hHtr := fun (.app _ _ hc ha) => ?_)
    (hels := ?_) (hFstep := fun bb x hbb hle => ?_) ?_
  · simp [Condition.dite, Condition.natLE, Expr.lam0, mkApp5, mkApp4, mkApp, mkAppB,
      mkAppN, succ, one, zero, FVarsIn, Level.hasMVar']
    exact ⟨⟨hy, hx⟩, hy⟩
  · cases hc.const0_inv (Us' := ctx.lparams) (Δ' := ctx.vlctx) |>.1; exact ⟨_, ha, rfl⟩
  · intro _ _ _ _ hX _ _ _ _
    cases TrExprS.unique (by simp [TrExprS.IsUnique, zero]) hX (zerob (c := ctx) hnat).trS
    simp only [zerob, TrTerm.natZero, TrTerm.of, VExpr.subst, VExpr.natZero]
    exact ⟨_, hlitT 0 []⟩
  · rw [Nat.div_eq x bb, if_pos ⟨hbb, hle⟩]
  intro m2 cwf2 idx idy hx2 hy le' go' w _ hdite hleC hgoC hleTΓ hgoTrΓ hgoTΓ hγ2 hxs hys
    e1' e1Ty' he1Tr he1T heq1 hfuel
  haveI : ctx.MLCWF m2 := cwf2
  refine P.mkResult (F := Nat.div) (hok h1.2) hnat (by simp [primSpecs, hname]) tyeq fun hvT => ?_
  -- the top conditional, taken apart: `dite_tr_inv` gives the pieces `checkType` produced
  obtain ⟨P1, D1, t1', e1'', hP1, hD1, ht1, he1, hshape1⟩ := Condition.dite_tr_inv
    (by simp [Condition.natLE, Expr.mkAppN_eq, Expr.appN, noProj, one, zero, succ]) he1Tr
  let oneb2 : TrTerm ctx.venv ctx.lparams (ctx.withMLC m2).vlctx _ .nat :=
    .natUnApp (succb hnat) (zerob hnat)
  obtain ⟨_, _, hP1a, hP1b, hP1eq⟩ := w.prop_app2_inv hP1
  cases TrExprS.unique (by simp [TrExprS.IsUnique, one, zero, succ]) hP1a oneb2.trS
  cases TrExprS.unique (by simp [TrExprS.IsUnique]) hP1b hy.trS
  obtain ⟨_, _, hD1a, hD1b, hD1eq⟩ := w.dec_app2_inv hD1
  cases TrExprS.unique (by simp [TrExprS.IsUnique, one, zero, succ]) hD1a oneb2.trS
  cases TrExprS.unique (by simp [TrExprS.IsUnique]) hD1b hy.trS
  -- the branches: the `else` is `0`, and the `then` is a `go` call whose guard proof is the one
  -- the conditional itself produces
  cases he1.const0_inv (Us' := ctx.lparams) (Δ' := ctx.vlctx) |>.1
  let .app hgo4T1 hlt1T ht1f ht1lt := ht1
  let .app _ hx1T ht1f2 ht1x := ht1f
  let .app _ hsx1T ht1f3 ht1sx := ht1f2
  let .app _ hpf1T ht1f4 ht1pf := ht1f3
  let .app _ hy1T ht1go ht1y := ht1f4
  cases TrExprS.unique (noProj.isUnique (by simp [noProj])) ht1go hgoTrΓ
  have hvalC : ci'.value.ClosedN := (hvT.closedN' ctx.Ewf.ordered.closed trivial).1
  have hdecC' : w.dec'.ClosedN := w.decC
  have hpropC' : w.prop'.ClosedN := w.propC
  refine ⟨hlp ▸ hvT, fun a b => hlp ▸ ?_⟩
  -- the `go` call's arguments, read off their translations
  have hfindy : ∃ A, m2.vlctx.find? (.inr idy) = some (hy.tgt, A) := by
    let .fvar h := hy.trS; exact ⟨_, h⟩
  have hfindx : ∃ A, m2.vlctx.find? (.inr idx) = some (hx2.tgt, A) := by
    let .fvar h := hx2.trS; exact ⟨_, h⟩
  obtain ⟨_, hfindy⟩ := hfindy; obtain ⟨_, hfindx⟩ := hfindx
  let .fvar hfy1 := ht1y
  let .bvar hfpf1 := ht1pf
  let .fvar hfx1 := ht1x
  let .app _ _ ht1sc ht1sa := ht1sx
  let .fvar hfsx1 := ht1sa
  cases ht1sc.const0_inv (Us' := ctx.lparams) (Δ' := ctx.vlctx) |>.1
  simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type, VLocalDecl.depth,
    Option.some.injEq, Prod.mk.injEq,
    VContext.vlctx, VContext.withMLC_mlctx, hfindy, hfindx] at hfy1 hfpf1 hfx1 hfsx1
  cases hfy1.1; cases hfpf1.1; cases hfx1.1; cases hfsx1.1
  have hc1 := heq1.subst ctx.Ewf.orderedStrong (hγ2 a b)
  rw [hshape1] at hc1 he1T
  have hwf1 := he1T.subst ctx.Ewf.orderedStrong (hγ2 a b)
  simp [diteApp, VExpr.subst, VExpr.Subst.cons, VExpr.Subst.lift,
    hxs, hys, hP1eq, hD1eq, hdecC'.subst_eq', hgoC.subst_eq', hvalC.subst_eq', hpropC'.subst_eq',
    TrTerm.of, TrTerm.of_nil', VExpr.liftN, Data.hv, id] at hc1 hwf1
  -- evaluate it: at literals the decision is `Nat.ble 1 b`
  obtain ⟨pf1, hev1⟩ := hdite.2.1 ctx.self (Γ := []) (args' := [.natLit 1, .natLit b])
    (Nat.ble 1 b) trivial (.cons (hlitT 1 []) (.cons (hlitT b []) .nil)) rfl
    (w.natLE_apply₀ wf.hasPrimitives ctx.self 1 b rfl) ⟨_, hwf1⟩
  simp only [VExpr.appN, diteApp, VExpr.natLit, VExpr.natSucc, VExpr.natZero] at hev1
  have hstep1 := hc1.trans ctx.Ewf trivial hev1
  have hwfr : ctx.WF₀ _ := ⟨_, hstep1.choose_spec.hasType.2⟩
  -- `b = 0` takes the `else` branch, and `Nat.div a 0 = 0`; otherwise the fuel recursion runs
  refine hstep1.trans ctx.Ewf trivial ?_
  cases hb : Nat.ble 1 b with
  | false =>
    let 0 := b
    have := (hwfr.betaU ctx.Ewf trivial).2
    simpa [VExpr.natLit, VExpr.natZero, Nat.div_zero, Nat.div]
  | true =>
    simp only [hb, if_true] at hstep1 hwfr
    have ⟨hpf1T, hbeta⟩ := hwfr.betaU ctx.Ewf trivial
    simp only [VExpr.inst, VExpr.instVar, hgoC.instN_eq (Nat.zero_le _),
      VExpr.closedN_natLit.instN_eq (Nat.zero_le _)] at hbeta
    refine hbeta.trans ctx.Ewf trivial ?_
    simp only [Nat.lt_irrefl, if_false, if_true, VExpr.liftN_zero] at hbeta ⊢
    exact hfuel (a+1) b a pf1 _ (Nat.le_of_ble_eq_true hb) (Nat.lt_succ_self _)
      ⟨_, VEnv.HasType.defeqU_l ctx.Ewf trivial hbeta hwfr.choose_spec⟩
