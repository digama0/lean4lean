import Lean4Lean.Verify.Environment.Primitive.Recursion

namespace Lean4Lean
open Lean4Lean TypeChecker
open Lean hiding Environment Exception
open Kernel

namespace Primitive

/-- `Nat.gcd`: a well-founded recursion, which the `eager` gadget packs into a form the
recognizer can probe. The base probe is `gcd' 0 n ≡ n`; the step probe's right-hand side is the
recursive call at `n % succ m`, which is what the branch's `Nat.mod` guard is for. -/
theorem checkNatGcd.WF {ves : VEnvs} (wf : ves.WF env)
    (hname : v.name = ``Nat.gcd) :
    let c := .mk' wf .safe v.levelParams; Data v ci' c →
    (checkNatGcd v).WF c state fun _ _ => PrimitiveResult (ves.venv .safe) v ci' := by
  intro ctx P; rw [← ctx.withMLC_self]; unfold checkNatGcd
  refine .getEnv <| elseFail fun h1 => elseFail fun h2 => ?_
  simp at h1
  -- the guard names `Nat.mod`, whose recorded typing supplies `Nat`, and `Bool`, which the
  -- `eager` gadget's conditional needs
  have hmod := VContext.contains_primitive rfl h1.1.1
  have hbool := VContext.contains_primitive rfl h1.1.2
  have hE := ctx.Ewf.orderedStrong
  have hΔ := ctx.Δwf.toCtx
  have hnat := wf.hasPrimitives.natOfMod hE hmod
  have tyeq := P.mkTyEq hnat (by simp [TrExprS.IsUnique]) (natCod hnat) h2
  -- the `eager` gadget's conditional is checked here now, and handed to the recognizer
  refine Condition.check.WF hnat hbool rfl .throw |>.bind fun _ _ _ ⟨wb, hite, _⟩ => ?_
  -- the recursion is on the first argument, and the intended answer is `Nat.gcd`
  refine unfoldNatWellFounded.WF₂ (c := ctx) (m₀ := ctx.mlctx) (P.hv tyeq ctx.mlctx).trS
      hnat rfl (hite rfl).1 (hite rfl).2 .throw |>.bind fun _ _ _ ⟨PB, hpr, hplen, hdone⟩ => ?_
  subst hpr
  refine .withNatProbe (m := ctx.mlctx) wf.hasPrimitives hnat .rfl ?_; intro idn mn _ _ _ _ hn
  -- the base probe `gcd' 0 n ≡ n`, then the step probe under one more binder
  refine .bind (ProbeBundle.probe.WF (c := ctx) (m := ctx.mlctx) (mp := mn) (P := PB)
    (R := fun _ γ _ v => v = γ 0) (.skip_fvar _ _ .refl) .throw
    (.cons (zerob hnat).trS (.cons hn.trS .nil)) hnat
    (by simp [hplen]) (List.forall_mem_pair (zerob hnat).hasType hn.hasType) ?_) ?_
  · refine fun id {cwf'} => ⟨hn.trS.fvarsIn.fvars_cons, fun _ rhsv hrhs _ γ ih _ _ => ?_⟩
    -- the right-hand side is the outer probe variable, so its value is the closing at it
    cases TrExprS.unique (by simp [TrExprS.IsUnique]) hrhs (hn.wk ctx.Ewf cwf'.wf.tr.wf).trS
    simp [VLocalDecl.depth, hn, TrTerm.wk, TrTerm.fvar]
  rintro _ _ _ heq
  refine .withNatProbe wf.hasPrimitives hnat .rfl ?_; intro idm mnn cwf _ _ _ hm
  let hn1 := hn.wk ctx.Ewf cwf.wf.tr.wf
  -- the step probe's right hand side is a recursive call, so its value is `ih` at an argument
  -- that is the packer at `n % succ m` and `succ m` -- but only once the closing is at
  -- literals, which is what `a`, `b` stand for
  refine .mono (ProbeBundle.probe.WF (c := ctx) (m := ctx.mlctx)
    (R := fun E γ ih v => ∀ a b : Nat, γ 1 = .natLit a → γ 0 = .natLit b →
      ∃ arg hy, E.IsDefEqU₀ arg
          (((PB.pack'.subst γ.tail.tail).app (.natLit (a % (b+1)))).app (.natLit (b+1))) ∧
        v = (ih.app arg).app hy)
    (.skip_fvar _ _ (.skip_fvar _ _ .refl)) .throw
    (.cons (TrTerm.natUnApp (succb hnat) hm).trS (.cons hn1.trS .nil)) hnat
    (by simp [hplen])
    (List.forall_mem_pair (TrTerm.natUnApp (succb hnat) hm).hasType hn1.hasType)
    fun id => ?_) ?_
  · intro m' cwf2; refine ⟨⟨⟨?_, ⟨?_, ?_⟩, ?_⟩, ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact (TrExprS.fvar (env := ctx.venv) (Us := ctx.lparams) VLCtx.find?_vlam_self).fvarsIn
    · exact PB.hpack.weakFV hE (.skip_fvar _ _ (.skip_fvar _ _ (.skip_fvar _ _ .refl)))
        cwf2.wf.tr.wf |>.fvarsIn
    · refine ((modb hmod).natBinApp hn1 ?_).wk ctx.Ewf cwf2.wf.tr.wf |>.trS.fvarsIn
      exact (succb hnat).natUnApp hm
    · exact (((succb hnat).natUnApp hm).wk ctx.Ewf cwf2.wf.tr.wf).trS.fvarsIn
    · exact .of_hasFVar rfl rfl rfl
    · exact (hm.wk ctx.Ewf cwf2.wf.tr.wf).trS.fvarsIn
    · exact (hn1.wk ctx.Ewf cwf2.wf.tr.wf).trS.fvarsIn
    -- split the right-hand side `ih (pack (n % succ m) (succ m)) pf` into its pieces; the `app`
    -- rule carries the typings, which is what makes the congruence below available
    intro hcl rhsv hrhs E γ ih hγ hihT a b ha hb
    cases hrhs with | app _ _ hrhs hpf
    cases hrhs with | @app _ _ _ arg _ _ _ _ _ hfv hX
    -- `ih` is the innermost binder, so its translation is `.bvar 0`
    cases TrExprS.unique (by simp [TrExprS.IsUnique]) hfv (TrExprS.fvar VLCtx.find?_vlam_self)
    refine ⟨_, _, ?_, rfl⟩
    -- the packed argument: its head translates to `pack'` only up to defeq, and its first
    -- argument is `Nat.mod` at the two literals
    cases hX with | app hfT haT hX hBv
    cases hX with | app hpT haT2 hpackv hAv
    cases TrExprS.unique (by simp [TrExprS.IsUnique, succ]) hBv
      (((succb hnat).natUnApp hm).wk ctx.Ewf cwf2.wf.tr.wf).trS
    cases TrExprS.unique (by simp [TrExprS.IsUnique, succ, mod]) hAv
      (((modb hmod).natBinApp hn1 ((succb hnat).natUnApp hm)).wk ctx.Ewf cwf2.wf.tr.wf).trS
    -- the head is only a *translation* of `pack`, so it is `pack'` up to defeq
    have hpk := PB.hpack.weakFV hE
      (.skip_fvar _ _ (.skip_fvar _ _ (.skip_fvar _ _ .refl))) cwf2.wf.tr.wf
    have hhd := hpackv.uniq ctx.Ewf (VLCtx.IsDefEq.refl ctx.Ewf cwf2.wf.tr.wf) hpk
    -- swap the head for `pack'` while still under the binders, then bring everything to ground
    -- in one step: `hcl` closes the probe's context, and substitution is a homomorphism
    have hΔ2 := (ctx.withMLC _ (wf := cwf2)).Δwf.toCtx
    have Wc := hcl E γ ih hγ hihT
    have hc := (E.mono <| VEnv.IsDefEqU.app_fun' ctx.Ewf hΔ2
      (.app_fun' ctx.Ewf hΔ2 hhd hpT haT2) hfT haT).subst E.wf.orderedStrong Wc
    have hpT3 := (E.monoT (hhd.of_l ctx.Ewf hΔ2 hpT).hasType.2).subst E.wf.orderedStrong Wc
    have hfT3 := (E.monoT <| (VEnv.IsDefEqU.app_fun' ctx.Ewf hΔ2 hhd hpT haT2
      |>.of_l ctx.Ewf hΔ2 hfT).hasType.2).subst E.wf.orderedStrong Wc
    have haT3 := (E.monoT haT2).subst E.wf.orderedStrong Wc
    have haT3' := (E.monoT haT).subst E.wf.orderedStrong Wc
    -- and finally the first argument evaluates: this is what the branch's `Nat.mod` guard buys
    have hmodeq := E.mono (ctx.natBinLit wf.hasPrimitives.natMod hmod a (b+1))
    have hΔ0 : OnCtx [] (E.venv.IsType ctx.lparams.length) := trivial
    simp [VExpr.Subst.tail, VExpr.liftN_subst, VLocalDecl.depth, VExpr.appN, VExpr.natLit,
      ha, hb, hn1, hm, hn, succb, modb, TrTerm.of, TrTerm.ofConst, TrTerm.fvar, TrTerm.natSucc,
      TrTerm.natUnApp, TrTerm.natBinApp, TrTerm.app', TrTerm.wk] at hc hpT3 hfT3 haT3 haT3' ⊢
    exact .trans E.wf hΔ0 hc <| .app_fun' E.wf hΔ0 (.app_arg' E.wf hΔ0 hmodeq hpT3 haT3) hfT3 haT3'
  rintro _ _ _ heq2
  refine P.mkResult (F := Nat.gcd) (hok h1.2) hnat (by simp [primSpecs, hname]) tyeq fun hvT => ?_
  have hlp : ctx.lparams.length = 0 := congrArg List.length (hok h1.2).2
  refine ⟨hlp ▸ hvT, fun a b => hlp ▸ ?_⟩
  refine (VExpr.subst_id ▸ hdone ctx.self .id .nil (fun a => Nat.gcd a.1 a.2) ?_ (a, b) :)
  rintro ⟨m, n⟩ ih hih IH
  simp only [ProbeBundle.arg, ProbeBundle.ihTy, ProbeBundle.Fc, ProbeBundle.packc,
    ProbeBundle.domc, VExpr.subst_id] at IH hih ⊢
  have hγ : (ctx.withMLC mn).Closing (.cons .id (.natLit n)) := by
    obtain ⟨_, hNatT'⟩ := hNatT hnat (Δ := []) trivial
    exact .cons .nil hNatT' (wf.hasPrimitives.natLitT hE hnat n [])
  -- one unfolding, split on the recursion variable; the fuel induction is `hdone`'s
  obtain _ | m := m
  · rw [Nat.gcd_zero_left]
    -- the probe bound one variable, `n`; closing it is the whole of the caller's obligation
    obtain ⟨_, rfl, h⟩ := heq ctx.self _ ih hγ <| by
      simpa [ProbeBundle.pihTy, ProbeBundle.parg, ProbeBundle.pγ, VLocalDecl.depth, TrTerm.of,
        VExpr.natLit, VExpr.Subst.cons, zerob, hn, TrTerm.natZero, TrTerm.fvar,
        VContext.withMLC_self] using hih
    simpa [ProbeBundle.plhs, ProbeBundle.parg, ProbeBundle.pγ, VLocalDecl.depth, TrTerm.of,
      VExpr.natLit, VExpr.Subst.cons, zerob, hn, TrTerm.natZero, TrTerm.fvar,
      VContext.withMLC_self] using h
  · -- the probe bound `n` then `m`; closing those two is the caller's whole obligation
    have hγ : (ctx.withMLC mnn).Closing (.cons (.cons .id (.natLit n)) (.natLit m)) := by
      obtain ⟨_, hNatT1⟩ := hNatT hnat (Δ := mn.vlctx) ⟨trivial, hNatT hnat trivial⟩
      exact hγ.cons hNatT1 (wf.hasPrimitives.natLitT hE hnat m [])
    obtain ⟨_, hR, heq⟩ := heq2 ctx.self _ ih hγ <| by
      simpa [ProbeBundle.pihTy, ProbeBundle.parg, ProbeBundle.pγ, VLocalDecl.depth,
        VExpr.natLit, VExpr.Subst.cons, hn1, hm, hn, succb, TrTerm.of, TrTerm.fvar,
        TrTerm.natSucc, TrTerm.natUnApp, TrTerm.app', TrTerm.wk,
        VContext.withMLC_self] using hih
    obtain ⟨arg, hy, harg, rfl⟩ := hR n m rfl rfl
    rw [Nat.gcd_rec (m+1) n]
    refine .trans ctx.Ewf hΔ ?_ <| IH (n % (m+1), m+1) arg hy
      (Nat.mod_lt _ (Nat.succ_pos m))
      (by simpa [VExpr.appN, VContext.withMLC_self] using harg)
      ⟨_, heq.choose_spec.hasType.2⟩
    simp [ProbeBundle.plhs, ProbeBundle.parg, ProbeBundle.pγ, VExpr.Subst.cons,
      VLocalDecl.depth, VExpr.natLit, hn1, hm, hn, succb, TrTerm.of, TrTerm.fvar,
      TrTerm.natSucc, TrTerm.natUnApp, TrTerm.app', TrTerm.wk] at heq ⊢
    exact heq
