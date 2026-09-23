import Lean4Lean.Verify.Environment.Primitive.Condition

/-!
The well-founded recursion recognizer: the bundle `unfoldNatWellFounded` hands back, the probes
run against it, and the fuel induction that turns one unfolding into a reflection.
-/

namespace Lean4Lean
open Lean4Lean TypeChecker
open Lean hiding Environment Exception
open Kernel

namespace Primitive

/-! ### Well-founded recursion

`unfoldNatWellFounded` reduces the definition's value to a `WellFounded.Nat.fix` application and
checks a chain of unfoldings. Its output is the equation body with recursive calls pointing at the
value under test, and what it certifies is the collection of definitional equations below.

`Nat.fix h F x` is *not* definitionally `F x (fun y _ => Nat.fix h F y)` -- `Nat.fix_eq` is a
theorem, proved through `go_congr`, and the `Nat.eager` gadget in the fuel deliberately blocks
reduction until the measure evaluates to a numeral. So the caller cannot get the unfolding in one
step; it has to consume fuel, which is why `goFn` and `F` are part of this interface rather than
hidden. The proof terms `goFn` takes are threaded but never inspected: the recognizer does not
check that they live in a proof-irrelevant position, so they are just expressions that grow as the
fuel is consumed. -/

/-! ### Ground judgements

The statements the caller ends up proving are about *closed* terms: `HasPrimitives` is a fact
about the empty context, and for `Nat.bitwise` the operator is a variable of the recognizer's
context whose evaluation behaviour only exists once it is instantiated. So the recognizer's
own context is closed off with `Ctx.Closing` and everything below is stated at `[]`. The
abbreviations themselves are at the top of the file, with the rest of the `VContext` vocabulary. -/

/-- What `unfoldNatWellFounded` hands back: the fixpoint functional `F`, which does not mention
the recursion variables at all; the packer `pack`, a closed lambda over them; and the `ih`
domain `dom`, which is a *single* expression with the packed argument as `bvar 0`, read off
`F`'s type rather than abstracted over the telescope. `c` is the context the recognizer ran in,
which is *not* the context a probe runs in -- probes bind the variables of a pattern, and
different patterns bind different variables. -/
structure ProbeBundle (c : VContext) extends Probe where
  (F' : VExpr) (hF : c.TrExprS F F')
  (pack' : VExpr) (hpack : c.TrExprS pack pack')
  (dom' : VExpr) (hdom : c.TrExprS dom dom')
  /-- The type a packed argument has to have. The recognizer reads it off `whnf (inferType F)` --
  it is `F`'s domain -- and builds `dom` as a lambda over it, so these two typings are exactly
  what it can certify about the pieces, and both are stated in the recognizer's own context
  because `F` and `dom` are telescope-free.

  Nothing here relates `Aty` to `pack`. The recognizer never checks that the packer lands in it:
  `pack` is `mkLambda fvs a₀`, whose result type is `inferType a₀`, and the only thing tested
  against that type is `f`, not `F`. So "this argument is a `Aty`" is a hypothesis of `applied`,
  which is where a caller that knows its own pattern discharges it. -/
  (Aty : VExpr)
  /-- The packer *is* a lambda telescope over the recursion domains, and its body has type `Aty` --
  the type `F` takes. The result being `Aty` rather than the unrelated `inferType a₀` is what the
  recognizer's `ty ≡ A` check buys; without it nothing connects a packed argument to `F`. -/
  (packAs : List VExpr) (packBody : VExpr)
  hpackLam : pack' = .lams packAs packBody
  hpackCtx : OnCtx (packAs.reverse ++ c.vlctx.toCtx) (c.venv.IsType c.lparams.length)
  hpackBodyT : c.venv.HasType c.lparams.length (packAs.reverse ++ c.vlctx.toCtx) packBody
    (Aty.liftN packAs.length 0)
  /-- and the domains are `Nat`, so a consumer can type its own arguments against them. -/
  hpackAsNat : packAs = List.replicate packAs.length .nat
  /-- `dom : Aty → Sort u`. -/
  hdomT : ∃ u, c.HasType dom' (.forallE Aty (.sort u))
  /-- `F : (a : Aty) → dom a → _`, which is what the recognizer's second `whnf` establishes:
  under a binder of type `Aty` it reduced `F`'s codomain to a `forallE` and took its domain. -/
  hFT : ∃ resTy, c.HasType F' (.forallE Aty (.forallE ((dom'.lift).app (.bvar 0)) resTy))

/-- What a probe needs about the pieces once applied to an argument: the `ih` binder's type is a
type, and the equation's left hand side is well typed. `Δ` is the probe's context, which extends
the recognizer's by whatever variables the pattern binds.

The argument is abstract. A probe applies `F` and `dom` to `mkAppN pack sub`, but nothing here
depends on its being *that*; what is needed is its translation and that it is an `Aty`, and both
of those are the caller's, since only the caller knows the pattern it packed. -/
theorem ProbeBundle.applied (P : ProbeBundle c)
    (W : VLCtx.FVLift c.vlctx Δ dk n k) (hΔ : Δ.WF c.venv c.lparams.length)
    (harg : TrExprS c.venv c.lparams Δ arg A)
    (hargT : c.venv.HasType c.lparams.length Δ.toCtx A (P.Aty.liftN n k)) :
    TrExprS c.venv c.lparams Δ (mkApp P.dom arg) ((P.dom'.liftN n k).app A) ∧
    c.venv.IsType c.lparams.length Δ.toCtx ((P.dom'.liftN n k).app A) ∧
    TrExprS c.venv c.lparams Δ (mkApp P.F arg) ((P.F'.liftN n k).app A) ∧
    ∃ resTy, c.venv.HasType c.lparams.length Δ.toCtx ((P.F'.liftN n k).app A)
      (.forallE ((P.dom'.liftN n k).app A) resTy) := by
  obtain ⟨u, hdomT⟩ := P.hdomT
  obtain ⟨resTy, hFT⟩ := P.hFT
  -- the two typings weaken along the probe's lift; `Aty` moves with them, and the sort does not
  have hdomTw := hdomT.weakN c.Ewf W.toCtx
  have hFTw := hFT.weakN c.Ewf W.toCtx
  simp only [VExpr.liftN] at hdomTw hFTw
  -- the `ih` domain in `F`'s type is `dom` at `bvar 0`, so instantiating it at the argument gives
  -- back exactly the `ih` type the first component built: the lift `dom'` picked up under the
  -- binder is what the instantiation consumes
  have hres := VEnv.HasType.app hFTw hargT
  simp only [VExpr.inst, ← VExpr.lift_liftN', VExpr.inst_liftN, liftVar_zero] at hres
  simp only [VExpr.instVar, Nat.lt_irrefl, if_false, if_true, VExpr.liftN_zero] at hres
  exact ⟨.app hdomTw hargT (P.hdom.weakFV c.Ewf W hΔ) harg,
    ⟨_, .app hdomTw hargT⟩,
    .app hFTw hargT (P.hF.weakFV c.Ewf W hΔ) harg, _, hres⟩

/-- The packed argument is an `Aty`. Everything the bundle records about the packer -- that it is
a telescope of `Nat`s over a body of type `Aty` -- exists for this step: a caller that knows only
that its own arguments are naturals gets the typing `applied` asks for, instead of having to type
the packed application itself, which it cannot do (nothing relates `pack`'s result type to `F`'s
domain except the recognizer's `ty ≡ A` check, and that is what `hpackBodyT` records). -/
theorem ProbeBundle.packAty (P : ProbeBundle c)
    (hnatT : ∀ Γ, OnCtx Γ (c.venv.IsType c.lparams.length) →
      c.venv.IsType c.lparams.length Γ .nat)
    (W : VLCtx.FVLift c.vlctx Δ dk n k) (hΔ : OnCtx Δ.toCtx (c.venv.IsType c.lparams.length))
    (hlen : τ.length = P.packAs.length)
    (hτnat : ∀ t ∈ τ, c.venv.HasType c.lparams.length Δ.toCtx t .nat) :
    c.venv.HasType c.lparams.length Δ.toCtx ((P.pack'.liftN n k).appN τ) (P.Aty.liftN n k) := by
  have hrev : P.packAs.reverse = List.replicate P.packAs.length .nat := by
    conv => lhs; rw [P.hpackAsNat]
    simp
  -- the packer, lifted: the domains are closed, so only the body's depth moves
  have hlam : P.pack'.liftN n k
      = VExpr.lams (List.replicate P.packAs.length VExpr.nat)
        (P.packBody.liftN n (k + P.packAs.length)) := by
    conv => lhs; rw [P.hpackLam, P.hpackAsNat]
    rw [VExpr.liftN_lams']
    simp [List.mapIdx_replicate_nat (fun i A => VExpr.liftN n A (k + i)) (fun _ => rfl)]
  have hctx : OnCtx (List.replicate P.packAs.length .nat ++ Δ.toCtx)
      (c.venv.IsType c.lparams.length) := OnCtx.natTelescope hnatT hΔ _
  have hbodyT := (hrev ▸ P.hpackBodyT).weakN c.Ewf (W.toCtx.natTelescope P.packAs.length)
  have hargs : VExpr.ArgsTyped c.venv c.lparams.length Δ.toCtx
      (List.replicate P.packAs.length .nat) .id τ := by
    rw [← hlen]; exact VExpr.ArgsTyped.natTelescope hτnat
  have hwfbody : (P.packBody.liftN n (k + P.packAs.length)).WF c.venv c.lparams.length
      (List.replicate P.packAs.length .nat ++ Δ.toCtx) := ⟨_, hbodyT⟩
  obtain ⟨hwfapp, hbeta⟩ := VExpr.lams_appN' c.Ewf hΔ (by simpa using hctx)
    (.id c.Ewf hΔ) hargs (by simpa using hwfbody)
  obtain ⟨hsub, -, -⟩ := VExpr.lams_appN c.Ewf hΔ (by simpa using hctx)
    (.id c.Ewf hΔ) (vs := τ) (e := P.packBody.liftN n (k + P.packAs.length))
    (by simpa using hlen) hwfapp
  simp only [List.reverse_replicate] at hsub
  -- the body's type, closed at the arguments: the two lifts commute, and the outer one is what
  -- the closing cancels
  have htype : ((P.Aty.liftN P.packAs.length 0).liftN n (k + P.packAs.length)).subst
      (VExpr.Subst.id.consN τ) = P.Aty.liftN n k := by
    rw [Nat.add_comm k, ← VExpr.liftN'_comm P.Aty n P.packAs.length k 0 (Nat.zero_le _),
      show P.packAs.length = τ.length from hlen.symm, VExpr.liftN_subst_consN, VExpr.subst_id]
  have hT := htype ▸ hbodyT.subst c.Ewf hsub
  simp only [VExpr.subst_id] at hbeta
  exact hlam ▸ VEnv.HasType.defeqU_l c.Ewf hΔ (hbeta.symm) hT

/-- The bundle's pieces at a closing substitution `γ` for the recognizer's context. Everything
below is built out of these, so the closing never has to be pushed through an application: it
is `VExpr.insts`, a substitution, and substitution commutes with application on the nose. -/
abbrev ProbeBundle.Fc (P : ProbeBundle c) (γ : VExpr.Subst) : VExpr := P.F'.subst γ
abbrev ProbeBundle.packc (P : ProbeBundle c) (γ : VExpr.Subst) : VExpr := P.pack'.subst γ
abbrev ProbeBundle.domc (P : ProbeBundle c) (γ : VExpr.Subst) : VExpr := P.dom'.subst γ

/-- The packed argument at a closing of the recursion telescope, and the `ih` binder's type
there. Accessors rather than extra parameters, so the statements below carry one bundle instead
of a handful of expressions that have to be kept in step.

`σ` produces *closed* arguments -- they are the literals a probe was run at -- so it is not
closed by `γ`; only the bundle's own pieces are. -/
abbrev ProbeBundle.arg (P : ProbeBundle c) (γ : VExpr.Subst) (σ : α → List VExpr) (a : α) :
    VExpr := (P.packc γ).appN (σ a)

abbrev ProbeBundle.ihTy (P : ProbeBundle c) (γ : VExpr.Subst) (σ : α → List VExpr) (a : α) :
    VExpr := (P.domc γ).app (P.arg γ σ a)

/-- One unfolding of the recursion, with the recursive calls already discharged. Stated at ground
arguments in the recognizer's own context, so `F'` and `pack'` are simply applied.

The hypothesis is restricted to arguments of smaller measure: that is all
`unfoldNatWellFounded.WF` can supply (a `go` at fuel `t` is stuck below `t`), and it is what
makes the caller's obligation the real termination argument rather than a vacuous one. -/
def ProbeBundle.Done (P : ProbeBundle c) (E : c.Ext) (γ : VExpr.Subst) (σ : α → List VExpr)
    (σm R : α → Nat) : Prop :=
  ∀ a ih, E.HasType₀ ih (P.ihTy γ σ a) →
    -- The recursive call's argument is only *definitionally* the packer at the intended
    -- literals: the recognizer hands back whatever the equation body applies `pack` to, and even
    -- its head is merely a translation of `pack`, so equal to `A y` only up to defeq. Taking
    -- the whole argument up to defeq keeps that congruence with the caller, which is where the
    -- typings live -- `TrExprS.app` carries them.
    (∀ y arg hy, σm y < σm a → E.IsDefEqU₀ arg (P.arg γ σ y) →
      E.WF₀ ((ih.app arg).app hy) →
      E.IsDefEqU₀ ((ih.app arg).app hy) (.natLit (R y))) →
    E.IsDefEqU₀ (((P.Fc γ).app (P.arg γ σ a)).app ih) (.natLit (R a))

/-! ### The fuel induction

`Nat.fix` is entered at fuel `measure x + 1` and each `Nat.rec` step spends one unit, so a value
is reached exactly when the fuel stays ahead of the measure. `Done` is one such step with the
recursive calls already discharged, and the induction below turns it into the reflection fact.

The induction is on the *fuel*, not on the argument: the recursive call is at a smaller measure
but the fuel it is given is whatever the outer call had left, so an induction on the argument
would not line the two up. `GoConverges` is the induction hypothesis, and the outer statement is
that hypothesis at fuel `σm a + 1`. -/

/-- What the fuel induction needs from the recognizer's checks, at ground arguments. This is not
a transcript of those checks: the `fix` delta step and the `eager` gadget are folded into
`entry`, since all they achieve is putting a *numeral* in the fuel position, and the beta steps
that turn the `Nat.rec` iota rule into a usable `ih` are folded into `step`. `F` is a single
expression because the recognizer asserts it does not mention the recursion variables.

`go` is *not*. It is the `Nat.fix.go` constant at `α`, `motive`, `f` and `F`, and only the last
of those is checked telescope-free, so closing the telescope at the arguments `σ a` may leave a
different term for each `a` -- hence `goFn : α → VExpr`. What saves the induction is that the
recognizer verifies the `go` equation with *every* argument of `go` bound (`lambdaTelescope go'`
rebinds `α`, `motive`, `f`, `F`, `t`), so `step` holds at whichever base point `b` one picks,
uniformly in the argument `a` it is used at. The fuel induction then runs at a fixed `b` and
`reflects` takes `b := a`, which is the base point `entry` hands it. Only the types of `ih` and
the call to `F` have to be base-independent, and they are, being built from `F` and `dom`.

The two axes of instantiation are separate. `γ` closes the *recognizer's* context, which does
not vary with the recursion: for `Nat.bitwise` it is the `Bool` operator the definition is
applied to, and it is what makes the statement ground. `α` indexes the *recursion* arguments,
which are literals and hence already closed. `R` is quantified after `γ` at the use site, so it
may depend on what `γ` denotes -- `Nat.bitwise`'s answer is a function of the operator.

The `ih` domain is not a family: `F` has one type, and `Dom` is its codomain's domain, so the
domain at `a` is `Dom.app (A a)`. -/
structure ProbeBundle.NatFixUnfold (P : ProbeBundle c) (E : c.Ext) (γ : VExpr.Subst)
    (σ : α → List VExpr) (σm : α → Nat) (ev : VExpr) where
  (goFn : α → VExpr)
  /-- The packed argument is well typed, hence defeq to itself. -/
  packT : ∀ a, ∃ T, E.HasType₀ (P.arg γ σ a) T
  /-- Entering the recursion: the value is `go` at fuel `measure + 1`. Entering at `a` is what
  fixes the base point: the fuel is a numeral only because the measure was closed at `σ a`. -/
  entry : ∀ a, ∃ pf, E.IsDefEqU₀ ((ev.subst γ).appN (σ a))
    ((((goFn a).app (.natLit (σm a + 1))).app (P.arg γ σ a)).app pf)
  /-- One unit of fuel buys one call to `F`, with the recursive calls pointing at `go` at the
  lower fuel. The `ih` it produces is at the type `Done` demands, and applying it to a packed
  argument is that lower-fuel call. Both sides use the *same* base point `b`, which is
  unconstrained: the equation is checked before anything is closed. -/
  step : ∀ b a t x pf, E.IsDefEqU₀ x (P.arg γ σ a) →
    E.WF₀ ((((goFn b).app (.natLit (t+1))).app x).app pf) → ∃ ih,
    E.HasType₀ ih (P.ihTy γ σ a) ∧
    (∀ y arg hy, E.IsDefEqU₀ arg (P.arg γ σ y) →
      E.WF₀ ((ih.app arg).app hy) →
      ∃ pf', E.IsDefEqU₀ ((ih.app arg).app hy) ((((goFn b).app (.natLit t)).app arg).app pf')) ∧
    E.IsDefEqU₀ ((((goFn b).app (.natLit (t+1))).app x).app pf)
      (((P.Fc γ).app (P.arg γ σ a)).app ih)

/-- `go` at fuel `t` computes `R` on every argument whose measure `t` outruns. Arguments are
taken up to defeq because the recognizer's equations produce them re-packed, not literally. -/
def ProbeBundle.GoConverges (P : ProbeBundle c) (E : c.Ext) (γ : VExpr.Subst) (goFn : VExpr)
    (σ : α → List VExpr) (σm R : α → Nat) (t : Nat) : Prop :=
  ∀ a arg pf, σm a < t → E.IsDefEqU₀ arg (P.arg γ σ a) →
    E.WF₀ (((goFn.app (.natLit t)).app arg).app pf) →
    E.IsDefEqU₀ (((goFn.app (.natLit t)).app arg).app pf) (.natLit (R a))

variable {c : VContext} {P : ProbeBundle c} {E : c.Ext} {γ : VExpr.Subst} {α}
  {σ : α → List VExpr} {σm R : α → Nat} {ev : VExpr}

/-- One unit of fuel. `Done` supplies the call to `F`; the induction hypothesis discharges the
recursive calls inside it, which is legitimate because `Done` only ever asks about arguments of
smaller measure and the fuel is one ahead of the measure. -/
theorem ProbeBundle.GoConverges.succ
    (hu : P.NatFixUnfold E γ σ σm ev) (hdone : P.Done E γ σ σm R) {b} {t : Nat}
    (IH : P.GoConverges E γ (hu.goFn b) σ σm R t) :
    P.GoConverges E γ (hu.goFn b) σ σm R (t+1) := by
  intro a arg pf hlt harg hwf
  obtain ⟨ih, hihT, hbeta, heq⟩ := hu.step b a t arg pf harg hwf
  refine VEnv.IsDefEqU.trans E.wf trivial heq (hdone a ih hihT ?_)
  intro y arg' hy hlt' harg' hwfy
  obtain ⟨pf', hb⟩ := hbeta y arg' hy harg' hwfy
  exact VEnv.IsDefEqU.trans E.wf trivial hb
    (IH y arg' pf' (Nat.lt_of_lt_of_le hlt' (Nat.lt_succ_iff.1 hlt)) harg'
      ⟨_, hb.choose_spec.hasType.2⟩)

theorem ProbeBundle.GoConverges.all (hu : P.NatFixUnfold E γ σ σm ev)
    (hdone : P.Done E γ σ σm R) (b) :
    ∀ t, P.GoConverges E γ (hu.goFn b) σ σm R t
  | 0 => fun _ _ _ h _ _ => absurd h (Nat.not_lt_zero _)
  | t+1 => (ProbeBundle.GoConverges.all hu hdone b t).succ hu hdone

/-- The fuel induction, at the fuel the recursion is actually entered with. -/
theorem ProbeBundle.NatFixUnfold.reflects (hu : P.NatFixUnfold E γ σ σm ev)
    (hdone : P.Done E γ σ σm R) (a) : E.IsDefEqU₀ ((ev.subst γ).appN (σ a)) (.natLit (R a)) := by
  obtain ⟨pf, hen⟩ := hu.entry a
  obtain ⟨_, hpT⟩ := hu.packT a
  exact VEnv.IsDefEqU.trans E.wf trivial hen
    (ProbeBundle.GoConverges.all hu hdone a _ a _ pf (Nat.lt_succ_self _) ⟨_, hpT⟩
      ⟨_, hen.choose_spec.hasType.2⟩)

/-- The context a probe runs its right-hand-side builder in: the caller's `mp` extended by the
`ih` binder, whose type is the bundle's `dom` at the packed argument. Named rather than inlined
so that a caller can `rintro` the conclusion without having to peel a `let`. -/
abbrev ProbeBundle.ihCtx {c : VContext} {m : MLCtx} [c.MLCWF m] (P : ProbeBundle (c.withMLC m))
    (mp : MLCtx) (subst : Array Expr) (τ : List VExpr) (n k : Nat) (id : FVarId) : MLCtx :=
  mp.vlam id `ih (mkApp P.dom (mkAppN P.pack subst))
    ((P.dom'.liftN n k).app ((P.pack'.liftN n k).appN τ)) .default

/-! ### A probe's pieces, closed off

The bundle's translations live in the *recognizer's* context, so inside a probe they carry the
lift `n k` that the probe's own variables introduced. Substituting absorbs that lift
(`VExpr.liftN_subst`) rather than cancelling it against the caller's instantiations one binder at
a time, which is what the long `simp` sets at the call sites were doing. -/

/-- A closing of a probe's context, pushed under the lift the probe's variables introduced. -/
abbrev ProbeBundle.pγ (γ : VExpr.Subst) (n k : Nat) : VExpr.Subst :=
  .lift_l (.consN (.skipN .refl n) k) γ

/-- The packed argument at a closing of the probe's context. -/
abbrev ProbeBundle.parg (P : ProbeBundle c) (τ : List VExpr) (γ : VExpr.Subst) (n k : Nat) :
    VExpr := (P.pack'.subst (pγ γ n k)).appN (τ.map (·.subst γ))

/-- The `ih` binder's type, closed off. `ih` itself is a parameter of `plhs` below rather than a
binder of the statement: `probe.WF` closes its own binder, so no caller names it. -/
abbrev ProbeBundle.pihTy (P : ProbeBundle c) (τ : List VExpr) (γ : VExpr.Subst) (n k : Nat) :
    VExpr := (P.dom'.subst (pγ γ n k)).app (P.parg τ γ n k)

/-- The equation's left hand side, closed off: this is the shape `Done` asks about. -/
abbrev ProbeBundle.plhs (P : ProbeBundle c) (τ : List VExpr) (γ : VExpr.Subst) (n k : Nat)
    (ih : VExpr) : VExpr := ((P.F'.subst (pγ γ n k)).app (P.parg τ γ n k)).app ih

/-- One `probe` call. It introduces the `ih` binder and hands the caller's builder the equation
`F a ih ≡ rhs` -- as an implication into whatever the caller wants to conclude, since `probe`
returns `Unit` and there is nowhere else to put it.

`replaceFVars` does not appear: applying the bundle's abstractions to `subst` is exactly what
`hτ` expresses on the translation side. `fail` is the caller's, so it is a hypothesis here
rather than a field of the bundle.

The probe runs in `mp`, any extension of the recognizer's own `m` -- these are the pattern's
variables, and each probe may bind a different number of them; `W` is that extension. The
bundle's translations are closed, so they need no lifting; only `τ` does.

`hFV` owes the right hand side's well-formedness: `probe` typechecks it, and `checkType` is only
specified on terms whose free variables are in the context. The left hand side needs no such
hypothesis -- it is built from the bundle and `subst`, whose translations already place their
variables.

The conclusion is `Done`'s shape: an arbitrary closing `γ` of the probe's own variables, an
arbitrary *closed* `ih` of the domain type, and the equation between closed terms. The `ih`
binder does not appear -- neither the context it extends nor its translation `.bvar 0` -- so a
caller never instantiates a telescope. What replaces the syntactic `Q` of an earlier version is
`R`, the caller's *semantic* description of the right hand side; `hR` owes it, and gets the
closing of the probe's own context (`hcl`) to discharge it with, since that is the one thing it
cannot build without naming the binder's type. Both hypotheses are plain propositions about
`mkRhs (.fvar id)`: `mkRhs` is a function, so nothing here is monadic. -/
theorem ProbeBundle.probe.WF {c : VContext} {m mp : MLCtx} [cwf : c.MLCWF m] [cwfp : c.MLCWF mp]
    {P : ProbeBundle (c.withMLC m)} {s : VState} {fail : ∀ {α}, M α}
    {subst : Array Expr} {mkRhs : Expr → Expr}
    {R : (c.withMLC m).Ext → VExpr.Subst → VExpr → VExpr → Prop}
    {τ : List VExpr} {dk n k}
    (W : VLCtx.FVLift m.vlctx mp.vlctx dk n k)
    (hfail : ∀ {α c s Q}, (@fail α).WF c s Q)
    (hτ : subst.toList.Forall₂ (c.withMLC mp).TrExprS τ)
    -- the pattern's arguments. The recognizer never checks that a packed argument is an `Aty` --
    -- `pack`'s result type is `inferType a₀`, and only `f` is tested against it, not `F` -- so
    -- that typing is `packAty`'s job, and all it asks of the caller is what the caller actually
    -- knows about its own pattern: that the arguments are naturals, and that there are as many of
    -- them as the packer has binders. The *translation* of the packed application needs no
    -- hypothesis at all: `TrExprS.appN` reads the intermediate typings back off the typing.
    (hnat : c.venv.contains ``Nat)
    (hτlen : τ.length = P.packAs.length)
    (hτnat : ∀ t ∈ τ, c.venv.HasType c.lparams.length mp.vlctx.toCtx t VExpr.nat)
    (hR : ∀ id, let m' := P.ihCtx mp subst τ n k id; ∀ [c.MLCWF m'],
      (mkRhs (.fvar id)).FVarsIn (· ∈ (c.withMLC (P.ihCtx mp subst τ n k id)).vlctx.fvars) ∧
      ((∀ (E : (c.withMLC m).Ext) γ ih, (E.cast (c' := c.withMLC mp)).Closing γ →
          E.HasType₀ ih (P.pihTy τ γ n k) →
        (E.cast (c' := c.withMLC m')).Closing (γ.cons ih)) →
      ∀ rhsv, (c.withMLC m').TrExprS (mkRhs (.fvar id)) rhsv →
        ∀ (E : (c.withMLC m).Ext) γ ih, (E.cast (c' := c.withMLC mp)).Closing γ →
          E.HasType₀ ih (P.pihTy τ γ n k) →
          R E γ ih (rhsv.subst (γ.cons ih)))) :
    (P.toProbe.probe subst fail mkRhs).WF (c.withMLC mp) s fun _ _ =>
    ∀ (E : (c.withMLC m).Ext) γ ih, (E.cast (c' := c.withMLC mp)).Closing γ →
      E.HasType₀ ih (P.pihTy τ γ n k) →
      ∃ v, R E γ ih v ∧ E.IsDefEqU₀ (P.plhs τ γ n k ih) v := by
  have hpackT : c.venv.HasType c.lparams.length mp.vlctx.toCtx
      ((P.pack'.liftN n k).appN τ) (P.Aty.liftN n k) :=
    P.packAty (fun _ h => c.hasPrimitives.natIsType' c.Ewf hnat h)
      W (c.withMLC mp).Δwf.toCtx hτlen hτnat
  obtain ⟨hdomTr, hdomTy, hFpackTr, resTy, hFpackT⟩ :=
    P.applied W cwfp.wf.tr.wf
      (Expr.mkAppN_eq _ _ ▸ TrExprS.appN c.Ewf.orderedStrong (c.withMLC mp).Δwf.toCtx
        (P.hpack.weakFV c.Ewf.ordered W cwfp.wf.tr.wf) hτ ⟨_, hpackT⟩) hpackT
  unfold Probe.probe
  refine M.WF.withLocalDecl hdomTr hdomTy .rfl ?_
  intro id cwf' s' hs hres
  -- inside the binder: `ih` is the variable, and the head weakens past it
  have hih : (c.withMLC _ (wf := cwf')).TrExprS (.fvar id) (.bvar 0) :=
    .fvar VLCtx.find?_vlam_self
  have hihT : (c.withMLC _ (wf := cwf')).HasType (.bvar 0)
      (((P.dom'.liftN n k).app ((P.pack'.liftN n k).appN τ)).lift) := .bvar .zero
  have hFp := hFpackTr.weakFV c.Ewf (.skip_fvar _ _ .refl) cwf'.wf.tr.wf
  have hFpT := hFpackT.weakN c.Ewf.ordered
    (VLCtx.FVLift.skip_fvar (id, (mkApp P.dom (mkAppN P.pack subst)).fvarsList)
      (.vlam ((P.dom'.liftN n k).app ((P.pack'.liftN n k).appN τ))) .refl).toCtx
  have hlhs : (c.withMLC _ (wf := cwf')).TrExprS
      (mkApp2 P.F (mkAppN P.pack subst) (.fvar id))
      ((((P.F'.liftN n k).app ((P.pack'.liftN n k).appN τ)).lift).app (.bvar 0)) :=
    .app hFpT hihT hFp hih
  -- the closing extended by the value the caller gives `ih`; its typing obligation is the
  -- caller's hypothesis, and the binder's own well-formedness is what `withLocalDecl` checked
  obtain ⟨_, hdomTyT⟩ := hdomTy
  have hcl : ∀ (E : (c.withMLC m).Ext) γ ih, (E.cast (c' := c.withMLC mp)).Closing γ →
      E.HasType₀ ih (P.pihTy τ γ n k) →
      (E.cast (c' := c.withMLC _ (wf := cwf'))).Closing (γ.cons ih) := fun E _ ih hγ hihT =>
    .cons hγ (E.monoT hdomTyT) (by
      show E.HasType₀ ih _
      simpa [pihTy, parg, pγ, VExpr.liftN_subst, VExpr.subst_appN] using hihT)
  refine .bind (checkType.WF (hR id).1) fun _ _ _ ⟨rhsv, _, _, hrhs, _, _⟩ => ?_
  refine .bind (isDefEq.WF hlhs hrhs) fun b _ _ hb => ?_
  split <;> [skip; exact hfail]
  refine .pure fun E γ ih hγ hihT => ⟨_, (hR id).2 hcl _ hrhs E γ ih hγ hihT, ?_⟩
  have hsub := (E.mono (hb ‹_›)).subst E.wf (hcl E γ ih hγ hihT)
  simp [plhs, parg, pγ, VExpr.Subst.cons, VExpr.liftN_subst, VExpr.subst_appN] at hsub ⊢
  exact hsub

-- def ProbeBundle.probe.WF (a₀ F dom : Expr) (fail : ∀ {α}, M α) (fvs : Array Expr) : Prop :=
--   ∀ subst mkRhs τ, subst.toList.Forall₂ c.TrExprS τ →
--     ∀ {β}, ∀ σ' : β → α,
--     (∀ b, c.IsDefEqU (F (σ' b) ih)) →
--     ∀ τn : List (α → Nat),
--     (∀ a ih ih', c.TrExprS lhs (f.app a |>.app ih') → c.TrExprS ih ih' →
--       (∀ {β}, ∀ σ' : β → List VExpr, ∀ τn : List (α → Nat),
--         τ.Forall₂ (fun x n => ∀ a, c.IsDefEqU (x.insts (σ a)) (.natLit (n a))) τn →
--         True) →
--       (mkRhs lhs ih).WF (c.withMLC m' (wf := cwf')) s'' fun rhs _ =>
--         ∃ rhsv, (c.withMLC m' (wf := cwf')).TrExprS rhs rhsv ∧
--         ((c.withMLC m' (wf := cwf')).IsDefEqU (.app (.app H.F aV) (.bvar 0)) rhsv → Q)) →
--     (r.1 subst mkRhs).WF (c.withMLC m) s' fun _ _ => Q)

/-! ### The `go` step equation, one telescope at a time

`go α motive f F (succ t) x hfuel ≡ F x fun y hy => go α motive f F t y pf` is checked with every
argument of `go` still bound -- that is what makes it uniform in them -- so it is exported under
the binders the recognizer's three telescopes opened, and closing them at a base point is the
consumer's business. Each level takes the context its telescope was entered at, and hands the
next level the context it opened; the `Expr`-level variables travel along because that is what
lets the equations be stated without computing de Bruijn indices for them here.
-/

/-- Innermost: the induction hypothesis is the recursor at the lower fuel, applied to the smaller
argument and its `Dom` proof. `natRec` and `tg` come from two levels up, where `go`'s own
telescope bound them. Like `lambdaTelescope.Inv`, each level is indexed by the base context and
the `MLCtx` its telescope was entered at, rather than by the `VContext` that pair builds: `Inv`
is indexed that way, and re-wrapping `withMLC` at every level only obscures that the environment
never changes. -/
def unfoldNatWellFounded.StepIH (c : VContext) (m3 : MLCtx) [c.MLCWF m3]
    (natRec tg : Expr) (ihv : VExpr) : Prop :=
  ∃ (m4 : MLCtx) (cwf4 : c.MLCWF m4) (n4 : Nat) (hn4 : n4 ≤ m4.length)
    (yg hy iharg : Expr) (As4 : List VExpr) (ihbv : VExpr),
    m4.dropN n4 hn4 = m3 ∧
    @lambdaTelescope.Inv c m3 m4 cwf4 #[yg, hy] n4 hn4 As4 ihv ihbv ∧
    (@VContext.withMLC c m4 cwf4).TrExprS (.app (.app (.app natRec tg) yg) iharg) ihbv

/-- The successor branch: a function of the recursion argument and its `Dom` proof, whose head is
`F` at that argument and whose second argument is the induction hypothesis. -/
def unfoldNatWellFounded.StepBranch (c : VContext) (m2 : MLCtx) [c.MLCWF m2]
    (natRec tg Fg : Expr) (gorv : VExpr) : Prop :=
  ∃ (m3 : MLCtx) (cwf3 : c.MLCWF m3) (n3 : Nat) (hn3 : n3 ≤ m3.length)
    (xg hx : Expr) (As3 : List VExpr) (Fxv ihv : VExpr),
    m3.dropN n3 hn3 = m2 ∧
    @lambdaTelescope.Inv c m2 m3 cwf3 #[xg, hx] n3 hn3 As3 gorv (.app Fxv ihv) ∧
    (@VContext.withMLC c m3 cwf3).TrExprS (.app Fg xg) Fxv ∧
    @StepIH c m3 cwf3 natRec tg ihv

/-- `go`'s own telescope: the four `fix` arguments again, then the fuel. Its body is a recursor
applied to the fuel variable -- the recognizer checks that the recursor part does not mention the
fuel, which is what makes the recursion uniform in it -- and one unit of fuel reduces that
recursor to the successor branch. -/
def unfoldNatWellFounded.Step (c : VContext) (m : MLCtx) [cwf : c.MLCWF m] (gohv : VExpr) : Prop :=
  ∃ (m2 : MLCtx) (cwf2 : c.MLCWF m2) (n2 : Nat) (hn2 : n2 ≤ m2.length)
    (a1 a2 a3 Fg tg natRec : Expr) (As2 : List VExpr) (goh2 nrv tgv tgv' gorv : VExpr),
    -- the head as the recognizer unfolded it, which is what the telescope was run on
    (@VContext.withMLC c m cwf).IsDefEqU goh2 gohv ∧
    m2.dropN n2 hn2 = m ∧
    @lambdaTelescope.Inv c m m2 cwf2 #[a1, a2, a3, Fg, tg] n2 hn2 As2 goh2 (.app nrv tgv') ∧
    (@VContext.withMLC c m2 cwf2).TrExprS natRec nrv ∧
    -- the recursor does not mention the fuel variable -- the recognizer's
    -- `!natRec.containsFVar t.fvarId!`. Without this, closing the telescope at two different
    -- fuels would give two unrelated recursors, and `step` relates fuel `t+1` on one side to
    -- `succ t` on the other. `lift` says it exactly: substituting a `cons` into a lifted term
    -- ignores the head, so the closing is independent of what the fuel is closed at.
    (∃ nrv₀ : VExpr, (@VContext.withMLC c m2 cwf2).IsDefEqU nrv nrv₀.lift) ∧
    -- the body is well typed where it stands, which is what closing it at the *lower* fuel needs:
    -- there the application `step` is handed says nothing, being at `t+1`
    VExpr.WF c.venv c.lparams.length (@VContext.withMLC c m2 cwf2).vlctx.toCtx (.app nrv tgv') ∧
    (@VContext.withMLC c m2 cwf2).TrExprS tg tgv ∧
    -- the recursor is applied to the fuel variable: `==` at the `Expr` level, defeq below it
    (@VContext.withMLC c m2 cwf2).IsDefEqU tgv tgv' ∧
    (@VContext.withMLC c m2 cwf2).IsDefEqU gorv (.app nrv (.app .natSucc tgv)) ∧
    @StepBranch c m2 cwf2 natRec tg Fg gorv

/-- The eager gadget: the recognizer checks `eager n ≡ if n == n then n else n` at a fresh `Nat`
variable. Both branches are `n`, so the conditional *is* `n` -- but only once the decision is known
to be a literal, and at a variable it is not: `Condition.bool`'s `WF_ite` fires at `be` with
`IsDefEqU be (.boolLit b)`, which `Nat.beq x x` at a variable does not supply.

Exporting that as an *implication* would be useless: its premise would live at the probe context,
so no consumer could ever supply it. The instantiation therefore happens in the block, where the
probe binder is still in scope -- `instDF` at a literal, the conditional rebuilt there, and only
then does the decision reduce. What escapes is the gadget at literals, which is all it is used
at, the fuel being a numeral by the time `NatFixUnfold.entry` reads it. -/
def unfoldNatWellFounded.Eager (c : VContext) (m : MLCtx) [cwf : c.MLCWF m]
    (eagerFn : Expr) : Prop :=
  ∃ (eagerv : VExpr) (idx : FVarId),
    c.MLCWF (m.vlam idx `x q(Nat) .nat .default) ∧
    (@VContext.withMLC c m cwf).TrExprS eagerFn eagerv ∧
    -- At a *literal* the gadget is the identity. Stating it that way rather than as an
    -- implication conditioned on the decision being a boolean literal is forced: that hypothesis
    -- would live at the probe context, where `Nat.beq x x` is precisely what is not a literal, so
    -- no consumer could ever supply it. The instantiation therefore happens here, where the probe
    -- binder is still in scope -- which is also the only place `Nat.beq`'s reflection is usable.
    ∀ k : Nat, (@VContext.withMLC c m cwf).IsDefEqU
      (.app eagerv (.natLit k)) (.natLit k)

/-- What the ``withLocalDecl `a`` block of `unfoldNatWellFounded` exports, at the context `ca` that
block opened. The block's four checks (see the comments in `unfoldNatWellFounded`) are
the only reason it exists, so this carries them forward verbatim; the intermediate terms they are
stated at -- `go`, the eager gadget, the fuel, the proof argument -- are the block's own and get
existentially quantified along with their translations.

The variable the block binds is quantified by the caller, not here: `ca` is already the extended
context and `a` is the variable. That is what makes the checks exportable at all -- they are plain
`Prop`s about a context the proof may keep naming after the *code*'s local context is reset.

Only the first two checks are recorded so far. The eager-gadget equation and the `go` step equation
live under further binders (the probe's `x`, and the three telescopes below it) and get their own
nested existentials as those blocks are discharged. -/
def unfoldNatWellFounded.BlockQ (c : VContext) (m : MLCtx) [cwf : c.MLCWF m]
    (fixFn f F a₀ body a : Expr) : Prop :=
  let ca := @VContext.withMLC c m cwf
  -- `f a₀ ≡ body`: the fixpoint's own measure agrees with the measure the caller supplied
  (∃ fv a₀v, ca.TrExprS f fv ∧ ca.TrExprS a₀ a₀v ∧ ca.TrExpr body (.app fv a₀v)) ∧
  -- `fix α motive f F a ≡ go α motive f F (eager (succ (f a))) a pf`, the entry equation: the
  -- fixpoint at the bound variable reduces to `go` at the same arguments, fuelled by the measure.
  -- The recognizer's "same arguments" test is `==` rather than equality, but `TrExprS.eqv` spends
  -- it on the spot, so the arguments `go` was found at need not survive into the statement.
  (∃ (goHead : Expr) (args4 : List Expr) (eagerFn fuelN pf : Expr)
      (Fv gohv gov fuelNv fav : VExpr),
    ca.TrExprS (Expr.mkAppList goHead (args4 ++ [.app eagerFn fuelN, a, pf])) gov ∧
    ca.TrExprS F Fv ∧ ca.TrExpr (.app fixFn a) gov ∧
    -- and the fuel is the successor of the measure at that variable
    ca.TrExprS fuelN fuelNv ∧ ca.TrExprS (.app f a) fav ∧
    ca.IsDefEqU fuelNv (.app .natSucc fav) ∧
    -- the step equation, at the same `go`. The four arguments the recognizer did not look at stay
    -- packed in `args4`; they are the ones `Step`'s telescope binds again, so the consumer needs
    -- only their number to line the two up.
    -- the fourth is `F` itself: the recognizer's `==` on `go`'s arguments covers it, and `step`
    -- needs it, since the call to `F` it produces has to be the bundle's `F` and not merely
    -- whatever `go` was applied to
    (∃ b1 b2 b3, args4 = [b1, b2, b3, F]) ∧ ca.TrExprS goHead gohv ∧ Step c m gohv ∧
    -- and the fuel's head is the eager gadget
    Eager c m eagerFn)

set_option maxHeartbeats 1000000 in
/-- The recognizer's own half: it returns a bundle, and the unfolding facts hold of it. This is
the plumbing -- tracking translations through `lambdaTelescope`, `whnfCore`, `unfoldDefinition`
and the `withApp` destructuring, and turning the checked defeq tests into the fields of
`NatFixUnfold`. It is independent of the fuel induction, which is `NatFixUnfold.reflects`.

`vb` is the precondition left behind by moving `Condition.bool.check` out to the callers: the
`eager` gadget is recognized by comparing against `Condition.bool.ite`, and nothing here
verifies that conditional any more. `WF_ite` quantifies over context extensions, which is what
lets it be used here: the comparison happens under the measure telescope, the `a` binder and the
probe, three binders past the `c` the caller checked at.

Two things this proof should do, worked out before writing it and recorded here because the
facts it collects -- the fixpoint, its `Nat.rec` unrolling, the `eager` gadget, the measure
function -- are local variables of the proof and never appear in a statement.

*The packer is used applied, never as an abstraction.* The recognizer finds the packed argument
as a term `a₀` and returns `lctx.mkLambda fvs a₀`, so the two have to be reconciled by beta
somewhere -- and `mkLambda` is not a homomorphism for application, which is what forced closing
substitutions in the first place. Do it here, once, and state everything else in terms of the
packer *applied* to the telescope: `ProbeBundle.applied` already gives the translation of
`mkAppN pack sub` as `pack'` applied, so that is the form everything downstream is in. Same for
the value and the measure, which are lifted over the telescope and applied to its variables, so
that closing turns the application into the ground recursion arguments and absorbs the lift
(`VExpr.liftN_subst`).

*Close the telescope per base point.* The induction needs `go` to be the same functional at every
recursion argument, and `go` may mention the telescope -- the recognizer checks only `F`. So
close the telescope at `σ b` for a base point `b` and derive `NatFixUnfold.step` there; it is
uniform in the argument it is used at because the recognizer verifies the `go` equation with
every argument of `go` still bound. `entry` at `a` fixes the base point to `a`, which is the one
`reflects` runs the induction at. `lambdaTelescope.Inv` supplies the closing (its domains and
`VExpr.lams_appN`), and `hσm` supplies the arguments' typing, which is what makes that closing a
`VEnv.Ctx.SubstEq`. -/
theorem unfoldNatWellFounded.WF' {c : VContext} {m₀ : MLCtx} [c.MLCWF m₀] {s : VState}
    {e meas : Expr} {fail : ∀ {α}, M α} {ev mv : VExpr}
    (hev : (c.withMLC m₀).TrExprS e ev) (hmv : (c.withMLC m₀).TrExprS meas mv)
    (hnat : c.venv.contains ``Nat) (hsafe : c.safety = .safe)
    {wb : Condition.WF c Condition.bool}
    (hbool : wb.WF_ite (natOnly := true)) (hbeval : wb.IteEval (natOnly := true))
    {α} (σ : α → List VExpr) (σm : α → Nat)
    (hσm : ∀ (E : (c.withMLC m₀).Ext) γ, E.Closing γ → ∀ a,
      E.IsDefEqU₀ ((mv.subst γ).appN (σ a)) (.natLit (σm a)))
    (hnd : meas.natBinderTypes = true)
    (hfail : ∀ {α c s Q}, (@fail α).WF c s Q) :
    (unfoldNatWellFounded e meas fail).WF (c.withMLC m₀) s fun r _ =>
      ∃ P : ProbeBundle (c.withMLC m₀), r = P.toProbe ∧
        P.packAs.length = meas.lambdaArity ∧
        ((∀ a, (σ a).length = meas.lambdaArity) →
          ∀ (E : (c.withMLC m₀).Ext) γ, E.Closing γ →
            Nonempty (P.NatFixUnfold E γ σ σm ev)) := by
  -- `fail` never returns, so a `fail` sitting in front of a continuation proves whatever the
  -- continuation was supposed to: this is the shape every `else` branch of the checks has.
  have hfailb : ∀ {α β} {k : α → M β} {c s Q}, (fail >>= k).WF c s Q :=
    .bind (hfail (Q := fun _ _ => False)) fun _ _ _ h => h.elim
  unfold unfoldNatWellFounded
  -- the measure's telescope: `fvs` are the recursion variables, `body` the measure at them
  refine lambdaTelescope.WF hmv ?_
  intro fvs m' _ s' body body' n hn As hs hdrop harr hlam hinv harity hbody
  -- The value at the recursion variables, weakened over the telescope. Its *typing* is what the
  -- `checkType` in the recognizer buys: nothing relates the measure's telescope to the value's,
  -- so without it `mkAppN e fvs` need not translate at all and `whnfCore.WF` does not apply.
  -- `checkType` hands back the translation, and `TrExprS.uniq` against `hev.weakFV` and
  -- `hinv.vars` identifies it as `(ev.liftN n 0).appN` at the variables -- which is the form that
  -- closing turns into `(ev.subst γ).appN (σ a)`, the left hand side of `NatFixUnfold.entry`.
  have hevw := hev.weakFV c.Ewf hinv.lift ‹c.MLCWF m'›.wf.tr.wf
  have hfvs : ∀ a ∈ fvs.toList, FVarsIn (· ∈ (c.withMLC m').vlctx.fvars) a := fun a ha =>
    hinv.vars.forall_left (fun h => h.fvarsIn) a (by simpa using ha)
  have hfv : FVarsIn (· ∈ (c.withMLC m').vlctx.fvars) (mkAppN e fvs) := by
    rw [Expr.mkAppN_eq]; exact FVarsIn.appN hevw.fvarsIn hfvs
  refine .bind (checkType.WF hfv) fun _ _ _ ⟨_, _, _, hX, _, hXT⟩ => ?_
  -- the application's translation is the value's applied to the variables': `TrExprS` takes an
  -- application apart without any typing, so `checkType`'s output is identified with the pieces
  rw [Expr.mkAppN_eq] at hX
  obtain ⟨X₀, xs, rfl, hX₀, hxs⟩ := hX.appN_inv
  rw [← Expr.mkAppN_eq] at hX
  refine .bind (whnfCore.WF hX) fun e1 _ _ h1 => ?_
  obtain ⟨_, _, he1S, he1eq⟩ := h1
  refine .bind (unfoldDefinition.WF he1S) fun e2 _ _ h2 => ?_
  obtain ⟨_, he2S, he2eq⟩ := h2
  refine .bind (whnfCore.WF he2S) fun e3 _ _ h3 => ?_
  obtain ⟨_, _, he3S, he3eq⟩ := h3
  rw [Expr.withApp_eq]
  -- the fixpoint application taken apart: `AppStack` carries a translation for the head and one
  -- for each argument, which is what the two pattern matches below then name
  have ⟨fixv, stk⟩ := AppStack.build <| e3.mkAppList_getAppArgsList ▸ he3S
  split <;> try exact hfail
  -- the arity match is on an array literal, which `split` cannot take apart: case the underlying
  -- list instead, and every length but five reduces to `fail`
  generalize hargs : e3.getAppArgs = args
  obtain ⟨largs⟩ := args
  rcases largs with _|⟨α,_|⟨motive,_|⟨f,_|⟨F,_|⟨a₀,_|l⟩⟩⟩⟩⟩ <;> try exact hfail
  let +generalize G (α:Expr) := _
  unfold unfoldWellFounded.match_11; simp [Array.getLit]; unfold G
  extract_lets -underBinder fixFn
  -- peel the stack: one `TrExprS` per argument, `α`, `motive`, `f`, `F` and the packed argument
  have hlist : e3.getAppArgsList = [α, motive, f, F, a₀] := by
    rw [← Expr.getAppArgs_toList, hargs]
  rw [hlist] at stk
  let .app _ _ _ hα stk := stk
  let .app _ _ _ hmot stk := stk
  let .app _ _ _ hfm stk := stk
  let .app _ _ _ hFF stk := stk
  let .app hfixT ha₀A hfixS ha₀ stk := stk
  -- `a`, the variable the `go` equation is checked at, standing for the packed argument
  refine .bind (inferType.WF ha₀) fun ty _ _ ⟨tyv, _, _, htyS, hty⟩ => ?_
  -- Next: `M.WF.withLocalDecl htyS (hty.isType c.Ewf.ordered (c.withMLC m').Δwf.toCtx)`, bound
  -- into the rest -- `withLocalDecl` is followed by `getLCtx` and the `F` closedness test, so it
  -- is a `.bind`, not the tail.
  --
  -- `Q` is fixed outside the binder, but that costs nothing. What the body checks are judgements
  -- in the context the binder opened, and those are plain `Prop`s: at the `VExpr` level the
  -- context is `ty' :: m'.vlctx.toCtx`, which names nothing local, and even the variable itself
  -- may be quantified and carried as `c.withMLC (m'.vlam id ..)`, the way `probe.WF`'s `hR`
  -- does. It is the *code* that must stop using the variable when the block ends, because the
  -- local context is reset there; the proof is under no such constraint. So the checks export
  -- verbatim, and reading them at the packed argument is the induction's business at the end.
  refine .bind (Q := fun _ _ => ∃ ida, ∃ cwfa : c.MLCWF (m'.vlam ida `a ty tyv .default),
      @BlockQ c (m'.vlam ida `a ty tyv .default) cwfa fixFn f F a₀ body (.fvar ida))
    (M.WF.withLocalDecl htyS (hty.isType c.Ewf.ordered (c.withMLC m').Δwf.toCtx) .rfl ?_) ?_
  · intro ida; let +generalize ma := MLCtx.vlam ..; intro cwfa sa hsa hresa
    -- everything found outside the binder weakens over it, and `a` itself is `bvar 0`
    have hfw := hfm.weakFV c.Ewf (.skip_fvar _ _ .refl) cwfa.wf.tr.wf
    have ha₀w := ha₀.weakFV c.Ewf (.skip_fvar _ _ .refl) cwfa.wf.tr.wf
    have hFw := hFF.weakFV c.Ewf (.skip_fvar _ _ .refl) cwfa.wf.tr.wf
    have hbodyw := hbody.weakFV c.Ewf (.skip_fvar _ _ .refl) cwfa.wf.tr.wf
    have hida : (c.withMLC _ (wf := cwfa)).TrExprS (.fvar ida) (.bvar 0) :=
      .fvar VLCtx.find?_vlam_self
    refine .bind (checkType.WF
      (show FVarsIn _ (f.app (.fvar ida)) by exact ⟨hfw.fvarsIn, hida.fvarsIn⟩))
      fun _ _ _ ⟨_, _, _, hfaS, hfaTy, hfaT⟩ => ?_
    refine .bind (isDefEq.WF hfaTy (c.hasPrimitives.trNat c.Ewf hnat))
      fun _ _ _ hfaNat => ?_
    split <;> [skip; exact hfailb]
    -- `f` has a pi type -- that `checkType (f.app a)` succeeded is how we know -- and its domain
    -- is the binder's type, so `f` also applies to the packed argument
    let .app hfT haT hfS haS := hfaS
    cases TrExprS.unique (by simp [TrExprS.IsUnique]) haS hida
    have hdom := (VEnv.HasType.bvar .zero).uniqU c.Ewf
      (c.withMLC _ (wf := cwfa)).Δwf.toCtx haT
    have ha₀T := VEnv.HasType.defeqU_r c.Ewf (c.withMLC _ (wf := cwfa)).Δwf.toCtx hdom
      (hty.weakN c.Ewf.ordered
        (VLCtx.FVLift.skip_fvar (ida, ty.fvarsList) (.vlam tyv) .refl).toCtx)
    refine .bind (isDefEq.WF (.app hfT ha₀T hfS ha₀w) hbodyw) fun _ _ _ hfa₀ => ?_
    split <;> [skip; exact hfailb]
    -- `fix α motive f F` applied to the variable: the stack's last step already typed it at the
    -- packed argument, and the binder's type is that argument's, so it applies to the variable
    have hA := (hty.uniqU c.Ewf (c.withMLC m').Δwf.toCtx ha₀A).weakN c.Ewf
      (VLCtx.FVLift.skip_fvar (ida, ty.fvarsList) (.vlam tyv) .refl).toCtx
    have hidaT := VEnv.HasType.defeqU_r c.Ewf (c.withMLC _ (wf := cwfa)).Δwf.toCtx hA
      (VEnv.HasType.bvar .zero)
    have hfixw := hfixS.weakFV c.Ewf (.skip_fvar _ _ .refl) cwfa.wf.tr.wf
    have hfixTw := hfixT.weakN c.Ewf.ordered
      (VLCtx.FVLift.skip_fvar (ida, ty.fvarsList) (.vlam tyv) .refl).toCtx
    refine .bind (unfoldDefinition.WF (.app hfixTw hidaT hfixw hida)) fun _ _ _ h4 => ?_
    obtain ⟨_, he4S, he4eq⟩ := h4
    refine .bind (whnfCore.WF he4S) fun e5 _ _ h5 => ?_
    obtain ⟨_, _, he5S, he5eq⟩ := h5
    rw [Expr.withApp_eq]
    -- the `go` application: same destructuring as the `fix` one, seven arguments this time
    have ⟨gov, stk2⟩ := AppStack.build <| e5.mkAppList_getAppArgsList ▸ he5S
    generalize hargs2 : e5.getAppArgs = args2
    obtain ⟨largs2⟩ := args2
    rcases largs2 with
      _|⟨α2,_|⟨motive2,_|⟨f2,_|⟨F2,_|⟨fuel,_|⟨a2,_|⟨pf,_|l2⟩⟩⟩⟩⟩⟩⟩ <;> try exact hfail
    let +generalize G (α:Expr) := _
    unfold unfoldNatWellFounded.match_3; simp [Array.getLit]; unfold G
    -- the recognizer insists `go` was handed back the very arguments `fix` had
    extract_lets -underBinder jp
    split <;> [skip; exact hfailb]
    rename_i hsame
    -- and that the fuel is `eager` applied to something
    cases fuel <;> try exact hfail
    rename_i eagerFn fuelN
    -- peel this stack too: the proof `pf` is the one argument whose type is inferred here
    have hlist2 : e5.getAppArgsList = [α2, motive2, f2, F2, .app eagerFn fuelN, a2, pf] := by
      rw [← Expr.getAppArgs_toList, hargs2]
    rw [hlist2] at stk2
    let .app _ _ hfixGoS hα2 stk2 := stk2
    let .app _ _ _ hmot2 stk2 := stk2
    let .app _ _ _ hf2 stk2 := stk2
    let .app _ _ _ hF2 stk2 := stk2
    let .app _ _ _ hfuel stk2 := stk2
    let .app _ _ _ ha2 stk2 := stk2
    let .app _ _ _ hpf stk2 := stk2
    refine .bind (inferType.WF hpf) fun _ _ _ ⟨_, _, _, hpfTyS, hpfT⟩ => ?_
    -- `pf`'s type is a proposition, which is what makes the proof argument ignorable: `Done` and
    -- `NatFixUnfold.step` quantify it away rather than tracking what it proves
    refine .bind (isProp.WF hpfTyS) fun _ _ _ hprop => ?_
    split <;> [rename_i hpropT; exact hfailb]
    -- the fuel is `Nat.succ` of the measure at `a`: this is the check `NatFixUnfold.entry` is
    -- built from, once `hσm` says what the measure is at ground arguments
    let .app hfuelFT hfuelNT hfuelF hfuelN := hfuel
    have hfaNatT := VEnv.HasType.defeqU_r c.Ewf (c.withMLC _ (wf := cwfa)).Δwf.toCtx
      (hfaNat ‹_›) hfaT
    refine .bind (isDefEq.WF hfuelN (.app (TrExprS.natSucc c.hasPrimitives hnat).2 hfaNatT
      (TrExprS.natSucc c.hasPrimitives hnat).1 (.app hfT haT hfS hida))) fun _ _ _ hfuelEq => ?_
    split <;> [skip; exact hfailb]
    -- `Nat.beq` has to be in the environment for the `eager` gadget's conditional to mean
    -- anything; `hbool` supplies the rest
    refine .bind getEnv.WF fun _ _ _ h => ?_
    obtain ⟨rfl, _⟩ := h
    extract_lets -underBinder jp4
    split <;> [skip; exact hfailb]
    rename_i hbeq
    -- the `eager` gadget: `eager x` is the `Nat`-valued conditional `if x == x then x else x`,
    -- which is where `hbool` is spent
    refine .bind (Q := fun _ _ => @Eager c ma cwfa eagerFn)
      (M.WF.withNatProbe c.hasPrimitives hnat .rfl ?_) fun _ _ _ heagerQ => ?_
    · intro idx mx cwfx sx hsx hresx
      -- `Nat.beq` translates: it is a reserved primitive, so the environment check transfers to
      -- the model, and `HasPrimitives` records the typing that `const_inv` reads the arity off
      have hbeqv := VContext.contains_primitive hsafe hbeq
      have hbeqC := TrExprS.ofConst (Us := c.lparams)
        (Δ := (c.withMLC _ (wf := cwfx)).vlctx) c.Ewf (c.hasPrimitives.natBEq hbeqv).1
        (by simp [VExpr.instL, VExpr.nat, VExpr.bool])
      have hidx : (c.withMLC _ (wf := cwfx)).TrExprS (.fvar idx) (.bvar 0) :=
        .fvar VLCtx.find?_vlam_self
      have hidxT : (c.withMLC _ (wf := cwfx)).HasType (.bvar 0) .nat := .bvar .zero
      -- `Nat.beq x x : Bool`, the decision the gadget's conditional is on
      have hbeqT1 : (c.withMLC _ (wf := cwfx)).HasType
          ((VExpr.const ``Nat.beq []).app (.bvar 0)) (.forallE .nat .bool) :=
        .app hbeqC.2 hidxT
      have hbeqT2 : (c.withMLC _ (wf := cwfx)).HasType
          (((VExpr.const ``Nat.beq []).app (.bvar 0)).app (.bvar 0)) .bool :=
        .app hbeqT1 hidxT
      have hbeqApp : (c.withMLC _ (wf := cwfx)).TrExprS
          (mkApp2 (.const ``Nat.beq []) (.fvar idx) (.fvar idx))
          (((VExpr.const ``Nat.beq []).app (.bvar 0)).app (.bvar 0)) :=
        .app hbeqT1 hidxT (.app hbeqC.2 hidxT hbeqC.1 hidx) hidx
      -- the conditional the gadget is compared against. This is the one use of `hbool`, and the
      -- reason `WF_ite` quantifies over extensions: `args` and both branches are the probe.
      have hrS := hbool (m := mx) (c.hasPrimitives.trNat c.Ewf hnat)
        nofun (fun _ => rfl) (.cons hbeqApp .nil) (.cons hbeqT2 .nil) hidx hidxT hidx hidxT
      -- `eager`'s domain is `Nat`: its argument in the recognized term is the fuel, which the
      -- previous check made `Nat.succ (f a)`
      have hnT : (c.withMLC _ (wf := cwfa)).HasType _ .nat :=
        .app (TrExprS.natSucc c.hasPrimitives hnat).2 hfaNatT
      have hAnat := hfuelNT.uniqU c.Ewf (c.withMLC _ (wf := cwfa)).Δwf.toCtx
        (VEnv.HasType.defeqU_l c.Ewf (c.withMLC _ (wf := cwfa)).Δwf.toCtx (hfuelEq ‹_›).symm hnT)
      have hAnatw := hAnat.weakN c.Ewf.ordered
        (VLCtx.FVLift.skip_fvar (idx, (Expr.const ``Nat []).fvarsList) (.vlam .nat) .refl).toCtx
      have hidxT' := VEnv.HasType.defeqU_r c.Ewf (c.withMLC _ (wf := cwfx)).Δwf.toCtx
        (by simpa [mx, VExpr.lift, VExpr.liftN, VExpr.nat] using hAnatw.symm) hidxT
      have heagerw := hfuelF.weakFV c.Ewf (.skip_fvar _ _ .refl) cwfx.wf.tr.wf
      have heagerTw := hfuelFT.weakN c.Ewf.ordered
        (VLCtx.FVLift.skip_fvar (idx, (Expr.const ``Nat []).fvarsList) (.vlam .nat) .refl).toCtx
      refine .bind (isDefEq.WF (.app heagerTw hidxT' heagerw hidx) hrS) fun _ _ _ heager => ?_
      split <;> [refine .pure ?_; exact hfail]
      -- both branches of the conditional are the probe variable, so `WF_ite`'s conclusion is the
      -- variable whichever way the decision goes -- `b` never has to be pinned down here
      refine ⟨_, idx, cwfx, hfuelF, fun k => ?_⟩
      -- the gadget's equation is checked at the probe variable; instantiate it at the literal,
      -- which is where `Nat.beq k k` reduces and `WF_ite` can fire
      have hlit := TrExprS.natLit (Us := c.lparams) (Δ := (c.withMLC _ (wf := cwfa)).vlctx)
        c.hasPrimitives hnat k
      obtain ⟨T, hgen⟩ := heager ‹_›
      have hinst := VEnv.IsDefEq.instDF c.Ewf.ordered (c.withMLC _ (wf := cwfa)).Δwf.toCtx
        hgen hlit.2
      simp [VExpr.inst, VExpr.instVar, VLocalDecl.depth, VExpr.inst_lift] at hinst
      refine VEnv.IsDefEqU.trans c.Ewf (c.withMLC _ (wf := cwfa)).Δwf.toCtx ⟨_, hinst⟩ ?_
      have hrI := TrExprS.instN (henv := c.Ewf.ordered) (h₀ := hlit.1) (W := .zero)
        (H := hrS.abstract (v₀ := idx) .zero) hlit.2
      -- the same conditional at the literal: both branches are it, and the decision now reduces
      have hbeqCa := TrExprS.ofConst (Us := c.lparams)
        (Δ := (c.withMLC _ (wf := cwfa)).vlctx) c.Ewf (c.hasPrimitives.natBEq hbeqv).1
        (by simp [VExpr.instL, VExpr.nat, VExpr.bool])
      have hbeqT1a : (c.withMLC _ (wf := cwfa)).HasType
          ((VExpr.const ``Nat.beq []).app (.natLit k)) (.forallE .nat .bool) :=
        .app hbeqCa.2 hlit.2
      have hbeqT2a : (c.withMLC _ (wf := cwfa)).HasType
          (((VExpr.const ``Nat.beq []).app (.natLit k)).app (.natLit k)) .bool :=
        .app hbeqT1a hlit.2
      have hbeqAppa : (c.withMLC _ (wf := cwfa)).TrExprS
          (mkApp2 (.const ``Nat.beq []) (.lit (.natVal k)) (.lit (.natVal k)))
          (((VExpr.const ``Nat.beq []).app (.natLit k)).app (.natLit k)) :=
        .app hbeqT1a hlit.2 (.app hbeqCa.2 hlit.2 hbeqCa.1 hlit.1) hlit.1
      have hrkS := hbool (m := ma)
        (c.hasPrimitives.trNat c.Ewf hnat) nofun (fun _ => rfl)
        (.cons hbeqAppa .nil) (.cons hbeqT2a .nil) hlit.1 hlit.2 hlit.1 hlit.2
      have hdec : (c.withMLC _ (wf := cwfa)).IsDefEqU
          (((VExpr.const ``Nat.beq []).app (.natLit k)).app (.natLit k)) (.boolLit true) := by
        simpa using (c.withMLC _ (wf := cwfa)).natBinLitBool c.hasPrimitives.natBEq hbeqv k k
      have heq : (Expr.abstract1 idx (Condition.bool.ite (.const ``Nat [])
          #[mkApp2 (.const ``Nat.beq []) (.fvar idx) (.fvar idx)]
          (.fvar idx) (.fvar idx))).instantiate1' (.lit (.natVal k)) =
          Condition.bool.ite (.const ``Nat [])
            #[mkApp2 (.const ``Nat.beq []) (.lit (.natVal k)) (.lit (.natVal k))]
            (.lit (.natVal k)) (.lit (.natVal k)) := by
        simp [Condition.ite, Expr.abstract1, Expr.instantiate1', mkApp2, mkApp,
          mkAppN, mkAppB, mkApp5, mkApp4, Condition.bool]
      -- the gadget at the literal and the conditional at the literal are the same term. That is
      -- also what types the latter: the evaluation wants it well formed, and only the gadget's
      -- own check says it is.
      have huniq := hrI.uniq c.Ewf (.refl c.Ewf (c.withMLC _ (wf := cwfa)).Δwf) (heq ▸ hrkS)
      have hred := hbeval c.self true (fun _ => rfl) (c.withMLC _ (wf := cwfa)).Δwf.toCtx
        (.cons hbeqT2a .nil) rfl hdec
        ⟨_, VEnv.HasType.defeqU_l c.Ewf (c.withMLC _ (wf := cwfa)).Δwf.toCtx huniq
          hinst.hasType.2⟩
      exact VEnv.IsDefEqU.trans c.Ewf (c.withMLC _ (wf := cwfa)).Δwf.toCtx huniq hred
    -- past the probe: `go` unfolds to a `Nat.rec` on the fuel, and the three telescopes below
    -- read the successor branch off it. `stk2`'s first peel kept the head's translation, which is
    -- what the recognizer unfolds -- the arguments it was applied to are checked separately.
    refine .bind (unfoldDefinition.WF hfixGoS) fun _ _ _ h6 => ?_
    obtain ⟨_, he6S, he6eq⟩ := h6
    -- the outermost telescope rebinds every argument of `go`, which is what makes the step
    -- equation below uniform in them -- `NatFixUnfold.step`'s base point relies on it
    refine lambdaTelescope.WF he6S ?_
    intro fvs2 m2 _ s2 go2 go2' n2 hn2 As2 hs2 hdrop2 harr2 hlam2 hinv2 _ hgo2
    -- five binders: the `fix` arguments again, then the fuel `t` the `Nat.rec` is on
    obtain ⟨lfvs2⟩ := fvs2
    rcases lfvs2 with _|⟨_,_|⟨_,_|⟨_,_|⟨Fg,_|⟨tg,_|l3⟩⟩⟩⟩⟩ <;> try exact hfail
    -- the body is the `Nat.rec` applied to the fuel variable, and the guard that the recursor
    -- part does not mention it is what makes the recursion uniform in the fuel
    cases go2 <;> try exact hfail
    rename_i natRec tg'
    let +generalize G (α:Expr) := _
    unfold unfoldWellFounded.match_11; simp [Array.getLit]; unfold G
    let +generalize G (_ _:Expr) := _; simp; unfold G
    split <;> [rename_i hrec; exact hfailb]
    -- `succ t` is checked before it is reduced: `whnfCore` needs a translation of the term it
    -- runs on, and nothing so far says the `Nat.rec`'s motive accepts it
    have hfvtg : FVarsIn (· ∈ (c.withMLC m2).vlctx.fvars) tg :=
      hinv2.vars.forall_left (fun h => h.fvarsIn) tg (by simp)
    refine .bind (checkType.WF ⟨nofun, hfvtg⟩) fun _ _ _ ⟨_, _, _, hsuccS, hsuccTy, hsuccT⟩ => ?_
    -- the guard: the recursor part is independent of the fuel variable, and the argument it is
    -- applied to is that variable
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hrec
    obtain ⟨hnc, hteq⟩ := hrec
    let .app hnrT htgT hnrS htgS := hgo2
    -- `t : Nat`, which only `checkType (succ t)` says: `Nat.succ`'s recorded type pins its
    -- domain, and the recursor's domain is the same by uniqueness at `t`
    let .app hnsT hargT hnsS hargS := hsuccS
    cases (TrExprS.const0_inv (Us' := c.lparams) (Δ' := (c.withMLC m2).vlctx) hnsS).1
    have hdomNat := (hnsT.uniqU c.Ewf (c.withMLC m2).Δwf.toCtx
      (TrExprS.natSucc c.hasPrimitives hnat).2).forallE_inv c.Ewf
      (c.withMLC m2).Δwf.toCtx |>.1
    -- `==` on `Expr` is an equivalence rather than equality, and `TrExprS.eqv` is what transfers
    -- across it: the guard's `t == t'` moves the checked argument onto the recursor's
    have htgeq := (hargS.eqv hteq).uniq c.Ewf
      (.refl c.Ewf (c.withMLC m2).Δwf) htgS
    have hdomNat' : (c.withMLC m2).IsDefEqU _ VExpr.nat := let ⟨_, h⟩ := hdomNat; ⟨_, h⟩
    have htgTnat := VEnv.HasType.defeqU_r c.Ewf (c.withMLC m2).Δwf.toCtx hdomNat' hargT
    have hAnat2 := htgT.uniqU c.Ewf (c.withMLC m2).Δwf.toCtx
      (VEnv.HasType.defeqU_l c.Ewf (c.withMLC m2).Δwf.toCtx htgeq htgTnat)
    have hsuccTnat : (c.withMLC m2).HasType _ .nat :=
      .app (TrExprS.natSucc c.hasPrimitives hnat).2 htgTnat
    refine .bind (whnfCore.WF (.app hnrT
      (VEnv.HasType.defeqU_r c.Ewf (c.withMLC m2).Δwf.toCtx hAnat2.symm hsuccTnat) hnrS
      (.app hnsT hargT hnsS hargS))) fun gor _ _ h7 => ?_
    obtain ⟨_, _, hgorS, hgoreq⟩ := h7
    -- the successor branch, as a function of the recursion argument and its `Dom` proof
    refine lambdaTelescope.WF hgorS ?_
    intro fvs3 m3 _ s3 gor3 gor3' n3 hn3 As3 hs3 hdrop3 harr3 hlam3 hinv3 _ hgor3
    obtain ⟨lfvs3⟩ := fvs3
    rcases lfvs3 with _|⟨xg,_|⟨_,_|l4⟩⟩ <;> try exact hfail
    -- the branch is `F x` applied to the induction hypothesis
    cases gor3 <;> try exact hfail
    rename_i Fx ihe
    let +generalize G (_ _:Expr) := _
    unfold unfoldNatWellFounded.match_1; simp [Array.getLit]; unfold G
    let +generalize G (_ _:Expr) := _; simp; unfold G
    split <;> [rename_i hFx; exact hfailb]
    -- the induction hypothesis: a function of the smaller argument and its `Dom` proof, whose
    -- body must be the recursive call at the predecessor fuel
    let .app hFxT hihT hFxS hihS := hgor3
    refine lambdaTelescope.WF hihS ?_
    intro fvs4 m4 _ s4 ih4 ih4' n4 hn4 As4 hs4 hdrop4 harr4 hlam4 hinv4 _ hih4
    obtain ⟨lfvs4⟩ := fvs4
    rcases lfvs4 with _|⟨yg,_|⟨_,_|l5⟩⟩ <;> try exact hfail
    cases ih4 <;> try exact hfail
    rename_i ihf iharg
    let +generalize G (_ _:Expr) := _
    unfold unfoldNatWellFounded.match_1; simp [Array.getLit]; unfold G
    let +generalize G (_ _:Expr) := _; simp; unfold G
    split <;> [rename_i hihq; exact hfail]
    -- every `==` the recognizer checked is spent here, by `TrExprS.eqv`: the recursion argument
    -- against `a`, the recursor's argument against the fuel variable, the branch head against
    -- `F x`, and the induction hypothesis against the recursor at the lower fuel. Each one is an
    -- application congruence for `==`, which is what the `Expr.eqv'` simp set does.
    have hrfl : ∀ e : Expr, e.eqv' e = true := fun e => by
      simpa [(· == ·)] using Expr.eqv_refl e
    have hgoApp : (c.withMLC _ (wf := cwfa)).TrExprS
        (Expr.mkAppList e5.getAppFn
          ([α2, motive2, f2, F] ++ [.app eagerFn fuelN, .fvar ida, pf])) _ :=
      (hlist2 ▸ e5.mkAppList_getAppArgsList ▸ he5S).eqv <| BEq.symm <| by
        simp only [Expr.mkAppList]; simp_all [(· == ·), Expr.eqv']
    -- the recursor is independent of the fuel variable, which is what the recognizer's
    -- `containsFVar` guard says
    have hnrlift : ∀ nrv : VExpr, (c.withMLC m2).TrExprS natRec nrv →
        ∃ nrv₀ : VExpr, (c.withMLC m2).IsDefEqU nrv nrv₀.lift := by
      intro nrv hnr
      have hn25 : n2 = 5 := by simpa using hinv2.vars.length_eq.symm
      subst hn25
      obtain ⟨x, nm2, ty2, tyv2, bi2, m2', rfl⟩ :=
        MLCtx.head_vlam (n := 4) (m := m2) (hn := hn2) (Bs := As2.reverse)
          (by simpa using hinv2.len) (by rw [hdrop2]; exact hinv2.toCtx)
      -- the fuel variable is that head, and the guard says `natRec` avoids it, so it translates
      -- one binder down -- the same `abstract`-then-`weakFV_inv` route `F` takes
      have htgx : tg = Expr.fvar x := by
        simp [MLCtx.fvarRevList] at harr2; exact harr2.1
      have hnc' : natRec.containsFVar' x = false := by
        rw [htgx] at hnc; simpa [Expr.containsFVar_eq, Expr.fvarId!] using hnc
      have cwf2b : c.MLCWF (MLCtx.vlam x nm2 ty2 tyv2 bi2 m2') := ‹_›
      have cwf2' : c.MLCWF m2' := ⟨cwf2b.wf.1⟩
      have hnrfv : FVarsIn (· ∈ (c.withMLC m2' (wf := cwf2')).vlctx.fvars) natRec := by
        refine (FVarsIn.of_containsFVar' hnr.fvarsIn hnc').mono fun fv h => ?_
        simp only [VContext.vlctx, VContext.withMLC_mlctx, MLCtx.vlctx, VLCtx.fvars,
          List.filterMap_cons, Option.map, List.mem_cons] at h ⊢
        exact h.1.resolve_left h.2
      obtain ⟨nrv₀, hnr₀⟩ := TrExprS.weakFV_inv c.Ewf (.skip_fvar _ (.vlam tyv2) .refl)
        (.refl c.Ewf (c.withMLC _ (wf := cwf2b)).Δwf) hnr (m2'.noBV ▸ hnr.closed) hnrfv
      exact ⟨nrv₀, ((hnr₀.weakFV c.Ewf.ordered (.skip_fvar _ _ .refl)
        (c.withMLC _ (wf := cwf2b)).Δwf).uniq c.Ewf
        (.refl c.Ewf (c.withMLC _ (wf := cwf2b)).Δwf) hnr).symm⟩
    refine .pure ⟨ida, cwfa, ?_, ?_⟩
    · exact ⟨_, _, hfS, ha₀w, _, hbodyw, (hfa₀ ‹_›).symm⟩
    have hihApp : (c.withMLC m4).TrExprS (.app (.app (.app natRec tg) yg) iharg) ih4' :=
      hih4.eqv (by simp_all [(· == ·), Expr.eqv'])
    exact ⟨_, _, _, _, _, _, _, _, _, _, hgoApp, hFw,
      ⟨_, .app hfixTw hidaT hfixw hida,
        (VEnv.IsDefEqU.trans c.Ewf (c.withMLC _ (wf := cwfa)).Δwf.toCtx he5eq he4eq).symm⟩,
      hfuelN, .app hfT haT hfS hida, hfuelEq ‹_›, ⟨_, _, _, rfl⟩, hfixGoS,
      ⟨m2, ‹_›, n2, hn2, _, _, _, _, _, natRec, As2, _, _, _, _, _, he6eq, hdrop2, hinv2, hnrS,
        hnrlift _ hnrS, ⟨_, VEnv.HasType.app hnrT htgT⟩, hargS, htgeq, hgoreq,
        m3, ‹_›, n3, hn3, _, _, As3, _, _, hdrop3, hinv3, hFxS.eqv (BEq.symm hFx),
        m4, ‹_›, n4, hn4, _, _, _, As4, _, hdrop4, hinv4, hihApp⟩,
      heagerQ⟩
  · -- post-block: everything found under the telescope is abstracted over it, so the guard that
    -- `F` has no loose bvars left is what says nothing escaped
    intro _ _ _ hQa
    refine .bind getLCtx.WF fun _ _ _ h => ?_
    obtain ⟨rfl, rfl⟩ := h
    extract_lets -underBinder Fa jp
    split <;> [exact hfailb; rename_i hF]
    unfold jp
    -- What the guard buys: abstracting can only *add* loose bvars, so `Fa` having none says `F`
    -- mentioned no telescope variable and the abstraction did nothing. `F` is therefore its own
    -- abstraction and `hFF`, its translation as an argument of the fixpoint, serves directly.
    have hfvs : fvs = ⟨List.map Expr.fvar (m'.fvarRevList n hn).reverse⟩ := by
      have := congrArg List.reverse harr; simp at this
      exact Array.toList_inj.1 (by simpa using this)
    have hFlb : (F.abstractList (m'.fvarRevList n hn).reverse).looseBVarRange' = 0 := by
      simp only [Fa, hfvs, Expr.abstract_eq] at hF; simpa [Expr.hasLooseBVars] using hF
    have hFaF : Fa = F := by
      simp only [Fa, hfvs, Expr.abstract_eq]
      exact Expr.abstractList_eq_self (Nat.le_of_eq hFlb)
    obtain ⟨Fv, hFaS⟩ : ∃ Fv, (c.withMLC m').TrExprS Fa Fv := ⟨_, hFaF ▸ hFF⟩
    -- and the same guard read on the variables rather than the term: `F` mentions none of the
    -- telescope's variables, so all of its free variables are already the recognizer's own. This
    -- is what will let `F`'s translation be pushed back down to `c`, where the bundle stores it.
    have hFfv : FVarsIn (· ∈ (c.withMLC m₀).vlctx.fvars) F := by
      refine (FVarsIn.of_abstractList hFF.fvarsIn (Nat.le_of_eq hFlb)).mono fun fv h => ?_
      have := MLCtx.fvars_eq_append (c := m') (n := n) (hn := hn)
      simp only [VContext.vlctx, VContext.withMLC_mlctx, this, hdrop, List.mem_append,
        List.mem_reverse] at h ⊢
      exact h.1.resolve_left h.2
    -- so `F` translates in `c` itself, which is the form the bundle stores
    obtain ⟨F', hFbase⟩ : ∃ F', (c.withMLC m₀).TrExprS F F' :=
      TrExprS.weakFV_inv (c.withMLC m₀).Ewf hinv.lift
        (.refl (c.withMLC m₀).Ewf (c.withMLC m').Δwf) hFF
        (m'.noBV ▸ hFF.closed) hFfv
    -- `pack` gets there a different way: it *binds* the telescope rather than avoiding it, and
    -- `mkLambda_eq` says the `LocalContext` form the recognizer builds is `MLCtx.mkLambda`, whose
    -- translation lands in the dropped context -- which `hdrop` says is `c`
    have hwf' : MLCtx.WF c.venv c.lparams m' := ‹c.MLCWF m'›.wf
    -- closing the telescope off is `VExpr.lams` over its domains, for *any* body: `Inv.lams` is
    -- stated with `mkLambda'`, and the binders it counts are all `vlam` because a `vlet` would
    -- leave the context an entry short of the `As` the invariant also records. Both the measure
    -- and the packer are closed this way, so the bridge is taken once, generically.
    have hmk : ∀ X : VExpr, m'.mkLambda' n hn X = VExpr.lams As X := fun X => by
      rw [MLCtx.mkLambda'_eq_lams (Bs := As.reverse) (by simpa using hinv.len)
        (by rw [hdrop]; exact hinv.toCtx), List.reverse_reverse]
    obtain ⟨a₀', pack', packTy, hpackS, hpackeq, hpackT, hwfa₀', ha₀'⟩ :
        ∃ a₀' pack' packTy, (c.withMLC m₀).TrExprS ((c.withMLC m').lctx'.mkLambda fvs a₀) pack' ∧
          pack' = VExpr.lams As a₀' ∧
          c.venv.HasType c.lparams.length (c.withMLC m₀).vlctx.toCtx pack' packTy ∧
          c.venv.HasType c.lparams.length (As.reverse ++ (c.withMLC m₀).vlctx.toCtx) a₀' tyv ∧
          (c.withMLC m').TrExprS a₀ a₀' := by
      rw [show (c.withMLC m').lctx' = m'.lctx from rfl, hwf'.mkLambda_eq n hn harr]
      refine ⟨_, _, _, hdrop ▸ (hwf'.mkLambda_trS c.Ewf ha₀ hty n hn).1, hmk _,
        hdrop ▸ (hwf'.mkLambda_trS c.Ewf ha₀ hty n hn).2, ?_⟩
      refine ⟨?_, ha₀⟩
      have h := hty
      rwa [show (c.withMLC m').vlctx = m'.vlctx from rfl, hinv.toCtx] at h
    -- the telescope's own variables are fresh, so "lives in `c`" is an up-set for `m'` and the
    -- `FVarsBelow`s that `inferType` and `whnf` hand out can be read as staying in `c`
    have hup : IsFVarUpSet (· ∈ (c.withMLC m₀).vlctx.fvars) (c.withMLC m').vlctx := by
      have := hwf'.isFVarUpSet_dropN n hn; rwa [hdrop] at this
    refine .bind (inferType.WF hFaS) fun _ _ _ ⟨_, hFTb, _, hFTS, hFT⟩ => ?_
    refine .bind (whnf.WF hFTS) fun _ _ _ h1 => ?_
    obtain ⟨hw1b, _, hw1S, hw1eq⟩ := h1
    have hw1fv := hw1b _ hup (hFTb _ hup (hFaF ▸ hFfv))
    split <;> try exact hfail
    rename_i _ Adom cod _
    obtain ⟨hAdomfv, hcodfv⟩ : FVarsIn _ Adom ∧ FVarsIn _ cod := hw1fv
    -- `F`'s type avoids the telescope, so the whole `forallE` translates at `c` too -- and because
    -- `TrExprS` is syntax-directed, that base translation *is* a `forallE`, whose domain is the
    -- `Aty` the bundle records and whose body is `F`'s codomain there. Identifying it with the
    -- telescope's translation and running `forallE_inv` hands the component defeqs back already
    -- *sorted*, which is what the congruences below need and what `uniq` on its own would not give.
    obtain ⟨_, hw1Base⟩ := TrExprS.weakFV_inv c.Ewf hinv.lift
      (.refl c.Ewf (c.withMLC m').Δwf) hw1S (m'.noBV ▸ hw1S.closed) ⟨hAdomfv, hcodfv⟩
    let .forallE (ty' := Aty) (body' := codv₀) hAty hcodTy hAtyS hcodS := hw1Base
    have hw1uniq := ((TrExprS.forallE hAty hcodTy hAtyS hcodS).weakFV c.Ewf hinv.lift
      hwf'.tr.wf).uniq c.Ewf (.refl c.Ewf (c.withMLC m').Δwf) hw1S
    simp only [VExpr.liftN] at hw1uniq
    -- `cod` is that `forallE`'s body, so the recognizer now opens a binder before reducing it.
    -- `hw1S`'s own `forallE` gives both halves this needs -- the domain's translation and typing
    -- for the `withLocalDecl`, and `cod`'s translation already in the extended context.
    let .forallE (ty' := Adomv) (body' := codv) hA hB hAS hBS := hw1S
    obtain ⟨⟨_, hAdefeq⟩, _, hcoddefeq⟩ :=
      VEnv.IsDefEqU.forallE_inv c.Ewf (c.withMLC m').Δwf.toCtx hw1uniq
    -- the block hands back the `ih` binder's type as a `lam` over the binder it opened, so what
    -- it has to establish is that that `lam` translates back in `m'` -- one `TrExprS.abstract`
    -- closing the variable it just opened.
    --
    -- It also owes the two typings the bundle records, and for the same reason: they are read off
    -- the `forallE` this block reduces to, so they are only available while its binder is open.
    -- `dom : Adom → Sort u` is that `forallE`'s domain being a type, and `F`'s codomain being a
    -- `forallE` at `dom` applied is the reduction itself, one beta step from the `lam` returned.
    -- the new check: the packed argument's type is `F`'s domain
    refine .bind (isDefEq.WF htyS hAS) fun _ _ _ htyA => ?_
    split <;> [skip; exact hfailb]
    refine .bind (Q := fun d _ => ∃ d', (c.withMLC m₀).TrExprS d d' ∧
        (∃ u, (c.withMLC m₀).HasType d' (.forallE Aty (.sort u))) ∧
        ∃ resTy u, c.venv.IsDefEq c.lparams.length (Aty :: (c.withMLC m₀).vlctx.toCtx) codv₀
          (.forallE ((d'.lift).app (.bvar 0)) resTy) (.sort u))
      (M.WF.withLocalDecl hAS hA .rfl ?_)
      fun _ _ _ ⟨dom', hdomBase, hdomT, hcodeq⟩ => ?_
    · intro idd cwfd sd hsd hresd
      -- the opened variable is fresh, so adding it to "lives in `c`" keeps that an up-set, and
      -- its own dependencies are `Adom`'s, which are already `c`'s
      have hidd : idd ∉ (c.withMLC m').vlctx.fvars := hwf'.tr.find?_eq_none.1 cwfd.wf.2.1
      have hupd : IsFVarUpSet (fun fv => fv ∈ (c.withMLC m₀).vlctx.fvars ∨ fv = idd)
          (c.withMLC _ (wf := cwfd)).vlctx :=
        ⟨(IsFVarUpSet.congr hwf'.tr.wf.fvwf fun _ h =>
            (or_iff_left (by rintro rfl; exact hidd h)).symm).1 hup,
         fun _ _ hfv' => .inl ((fvarsIn_iff.1 hAdomfv).1 _ hfv')⟩
      -- `hBS` translates `cod` under the `none`-tagged `vlam` the `forallE` rule produces, and
      -- `inst_fvar` turns that binder into `idd`'s -- exactly the substitution the code performs
      simp only [Expr.instantiate1_eq]
      refine .bind (whnf.WF (hBS.inst_fvar c.Ewf.ordered cwfd.wf.tr.wf)) fun _ _ _ h2 => ?_
      obtain ⟨hw2b, _, hw2S, hw2eq⟩ := h2
      have hw2fv := hw2b _ hupd ((hcodfv.mono fun _ => .inl).instantiate1 (.inr rfl))
      split <;> try exact hfail
      rename_i bn dAE restE bi2
      let .forallE (ty' := dAv) (body' := restv) hdA hrest hdAS hrestS := hw2S
      -- `whnf`'s result mentions the opened variable, so nothing about it descends to `c` as it
      -- stands. Abstracting it first is what fixes that: `TrExprS.abstract` retags the `idd`
      -- binder as the plain `bvar` binder `FVLift.cons_bvar` understands, leaving the translation
      -- untouched, and now the whole `forallE` lives one binder above the base context. Its
      -- binder's type there is `Aty`, not `Adomv`, which is why `weakFV_inv` is handed the
      -- *defeq* context `hΔdefeq` rather than a reflexivity.
      have hΔdefeq : VLCtx.IsDefEq c.venv c.lparams.length
          ((none, .vlam (Aty.liftN n 0)) :: (c.withMLC m').vlctx)
          ((none, .vlam Adomv) :: (c.withMLC m').vlctx) :=
        .cons (.refl c.Ewf hwf'.tr.wf) nofun (.vlam hAdefeq)
      have hw2A := (TrExprS.forallE (name := bn) (bi := bi2) hdA hrest hdAS hrestS).abstract
        (v₀ := idd) .zero
      have hw2Afv := FVarsIn.abstract1_erase (k := 0) (P := (· ∈ (c.withMLC m₀).vlctx.fvars)) hw2fv
      obtain ⟨_, hw2Base⟩ := TrExprS.weakFV_inv c.Ewf
        (Δ := (none, .vlam Aty) :: (c.withMLC m₀).vlctx) (.cons_bvar (.vlam Aty) hinv.lift)
        (hΔdefeq.symm c.Ewf) hw2A (by simpa [VLCtx.bvars, m'.noBV] using hw2A.closed) hw2Afv
      let .forallE (ty' := dAv₀) (body' := restv₀) hdAty hrestTy hdAS₀ hrestS₀ := hw2Base
      have hw2uniq := ((TrExprS.forallE (name := bn) (bi := bi2) hdAty hrestTy hdAS₀
        hrestS₀).weakFV c.Ewf (.cons_bvar (.vlam Aty) hinv.lift) hΔdefeq.wf).uniq
        c.Ewf hΔdefeq hw2A
      -- the binder type's typing is read straight off the base translation
      obtain ⟨u1, hdAT⟩ : ∃ u, c.venv.HasType c.lparams.length
        (Aty :: (c.withMLC m₀).vlctx.toCtx) dAv₀ (.sort u) := hdAty
      have hΓc : OnCtx (Aty :: (c.withMLC m₀).vlctx.toCtx) (c.venv.IsType c.lparams.length) :=
        ⟨(c.withMLC m₀).Δwf.toCtx, hAty⟩
      -- `cod` and the reduct are now both lifts of base terms, so the reduction descends too
      have hctx : c.venv.IsDefEqCtx c.lparams.length (c.withMLC m').vlctx.toCtx
          (Adomv :: (c.withMLC m').vlctx.toCtx) ((Aty.liftN n 0) :: (c.withMLC m').vlctx.toCtx) :=
        .succ .zero hAdefeq.symm
      have hcodbase : c.venv.IsDefEqU c.lparams.length (Aty :: (c.withMLC m₀).vlctx.toCtx) codv₀
          (.forallE dAv₀ restv₀) :=
        (VEnv.IsDefEqU.weakN_iff c.Ewf hΔdefeq.wf.toCtx (.succ hinv.lift.toCtx)
          (e1 := codv₀) (e2 := .forallE dAv₀ restv₀)).1 <|
        .trans c.Ewf hΔdefeq.wf.toCtx ⟨_, hcoddefeq⟩ <|
        .trans c.Ewf hΔdefeq.wf.toCtx
          (VEnv.IsDefEqU.defeqDFC c.Ewf hctx hw2eq.symm) hw2uniq.symm
      -- one beta step: the `lam` this block returns, lifted over the binder and applied to its
      -- variable, is the `forallE`'s domain back again -- `inst_liftN_bvar` is the lift the
      -- application introduced being consumed by the substitution
      let ⟨_, hcodv₀T⟩ := hcodTy
      let ⟨_, hrestv₀⟩ := hrestTy
      have hbeta : c.venv.IsDefEq c.lparams.length (Aty :: (c.withMLC m₀).vlctx.toCtx)
          (((VExpr.lam Aty dAv₀).lift).app (.bvar 0)) dAv₀ (.sort u1) := by
        have := VEnv.IsDefEq.beta (hdAT.weakN c.Ewf (.succ .one)) (.bvar .zero)
        simpa [VExpr.inst_liftN_bvar, VExpr.inst, VExpr.lift, VExpr.liftN,
          VLCtx.toCtx] using this
      obtain ⟨_, hT⟩ : c.venv.IsDefEqU c.lparams.length (Aty :: (c.withMLC m₀).vlctx.toCtx) codv₀
          (.forallE (((VExpr.lam Aty dAv₀).lift).app (.bvar 0)) restv₀) :=
        .trans c.Ewf hΓc hcodbase ⟨_, .forallEDF hbeta.symm hrestv₀⟩
      have hsorted := VEnv.IsDefEqU.defeqDF c.Ewf hΓc (hT.hasType.1.uniqU c.Ewf hΓc hcodv₀T) hT
      have hlamS : (c.withMLC m₀).TrExprS (.lam `a Adom (dAE.abstract #[.fvar idd]) .default)
          (.lam Aty dAv₀) := by
        simp only [show (#[Expr.fvar idd] : Array Expr) = ⟨[idd].map .fvar⟩ from rfl,
          Expr.abstract_eq, Expr.abstractList]
        exact .lam hAty hAtyS hdAS₀
      exact .pure ⟨.lam Aty dAv₀, hlamS, ⟨_, .lam hAty.choose_spec hdAT⟩, restv₀, _, hsorted⟩
    -- `F`'s own typing comes down the same way: `inferType`'s judgement is transported onto the
    -- lifted base term and the lifted base type, and then `weakN_iff` -- sound exactly because
    -- neither mentions the telescope -- drops the whole judgement to `c`
    have hFw := hFbase.weakFV c.Ewf hinv.lift hwf'.tr.wf
    have hFeq := hFw.uniq c.Ewf (.refl c.Ewf (c.withMLC m').Δwf) (hFaF ▸ hFaS)
    have hFTm := ((hFT.defeqU_r c.Ewf (c.withMLC m').Δwf.toCtx hw1eq.symm).defeqU_r c.Ewf
      (c.withMLC m').Δwf.toCtx hw1uniq.symm).defeqU_l c.Ewf (c.withMLC m').Δwf.toCtx hFeq.symm
    have hFTc : (c.withMLC m₀).HasType F' (.forallE Aty codv₀) :=
      (VEnv.HasType.weakN_iff c.Ewf (c.withMLC m').Δwf.toCtx hinv.lift.toCtx
        (A := .forallE Aty codv₀)).1 hFTm
    -- and the block's defeq turns that codomain into the pi at `dom` applied that the bundle
    -- records; the domain is untouched, so the congruence needs nothing but `Aty`'s own typing
    obtain ⟨_, hAtyT⟩ := hAty
    obtain ⟨resTy, _, hcodDefEq⟩ := hcodeq
    -- The telescope's own domains, which is the form `lams_appN` closes: `Inv.lams` is stated
    -- with `mkLambda'`, and the binders it counts are all `vlam` because a `vlet` would leave the
    -- context an entry short of the `As` it also records.
    have hmvlams : mv = VExpr.lams As body' := hinv.lams.trans (hmk _)
    have hctxAs : OnCtx (As.reverse ++ (c.withMLC m₀).vlctx.toCtx)
        (c.venv.IsType c.lparams.length) := by
      have := (c.withMLC m').Δwf.toCtx
      rwa [show (c.withMLC m').vlctx = m'.vlctx from rfl, hinv.toCtx] at this
    -- the packer's type: a pi telescope over the recursion domains whose *result* is `Aty`.
    -- That result is what the new check buys -- before it, it was the unrelated `inferType a₀`,
    -- and nothing downstream could connect the packed argument to what `F` takes.
    have hctxAs' : OnCtx (As.reverse ++ (c.withMLC m₀).vlctx.toCtx)
        (c.venv.IsType c.lparams.length) := by
      have h := (c.withMLC m').Δwf.toCtx
      rwa [show (c.withMLC m').vlctx = m'.vlctx from rfl, hinv.toCtx] at h
    have ha₀Aty : c.venv.HasType c.lparams.length (As.reverse ++ (c.withMLC m₀).vlctx.toCtx) a₀'
        (Aty.liftN n 0) := by
      refine hwfa₀'.defeqU_r c.Ewf hctxAs'
        (VEnv.IsDefEqU.trans c.Ewf hctxAs' (e₂ := Adomv) ?_ ?_)
      · exact hinv.toCtx ▸ htyA ‹_›
      · exact hinv.toCtx ▸ ⟨_, hAdefeq.symm⟩
    have hpackTy : (c.withMLC m₀).HasType pack' (VExpr.forallEs As (Aty.liftN n 0)) :=
      hpackeq ▸ VEnv.HasType.lams c.Ewf hctxAs' ha₀Aty
    have ha₀Aty' : c.venv.HasType c.lparams.length (As.reverse ++ (c.withMLC m₀).vlctx.toCtx) a₀'
        (Aty.liftN As.length 0) := by rw [hinv.len]; exact ha₀Aty
    have hAsNat : As = List.replicate As.length VExpr.nat := by
      have h := (MLCtx.mkLambda_natBinderTypes (Bs := As.reverse) hwf'
        (by simpa using hinv.len) (by rw [hdrop]; exact hinv.toCtx) (hlam ▸ hnd)).1
      simpa [hinv.len] using congrArg List.reverse h
    have hFTfinal := hFTc.defeqU_r c.Ewf (c.withMLC m₀).Δwf.toCtx ⟨_, .forallEDF hAtyT hcodDefEq⟩
    refine .pure ⟨⟨⟨_, _, _⟩, F', hFaF ▸ hFbase, _, hpackS, dom', hdomBase, Aty,
      As, a₀', hpackeq, hctxAs', ha₀Aty', hAsNat,
      hdomT, resTy, hFTfinal⟩, rfl, by rw [hinv.len, harity],
      fun hlen E γ hγ => ?_⟩
    -- the recognizer's checks, as `BlockQ` exported them: the fixpoint's own measure agreeing
    -- with the caller's, and the entry equation at the binder standing for the packed argument
    obtain ⟨ida, cwfa, ⟨fv, a₀v2, hfS2, ha₀S2, hbodyeq⟩, goHead, args4, eagerFn, fuelN, pf,
      Fv2, gohv, gov, fuelNv, fav, hgoApp, hFv2, hfixgo, hfuelNS, hfaS, hfueleq,
      hargs4len, hgohS, hstep, heager⟩ := hQa
    -- `go`'s application split: the four arguments the recognizer never inspected stay packed,
    -- and what follows them is the fuel, the packed argument and the proof
    obtain ⟨gohv', allxs, hgoveq, hgohS', hallxs⟩ :=
      TrExprS.appN_inv ((Expr.appN_eq_mkAppList _ _).symm ▸ hgoApp)
    obtain ⟨xs4, xs3, rfl, hxs4, hxs3⟩ := List.Forall₂.append_inv hallxs
    let .cons (b := fuelv) hfuelS (.cons (b := idav) hidaS (.cons (b := pfv) hpfS .nil)) :=
      hxs3
    -- the binder is `bvar 0`, which is what closing sends to the packed argument on the nose
    have hidav : _ = VExpr.bvar 0 :=
      TrExprS.fvar_uniq hidaS (.fvar VLCtx.find?_vlam_self)
    rw [VExpr.appN_append] at hgoveq
    -- one closing of the recursion telescope per argument, paid for by `hσm`: the measure applied
    -- to `σ a` is a numeral, hence well typed, and that is exactly what `lams_appN` consumes.
    -- Everything else closed at these arguments reuses this substitution rather than rebuilding it.
    have hclose : ∀ a, VEnv.Ctx.SubstEq E.venv c.lparams.length [] (γ.consN (σ a)) (γ.consN (σ a))
        (As.reverse ++ (c.withMLC m₀).vlctx.toCtx) ∧
        E.IsDefEqU₀ ((mv.subst γ).appN (σ a)) (body'.subst (γ.consN (σ a))) ∧
        VExpr.ArgsTyped E.venv c.lparams.length [] As γ (σ a) := fun a => by
      have hwf : E.WF₀
          (((VExpr.lams As body').subst γ).appN (σ a)) := by
        obtain ⟨_, h⟩ := hσm E.cast γ hγ a
        rw [← hmvlams]; exact ⟨_, h.hasType.1⟩
      have := VExpr.lams_appN E.wf trivial (E.monoCtx hctxAs) hγ (e := body')
        (by rw [hlen a, harity, hinv.len]) hwf
      rw [hmvlams]; exact this
    -- the value's arguments are the telescope's own variables. An fvar's translation is a
    -- `find?`, so this is a syntactic identification rather than a defeq -- which is what lets
    -- closing send them to `σ a` below.
    have hxseq : xs = ((List.range n).map VExpr.bvar).reverse := by
      refine (List.reverse_reverse xs) ▸ congrArg List.reverse ?_
      refine List.Forall₂.fvars_uniq hxs.rev hinv.vars fun e he => ?_
      rw [harr] at he
      obtain ⟨fv, _, rfl⟩ := List.mem_map.1 he
      exact ⟨fv, rfl⟩
    -- the packed argument is well typed. The packer is a lambda over the *same* telescope closed
    -- at the *same* arguments, so this reuses the measure's closing rather than asking for a
    -- well-typedness of `pack` applied that nothing independently supplies.
    have hpackApp : ∀ a, E.WF₀
        (((VExpr.lams As a₀').subst γ).appN (σ a)) ∧
        E.IsDefEqU₀ (((VExpr.lams As a₀').subst γ).appN (σ a)) (a₀'.subst (γ.consN (σ a))) :=
      fun a => VExpr.lams_appN' E.wf trivial (E.monoCtx hctxAs) hγ (hclose a).2.2
        ⟨_, E.monoT hwfa₀'⟩
    -- and this is the one place the packed argument has to be looked inside. Everything the
    -- recognizer checked about the `a` binder can be read at *any* well-typed term, but its type
    -- is `a₀`'s, and only the beta equation says the packer applied has that type. After this the
    -- argument is opaque again: `NatFixUnfold` refers to it only as `P.arg`.
    have hclosea : ∀ a, VEnv.Ctx.SubstEq E.venv c.lparams.length []
        ((γ.consN (σ a)).cons ((pack'.subst γ).appN (σ a)))
        ((γ.consN (σ a)).cons ((pack'.subst γ).appN (σ a)))
        (tyv :: (As.reverse ++ (c.withMLC m₀).vlctx.toCtx)) := fun a => by
      have htyv : c.venv.IsType c.lparams.length
          (As.reverse ++ (c.withMLC m₀).vlctx.toCtx) tyv := by
        have h := hty.isType c.Ewf.ordered (c.withMLC m').Δwf.toCtx
        rwa [show (c.withMLC m').vlctx = m'.vlctx from rfl, hinv.toCtx] at h
      obtain ⟨u, hu⟩ := htyv
      refine .cons (hclose a).1 (E.monoT hu) ?_
      have hbase := VEnv.HasType.subst E.wf (hclose a).1 (E.monoT hwfa₀')
      rw [hpackeq]
      exact hbase.defeqU_l E.wf trivial (hpackApp a).2.symm
    -- `entry`'s left hand side: the value applied to the telescope, closed. The arguments are the
    -- telescope's variables, so the closing sends them to `σ a`, and the lift the value picked up
    -- over the telescope is absorbed by that same closing.
    have hevclosed : ∀ a, E.IsDefEqU₀ ((X₀.appN xs).subst (γ.consN (σ a)))
        ((ev.subst γ).appN (σ a)) := fun a => by
      have hlen' : (σ a).length = n := by rw [hlen a, harity]
      have h0 : c.venv.IsDefEqU c.lparams.length (c.withMLC m').vlctx.toCtx
          (X₀.appN xs) ((VExpr.liftN n ev 0).appN xs) :=
        VEnv.IsDefEqU.appN c.Ewf (c.withMLC m').Δwf.toCtx
          (hX₀.uniq c.Ewf (.refl c.Ewf (c.withMLC m').Δwf) hevw) ⟨_, hXT⟩
      rw [show (c.withMLC m').vlctx.toCtx = _ from hinv.toCtx] at h0
      have h1 := VEnv.IsDefEqU.subst E.wf (hclose a).1 (E.mono h0)
      rw [VExpr.subst_appN, VExpr.subst_appN, hxseq, ← hlen'] at h1
      rw [VExpr.subst_consN_bvars, VExpr.liftN_subst_consN] at h1
      rw [VExpr.subst_appN, hxseq, ← hlen', VExpr.subst_consN_bvars]
      exact h1
    -- and the recognizer's unfolding chain, closed: the value applied to the recursion arguments
    -- is the fixpoint at an argument that is the packer applied -- which is the one place the
    -- packed argument is looked inside, discharged by `hpackApp`'s beta equation.
    have hΓm : (c.withMLC m').vlctx.toCtx = As.reverse ++ (c.withMLC m₀).vlctx.toCtx := hinv.toCtx
    have hΓa : (c.withMLC _ (wf := cwfa)).vlctx.toCtx =
        tyv :: (As.reverse ++ (c.withMLC m₀).vlctx.toCtx) := by
      show tyv :: (c.withMLC m').vlctx.toCtx = _
      rw [hΓm]
    have hfixclosed : ∀ a (F₂ : VExpr), (c.withMLC _ (wf := cwfa)).TrExprS fixFn F₂ →
        E.IsDefEqU₀ ((ev.subst γ).appN (σ a))
          ((F₂.subst ((γ.consN (σ a)).cons ((pack'.subst γ).appN (σ a)))).app
            ((pack'.subst γ).appN (σ a))) := fun a F₂ hF₂ => by
      have he3S' := e3.mkAppList_getAppArgsList ▸ he3S
      rw [hlist] at he3S'
      have hch := VEnv.IsDefEqU.trans c.Ewf (c.withMLC m').Δwf.toCtx
        (((VEnv.IsDefEqU.trans c.Ewf (c.withMLC m').Δwf.toCtx he3eq he2eq).trans
          c.Ewf (c.withMLC m').Δwf.toCtx he1eq).symm)
        ((AppStack.tr stk).uniq c.Ewf (.refl c.Ewf (c.withMLC m').Δwf) he3S').symm
      rw [hΓm] at hch
      have h1 := VEnv.IsDefEqU.subst E.wf (hclose a).1 (E.mono hch)
      refine VEnv.IsDefEqU.trans E.wf trivial
        (VEnv.IsDefEqU.trans E.wf trivial (hevclosed a).symm h1) ?_
      -- the argument: the value chain ends at `a₀`, the recognizer's checks at the binder, and
      -- the packer's beta equation is what joins them -- the one conversion
      have hfixTc := VEnv.HasType.subst E.wf (hclose a).1 <| E.monoT <| hΓm ▸ hfixT
      have ha₀Ac := VEnv.HasType.subst E.wf (hclose a).1 <| E.monoT <| hΓm ▸ ha₀A
      have hstep1 := VEnv.IsDefEqU.app_arg E.wf trivial hfixTc ha₀Ac
          (a' := (pack'.subst γ).appN (σ a)) <| by
        rw [hpackeq]
        refine VEnv.IsDefEqU.trans E.wf trivial ?_ (hpackApp a).2.symm
        exact VEnv.IsDefEqU.subst E.wf (hclose a).1 <|
          E.mono <| hΓm ▸ ha₀.uniq c.Ewf (.refl c.Ewf (c.withMLC m').Δwf) ha₀'
      refine VEnv.IsDefEqU.trans E.wf trivial hstep1 ?_
      -- and the function: `F₂` and the stack's head both translate `fixFn`, the latter weakened
      -- over the binder, whose lift the closing absorbs
      have hfw := hfixS.weakFV c.Ewf (.skip_fvar _ _ .refl) cwfa.wf.tr.wf
      have hfeq := VEnv.IsDefEqU.subst E.wf (hclosea a) <|
        E.mono <| hΓa ▸ hfw.uniq c.Ewf (.refl c.Ewf (c.withMLC _ (wf := cwfa)).Δwf) hF₂
      simp only [VLocalDecl.depth, Nat.zero_add, VExpr.lift_subst] at hfeq
      exact hfeq.appN E.wf trivial (vs := [(pack'.subst γ).appN (σ a)])
        ⟨_, hstep1.choose_spec.hasType.2⟩
    -- the measure, closed: the caller's `hσm` reads it at the recursion arguments, and the
    -- telescope's beta equation identifies that with the measure's body closed
    have hmeasclosed a : E.IsDefEqU₀ (body'.subst (γ.consN (σ a))) (.natLit (σm a)) :=
      (hclose a).2.1.symm.trans E.wf trivial (hσm E.cast γ hγ a)
    -- and the fixpoint's own measure at the packed argument is that same numeral: `BlockQ`'s
    -- first check reads `f a₀ ≡ body` at the binder, and closing turns `body` into the measure
    have hfa₀closed a : E.IsDefEqU₀
        ((fv.subst ((γ.consN (σ a)).cons ((pack'.subst γ).appN (σ a)))).app
          (a₀v2.subst ((γ.consN (σ a)).cons ((pack'.subst γ).appN (σ a)))))
        (.natLit (σm a)) := by
      obtain ⟨eb, hebS, hebeq⟩ := hbodyeq
      have hbodyw := hbody.weakFV c.Ewf (.skip_fvar _ _ .refl) cwfa.wf.tr.wf
      have huniq := hebS.uniq c.Ewf (.refl c.Ewf (c.withMLC _ (wf := cwfa)).Δwf) hbodyw
      have hma := VEnv.IsDefEqU.trans c.Ewf (c.withMLC _ (wf := cwfa)).Δwf.toCtx huniq.symm hebeq
      have h := VEnv.IsDefEqU.subst E.wf (hclosea a) (E.mono <| hΓa ▸ hma)
      simp only [VLocalDecl.depth, Nat.zero_add, VExpr.lift_subst] at h
      exact VEnv.IsDefEqU.trans E.wf trivial h.symm (hmeasclosed a)
    -- the binder's own `a₀`, closed, is the packer applied -- the same beta seam, reused
    have hargclosed a : E.IsDefEqU₀
        (a₀v2.subst ((γ.consN (σ a)).cons ((pack'.subst γ).appN (σ a))))
        ((pack'.subst γ).appN (σ a)) := by
      have hw := ha₀'.weakFV c.Ewf (.skip_fvar _ _ .refl) cwfa.wf.tr.wf
      have hu := ha₀S2.uniq c.Ewf (.refl c.Ewf (c.withMLC _ (wf := cwfa)).Δwf) hw
      have h := VEnv.IsDefEqU.subst E.wf (hclosea a) (E.mono <| hΓa ▸ hu)
      simp only [VLocalDecl.depth, Nat.zero_add, VExpr.lift_subst, VExpr.Subst.tail_cons] at h
      rw [hpackeq] at h ⊢
      exact VEnv.IsDefEqU.trans E.wf trivial h (hpackApp a).2.symm
    -- so the fixpoint's measure at the *binder* is the numeral too
    have hfavclosed a : E.IsDefEqU₀
        (fav.subst ((γ.consN (σ a)).cons ((pack'.subst γ).appN (σ a))))
        (.natLit (σm a)) := by
      let .app hfT3 haT3 hfS3 hidaS3 := hfaS
      have hbv := TrExprS.fvar_uniq hidaS3 (.fvar VLCtx.find?_vlam_self)
      subst hbv
      have hfT3c := VEnv.HasType.subst E.wf (hclosea a) (E.monoT <| hΓa ▸ hfT3)
      have haT3c := VEnv.HasType.subst E.wf (hclosea a) (E.monoT <| hΓa ▸ haT3)
      simp only [VExpr.subst, VExpr.Subst.cons] at hfT3c haT3c ⊢
      have h1 := VEnv.IsDefEqU.app_arg E.wf trivial hfT3c haT3c (hargclosed a).symm
      have hfeq := VEnv.IsDefEqU.subst E.wf (hclosea a)
        (E.mono <| hΓa ▸ (hfS3.uniq c.Ewf (.refl c.Ewf (c.withMLC _ (wf := cwfa)).Δwf) hfS2))
      have h2 := VEnv.IsDefEqU.appN E.wf trivial
        (vs := [VExpr.subst a₀v2 ((γ.consN (σ a)).cons ((pack'.subst γ).appN (σ a)))])
        hfeq ⟨_, h1.choose_spec.hasType.2⟩
      exact VEnv.IsDefEqU.trans E.wf trivial
        (VEnv.IsDefEqU.trans E.wf trivial h1 h2) (hfa₀closed a)
    -- and the fuel the recognizer checked is that numeral's successor. `natLit (k+1)` *is*
    -- `natSucc` applied to `natLit k`, so this is one congruence in the argument, and `natSucc`'s
    -- own typing comes from the equation's right hand side being well typed already.
    have hfuelNclosed a : E.IsDefEqU₀
        (fuelNv.subst ((γ.consN (σ a)).cons ((pack'.subst γ).appN (σ a))))
        (.natLit (σm a + 1)) := by
      have hfe : c.venv.IsDefEqU c.lparams.length
        (c.withMLC _ (wf := cwfa)).vlctx.toCtx fuelNv (.app .natSucc fav) := hfueleq
      have h := VEnv.IsDefEqU.subst E.wf (hclosea a) (E.mono <| hΓa ▸ hfe)
      simp only [VExpr.subst, VExpr.subst_natSucc] at h
      refine VEnv.IsDefEqU.trans E.wf trivial h ?_
      obtain ⟨A, B, hfT, haT⟩ :=
        VExpr.WF.app_inv E.wf trivial ⟨_, h.choose_spec.hasType.2⟩
      exact VEnv.IsDefEqU.app_arg E.wf trivial hfT haT (hfavclosed a)
    -- the gadget, already at literals
    obtain ⟨eagerv, idx, cwfx, heagerS, heagerlit⟩ := heager
    -- the fuel, closed: the gadget is the identity at the literal the previous steps produced
    have hfuelclosed a (fv2 : VExpr)
        (hfv2 : (c.withMLC _ (wf := cwfa)).TrExprS (.app eagerFn fuelN) fv2) :
        E.IsDefEqU₀ (fv2.subst ((γ.consN (σ a)).cons ((pack'.subst γ).appN (σ a))))
          (.natLit (σm a + 1)) := by
      let .app heT2 hfnT2 heagerS2 hfuelNS2 := hfv2
      have heT2c := E.monoT (hΓa ▸ heT2) |>.subst E.wf (hclosea a)
      have hfnT2c := E.monoT (hΓa ▸ hfnT2) |>.subst E.wf (hclosea a)
      have h1 :=
        E.mono (hΓa ▸ hfuelNS2.uniq c.Ewf (.refl c.Ewf (c.withMLC _ (wf := cwfa)).Δwf) hfuelNS)
        |>.subst E.wf (hclosea a) |>.trans E.wf trivial (hfuelNclosed a)
        |>.app_arg E.wf trivial heT2c hfnT2c
      have heagerc :=
        E.mono (hΓa ▸ heagerS2.uniq c.Ewf (.refl c.Ewf (c.withMLC _ (wf := cwfa)).Δwf) heagerS)
        |>.subst E.wf (hclosea a)
      have h2 := VEnv.IsDefEqU.appN E.wf trivial (vs := [VExpr.natLit (σm a + 1)])
        heagerc ⟨_, h1.choose_spec.hasType.2⟩
      have hel : c.venv.IsDefEqU c.lparams.length (c.withMLC _ (wf := cwfa)).vlctx.toCtx
        (.app eagerv (.natLit (σm a + 1))) (.natLit (σm a + 1)) := heagerlit (σm a + 1)
      have h3 := VEnv.IsDefEqU.subst E.wf (hclosea a) (E.mono <| hΓa ▸ hel)
      simp only [VExpr.subst, VExpr.subst_natLit] at h3
      simp only [VExpr.subst]
      exact h1.trans E.wf trivial h2 |>.trans E.wf trivial h3
    -- `entry`, up to naming the fuel: the value at the recursion arguments is the `go`
    -- application the recognizer found, closed at those arguments and at the packed one
    have hentry a : E.IsDefEqU₀ ((ev.subst γ).appN (σ a))
        (gov.subst ((γ.consN (σ a)).cons ((pack'.subst γ).appN (σ a)))) := by
      have ⟨e₂, he₂S, he₂eq⟩ := hfixgo
      let .app _ _ hfixS2 hidaS2 := he₂S
      cases TrExprS.fvar_uniq hidaS2 (.fvar VLCtx.find?_vlam_self)
      refine hfixclosed a _ hfixS2 |>.trans E.wf trivial ?_
      exact E.mono (hΓa ▸ he₂eq) |>.subst E.wf (hclosea a)
    refine ⟨⟨fun a => ?_, fun a => ?_, fun a => ?_, fun b a t x pf hxa hwfx => ?_⟩⟩
    · exact (gohv'.appN xs4).subst ((γ.consN (σ a)).cons ((pack'.subst γ).appN (σ a)))
    · simp only [ProbeBundle.arg, ProbeBundle.packc, hpackeq]; exact (hpackApp a).1
    · -- `entry`: the closed equation, with the fuel replaced by the numeral it computes to. The
      -- packed argument needs no conversion -- it is `bvar 0`, which the closing sends there.
      obtain ⟨Tg, hen⟩ := hentry a
      have hwf := hen.hasType.2
      simp only [hgoveq, VExpr.appN, VExpr.subst, hidav, VExpr.Subst.cons] at hwf
      obtain ⟨_, _, hf1, _⟩ := VExpr.WF.app_inv E.wf trivial ⟨_, hwf⟩
      obtain ⟨_, _, hf2, _⟩ := VExpr.WF.app_inv E.wf trivial ⟨_, hf1⟩
      obtain ⟨_, _, hf3, ha3⟩ := VExpr.WF.app_inv E.wf trivial ⟨_, hf2⟩
      refine ⟨pfv.subst ((γ.consN (σ a)).cons ((pack'.subst γ).appN (σ a))),
        VEnv.IsDefEqU.trans E.wf trivial ⟨_, hen⟩ ?_⟩
      simp only [hgoveq, VExpr.appN, VExpr.subst, hidav, VExpr.Subst.cons]
      exact VEnv.IsDefEqU.appN E.wf trivial
        (vs := [(pack'.subst γ).appN (σ a),
          pfv.subst ((γ.consN (σ a)).cons ((pack'.subst γ).appN (σ a)))])
        (VEnv.IsDefEqU.app_arg E.wf trivial hf3 ha3 (hfuelclosed a _ hfuelS)) ⟨_, hwf⟩
    -- `step`, at the base point `b`. `Step`'s telescope rebinds every argument of `go`, so
    -- closing it at the four the recognizer never inspected plus the fuel turns `goFn b` applied
    -- to the fuel into the `Nat.rec` the recognizer found underneath.
    obtain ⟨m2, cwf2, n2, hn2, a1, a2, a3, Fg, tg, natRec, As2, goh2, nrv, tgv, tgv', gorv,
      he6eq, hdrop2, hinv2, hnrS, ⟨nrv₀, hnrv₀⟩, hbodyT2, htgS, htgeq, hgoreq, hbranch⟩ := hstep
    have hmk2 : ∀ X : VExpr, m2.mkLambda' n2 hn2 X = VExpr.lams As2 X := fun X => by
      rw [MLCtx.mkLambda'_eq_lams (Bs := As2.reverse) (by simpa using hinv2.len)
        (by rw [hdrop2]; exact hinv2.toCtx), List.reverse_reverse]
    -- `go`'s head *is* that telescope: `he6eq` identifies the term the recognizer unfolded with
    -- the head the entry equation was found at, and `uniq` ties in the split's own translation
    have hgoh2 : goh2 = VExpr.lams As2 (.app nrv tgv') := hinv2.lams.trans (hmk2 _)
    have hheadeq : c.venv.IsDefEqU c.lparams.length
        (c.withMLC _ (wf := cwfa)).vlctx.toCtx gohv' (VExpr.lams As2 (.app nrv tgv')) :=
      hgohS'.uniq c.Ewf (.refl c.Ewf (c.withMLC _ (wf := cwfa)).Δwf) hgohS
      |>.trans c.Ewf (c.withMLC _ (wf := cwfa)).Δwf.toCtx (hgoh2 ▸ he6eq).symm
    -- the telescope has exactly the five arguments `go` takes, and the recognizer's split
    -- accounted for four of them, so the fuel makes up the difference
    cases show n2 = 5 by simpa using hinv2.vars.length_eq.symm
    have hxs4len : xs4.length = 4 := by
      obtain ⟨_, _, _, rfl⟩ := hargs4len
      rw [← hxs4.length_eq]; rfl
    have hAs2ctx : OnCtx (As2.reverse ++ (tyv :: (As.reverse ++ (c.withMLC m₀).vlctx.toCtx)))
        (c.venv.IsType c.lparams.length) := by
      rw [← hΓa]
      have h := (c.withMLC _ (wf := cwf2)).Δwf.toCtx
      rwa [show (c.withMLC m2).vlctx = m2.vlctx from rfl, hinv2.toCtx] at h
    -- and the closing of that telescope, paid for by the well-typedness `step` is handed: the
    -- head applied to its five arguments is what `hwfx` says is well typed
    obtain ⟨_, _, hwf1, _⟩ := VExpr.WF.app_inv E.wf trivial hwfx
    obtain ⟨_, _, hwfhead, _⟩ := VExpr.WF.app_inv E.wf trivial ⟨_, hwf1⟩
    have hshape : ((gohv'.appN xs4).subst
          ((γ.consN (σ b)).cons ((pack'.subst γ).appN (σ b)))).app (.natLit (t+1)) =
        ((gohv'.subst ((γ.consN (σ b)).cons ((pack'.subst γ).appN (σ b)))).appN
          (xs4.map (VExpr.subst · ((γ.consN (σ b)).cons ((pack'.subst γ).appN (σ b)))) ++
            [.natLit (t+1)])) := by
      rw [VExpr.subst_appN, VExpr.appN_append]; rfl
    rw [hshape] at hwfhead
    have hheadc := E.mono (hΓa ▸ hheadeq) |>.subst E.wf (hclosea b)
    have hwflams := hheadc.appN E.wf trivial ⟨_, hwfhead⟩
    obtain ⟨hcl2, hbeta2, hargs2⟩ := VExpr.lams_appN E.wf trivial (E.monoCtx hAs2ctx) (hclosea b)
      (by simp [hxs4len, hinv2.len]) ⟨_, hwflams.choose_spec.hasType.2⟩
    -- the successor branch: `gor` is what `whnfCore` reduced the recursor at `succ t` to, and
    -- it is itself a two-binder telescope -- the recursion argument and its `Dom` proof
    obtain ⟨m3, cwf3, n3, hn3, xg, hx, As3, Fxv, ihv, hdrop3, hinv3, hFxS, hstepih⟩ := hbranch
    cases show n3 = 2 by simpa using hinv3.vars.length_eq.symm
    have hmk3 X : m3.mkLambda' 2 hn3 X = VExpr.lams As3 X := by
      rw [MLCtx.mkLambda'_eq_lams (Bs := As3.reverse) (by simpa using hinv3.len)
        (by rw [hdrop3]; exact hinv3.toCtx), List.reverse_reverse]
    have hgor3 : gorv = VExpr.lams As3 (.app Fxv ihv) := hinv3.lams.trans (hmk3 _)
    -- the branch is read at the *lower* fuel: `gor` is the recursor at `succ t`, so the
    -- telescope has to be closed at `t` there, while `step`'s left hand side is at `t+1`.
    -- Only the fuel component of the argument typings differs, and both are numerals.
    have hargs2t : VExpr.ArgsTyped E.venv c.lparams.length [] As2
        ((γ.consN (σ b)).cons ((pack'.subst γ).appN (σ b)))
        (xs4.map (VExpr.subst · ((γ.consN (σ b)).cons ((pack'.subst γ).appN (σ b)))) ++
          [VExpr.natLit t]) := by
      obtain ⟨_, _, _, rfl⟩ := hargs4len
      obtain _ | ⟨w1, ws⟩ := xs4 <;> [simp at hxs4len; skip]
      obtain _ | ⟨w2, ws⟩ := ws <;> [simp at hxs4len; skip]
      obtain _ | ⟨w3, ws⟩ := ws <;> [simp at hxs4len; skip]
      obtain _ | ⟨w4, ws⟩ := ws <;> [simp at hxs4len; skip]
      obtain _ | ⟨w5, ws⟩ := ws <;> [skip; simp at hxs4len]
      let .cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 .nil)))) := hargs2
      refine .cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons ?_ .nil))))
      have hn t := E.monoT (TrExprS.natLit c.hasPrimitives hnat (Us := c.lparams) (Δ := []) t).2
      exact (hn t).defeqU_r E.wf trivial <| (hn (t+1)).uniqU E.wf trivial h5
    -- so the telescope closes at the lower fuel too, and that closing is the one the branch
    -- and the `ih` are read at
    obtain ⟨hwf2t, hbeta2t⟩ := VExpr.lams_appN' E.wf trivial (E.monoCtx hAs2ctx) (hclosea b)
      hargs2t (E.monoW (hΓa ▸ hinv2.toCtx ▸ hbodyT2))
    obtain ⟨hcl2t, -⟩ := VExpr.lams_appN E.wf trivial (E.monoCtx hAs2ctx) (hclosea b)
      (vs := xs4.map (VExpr.subst · ((γ.consN (σ b)).cons ((pack'.subst γ).appN (σ b)))) ++
        [VExpr.natLit t])
      (by simp [hxs4len, hinv2.len]) hwf2t
    -- the branch, closed at the lower fuel, is the recursor at `t+1`
    have hgoreq' : c.venv.IsDefEqU c.lparams.length
        (As2.reverse ++ (tyv :: (As.reverse ++ (c.withMLC m₀).vlctx.toCtx))) gorv
        (.app nrv (.app .natSucc tgv)) := hΓa ▸ hinv2.toCtx ▸ hgoreq
    have hgoreqc := E.mono hgoreq' |>.subst E.wf hcl2t
    -- fuel-independence in action: the recursor is the same under both closings, because they
    -- differ only in the head, which a lifted term ignores
    have hnrv₀' : c.venv.IsDefEqU c.lparams.length
        (As2.reverse ++ (tyv :: (As.reverse ++ (c.withMLC m₀).vlctx.toCtx))) nrv nrv₀.lift := by
      exact hΓa ▸ hinv2.toCtx ▸ hnrv₀
    have hnrsame := by
      have hA := E.mono hnrv₀' |>.subst E.wf hcl2
      have hB := E.mono hnrv₀' |>.subst E.wf hcl2t
      simp only [VExpr.Subst.consN_append_singleton, VExpr.lift_subst,
        VExpr.Subst.tail_cons] at hA hB
      exact hA.trans E.wf trivial hB.symm
    -- the fuel variable's translation is `bvar 0`, so it closes to whichever numeral the
    -- telescope was closed at
    let .cons htg0 (.cons hFg0 _) := hinv2.vars
    let .cons hhx0 (.cons hxg0 _) := hinv3.vars
    have htgv := htgS.uniq c.Ewf (.refl c.Ewf (c.withMLC m2).Δwf) htg0
    have htgv'0 := E.mono (hΓa ▸ hinv2.toCtx ▸ htgeq.symm.trans c.Ewf (c.withMLC m2).Δwf.toCtx htgv)
    have htgA := htgv'0.subst E.wf hcl2
    have htgB := E.mono (hΓa ▸ hinv2.toCtx ▸ htgv) |>.subst E.wf hcl2t
    simp only [VExpr.Subst.consN_append_singleton, VExpr.subst, VExpr.Subst.cons] at htgA htgB
    -- the fuel step: `go` at `t+1` *is* the branch read at `t`. Both sides reach the recursor
    -- applied to the numeral `t+1`, one through the telescope's own fuel argument and one
    -- through `succ` of the fuel variable.
    have hstep1 := hwflams.trans E.wf trivial hbeta2
    simp only [VExpr.Subst.consN_append_singleton, VExpr.subst] at hstep1 hgoreqc
    obtain ⟨_, _, hnrT2, htgT2⟩ := VExpr.WF.app_inv E.wf trivial
      ⟨_, hstep1.choose_spec.hasType.2⟩
    have hstep2 := htgA.app_arg E.wf trivial hnrT2 htgT2
    have hstep3 := hnrsame.appN E.wf trivial (vs := [.natLit (t+1)])
      ⟨_, hstep2.choose_spec.hasType.2⟩
    obtain ⟨_, _, hnrT2t, hsuccT2t⟩ := VExpr.WF.app_inv E.wf trivial
      ⟨_, hgoreqc.choose_spec.hasType.2⟩
    obtain ⟨_, _, hnsT, htgT2t⟩ := VExpr.WF.app_inv E.wf trivial ⟨_, hsuccT2t⟩
    have hstep4 := htgB.app_arg E.wf trivial hnsT htgT2t |>.app_arg E.wf trivial hnrT2t hsuccT2t
    have hgostep := hstep1.trans E.wf trivial hstep2 |>.trans E.wf trivial hstep3
      |>.trans E.wf trivial (hgoreqc.trans E.wf trivial hstep4).symm
    -- so the branch's own telescope closes at `x` and the proof, landing on `F x` applied to
    -- the `ih` -- which is `step`'s call to `F`, and names the `ih` at the same time
    have hAs3ctx : OnCtx
        (As3.reverse ++ (As2.reverse ++ (tyv :: (As.reverse ++ (c.withMLC m₀).vlctx.toCtx))))
        (c.venv.IsType c.lparams.length) := by
      have h := (c.withMLC m3).Δwf.toCtx
      rw [show (c.withMLC m3).vlctx = m3.vlctx from rfl, hinv3.toCtx] at h
      exact hΓa ▸ hinv2.toCtx ▸ h
    obtain ⟨hcl3, hbeta3, -⟩ := VExpr.lams_appN E.wf trivial (E.monoCtx hAs3ctx) hcl2t
      (vs := [x, pf]) (e := .app Fxv ihv) (by simp [hinv3.len]) <| by
      rw [← hgor3]; simp only [VExpr.Subst.consN_append_singleton]
      exact ⟨_, (hgostep.appN E.wf trivial (vs := [x, pf]) (hshape ▸ hwfx)).choose_spec.hasType.2⟩
    -- and the `ih` the branch hands `F` is a two-binder telescope too, whose body is the
    -- recursor at the *lower* fuel -- which is what makes the recursive calls line up
    obtain ⟨m4, cwf4, n4, hn4, yg, hy, iharg, As4, ihbv, hdrop4, hinv4, hihApp⟩ := hstepih
    cases show n4 = 2 by simpa using hinv4.vars.length_eq.symm
    have hmk4 X : m4.mkLambda' 2 hn4 X = VExpr.lams As4 X := by
      rw [MLCtx.mkLambda'_eq_lams (Bs := As4.reverse) (by simpa using hinv4.len)
        (by rw [hdrop4]; exact hinv4.toCtx), List.reverse_reverse]
    have hih4 : ihv = VExpr.lams As4 ihbv := hinv4.lams.trans (hmk4 _)
    have hΓ3 : (c.withMLC m3).vlctx.toCtx =
        As3.reverse ++ (As2.reverse ++ (tyv :: (As.reverse ++ (c.withMLC m₀).vlctx.toCtx))) := by
      have h2 : m2.vlctx.toCtx =
          As2.reverse ++ (tyv :: (As.reverse ++ (c.withMLC m₀).vlctx.toCtx)) := by
        rw [hinv2.toCtx]; exact congrArg _ hΓa
      rw [show (c.withMLC m3).vlctx = m3.vlctx from rfl, hinv3.toCtx, h2]
    -- the call to `F`: the branch's head is `F` applied to the recursion argument, and the
    -- closing sends the outer telescope's `F` binder to `go`'s fourth argument, which `BlockQ`
    -- records as `F` itself
    obtain ⟨w1, w2, w3, w4, rfl⟩ : ∃ w1 w2 w3 w4, xs4 = [w1, w2, w3, w4] := by
      rcases xs4 with _|⟨w1,_|⟨w2,_|⟨w3,_|⟨w4,_|_⟩⟩⟩⟩ <;> simp at hxs4len ⊢
    let .app _ _ hFgS hxgS := hFxS
    have hFg3 := hFg0.weakFV c.Ewf.ordered hinv3.lift (c.withMLC m3).Δwf
    have hFgeq := hFgS.uniq c.Ewf (.refl c.Ewf (c.withMLC m3).Δwf) hFg3
    have hxgeq := hxgS.uniq c.Ewf (.refl c.Ewf (c.withMLC m3).Δwf) hxg0
    have hFgc := E.mono (hΓ3 ▸ hFgeq) |>.subst E.wf hcl3
    have hxgc := E.mono (hΓ3 ▸ hxgeq) |>.subst E.wf hcl3
    simp only [VExpr.Subst.consN_append_singleton, VExpr.liftN, liftVar, VExpr.subst,
      VExpr.Subst.cons, VExpr.Subst.consN] at hFgc hxgc
    -- and `go`'s fourth argument is the bundle's `F`: the lift it picked up over the telescope
    -- and the `a` binder is absorbed by the closing
    obtain ⟨_, _, _, rfl⟩ := hargs4len
    let .cons _ (.cons _ (.cons _ (.cons hFxs4 .nil))) := hxs4
    have hFwa := hFw.weakFV c.Ewf (.skip_fvar _ _ .refl) cwfa.wf.tr.wf
    have hw4 := E.mono (hΓa ▸ hFxs4.uniq c.Ewf (.refl c.Ewf (c.withMLC _ (wf := cwfa)).Δwf) hFwa)
      |>.subst E.wf (hclosea b)
    have hlen' : (σ b).length = n := by rw [hlen b, harity]
    simp only [← hlen', VLocalDecl.depth, Nat.zero_add, VExpr.lift_subst,
      VExpr.Subst.tail_cons, VExpr.liftN_subst_consN] at hw4
    -- assemble: the `go` call is the branch, the branch's head is `F` at the recursion
    -- argument, and both components are the bundle's
    simp only [← hgor3, VExpr.Subst.consN_append_singleton] at hbeta3
    have hgc := VEnv.IsDefEqU.appN E.wf trivial (vs := [x, pf]) hgostep (hshape ▸ hwfx)
    have hchain := VEnv.IsDefEqU.trans E.wf trivial hgc hbeta3
    simp only [VExpr.subst] at hchain
    obtain ⟨_, _, hFxT, hihT0⟩ := VExpr.WF.app_inv E.wf trivial
      ⟨_, hchain.choose_spec.hasType.2⟩
    obtain ⟨_, _, hFgT, hxgT⟩ := VExpr.WF.app_inv E.wf trivial ⟨_, hFxT⟩
    have hFgP := hFgc.trans E.wf trivial hw4
    have hxgP := hxgc.trans E.wf trivial hxa
    have hc1 := hxgP.app_arg E.wf trivial hFgT hxgT
    have hc2 := hFgP.appN E.wf trivial (vs := [(pack'.subst γ).appN (σ a)])
      ⟨_, hc1.choose_spec.hasType.2⟩
    have hFxP := hc1.trans E.wf trivial hc2
    refine ⟨_, ?_, fun y arg hy harg hwfy => ?_, hchain.trans E.wf trivial <|
      hFxP.appN E.wf trivial (vs := [ihv.subst _]) ⟨_, hchain.choose_spec.hasType.2⟩⟩
    · -- `ih`'s type: it is `F`'s second argument, so `dom` at the packed argument
      have happ := hFxT.defeqU_l E.wf trivial hFxP
      obtain ⟨_, _, hFcT, hargT⟩ := VExpr.WF.app_inv E.wf trivial ⟨_, happ⟩
      have hFTγ := VEnv.HasType.subst E.wf hγ (E.monoT hFTfinal)
      simp only [VExpr.subst] at hFTγ
      obtain ⟨⟨_, hAeq'⟩, -⟩ := VEnv.IsDefEqU.forallE_inv E.wf trivial
        (hFcT.uniqU E.wf trivial hFTγ)
      have hargT' := hargT.defeqU_r E.wf trivial ⟨_, hAeq'⟩
      have hFTapp := VEnv.HasType.app hFTγ hargT'
      simp [VExpr.inst, VExpr.instVar, VExpr.lift_subst, VExpr.Subst.lift,
        VExpr.subst_lift_tail_inst] at hFTapp
      obtain ⟨⟨_, hdomeq'⟩, -⟩ := VEnv.IsDefEqU.forallE_inv E.wf trivial
        (happ.uniqU E.wf trivial hFTapp)
      exact hihT0.defeqU_r E.wf trivial ⟨_, hdomeq'⟩
    -- the recursive call: the `ih` telescope closes at the argument and its proof, landing on
    -- the recursor at the *lower* fuel, which is the `go` call `step` has to produce
    have hAs4ctx : OnCtx
        (As4.reverse ++ (As3.reverse ++ (As2.reverse ++
          (tyv :: (As.reverse ++ (c.withMLC m₀).vlctx.toCtx)))))
        (c.venv.IsType c.lparams.length) := by
      rw [← hΓ3]
      have h := (c.withMLC m4).Δwf.toCtx
      rwa [show (c.withMLC m4).vlctx = m4.vlctx from rfl, hinv4.toCtx] at h
    simp only [VExpr.Subst.consN_append_singleton] at hcl3
    rw [hih4] at hwfy
    obtain ⟨hcl4, hbeta4, -⟩ := VExpr.lams_appN E.wf trivial (E.monoCtx hAs4ctx) hcl3
      (vs := [arg, hy]) (e := ihbv) (by simp [hinv4.len]) hwfy
    -- and what it lands on is the recursor applied to the fuel, the argument and a proof
    let .app _ _ (.app _ _ (.app _ _ hnrS4 htgS4) hygS) hihargS := hihApp
    let  .cons hhy0 (.cons hyg0 _) := hinv4.vars
    have hΓ4 : (c.withMLC m4).vlctx.toCtx =
        As4.reverse ++ (As3.reverse ++ (As2.reverse ++
          (tyv :: (As.reverse ++ (c.withMLC m₀).vlctx.toCtx)))) := by
      have h3' : m3.vlctx.toCtx = As3.reverse ++
          (As2.reverse ++ (tyv :: (As.reverse ++ (c.withMLC m₀).vlctx.toCtx))) := hΓ3
      rw [show (c.withMLC m4).vlctx = m4.vlctx from rfl, hinv4.toCtx, h3']
    -- the recursor, weakened over the two inner telescopes and closed
    have hnr4 := hnrS.weakFV c.Ewf.ordered hinv3.lift (c.withMLC m3).Δwf
      |>.weakFV c.Ewf.ordered hinv4.lift (c.withMLC m4).Δwf
    have hnreq4 := E.mono (hΓ4 ▸ hnrS4.uniq c.Ewf (.refl c.Ewf (c.withMLC m4).Δwf) hnr4)
      |>.subst E.wf hcl4
    -- the fuel, and the recursion argument the `ih` telescope binds
    have htg4 := htg0.weakFV c.Ewf.ordered hinv3.lift (c.withMLC m3).Δwf
      |>.weakFV c.Ewf.ordered hinv4.lift (c.withMLC m4).Δwf
    have htgeq4 := E.mono (hΓ4 ▸ htgS4.uniq c.Ewf (.refl c.Ewf (c.withMLC m4).Δwf) htg4)
      |>.subst E.wf hcl4
    have hygeq4 := E.mono (hΓ4 ▸ hygS.uniq c.Ewf (.refl c.Ewf (c.withMLC m4).Δwf) hyg0)
      |>.subst E.wf hcl4
    -- and `go` at the lower fuel is that same recursor there
    have hshape_t : ((gohv'.appN [w1, w2, w3, w4]).subst
          ((γ.consN (σ b)).cons ((pack'.subst γ).appN (σ b)))).app (.natLit t) =
        ((gohv'.subst ((γ.consN (σ b)).cons ((pack'.subst γ).appN (σ b)))).appN
          ([w1, w2, w3, w4].map (.subst · ((γ.consN (σ b)).cons ((pack'.subst γ).appN (σ b)))) ++
            [.natLit t])) := by
      rw [VExpr.subst_appN, VExpr.appN_append]; rfl
    have hwflams_t := hheadc.symm.appN E.wf trivial
      (vs := [w1, w2, w3, w4].map
        (VExpr.subst · ((γ.consN (σ b)).cons ((pack'.subst γ).appN (σ b)))) ++
        [VExpr.natLit t]) hwf2t
    have htgv'2t := htgv'0.subst E.wf hcl2t
    simp only [VExpr.Subst.consN_append_singleton, VExpr.subst, VExpr.Subst.cons] at htgv'2t
    have hgott := hwflams_t.symm.trans E.wf trivial hbeta2t
    simp only [VExpr.Subst.consN_append_singleton, VExpr.subst] at hgott
    obtain ⟨_, _, hnrTt, htgTt⟩ := VExpr.WF.app_inv E.wf trivial
      ⟨_, hgott.choose_spec.hasType.2⟩
    have hgot := hgott.trans E.wf trivial <| htgv'2t.app_arg E.wf trivial hnrTt htgTt
    simp only [VExpr.liftN_liftN, VExpr.Subst.consN_append, VExpr.subst, VExpr.liftN,
      liftVar, List.cons_append, List.nil_append] at hnreq4 htgeq4 hygeq4
    rw [fun e τ => show (VExpr.liftN (2+2) e 0).subst _ = e.subst τ from
      VExpr.liftN_subst_consN (vs := [x, pf, arg, hy])] at hnreq4
    simp [VExpr.Subst.consN, VExpr.Subst.cons] at htgeq4 hygeq4
    -- assemble: the recursor at the lower fuel, the argument, and the proof
    rw [hih4]
    simp only [VExpr.appN, VExpr.subst] at hbeta4
    obtain ⟨_, _, hD1, _⟩ := VExpr.WF.app_inv E.wf trivial
      ⟨_, hbeta4.choose_spec.hasType.2⟩
    obtain ⟨_, _, hE1, _⟩ := VExpr.WF.app_inv E.wf trivial ⟨_, hD1⟩
    obtain ⟨_, _, hF1, hF2⟩ := VExpr.WF.app_inv E.wf trivial ⟨_, hE1⟩
    have hg1 := htgeq4.app_arg E.wf trivial hF1 hF2
    have hg2 := hg1.appN E.wf trivial (vs := [_, _]) ⟨_, hbeta4.choose_spec.hasType.2⟩
    obtain ⟨_, _, hG1, _⟩ := VExpr.WF.app_inv E.wf trivial ⟨_, hg2.choose_spec.hasType.2⟩
    obtain ⟨_, _, hH1, hH2⟩ := VExpr.WF.app_inv E.wf trivial ⟨_, hG1⟩
    have hg3 := hygeq4.app_arg E.wf trivial hH1 hH2
    have hg4 := hg3.appN E.wf trivial (vs := [_]) ⟨_, hg2.choose_spec.hasType.2⟩
    have hg5 := hnreq4.appN E.wf trivial (vs := [_, _, _]) ⟨_, hg4.choose_spec.hasType.2⟩
    have hchain := hbeta4.trans E.wf trivial <| hg2.trans E.wf trivial <| hg4.trans E.wf trivial hg5
    have hhead := hgot.symm.appN E.wf trivial (vs := [_, _]) ⟨_, hchain.choose_spec.hasType.2⟩
    exact ⟨_, hchain.trans E.wf trivial (hshape_t ▸ hhead)⟩

/-- Verification boundary for the well-founded recursion recognizer.

The unfolding facts are `NatFixUnfold'`, but the `probe` half cannot be folded into it: `probe`
runs the caller's right-hand-side builder under a binder it introduces, so its specification has
to quantify over that builder's behaviour. `probe` returns `Unit`, so there is nowhere to put the
equation it establishes except into the builder's own postcondition -- hence the implication into
a caller-chosen `Q`, which is where the caller does the instantiation it wants.

`e` and `meas` live in `c` and the recognizer opens its telescope internally, so no context
manipulation appears here at all -- the recursion telescope is instantiated by *application*
and `c`'s own binders by a closing substitution `γ`, leaving a ground statement. The probes'
contexts are built on top of `c` and are the business of `probe.WF`.

`R` is quantified after `γ`, which is what lets the answer depend on the closing: `Nat.bitwise`
is checked with its operator still a variable of `c`, and only a closing says which `Bool`
operation that variable stands for. -/
theorem unfoldNatWellFounded.WF {c : VContext} {m₀ : MLCtx} [c.MLCWF m₀] {s : VState}
    {e meas : Expr} {fail : ∀ {α}, M α} {ev mv : VExpr}
    (hev : (c.withMLC m₀).TrExprS e ev) (hmv : (c.withMLC m₀).TrExprS meas mv)
    (hnat : c.venv.contains ``Nat) (hsafe : c.safety = .safe)
    {wb : Condition.WF c Condition.bool}
    (hbool : wb.WF_ite (natOnly := true)) (hbeval : wb.IteEval (natOnly := true))
    {α} (σ : α → List VExpr) (σm : α → Nat)
    (hσm : ∀ (E : (c.withMLC m₀).Ext) γ, E.Closing γ → ∀ a,
      E.IsDefEqU₀ ((mv.subst γ).appN (σ a)) (.natLit (σm a)))
    (hnd : meas.natBinderTypes = true)
    (hfail : ∀ {α c s Q}, (@fail α).WF c s Q) :
    (unfoldNatWellFounded e meas fail).WF (c.withMLC m₀) s fun r _ =>
      ∃ P : ProbeBundle (c.withMLC m₀), r = P.toProbe ∧
        P.packAs.length = meas.lambdaArity ∧
        ((∀ a, (σ a).length = meas.lambdaArity) →
          ∀ (E : (c.withMLC m₀).Ext) γ, E.Closing γ → ∀ R : α → Nat, P.Done E γ σ σm R →
            ∀ a, E.IsDefEqU₀ ((ev.subst γ).appN (σ a)) (.natLit (R a))) :=
  (unfoldNatWellFounded.WF' hev hmv hnat hsafe hbool hbeval σ σm hσm hnd hfail).mono
    fun _ _ _ ⟨P, hr, hlp, hu⟩ =>
    ⟨P, hr, hlp, fun hlen E γ hg _ hdone a => (hu hlen E γ hg).elim (·.reflects hdone a)⟩

/-- The recursion `Nat.gcd` and `Nat.bitwise` share: two `Nat` arguments, well founded on the
first, which is what `fun m _ => m` measures.

The measure being fixed, so are its translation and what it is worth at the recursion's
arguments -- that is `natFstLamApp`, and it is a closed term, so no closing reaches it -- and all
that is left of `unfoldNatWellFounded.WF` for the caller is the value being unfolded. -/
theorem unfoldNatWellFounded.WF₂ {c : VContext} {m₀ : MLCtx} [c.MLCWF m₀] {s : VState}
    {e : Expr} {fail : ∀ {α}, M α} {ev : VExpr}
    (hev : (c.withMLC m₀).TrExprS e ev)
    (hnat : c.venv.contains ``Nat) (hsafe : c.safety = .safe)
    {wb : Condition.WF c Condition.bool}
    (hbool : wb.WF_ite (natOnly := true)) (hbeval : wb.IteEval (natOnly := true))
    (hfail : ∀ {α c s Q}, (@fail α).WF c s Q) :
    (unfoldNatWellFounded e q(fun m _n : Nat => m) fail).WF (c.withMLC m₀) s fun r _ =>
      ∃ P : ProbeBundle (c.withMLC m₀), r = P.toProbe ∧ P.packAs.length = 2 ∧
        ∀ (E : (c.withMLC m₀).Ext) γ, E.Closing γ → ∀ R : Nat × Nat → Nat,
          P.Done E γ (fun (m, n) => [.natLit m, .natLit n]) (·.1) R →
          ∀ a : Nat × Nat,
            E.IsDefEqU₀ ((ev.subst γ).appN [.natLit a.1, .natLit a.2]) (.natLit (R a)) := by
  have hΔ := (c.withMLC m₀).Δwf.toCtx
  have trNat {Δ} := c.hasPrimitives.trNat (Us := c.lparams) c.Ewf hnat (Δ := Δ)
  refine unfoldNatWellFounded.WF hev
    (.lam (hNatT hnat hΔ) trNat (.lam (hNatT hnat ⟨hΔ, hNatT hnat hΔ⟩) trNat (.bvar rfl)))
    hnat hsafe hbool hbeval (fun (m, n) => [.natLit m, .natLit n]) (·.1) ?_
    (by simp [Expr.natBinderTypes]) hfail |>.mono fun _ _ _ ⟨P, hr, hlp, hu⟩ => ?_
  · -- the measure is closed, so the closing goes straight past it
    rintro E γ hγ ⟨m, n⟩
    simpa [VLocalDecl.depth, VLocalDecl.value, VExpr.liftN, liftVar, VExpr.subst,
      VExpr.Subst.lift, VExpr.nat, VExpr.appN] using
      E.mono (c.hasPrimitives.natFstLamApp c.Ewf hnat trivial m n)
  · exact ⟨P, hr, by simpa [Expr.lambdaArity] using hlp,
      fun E γ hg R hd => hu (fun _ => by simp [Expr.lambdaArity]) E γ hg R hd⟩
