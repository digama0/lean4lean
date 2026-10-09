import Lean4Lean.Theory.Typing.Strengthening.Replay
import Lean4Lean.Theory.Typing.LevelledReduction

/-! # Typing strengthening: exposure through eta chains

The replay invariant and the exact remaining obligation.

An exposure path above `F↑ →* Π A B` is a sequence of `UpStep`s (parallel core, delta and eta
steps, `FullStep.upStep`). Replaying it below step by step is impossible with the invariant
"the current reduct is a lift": eta steps annotate with domains and parameters read from types
above (`headTypeBad`). The right invariant is **"the current reduct is an eta chain of a lift"**:
`EtaChain Γ' (e↑) X := ReflTransGen (EtaPar Γ') (e↑) X`, with `e` typed below.

* An eta step above extends the chain (nothing to do below).
* An eta-free step above must be pushed through the chain: `EtaReplay` (the exact remaining
  obligation): the chain of eta expansions of a lift, followed by a core or delta step, is
  simulated by a reduction of the term below, followed by a (possibly longer) eta chain. On the
  empty chain this is exactly the descent of `Replay.lean` (`etaReplay_of_descent`), so
  `EtaReplay` is "descent plus eta postponement with structure eta at firing majors absorbed".
* At the end, an eta chain from a lift of a type to a `Π` forces the lift to be a `Π`
  (`EtaChain.forallE_inv`: a type is neither a function nor a structure, so only the `forallE`
  congruence of `EtaPar` applies).

`piExposureRed_of_etaReplay`: `TypedFront ∧ EtaReplay → PiExposureRedN`;
`cancel_of_typedFront_of`: with `ProjFrontN` and `ElimFrontN`, `TypedFront → Cancel`;
`cancel_iff_typedFront_of`: the biconditional under these obligations. -/

namespace Lean4Lean.VEnv.StrengtheningExposure
open VExpr VEnv.StrengtheningTypingFront VEnv.StrengtheningReplay
variable {env : VEnv} {U k : Nat} {Γ Γ' : List VExpr} {A B F T e : VExpr}

section
open VEnv.Params
variable [VEnv.Params]

/-- A chain of parallel eta expansions. -/
abbrev EtaChain (Γ : List VExpr) : VExpr → VExpr → Prop := ReflTransGen (EtaPar Γ)

theorem EtaChain.hasType (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : EtaChain Γ a b) (ha : Params.env.HasType univs Γ a A) :
    Params.env.HasType univs Γ b A := by
  induction H with
  | rfl => exact ha
  | tail _ h ih => exact (EtaPar.full hΓ h ih).hasType hΓ ih

/-- A type eta-expands only by congruence; an eta expansion of a type into a `Π` is a `Π`. -/
theorem EtaPar.forallE_inv_r (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : EtaPar Γ x (.forallE A B)) (hx : Params.env.HasType univs Γ x (.sort u)) :
    ∃ A₀ B₀, x = .forallE A₀ B₀ := by
  generalize he : VExpr.forallE A B = r at H
  cases H with
  | forallE => exact ⟨_, _, rfl⟩
  | funEta _ _ ht => exact (type_not_function hΓ hx ht).elim
  | structEta _ _ _ hl _ _ hs _ => exact (type_not_structure hΓ hx hl hs).elim
  | _ => cases he

theorem EtaChain.forallE_inv (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : EtaChain Γ x (.forallE A B)) (hx : Params.env.HasType univs Γ x (.sort u)) :
    ∃ A₀ B₀, x = .forallE A₀ B₀ := by
  generalize hr : VExpr.forallE A B = r at H
  induction H generalizing A B with
  | rfl => exact ⟨_, _, hr.symm⟩
  | tail hchain hstep ih =>
    subst hr
    obtain ⟨A₁, B₁, rfl⟩ := EtaPar.forallE_inv_r hΓ hstep (EtaChain.hasType hΓ hchain hx)
    exact ih rfl

/-- OPEN: the exact remaining replay obligation. An eta chain above from the lift of a term typed
below, followed by one `UpStep`, is simulated by a reduction below followed by an eta chain. For
the empty chain this is the descent of core and delta steps (`etaReplay_of_descent`); for an eta
step it is trivial (`etaReplay_eta`); the content is pushing a core or delta step through eta
expansions, with structure eta at a firing major absorbed into the step below. -/
def EtaReplay : Prop :=
  ∀ ⦃k Γ Γ' e T X Y⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (Params.env.IsType univs) →
    OnCtx Γ' (Params.env.IsType univs) → Params.env.HasType univs Γ e T →
    EtaChain Γ' (e.liftN 1 k) X → UpStep Γ' X Y →
    ∃ e', FullReduction Γ e e' ∧ EtaChain Γ' (e'.liftN 1 k) Y

/-- The eta case of `EtaReplay` is trivial. -/
theorem etaReplay_eta (hX : EtaChain Γ' (e.liftN 1 k) X) (hY : EtaPar Γ' X Y) :
    ∃ e', FullReduction Γ e e' ∧ EtaChain Γ' (e'.liftN 1 k) Y :=
  ⟨e, .rfl, hX.tail hY⟩

/-- On the empty chain, `EtaReplay` is exactly the descent of `Replay.lean`. -/
theorem etaReplay_of_descent (hTF : TypedFrontN Params.env) (hcase : CaseRedexDescends)
    (hunfold : UnfoldingCheckDescends)
    (hcv : ∀ {p : Pattern} {r : p.RHS × p.Check}, Pat p r → CheckVars r.2)
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (he : Params.env.HasType univs Γ e T)
    (hY : UpStep Γ' (e.liftN 1 k) Y) :
    ∃ e', FullReduction Γ e e' ∧ EtaChain Γ' (e'.liftN 1 k) Y := by
  rcases hY with h | h | h
  · obtain ⟨e', rfl, h'⟩ := ParRed.descend hTF hcase hcv W hΓ hΓ' he h
    exact ⟨e', .tail .rfl (.core h'), .rfl⟩
  · obtain ⟨e', rfl, h'⟩ := DeltaPar.descend hTF hunfold W hΓ hΓ' he h
    exact ⟨e', h'.full, .rfl⟩
  · exact etaReplay_eta .rfl h

/-- Path replay with the eta-chain invariant: induction on the above `UpStep` path. -/
theorem path_replay (H : EtaReplay) (W : Ctx.LiftN 1 k Γ Γ')
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    (he : Params.env.HasType univs Γ e T)
    (hr : ReflTransGen (UpStep Γ') (e.liftN 1 k) Z) :
    ∃ e', FullReduction Γ e e' ∧ EtaChain Γ' (e'.liftN 1 k) Z := by
  induction hr with
  | rfl => exact ⟨e, .rfl, .rfl⟩
  | tail _ step ih =>
    obtain ⟨e₁, hred, hchain⟩ := ih
    obtain ⟨e₂, hred₂, hchain₂⟩ := H W hΓ hΓ' (hred.hasType hΓ he) hchain step
    exact ⟨e₂, hred.trans hred₂, hchain₂⟩

theorem FullReduction.upSteps (H : FullReduction Γ a b) : ReflTransGen (UpStep Γ) a b := by
  induction H with
  | rfl => exact .rfl
  | tail _ h ih => exact ih.trans h.upStep

end

/-- Reduction-form exposure from the typed front and the replay obligation. -/
theorem piExposureRed_of_etaReplay (henv : env.WF)
    (H : ∀ U, @EtaReplay (henv.params U)) : PiExposureRedN henv := by
  intro U k Γ Γ' f F u A B W hΓ hΓ' _ hF hr
  letI := henv.params U
  obtain ⟨F', hred, hchain⟩ := path_replay (H U) W hΓ hΓ' hF (FullReduction.upSteps hr)
  have hF' : env.HasType U Γ' (F'.liftN 1 k) (.sort u) :=
    (hred.hasType hΓ hF).weakN henv.ordered W
  obtain ⟨A₁, B₁, hPi⟩ := EtaChain.forallE_inv hΓ' hchain hF'
  obtain ⟨A₀, B₀, rfl, -, -⟩ := liftN_eq_forallE_inv hPi
  exact ⟨A₀, B₀, hred⟩

/-- `TypedFront → Cancel`, given the replay obligation and the projection and eliminator
closures. The typed front enters only through `AppFrontN.of_piExposure` (domain agreement) and,
inside `EtaReplay`, through the guards of the replayed steps. -/
theorem cancel_of_typedFront_of (henv : env.WF) (heq : env.HasCanonicalEq)
    (hTF : StrengtheningKripke.TypedFront env) (H : ∀ U, @EtaReplay (henv.params U))
    (hProj : ProjFrontN env) (hElim : ElimFrontN env) : Cancel env :=
  cancel_of_piExposureRed henv heq (piExposureRed_of_etaReplay henv H)
    ((typeFrontN_iff_typedFront henv heq).mpr hTF) hProj hElim

theorem cancel_iff_typedFront_of (henv : env.WF) (heq : env.HasCanonicalEq)
    (H : ∀ U, @EtaReplay (henv.params U)) (hProj : ProjFrontN env) (hElim : ElimFrontN env) :
    Cancel env ↔ StrengtheningKripke.TypedFront env :=
  ⟨fun hc => ((cancel_iff_typedFront_and_closures henv heq).mp hc).1,
    fun hTF => cancel_of_typedFront_of henv heq hTF H hProj hElim⟩

/-- The replay obligation holds on empty chains from the typed front and the two guard
descents, in every well-formed environment (the concrete pattern table has `CheckVars`). -/
theorem etaReplay_empty_chain (henv : env.WF) (heq : env.HasCanonicalEq)
    (hTF : StrengtheningKripke.TypedFront env) (U : Nat)
    (hcase : @CaseRedexDescends (henv.params U)) (hunfold : @UnfoldingCheckDescends (henv.params U))
    {k : Nat} {Γ Γ' : List VExpr} {e T Y : VExpr}
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    (he : env.HasType U Γ e T) (hY : @UpStep (henv.params U) Γ' (e.liftN 1 k) Y) :
    letI := henv.params U
    ∃ e', FullReduction Γ e e' ∧ EtaChain Γ' (e'.liftN 1 k) Y := by
  letI := henv.params U
  exact etaReplay_of_descent ((typedFrontN_iff_typedFront henv heq).mpr hTF) hcase hunfold
    (fun hp => Params.checkVars henv U hp) W hΓ hΓ' he hY

/-! ## The regression path satisfies the eta-chain invariant

Astra's `headSource` path (`TypingFront.lean`): one eta step inside the argument (output not a
lift, `headType_bad_reduct`), then a beta at the root. It defeats the invariant "the reduct is a
lift" (`headSource_path_not_descending`) but not the eta-chain invariant: the reduct after the eta
step is an eta chain of the lift, the beta step above is simulated by the beta step below, and
the final reduct `headTypeBad Q` is an eta chain of the lift of the exposed `Π` below. -/

section
open VEnv.Params
variable [VEnv.Params]

/-- The eta step of the regression path as a parallel eta expansion of the lift. -/
theorem etaPar_headType_bad {Q : VExpr} :
    EtaPar (Q :: Γ) headType.lift (headTypeBad Q) := by
  have hd : Params.env.IsDefEq univs (Q :: Γ) (badDomain Q) (.sort .zero) (.sort (.succ .zero)) :=
    .beta (HasType.sort (l := .zero) trivial) (.bvar .zero)
  have hf : Params.env.HasType univs (Q :: Γ) StrengtheningObstructions.idProp
      (.forallE (.sort .zero) (.sort .zero)) := .lamDF (HasType.sort (l := .zero) trivial) (.bvar .zero)
  have hp := IsDefEq.forallEDF hd.symm (HasType.sort (env := Params.env) (U := univs)
    (Γ := .sort .zero :: Q :: Γ) (l := .zero) trivial)
  have hEta : EtaPar (Q :: Γ) StrengtheningObstructions.idProp (badEta Q) := by
    simpa [badEta, StrengtheningObstructions.idProp, lift, liftN, liftVar] using
      EtaPar.funEta (e' := StrengtheningObstructions.idProp) (A' := badDomain Q) .rfl .rfl
        (IsDefEq.defeqDF hp hf)
  simpa [headType, headTypeBad, StrengtheningObstructions.idProp, lift, liftN, liftVar] using
    EtaPar.forallE (EtaPar.app .rfl hEta) .rfl

/-- The regression path: an eta chain from the lift, one beta step above, the beta step below,
and the eta-chain invariant at the end. -/
theorem headSource_etaReplay_instance {Q : VExpr} :
    EtaChain (Q :: Γ) headSource.lift (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (headTypeBad Q)) ∧
    ParRed (Q :: Γ) (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (headTypeBad Q)) (headTypeBad Q) ∧
    FullReduction Γ headSource headType ∧
    EtaChain (Q :: Γ) headType.lift (headTypeBad Q) := by
  refine ⟨?_, ?_, ?_, .tail .rfl etaPar_headType_bad⟩
  · refine .tail .rfl ?_
    simpa [headSource, lift, liftN, liftVar] using
      EtaPar.app (.rfl (e := VExpr.lam (.sort (.succ .zero)) (.bvar 0))) etaPar_headType_bad
  · simpa [inst, instVar] using
      (ParRed.beta (Γ := Q :: Γ) (A := .sort (.succ .zero)) (e₁ := .bvar 0)
        (e₂ := headTypeBad Q) .rfl .rfl)
  · refine .tail .rfl ?_
    simpa [headSource, inst, instVar] using
      (FullStep.core (ParRed.beta (Γ := Γ) (A := .sort (.succ .zero)) (e₁ := .bvar 0)
        (e₂ := headType) .rfl .rfl))

end

end Lean4Lean.VEnv.StrengtheningExposure

