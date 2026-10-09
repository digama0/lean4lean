import Lean4Lean.Theory.Typing.Strengthening.Kripke
import Lean4Lean.Theory.Typing.EqTyping
import Lean4Lean.Theory.Typing.Confluence.QuotPrefixTyping
import Lean4Lean.Theory.Typing.Confluence.SingletonExtractionTyping

/-! # Counterexample candidates for `Cancel` under canonical `Eq`: the mechanism ledger

`Cancel env` (`Strengthening/Cancel.lean`): `Γ ⊢ λ Q. a↑ ≡ λ Q. b↑` implies `Γ ⊢ a ≡ b`. A
counterexample needs a well-formed environment with canonical `Eq`, a context `Γ`, a type `Q`
with no inhabitant in `Γ` (`Cancel.inhabited` settles the inhabited case by substitution), and
`q`-free `a`, `b` with `Q :: Γ ⊢ a↑ ≡ b↑` and `Γ ⊬ a ≡ b`. This file is the checked ledger of
the mechanisms tried for producing such a `Q`-dependent conversion between `q`-free terms, one
bullet per mechanism and the theorem that kills it. Every theorem is about the declarative
judgement `VEnv.IsDefEq` itself (all derivations, not a chosen evaluator), with its typing
premises explicit; none assumes `Strengthening` or `Cancel`. Adapted from Astra's round 7
ledger (`strengthening-context/round7/counterexample/Round7.lean`, 2026-10-09).

* **K on an unaligned cast.** `typeCast u X Y e x ≡ x` holds exactly when `X ≡ Y` already
  holds in the same context (`cast_identity_iff`, by unique typing of the cast and of `x`); so
  a hypothesis `q : Eq (Sort u) X Y` between judgmentally distinct types does not make the cast
  compute (`unaligned_cast_not_identity`, on `X := Prop`, `Y := Prop → Prop`, where head
  separation keeps the endpoints apart even with the hypothesis in the context,
  `assumed_equality_does_not_align`), and the `UnfoldingCheck` spine comparison of `Eq.rec`
  with its iota instance already contains the alignment (`eqRec_spine_requires_alignment`,
  `unaligned_spine_check_impossible`). When the endpoints are aligned below, the cast computes
  below with a proof built from `Eq.refl` (`aligned_cast_below`); above it computes with any
  proof, including one mentioning `q` (`aligned_cast_above`). Residual: an endpoint alignment
  `X↑ ≡ Y↑` available only above, which is a type-level instance of `Cancel` itself.
* **Prop-source quotients.** A typed major of `Quot Q r` with `Q : Sort u`, `u ≈ 0`, supplies
  an inhabitant of `Q` below through `Quot.ind` (`quotient_source_cannot_be_missing`), so
  the `Cancel` instance is the inhabited one (`quotient_source_cancel`). The five-argument
  `Quot.lift` prefix equation holds below whenever the prefix is typed below
  (`quotient_prefix_below`, `quotient_prefix_above`). Definitional rules of quotients are
  unconditional stored equations with no proof guard.
* **Dependent singleton proof fields.** The proof-major/iota join `f p ≡ f (mk ..) ≡ middle ≡
  g (mk' ..) ≡ g r` is the exact declarative chain of the Eq-free countermodel
  (`proof_major_join`, all iota premises explicit). With canonical `Eq` the Prop field of a
  singleton is extracted from any major typed below by the cast-telescope extractor
  (`singleton_cast_extractor_exists`, from `PropElim.value_typed`), so the proposed missing
  inhabitant exists below. Residual: a major typed at the family only above.
* **Unit-like and structure eta.** Both rules use only the registered shape and the typing of
  their subjects; given those below, the equation holds below (`unit_below`, `unit_above`,
  `structure_eta_below`, `structure_eta_above`). Retyping two independently typed values at a
  common type above forces their types to agree above (`common_retyping_requires_alignment`,
  `shared_middle_forces_type_agreement`). Residual: the retyping available only above.
* **Definitions and recursors blocked until `q` is present.** Stored equations have no local
  proof guard (`definition_equation_below`, `definition_equation_above`). Applying an
  abstraction to `q` and beta-reducing produces an intermediate that mentions `q` but an
  equation that is reflexive below (`detour_eq`).
* **Universe identities forced by `Q`.** No context makes `Sort u ≡ Sort v` for `u ≉ v`
  (`universe_gate_impossible`); a sort equation above descends with its well-formedness
  (`sort_front`).
* **Syntactic separating invariants.** Raw support (not mentioning `q`) is not preserved by
  `IsDefEq` in the larger context (`no_support_invariant`, `wellformed_support_obstruction`),
  nor is the parity of the number of occurrences of `q` (`no_occurrence_parity_invariant`);
  the beta detour breaks both.
* **The remaining obligation.** `UninhabitedCancel`: `Cancel` restricted to binders with no
  inhabitant below; equivalent to `Cancel` under `WF` (`uninhabitedCancel_iff_cancel`).

The second part of the hunt (the typing gap and rigid binders) continues in
`Strengthening/Hunt.lean`. -/

namespace Lean4Lean
namespace VEnv.StrengtheningCandidates
open VEnv VExpr


variable {env : VEnv} {U : Nat} {Γ : List VExpr}

/-- A cast computes to the original term exactly when its endpoint types
are already judgmentally equal. The forward implication uses unique typing,
not an assumption that the derivation ends in the K rule. -/
theorem cast_identity_iff (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (hu : u.WF U)
    (hX : env.HasType U Γ X (.sort u)) (hY : env.HasType U Γ Y (.sort u))
    (he : env.HasType U Γ e (eqApp (.succ u) (.sort u) X Y))
    (hx : env.HasType U Γ x X) :
    env.IsDefEqU U Γ (typeCast u X Y e x) x ↔
      env.IsDefEq U Γ X Y (.sort u) := by
  constructor
  · intro H
    have hc := HasType.typeCast henv.ordered heq hu hX hY he hx
    have hyx := (H.of_l henv hΓ hc).uniqU henv hΓ hx
    exact hyx.symm.of_l henv hΓ hX
  · intro H
    exact ⟨_, IsDefEq.typeCast_refl henv heq hu hΓ H he hx⟩

/-- One shared intermediate cannot hide disagreement between independently
typed endpoint types. This includes casts, recursors and eta expansions. -/
theorem shared_middle_forces_type_agreement (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (ha : env.HasType U Γ a A) (hb : env.HasType U Γ b B)
    (ham : env.IsDefEqU U Γ a m) (hmb : env.IsDefEqU U Γ m b) :
    env.IsDefEqU U Γ A B :=
  ((ham.trans henv hΓ hmb).of_l henv hΓ ha).uniqU henv hΓ hb

/-- Extract the literal argument comparisons from the actual alignment
predicate used in UnfoldingCheck.recursor_lhs. -/
theorem spine_arguments
    (H : ConstSpineDefEq env U Γ (mkApps (.const c ls) args)
      (mkApps (.const c ls') args')) :
    List.Forall₂ (env.IsDefEqU U Γ) args args' := by
  obtain ⟨n, us, vs, xs, ys, ha, hb, _, _, _, hargs⟩ := H
  have ha' := congrArg VExpr.getAppFnArgs ha
  have hb' := congrArg VExpr.getAppFnArgs hb
  simp only [getAppFnArgs_mkApps_const, Prod.mk.injEq] at ha' hb'
  rw [ha'.2, hb'.2]
  exact hargs

/-- For the six-argument Eq.rec spine, alignment with the iota instance
already contains judgmental equality of the endpoint and the basepoint. -/
theorem eqRec_spine_requires_alignment
    (H : ConstSpineDefEq env U Γ
      (eqRecApp v w α a M x b e)
      (eqRecApp v w α a M x a (eqReflApp w α a))) :
    env.IsDefEqU U Γ b a := by
  have h : List.Forall₂ (env.IsDefEqU U Γ)
      [α, a, M, x, b, e] [α, a, M, x, a, eqReflApp w α a] :=
    spine_arguments H
  cases h with | cons _ h =>
    cases h with | cons _ h =>
      cases h with | cons _ h =>
        cases h with | cons _ h =>
          cases h with | cons h _ => exact h

def S0 : VExpr := .sort .zero
def S1 : VExpr := .sort (.succ .zero)
def piProp : VExpr := .forallE S0 S0
def falseAlignment : VExpr := eqApp (.succ (.succ .zero)) S1 S0 piProp

theorem piProp_type : env.HasType U Γ piProp S1 :=
  StrengtheningObstructions.bodyPi_typed

theorem falseAlignment_type (heq : env.HasCanonicalEq) :
    env.HasType U Γ falseAlignment S0 :=
  HasType.eqApp heq trivial (.sort trivial) (.sort trivial) piProp_type

/-- Even in a well-formed context containing an object-language proof of
the equality of these types, the two types are not judgmentally equal. -/
theorem assumed_equality_does_not_align (henv : env.WF)
    (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType U)) :
    env.HasType U (falseAlignment :: Γ) (.bvar 0) falseAlignment ∧
      ¬ env.IsDefEqU U (falseAlignment :: Γ) S0 piProp := by
  constructor
  · exact .bvar .zero
  · exact IsDefEqU.sort_forallE_inv henv ⟨hΓ, _, falseAlignment_type heq⟩

/-- The K shortcut fails for every argument x : Prop, not just a selected
reduction strategy. This rules out all declarative derivations of it. -/
theorem unaligned_cast_not_identity (henv : env.WF)
    (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType U))
    (hx : env.HasType U Γ x S0) :
    ¬ env.IsDefEqU U (falseAlignment :: Γ)
      (typeCast (.succ .zero) S0 piProp (.bvar 0) x.lift) x.lift := by
  have hΔ : OnCtx (falseAlignment :: Γ) (env.IsType U) :=
    ⟨hΓ, _, falseAlignment_type heq⟩
  intro H
  have h := (cast_identity_iff (u := .succ .zero) henv heq hΔ trivial
    (HasType.sort (l := .zero) trivial) piProp_type (.bvar .zero)
    (hx.weak henv.ordered)).mp H
  exact (assumed_equality_does_not_align henv heq hΓ).2 ⟨_, h⟩

/-- The literal UnfoldingCheck alignment shortcut is blocked too. Merely
possessing q : Eq S1 S0 piProp does not pass its spine comparison. -/
theorem unaligned_spine_check_impossible (henv : env.WF)
    (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType U)) :
    ¬ ConstSpineDefEq env U (falseAlignment :: Γ)
      (eqRecApp v (.succ (.succ .zero)) S1 S0 M x piProp (.bvar 0))
      (eqRecApp v (.succ (.succ .zero)) S1 S0 M x S0
        (eqReflApp (.succ (.succ .zero)) S1 S0)) := by
  intro H
  exact (assumed_equality_does_not_align henv heq hΓ).2
    (eqRec_spine_requires_alignment H).symm

/-- The canonical-Eq extraction function is typed before the occurrence
and before any proposed missing inhabitant. Its result is a function of
the cast telescope, so this statement does not assert occurrence alignment. -/
theorem singleton_cast_extractor_exists (henv : env.WF) (heq : env.HasCanonicalEq)
    {S : SingletonLayout} {E : PropElim} {params : List VExpr}
    (W : E.WF S params env U) (hj : j < S.fields.length)
    (hs : S.slot.getD j none = none) :
    env.HasType U [] (PropElim.value S params E j)
      (PropElim.valueType S params E j) :=
  PropElim.value_typed params henv heq W hj hs

/-- Exact declarative proof-major/iota join, used by both the old example
and its dependent-field variants. All iota premises are stated explicitly;
this theorem does not invent an environment containing those equations. -/
theorem proof_major_join
    (hI : env.HasType U Γ I S0) (hJ : env.HasType U Γ J S0)
    (hp : env.HasType U Γ p I) (hr : env.HasType U Γ r J)
    (hcI : env.HasType U Γ cI I) (hcJ : env.HasType U Γ cJ J)
    (hf : env.HasType U Γ f (.forallE I T.lift))
    (hg : env.HasType U Γ g (.forallE J T.lift))
    (hi : env.IsDefEq U Γ (.app f cI) middle T)
    (hj : env.IsDefEq U Γ (.app g cJ) middle T) :
    env.IsDefEq U Γ (.app f p) (.app g r) T := by
  have hleft : env.IsDefEq U Γ (.app f p) (.app f cI) T := by
    simpa only [inst_lift] using IsDefEq.appDF hf (IsDefEq.proofIrrel hI hp hcI)
  have hright : env.IsDefEq U Γ (.app g r) (.app g cJ) T := by
    simpa only [inst_lift] using IsDefEq.appDF hg (IsDefEq.proofIrrel hJ hr hcJ)
  exact ((hleft.trans hi).trans hj.symm).trans hright.symm

/-- Aligned K computation in an arbitrary larger context. The removed
variable may occur in the proof; only the endpoint conversion is used. -/
theorem aligned_cast_above (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓQ : OnCtx (Q :: Γ) (env.IsType U)) (hu : u.WF U)
    (hXY : env.IsDefEq U Γ X Y (.sort u)) (hx : env.HasType U Γ x X)
    (he : env.HasType U (Q :: Γ) e
      (eqApp (.succ u) (.sort u) X.lift Y.lift)) :
    env.IsDefEq U (Q :: Γ) (typeCast u X.lift Y.lift e x.lift) x.lift Y.lift :=
  IsDefEq.typeCast_refl henv heq hu hΓQ (hXY.weak henv.ordered) he
    (hx.weak henv.ordered)

/-- If the alignment is already available below, so is a proof that makes
the cast compute below. No proof of Q is needed. -/
theorem aligned_cast_below (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (hu : u.WF U)
    (hXY : env.IsDefEq U Γ X Y (.sort u)) (hx : env.HasType U Γ x X) :
    ∃ e, env.HasType U Γ e (eqApp (.succ u) (.sort u) X Y) ∧
      env.IsDefEq U Γ (typeCast u X Y e x) x Y := by
  have hr := HasType.eqReflApp (w := .succ u) heq hu (HasType.sort hu) hXY.hasType.1
  have he := (IsDefEq.eqApp_r (w := .succ u) heq hu (HasType.sort hu) hXY.hasType.1 hXY).defeq hr
  exact ⟨_, he, IsDefEq.typeCast_refl henv heq hu hΓ hXY he hx⟩

/-- A Prop-source quotient already supplies the proposed missing source
inhabitant, in the smaller context. -/
theorem quotient_source_cannot_be_missing (hr : QuotRegistered env)
    (hu : u.WF U) (hz : u ≈ .zero)
    (ha : env.HasType U Γ Q (.sort u))
    (hrel : env.HasType U Γ r (.forallE Q (.forallE Q.lift S0)))
    (hm : env.HasType U Γ m (mkApps (.const ``Quot [u]) [Q, r])) :
    ∃ q, env.HasType U Γ q Q :=
  ⟨_, hr.propInhabitant_app hu hz ha hrel hm⟩

/-- The corresponding full Cancel instance is solved by that selector. -/
theorem quotient_source_cancel (henv : env.WF) (hr : QuotRegistered env)
    (hΓ : OnCtx Γ (env.IsType U)) (hu : u.WF U) (hz : u ≈ .zero)
    (ha : env.HasType U Γ Q (.sort u))
    (hrel : env.HasType U Γ r (.forallE Q (.forallE Q.lift S0)))
    (hm : env.HasType U Γ m (mkApps (.const ``Quot [u]) [Q, r]))
    (H : env.IsDefEqU U Γ (.lam Q a.lift) (.lam Q b.lift)) :
    env.IsDefEqU U Γ a b := by
  obtain ⟨q, hq⟩ := quotient_source_cannot_be_missing hr hu hz ha hrel hm
  exact Cancel.inhabited henv hΓ hq H

/-- At the actual five-argument prefix, quotient computation is already
available below whenever that prefix is typed below. -/
theorem quotient_prefix_below (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hr : QuotRegistered env) (hu : u.WF U) (hv : v.WF U) (hz : u ≈ .zero)
    (ht : VExpr.WF env U Γ (mkApps (.const ``Quot.lift [u,v]) [α, r, B, f, c])) :
    env.IsDefEqU U Γ (mkApps (.const ``Quot.lift [u,v]) [α, r, B, f, c])
      (.lam (mkApps (.const ``Quot [u]) [α,r])
        (.app f.lift (mkApps (QuotPrefixUnfolding.propInhabitant u)
          [α.lift, r.lift, .bvar 0]))) :=
  (QuotPrefixUnfold.atFive henv hΓ hr hu hv hz ht).defeq henv hΓ

/-- The same equation is checked in the larger context as well. -/
theorem quotient_prefix_above (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hr : QuotRegistered env) (hu : u.WF U) (hv : v.WF U) (hz : u ≈ .zero)
    (ht : VExpr.WF env U Γ (mkApps (.const ``Quot.lift [u,v]) [α, r, B, f, c])) :
    env.IsDefEqU U (Q :: Γ)
      ((mkApps (.const ``Quot.lift [u,v]) [α, r, B, f, c]).lift)
      ((.lam (mkApps (.const ``Quot [u]) [α,r])
        (.app f.lift (mkApps (QuotPrefixUnfolding.propInhabitant u)
          [α.lift, r.lift, .bvar 0])) : VExpr).lift) :=
  (quotient_prefix_below henv hΓ hr hu hv hz ht).weakN henv.ordered Ctx.LiftN.one

/-- No local hypothesis changes universe equivalence. This quantifies over
all declarative derivations, including arbitrary dependent intermediates. -/
theorem universe_gate_impossible (henv : env.WF)
    (hΓQ : OnCtx (Q :: Γ) (env.IsType U)) (hne : ¬ u ≈ v) :
    ¬ env.IsDefEqU U (Q :: Γ) (.sort u) (.sort v) :=
  fun H => hne (H.sort_inv henv hΓQ)

/-- Complete descent for sort endpoints, including their well-formedness.
Thus the universe candidate either fails above or succeeds below. -/
theorem sort_front (henv : env.WF)
    (hΓQ : OnCtx (Q :: Γ) (env.IsType U))
    (H : env.IsDefEqU U (Q :: Γ) (.sort u) (.sort v)) :
    env.IsDefEqU U Γ (.sort u) (.sort v) := by
  obtain ⟨T, h⟩ := H
  exact ⟨_, .sortDF (h.sort_inv_l henv.ordered) (h.symm.sort_inv_l henv.ordered)
    (IsDefEqU.sort_inv henv hΓQ ⟨T, h⟩)⟩

/-- Installed definition equations have no local proof guard. -/
theorem definition_equation_below (hd : env.defeqs df)
    (hw : ∀ l ∈ ls, l.WF U) (hl : ls.length = df.uvars) :
    env.IsDefEq U Γ (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) :=
  .extra hd hw hl

theorem definition_equation_above (hd : env.defeqs df)
    (hw : ∀ l ∈ ls, l.WF U) (hl : ls.length = df.uvars) :
    env.IsDefEq U (Q :: Γ) (df.lhs.instL ls) (df.rhs.instL ls) (df.type.instL ls) :=
  .extra hd hw hl

/-- Unit-like equality uses only the registered shape and the two typings.
If these are available below, the equality is available below. -/
theorem unit_below (hi : env.projections name info)
    (hp : ps.length = info.nparams) (hn : info.nindices = 0) (hf : info.numFields = 0)
    (ha : env.HasType U Γ a (mkApps (.const name ls) ps))
    (hb : env.HasType U Γ b (mkApps (.const name ls) ps)) :
    env.IsDefEq U Γ a b (mkApps (.const name ls) ps) :=
  .unitLike hi hp hn hf ha hb

theorem unit_above (henv : env.WF) (hi : env.projections name info)
    (hp : ps.length = info.nparams) (hn : info.nindices = 0) (hf : info.numFields = 0)
    (ha : env.HasType U Γ a (mkApps (.const name ls) ps))
    (hb : env.HasType U Γ b (mkApps (.const name ls) ps)) :
    env.IsDefEqU U (Q :: Γ) a.lift b.lift :=
  (show env.IsDefEqU U Γ a b from ⟨_, unit_below hi hp hn hf ha hb⟩).weakN
    henv.ordered Ctx.LiftN.one

theorem structure_eta_below (hi : env.projections name info)
    (hp : ps.length = info.nparams) (hn : info.nindices = 0)
    (he : env.HasType U Γ e (mkApps (.const name ls) ps))
    (hc : env.HasType U Γ (mkApps (.const info.ctorName ls)
      (ps ++ (List.range info.numFields).map fun i => .proj name i e))
      (mkApps (.const name ls) ps)) :
    env.IsDefEq U Γ (mkApps (.const info.ctorName ls)
      (ps ++ (List.range info.numFields).map fun i => .proj name i e)) e
      (mkApps (.const name ls) ps) :=
  .structEta hi hp hn he hc

theorem structure_eta_above (henv : env.WF) (hi : env.projections name info)
    (hp : ps.length = info.nparams) (hn : info.nindices = 0)
    (he : env.HasType U Γ e (mkApps (.const name ls) ps))
    (hc : env.HasType U Γ (mkApps (.const info.ctorName ls)
      (ps ++ (List.range info.numFields).map fun i => .proj name i e))
      (mkApps (.const name ls) ps)) :
    env.IsDefEqU U (Q :: Γ)
      (mkApps (.const info.ctorName ls)
        (ps ++ (List.range info.numFields).map fun i => .proj name i e)).lift e.lift :=
  (show env.IsDefEqU U Γ _ _ from ⟨_, structure_eta_below hi hp hn he hc⟩).weakN
    henv.ordered Ctx.LiftN.one

/-- Retyping independently typed values into a common unit-like or
structure type requires agreement of their original types in that context.
It supplies no smaller derivation of that agreement. -/
theorem common_retyping_requires_alignment (henv : env.WF)
    (hΓQ : OnCtx (Q :: Γ) (env.IsType U))
    (ha : env.HasType U Γ a A) (hb : env.HasType U Γ b B)
    (ha' : env.HasType U (Q :: Γ) a.lift T)
    (hb' : env.HasType U (Q :: Γ) b.lift T) :
    env.IsDefEqU U (Q :: Γ) A.lift B.lift := by
  have hAT := (ha.weak henv.ordered).uniqU henv hΓQ ha'
  have hTB := hb'.uniqU henv hΓQ (hb.weak henv.ordered)
  exact hAT.trans henv hΓQ hTB

/-- A syntactic "does not mention q" invariant cannot be preserved by every
equality rule, even if Q has no inhabitant below. Beta expansion alone
introduces q in an intermediate. -/
def detour (Q a : VExpr) : VExpr :=
  .app (.lam Q.lift (a.liftN 2)) (.bvar 0)

theorem detour_eq (henv : env.Ordered) (ha : env.HasType U Γ a A) :
    env.IsDefEq U (Q :: Γ) (detour Q a) a.lift A.lift := by
  have hb : env.HasType U (Q.lift :: Q :: Γ) (a.liftN 2) (A.liftN 2) :=
    ha.weakN henv (Ctx.LiftN.zero [Q.lift, Q] rfl)
  simpa only [detour, inst_liftN', lift] using
    (IsDefEq.beta hb (show env.HasType U (Q :: Γ) (.bvar 0) Q.lift from .bvar .zero))

theorem detour_mentions_removed (Q a : VExpr) : ¬ (detour Q a).Skips 1 0 := by
  simp [detour, VExpr.skips_iff, VExpr.Skips']

def SupportInvariant (env : VEnv) (U : Nat) (Δ : List VExpr) : Prop :=
  ∀ a b, env.IsDefEqU U Δ a b → a.Skips 1 0 → b.Skips 1 0

theorem no_support_invariant (henv : env.Ordered) (ha : env.HasType U Γ a A) :
    ¬ SupportInvariant env U (Q :: Γ) := by
  intro hi
  exact detour_mentions_removed Q a
    (hi a.lift (detour Q a) ⟨_, (detour_eq henv ha).symm⟩ .liftN)

/-- This obstruction occurs in every well-formed extension, including
every uninhabited one: choose the closed term Prop as the source. -/
theorem wellformed_support_obstruction (henv : env.WF)
    (_hΓQ : OnCtx (Q :: Γ) (env.IsType U)) :
    ∃ a m T, a.Skips 1 0 ∧ ¬ m.Skips 1 0 ∧
      env.IsDefEq U (Q :: Γ) a m T ∧
      env.IsDefEq U (Q :: Γ) m a T := by
  have h := detour_eq (Q := Q) henv.ordered
    (show env.HasType U Γ S0 S1 from .sort trivial)
  exact ⟨S0.lift, detour Q S0, S1.lift, .liftN,
    detour_mentions_removed Q S0, h.symm, h⟩

/-- Counts free occurrences of exactly one de Bruijn variable, accounting
for the change of depth beneath binders. -/
def occurrences (k : Nat) : VExpr → Nat
  | .bvar i => if i = k then 1 else 0
  | .app f a => occurrences k f + occurrences k a
  | .lam A b | .forallE A b => occurrences k A + occurrences (k + 1) b
  | .proj _ _ e => occurrences k e
  | _ => 0

theorem occurrences_lift (e : VExpr) (k : Nat) :
    occurrences k (e.liftN 1 k) = 0 := by
  induction e generalizing k <;> simp [VExpr.liftN, occurrences, *]
  case bvar i =>
    unfold liftVar
    split <;> rename_i h
    · simp [show i ≠ k by omega]
    · simp [show 1 + i ≠ k by omega]

/-- Parity of the removed variable's occurrences also fails as an
invariant of the full judgment: the same beta detour changes 0 to 1. -/
theorem no_occurrence_parity_invariant (henv : env.Ordered) :
    ∃ a b T, env.IsDefEq U (Q :: Γ) a b T ∧
      occurrences 0 a % 2 = 0 ∧ occurrences 0 b % 2 = 1 := by
  have h := detour_eq (Q := Q) henv
    (show env.HasType U Γ S0 S1 from .sort trivial)
  refine ⟨S0.lift, detour Q S0, S1.lift, h.symm, rfl, ?_⟩
  simp [detour, occurrences, lift, occurrences_lift, S0, liftN]

/-- The sole unproved obligation, restricted to the only unsolved case.
No independent smaller-context typing of a or b is assumed. -/
def UninhabitedCancel (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q a b⦄, OnCtx Γ (env.IsType U) →
    (∀ q, ¬ env.HasType U Γ q Q) →
    env.IsDefEqU U Γ (.lam Q a.lift) (.lam Q b.lift) →
    env.IsDefEqU U Γ a b

theorem uninhabitedCancel_iff_cancel (henv : env.WF) :
    UninhabitedCancel env ↔ Cancel env := by
  constructor
  · intro H U Γ Q a b hΓ hab
    classical
    by_cases hq : ∃ q, env.HasType U Γ q Q
    · obtain ⟨q, hq⟩ := hq
      exact Cancel.inhabited henv hΓ hq hab
    · exact H hΓ (by simpa using hq) hab
  · intro H U Γ Q a b hΓ _ hab
    exact H hΓ hab

end VEnv.StrengtheningCandidates
end Lean4Lean
