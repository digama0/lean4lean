import Lean4Lean.Theory.Typing.Strengthening.TypingFront
import Lean4Lean.Theory.Typing.Strengthening.Hunt
import Lean4Lean.Theory.Typing.HeadReduction

/-! # Typing strengthening: local replay of reduction steps

Astra's round 9 design check (checked file
`StrengtheningRound9_2026-10-09.lean`, outside this repository), adapted with names kept:

* `typeFrontN_iff_typeFront`, `typeFrontN_iff_typedFront`: the `LiftN` form of the type front is
  the front form, hence Kripke's `TypedFront` under canonical `Eq` (induction on the insertion,
  abstracting the two types by `Π D`).
* `piExposureRed_iff_piExposure`: exposure in reduction form is exposure in conversion form.
* `retyping_of_typeFrontN`: a term typed below at `T` and above at the lift of a type `A` of `Γ`
  is typed below at `A` (unique typing plus the type front).
* `cancel_iff_typedFront_and_closures`: the exact formulation
  `Cancel ↔ TypedFront ∧ AppFrontN ∧ ProjFrontN ∧ ElimFrontN`.
* `core_exposure_standard`: core standardisation gives head exposure for `ParRedS`; projections
  have no core head exposure (`projection_full_exposure`), so a head strategy for `FullReduction`
  is outside `WHRed`.
* `saturated_projection_replay`: projection iota replays below with no hypothesis.
* `HeadStep`, `LocalReplay` (Astra's `HeadReplay`), `HeadStandard`, `head_path_replay`: given an
  exact local replay interface for the eta-free head fragment, induction on the above path (no
  size component) exposes below; `piExposureRed_of_head_interfaces` assembles the two open
  interfaces into `PiExposureRedN`.

The second part of this file is this branch's own work. -/

namespace Lean4Lean.VEnv.StrengtheningReplay
open VExpr VEnv.StrengtheningTypingFront
variable {env : VEnv} {U k : Nat} {Γ Γ' : List VExpr} {A B F f Q T e : VExpr}

/-! ## The type front in `LiftN` form is `TypedFront` -/

theorem typeFrontN_of_typeFront (henv : env.WF) (H : TypeFront env) : TypeFrontN env := by
  intro U k Γ Γ' A B u v W
  induction W generalizing A B u v with
  | zero As hn =>
    cases As with
    | nil => simp at hn
    | cons Q As =>
      cases As with
      | nil => exact fun _ hΓ' hA hB hAB => H hΓ' hA hB hAB
      | cons => simp at hn
  | @succ k Γ Γ' D W ih =>
    intro hΓ hΓ' hA hB hAB
    obtain ⟨w, hD⟩ := hΓ.2
    have hD' := hD.weakN henv.ordered W
    have hAB' := hAB.of_l henv hΓ' (hA.weakN henv.ordered W.succ)
    have hPi : env.IsDefEqU U Γ' ((VExpr.forallE D A).liftN 1 k)
        ((VExpr.forallE D B).liftN 1 k) := ⟨_, .forallEDF hD' hAB'⟩
    have hd := ih hΓ.1 hΓ'.1 (.forallE hD hA) (.forallE hD hB) hPi
    obtain ⟨_, hb⟩ := (hd.forallE_inv henv hΓ.1).2
    exact ⟨_, hb⟩

theorem typeFrontN_iff_typeFront (henv : env.WF) : TypeFrontN env ↔ TypeFront env :=
  ⟨TypeFront.of_typeFrontN, typeFrontN_of_typeFront henv⟩

theorem typeFrontN_iff_typedFront (henv : env.WF) (heq : env.HasCanonicalEq) :
    TypeFrontN env ↔ StrengtheningKripke.TypedFront env :=
  (typeFrontN_iff_typeFront henv).trans (typeFront_iff_typedFront henv heq)

theorem piExposureRed_iff_piExposure (henv : env.WF) (heq : env.HasCanonicalEq) :
    PiExposureRedN henv ↔ PiExposureN env := by
  refine ⟨PiExposureN.of_red henv heq, ?_⟩
  intro H U k Γ Γ' f F u A B W hΓ hΓ' hf hF hr
  letI := henv.params U
  have hc : env.IsDefEqU U Γ' (F.liftN 1 k) (.forallE A B) :=
    ⟨_, hr.defeq hΓ' (hF.weakN henv.ordered W)⟩
  obtain ⟨A₀, B₀, hPi⟩ := H W hΓ hΓ' hf hc
  exact exposure_reduces henv heq hΓ hF hPi

/-- A term typed below at some `T` and above at the lift of a type `A` of `Γ` is typed below at
`A`: unique typing above gives `T↑ ≡ A↑`, the type front descends it. -/
theorem retyping_of_typeFrontN (henv : env.WF) (H : TypeFrontN env)
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (env.IsType U))
    (hΓ' : OnCtx Γ' (env.IsType U)) (he : env.HasType U Γ e T)
    (hA : env.HasType U Γ A (.sort u))
    (he' : env.HasType U Γ' (e.liftN 1 k) (A.liftN 1 k)) : env.HasType U Γ e A := by
  obtain ⟨v, hT⟩ := he.isType henv.ordered hΓ
  exact he.defeqU_r henv hΓ (H W hΓ hΓ' hT hA
    ((he.weakN henv.ordered W).uniqU henv hΓ' he'))

/-- Two terms typed below (at any types) whose lifts are convertible above are convertible
below: the types agree by unique typing and the type front, then `TypedFront` applies. -/
theorem typedFront_independent_endpoints (henv : env.WF)
    (H : StrengtheningKripke.TypedFront env) (hΓ' : OnCtx (Q :: Γ) (env.IsType U))
    (ha : env.HasType U Γ a A) (hb : env.HasType U Γ b B)
    (hab : env.IsDefEqU U (Q :: Γ) a.lift b.lift) : env.IsDefEqU U Γ a b := by
  have hTy := typeFront_of_typedFront henv H
  obtain ⟨u, hA⟩ := ha.isType henv.ordered hΓ'.1
  obtain ⟨v, hB⟩ := hb.isType henv.ordered hΓ'.1
  have he := hab.of_l henv hΓ' (ha.weak henv.ordered)
  have hAB := he.uniqU henv hΓ' (hb.weak henv.ordered)
  have hbA := hb.defeqU_r henv hΓ'.1 (hTy hΓ' hA hB hAB).symm
  exact ⟨_, H hΓ'.1 hΓ'.2 ha hbA he⟩

/-! ## The exact formulation -/

theorem cancel_iff_typedFront_and_closures (henv : env.WF) (heq : env.HasCanonicalEq) :
    Cancel env ↔ StrengtheningKripke.TypedFront env ∧ AppFrontN env ∧
      ProjFrontN env ∧ ElimFrontN env := by
  constructor
  · intro H
    have ht := typingFrontN_of_cancel henv H
    exact ⟨(typeFrontN_iff_typedFront henv heq).mp (TypeFrontN.of_typingFrontN henv ht),
      AppFrontN.of_typingFrontN ht, ProjFrontN.of_typingFrontN ht, ElimFrontN.of_typingFrontN ht⟩
  · rintro ⟨ht, ha, hp, he⟩
    exact (typingFrontN_iff_cancel henv heq).mp
      (typingFrontN_of_closures henv ha ((typeFrontN_iff_typedFront henv heq).mpr ht) hp he)

theorem cancel_of_typedFront_and_exposure (henv : env.WF) (heq : env.HasCanonicalEq)
    (ht : StrengtheningKripke.TypedFront env) (hPi : PiExposureN env)
    (hp : ProjFrontN env) (he : ElimFrontN env) : Cancel env := by
  have hTy := (typeFrontN_iff_typedFront henv heq).mpr ht
  exact (cancel_iff_typedFront_and_closures henv heq).mpr
    ⟨ht, AppFrontN.of_piExposure henv hPi hTy, hp, he⟩

/-! ## Standardisation, projections and the head fragment -/

section
open VEnv.Params
variable [VEnv.Params]

theorem core_exposure_standard (hΓ : OnCtx Γ (Params.env.IsType univs))
    (ht : Params.env.HasType univs Γ F (.sort u))
    (hr : ParRedS Γ F (.forallE A B)) :
    ∃ A₀ B₀, WHRedS Γ F (.forallE A₀ B₀) := by
  have hs := hr.standard hΓ ht
  cases hs with
  | forallE h _ _ => exact ⟨_, _, h⟩

theorem whnf_proj (family : Name) (i : Nat) (m : VExpr) : WHNF Γ (.proj family i m) := by
  intro out h
  cases h with
  | schema h =>
    obtain ⟨_, _, _, hh⟩ := h.head
    cases hh
  | extra hp hm _ =>
    obtain ⟨name, hh⟩ := (Params.constHeaded hp).matches_head hm
    cases hh

theorem projection_has_no_core_head_exposure (family : Name) (i : Nat) (m : VExpr) :
    ¬ ∃ A B, WHRedS Γ (.proj family i m) (.forallE A B) := by
  rintro ⟨A, B, hr⟩
  have hh := (whnf_proj family i m).whRedS hr
  cases hh

theorem projection_full_exposure (hp : Params.env.projections family info)
    (ht : Params.env.HasType univs Γ
      (.proj family i (mkApps (.const info.ctorName ls) args)) (.sort u))
    (hi : args[info.nparams + i]? = some (.forallE A B))
    (hPi : Params.env.HasType univs Γ (.forallE A B) (.sort u)) :
    FullReduction Γ (.proj family i (mkApps (.const info.ctorName ls) args)) (.forallE A B) ∧
      ¬ ∃ C D, WHRedS Γ (.proj family i (mkApps (.const info.ctorName ls) args)) (.forallE C D) :=
  ⟨.tail .rfl (.projIota hp ht hi hPi), projection_has_no_core_head_exposure _ _ _⟩

theorem type_not_function (hΓ : OnCtx Γ (Params.env.IsType univs))
    (ht : Params.env.HasType univs Γ F (.sort u)) :
    ¬ Params.env.HasType univs Γ F (.forallE A B) :=
  fun hf => IsDefEqU.sort_forallE_inv henv hΓ (ht.uniqU henv hΓ hf)

theorem type_not_structure (hΓ : OnCtx Γ (Params.env.IsType univs))
    (ht : Params.env.HasType univs Γ F (.sort u))
    (hi : Params.env.projections family info) :
    ¬ Params.env.HasType univs Γ F (mkApps (.const family ls) args) := by
  intro hs
  exact henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
    ((ht.uniqU henv hΓ hs).typeChain henv hΓ (.sort (ht.sort_r henv.ordered hΓ)))

/-- Projection iota replays from the typing of the projection alone. -/
theorem saturated_projection_replay (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hi : Params.env.projections family info)
    (ht : Params.env.HasType univs Γ
      (.proj family i (mkApps (.const info.ctorName ls) args)) T)
    (hlen : args.length = info.nparams + info.numFields)
    (hget : args[info.nparams + i]? = some field) :
    FullStep Γ (.proj family i (mkApps (.const info.ctorName ls) args)) field :=
  .projIota hi ht hget (HasType.projIota_field hΓ hi ht hlen hget)

/-- Astra's eta-free demanded-head fragment; not claimed complete for `FullReduction`. -/
inductive HeadStep (Γ : List VExpr) : VExpr → VExpr → Prop where
  | beta {A b a : VExpr} : HeadStep Γ (.app (.lam A b) a) (b.inst a)
  | extra {e : VExpr} : Pat p r → p.Matches e ls values →
      r.2.OK (Params.env.IsDefEqU univs Γ) ls values →
      HeadStep Γ e (r.1.apply ls values)
  | schema {e : VExpr} : CaseIota Params.env univs Γ e e' → HeadStep Γ e e'
  | delta : PrefixUnfold Params.env univs recursorData Γ c ls args rhs →
      HeadStep Γ (mkApps (.const c ls) args) rhs
  | quotDelta : QuotPrefixUnfold Params.env univs Γ ls args rhs →
      HeadStep Γ (mkApps (.const ``Quot.lift ls) args) rhs
  | projIota {T : VExpr} : Params.env.projections S info →
      Params.env.HasType univs Γ (.proj S i (mkApps (.const info.ctorName ls) args)) T →
      args[info.nparams + i]? = some field → Params.env.HasType univs Γ field T →
      HeadStep Γ (.proj S i (mkApps (.const info.ctorName ls) args)) field
  | app {f : VExpr} : HeadStep Γ f f' → HeadStep Γ (.app f a) (.app f' a)
  | major {f : VExpr} : IsMajorPremise f → HeadStep Γ a a' → HeadStep Γ (.app f a) (.app f a')
  | caseMajor {f : VExpr} : IsCaseMajorPremise Params.env f → HeadStep Γ a a' →
      HeadStep Γ (.app f a) (.app f a')
  | proj : HeadStep Γ m m' → HeadStep Γ (.proj S i m) (.proj S i m')

theorem HeadStep.full (H : HeadStep Γ e e') : FullStep Γ e e' := by
  induction H with
  | beta => exact .core (.beta .rfl .rfl)
  | extra hp hm hg => exact .core (.extra hp hm hg fun _ => .rfl)
  | schema h => exact .core (.of_schema h)
  | delta h => exact .delta h
  | quotDelta h => exact .quotDelta h
  | projIota hi ht hg hf => exact .projIota hi ht hg hf
  | app _ ih => exact .app ih .rfl
  | major _ _ ih | caseMajor _ _ ih => exact .app .rfl ih
  | proj _ ih => exact .proj ih

/-- OPEN (Astra's `HeadReplay`): the sufficient local replay interface for the head fragment.
A head step above on the lift of a term typed below is the lift of a full step below. -/
def LocalReplay : Prop :=
  ∀ ⦃k Γ Γ' e T out⦄, Ctx.LiftN 1 k Γ Γ' →
    OnCtx Γ (Params.env.IsType univs) → OnCtx Γ' (Params.env.IsType univs) →
    Params.env.HasType univs Γ e T → HeadStep Γ' (e.liftN 1 k) out →
    ∃ e', out = e'.liftN 1 k ∧ FullStep Γ e e'

/-- OPEN: the full-to-demanded-head exposure bridge for this fragment. -/
def HeadStandard : Prop :=
  ∀ ⦃Γ F u A B⦄, OnCtx Γ (Params.env.IsType univs) →
    Params.env.HasType univs Γ F (.sort u) → FullReduction Γ F (.forallE A B) →
    ∃ C D, ReflTransGen (HeadStep Γ) F (.forallE C D)

/-- Given local replay, induction on the above path (no size component) replays it below. -/
theorem head_path_replay (H : LocalReplay) (W : Ctx.LiftN 1 k Γ Γ')
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    (ht : Params.env.HasType univs Γ e T)
    (hr : ReflTransGen (HeadStep Γ') (e.liftN 1 k) out) :
    ∃ e', out = e'.liftN 1 k ∧ FullReduction Γ e e' := by
  generalize hs : e.liftN 1 k = source at hr
  induction hr using ReflTransGen.headIndOn generalizing e with
  | rfl => exact ⟨e, hs.symm, .rfl⟩
  | head step tail ih =>
    rw [← hs] at step
    obtain ⟨m, hm, hstep⟩ := H W hΓ hΓ' ht step
    obtain ⟨e', he', htail⟩ := ih (hstep.hasType hΓ ht) hm.symm
    exact ⟨e', he', (ReflTransGen.tail .rfl hstep).trans htail⟩

end

theorem piExposureRed_of_head_interfaces (henv : env.WF)
    (standard : ∀ U, @HeadStandard (henv.params U))
    (replay : ∀ U, @LocalReplay (henv.params U)) : PiExposureRedN henv := by
  intro U k Γ Γ' f F u A B W hΓ hΓ' _ hF hr
  letI := henv.params U
  obtain ⟨C, D, hh⟩ := standard U hΓ' (hF.weakN henv.ordered W) hr
  obtain ⟨F', he, hf⟩ := head_path_replay (replay U) W hΓ hΓ' hF hh
  cases F' <;> simp only [liftN] at he <;> cases he
  exact ⟨_, _, hf⟩

/-! ## Part 2: descent of eta-free parallel steps

This branch's own work. `TypedFrontN` is Kripke's
`TypedFront` along any single-binder insertion (equivalent under canonical `Eq`,
`typedFrontN_iff_typedFront`); `TypedFrontN.independent` descends a conversion between lifts of
two terms typed below at any types, `TypedFrontN.retype` retypes at the lift of a type below.

`ParRed.descend`: a parallel core step above (`ChurchRosser.ParRed`: beta, stored-rule
computation, case iota, congruences) on the lift of a term typed below is the lift of a parallel
core step below. Its guards: the stored-rule check (`Pattern.Check.OK`) compares captured
subterms only in every concrete pattern (`CheckVars`, `ConcretePattern.checkVars`), and those are
typed below (`Pattern.Matches.typed`), so the check descends by `TypedFrontN.independent`
(`Check.OK.descend`); the case guard `CaseRedex` is left as the obligation `CaseRedexDescends`.
`DeltaPar.descend`: a parallel delta step (`LevelledReduction.DeltaPar`: singleton and quotient
prefix unfolding, projection iota) descends given `UnfoldingCheckDescends`; generation commutes
with lifting (`singletonUnfolding_lift'`, `generate_rename`), so the unfolding check is the whole
guard; projection iota needs only retyping of the field at the projection's type. -/

variable {A B T : VExpr}


/-- Kripke's `TypedFront` along any single-binder insertion. -/
def TypedFrontN (env : VEnv) : Prop :=
  ∀ ⦃U k Γ Γ' a b T⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ a T → env.HasType U Γ b T →
    env.IsDefEqU U Γ' (a.liftN 1 k) (b.liftN 1 k) → env.IsDefEqU U Γ a b

theorem typedFrontN_of_typeFrontN (henv : env.WF) (heq : env.HasCanonicalEq)
    (H : TypeFrontN env) : TypedFrontN env := by
  intro U k Γ Γ' a b T W hΓ hΓ' ha hb hab
  obtain ⟨u, hT⟩ := ha.isType henv.ordered hΓ
  have hu := hT.sort_r henv.ordered hΓ
  have hab' := hab.of_l henv hΓ' (ha.weakN henv.ordered W)
  have e1 := IsDefEq.eqApp_r heq hu (hT.weakN henv.ordered W) (ha.weakN henv.ordered W) hab'
  have e2 : env.IsDefEqU U Γ' ((eqApp u T a a).liftN 1 k) ((eqApp u T a b).liftN 1 k) :=
    ⟨_, by simpa only [eqApp, liftN] using e1⟩
  have h := H W hΓ hΓ' (HasType.eqApp heq hu hT ha ha) (HasType.eqApp heq hu hT ha hb) e2
  exact eqApp_injective henv heq hΓ hT ha hu h

theorem typeFrontN_of_typedFrontN (henv : env.WF) (H : TypedFrontN env) : TypeFrontN env := by
  intro U k Γ Γ' A B u v W hΓ hΓ' hA hB hAB
  have hd := hAB.of_l henv hΓ' (hA.weakN henv.ordered W)
  have huv := (hd.uniqU henv hΓ' (hB.weakN henv.ordered W)).sort_inv henv hΓ'
  have hBu : env.HasType U Γ B (.sort u) :=
    (IsDefEq.sortDF (hB.sort_r henv.ordered hΓ) (hA.sort_r henv.ordered hΓ) huv.symm).defeq hB
  exact H W hΓ hΓ' hA hBu hAB

theorem typedFrontN_iff_typedFront (henv : env.WF) (heq : env.HasCanonicalEq) :
    TypedFrontN env ↔ StrengtheningKripke.TypedFront env :=
  ⟨fun H => (typeFrontN_iff_typedFront henv heq).mp (typeFrontN_of_typedFrontN henv H),
    fun H => typedFrontN_of_typeFrontN henv heq ((typeFrontN_iff_typedFront henv heq).mpr H)⟩

/-- Two terms typed below at any types whose lifts are convertible above are convertible
below (along any single-binder insertion). -/
theorem TypedFrontN.independent (henv : env.WF) (H : TypedFrontN env)
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    (ha : env.HasType U Γ a A) (hb : env.HasType U Γ b B)
    (hab : env.IsDefEqU U Γ' (a.liftN 1 k) (b.liftN 1 k)) : env.IsDefEqU U Γ a b := by
  have hTy := typeFrontN_of_typedFrontN henv H
  obtain ⟨u, hA⟩ := ha.isType henv.ordered hΓ
  obtain ⟨v, hB⟩ := hb.isType henv.ordered hΓ
  have he := hab.of_l henv hΓ' (ha.weakN henv.ordered W)
  have hAB := he.uniqU henv hΓ' (hb.weakN henv.ordered W)
  have hbA := hb.defeqU_r henv hΓ (hTy W hΓ hΓ' hA hB hAB).symm
  exact H W hΓ hΓ' ha hbA hab

/-- Retyping at the lift of a type below, from `TypedFrontN`. -/
theorem TypedFrontN.retype (henv : env.WF) (H : TypedFrontN env)
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    (he : env.HasType U Γ e T) (hA : env.HasType U Γ A (.sort u))
    (he' : env.HasType U Γ' (e.liftN 1 k) (A.liftN 1 k)) : env.HasType U Γ e A :=
  retyping_of_typeFrontN henv (typeFrontN_of_typedFrontN henv H) W hΓ hΓ' he hA he'

/-! ## Syntactic inversion of lifts -/

theorem liftN_eq_app_inv {e f a : VExpr} (h : e.liftN 1 k = .app f a) :
    ∃ f₀ a₀, e = .app f₀ a₀ ∧ f = f₀.liftN 1 k ∧ a = a₀.liftN 1 k := by
  cases e <;> simp only [liftN] at h <;> cases h
  exact ⟨_, _, rfl, rfl, rfl⟩

theorem liftN_eq_lam_inv {e A b : VExpr} (h : e.liftN 1 k = .lam A b) :
    ∃ A₀ b₀, e = .lam A₀ b₀ ∧ A = A₀.liftN 1 k ∧ b = b₀.liftN 1 (k+1) := by
  cases e <;> simp only [liftN] at h <;> cases h
  exact ⟨_, _, rfl, rfl, rfl⟩

theorem liftN_eq_forallE_inv {e A b : VExpr} (h : e.liftN 1 k = .forallE A b) :
    ∃ A₀ b₀, e = .forallE A₀ b₀ ∧ A = A₀.liftN 1 k ∧ b = b₀.liftN 1 (k+1) := by
  cases e <;> simp only [liftN] at h <;> cases h
  exact ⟨_, _, rfl, rfl, rfl⟩

theorem liftN_eq_proj_inv {e m : VExpr} {S : Name} {i : Nat}
    (h : e.liftN 1 k = .proj S i m) :
    ∃ m₀, e = .proj S i m₀ ∧ m = m₀.liftN 1 k := by
  cases e <;> simp only [liftN] at h <;> cases h
  exact ⟨_, rfl, rfl⟩

theorem liftN_eq_const_inv {e : VExpr} {c : Name} {ls : List VLevel}
    (h : e.liftN 1 k = .const c ls) : e = .const c ls := by
  cases e <;> simp only [liftN] at h <;> cases h; rfl

theorem liftN_eq_elim_inv {e : VExpr} {b : Name} {o : Nat} {ls : List VLevel}
    (h : e.liftN 1 k = .elim b o ls) : e = .elim b o ls := by
  cases e <;> simp only [liftN] at h <;> cases h; rfl

/-- A spine that is a lift is the lift of a spine. -/
theorem liftN_eq_mkApps_inv {e f : VExpr} :
    ∀ {args : List VExpr}, e.liftN 1 k = mkApps f args →
      ∃ f₀ args₀, e = mkApps f₀ args₀ ∧ f = f₀.liftN 1 k ∧ args = args₀.map (·.liftN 1 k) := by
  intro args
  induction args generalizing e f with
  | nil => intro h; exact ⟨e, [], rfl, h.symm, rfl⟩
  | cons a args ih =>
    intro h
    simp only [mkApps, List.foldl_cons] at h
    obtain ⟨g₀, args₀, rfl, hg, rfl⟩ := ih h
    obtain ⟨f₀, a₀, rfl, rfl, rfl⟩ := liftN_eq_app_inv hg.symm
    exact ⟨f₀, a₀ :: args₀, rfl, rfl, rfl⟩

theorem liftN_eq_mkApps_const_inv {e : VExpr} {c : Name} {ls : List VLevel} {args : List VExpr}
    (h : e.liftN 1 k = mkApps (.const c ls) args) :
    ∃ args₀, e = mkApps (.const c ls) args₀ ∧ args = args₀.map (·.liftN 1 k) := by
  obtain ⟨f₀, args₀, rfl, hf, rfl⟩ := liftN_eq_mkApps_inv h
  exact ⟨args₀, by rw [liftN_eq_const_inv hf.symm], rfl⟩

theorem liftN_eq_mkApps_elim_inv {e : VExpr} {b : Name} {o : Nat} {ls : List VLevel}
    {args : List VExpr} (h : e.liftN 1 k = mkApps (.elim b o ls) args) :
    ∃ args₀, e = mkApps (.elim b o ls) args₀ ∧ args = args₀.map (·.liftN 1 k) := by
  obtain ⟨f₀, args₀, rfl, hf, rfl⟩ := liftN_eq_mkApps_inv h
  exact ⟨args₀, by rw [liftN_eq_elim_inv hf.symm], rfl⟩

/-! ## Matched subterms of a typed term are typed -/

theorem _root_.Lean4Lean.Pattern.Matches.typed (henv : env.Ordered)
    (hΓ : OnCtx Γ (env.IsType U)) {p : Pattern} {e : VExpr} {m1 : List VLevel}
    {m2 : p.Path → VExpr} (hm : p.Matches e m1 m2) (he : env.HasType U Γ e T) :
    ∀ x, ∃ A, env.HasType U Γ (m2 x) A := by
  induction hm generalizing T with
  | const | elim => intro x; cases x
  | var _ ih =>
    obtain ⟨A, B, hf, ha⟩ := he.app_inv henv hΓ
    intro x
    cases x with
    | none => exact ⟨_, ha⟩
    | some x => exact ih hf x
  | app _ _ ih1 ih2 =>
    obtain ⟨A, B, hf, ha⟩ := he.app_inv henv hΓ
    intro x
    cases x with
    | inl x => exact ih1 hf x
    | inr x => exact ih2 ha x


/-! ## Pointwise descent of lists -/

theorem list_descend {R : VExpr → VExpr → Prop} :
    ∀ {l l₀ : List VExpr}, l.length = l₀.length →
      (∀ i (hi : i < l.length) (hi' : i < l₀.length), ∃ b, l[i] = b.liftN 1 k ∧ R l₀[i] b) →
      ∃ l₀' : List VExpr, l = l₀'.map (·.liftN 1 k) ∧ l₀'.length = l₀.length ∧
        ∀ i (hi : i < l₀.length) (hi' : i < l₀'.length), R l₀[i] l₀'[i] := by
  intro l l₀
  induction l₀ generalizing l with
  | nil =>
    intro hlen _
    cases l with
    | nil => exact ⟨[], rfl, rfl, fun i hi => by cases hi⟩
    | cons => simp at hlen
  | cons a₀ l₀ ih =>
    intro hlen h
    cases l with
    | nil => simp at hlen
    | cons a l =>
      obtain ⟨b, hb, hR⟩ := h 0 (by simp) (by simp)
      obtain ⟨l₀', rfl, hl, hrest⟩ := ih (by simpa using hlen) fun i hi hi' =>
        h (i+1) (by simpa using hi) (by simpa using hi')
      have hb' : a = b.liftN 1 k := by simpa using hb
      refine ⟨b :: l₀', by simp [hb'], by simp [hl], ?_⟩
      intro i hi hi'
      cases i with
      | zero => exact hR
      | succ i => exact hrest i (by simpa using hi) (by simpa using hi')

section Descent
open VEnv.Params
variable [VEnv.Params]

/-- Checks whose conversion nodes compare captured subterms only (every concrete check). -/
def CheckVars {p : Pattern} : p.Check → Prop
  | .true => True
  | .nonzero _ rest => CheckVars rest
  | .defeq (.var _) (.var _) rest => CheckVars rest
  | .defeq _ _ _ => False

omit [VEnv.Params] in
theorem ConcretePattern.checkVars {registry : HeadRegistry.Registry} {E : VEnv} {p : Pattern}
    {r : p.RHS × p.Check} (H : ConcretePattern registry E p r) : CheckVars r.2 := by
  rcases H with H | ⟨_, H⟩ | H
  · cases H; trivial
  · cases H; trivial
  · cases H
    simp only [InductiveSignature.RecursorData.ruleCheck]
    split <;> trivial

omit [VEnv.Params] in
theorem Params.checkVars {env : VEnv} (henv : env.WF) (U : Nat) {p : Pattern} {r : p.RHS × p.Check}
    (H : @Params.Pat (henv.params U) p r) : CheckVars r.2 :=
  ConcretePattern.checkVars H

/-- A guard on lifted captured subterms, all typed below, descends. -/
theorem Check.OK.descend (hTF : TypedFrontN Params.env) (W : Ctx.LiftN 1 k Γ Γ')
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    {p : Pattern} {m1 : List VLevel} {m2 : p.Path → VExpr}
    (hty : ∀ x, ∃ A, Params.env.HasType univs Γ (m2 x) A) :
    ∀ {ck : p.Check}, CheckVars ck →
      ck.OK (Params.env.IsDefEqU univs Γ') m1 (fun x => (m2 x).liftN 1 k) →
      ck.OK (Params.env.IsDefEqU univs Γ) m1 m2 := by
  intro ck
  induction ck with
  | true => intros; trivial
  | nonzero level rest ih => intro hcv H; exact ⟨H.1, ih hcv H.2⟩
  | defeq x y rest ih =>
    intro hcv H
    cases x with
    | var x =>
      cases y with
      | var y =>
        obtain ⟨_, hx⟩ := hty x
        obtain ⟨_, hy⟩ := hty y
        exact ⟨hTF.independent henv W hΓ hΓ' hx hy H.1, ih hcv H.2⟩
      | _ => exact hcv.elim
    | _ => exact hcv.elim

/-- OPEN: the case-iota guard (`CaseRedex`: the typed case computation of its captures and the
alignment conversion) descends from lifted data. -/
def CaseRedexDescends : Prop :=
  ∀ ⦃k Γ Γ' rule actual T⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (Params.env.IsType univs) →
    OnCtx Γ' (Params.env.IsType univs) →
    Params.env.HasType univs Γ (InductiveSignature.CaseSchema.Application.expr actual) T →
    CaseRedex Params.env univs Γ' rule (CaseApplicationMap actual fun e => e.liftN 1 k) →
    CaseRedex Params.env univs Γ rule actual

omit [VEnv.Params] in
theorem case_application_liftN_inv {actual : InductiveSignature.CaseSchema.Application} {e : VExpr}
    (h : e.liftN 1 k = actual.expr) :
    ∃ actual₀, e = actual₀.expr ∧ actual = CaseApplicationMap actual₀ fun e => e.liftN 1 k := by
  obtain ⟨block, owner, levels, args, ctor, ctorLevels, ctorArgs⟩ := actual
  simp only [InductiveSignature.CaseSchema.Application.expr] at h
  obtain ⟨f₀, a₀, rfl, hf, ha⟩ := liftN_eq_app_inv h
  obtain ⟨args₀, rfl, rfl⟩ := liftN_eq_mkApps_elim_inv hf.symm
  obtain ⟨ctorArgs₀, rfl, rfl⟩ := liftN_eq_mkApps_const_inv ha.symm
  exact ⟨⟨block, owner, levels, args₀, ctor, ctorLevels, ctorArgs₀⟩, rfl, rfl⟩

/-- Descent of a parallel core step above on the lift of a term typed below, given the case
guard descends. Every guard is a `TypedFrontN` instance (`Check.OK.descend`) or is syntactic. -/
theorem ParRed.descend (hTF : TypedFrontN Params.env) (hcase : CaseRedexDescends)
    (hcv : ∀ {p : Pattern} {r : p.RHS × p.Check}, Pat p r → CheckVars r.2)
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    (he : Params.env.HasType univs Γ e T) (H : ParRed Γ' (e.liftN 1 k) out) :
    ∃ e', out = e'.liftN 1 k ∧ ParRed Γ e e' := by
  generalize hs : e.liftN 1 k = src at H
  induction H generalizing e T k Γ with
  | @schema Γ' args rule actual hm hl hr ih =>
    obtain ⟨actual₀, rfl, rfl⟩ := case_application_liftN_inv hs
    have hm₀ := hcase W hΓ hΓ' he hm
    have hc : (rule.body.rhs.instL actual₀.levels).ClosedN args.length := by
      simpa [hl, case_capture_map] using hm.source.closed.2.1.instL
    obtain ⟨args₀, rfl, hlen₀, hred₀⟩ := list_descend (R := ParRed Γ)
      (l := args) (l₀ := rule.capture actual₀) (by simpa [case_capture_map] using hl) (by
        intro i hi hi'
        obtain ⟨A, hA⟩ := hm₀.source.arguments_typed (List.getElem_mem hi')
        have hi'' : i < (rule.capture (CaseApplicationMap actual₀ fun e => e.liftN 1 k)).length := by
          simpa [case_capture_map] using hi'
        have := ih i hi'' W hΓ hΓ' hA (by simp [case_capture_map])
        simpa using this)
    refine ⟨rule.rhs actual₀.levels args₀, ?_,
      .schema hm₀ (by simpa using hlen₀) (fun i hi => hred₀ i hi (by omega))⟩
    simp only [case_application_map_levels, InductiveSignature.CaseSchema.AppliedRule.rhs]
    rw [instantiateParams_liftN (by simpa using hc)]
  | bvar | sort | const | elim => exact ⟨e, hs.symm, .rfl⟩
  | app _ _ ih1 ih2 =>
    obtain ⟨f₀, a₀, rfl, rfl, rfl⟩ := liftN_eq_app_inv hs
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv.ordered hΓ
    obtain ⟨f', rfl, hf'⟩ := ih1 W hΓ hΓ' hf rfl
    obtain ⟨a', rfl, ha'⟩ := ih2 W hΓ hΓ' ha rfl
    exact ⟨.app f' a', rfl, .app hf' ha'⟩
  | proj _ ih =>
    obtain ⟨m₀, rfl, rfl⟩ := liftN_eq_proj_inv hs
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv.ordered hΓ
    obtain ⟨m', rfl, hm'⟩ := ih W hΓ hΓ' hm.hasType.2 rfl
    exact ⟨.proj _ _ m', rfl, .proj hm'⟩
  | lam _ _ ih1 ih2 =>
    obtain ⟨A₀, b₀, rfl, rfl, rfl⟩ := liftN_eq_lam_inv hs
    obtain ⟨⟨u, hA⟩, _, hb⟩ := he.lam_inv henv.ordered hΓ
    obtain ⟨A', rfl, hA'⟩ := ih1 W hΓ hΓ' hA rfl
    obtain ⟨b', rfl, hb'⟩ := ih2 W.succ ⟨hΓ, u, hA⟩ ⟨hΓ', u, hA.weakN henv.ordered W⟩ hb rfl
    exact ⟨.lam A' b', rfl, .lam hA' hb'⟩
  | forallE _ _ ih1 ih2 =>
    obtain ⟨A₀, b₀, rfl, rfl, rfl⟩ := liftN_eq_forallE_inv hs
    obtain ⟨⟨u, hA⟩, _, hb⟩ := he.forallE_inv henv.ordered
    obtain ⟨A', rfl, hA'⟩ := ih1 W hΓ hΓ' hA rfl
    obtain ⟨b', rfl, hb'⟩ := ih2 W.succ ⟨hΓ, u, hA⟩ ⟨hΓ', u, hA.weakN henv.ordered W⟩ hb rfl
    exact ⟨.forallE A' b', rfl, .forallE hA' hb'⟩
  | beta _ _ ih1 ih2 =>
    obtain ⟨f₀, a₀, rfl, hf, rfl⟩ := liftN_eq_app_inv hs
    obtain ⟨A₀, b₀, rfl, rfl, rfl⟩ := liftN_eq_lam_inv hf.symm
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv.ordered hΓ
    obtain ⟨⟨u, hA⟩, _, hb⟩ := hf.lam_inv henv.ordered hΓ
    obtain ⟨b', rfl, hb'⟩ := ih1 W.succ ⟨hΓ, u, hA⟩ ⟨hΓ', u, hA.weakN henv.ordered W⟩ hb rfl
    obtain ⟨a', rfl, ha'⟩ := ih2 W hΓ hΓ' ha rfl
    exact ⟨b'.inst a', (liftN_inst_hi b' a' 1 k).symm, .beta hb' ha'⟩
  | extra hp hm hok hred ih =>
    rename_i p r m1 m2 Γ₁ m2'
    subst hs
    obtain ⟨m2₀, hm₀, hm2⟩ := Pattern.matches_liftN.1 hm
    have hty := hm₀.typed henv.ordered hΓ he
    have hdesc : ∀ x, ∃ b, m2' x = b.liftN 1 k ∧ ParRed Γ (m2₀ x) b := by
      intro x
      obtain ⟨A, hA⟩ := hty x
      exact ih x W hΓ hΓ' hA (hm2 x).symm
    let m2₀' := fun x => Classical.choose (hdesc x)
    have hm2' : ∀ x, _ = (m2₀' x).liftN 1 k := fun x => (Classical.choose_spec (hdesc x)).1
    have hred₀ : ∀ x, ParRed Γ (m2₀ x) (m2₀' x) := fun x => (Classical.choose_spec (hdesc x)).2
    have hm2f : _ = fun x => (m2₀ x).liftN 1 k := funext hm2
    subst hm2f
    have hok₀ := Check.OK.descend hTF W hΓ hΓ' hty (hcv hp) hok
    refine ⟨_, ?_, .extra hp hm₀ hok₀ hred₀⟩
    rw [Pattern.RHS.liftN_apply]
    congr 1
    exact funext hm2'


/-! ## Descent of prefix unfolding -/

/-- OPEN: the unfolding check (`UnfoldingCheck`: typed captures, the major proposition and the
spine alignment) descends from lifted data to the source typed below. -/
def UnfoldingCheckDescends : Prop :=
  ∀ ⦃k Γ Γ' source T⦄ ⦃program : InductiveSignature.RecursorData.PrefixUnfolding⦄,
    Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (Params.env.IsType univs) → OnCtx Γ' (Params.env.IsType univs) →
    Params.env.HasType univs Γ source T →
    UnfoldingCheck Params.env univs Γ' (source.liftN 1 k)
      (program.rename ((Lift.refl.skipN 1).consN k)) →
    UnfoldingCheck Params.env univs Γ source program

omit [VEnv.Params] in
theorem map_liftN_eq_lift' (args : List VExpr) :
    args.map (·.liftN 1 k) = args.map (·.lift' ((Lift.refl.skipN 1).consN k)) := by
  apply List.map_congr_left
  intro a _
  exact lift'_consN_skipN.symm

theorem PrefixUnfold.descend (hunfold : UnfoldingCheckDescends) (W : Ctx.LiftN 1 k Γ Γ')
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    {name : Name} {levels : List VLevel} {args : List VExpr}
    (he : Params.env.HasType univs Γ (mkApps (.const name levels) args) T)
    (H : PrefixUnfold Params.env univs recursorData Γ' name levels (args.map (·.liftN 1 k)) rhs) :
    ∃ rhs₀, rhs = rhs₀.liftN 1 k ∧ PrefixUnfold Params.env univs recursorData Γ name levels args rhs₀ := by
  cases H with
  | @intro data program hl hr hn ht hw hz hg replay =>
    obtain ⟨program₀, hg₀⟩ :=
      InductiveSignature.RecursorData.singletonUnfolding_sameArity (args' := args) hg (by simp)
    obtain ⟨type, htype⟩ := hr.recursorType_exists
    have hg₁ := InductiveSignature.RecursorData.singletonUnfolding_lift'
      (ρ := (Lift.refl.skipN 1).consN k) henv hr ht hz htype (hr.recursorType_closed henv htype) hg₀
    rw [← map_liftN_eq_lift'] at hg₁
    cases InductiveSignature.RecursorData.singletonUnfolding_unique hg hg₁
    have hsrc : mkApps (.const name levels) (args.map (·.liftN 1 k)) =
        (mkApps (.const name levels) args).liftN 1 k := by rw [liftN_mkApps]; rfl
    rw [hsrc] at replay
    have replay₀ := hunfold W hΓ hΓ' he replay
    refine ⟨program₀.rhs, ?_, .intro hl hr hn ht hw hz hg₀ replay₀⟩
    rw [InductiveSignature.RecursorData.PrefixUnfolding.rename_rhs (replay₀.templateScope henv).2.1,
      lift'_consN_skipN]

theorem QuotPrefixUnfold.descend (hunfold : UnfoldingCheckDescends) (W : Ctx.LiftN 1 k Γ Γ')
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    {levels : List VLevel} {args : List VExpr}
    (he : Params.env.HasType univs Γ (mkApps (.const ``Quot.lift levels) args) T)
    (H : QuotPrefixUnfold Params.env univs Γ' levels (args.map (·.liftN 1 k)) rhs) :
    ∃ rhs₀, rhs = rhs₀.liftN 1 k ∧ QuotPrefixUnfold Params.env univs Γ levels args rhs₀ := by
  cases H with
  | @intro program hr hw hz hg replay =>
    have hg₀ := QuotPrefixUnfolding.generate_inst (arg := .sort .zero) (k := k) hg
    have hargs : (args.map (·.liftN 1 k)).map (·.inst (.sort .zero) k) = args := by
      simp [List.map_map, Function.comp_def, inst_liftN]
    rw [hargs] at hg₀
    have hg₁ := QuotPrefixUnfolding.generate_rename (ρ := (Lift.refl.skipN 1).consN k) hg₀
    rw [← map_liftN_eq_lift'] at hg₁
    have hpe := QuotPrefixUnfolding.generate_unique hg hg₁
    have hsrc : mkApps (.const ``Quot.lift levels) (args.map (·.liftN 1 k)) =
        (mkApps (.const ``Quot.lift levels) args).liftN 1 k := by rw [liftN_mkApps]; rfl
    rw [hsrc, hpe] at replay
    have replay₀ := hunfold W hΓ hΓ' he replay
    refine ⟨_, ?_, .intro hr hw hz hg₀ replay₀⟩
    calc program.rhs
        = ((program.instN (.sort .zero) k).rename ((Lift.refl.skipN 1).consN k)).rhs := by rw [← hpe]
      _ = _ := by
        rw [InductiveSignature.RecursorData.PrefixUnfolding.rename_rhs
          (replay₀.templateScope henv).2.1, lift'_consN_skipN]

omit [VEnv.Params] in
theorem forall₂_of_pointwise {R : VExpr → VExpr → Prop} {l l' : List VExpr}
    (hlen : l'.length = l.length)
    (h : ∀ i (hi : i < l.length) (hi' : i < l'.length), R l[i] l'[i]) : List.Forall₂ R l l' := by
  induction l generalizing l' with
  | nil => cases l' with
    | nil => exact .nil
    | cons => simp at hlen
  | cons a l ih =>
    cases l' with
    | nil => simp at hlen
    | cons b l' =>
      exact .cons (h 0 (by simp) (by simp))
        (ih (by simpa using hlen) fun i hi hi' => h (i+1) (by simpa using hi) (by simpa using hi'))

/-- Descent of a parallel delta step (prefix unfolding and projection iota) above on the lift of
a term typed below, given the unfolding check descends. Projection iota needs only retyping. -/
theorem DeltaPar.descend (hTF : TypedFrontN Params.env) (hunfold : UnfoldingCheckDescends)
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs))
    (he : Params.env.HasType univs Γ e T) (H : DeltaPar Γ' (e.liftN 1 k) out) :
    ∃ e', out = e'.liftN 1 k ∧ DeltaPar Γ e e' := by
  generalize hs : e.liftN 1 k = src at H
  induction H generalizing e T k Γ with
  | bvar | sort | const | elim => exact ⟨e, hs.symm, .rfl⟩
  | app _ _ ih1 ih2 =>
    obtain ⟨f₀, a₀, rfl, rfl, rfl⟩ := liftN_eq_app_inv hs
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv.ordered hΓ
    obtain ⟨f', rfl, hf'⟩ := ih1 W hΓ hΓ' hf rfl
    obtain ⟨a', rfl, ha'⟩ := ih2 W hΓ hΓ' ha rfl
    exact ⟨.app f' a', rfl, .app hf' ha'⟩
  | proj _ ih =>
    obtain ⟨m₀, rfl, rfl⟩ := liftN_eq_proj_inv hs
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv.ordered hΓ
    obtain ⟨m', rfl, hm'⟩ := ih W hΓ hΓ' hm.hasType.2 rfl
    exact ⟨.proj _ _ m', rfl, .proj hm'⟩
  | lam _ _ ih1 ih2 =>
    obtain ⟨A₀, b₀, rfl, rfl, rfl⟩ := liftN_eq_lam_inv hs
    obtain ⟨⟨u, hA⟩, _, hb⟩ := he.lam_inv henv.ordered hΓ
    obtain ⟨A', rfl, hA'⟩ := ih1 W hΓ hΓ' hA rfl
    obtain ⟨b', rfl, hb'⟩ := ih2 W.succ ⟨hΓ, u, hA⟩ ⟨hΓ', u, hA.weakN henv.ordered W⟩ hb rfl
    exact ⟨.lam A' b', rfl, .lam hA' hb'⟩
  | forallE _ _ ih1 ih2 =>
    obtain ⟨A₀, b₀, rfl, rfl, rfl⟩ := liftN_eq_forallE_inv hs
    obtain ⟨⟨u, hA⟩, _, hb⟩ := he.forallE_inv henv.ordered
    obtain ⟨A', rfl, hA'⟩ := ih1 W hΓ hΓ' hA rfl
    obtain ⟨b', rfl, hb'⟩ := ih2 W.succ ⟨hΓ, u, hA⟩ ⟨hΓ', u, hA.weakN henv.ordered W⟩ hb rfl
    exact ⟨.forallE A' b', rfl, .forallE hA' hb'⟩
  | @delta Γ₁ name levels rhs args args' hlen hargs hunf ih =>
    obtain ⟨args₀, rfl, rfl⟩ := liftN_eq_mkApps_const_inv hs
    have hwf := VExpr.WF.args_of_mkApps henv.ordered hΓ ⟨_, he⟩
    obtain ⟨args₀', rfl, hlen₀, hred₀⟩ := list_descend (R := DeltaPar Γ) (l := args') (l₀ := args₀)
      (by simpa using hlen.symm) (by
        intro i hi hi'
        obtain ⟨A, hA⟩ := hwf _ (List.getElem_mem hi')
        exact ih i (by simpa using hi') hi W hΓ hΓ' hA (by simp))
    have hfr : List.Forall₂ (FullReduction Γ) args₀ args₀' :=
      forall₂_of_pointwise hlen₀ fun i hi hi' => (hred₀ i hi hi').full
    have he' := (FullReduction.mkApps .rfl hfr).hasType hΓ he
    obtain ⟨rhs₀, rfl, hunf₀⟩ := PrefixUnfold.descend hunfold W hΓ hΓ' he' hunf
    exact ⟨rhs₀, rfl, .delta hlen₀.symm (fun i hi hi' => hred₀ i hi hi') hunf₀⟩
  | @quotDelta Γ₁ levels rhs args args' hlen hargs hunf ih =>
    obtain ⟨args₀, rfl, rfl⟩ := liftN_eq_mkApps_const_inv hs
    have hwf := VExpr.WF.args_of_mkApps henv.ordered hΓ ⟨_, he⟩
    obtain ⟨args₀', rfl, hlen₀, hred₀⟩ := list_descend (R := DeltaPar Γ) (l := args') (l₀ := args₀)
      (by simpa using hlen.symm) (by
        intro i hi hi'
        obtain ⟨A, hA⟩ := hwf _ (List.getElem_mem hi')
        exact ih i (by simpa using hi') hi W hΓ hΓ' hA (by simp))
    have hfr : List.Forall₂ (FullReduction Γ) args₀ args₀' :=
      forall₂_of_pointwise hlen₀ fun i hi hi' => (hred₀ i hi hi').full
    have he' := (FullReduction.mkApps .rfl hfr).hasType hΓ he
    obtain ⟨rhs₀, rfl, hunf₀⟩ := QuotPrefixUnfold.descend hunfold W hΓ hΓ' he' hunf
    exact ⟨rhs₀, rfl, .quotDelta hlen₀.symm (fun i hi hi' => hred₀ i hi hi') hunf₀⟩
  | @projIota Γ₁ family info index levels fieldType field args args' hlen hargs hi hs' hget hfield ih =>
    obtain ⟨m₀, rfl, hm⟩ := liftN_eq_proj_inv hs
    obtain ⟨args₀, rfl, rfl⟩ := liftN_eq_mkApps_const_inv hm.symm
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ := he.proj_inv henv.ordered hΓ
    have hwf := VExpr.WF.args_of_mkApps henv.ordered hΓ ⟨_, hmajor.hasType.2⟩
    obtain ⟨args₀', rfl, hlen₀, hred₀⟩ := list_descend (R := DeltaPar Γ) (l := args') (l₀ := args₀)
      (by simpa using hlen.symm) (by
        intro i hi hi'
        obtain ⟨A, hA⟩ := hwf _ (List.getElem_mem hi')
        exact ih i (by simpa using hi') hi W hΓ hΓ' hA (by simp))
    have hfr : List.Forall₂ (FullReduction Γ) args₀ args₀' :=
      forall₂_of_pointwise hlen₀ fun i hi hi' => (hred₀ i hi hi').full
    have he' := (FullReduction.proj (FullReduction.mkApps .rfl hfr)).hasType hΓ he
    obtain ⟨field₀, hget₀, rfl⟩ : ∃ field₀, args₀'[info.nparams + index]? = some field₀ ∧
        field = field₀.liftN 1 k := by
      rw [List.getElem?_map] at hget
      cases h : args₀'[info.nparams + index]? with
      | none => rw [h] at hget; cases hget
      | some f => rw [h] at hget; exact ⟨f, rfl, (Option.some.inj hget).symm⟩
    have hmajor' := (FullReduction.mkApps .rfl hfr).hasType hΓ hmajor.hasType.2
    obtain ⟨_, hf₀⟩ := VExpr.WF.args_of_mkApps henv.ordered hΓ ⟨_, hmajor'⟩ _
      (List.mem_of_getElem? hget₀)
    obtain ⟨u, hT⟩ := he.isType henv.ordered hΓ
    have hs'' : Params.env.HasType univs Γ₁
        ((VExpr.proj family index (mkApps (.const info.ctorName levels) args₀')).liftN 1 k)
        (T.liftN 1 k) := he'.weakN henv.ordered W
    simp only [liftN, liftN_mkApps] at hs''
    have hfield' : Params.env.HasType univs Γ₁ (field₀.liftN 1 k) (T.liftN 1 k) :=
      hfield.defeqU_r henv hΓ' (hs'.uniqU henv hΓ' hs'')
    have hfieldT := hTF.retype henv W hΓ hΓ' hf₀ hT hfield'
    exact ⟨field₀, rfl, .projIota hlen₀.symm (fun i hi hi' => hred₀ i hi hi') hi he' hget₀ hfieldT⟩

end Descent

/-! ### The alignment guards of the unfolding check are `TypedFront` instances -/


/-- The spine alignment guard of a prefix unfolding (`UnfoldingCheck.recursor_lhs`, a
`ConstSpineDefEq`: pairwise conversions between the arguments of two constant spines, the
K-alignment of the actual indices with the reconstructed constructor's indices) descends from
lifted spines whenever every argument of both spines is typed below: each pair is a
`TypedFrontN.independent` instance. Level data are context-free. -/
theorem ConstSpineDefEq.descend (henv : env.WF) (hTF : TypedFrontN env)
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    {c : Name} {ls ls' : List VLevel} {as as' : List VExpr}
    (has : ∀ a ∈ as, VExpr.WF env U Γ a) (has' : ∀ a ∈ as', VExpr.WF env U Γ a)
    (H : ConstSpineDefEq env U Γ' (mkApps (.const c ls) (as.map (·.liftN 1 k)))
      (mkApps (.const c ls') (as'.map (·.liftN 1 k)))) :
    ConstSpineDefEq env U Γ (mkApps (.const c ls) as) (mkApps (.const c ls') as') := by
  obtain ⟨name, levels, levels', args, args', h1, h2, hw, hw', hl, hargs⟩ := H
  obtain ⟨rfl, rfl, rfl⟩ := VExpr.mkApps_const_inj h1
  obtain ⟨-, rfl, rfl⟩ := VExpr.mkApps_const_inj h2
  refine ⟨c, ls, ls', as, as', rfl, rfl, hw, hw', hl, ?_⟩
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff] at hargs
  have hlen := Lean4Lean.List.Forall₂.length_eq hargs
  refine List.forall₂_of_getElem hlen fun i hi hi' => ?_
  obtain ⟨_, ha⟩ := has _ (List.getElem_mem hi)
  obtain ⟨_, ha'⟩ := has' _ (List.getElem_mem hi')
  exact hTF.independent henv W hΓ hΓ' ha ha' (List.forall₂_getElem hargs i hi hi')

/-- The major-proposition guard of a prefix unfolding (`UnfoldingCheck.major_prop`) descends:
the major variable's type is a type below, its `Prop`-sort is context-free (`sort_inv`), and
the reconstructed constructor is retyped at it by `TypedFrontN.retype` once it is typed below
at some type. -/
theorem majorProp_descend (henv : env.WF) (hTF : TypedFrontN env)
    (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    {D c C : VExpr} (hD : env.HasType U Γ D (.sort u)) (hc : env.HasType U Γ c C)
    (hvar : env.HasType U Γ (.bvar 0) D)
    (H : ∃ majorType, env.HasType U Γ' majorType (.sort .zero) ∧
      env.HasType U Γ' (.bvar 0) majorType ∧ env.HasType U Γ' (c.liftN 1 k) majorType)
    (hvar' : env.HasType U Γ' (.bvar 0) (D.liftN 1 k)) :
    ∃ majorType, env.HasType U Γ majorType (.sort .zero) ∧
      env.HasType U Γ (.bvar 0) majorType ∧ env.HasType U Γ c majorType := by
  obtain ⟨M, hM, hv, hc'⟩ := H
  have hMD : env.IsDefEqU U Γ' M (D.liftN 1 k) := hv.uniqU henv hΓ' hvar'
  have hD' : env.HasType U Γ' (D.liftN 1 k) (.sort .zero) := (hMD.of_l henv hΓ' hM).hasType.2
  have hu : u ≈ .zero :=
    ((hD.weakN henv.ordered W).uniqU henv hΓ' hD').sort_inv henv hΓ'
  have hD0 : env.HasType U Γ D (.sort .zero) :=
    (IsDefEq.sortDF (l' := .zero) (hD.sort_r henv.ordered hΓ) trivial hu).defeq hD
  refine ⟨D, hD0, hvar, hTF.retype henv W hΓ hΓ' hc hD ?_⟩
  exact hc'.defeqU_r henv hΓ' hMD

end Lean4Lean.VEnv.StrengtheningReplay
