import Lean4Lean.Theory.Typing.Strengthening.TermModel
import Lean4Lean.Theory.Typing.EqTyping

/-! # Typing strengthening: the typing front and its one-step closures

`TypingFront env`: a `q`-free term typable in `Q :: Γ` is typable in `Γ` at some type.
`UninhabitedTypingFront env` restricts this to binders `Q` with no inhabitant in `Γ`; the two are
equivalent in every well-formed environment (`typingFront_of_uninhabited`: the inhabited case is
substitution).

**The typing front is the whole problem.** Under `WF` and canonical `Eq`,
`uninhabitedTypingFront_iff_cancel`: `UninhabitedTypingFront env ↔ Cancel env`. Existential
typing descent gives fixed-type descent through the ascription `ascribe e A := (λ x : A. x) e`
(`ascribe_inv`: typability of the ascription at any type forces `e : A`, by application and
lambda inversion and `Π`-injectivity, `fixed_typingFront`), and an equation `a↑ ≡ b↑` above is
encoded as the typing `Eq.refl a↑ : Eq A↑ a↑ b↑`, whose descent yields `a ≡ b` below by unique
typing and injectivity of the rigid head `Eq` (`canonicalEq_rigid`: canonical `Eq` is rigid by
`WF.installed_constructor_result_rigid` applied to the installed `Eq.rec` rule).
`not_cancel_iff_typing_gap`: `Cancel` fails exactly when some `q`-free term is typable above and
at no type below. So the question "does an equation descend" is the question "does a typing
descend", with no equation in it.

**Head exposure.** The application case of a structural induction on the term needs the type
of a function, typable below, whose lift is convertible above to a `Π`, to be convertible below
to a `Π`. Endpoint-preserving descent is false: `headSource_bad_path` reduces the lift of a type
typable below to a `Π` whose domain mentions the inserted variable, for every `Q`
(`headType_bad_reduct`, `arbitrary_Q_eta`); the reduct has a supported repair
(`arbitrary_Q_eta_repaired`). Existential exposure, `UninhabitedPiExposure`, is an open
proposition, not a theorem. `derived_proof_irrel` and `rigid_q_not_proof` record that rigidity
of `Q` excludes operations on the bare variable but not `q`-dependence through derived proofs.

Astra's round 8 design check (`strengthening-context/round8/design_check/Round8.lean`), adapted
with names kept. The second part of this file (`LiftN` form, one-step closures and the
structural induction) is this branch's own work. -/

namespace Lean4Lean.VEnv.StrengtheningTypingFront
open VExpr
variable {env : VEnv} {U : Nat} {Γ : List VExpr} {Q a b T : VExpr}

def TypingFront (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q e A⦄, OnCtx (Q :: Γ) (env.IsType U) →
    env.HasType U (Q :: Γ) e.lift A → ∃ B, env.HasType U Γ e B

def UninhabitedTypingFront (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q e A⦄, OnCtx (Q :: Γ) (env.IsType U) →
    (∀ q, ¬ env.HasType U Γ q Q) →
    env.HasType U (Q :: Γ) e.lift A → ∃ B, env.HasType U Γ e B

theorem typingFront_of_uninhabited (henv : env.WF)
    (H : UninhabitedTypingFront env) : TypingFront env := by
  intro U Γ Q e A hΓ he
  classical
  by_cases h : ∃ q, env.HasType U Γ q Q
  · obtain ⟨q, hq⟩ := h
    exact ⟨A.inst q, by simpa only [inst_lift] using he.instN henv.ordered Ctx.InstN.zero hq⟩
  · exact H hΓ (by simpa using h) he

-- A type annotation encoded using ordinary application and lambda syntax.
def ascribe (e A : VExpr) : VExpr := .app (.lam A (.bvar 0)) e

theorem ascribe_typed (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (he : env.HasType U Γ e A) : env.HasType U Γ (ascribe e A) A := by
  obtain ⟨u, hA⟩ := he.isType henv hΓ
  simpa only [ascribe, inst_lift] using HasType.app (HasType.lam hA (.bvar .zero)) he

theorem ascribe_inv (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (he : env.HasType U Γ (ascribe e A) B) : env.HasType U Γ e A := by
  obtain ⟨D, E, hf, he⟩ := he.app_inv henv.ordered hΓ
  obtain ⟨C, hPi, _⟩ := hf.lam_inv_forallE henv hΓ
  obtain ⟨u, hAD⟩ := (hPi.forallE_inv henv hΓ).1
  exact .defeqDF hAD.symm he

theorem fixed_typingFront (henv : env.WF) (H : TypingFront env)
    (hΓ : OnCtx (Q :: Γ) (env.IsType U))
    (he : env.HasType U (Q :: Γ) e.lift A.lift) : env.HasType U Γ e A := by
  have ht := ascribe_typed henv.ordered hΓ he
  have ht' : env.HasType U (Q :: Γ) (ascribe e A).lift A.lift := ht
  obtain ⟨B, hb⟩ := H hΓ ht'
  exact ascribe_inv henv hΓ.1 hb

theorem canonicalEq_rigid (henv : env.WF) (heq : env.HasCanonicalEq) : env.Rigid ``Eq := by
  have hm : canonicalEqRecRule.HasConstructorMajor ``Eq.refl :=
    ⟨_, [.param 1], [.bvar 3, .bvar 2], rfl⟩
  have h := henv.installed_constructor_result_rigid heq.2.2.2 hm
  unfold VEnv.CtorResultRigid at h
  obtain ⟨ci, hc, F, ls, hf, _, hr⟩ := h
  rw [heq.2.1] at hc
  cases hc
  have hf : VExpr.const ``Eq [.param 0] = .const F ls := hf
  cases hf
  exact hr

theorem eqApp_injective (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U))
    (hT : env.HasType U Γ T (.sort u)) (ha : env.HasType U Γ a T)
    (hu : u.WF U)
    (H : env.IsDefEqU U Γ (eqApp u T a a) (eqApp u T a b)) :
    env.IsDefEqU U Γ a b := by
  have ht := HasType.eqApp heq hu hT ha ha
  have hh := (IsDefEqU.rigidApp_inv (args := [T,a,a]) (args' := [T,a,b]) henv hΓ (canonicalEq_rigid henv heq) H ht).2
  cases hh with | cons _ hh =>
    cases hh with | cons _ hh =>
      cases hh with | cons h _ => exact h

theorem cancel_of_typingFront (henv : env.WF) (heq : env.HasCanonicalEq)
    (H : TypingFront env) : Cancel env := by
  apply Cancel.of_front henv
  intro U Γ Q a b hΓ hab
  obtain ⟨R, hab⟩ := hab
  obtain ⟨A, ha⟩ := H hΓ hab.hasType.1
  obtain ⟨u, hA⟩ := ha.isType henv.ordered hΓ.1
  have hu := hA.sort_r henv.ordered hΓ.1
  have ha' := ha.weak henv.ordered (B := Q)
  have hab' := (show env.IsDefEqU U (Q :: Γ) a.lift b.lift from ⟨_, hab⟩).of_l henv hΓ ha'
  have hA' := hA.weak henv.ordered (B := Q)
  have hr := HasType.eqReflApp heq hu hA' ha'
  have hr' := (IsDefEq.eqApp_r heq hu hA' ha' hab').defeq hr
  have hd : env.HasType U Γ (eqReflApp u A a) (eqApp u A a b) := by
    apply fixed_typingFront henv H hΓ
    simpa only [eqReflApp, eqApp, lift, liftN] using hr'
  have hr₀ := HasType.eqReflApp heq hu hA ha
  exact eqApp_injective henv heq hΓ.1 hA ha hu (hr₀.uniqU henv hΓ.1 hd)

theorem uninhabitedTypingFront_iff_cancel (henv : env.WF) (heq : env.HasCanonicalEq) :
    UninhabitedTypingFront env ↔ Cancel env := by
  constructor
  · intro H
    exact cancel_of_typingFront henv heq (typingFront_of_uninhabited henv H)
  · intro H U Γ Q e A hΓ _ he
    obtain ⟨B, hb⟩ := Front.of_cancel H hΓ ⟨A, he⟩
    exact ⟨B, hb⟩

/-! ## Derived proofs, rigid binders and the head-exposure counterexample -/

variable {P f h : VExpr}

-- Rigidity of Q does not prevent a proof application from using q.
theorem derived_proof_irrel (henv : env.Ordered)
    (hP : env.HasType U Γ P (.sort .zero))
    (hf : env.HasType U Γ f (.forallE Q P.lift))
    (hh : env.HasType U Γ h P) :
    env.IsDefEq U (Q :: Γ) (.app f.lift (.bvar 0)) h.lift P.lift := by
  have ha : env.HasType U (Q :: Γ) (.app f.lift (.bvar 0)) P.lift := by
    simpa only [lift, liftN, inst_liftN_bvar] using
      HasType.app (hf.weak henv (B := Q)) (HasType.bvar (env := env) (U := U) (Lookup.zero (ty := Q)))
  exact .proofIrrel (hP.weak henv) ha (hh.weak henv)

theorem derived_proof_mentions_q : ¬ (VExpr.app f.lift (.bvar 0)).Skips 1 0 := by
  simp [VExpr.skips_iff, VExpr.Skips']

theorem rigid_q_not_proof (henv : env.WF)
    (hΓ : OnCtx (VExpr.const I ls :: Γ) (env.IsType U))
    (hI : env.HasType U Γ (.const I ls) (.sort u)) (hne : ¬ u ≈ .zero)
    (hP : env.HasType U (.const I ls :: Γ) P (.sort .zero)) :
    ¬ env.HasType U (.const I ls :: Γ) (.bvar 0) P := by
  intro hp
  have hq : env.HasType U (.const I ls :: Γ) (.bvar 0) (.const I ls) := .bvar .zero
  have ht := (hq.uniqU henv hΓ hp).of_r henv hΓ hP
  have hi := hI.weak henv.ordered (B := .const I ls)
  exact hne ((hi.uniqU henv hΓ ht.hasType.1).sort_inv henv hΓ)

-- A bad eta domain works for every Q, including a rigid uninhabited Type.
def badDomain (Q : VExpr) : VExpr := .app (.lam Q.lift (.sort .zero)) (.bvar 0)
def badEta (Q : VExpr) : VExpr :=
  .lam (badDomain Q) (.app StrengtheningObstructions.idProp.lift (.bvar 0))

section
open VEnv.Params
variable [VEnv.Params]

theorem arbitrary_Q_eta :
    FullStep (Q :: Γ) StrengtheningObstructions.idProp.lift (badEta Q) ∧
      ¬ (badEta Q).Skips 1 0 := by
  have hd : Params.env.IsDefEq univs (Q :: Γ) (badDomain Q) (.sort .zero) (.sort (.succ .zero)) :=
    .beta (HasType.sort (l := .zero) trivial) (.bvar .zero)
  have hf : Params.env.HasType univs (Q :: Γ) StrengtheningObstructions.idProp
      (.forallE (.sort .zero) (.sort .zero)) := .lamDF (HasType.sort (l := .zero) trivial) (.bvar .zero)
  have hp := IsDefEq.forallEDF hd.symm (HasType.sort (env := Params.env) (U := univs)
    (Γ := .sort .zero :: Q :: Γ) (l := .zero) trivial)
  constructor
  · simpa [badEta, StrengtheningObstructions.idProp, lift, liftN, liftVar] using
      FullStep.funEta (IsDefEq.defeqDF hp hf)
  · simp [badEta, badDomain, VExpr.skips_iff, VExpr.Skips']

-- A lifted TYPE can have a non-lift Pi reduct; exact endpoint descent fails.
def headType : VExpr := .forallE
  (.app (.lam (.forallE (.sort .zero) (.sort .zero)) (.sort .zero))
    StrengtheningObstructions.idProp) (.sort .zero)

def headTypeBad (Q : VExpr) : VExpr := .forallE
  (.app (.lam (.forallE (.sort .zero) (.sort .zero)) (.sort .zero)) (badEta Q)) (.sort .zero)

theorem headType_typed : Params.env.HasType univs Γ headType (.sort (.succ .zero)) := by
  have hi : Params.env.HasType univs Γ StrengtheningObstructions.idProp
      (.forallE (.sort .zero) (.sort .zero)) := .lamDF (HasType.sort (l := .zero) trivial) (.bvar .zero)
  have hpi : Params.env.HasType univs Γ (.forallE (.sort .zero) (.sort .zero))
      (.sort (.succ .zero)) := StrengtheningObstructions.bodyPi_typed
  have ha : Params.env.HasType univs Γ
      (.app (.lam (.forallE (.sort .zero) (.sort .zero)) (.sort .zero))
        StrengtheningObstructions.idProp) (.sort (.succ .zero)) :=
    .app (.lamDF hpi (HasType.sort (l := .zero) trivial)) hi
  have hh : Params.env.HasType univs Γ headType
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
    .forallE ha (.sort trivial)
  exact .defeqDF (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero))
    (l' := .succ .zero) ⟨trivial, trivial⟩ trivial rfl) hh

theorem headType_bad_reduct :
    FullStep (Q :: Γ) headType.lift (headTypeBad Q) ∧
    ¬ (headTypeBad Q).Skips 1 0 := by
  constructor
  · exact .forallE (.app .rfl arbitrary_Q_eta.1) .rfl
  · simp [headTypeBad, VExpr.skips_iff, VExpr.Skips', badEta, badDomain]

def headSource : VExpr := .app (.lam (.sort (.succ .zero)) (.bvar 0)) headType

theorem headSource_typed : Params.env.HasType univs Γ headSource (.sort (.succ .zero)) :=
  .app (.lamDF (HasType.sort (l := .succ .zero) trivial) (.bvar .zero)) headType_typed

theorem headSource_bad_path :
    FullReduction (Q :: Γ) headSource.lift (headTypeBad Q) := by
  refine (ReflTransGen.tail .rfl (FullStep.app FullStep.rfl headType_bad_reduct.1)).tail ?_
  simpa [lift, liftN, liftVar, inst, instVar] using
    (FullStep.core (ParRed.beta (Γ := Q :: Γ) (A := .sort (.succ .zero))
      (e₁ := .bvar 0) (e₂ := headTypeBad Q) .rfl .rfl))

theorem arbitrary_Q_eta_repaired :
    FullStep (Q :: Γ) (badEta Q) StrengtheningObstructions.etaGood.lift := by
  exact .lam (.core (.beta .rfl .rfl)) .rfl

-- With a fixed common Pi, declarative subject reduction retains the eta domain.
theorem fixed_type_eta_peak
    (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hf : Params.env.HasType univs Γ f (.forallE A B)) (hs : FullStep Γ f g) :
    FullStep Γ g (.lam A (.app g.lift (.bvar 0))) ∧
    FullStep Γ (.lam A (.app f.lift (.bvar 0)))
      (.lam A (.app g.lift (.bvar 0))) := by
  exact ⟨.funEta (hs.hasType hΓ hf), .lam .rfl (.app (hs.weakN Ctx.LiftN.one) .rfl)⟩
end

/-! ## The typing gap -/

theorem not_cancel_iff_typing_gap {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq) :
    ¬ Cancel env ↔
      ∃ (U : Nat) (Γ : List VExpr) (Q e A : VExpr),
        OnCtx (Q :: Γ) (env.IsType U) ∧
        (∀ q, ¬ env.HasType U Γ q Q) ∧
        env.HasType U (Q :: Γ) e.lift A ∧
        ∀ B, ¬ env.HasType U Γ e B := by
  classical
  rw [← uninhabitedTypingFront_iff_cancel henv heq]
  simp only [UninhabitedTypingFront, Classical.not_forall, not_exists, exists_prop]

/-! ## Existential exposure: the open proposition -/

section
open VEnv.Params
variable [VEnv.Params]

/-- An OPEN obligation, not a theorem. The output Pi may differ from the given Pi. -/
def UninhabitedPiExposure : Prop :=
  ∀ {Γ Q T A B u}, OnCtx (Q :: Γ) (Params.env.IsType univs) →
    (∀ q, ¬ Params.env.HasType univs Γ q Q) →
    Params.env.HasType univs Γ T (.sort u) →
    FullReduction (Q :: Γ) T.lift (.forallE A B) →
    ∃ A₀ B₀, FullReduction Γ T (.forallE A₀ B₀)
end

/-! ## Part 2: the `LiftN` form, the one-step closures and the structural induction

`TypingFrontN`: typing descent along any single-binder insertion `Ctx.LiftN 1 k Γ Γ'`
(equivalent to `TypingFront` and to `Cancel` under canonical `Eq`, `typingFrontN_iff_cancel`).
The structural induction on the term reduces it exactly to four one-step closures
(`typingFrontN_iff_closures`), each necessary:

* `AppFrontN`: an application of terms typable below, typable above, is typable below;
* `TypeFrontN`: two types of `Γ` with convertible lifts are convertible (this is `Front`
  restricted to types; the `λ`/`Π` cases need it as sort exposure, `TypeFrontN.sort`);
* `ProjFrontN`, `ElimFrontN`: the projection and eliminator-constant closures.

`AppFrontN` follows from existential `Π` exposure `PiExposureN` (statement (i)) and `TypeFrontN`
(domain agreement, statement (ii)): `AppFrontN.of_piExposure`; conversely `AppFrontN.piExposure`
is exposure for a lifted inhabited domain. Under canonical `Eq`, exposure in conversion form
follows from exposure in reduction form `PiExposureRedN` (`exposure_reduces`: a type convertible
to a `Π` reduces to a `Π`, by Church-Rosser and the `Π`-stability of `FullStep` and `NormalEqN`).
Descending paths expose (`piExposure_of_descending`); the path of `headSource` is not descending
(`headSource_path_not_descending`). Stuck heads never expose a `Π` (`stationary_type_not_pi`,
`rigid_type_not_pi`, `loop_not_pi`). -/

variable {Γ : List VExpr}

/-! ## Typing descent along any single-binder insertion -/

def TypingFrontN (env : VEnv) : Prop :=
  ∀ ⦃U k Γ Γ' e T⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ' (e.liftN 1 k) T → ∃ T₀, env.HasType U Γ e T₀

theorem typingFront_of_typingFrontN (H : TypingFrontN env) : TypingFront env :=
  fun _ _ _ _ _ hΓ he => H Ctx.LiftN.one hΓ.1 hΓ he

theorem typingFrontN_of_cancel (henv : env.WF) (hc : Cancel env) : TypingFrontN env :=
  fun _ _ _ _ _ _ W _ hΓ' he => Strengthening.of_cancel henv hc W hΓ' ⟨_, he⟩

theorem typingFrontN_iff_cancel (henv : env.WF) (heq : env.HasCanonicalEq) :
    TypingFrontN env ↔ Cancel env :=
  ⟨fun H => cancel_of_typingFront henv heq (typingFront_of_typingFrontN H),
    typingFrontN_of_cancel henv⟩

/-! ## The one-step closures -/

def TypeFrontN (env : VEnv) : Prop :=
  ∀ ⦃U k Γ Γ' A B u v⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ A (.sort u) → env.HasType U Γ B (.sort v) →
    env.IsDefEqU U Γ' (A.liftN 1 k) (B.liftN 1 k) → env.IsDefEqU U Γ A B

def AppFrontN (env : VEnv) : Prop :=
  ∀ ⦃U k Γ Γ' f a F A T⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ f F → env.HasType U Γ a A →
    env.HasType U Γ' (.app (f.liftN 1 k) (a.liftN 1 k)) T → ∃ T₀, env.HasType U Γ (.app f a) T₀

def ProjFrontN (env : VEnv) : Prop :=
  ∀ ⦃U k Γ Γ' S i m M T⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ m M → env.HasType U Γ' (.proj S i (m.liftN 1 k)) T →
    ∃ T₀, env.HasType U Γ (.proj S i m) T₀

def ElimFrontN (env : VEnv) : Prop :=
  ∀ ⦃U k Γ Γ' block slot packed T⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (env.IsType U) →
    OnCtx Γ' (env.IsType U) → env.HasType U Γ' (.elim block slot packed) T →
    ∃ T₀, env.HasType U Γ (.elim block slot packed) T₀

def PiExposureN (env : VEnv) : Prop :=
  ∀ ⦃U k Γ Γ' f F A B⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (env.IsType U) → OnCtx Γ' (env.IsType U) →
    env.HasType U Γ f F → env.IsDefEqU U Γ' (F.liftN 1 k) (.forallE A B) →
    ∃ A₀ B₀, env.IsDefEqU U Γ F (.forallE A₀ B₀)

theorem lookup_append_inv : ∀ (As : List VExpr), Lookup (As ++ Γ) (As.length + i) A' →
    ∃ A, Lookup Γ i A
  | [], h => ⟨_, by simpa using h⟩
  | _ :: As, h => by
    rw [List.length_cons, Nat.add_right_comm] at h
    cases h with
    | succ h => exact lookup_append_inv As h

theorem Lookup.of_liftN (W : Ctx.LiftN n k Γ Γ') (H : Lookup Γ' (liftVar n i k) A') :
    ∃ A, Lookup Γ i A := by
  induction W generalizing i A' with
  | zero As hn =>
    subst hn
    rw [liftVar_base] at H
    exact lookup_append_inv As H
  | succ _ ih =>
    cases i with
    | zero => exact ⟨_, .zero⟩
    | succ i =>
      rw [liftVar_succ] at H
      cases H with
      | succ H =>
        obtain ⟨A, hA⟩ := ih H
        exact ⟨_, .succ hA⟩

/-- Sort exposure for a type of `Γ` whose lift is a sort above, from the type front. -/
theorem TypeFrontN.sort (henv : env.WF) (hTy : TypeFrontN env) (W : Ctx.LiftN 1 k Γ Γ')
    (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    (hA : env.HasType U Γ A T) (hA' : env.HasType U Γ' (A.liftN 1 k) (.sort u)) :
    env.HasType U Γ A (.sort u) := by
  obtain ⟨w, hT⟩ := hA.isType henv.ordered hΓ
  have hu := hA'.sort_r henv.ordered hΓ'
  have h1 : env.IsDefEqU U Γ' (T.liftN 1 k) ((VExpr.sort u).liftN 1 k) :=
    (hA.weakN henv.ordered W).uniqU henv hΓ' hA'
  exact hA.defeqU_r henv hΓ (hTy W hΓ hΓ' hT (.sort hu) h1)

/-- The structural induction: the typing front follows from its one-step closures. -/
theorem typingFrontN_of_closures (henv : env.WF) (hApp : AppFrontN env) (hTy : TypeFrontN env)
    (hProj : ProjFrontN env) (hElim : ElimFrontN env) : TypingFrontN env := by
  intro U k Γ Γ' e T W hΓ hΓ' he
  induction e generalizing k Γ Γ' T with
  | bvar i =>
    obtain ⟨A', hA'⟩ := he.bvar_inv henv.ordered hΓ'
    obtain ⟨A, hA⟩ := Lookup.of_liftN W hA'
    exact ⟨_, .bvar hA⟩
  | sort u => exact ⟨_, .sort (he.sort_inv henv.ordered)⟩
  | const c ls =>
    obtain ⟨ci, h1, h2, h3⟩ := he.const_inv henv.ordered hΓ'
    exact ⟨_, .const h1 h2 h3⟩
  | elim block slot packed => exact hElim W hΓ hΓ' he
  | app f a ihf iha =>
    obtain ⟨A, B, hf, ha⟩ := he.app_inv henv.ordered hΓ'
    obtain ⟨F, hF⟩ := ihf W hΓ hΓ' hf
    obtain ⟨A₀, hA₀⟩ := iha W hΓ hΓ' ha
    exact hApp W hΓ hΓ' hF hA₀ he
  | lam A b ihA ihb =>
    obtain ⟨⟨u, hA'⟩, _, hb'⟩ := he.lam_inv henv.ordered hΓ'
    obtain ⟨TA, hTA⟩ := ihA W hΓ hΓ' hA'
    have hA := TypeFrontN.sort henv hTy W hΓ hΓ' hTA hA'
    obtain ⟨Tb, hTb⟩ := ihb W.succ ⟨hΓ, u, hA⟩ ⟨hΓ', u, hA'⟩ hb'
    exact ⟨_, .lam hA hTb⟩
  | forallE A B ihA ihB =>
    obtain ⟨⟨u, hA'⟩, v, hB'⟩ := he.forallE_inv henv.ordered
    obtain ⟨TA, hTA⟩ := ihA W hΓ hΓ' hA'
    have hA := TypeFrontN.sort henv hTy W hΓ hΓ' hTA hA'
    have hΓA : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, u, hA⟩
    have hΓA' : OnCtx (A.liftN 1 k :: Γ') (env.IsType U) := ⟨hΓ', u, hA'⟩
    obtain ⟨TB, hTB⟩ := ihB W.succ hΓA hΓA' hB'
    have hB := TypeFrontN.sort henv hTy W.succ hΓA hΓA' hTB hB'
    exact ⟨_, .forallE hA hB⟩
  | proj S i m ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv.ordered hΓ'
    obtain ⟨M, hM⟩ := ih W hΓ hΓ' hm.hasType.2
    exact hProj W hΓ hΓ' hM he

/-! ### The closures are necessary -/

theorem AppFrontN.of_typingFrontN (H : TypingFrontN env) : AppFrontN env :=
  fun _ _ _ _ _ _ _ _ _ W hΓ hΓ' _ _ he => H W hΓ hΓ' he

theorem ProjFrontN.of_typingFrontN (H : TypingFrontN env) : ProjFrontN env :=
  fun _ _ _ _ _ _ _ _ _ W hΓ hΓ' _ he => H W hΓ hΓ' he

theorem ElimFrontN.of_typingFrontN (H : TypingFrontN env) : ElimFrontN env :=
  fun _ _ _ _ _ _ _ _ W hΓ hΓ' he => H W hΓ hΓ' he

theorem liftN_lift_succ (e : VExpr) (k : Nat) : e.lift.liftN 1 (k+1) = (e.liftN 1 k).lift :=
  (lift_liftN' e k).symm

/-- The type front is the typing front at the ascription `(λ x : Π B. B↑. x) (λ x : A. x)`. -/
theorem TypeFrontN.of_typingFrontN (henv : env.WF) (H : TypingFrontN env) : TypeFrontN env := by
  intro U k Γ Γ' A B u v W hΓ hΓ' hA hB hAB
  have hid : env.HasType U Γ (.lam A (.bvar 0)) (.forallE A A.lift) := .lam hA (.bvar .zero)
  have hA' : env.HasType U Γ' (A.liftN 1 k) (.sort u) := hA.weakN henv.ordered W
  have hAB' := hAB.of_l henv hΓ' hA'
  have hPi : env.IsDefEq U Γ' (.forallE (A.liftN 1 k) (A.liftN 1 k).lift)
      (.forallE (B.liftN 1 k) (B.liftN 1 k).lift) (.sort (.imax u u)) :=
    .forallEDF hAB' (hAB'.weak henv.ordered)
  have hid' : env.HasType U Γ' ((VExpr.lam A (.bvar 0)).liftN 1 k)
      (.forallE (B.liftN 1 k) (B.liftN 1 k).lift) := by
    have := hid.weakN henv.ordered W
    simp only [liftN, liftVar_zero, liftN_lift_succ] at this ⊢
    exact hPi.defeq this
  have hasc := ascribe_typed henv.ordered hΓ' hid'
  have hasc' : env.HasType U Γ' ((ascribe (.lam A (.bvar 0)) (.forallE B B.lift)).liftN 1 k)
      (.forallE (B.liftN 1 k) (B.liftN 1 k).lift) := by
    simpa only [ascribe, liftN, liftVar_zero, liftN_lift_succ] using hasc
  obtain ⟨T₀, hT₀⟩ := H W hΓ hΓ' hasc'
  have hidB := ascribe_inv henv hΓ hT₀
  obtain ⟨_, h⟩ := ((hid.uniqU henv hΓ hidB).forallE_inv henv hΓ).1
  exact ⟨_, h⟩

theorem typingFrontN_iff_closures (henv : env.WF) :
    TypingFrontN env ↔ AppFrontN env ∧ TypeFrontN env ∧ ProjFrontN env ∧ ElimFrontN env :=
  ⟨fun H => ⟨AppFrontN.of_typingFrontN H, TypeFrontN.of_typingFrontN henv H,
    ProjFrontN.of_typingFrontN H, ElimFrontN.of_typingFrontN H⟩,
    fun h => typingFrontN_of_closures henv h.1 h.2.1 h.2.2.1 h.2.2.2⟩

/-! ### The application closure from exposure and domain agreement -/

theorem AppFrontN.of_piExposure (henv : env.WF) (hPi : PiExposureN env) (hTy : TypeFrontN env) :
    AppFrontN env := by
  intro U k Γ Γ' f a F A T W hΓ hΓ' hf ha he
  obtain ⟨A', B', hf', ha'⟩ := he.app_inv henv.ordered hΓ'
  have hF' := (hf.weakN henv.ordered W).uniqU henv hΓ' hf'
  obtain ⟨A₀, B₀, hFPi⟩ := hPi W hΓ hΓ' hf hF'
  have hfPi : env.HasType U Γ f (.forallE A₀ B₀) := hf.defeqU_r henv hΓ hFPi
  have h1 : env.IsDefEqU U Γ' ((VExpr.forallE A₀ B₀).liftN 1 k) (.forallE A' B') :=
    (hFPi.weakN henv.ordered W).symm.trans henv hΓ' hF'
  obtain ⟨⟨_, hdom⟩, _⟩ := h1.forallE_inv henv hΓ'
  have hAA₀ : env.IsDefEqU U Γ' (A.liftN 1 k) (A₀.liftN 1 k) :=
    ((ha.weakN henv.ordered W).uniqU henv hΓ' ha').trans henv hΓ' ⟨_, hdom.symm⟩
  obtain ⟨u, hAs⟩ := ha.isType henv.ordered hΓ
  obtain ⟨_, hPis⟩ := hfPi.isType henv.ordered hΓ
  obtain ⟨⟨v, hA₀s⟩, _⟩ := hPis.forallE_inv henv.ordered
  exact ⟨_, .app hfPi (ha.defeqU_r henv hΓ (hTy W hΓ hΓ' hAs hA₀s hAA₀))⟩

/-- Exposure with a lifted inhabited domain is the application closure. -/
theorem AppFrontN.piExposure (henv : env.WF) (hApp : AppFrontN env) (W : Ctx.LiftN 1 k Γ Γ')
    (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    (hf : env.HasType U Γ f F) (ha : env.HasType U Γ a A₀)
    (hF : env.IsDefEqU U Γ' (F.liftN 1 k) (.forallE (A₀.liftN 1 k) B)) :
    ∃ A₁ B₁, env.IsDefEqU U Γ F (.forallE A₁ B₁) := by
  have hf' : env.HasType U Γ' (f.liftN 1 k) (.forallE (A₀.liftN 1 k) B) :=
    (hf.weakN henv.ordered W).defeqU_r henv hΓ' hF
  obtain ⟨T₀, hT₀⟩ := hApp W hΓ hΓ' hf ha (hf'.app (ha.weakN henv.ordered W))
  obtain ⟨A₁, B₁, hf₁, _⟩ := hT₀.app_inv henv.ordered hΓ
  exact ⟨A₁, B₁, hf.uniqU henv hΓ hf₁⟩

/-! ## Exposure through reduction -/

section Reduction
open VEnv.Params
variable [VEnv.Params]

theorem parRed_forallE_inv (H : ParRed Γ (.forallE A B) e') : ∃ A' B', e' = .forallE A' B' := by
  generalize he : VExpr.forallE A B = e at H
  cases H with
  | forallE => exact ⟨_, _, rfl⟩
  | schema hm hl hr =>
    have hh := congrArg (fun e : VExpr => e.getAppFnArgs.1) he
    rw [InductiveSignature.CaseSchema.Application.head] at hh
    cases hh
  | extra hp hm =>
    obtain ⟨sp, rfl⟩ := pat_simple hp
    obtain ⟨name, hhead⟩ := InductiveSignature.CaseSchema.recursor_pattern_head hm
    rw [← he] at hhead
    cases hhead
  | _ => cases he

/-- A `Π` type steps only to a `Π`. -/
theorem fullStep_forallE_inv (hΓ : OnCtx Γ (Params.env.IsType univs))
    (ht : Params.env.HasType univs Γ (.forallE A B) (.sort u))
    (H : FullStep Γ (.forallE A B) e') : ∃ A' B', e' = .forallE A' B' := by
  generalize he : VExpr.forallE A B = e at H
  cases H with
  | core h => subst he; exact parRed_forallE_inv h
  | forallE _ _ => exact ⟨_, _, rfl⟩
  | delta h => exact False.elim (VExpr.mkApps_ne_forallE (by intros; intro h; cases h) _ he.symm)
  | quotDelta h =>
    exact False.elim (VExpr.mkApps_ne_forallE (by intros; intro h; cases h) _ he.symm)
  | structEta hi _ _ hs _ =>
    subst he
    exact False.elim (henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
      ((ht.uniqU henv hΓ hs).typeChain henv hΓ (.sort (ht.sort_r henv.ordered hΓ))))
  | funEta hf =>
    subst he
    exact False.elim (IsDefEqU.sort_forallE_inv henv hΓ (ht.uniqU henv hΓ hf))
  | _ => cases he

theorem fullReduction_forallE_inv (hΓ : OnCtx Γ (Params.env.IsType univs))
    (ht : Params.env.HasType univs Γ (.forallE A B) (.sort u))
    (H : FullReduction Γ (.forallE A B) e') : ∃ A' B', e' = .forallE A' B' := by
  induction H with
  | rfl => exact ⟨_, _, rfl⟩
  | tail hr hs ih =>
    obtain ⟨A', B', rfl⟩ := ih
    exact fullStep_forallE_inv hΓ (FullReduction.hasType hΓ hr ht) hs

/-- A term normally equal to a `Π` is a `Π`. -/
theorem normalEqN_forallE_inv_r (hΓ : OnCtx Γ (Params.env.IsType univs))
    (ht : Params.env.HasType univs Γ (.forallE A B) (.sort u))
    (H : NormalEqN η n Γ e (.forallE A B)) : ∃ A' B', e = .forallE A' B' := by
  generalize he : VExpr.forallE A B = r at H
  cases H with
  | refl _ => exact ⟨_, _, he.symm⟩
  | forallEDF => exact ⟨_, _, rfl⟩
  | etaL ht' _ =>
    subst he
    exact False.elim (IsDefEqU.sort_forallE_inv henv hΓ (ht.uniqU henv hΓ ht'))
  | etaBoth _ ht' _ =>
    subst he
    exact False.elim (IsDefEqU.sort_forallE_inv henv hΓ (ht.uniqU henv hΓ ht'))
  | proofIrrel hp _ hb =>
    subst he
    have h1 := (ht.uniqU henv hΓ hb).of_r henv hΓ hp
    have h2 := (HasType.sort (ht.sort_r henv.ordered hΓ) :
      Params.env.HasType univs Γ (.sort u) (.sort (.succ u))).uniqU henv hΓ h1.hasType.1
    have h3 := congrFun (h2.sort_inv henv hΓ) []
    simp [VLevel.eval] at h3
  | _ => cases he

end Reduction

/-- A type convertible to a `Π` reduces to a `Π` (canonical `Eq`, through Church-Rosser). -/
theorem exposure_reduces {E : VEnv} (hE : E.WF) (hEq : E.HasCanonicalEq)
    (hΓ : OnCtx Γ (E.IsType U)) (hT : E.HasType U Γ T (.sort u))
    (H : E.IsDefEqU U Γ T (.forallE A B)) :
    letI := hE.params U
    ∃ A' B', FullReduction Γ T (.forallE A' B') := by
  letI := hE.params U
  have hd := H.of_l hE hΓ hT
  obtain ⟨x, y, hx, hy, hn⟩ := hE.church_rosser hEq hΓ hd
  have hPi : E.HasType U Γ (.forallE A B) (.sort u) := hd.hasType.2
  obtain ⟨A', B', rfl⟩ := fullReduction_forallE_inv hΓ hPi hy
  obtain ⟨n, hn⟩ := hn
  obtain ⟨A'', B'', rfl⟩ := normalEqN_forallE_inv_r hΓ (hy.hasType hΓ hPi) hn
  exact ⟨_, _, hx⟩

/-- Existential `Π` exposure in reduction form: a type of `Γ`, inhabited in `Γ`, whose lift
reduces above to a `Π`, reduces below to some `Π`. -/
def PiExposureRedN {E : VEnv} (hE : E.WF) : Prop :=
  ∀ ⦃U k Γ Γ' f F u A B⦄, Ctx.LiftN 1 k Γ Γ' → OnCtx Γ (E.IsType U) → OnCtx Γ' (E.IsType U) →
    E.HasType U Γ f F → E.HasType U Γ F (.sort u) →
    (letI := hE.params U; FullReduction Γ' (F.liftN 1 k) (.forallE A B)) →
    ∃ A₀ B₀, letI := hE.params U; FullReduction Γ F (.forallE A₀ B₀)

theorem PiExposureN.of_red {E : VEnv} (hE : E.WF) (hEq : E.HasCanonicalEq)
    (H : PiExposureRedN hE) : PiExposureN E := by
  intro U k Γ Γ' f F A B W hΓ hΓ' hf hF
  obtain ⟨u, hFs⟩ := hf.isType hE.ordered hΓ
  have hFs' : E.HasType U Γ' (F.liftN 1 k) (.sort u) := hFs.weakN hE.ordered W
  obtain ⟨A', B', hred⟩ := exposure_reduces hE hEq hΓ' hFs' hF
  obtain ⟨A₀, B₀, hred₀⟩ := H W hΓ hΓ' hf hFs hred
  letI := hE.params U
  exact ⟨A₀, B₀, _, hred₀.defeq hΓ hFs⟩

/-- Under canonical `Eq`, reduction-form exposure (with the type front) gives the typing front,
hence `Cancel`. -/
theorem cancel_of_piExposureRed {E : VEnv} (hE : E.WF) (hEq : E.HasCanonicalEq)
    (hRed : PiExposureRedN hE) (hTy : TypeFrontN E) (hProj : ProjFrontN E) (hElim : ElimFrontN E) :
    Cancel E :=
  (typingFrontN_iff_cancel hE hEq).mp (typingFrontN_of_closures hE
    (AppFrontN.of_piExposure hE (PiExposureN.of_red hE hEq hRed) hTy) hTy hProj hElim)

section Descending
open VEnv.Params
variable [VEnv.Params]

/-- A descending path (every step a lifted step) exposes a `Π` below: the case that closes. -/
theorem piExposure_of_descending (W : Ctx.LiftN n k Γ Γ')
    (H : ReflTransGen (DescendingStep W) (F.liftN n k) (.forallE A B)) :
    ∃ A₀ B₀, FullReduction Γ F (.forallE A₀ B₀) ∧
      A = A₀.liftN n k ∧ B = B₀.liftN n (k+1) := by
  obtain ⟨b, hb, hred⟩ := descending_path_down H
  cases b <;> simp only [liftN] at hb <;> cases hb
  exact ⟨_, _, hred, rfl, rfl⟩

/-- The exposing path of `headSource` is not descending: its eta step annotates with a domain
mentioning the inserted variable. -/
theorem headSource_path_not_descending :
    ¬ ReflTransGen (DescendingStep (Ctx.LiftN.one (A := Q) (Γ := Γ)))
      headSource.lift (headTypeBad Q) := by
  intro hd
  obtain ⟨b, hb, _⟩ := descending_path_down hd
  exact (headType_bad_reduct (Γ := Γ) (Q := Q)).2 (by rw [hb]; exact VExpr.Skips.liftN)

end Descending

/-! ## Stuck heads never expose a `Π` -/

/-- A stationary type that is not syntactically a `Π` is not convertible to one. -/
theorem stationary_type_not_pi {E : VEnv} (hE : E.WF) (hEq : E.HasCanonicalEq)
    (hΓ : OnCtx Γ (E.IsType U)) (hs : @StrengtheningTermModel.Stationary (hE.params U) Γ e)
    (hne : ∀ A B, e ≠ .forallE A B) (he : E.HasType U Γ e (.sort u)) :
    ¬ E.IsDefEqU U Γ e (.forallE A B) := by
  intro H
  obtain ⟨A', B', hred⟩ := exposure_reduces hE hEq hΓ he H
  exact hne _ _ (hs _ hred).symm

/-- An opaque type (rigid constant head) never exposes a `Π`, in any context. -/
theorem rigid_type_not_pi {E : VEnv} (hE : E.WF) (hΓ : OnCtx Γ (E.IsType U))
    (hr : E.Rigid c) (hI : E.HasType U Γ (.const c ls) (.sort u)) :
    ¬ E.IsDefEqU U Γ (.const c ls) (.forallE A B) :=
  IsDefEqU.rigidApp_forallE_inv (args := []) hE hΓ hr hI

open StrengtheningKripke in
theorem loopEnv_onCtx_toAxioms {env env₁ env' : VEnv} {L₁ L₂ : Name}
    (H : LoopEnv env L₁ L₂ env₁ env') (hne : L₁ ≠ L₂) {U : Nat} :
    ∀ {Γ : List VExpr}, OnCtx Γ (env'.IsType U) → OnCtx Γ (env₁.IsType U)
  | [], _ => trivial
  | _ :: _, ⟨hΓ, _, hA⟩ => ⟨loopEnv_onCtx_toAxioms H hne hΓ, _, H.toAxioms hne hA⟩

open StrengtheningKripke in
/-- A self-looping definition never exposes a `Π`: every derivation of the looping environment
is a derivation of the axiom environment, where the constant is rigid. -/
theorem loop_not_pi {env env₁ env' : VEnv} {L₁ L₂ : Name} (henv : env.WF)
    (H : LoopEnv env L₁ L₂ env₁ env') (hne : L₁ ≠ L₂) (h₁ : env.constants L₁ = none)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env'.IsType U)) :
    ¬ env'.IsDefEqU U Γ (.const L₁ []) (.forallE A B) := by
  rintro ⟨T, D⟩
  have henv₁ := H.wf₁ henv
  have hr₁ : env₁.Rigid L₁ := by
    intro df hdf ls h
    rw [H.defeqs₁] at hdf
    exact (henv.rigid_of_fresh h₁) df hdf ls h
  exact rigid_type_not_pi henv₁ (loopEnv_onCtx_toAxioms H hne hΓ) hr₁ (H.typed₁ hne rfl)
    ⟨_, H.toAxioms hne D⟩


/-! ## Part 3: fragments that close, and the eliminator closure

`SortSkeleton` (sorts and `Π` over skeletons) is closed and context-free: `SortSkeleton.hasType_of`
moves its sort typing between any two well-formed contexts, and `typeFrontN_skeleton` is the type
front between skeletons (sort and `Π` heads descend; the only inversions used are `sort_inv`,
`sort_forallE_inv`, `forallE_inv`). `typingFrontN_skeletonFragment`: the typing front holds, with
no hypothesis on the environment, for variables, sorts, constants, skeletons and `λ` over such
bodies with skeleton domains. Every extension is blocked by exactly one closure: a non-skeleton
domain by `TypeFrontN.sort`, an application by `AppFrontN`, a projection by `ProjFrontN`, an
eliminator constant by `ElimFrontN`. `ElimFrontN.of_genericTyped` discharges the last one from
`GenericTypesTyped`, an environment-level statement (generic eliminator types are typed in `[]`)
that the library does not currently provide. -/

variable {Γ' : List VExpr}

/-! ## Fragments that close -/

/-- Closed type skeletons: sorts and `Π` over skeletons. -/
inductive SortSkeleton : VExpr → Prop
  | sort (u : VLevel) : SortSkeleton (.sort u)
  | forallE {A B : VExpr} : SortSkeleton A → SortSkeleton B → SortSkeleton (.forallE A B)

theorem SortSkeleton.liftN_eq {A : VExpr} (h : SortSkeleton A) (n k : Nat) : A.liftN n k = A := by
  induction h generalizing k with
  | sort => rfl
  | forallE _ _ ih1 ih2 => simp only [liftN, ih1, ih2]

/-- A skeleton typed at a sort in one well-formed context is typed at that sort in every
well-formed context. -/
theorem SortSkeleton.hasType_of (henv : env.WF) {A : VExpr} (hs : SortSkeleton A)
    (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    (h : env.HasType U Γ' A (.sort u)) : env.HasType U Γ A (.sort u) := by
  induction hs generalizing Γ Γ' u with
  | sort w =>
    have hw := h.sort_inv henv.ordered
    have hu := h.sort_r henv.ordered hΓ'
    have he := (HasType.sort (Γ := Γ') hw).uniqU henv hΓ' h
    exact (IsDefEq.sortDF (l := .succ w) hw hu (he.sort_inv henv hΓ')).defeq (.sort hw)
  | @forallE A B _ _ ih1 ih2 =>
    obtain ⟨⟨a, hA⟩, b, hB⟩ := h.forallE_inv henv.ordered
    have hA' := ih1 hΓ hΓ' hA
    have hΓA : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, _, hA'⟩
    have hΓA' : OnCtx (A :: Γ') (env.IsType U) := ⟨hΓ', _, hA⟩
    have hB' := ih2 hΓA hΓA' hB
    have hu := h.sort_r henv.ordered hΓ'
    have he := (HasType.forallE hA hB).uniqU henv hΓ' h
    exact (IsDefEq.sortDF ((HasType.forallE hA' hB').sort_r henv.ordered hΓ) hu
      (he.sort_inv henv hΓ')).defeq (.forallE hA' hB')

/-- The type front holds between skeletons (sort and `Π` heads descend). -/
theorem typeFrontN_skeleton (henv : env.WF) {A B : VExpr} (hA : SortSkeleton A)
    (hB : SortSkeleton B) (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    (htA : env.HasType U Γ A (.sort u)) (htB : env.HasType U Γ B (.sort v))
    (H : env.IsDefEqU U Γ' A B) : env.IsDefEqU U Γ A B := by
  induction hA generalizing B Γ Γ' u v with
  | sort w =>
    cases hB with
    | sort w' =>
      exact ⟨_, .sortDF (htA.sort_inv henv.ordered) (htB.sort_inv henv.ordered)
        (H.sort_inv henv hΓ')⟩
    | forallE => exact (IsDefEqU.sort_forallE_inv henv hΓ' H).elim
  | @forallE A₁ A₂ hA₁ hA₂ ih1 ih2 =>
    cases hB with
    | sort => exact (IsDefEqU.sort_forallE_inv henv hΓ' H.symm).elim
    | @forallE B₁ B₂ hB₁ hB₂ =>
      obtain ⟨⟨_, h1⟩, _, h2⟩ := H.forallE_inv henv hΓ'
      obtain ⟨⟨a, htA₁⟩, a', htA₂⟩ := htA.forallE_inv henv.ordered
      obtain ⟨⟨b, htB₁⟩, b', htB₂⟩ := htB.forallE_inv henv.ordered
      have hΓA : OnCtx (A₁ :: Γ) (env.IsType U) := ⟨hΓ, _, htA₁⟩
      have hΓA' : OnCtx (A₁ :: Γ') (env.IsType U) := ⟨hΓ', _, (h1.hasType.1)⟩
      have e1 := ih1 hB₁ hΓ hΓ' htA₁ htB₁ ⟨_, h1⟩
      have hΓB : OnCtx (B₁ :: Γ) (env.IsType U) := ⟨hΓ, _, htB₁⟩
      have htB₂' := hB₂.hasType_of henv hΓA hΓB htB₂
      have e2 := ih2 hB₂ hΓA hΓA' htA₂ htB₂' ⟨_, h2⟩
      exact ⟨_, .forallEDF (e1.of_l henv hΓ htA₁) (e2.of_l henv hΓA htA₂)⟩

/-- Terms whose binder domains are skeletons and whose `Π`s are skeletons: variables, sorts,
constants, `λ` over such bodies with skeleton domains, and skeletons. -/
inductive SkeletonFragment : VExpr → Prop
  | bvar (i : Nat) : SkeletonFragment (.bvar i)
  | sort (u : VLevel) : SkeletonFragment (.sort u)
  | const (c : Name) (ls : List VLevel) : SkeletonFragment (.const c ls)
  | lam {A b : VExpr} : SortSkeleton A → SkeletonFragment b → SkeletonFragment (.lam A b)
  | skeleton {A : VExpr} : SortSkeleton A → SkeletonFragment A

/-- The typing front holds on the skeleton fragment with no hypothesis on the environment. -/
theorem typingFrontN_skeletonFragment (henv : env.WF) {e : VExpr} (he : SkeletonFragment e)
    {k : Nat} {T : VExpr} (W : Ctx.LiftN 1 k Γ Γ') (hΓ : OnCtx Γ (env.IsType U))
    (hΓ' : OnCtx Γ' (env.IsType U)) (h : env.HasType U Γ' (e.liftN 1 k) T) :
    ∃ T₀, env.HasType U Γ e T₀ := by
  induction he generalizing k Γ Γ' T with
  | bvar i =>
    obtain ⟨A', hA'⟩ := h.bvar_inv henv.ordered hΓ'
    obtain ⟨A, hA⟩ := Lookup.of_liftN W hA'
    exact ⟨_, .bvar hA⟩
  | sort u => exact ⟨_, .sort (h.sort_inv henv.ordered)⟩
  | const c ls =>
    obtain ⟨ci, h1, h2, h3⟩ := h.const_inv henv.ordered hΓ'
    exact ⟨_, .const h1 h2 h3⟩
  | @lam A b hA _ ih =>
    obtain ⟨⟨u, hA'⟩, _, hb'⟩ := h.lam_inv henv.ordered hΓ'
    rw [hA.liftN_eq] at hA' hb'
    have hA₀ := hA.hasType_of henv hΓ hΓ' hA'
    have W' : Ctx.LiftN 1 (k+1) (A :: Γ) (A :: Γ') := by
      have := W.succ (A := A)
      rwa [hA.liftN_eq] at this
    have hΓA : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, u, hA₀⟩
    have hΓA' : OnCtx (A :: Γ') (env.IsType U) := ⟨hΓ', u, hA'⟩
    obtain ⟨Tb, hTb⟩ := ih W' hΓA hΓA' hb'
    exact ⟨_, .lam hA₀ hTb⟩
  | skeleton hs =>
    rw [hs.liftN_eq] at h
    cases hs with
    | sort w => exact ⟨_, .sort (h.sort_inv henv.ordered)⟩
    | forallE h1 h2 =>
      obtain ⟨⟨a, hA⟩, b, hB⟩ := h.forallE_inv henv.ordered
      exact ⟨_, (SortSkeleton.forallE h1 h2).hasType_of henv hΓ hΓ' (.forallE hA hB)⟩

/-! ## The eliminator closure from typed generic types -/

/-- Every registered eliminator schema has its generic type typed at a sort in the empty
context, at every permitted universe specialization. Not a library theorem (the library has
`WF.eliminator_genericType_closed` only); stated as the hypothesis that discharges
`ElimFrontN`. -/
def GenericTypesTyped (env : VEnv) : Prop :=
  ∀ ⦃U block schema owner type target levels⦄, env.eliminators block schema →
    schema.genericType owner = some type → schema.Permission U owner levels target →
    ∃ l, env.HasType U [] (type.instL (target :: levels)) (.sort l)

theorem ElimFrontN.of_genericTyped (henv : env.WF) (H : GenericTypesTyped env) :
    ElimFrontN env := by
  intro U k Γ Γ' block slot packed T W hΓ hΓ' he
  obtain ⟨schema, owner, type, target, levels, typeLevel, rfl, rfl, hl, ht, hc, hp, _, _⟩ :=
    he.elim_inv henv.ordered hΓ'
  obtain ⟨l, hgen⟩ := H hl ht hp
  have hrefl : ∀ ls : List VLevel, List.Forall₂ (· ≈ ·) ls ls := by
    intro ls
    induction ls with
    | nil => exact .nil
    | cons l ls ih => exact .cons rfl ih
  exact ⟨_, .elimDF hl ht hc hp hp.packedWF (hrefl _) (hgen.weak0 henv.ordered)⟩


/-! ## Part 4: statement (ii) is `TypedFront`

`TypeFront` (the type front at the front of the context) is implied by `TypeFrontN` and by
`Cancel`; under canonical `Eq` it is equivalent to Kripke's `TypedFront`
(`typeFront_iff_typedFront`), hence to `KeyFaithful` (`keyFaithful_iff_typedFront`). So the
domain-agreement obligation of the application case is exactly the fixed-type front for terms
typable below, which the observation model of `Kripke.lean` could not deliver. -/

/-! ## Statement (ii) is `TypedFront` -/

/-- The type front at the front of the context. -/
def TypeFront (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q A B u v⦄, OnCtx (Q :: Γ) (env.IsType U) →
    env.HasType U Γ A (.sort u) → env.HasType U Γ B (.sort v) →
    env.IsDefEqU U (Q :: Γ) A.lift B.lift → env.IsDefEqU U Γ A B

theorem TypeFront.of_typeFrontN (H : TypeFrontN env) : TypeFront env :=
  fun _ _ _ _ _ _ _ hΓ hA hB hAB => H Ctx.LiftN.one hΓ.1 hΓ hA hB hAB

theorem typeFrontN_of_cancel (henv : env.WF) (hc : Cancel env) : TypeFrontN env :=
  TypeFrontN.of_typingFrontN henv (typingFrontN_of_cancel henv hc)

/-- Domain agreement (ii) gives Kripke's fixed-type front for terms: an equation between terms
typable below at a common type is encoded as the `Eq` types `Eq T a a` and `Eq T a b`, which are
types below with convertible lifts above; their agreement below gives `a ≡ b` by injectivity of
the rigid head `Eq`. -/
theorem typedFront_of_typeFront (henv : env.WF) (heq : env.HasCanonicalEq) (H : TypeFront env) :
    StrengtheningKripke.TypedFront env := by
  intro U Γ Q a b T hΓ hQ ha hb hab
  obtain ⟨u, hT⟩ := ha.isType henv.ordered hΓ
  have hu := hT.sort_r henv.ordered hΓ
  have hΓ' : OnCtx (Q :: Γ) (env.IsType U) := ⟨hΓ, hQ⟩
  have e1 := IsDefEq.eqApp_r heq hu (hT.weak henv.ordered (B := Q)) (ha.weak henv.ordered (B := Q)) hab
  have e2 : env.IsDefEqU U (Q :: Γ) (eqApp u T a a).lift (eqApp u T a b).lift :=
    ⟨_, by simpa only [eqApp, lift, liftN] using e1⟩
  have h := H hΓ' (HasType.eqApp heq hu hT ha ha) (HasType.eqApp heq hu hT ha hb) e2
  exact (eqApp_injective henv heq hΓ hT ha hu h).of_l henv hΓ ha

theorem typeFront_of_typedFront (henv : env.WF) (H : StrengtheningKripke.TypedFront env) :
    TypeFront env := by
  intro U Γ Q A B u v hΓ hA hB hAB
  have hA' := hA.weak henv.ordered (B := Q)
  have hB' := hB.weak henv.ordered (B := Q)
  have hd := hAB.of_l henv hΓ hA'
  have huv := (hd.uniqU henv hΓ hB').sort_inv henv hΓ
  have hBu : env.HasType U Γ B (.sort u) :=
    (IsDefEq.sortDF (hB.sort_r henv.ordered hΓ.1) (hA.sort_r henv.ordered hΓ.1)
      (Eq.symm huv)).defeq hB
  exact ⟨_, H hΓ.1 hΓ.2 hA hBu hd⟩

/-- Under canonical `Eq`, statement (ii) at the front is exactly `TypedFront`, hence
`KeyFaithful` (`keyFaithful_iff_typedFront`). -/
theorem typeFront_iff_typedFront (henv : env.WF) (heq : env.HasCanonicalEq) :
    TypeFront env ↔ StrengtheningKripke.TypedFront env :=
  ⟨typedFront_of_typeFront henv heq, typeFront_of_typedFront henv⟩


end Lean4Lean.VEnv.StrengtheningTypingFront
