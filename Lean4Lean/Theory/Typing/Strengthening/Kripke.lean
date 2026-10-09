import Lean4Lean.Theory.Typing.Strengthening.Obstructions

/-! # The all-target observation model, its reflection problem, and a refutation

`KEq env U Γ a b`: the observation model of `HeadInjectivity/Model` quantified over every
well-formed target context, typed anchor and admissible variable-observation assignment.
It is sound for definitional equality (`KEq.sound`, from `WF.soundEnv`), it separates the
two test cases on which the fixed-target interpretation failed (`KEq.separates_variables`,
`KEq.separates_empty_domain_lambdas`), and it forgets the propositions of proofs
(`heterogeneous_reflection_false`), so a reflection statement must keep a common displayed
type: `FreshReflection`. `Cancel.of_freshReflection`: `FreshReflection` would give `Cancel`.
`keyFaithful_iff_typedFront`: assuming that lifted element classes reflect is already a
fixed-type strengthening statement.

Astra's third-round derivation (2026-10-08), kernel-checked outside this repository as
`StrengtheningKripke_2026-10-08.lean`, adapted.

**Refutation** (`freshReflection_false`, this attempt): `FreshReflection` is false in some
well-formed environments with canonical `Eq`. Extend any such environment by two
self-looping type constants `L₁ : Type := L₁`, `L₂ : Type := L₂` (a `mutualDef`, which
`VDecl.WF` admits). Neither has any observation, in any target and at any valuation: the
observations of a defined constant are those of its value, and the value is the constant
itself. So `KEq` identifies them, at the common type `Type`, in every context. But they are
not definitionally equal: every derivation in the extended environment is a derivation in the
environment where the two are axioms (their equations are reflexivities), and there both are
rigid heads, which head separation keeps apart. So the all-target observation model cannot
reflect definitional equality in environments with non-terminating definitions, which
`VEnv.WF` admits and which the theorem must cover. -/

namespace Lean4Lean
namespace VEnv.StrengtheningKripke
open VEnv VExpr VEnv.StrengtheningObstructions
open VEnv.Model

/-- All well-formed targets, all typed anchors, and all backed, typed variable
observations. Equality here is mutual subsumption, not equality of raw sets. -/
def KEq (env : VEnv) (U : Nat) (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∀ (Δ : List VExpr) (σ : VExpr.Subst) (S : ObSets),
    OnCtx Δ (env.IsType U) → Ctx.SubstEq env U Δ σ σ Γ →
    TV env U Δ Γ σ S →
    Ob.Sub (Obs env U Δ σ S a) (Obs env U Δ σ S b) ∧
    Ob.Sub (Obs env U Δ σ S b) (Obs env U Δ σ S a)

theorem KEq.sound {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (H : env.IsDefEqU U Γ a b) :
    KEq env U Γ a b := by
  obtain ⟨T, H⟩ := H
  intro Δ σ S hΔ hσ hS
  have Hs := (henv.soundEnv hΔ (H.strong henv.ordered hΓ)).1 σ σ S hσ hS hS
  exact ⟨Hs.1, Hs.2.1⟩

theorem KEq.symm (H : KEq env U Γ a b) : KEq env U Γ b a :=
  fun Δ σ S hΔ hσ hS => (H Δ σ S hΔ hσ hS).symm

theorem KEq.trans (H : KEq env U Γ a b) (H' : KEq env U Γ b c) :
    KEq env U Γ a c := by
  intro Δ σ S hΔ hσ hS
  have h := H Δ σ S hΔ hσ hS
  have h' := H' Δ σ S hΔ hσ hS
  exact ⟨h.1.trans h'.1, h'.2.trans h.2⟩

theorem proof_no_observations {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (hP : env.HasType U Γ P (.sort .zero))
    (ha : env.HasType U Γ a P) (hΔ : OnCtx Δ (env.IsType U))
    (hσ : Ctx.SubstEq env U Δ σ σ Γ) (hS : TV env U Δ Γ σ S) :
    ∀ o, ¬ Obs env U Δ σ S a o := by
  have ihP := (henv.soundEnv hΔ (hP.strong henv.ordered hΓ)).1 σ σ S hσ hS hS
  have iha := (henv.soundEnv hΔ (ha.strong henv.ordered hΓ)).1 σ σ S hσ hS hS
  intro o ho
  obtain ⟨τs, hτs, ht⟩ := iha.2.2.1 o ho
  exact ht.not_prop fun τ hτ => ⟨_, typedAt_sort_iff.1 (ihP.2.2.1 τ (hτs τ hτ))⟩

/-- KEq forgets proof TYPES: common typing must be retained in reflection. -/
theorem KEq.proofs {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (hP : env.HasType U Γ P (.sort .zero))
    (hQ : env.HasType U Γ Q (.sort .zero))
    (ha : env.HasType U Γ a P) (hb : env.HasType U Γ b Q) : KEq env U Γ a b := by
  intro Δ σ S hΔ hσ hS
  exact ⟨fun o ho => (proof_no_observations henv hΓ hP ha hΔ hσ hS o ho).elim,
    fun o ho => (proof_no_observations henv hΓ hQ hb hΔ hσ hS o ho).elim⟩

/-- Fresh target keys exist without a term of Q in the source context. -/
theorem fresh_key {env : VEnv} {U : Nat} (Γ : List VExpr) (Q : VExpr) :
    TypedElCls env U (Q :: Γ) (TyCls env U (Q :: Γ) Q.lift)
      (ElCls env U (Q :: Γ) (TyCls env U (Q :: Γ) Q.lift) (.bvar 0)) :=
  TypedElCls.of_hasType (show env.HasType U (Q :: Γ) (.bvar 0) Q.lift from .bvar .zero)

/-- This one observation suffices to distinguish the first variable from a
second variable with the SAME type. No identity/name observation is needed here. -/
def distinguishSets : ObSets :=
  fun i o => i = 0 ∧ o = .sort (fun _ => 0)

theorem distinguishSets_typed {env : VEnv} {U : Nat} {Δ : List VExpr}
    (σ : VExpr.Subst) :
    TV env U Δ [.sort (.succ .zero), .sort (.succ .zero)] σ distinguishSets := by
  constructor
  · intro i o ho w hw
    obtain ⟨_, rfl⟩ := ho
    cases hw
  · intro i A hL o ho
    obtain ⟨rfl, rfl⟩ := ho
    cases hL with
    | zero =>
      refine ⟨[.sort (fun _ => 1)], ?_, ?_⟩
      · intro τ hτ
        simp only [List.mem_singleton] at hτ
        subst τ
        exact .sort
      · exact .sort (by simp)

theorem KEq.separates_variables {env : VEnv} (henv : env.WF) (U : Nat) :
    ¬ KEq env U [.sort (.succ .zero), .sort (.succ .zero)] (.bvar 0) (.bvar 1) := by
  let Γ : List VExpr := [.sort (.succ .zero), .sort (.succ .zero)]
  have hs {Δ : List VExpr} : env.IsType U Δ (.sort (.succ .zero)) :=
    ⟨_, .sort trivial⟩
  have hΓ : OnCtx Γ (env.IsType U) := ⟨⟨trivial, hs⟩, hs⟩
  intro H
  obtain ⟨o, ho, _⟩ := (H Γ .id distinguishSets hΓ
    (Ctx.SubstEq.id henv.ordered hΓ) (distinguishSets_typed .id)).1
      _ (.bvar ⟨rfl, rfl⟩)
  have := (Obs.bvar_iff.mp ho).1
  contradiction

/-- Observing only the variable's type (or a chain computed from that type)
necessarily loses this distinction. This applies to ANY such observation set F. -/
theorem type_only_sets_collapse (F : VExpr → Ob → Prop)
    {env : VEnv} {U : Nat} {Δ : List VExpr} (σ : VExpr.Subst) :
    Obs env U Δ σ (fun _ => F (.sort (.succ .zero))) (.bvar 0) =
    Obs env U Δ σ (fun _ => F (.sort (.succ .zero))) (.bvar 1) := by
  funext o
  simp only [Obs.bvar_iff]

/-- In the fresh target, a lambda with constant Sort 0 body has an application
observation whose result is sort 0. The finite key list may be empty. -/
theorem fresh_lam_sort_observation {env : VEnv} {U : Nat} (Γ : List VExpr) (Q : VExpr) :
    Obs env U (Q :: Γ) (fun i => .bvar (i + 1)) .empty
      (.lam Q bodySort)
      (.app (TyCls env U (Q :: Γ) Q.lift)
        (ElCls env U (Q :: Γ) (TyCls env U (Q :: Γ) Q.lift) (.bvar 0))
        [] (.sort (fun _ => 0))) := by
  have he : Q.subst (fun i => .bvar (i + 1)) = Q.lift := by
    change Q.subst (.lift_r .id (.skip .refl)) = Q.lift
    rw [← VExpr.lift'_subst, VExpr.subst_id, ← VExpr.lift_eq_lift']
  rw [← he]
  apply Obs.lam (τs := []) (x := .bvar 0)
  · rw [he]
    exact fresh_key Γ Q
  · simp
  · simp
  · intro o ho
    cases ho
  · exact ElCls.self
  · exact .sort

/-- Any target admitting a typed anchor for Γ and a key for Q distinguishes
these abstractions. We choose the target Q::Γ, so no inhabitant in Γ is used. -/
theorem KEq.separates_empty_domain_lambdas {env : VEnv} (henv : env.WF)
    {U : Nat} {Γ : List VExpr} {Q : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (hQ : env.IsType U Γ Q) :
    ¬ KEq env U Γ (.lam Q bodySort) (.lam Q bodyPi) := by
  intro H
  have hΔ : OnCtx (Q :: Γ) (env.IsType U) := ⟨hΓ, hQ⟩
  have hσ : Ctx.SubstEq env U (Q :: Γ) (fun i => .bvar (i + 1))
      (fun i => .bvar (i + 1)) Γ := by
    exact (Ctx.SubstEq.id henv.ordered hΓ).skip henv.ordered
  obtain ⟨o, ho, hl⟩ := (H (Q :: Γ) _ .empty hΔ hσ TV.empty).1
    _ (fresh_lam_sort_observation Γ Q)
  obtain ⟨K, p, rfl, _, hp⟩ := hl.app_inv
  rw [hp.sort_inv] at ho
  obtain ⟨c, K', x, τs, p', he, _, _, _, _, _, hb⟩ := Obs.lam_iff.mp ho
  have hp' := (Ob.app.inj he).2.2.2
  rw [← hp'] at hb
  exact Model.forallE_not_sort hb

/-- The obstruction to transporting class-valued keys back is already a
restricted strengthening theorem, not an untyped injectivity fact. -/
def KeyFaithful (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q a b T⦄, OnCtx Γ (env.IsType U) → env.IsType U Γ Q →
    env.HasType U Γ a T → env.HasType U Γ b T →
    ElCls env U (Q :: Γ) (TyCls env U (Q :: Γ) T.lift) a.lift =
      ElCls env U (Q :: Γ) (TyCls env U (Q :: Γ) T.lift) b.lift →
    ElCls env U Γ (TyCls env U Γ T) a = ElCls env U Γ (TyCls env U Γ T) b

def TypedFront (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q a b T⦄, OnCtx Γ (env.IsType U) → env.IsType U Γ Q →
    env.HasType U Γ a T → env.HasType U Γ b T →
    env.IsDefEq U (Q :: Γ) a.lift b.lift T.lift → env.IsDefEq U Γ a b T

theorem keyFaithful_iff_typedFront {env : VEnv} (henv : env.WF) :
    KeyFaithful env ↔ TypedFront env := by
  constructor
  · intro hk U Γ Q a b T hΓ hQ ha hb H
    have he := hk hΓ hQ ha hb (ElCls.eq_of_defeq TyCls.self H)
    have hm : ElCls env U Γ (TyCls env U Γ T) a b := by
      rw [he]; exact ElCls.self
    exact ElCls.collapse henv.ordered hΓ ha TyCls.self hm
  · intro hf U Γ Q a b T hΓ hQ ha hb he
    have hm : ElCls env U (Q :: Γ) (TyCls env U (Q :: Γ) T.lift) a.lift b.lift := by
      rw [he]; exact ElCls.self
    have H := ElCls.collapse henv.ordered (show OnCtx (Q :: Γ) (env.IsType U) from ⟨hΓ, hQ⟩)
      (ha.weakN henv.ordered Ctx.LiftN.one) TyCls.self hm
    exact ElCls.eq_of_defeq TyCls.self (hf hΓ hQ ha hb H)

/-- A small reflecting fragment: the two closed type-former bodies, even when
observed only through constant abstractions over an arbitrary domain Q. -/
def testBody : Bool → VExpr
  | false => bodySort
  | true => bodyPi

theorem reflect_test_lambdas {env : VEnv} (henv : env.WF)
    {U : Nat} {Γ : List VExpr} {Q : VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) (hQ : env.IsType U Γ Q)
    (i j : Bool) (H : KEq env U Γ (.lam Q (testBody i)) (.lam Q (testBody j))) :
    env.IsDefEq U Γ (testBody i) (testBody j) (.sort (.succ .zero)) := by
  cases i <;> cases j
  · exact bodySort_typed
  · exact (KEq.separates_empty_domain_lambdas henv hΓ hQ H).elim
  · exact (KEq.separates_empty_domain_lambdas henv hΓ hQ H.symm).elim
  · exact bodyPi_typed

/-- A second reflecting fragment: independent variables at Sort 1. -/
theorem reflect_test_variables {env : VEnv} (henv : env.WF)
    (U : Nat) (i j : Fin 2)
    (H : KEq env U [.sort (.succ .zero), .sort (.succ .zero)] (.bvar i) (.bvar j)) :
    env.IsDefEq U [.sort (.succ .zero), .sort (.succ .zero)] (.bvar i) (.bvar j)
      (.sort (.succ .zero)) := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  have hi' : i = 0 ∨ i = 1 := by omega
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
  · exact .bvar .zero
  · exact (KEq.separates_variables henv U H).elim
  · exact (KEq.separates_variables henv U H.symm).elim
  · exact .bvar (.succ .zero)

def propId : VExpr := .forallE (.sort .zero) (.forallE (.bvar 0) (.bvar 1))
def propIdArrow : VExpr := .forallE propId propId.lift

theorem propId_typed {env : VEnv} {U : Nat} (Γ : List VExpr) :
    env.HasType U Γ propId (.sort .zero) := by
  have hinner : env.HasType U (.sort .zero :: Γ) (.forallE (.bvar 0) (.bvar 1))
      (.sort (.imax .zero .zero)) := .forallE (.bvar .zero) (.bvar (.succ .zero))
  have hi : env.HasType U (.sort .zero :: Γ) (.forallE (.bvar 0) (.bvar 1))
      (.sort .zero) := .defeqDF (IsDefEq.sortDF (l := .imax .zero .zero) (l' := .zero)
        ⟨trivial, trivial⟩ trivial rfl) hinner
  exact .defeqDF (IsDefEq.sortDF (l := .imax (.succ .zero) .zero) (l' := .zero)
    ⟨trivial, trivial⟩ trivial rfl) (HasType.forallE (HasType.sort trivial) hi)

theorem propIdArrow_typed {env : VEnv} (henv : env.Ordered) {U : Nat} (Γ : List VExpr) :
    env.HasType U Γ propIdArrow (.sort .zero) := by
  have hp := propId_typed (env := env) (U := U) Γ
  exact .defeqDF (IsDefEq.sortDF (l := .imax .zero .zero) (l' := .zero)
    ⟨trivial, trivial⟩ trivial rfl)
    (HasType.forallE hp (hp.weakN henv Ctx.LiftN.one))

/-- Even all targets and rich valuations do not reflect HETEROGENEOUS proof
equality. The failure is unconditional for every WF environment. -/
theorem heterogeneous_reflection_false {env : VEnv} (henv : env.WF) (U : Nat) :
    ∃ Γ a b P Q, OnCtx Γ (env.IsType U) ∧
      env.HasType U Γ a P ∧ env.HasType U Γ b Q ∧
      KEq env U Γ a b ∧ ¬ env.IsDefEqU U Γ a b := by
  let Γ := [propIdArrow, propId]
  have hΓ : OnCtx Γ (env.IsType U) :=
    ⟨⟨trivial, _, propId_typed []⟩, _, propIdArrow_typed henv.ordered [propId]⟩
  have ha : env.HasType U Γ (.bvar 1) propId := by
    simpa [Γ, propId, propIdArrow, lift, liftN, liftVar] using
      (HasType.bvar (env := env) (U := U) (Lookup.succ (A := propIdArrow)
        (Lookup.zero (Γ := []) (ty := propId))))
  have hb : env.HasType U Γ (.bvar 0) propIdArrow := by
    simpa [Γ, propId, propIdArrow, lift, liftN, liftVar] using
      (HasType.bvar (env := env) (U := U) (Lookup.zero (Γ := [propId]) (ty := propIdArrow)))
  refine ⟨Γ, .bvar 1, .bvar 0, propId, propIdArrow, hΓ, ha, hb,
    KEq.proofs henv hΓ (propId_typed Γ) (propIdArrow_typed henv.ordered Γ) ha hb, ?_⟩
  intro H
  have htypes := (IsDefEqU.of_l henv hΓ H ha).uniqU henv hΓ hb
  obtain ⟨u, hd⟩ := (htypes.forallE_inv henv hΓ).1
  exact IsDefEqU.sort_forallE_inv henv hΓ ⟨_, hd⟩

/-- The exact remaining semantic reflection obligation. Source terms need not
already be typed below; their COMMON larger-context type may use Q. -/
def FreshReflection (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q a b T⦄,
    OnCtx (Q :: Γ) (env.IsType U) →
    env.HasType U (Q :: Γ) a.lift T →
    env.HasType U (Q :: Γ) b.lift T →
    KEq env U (Q :: Γ) a.lift b.lift →
    env.IsDefEqU U Γ a b

theorem cancel_of_freshReflection {env : VEnv} (henv : env.WF)
    (hr : FreshReflection env) : Cancel env := by
  apply Cancel.of_front henv
  intro U Γ Q a b hΓ H
  obtain ⟨T, H⟩ := H
  exact hr hΓ H.hasType.1 H.hasType.2 (KEq.sound henv hΓ ⟨T, H⟩)

theorem joinRepair_of_freshReflection {env : VEnv} (henv : env.WF)
    (heq : env.HasCanonicalEq) (hr : FreshReflection env) :
    ∀ U, @JoinRepair (henv.params U) :=
  (cancel_iff_joinRepair henv heq).mp (cancel_of_freshReflection henv hr)


/-! ## `FreshReflection` is false in some well-formed environments with canonical `Eq` -/

section Refutation
open VEnv

/-- A self-looping type constant `L : Type := L`. -/
def loopVal (L : Name) : VDefVal :=
  { uvars := 0, type := .sort (.succ .zero), name := L, value := .const L [] }

theorem _root_.Lean4Lean.VExpr.stripLams_mkApps_app :
    ∀ (args : List VExpr) (f a : VExpr),
      (VExpr.mkApps (.app f a) args).stripLams = VExpr.mkApps (.app f a) args
  | [], _, _ => rfl
  | b :: args, f, a => VExpr.stripLams_mkApps_app args (.app f a) b

theorem _root_.Lean4Lean.VExpr.stripLams_mkApps_const (n : Name) (ls : List VLevel) :
    ∀ args : List VExpr, (VExpr.mkApps (.const n ls) args).stripLams = VExpr.mkApps (.const n ls) args
  | [] => rfl
  | a :: args => VExpr.stripLams_mkApps_app args (.const n ls) a

theorem _root_.Lean4Lean.VExpr.getAppFnArgs_go_fst (e : VExpr) :
    ∀ args, (VExpr.getAppFnArgs.go e args).1 = (VExpr.getAppFnArgs.go e []).1 := by
  induction e with
  | app f a ih => intro args; simp only [VExpr.getAppFnArgs.go]; rw [ih, ih [a]]
  | _ => intro args; rfl

/-- The head constant of a typed application spine is a constant of the environment. -/
theorem _root_.Lean4Lean.VEnv.HasType.getAppFn_const_mem {env : VEnv} (henv : env.WF)
    {U : Nat} : ∀ {Γ e T}, OnCtx Γ (env.IsType U) → env.HasType U Γ e T →
      e.getAppFnArgs.1 = .const c ls → ∃ ci, env.constants c = some ci := by
  intro Γ e
  induction e generalizing Γ with
  | app f a ih _ =>
    intro T hΓ H h
    obtain ⟨_, _, hf, _⟩ := H.app_inv henv.ordered hΓ
    refine ih hΓ hf ?_
    simpa only [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go, VExpr.getAppFnArgs_go_fst f [a]]
      using h
  | const c' ls' =>
    intro T hΓ H h
    simp only [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go, VExpr.const.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨ci, hci, -⟩ := H.const_inv henv.ordered hΓ
    exact ⟨ci, hci⟩
  | _ => intro T hΓ H h; simp [VExpr.getAppFnArgs, VExpr.getAppFnArgs.go] at h

/-- The head constant of a typed term, after stripping its lambdas and arguments, is a
constant of the environment. -/
theorem _root_.Lean4Lean.VEnv.HasType.head_const_mem {env : VEnv} (henv : env.WF)
    {U : Nat} : ∀ {Γ e T}, OnCtx Γ (env.IsType U) → env.HasType U Γ e T →
      e.stripLams.getAppFnArgs.1 = .const c ls → ∃ ci, env.constants c = some ci := by
  intro Γ e
  induction e generalizing Γ with
  | lam A b _ ih =>
    intro T hΓ H h
    obtain ⟨⟨_, hA⟩, _, hb⟩ := H.lam_inv henv.ordered hΓ
    have hΓ' : OnCtx (_ :: _) (env.IsType U) := ⟨hΓ, _, hA⟩
    exact ih hΓ' hb h
  | _ => intro T hΓ H h; exact HasType.getAppFn_const_mem henv hΓ H h

/-- A fresh name is a rigid head of every stored equation of a well-formed environment. -/
theorem _root_.Lean4Lean.VEnv.WF.rigid_of_fresh {env : VEnv} (henv : env.WF)
    (hfresh : env.constants L = none) : env.Rigid L := by
  intro df hdf ls h
  obtain ⟨ci, hci⟩ := HasType.head_const_mem henv (Γ := []) trivial
    (henv.ordered.defEqWF hdf).1 h
  rw [hfresh] at hci
  cases hci

theorem _root_.Lean4Lean.VEnv.addConsts_defeqs {env env' : VEnv} :
    ∀ {cis}, env.addConsts cis = some env' → env'.defeqs = env.defeqs
  | [], h => by cases h; rfl
  | _ :: _, h => by
    simp only [VEnv.addConsts, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨middle, hfirst, hrest⟩ := h
    exact (VEnv.addConsts_defeqs hrest).trans (VEnv.addConst_defeqs hfirst)

variable {env : VEnv} {L₁ L₂ : Name}

/-- The environment with the two looping constants and their equations. -/
structure LoopEnv (env : VEnv) (L₁ L₂ : Name) (env₁ env' : VEnv) : Prop where
  add : env.addConsts [loopVal L₁, loopVal L₂] = some env₁
  eq : env' = env₁.addDefEqs [loopVal L₁, loopVal L₂]

namespace LoopEnv
variable (H : LoopEnv env L₁ L₂ env₁ env')
include H

theorem defeqs₁ : env₁.defeqs = env.defeqs := VEnv.addConsts_defeqs H.add

theorem projections₁ : env₁.projections = env.projections := VEnv.addConsts_projections H.add
theorem eliminators₁ : env₁.eliminators = env.eliminators := VEnv.addConsts_eliminators H.add

theorem constants' : env'.constants = env₁.constants := by rw [H.eq]; rfl
theorem projections' : env'.projections = env₁.projections := by rw [H.eq]; rfl
theorem eliminators' : env'.eliminators = env₁.eliminators := by rw [H.eq]; rfl
theorem defeqs' : env'.defeqs = fun df =>
    df = (loopVal L₂).toDefEq ∨ df = (loopVal L₁).toDefEq ∨ env.defeqs df := by
  rw [H.eq]; funext df; simp [VEnv.addDefEqs, VEnv.addDefEq, H.defeqs₁]

theorem le₁ : env ≤ env₁ := VEnv.addConsts_le H.add
theorem le' : env₁ ≤ env' := by
  rw [H.eq]; exact VEnv.LE.trans VEnv.addDefEq_le VEnv.addDefEq_le
theorem le : env ≤ env' := VEnv.LE.trans H.le₁ H.le'

end LoopEnv

theorem loopEnv_exists (h₁ : env.constants L₁ = none) (h₂ : env.constants L₂ = none)
    (hne : L₁ ≠ L₂) : ∃ env₁ env', LoopEnv env L₁ L₂ env₁ env' := by
  obtain ⟨env₁, hadd⟩ := VEnv.exists_addConsts (env := env) (cis := [loopVal L₁, loopVal L₂])
    (by simp [loopVal, h₁, h₂]) (by simp [loopVal, hne])
  exact ⟨env₁, _, ⟨hadd, rfl⟩⟩

theorem sortOne_isType {env : VEnv} : env.IsType 0 [] (.sort (.succ .zero)) :=
  ⟨_, .sort trivial⟩

theorem LoopEnv.const₁ (H : LoopEnv env L₁ L₂ env₁ env') (_hne : L₁ ≠ L₂) :
    env₁.constants L₁ = some ⟨0, .sort (.succ .zero)⟩ :=
  VEnv.addConsts_constants H.add (loopVal L₁) (by simp)

theorem LoopEnv.const₂ (H : LoopEnv env L₁ L₂ env₁ env') :
    env₁.constants L₂ = some ⟨0, .sort (.succ .zero)⟩ :=
  VEnv.addConsts_constants H.add (loopVal L₂) (by simp)

theorem LoopEnv.typed₁ (H : LoopEnv env L₁ L₂ env₁ env') (hne : L₁ ≠ L₂) {E : VEnv}
    (hE : E.constants = env₁.constants) {U : Nat} {Γ : List VExpr} :
    E.HasType U Γ (.const L₁ []) (.sort (.succ .zero)) :=
  HasType.const (hE ▸ H.const₁ hne) (by simp) rfl

theorem LoopEnv.typed₂ (H : LoopEnv env L₁ L₂ env₁ env') {E : VEnv}
    (hE : E.constants = env₁.constants) {U : Nat} {Γ : List VExpr} :
    E.HasType U Γ (.const L₂ []) (.sort (.succ .zero)) :=
  HasType.const (hE ▸ H.const₂) (by simp) rfl

/-- The environment with the two looping definitions is well formed. -/
theorem LoopEnv.wf' (henv : env.WF) (H : LoopEnv env L₁ L₂ env₁ env') (hne : L₁ ≠ L₂) :
    env'.WF := by
  obtain ⟨ds, hds⟩ := henv
  refine ⟨_, H.eq ▸ VEnv.WF'.decl (VDecl.WF.mutualDef ?_ H.add ?_) hds⟩
  · intro ci hci
    simp only [List.mem_cons] at hci
    rcases hci with rfl | rfl | h
    · exact sortOne_isType
    · exact sortOne_isType
    · cases h
  · intro ci hci
    simp only [List.mem_cons] at hci
    rcases hci with rfl | rfl | h
    · exact H.typed₁ hne rfl
    · exact H.typed₂ rfl
    · cases h

/-- The environment with the two constants as axioms is well formed. -/
theorem LoopEnv.wf₁ (henv : env.WF) (H : LoopEnv env L₁ L₂ env₁ env') : env₁.WF := by
  obtain ⟨ds, hds⟩ := henv
  have h := H.add
  simp only [VEnv.addConsts, List.foldlM_cons, List.foldlM_nil, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨e₁, h₁, e₂, h₂, rfl⟩ := h
  exact ⟨_, .decl (.axiom (ci := (loopVal L₂).toVConstVal) sortOne_isType h₂)
    (.decl (.axiom (ci := (loopVal L₁).toVConstVal) sortOne_isType h₁) hds)⟩

theorem LoopEnv.canonicalEq (H : LoopEnv env L₁ L₂ env₁ env') (heq : env.HasCanonicalEq) :
    env'.HasCanonicalEq := heq.mono H.le

/-- Every derivation of the looping environment is a derivation of the axiom environment:
the two defining equations are reflexivities there. -/
theorem LoopEnv.toAxioms (H : LoopEnv env L₁ L₂ env₁ env') (hne : L₁ ≠ L₂)
    {U : Nat} {Γ : List VExpr} {a b A : VExpr}
    (D : env'.IsDefEq U Γ a b A) : env₁.IsDefEq U Γ a b A := by
  have hc := H.constants'
  have hp := H.projections'
  have he := H.eliminators'
  induction D with
  | bvar h => exact .bvar h
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF (hc ▸ h1) h2 h3 h4 h5
  | elimDF h1 h2 h3 h4 h5 h6 _ ih => exact .elimDF (he ▸ h1) h2 h3 h4 h5 h6 ih
  | appDF _ _ ih1 ih2 => exact .appDF ih1 ih2
  | projDF h1 h2 h3 h4 h5 h6 _ _ _ h10 h11 ih1 ih2 ih3 =>
    exact .projDF (hp ▸ h1) h2 h3 h4 h5 h6 ih1 ih2 ih3 h10 h11
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ ih1 ih2 => exact .beta ih1 ih2
  | eta _ ih => exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 =>
    rw [H.defeqs'] at h1
    rcases h1 with rfl | rfl | h1
    · have hls : _ = [] := List.length_eq_zero_iff.mp (by simpa [loopVal, VDefVal.toDefEq] using h3)
      subst hls
      exact H.typed₂ rfl
    · have hls : _ = [] := List.length_eq_zero_iff.mp (by simpa [loopVal, VDefVal.toDefEq] using h3)
      subst hls
      exact H.typed₁ hne rfl
    · exact .extra (H.defeqs₁ ▸ h1) h2 h3
  | elimIota h1 h2 h3 h4 h5 _ _ ih1 ih2 => exact .elimIota (he ▸ h1) h2 h3 h4 h5 ih1 ih2
  | projIota h1 _ h3 _ ih1 ih2 => exact .projIota (hp ▸ h1) ih1 h3 ih2
  | structEta h1 h2 h3 _ _ ih1 ih2 => exact .structEta (hp ▸ h1) h2 h3 ih1 ih2
  | unitLike h1 h2 h3 h4 _ _ ih1 ih2 => exact .unitLike (hp ▸ h1) h2 h3 h4 ih1 ih2

/-- The two looping constants are not definitionally equal. -/
theorem LoopEnv.not_defeq (henv : env.WF) (H : LoopEnv env L₁ L₂ env₁ env') (hne : L₁ ≠ L₂)
    (h₁ : env.constants L₁ = none) (h₂ : env.constants L₂ = none) :
    ¬ env'.IsDefEqU 0 [] (.const L₁ []) (.const L₂ []) := by
  rintro ⟨T, D⟩
  have henv₁ := H.wf₁ henv
  have D₁ : env₁.IsDefEqU 0 [] (.const L₁ []) (.const L₂ []) := ⟨_, H.toAxioms hne D⟩
  have chain : env₁.TypeChain 0 [] (.const L₁ []) (.const L₂ []) :=
    D₁.typeChain henv₁ trivial (H.typed₁ hne rfl)
  have hr₁ : env₁.Rigid L₁ := by
    intro df hdf ls h
    rw [H.defeqs₁] at hdf
    exact (henv.rigid_of_fresh h₁) df hdf ls h
  have hr₂ : env₁.Rigid L₂ := by
    intro df hdf ls h
    rw [H.defeqs₁] at hdf
    exact (henv.rigid_of_fresh h₂) df hdf ls h
  exact hne (henv₁.headSeparation.rigid_heads (args := []) (args' := [])
    (show OnCtx [] (env₁.IsType 0) from trivial) hr₁ hr₂ chain).1

/-- A looping constant has no observation, in any target and at any valuation. -/
theorem LoopEnv.no_observation (henv : env.WF) (H : LoopEnv env L₁ L₂ env₁ env') (hne : L₁ ≠ L₂)
    (h₁ : env.constants L₁ = none) (h₂ : env.constants L₂ = none) {L : Name}
    (hL : L = L₁ ∨ L = L₂)
    {U : Nat} {Δ : List VExpr} {σ : VExpr.Subst} {S : ObSets} {o : Ob} :
    ¬ Obs env' U Δ σ S (.const L []) o := by
  have henv' := H.wf' henv hne
  have hfresh : env.constants L = none := by rcases hL with rfl | rfl <;> assumption
  have hrule : env'.defeqs (loopVal L).toDefEq := by
    rw [H.defeqs']; rcases hL with rfl | rfl <;> simp
  have hnotRigid : ¬ env'.Rigid L := fun hr => hr _ hrule [] rfl
  intro Hobs
  generalize he : VExpr.const L [] = e at Hobs
  induction Hobs with
  | const hrig => exact hnotRigid ((VExpr.const.inj he.symm).1 ▸ hrig)
  | delta hdf hlhs hci _ _ _ _ ih =>
    obtain ⟨rfl, rfl⟩ := VExpr.const.inj he.symm
    rw [H.defeqs'] at hdf
    rcases hdf with rfl | rfl | hdf
    · have h' : VExpr.const L₂ [] = VExpr.const _ [] := hlhs
      obtain rfl := (VExpr.const.inj h').1
      exact ih rfl
    · have h' : VExpr.const L₁ [] = VExpr.const _ [] := hlhs
      obtain rfl := (VExpr.const.inj h').1
      exact ih rfl
    · have := henv.rigid_of_fresh hfresh _ hdf
      rw [hlhs] at this
      exact this _ rfl
  | ctor hctor =>
    obtain ⟨rfl, rfl⟩ := VExpr.const.inj he.symm
    rcases hctor with ⟨df, hdf, hmajor⟩ | ⟨b, schema, owner, rule, hreg, hgen, hname⟩
    · exact hnotRigid (henv'.installed_constructor_rigid hdf hmajor)
    · exact hnotRigid (hname ▸ henv'.case_constructor_rigid hreg hgen)
  | projCtor hproj hname =>
    obtain ⟨rfl, rfl⟩ := VExpr.const.inj he.symm
    rw [H.projections', H.projections₁] at hproj
    have := henv.ordered.projectionConstructor hproj
    rw [hname, hfresh] at this
    cases this
  | famTy hrig =>
    obtain ⟨rfl, rfl⟩ := VExpr.const.inj he.symm
    exact hnotRigid hrig
  | famDom hrig =>
    obtain ⟨rfl, rfl⟩ := VExpr.const.inj he.symm
    exact hnotRigid hrig
  | rule hdf hlhs =>
    obtain ⟨rfl, rfl⟩ := VExpr.const.inj he.symm
    rw [H.defeqs'] at hdf
    rcases hdf with rfl | rfl | hdf
    · have := congrArg (fun e => e.stripLams.getAppFnArgs.2) hlhs
      simp only [VExpr.stripLams_wrapLams, VExpr.stripLams_mkApps_const,
        VExpr.getAppFnArgs_mkApps_const] at this
      have h0 : (loopVal L₂).toDefEq.lhs.stripLams.getAppFnArgs.2 = [] := rfl
      rw [h0] at this
      exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _) this.symm
    · have := congrArg (fun e => e.stripLams.getAppFnArgs.2) hlhs
      simp only [VExpr.stripLams_wrapLams, VExpr.stripLams_mkApps_const,
        VExpr.getAppFnArgs_mkApps_const] at this
      have h0 : (loopVal L₁).toDefEq.lhs.stripLams.getAppFnArgs.2 = [] := rfl
      rw [h0] at this
      exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _) this.symm
    · exact henv.rigid_of_fresh hfresh _ hdf _
        (by rw [hlhs, VExpr.stripLams_wrapLams_mkApps_head])
  | _ => cases he

/-- **`FreshReflection` fails.** Every well-formed environment with canonical `Eq` extends,
by two self-looping type constants, to one in which the all-target observation model
identifies two definitionally distinct closed types at the common type `Type`. -/
theorem freshReflection_false (henv : env.WF) (heq : env.HasCanonicalEq)
    (h₁ : env.constants L₁ = none) (h₂ : env.constants L₂ = none) (hne : L₁ ≠ L₂) :
    ∃ env' : VEnv, env'.WF ∧ env'.HasCanonicalEq ∧ ¬ FreshReflection env' := by
  obtain ⟨env₁, env', H⟩ := loopEnv_exists h₁ h₂ hne
  have henv' := H.wf' henv hne
  refine ⟨env', henv', H.canonicalEq heq, fun hr => ?_⟩
  have hΓ : OnCtx [VExpr.sort .zero] (env'.IsType 0) := ⟨⟨⟩, _, .sort trivial⟩
  have hc : env'.constants = env₁.constants := H.constants'
  have hK : KEq env' 0 [.sort .zero] (VExpr.const L₁ []).lift (VExpr.const L₂ []).lift := by
    intro Δ σ S _ _ _
    constructor
    · intro o ho
      exact (H.no_observation henv hne h₁ h₂ (.inl rfl) ho).elim
    · intro o ho
      exact (H.no_observation henv hne h₁ h₂ (.inr rfl) ho).elim
  exact H.not_defeq henv hne h₁ h₂
    (hr hΓ (H.typed₁ hne hc) (H.typed₂ hc) hK)

end Refutation

end VEnv.StrengtheningKripke
end Lean4Lean
