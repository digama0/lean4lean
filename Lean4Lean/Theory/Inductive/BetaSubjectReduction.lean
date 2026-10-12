import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.IotaLemmas

/-! # Subject reduction for beta

`VEnv.SimAt env U Γ x x'`: `x'` is definitionally equal to `x` at every type of `x`. Beta
reduction (`VExpr.BetaRed`, the compatible closure of the contraction of a beta redex) is a
`SimAt` relation in every well-formed context of an environment with subject reduction for a
single beta step (`VExpr.BetaRed.simAt`). That hypothesis, `VEnv.BetaSubjectReduction`, holds
in every well-formed environment (`VEnv.WF.betaSubjectReduction`), by unique typing and
injectivity of Pi types (`IsDefEq.uniq`, `IsDefEqU.forallE_inv`).
-/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv}

/-- `x'` is definitionally equal to `x` at every type of `x`. -/
def SimAt (env : VEnv) (U : Nat) (Γ : List VExpr) (x x' : VExpr) : Prop :=
  ∀ T, env.HasType U Γ x T → env.IsDefEq U Γ x x' T

/-- Subject reduction for a single beta step. It is a consequence of
injectivity of Pi types; `VEnv.WF.betaSubjectReduction` proves it for well-formed
environments. -/
def BetaSubjectReduction (env : VEnv) (U : Nat) : Prop :=
  ∀ Γ A b a, OnCtx Γ (env.IsType U) → env.SimAt U Γ (.app (.lam A b) a) (b.inst a)

theorem SimAt.refl : env.SimAt U Γ x x := fun _ h => h

theorem SimAt.trans (h1 : env.SimAt U Γ x y) (h2 : env.SimAt U Γ y z) : env.SimAt U Γ x z :=
  fun _ h => let h1 := h1 _ h; h1.trans (h2 _ h1.hasType.2)

theorem SimAt.app (henv : env.OrderedStrong) (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.SimAt U Γ f f') (ha : env.SimAt U Γ a a') :
    env.SimAt U Γ (.app f a) (.app f' a') := by
  intro T H
  replace H := (H.strong henv hΓ).hasType'.1
  generalize eq : true = b, eq' : f.app a = e' at H
  induction H with cases eq
  | defeq _ h2 _ _ _ _ _ ih => exact .defeqDF h2.defeq (ih hΓ hf ha rfl eq')
  | base H =>
    subst eq'
    let .app _ _ _ _ _ h1 h2 _ := H
    exact .appDF (hf _ h1.hasType) (ha _ h2.hasType)

theorem SimAt.lam (henv : env.OrderedStrong) (hΓ : OnCtx Γ (env.IsType U))
    (hd : env.SimAt U Γ d d')
    (hb : OnCtx (d :: Γ) (env.IsType U) → env.SimAt U (d :: Γ) b b') :
    env.SimAt U Γ (.lam d b) (.lam d' b') := by
  intro T H
  replace H := (H.strong henv hΓ).hasType'.1
  generalize eq : true = bb, eq' : VExpr.lam d b = e' at H
  induction H with cases eq
  | defeq _ h2 _ _ _ _ _ ih => exact .defeqDF h2.defeq (ih hΓ hd hb rfl eq')
  | base H =>
    subst eq'
    let .lam _ _ h1 _ h2 _ := H
    exact .lamDF (hd _ h1.hasType) (hb ⟨hΓ, _, h1.hasType⟩ _ h2.hasType)

theorem SimAt.forallE (henv : env.OrderedStrong) (hΓ : OnCtx Γ (env.IsType U))
    (hd : env.SimAt U Γ d d')
    (hb : OnCtx (d :: Γ) (env.IsType U) → env.SimAt U (d :: Γ) b b') :
    env.SimAt U Γ (.forallE d b) (.forallE d' b') := by
  intro T H
  replace H := (H.strong henv hΓ).hasType'.1
  generalize eq : true = bb, eq' : VExpr.forallE d b = e' at H
  induction H with cases eq
  | defeq _ h2 _ _ _ _ _ ih => exact .defeqDF h2.defeq (ih hΓ hd hb rfl eq')
  | base H =>
    subst eq'
    let .forallE _ _ h1 h2 := H
    exact .forallEDF (hd _ h1.hasType) (hb ⟨hΓ, _, h1.hasType⟩ _ h2.hasType)

theorem SimAt.proj (henv : env.OrderedStrong) (hΓ : OnCtx Γ (env.IsType U))
    (hm : env.SimAt U Γ m m') :
    env.SimAt U Γ (.proj typeName index m) (.proj typeName index m') := by
  intro T H
  replace H := (H.strong henv hΓ).hasType'.1
  generalize eq : true = bb, eq' : VExpr.proj typeName index m = e' at H
  induction H with cases eq
  | defeq _ h2 _ _ _ _ _ ih => exact .defeqDF h2.defeq (ih hΓ hm rfl eq')
  | base H =>
    subst eq'
    let .proj hinfo hlevels huvars hparams hindices hfield _ hfieldTyping hmajorEq hmajor
      hclosed hguard := H
    exact .projDF hinfo hlevels huvars hparams hindices hfield hfieldTyping.hasType
      hmajorEq.defeq (hmajorEq.defeq.trans (hm _ hmajor.hasType)) hclosed hguard

theorem SimAt.mkApps (henv : env.OrderedStrong) (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.SimAt U Γ f f') (has : List.Forall₂ (env.SimAt U Γ) as as') :
    env.SimAt U Γ (VExpr.mkApps f as) (VExpr.mkApps f' as') := by
  induction has generalizing f f' with
  | nil => exact hf
  | cons ha _ ih => exact ih (hf.app henv hΓ ha)

theorem HasType.mkApps_head (henv : env.OrderedStrong) (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {as : List VExpr} {f T : VExpr}, env.HasType U Γ (VExpr.mkApps f as) T →
      ∃ T', env.HasType U Γ f T'
  | [], _, _, h => ⟨_, h⟩
  | a :: as, f, _, h =>
    let ⟨_, h⟩ := HasType.mkApps_head henv hΓ (as := as) (f := .app f a) h
    let ⟨_, _, h, _⟩ := HasType.app_inv henv hΓ h
    ⟨_, h⟩

theorem SimAt.forall₂_refl : ∀ (as : List VExpr), List.Forall₂ (env.SimAt U Γ) as as
  | [] => .nil
  | _ :: as => .cons SimAt.refl (SimAt.forall₂_refl as)

theorem WF.betaSubjectReduction (henv : VEnv.WF env) : env.BetaSubjectReduction U := by
  intro Γ A b a hΓ T H
  obtain ⟨A', B', hf, ha⟩ := H.app_inv henv hΓ
  -- `T` agrees with the codomain of the application rule.
  have hT : env.IsDefEqU U Γ (B'.inst a) T :=
    let ⟨_, h⟩ := IsDefEq.uniq henv hΓ (.appDF hf ha) H; ⟨_, h⟩
  obtain ⟨B, hB, hb⟩ := HasType.lam_inv_forallE henv hΓ hf
  obtain ⟨⟨_, hAA'⟩, _, hBB'⟩ := IsDefEqU.forallE_inv henv hΓ hB
  have ha' : env.HasType U Γ a A := .defeqDF hAA'.symm ha
  have hbeta : env.IsDefEq U Γ (.app (.lam A b) a) (b.inst a) (B.inst a) := .beta hb ha'
  have hBinst : env.IsDefEqU U Γ (B.inst a) (B'.inst a) :=
    IsDefEqU.instN henv.ordered .zero ⟨_, hBB'⟩ ha'
  exact (hBinst.trans henv hΓ hT).defeqDF henv hΓ hbeta

end VEnv

namespace VExpr

/-- Beta reduction: the reflexive-transitive compatible closure of the
contraction of a beta redex. -/
inductive BetaRed : VExpr → VExpr → Prop
  | refl : BetaRed e e
  | trans : BetaRed e₁ e₂ → BetaRed e₂ e₃ → BetaRed e₁ e₃
  | app : BetaRed f f' → BetaRed a a' → BetaRed (.app f a) (.app f' a')
  | lam : BetaRed d d' → BetaRed b b' → BetaRed (.lam d b) (.lam d' b')
  | forallE : BetaRed d d' → BetaRed b b' → BetaRed (.forallE d b) (.forallE d' b')
  | proj : BetaRed m m' → BetaRed (.proj n i m) (.proj n i m')
  | beta : BetaRed (.app (.lam A b) a) (b.inst a)

namespace BetaRed

theorem instN (H : BetaRed e e') (v : VExpr) (k : Nat) :
    BetaRed (e.inst v k) (e'.inst v k) := by
  induction H generalizing k with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans (ih1 k) (ih2 k)
  | app _ _ ih1 ih2 => exact .app (ih1 k) (ih2 k)
  | lam _ _ ih1 ih2 => exact .lam (ih1 k) (ih2 (k + 1))
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 k) (ih2 (k + 1))
  | proj _ ih => exact .proj (ih k)
  | @beta A b a => rw [inst0_inst_hi]; exact .beta

theorem instL (H : BetaRed e e') (ls : List VLevel) : BetaRed (e.instL ls) (e'.instL ls) := by
  induction H with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih
  | beta => rw [instL_instN]; exact .beta

theorem mkApps (hf : BetaRed f f') (has : List.Forall₂ BetaRed as as') :
    BetaRed (VExpr.mkApps f as) (VExpr.mkApps f' as') := by
  induction has generalizing f f' with
  | nil => exact hf
  | cons ha _ ih => exact ih (.app hf ha)

theorem forall₂_refl : ∀ (as : List VExpr), List.Forall₂ BetaRed as as
  | [] => .nil
  | _ :: as => .cons .refl (forall₂_refl as)

theorem forallE_inv (H : BetaRed (.forallE d b) y) :
    ∃ d' b', y = .forallE d' b' ∧ BetaRed d d' ∧ BetaRed b b' := by
  generalize hx : VExpr.forallE d b = x at H
  induction H generalizing d b with
  | refl => subst hx; exact ⟨_, _, rfl, .refl, .refl⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨d1, b1, rfl, h1, h2⟩ := ih1 hx
    obtain ⟨d2, b2, rfl, h3, h4⟩ := ih2 rfl
    exact ⟨_, _, rfl, h1.trans h3, h2.trans h4⟩
  | forallE h1 h2 => cases hx; exact ⟨_, _, rfl, h1, h2⟩
  | app | lam | proj | beta => cases hx

/-- Full beta reduction of a lambda telescope applied to at least as many
arguments as it has binders. -/
theorem mkApps_wrapLams :
    ∀ (doms : List VExpr) (body : VExpr) (args : List VExpr), doms.length ≤ args.length →
      BetaRed (VExpr.mkApps (VExpr.wrapLams doms body) args)
        (VExpr.mkApps (body.instOuter (args.take doms.length)) (args.drop doms.length))
  | [], body, args, _ => by simpa [VExpr.wrapLams] using BetaRed.refl
  | _ :: _, _, [], h => by simp at h
  | d :: ds, body, a :: rest, h => by
    simp only [List.length_cons, Nat.add_le_add_iff_right] at h
    have h1 : BetaRed (VExpr.mkApps (VExpr.wrapLams (d :: ds) body) (a :: rest))
        (VExpr.mkApps ((VExpr.wrapLams ds body).inst a) rest) :=
      BetaRed.mkApps (f := .app (.lam d (VExpr.wrapLams ds body)) a) (as := rest)
        .beta (forall₂_refl rest)
    rw [VExpr.wrapLams_inst, Nat.zero_add] at h1
    have h2 := mkApps_wrapLams (VExpr.instDomains ds a 0) (body.inst a ds.length) rest
      (by simpa using h)
    simp only [VExpr.instDomains_length] at h2
    have hlen : (rest.take ds.length).length = ds.length := by simp; omega
    simpa [List.take_succ_cons, VExpr.instOuter_cons, hlen] using h1.trans h2

/-- In a well-formed context, beta reduction is a definitional equality at
every type of the reduced term. -/
theorem simAt {env : VEnv} {U : Nat} (henv : env.OrderedStrong)
    (hβ : env.BetaSubjectReduction U) {x x' : VExpr} (H : BetaRed x x') :
    ∀ {Γ : List VExpr}, OnCtx Γ (env.IsType U) → env.SimAt U Γ x x' := by
  induction H with
  | refl => intro _ _; exact VEnv.SimAt.refl
  | trans _ _ ih1 ih2 => intro _ hΓ; exact (ih1 hΓ).trans (ih2 hΓ)
  | app _ _ ih1 ih2 => intro _ hΓ; exact VEnv.SimAt.app henv hΓ (ih1 hΓ) (ih2 hΓ)
  | lam _ _ ih1 ih2 =>
    intro _ hΓ; exact VEnv.SimAt.lam henv hΓ (ih1 hΓ) fun hΓ' => ih2 hΓ'
  | forallE _ _ ih1 ih2 =>
    intro _ hΓ; exact VEnv.SimAt.forallE henv hΓ (ih1 hΓ) fun hΓ' => ih2 hΓ'
  | proj _ ih => intro _ hΓ; exact VEnv.SimAt.proj henv hΓ (ih hΓ)
  | beta => intro Γ hΓ; exact hβ Γ _ _ _ hΓ

end BetaRed
end VExpr
end Lean4Lean
