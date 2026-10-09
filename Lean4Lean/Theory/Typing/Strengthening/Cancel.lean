import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.Typing.Injectivity

/-! # Context strengthening: the statement and its reduction to constant abstractions

`VEnv.Strengthening`: an equation between two lifted expressions in a context extended by
`n` binders (inserted below `k` binders) already holds in the smaller context. It is false
in some well-formed environments (the two-dependent-singleton countermodel of
section 5.1 of the design notes); whether it holds in every well-formed environment with
canonical `Eq` is open (section 5 of the design notes).

This file proves, for every well-formed environment, that the full statement is equivalent to
two simpler ones:

* `Front`: removal of one binder at the front of the context;
* `Cancel`: cancellation of constant abstractions, `Γ ⊢ λ Q. a↑ ≡ λ Q. b↑` implies `Γ ⊢ a ≡ b`,
  stated in a single well-formed context.

It also proves the retraction cases (an inhabited binder is removed by substitution, with no
hypothesis on the environment) and the typed form of descent, `IsDefEq.weakN_iff'`.

The reduction to `Cancel` is a second-opinion derivation by Astra (gpt-6-astra, 2026-10-08),
kernel-checked outside this repository as `StrengtheningPartial_2026-10-08.lean` and adapted
here. -/

namespace Lean4Lean
namespace VEnv
open VExpr

variable {env : VEnv} {U : Nat}

/-- Context strengthening for definitional equality: an equation between two
lifted expressions in a context extended by `n` binders (inserted below `k`
binders) already holds in the smaller context.

This is an explicit hypothesis on the environment, not a theorem: it fails in
some well-formed environments (the two-dependent-singleton countermodel in
section 5.1 of the design notes, which uses singleton `Prop` families with
large elimination). It is also not monotone in the environment: adding
constants can break it. Whether it holds in every well-formed environment with
canonical `Eq` is open; see `VEnv.Cancel` for the equivalent one-context form. -/
def Strengthening (env : VEnv) : Prop :=
  ∀ ⦃U n k Γ Γ' e1 e2⦄, Ctx.LiftN n k Γ Γ' → OnCtx Γ' (env.IsType U) →
    env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) → env.IsDefEqU U Γ e1 e2

/-- Strengthening across one binder at the front of the context. -/
def Front (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q a b⦄, OnCtx (Q :: Γ) (env.IsType U) →
    env.IsDefEqU U (Q :: Γ) a.lift b.lift → env.IsDefEqU U Γ a b

/-- Cancellation of constant abstractions: two constant functions with the same domain that
are definitionally equal have definitionally equal values. Equivalent to `Strengthening` in
every well-formed environment (`strengthening_iff_cancel`); this is the form in which the
open problem is stated, in one well-formed context, with no hypothesis that `a` or `b` is
typable in `Γ`, and without an inhabitant of `Q`. -/
def Cancel (env : VEnv) : Prop :=
  ∀ ⦃U Γ Q a b⦄, OnCtx Γ (env.IsType U) →
    env.IsDefEqU U Γ (.lam Q a.lift) (.lam Q b.lift) →
    env.IsDefEqU U Γ a b

/-- Equal abstractions with the same domain have equal bodies in the extended context. The
chain is `b₁ ≡ (λ A. b₁)↑ 0 ≡ (λ A. b₂)↑ 0 ≡ b₂`; no strengthening is involved. -/
theorem IsDefEqU.lam_body (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEqU U Γ (.lam A b₁) (.lam A b₂)) :
    env.IsDefEqU U (A :: Γ) b₁ b₂ := by
  obtain ⟨T, H⟩ := H
  obtain ⟨⟨u, hA⟩, B₁, hb₁⟩ := H.hasType.1.lam_inv henv.ordered hΓ
  obtain ⟨_, B₂, hb₂⟩ := H.hasType.2.lam_inv henv.ordered hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, u, hA⟩
  have hL : env.HasType U Γ (.lam A b₁) (.forallE A B₁) := .lamDF hA hb₁
  have hE := (IsDefEqU.of_l henv hΓ ⟨T, H⟩ hL).weakN henv.ordered (Ctx.LiftN.one (A := A))
  have hv : env.HasType U (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have hApp := IsDefEq.appDF hE hv
  have beta₁ := IsDefEq.beta (hb₁.weakN henv.ordered (Ctx.LiftN.succ Ctx.LiftN.one)) hv
  have beta₂ := IsDefEq.beta (hb₂.weakN henv.ordered (Ctx.LiftN.succ Ctx.LiftN.one)) hv
  have Hout := (IsDefEqU.trans henv hΓA ⟨_, beta₁.symm⟩ ⟨_, hApp⟩).trans henv hΓA ⟨_, beta₂⟩
  simpa only [lift, liftN, inst_liftN_bvar] using Hout

/-- Equal abstractions have equal domains. -/
theorem IsDefEqU.lam_domain (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : env.IsDefEqU U Γ (.lam A₁ b₁) (.lam A₂ b₂)) :
    ∃ u, env.IsDefEq U Γ A₁ A₂ (.sort u) := by
  obtain ⟨T, H⟩ := H
  obtain ⟨⟨u₁, hA₁⟩, B₁, hb₁⟩ := H.hasType.1.lam_inv henv.ordered hΓ
  obtain ⟨⟨u₂, hA₂⟩, B₂, hb₂⟩ := H.hasType.2.lam_inv henv.ordered hΓ
  have hl : env.HasType U Γ (.lam A₁ b₁) (.forallE A₁ B₁) := .lamDF hA₁ hb₁
  have hr : env.HasType U Γ (.lam A₂ b₂) (.forallE A₂ B₂) := .lamDF hA₂ hb₂
  have e := IsDefEqU.of_l henv hΓ ⟨_, H⟩ hl
  exact ((e.uniqU henv hΓ hr).forallE_inv henv hΓ).1

/-- Removing an inhabited front binder is substitution; no hypothesis on the environment
beyond `Ordered`, and the equation's type need not avoid the binder. -/
theorem IsDefEqU.strengthen_inhabited (henv : env.Ordered) (hq : env.HasType U Γ q Q)
    (H : env.IsDefEqU U (Q :: Γ) a.lift b.lift) : env.IsDefEqU U Γ a b := by
  simpa only [inst_lift] using H.instN henv Ctx.InstN.zero hq

/-- Removing a block of binders along a typed retraction `σ` of the larger context onto the
smaller one. -/
theorem IsDefEqU.retract (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (hσ : Ctx.SubstEq env U Γ σ σ Γ')
    (ha : (a.liftN n k).subst σ = a) (hb : (b.liftN n k).subst σ = b)
    (H : env.IsDefEqU U Γ' (a.liftN n k) (b.liftN n k)) : env.IsDefEqU U Γ a b := by
  simpa only [ha, hb] using H.subst henv hσ hΓ

/-- The inhabited case of `Cancel`. -/
theorem Cancel.inhabited (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hq : env.HasType U Γ q Q)
    (H : env.IsDefEqU U Γ (.lam Q a.lift) (.lam Q b.lift)) : env.IsDefEqU U Γ a b :=
  IsDefEqU.strengthen_inhabited henv.ordered hq (IsDefEqU.lam_body henv hΓ H)

theorem Front.of_cancel (hc : Cancel env) : Front env := by
  intro U Γ Q a b hΓ H
  obtain ⟨hΓ, u, hQ⟩ := hΓ
  obtain ⟨T, H⟩ := H
  exact hc hΓ ⟨_, .lamDF hQ H⟩

theorem Cancel.of_front (henv : env.WF) (hf : Front env) : Cancel env := by
  intro U Γ Q a b hΓ H
  obtain ⟨T, hT⟩ := H
  have hQ := (hT.hasType.1.lam_inv henv.ordered hΓ).1
  exact hf ⟨hΓ, hQ⟩ (IsDefEqU.lam_body henv hΓ ⟨T, hT⟩)

/-- Removing a block of binders at the front, one at a time. -/
theorem Front.block (hf : Front env) {As : List VExpr}
    (hΓ : OnCtx (As ++ Γ) (env.IsType U))
    (H : env.IsDefEqU U (As ++ Γ) (a.liftN As.length) (b.liftN As.length)) :
    env.IsDefEqU U Γ a b := by
  induction As with
  | nil => simpa using H
  | cons Q As ih =>
    apply ih hΓ.1
    apply hf (a := a.liftN As.length) (b := b.liftN As.length) hΓ
    simpa [lift, liftN'_liftN_hi, Nat.add_comm] using H

/-- Fixed-type descent from existential descent, given a descent operation for the same
insertion and well-formedness of both contexts. The type `T` is recovered by unique typing
and a second descent. -/
theorem IsDefEq.weakN_inv_of_down (henv : env.WF) (W : Ctx.LiftN n k Γ Γ')
    (hΓ : OnCtx Γ (env.IsType U)) (hΓ' : OnCtx Γ' (env.IsType U))
    (down : ∀ {a b}, env.IsDefEqU U Γ' (a.liftN n k) (b.liftN n k) → env.IsDefEqU U Γ a b)
    (H : env.IsDefEq U Γ' (a.liftN n k) (b.liftN n k) (T.liftN n k)) :
    env.IsDefEq U Γ a b T := by
  obtain ⟨S, hS⟩ := down ⟨_, H⟩
  have hST := (hS.weakN henv.ordered W).uniqU henv hΓ' H.symm
  exact (down hST).defeqDF henv hΓ hS

/-- The front case gives every insertion, together with well-formedness of the smaller
context. Induction on the insertion: the measure is `(k, n)` lexicographically; the successor
case abstracts the equation with `lamDF`, descends by the induction hypothesis and reopens the
abstraction with `IsDefEqU.lam_body`. -/
theorem Front.liftN (henv : env.WF) (hf : Front env) (W : Ctx.LiftN n k Γ Γ')
    (hΓ' : OnCtx Γ' (env.IsType U)) :
    OnCtx Γ (env.IsType U) ∧
    ∀ {a b}, env.IsDefEqU U Γ' (a.liftN n k) (b.liftN n k) → env.IsDefEqU U Γ a b := by
  induction W with
  | zero As hn =>
    subst n
    exact ⟨hΓ'.of_append, fun H => hf.block hΓ' H⟩
  | @succ k Γ Γ' A W ih =>
    obtain ⟨hΓ, down⟩ := ih hΓ'.1
    obtain ⟨u, hA'⟩ := hΓ'.2
    have hA : env.HasType U Γ A (.sort u) :=
      IsDefEq.weakN_inv_of_down henv W hΓ hΓ'.1 down hA'
    refine ⟨⟨hΓ, u, hA⟩, ?_⟩
    intro a b H
    obtain ⟨T, H⟩ := H
    have HL : env.IsDefEqU U Γ (.lam A a) (.lam A b) := down ⟨_, IsDefEq.lamDF hA' H⟩
    exact IsDefEqU.lam_body henv hΓ HL

theorem Strengthening.of_front (henv : env.WF) (hf : Front env) : env.Strengthening :=
  fun _ _ _ _ _ _ _ W hΓ' H => (hf.liftN henv W hΓ').2 H

theorem Strengthening.front (hs : env.Strengthening) : Front env :=
  fun _ _ _ _ _ hΓ H => hs Ctx.LiftN.one hΓ H

theorem Strengthening.cancel (henv : env.WF) (hs : env.Strengthening) : Cancel env :=
  Cancel.of_front henv hs.front

theorem Strengthening.of_cancel (henv : env.WF) (hc : Cancel env) : env.Strengthening :=
  Strengthening.of_front henv (Front.of_cancel hc)

/-- In a well-formed environment, strengthening is equivalent to cancellation of constant
abstractions. -/
theorem strengthening_iff_cancel (henv : env.WF) : env.Strengthening ↔ Cancel env :=
  ⟨Strengthening.cancel henv, Strengthening.of_cancel henv⟩

theorem strengthening_iff_front (henv : env.WF) : env.Strengthening ↔ Front env :=
  ⟨Strengthening.front, Strengthening.of_front henv⟩

/-! ## Consequences of `Strengthening`: the former consumers -/

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ : OnCtx Γ' (env.IsType U)) in
/-- Inverse weakening for definitional equality. The `.2` direction is the
true `IsDefEqU.weakN`; the `.1` direction is exactly the environment
hypothesis `VEnv.Strengthening`. -/
theorem IsDefEqU.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) ↔ env.IsDefEqU U Γ e1 e2 :=
  ⟨hs W hΓ, fun h => h.weakN henv.ordered W⟩

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ : OnCtx Γ' (env.IsType U)) in
theorem _root_.Lean4Lean.VExpr.WF.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    VExpr.WF env U Γ' (e.liftN n k) ↔ VExpr.WF env U Γ e := IsDefEqU.weakN_iff henv hs hΓ W

theorem IsDefEq.skips (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ : OnCtx Γ' (env.IsType U))
    (W : Ctx.LiftN n k Γ Γ')
    (H : env.IsDefEq U Γ' e₁ e₂ A) (h1 : e₁.Skips n k) (h2 : e₂.Skips n k) :
    ∃ B, env.IsDefEq U Γ' e₁ e₂ B ∧ B.Skips n k := by
  obtain ⟨e₁, rfl⟩ := VExpr.skips_iff_exists.1 h1
  obtain ⟨e₂, rfl⟩ := VExpr.skips_iff_exists.1 h2
  have ⟨_, H⟩ := (IsDefEqU.weakN_iff henv hs hΓ W).1 ⟨_, H⟩
  exact ⟨_, H.weakN henv.ordered W, .liftN⟩

variable! (henv : VEnv.WF env) (hs : env.Strengthening) in
theorem _root_.Lean4Lean.OnCtx.weakN_inv
    (W : Ctx.LiftN n k Γ Γ') (H : OnCtx Γ' (env.IsType U)) : OnCtx Γ (env.IsType U) :=
  (hs.front.liftN henv W H).1

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem IsDefEq.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    env.IsDefEq U Γ' (e1.liftN n k) (e2.liftN n k) (A.liftN n k) ↔ env.IsDefEq U Γ e1 e2 A :=
  ⟨fun h => IsDefEq.weakN_inv_of_down henv W (hΓ'.weakN_inv henv hs W) hΓ' (hs W hΓ') h,
    fun h => h.weakN henv.ordered W⟩

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ' : OnCtx Γ' (env.IsType U))
  (hΓ : OnCtx Γ (env.IsType U)) in
theorem IsDefEq.weakN_iff' (W : Ctx.LiftN n k Γ Γ') :
    env.IsDefEq U Γ' (e1.liftN n k) (e2.liftN n k) (A.liftN n k) ↔ env.IsDefEq U Γ e1 e2 A :=
  ⟨fun h => IsDefEq.weakN_inv_of_down henv W hΓ hΓ' (hs W hΓ') h, fun h => h.weakN henv.ordered W⟩

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem HasType.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    env.HasType U Γ' (e.liftN n k) (A.liftN n k) ↔ env.HasType U Γ e A :=
  IsDefEq.weakN_iff henv hs hΓ' W

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem IsType.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    env.IsType U Γ' (A.liftN n k) ↔ env.IsType U Γ A :=
  exists_congr fun _ => HasType.weakN_iff henv hs hΓ' W (A := .sort _)

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem HasType.skips (W : Ctx.LiftN n k Γ Γ')
    (h1 : env.HasType U Γ' e A) (h2 : e.Skips n k) : ∃ B, env.HasType U Γ' e B ∧ B.Skips n k :=
  IsDefEq.skips henv hs hΓ' W h1 h2 h2

end VEnv
end Lean4Lean
