import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.Typing.LevelEquiv
import Lean4Lean.WHNFCacheKey
import Lean4Lean.Verify.Typing.Syntactic.Strengthening

namespace Lean4Lean
open VEnv Lean

def ConditionallyTyped
    (ngen : NameGenerator) (env : VEnv) (Us : List Name) (Δ : VLCtx) (e : Expr) : Prop :=
  Closed e ∧ FVarsIn ngen.Reserves e ∧ (FVarsIn (· ∈ Δ.fvars) e → ∃ e', TrExprS env Us Δ e e')

theorem ConditionallyTyped.mk {Δ : VLCtx}
    (noBV : Δ.NoBV) (r : FVarsIn ngen.Reserves e) (H : TrExprS env Us Δ e e') :
    ConditionallyTyped ngen env Us Δ e := ⟨noBV ▸ H.closed, r, fun _ => ⟨_, H⟩⟩

theorem ConditionallyTyped.mono (H : ngen₁ ≤ ngen₂) :
    ConditionallyTyped ngen₁ env Us Δ e → ConditionallyTyped ngen₂ env Us Δ e
  | ⟨h1, h2, h3⟩ => ⟨h1, h2.mono fun _ h => h.mono H, h3⟩

theorem ConditionallyTyped.fresh
    (henv : Ordered env) (hΔ : VLCtx.WF env Us.length ((some (⟨ngen.curr⟩, deps), d) :: Δ))
    (H : ConditionallyTyped ngen env Us Δ e) :
    ConditionallyTyped ngen env Us ((some (⟨ngen.curr⟩, deps), d) :: Δ) e := by
  refine have ⟨H1, H2, H3⟩ := H; ⟨H1, H2, fun H4 => ?_⟩
  refine have ⟨_, h⟩ := H3 (H4.mp ?_ H2); ⟨_, h.weakFV henv (.skip_fvar _ _ .refl) hΔ⟩
  intro _ h1 h2; simp at h1; rcases h1 with rfl | h1
  · cases Nat.lt_irrefl _ (h2 _ rfl)
  · exact h1

def ConditionallyHasType
    (ngen : NameGenerator) (env : VEnv) (Us : List Name) (Δ : VLCtx) (e A : Expr) : Prop :=
  Closed e ∧ FVarsIn ngen.Reserves e ∧ Closed A ∧ FVarsIn ngen.Reserves A ∧
    (FVarsIn (· ∈ Δ.fvars) e → ∃ e' A', TrTyping env Us Δ e A e' A')

theorem ConditionallyHasType.mk {Δ : VLCtx}
    (noBV : Δ.NoBV) (he : TrTyping env Us Δ e A e' A')
    (re : FVarsIn ngen.Reserves e) (rA : FVarsIn ngen.Reserves A) :
    ConditionallyHasType ngen env Us Δ e A := by
  refine ⟨noBV ▸ he.2.1.closed, re, noBV ▸ he.2.2.1.closed, rA, fun _ => ⟨_, _, he.1, he.2⟩⟩

theorem ConditionallyHasType.typed :
    ConditionallyHasType ngen env Us Δ e A → ConditionallyTyped ngen env Us Δ e
  | ⟨c1, f1, _, _, H⟩ => ⟨c1, f1, fun h => let ⟨_, _, _, h, _⟩ := H h; ⟨_, h⟩⟩

theorem ConditionallyHasType.mono (H : ngen₁ ≤ ngen₂) :
    ConditionallyHasType ngen₁ env Us Δ e A → ConditionallyHasType ngen₂ env Us Δ e A
  | ⟨c1, f1, c2, f2, h'⟩ => ⟨c1, f1.mono fun _ h => h.mono H, c2, f2.mono fun _ h => h.mono H, h'⟩

theorem ConditionallyHasType.fresh
    (henv : Ordered env)
    (hΔ : VLCtx.WF env Us.length ((some (⟨ngen.curr⟩, deps), d) :: Δ))
    (H : ConditionallyHasType ngen env Us Δ e A) :
    ConditionallyHasType ngen env Us ((some (⟨ngen.curr⟩, deps), d) :: Δ) e A := by
  refine have ⟨c1, f1, c2, f2, H⟩ := H; ⟨c1, f1, c2, f2, fun H4 => ?_⟩
  have ⟨_, _, h1, h2, h3, h4⟩ := H (H4.mp ?_ f1)
  · have W : VLCtx.FVLift Δ ((some (⟨ngen.curr⟩, deps), d) :: Δ) 0 (0 + d.depth) 0 :=
      .skip_fvar _ _ .refl
    exact ⟨_, _, fun P hP => h1 _ hP.1,
      h2.weakFV henv W hΔ, h3.weakFV henv W hΔ, h4.weakN henv W.toCtx⟩
  · intro _ h1 h2; simp at h1; rcases h1 with rfl | h1
    · cases Nat.lt_irrefl _ (h2 _ rfl)
    · exact h1

theorem whnfCacheKey_eqv {e e' : Expr} (h : e == e') :
    whnfCacheKey e = whnfCacheKey e' := by
  simp [(· == ·)] at h
  cases e <;> cases e' <;> first | rfl | (change false = true at h; cases h)

theorem TrExprS.cacheKey_not_forall (H : TrExprS env Us Δ e e')
    (hkey : whnfCacheKey e = true) : e' ≠ .forallE domain body := by
  cases H <;> simp only [whnfCacheKey] at hkey
  all_goals first | contradiction | (intro h; cases h)

/-- A `whnf` cache entry `e ↦ e₁` that is valid conditionally on the context: both sides are
closed and mention only reserved free variables, and whenever the free variables of `e` lie in `Δ`,
`e` is a cache key (`whnfCacheKey`, so its translation is not a forall) translating to some `e'`
to which `e₁` also translates, with `FVarsBelow Δ e e₁`. -/
def ConditionallyWHNF
    (ngen : NameGenerator) (env : VEnv) (Us : List Name) (Δ : VLCtx) (e e₁ : Expr) : Prop :=
  Closed e ∧ FVarsIn ngen.Reserves e ∧ Closed e₁ ∧ FVarsIn ngen.Reserves e₁ ∧
    (FVarsIn (· ∈ Δ.fvars) e → ∃ e',
      FVarsBelow Δ e e₁ ∧ TrExprS env Us Δ e e' ∧ TrExpr env Us Δ e₁ e' ∧
      whnfCacheKey e = true)

theorem ConditionallyWHNF.mk {Δ : VLCtx}
    (noBV : Δ.NoBV) (hb : FVarsBelow Δ e e₁)
    (he : TrExprS env Us Δ e e') (he₁ : TrExpr env Us Δ e₁ e')
    (hkey : whnfCacheKey e = true)
    (re : FVarsIn ngen.Reserves e) (re₁ : FVarsIn ngen.Reserves e₁) :
    ConditionallyWHNF ngen env Us Δ e e₁ := by
  refine ⟨noBV ▸ he.closed, re, noBV ▸ he₁.closed, re₁, fun _ => ⟨_, hb, he, he₁, hkey⟩⟩

theorem ConditionallyWHNF.mono (H : ngen₁ ≤ ngen₂) :
    ConditionallyWHNF ngen₁ env Us Δ e A → ConditionallyWHNF ngen₂ env Us Δ e A
  | ⟨c1, f1, c2, f2, h'⟩ => ⟨c1, f1.mono fun _ h => h.mono H, c2, f2.mono fun _ h => h.mono H, h'⟩

theorem ConditionallyWHNF.fresh
    (henv : env.WF)
    (hΔ : VLCtx.WF env Us.length ((some (⟨ngen.curr⟩, deps), d) :: Δ))
    (H : ConditionallyWHNF ngen env Us Δ e e₁) :
    ConditionallyWHNF ngen env Us ((some (⟨ngen.curr⟩, deps), d) :: Δ) e e₁ := by
  refine have ⟨c1, f1, c2, f2, H⟩ := H; ⟨c1, f1, c2, f2, fun H4 => ?_⟩
  have ⟨e', h1, h2, h3, h5⟩ := H (H4.mp ?_ f1)
  · have W : VLCtx.FVLift Δ ((some (⟨ngen.curr⟩, deps), d) :: Δ) 0 (0 + d.depth) 0 :=
      .skip_fvar _ _ .refl
    exact ⟨_, fun P hP => h1 _ hP.1, h2.weakFV henv W hΔ, h3.weakFV henv W hΔ, h5⟩
  · intro _ h1 h2; simp at h1; rcases h1 with rfl | h1
    · cases Nat.lt_irrefl _ (h2 _ rfl)
    · exact h1

/-! ### Leaving a binder under a strengthening hypothesis

The conditional cache entries stay valid when a free variable is removed from the context, given
`VEnv.Strengthening`: an entry whose key does not mention the variable was, by the condition,
derived in the larger context, and strengthening moves it to the smaller one. These are used only
by the verification of the checker's global cache mode (`CacheMode.global`), where the hypothesis
comes from a `GlobalCacheLicense`. -/

private theorem upSet_tail {env : VEnv} {Us : List Name} {Δ : VLCtx} (hΔ : VLCtx.WF env Us.length ((some (fv, deps), d) :: Δ)) :
    IsFVarUpSet (· ∈ VLCtx.fvars Δ) ((some (fv, deps), d) :: Δ) :=
  ⟨.fvars hΔ.1.fvwf, (hΔ.2.1 _ _ rfl).1.elim⟩

private theorem fvarsBelow_tail {env : VEnv} {Us : List Name} {Δ : VLCtx} (hΔ : VLCtx.WF env Us.length ((some (fv, deps), d) :: Δ))
    (h1 : FVarsBelow ((some (fv, deps), d) :: Δ) e A) (he : FVarsIn (· ∈ Δ.fvars) e) :
    FVarsBelow Δ e A := fun P hP he' =>
  h1 _ ⟨(IsFVarUpSet.and_fvars hΔ.1.fvwf).1 hP, fun h => (hΔ.2.1 _ _ rfl).1.elim h.2⟩
    (he'.mp (fun _ => .intro) he) |>.mono fun _ => (·.1)

variable! (henv : VEnv.WF env) (hs : env.Strengthening) in
theorem ConditionallyTyped.weakN_inv
    (hΔ : VLCtx.WF env Us.length ((some fv, d) :: Δ))
    (H : ConditionallyTyped ngen env Us ((some fv, d) :: Δ) e) :
    ConditionallyTyped ngen env Us Δ e := by
  refine ⟨H.1, H.2.1, fun H2 => ?_⟩
  have ⟨_, h⟩ := H.2.2 H2.fvars_cons
  obtain ⟨_, h, -⟩ := h.restrictFV_inv henv hs (.skip_fvar _ _ .refl) hΔ H2
  exact ⟨_, h⟩

variable! (henv : VEnv.WF env) (hs : env.Strengthening) in
theorem ConditionallyHasType.weakN_inv
    (hΔ : VLCtx.WF env Us.length ((some fv, d) :: Δ))
    (H : ConditionallyHasType ngen env Us ((some fv, d) :: Δ) e A) :
    ConditionallyHasType ngen env Us Δ e A := by
  obtain ⟨fv, deps⟩ := fv
  have ⟨c1, f1, c2, f2, H⟩ := H
  refine ⟨c1, f1, c2, f2, fun H4 => ?_⟩
  have ⟨e', A', h1, h2, h3, h4⟩ := H H4.fvars_cons
  have W : VLCtx.FVLift Δ ((some (fv, deps), d) :: Δ) 0 (0 + d.depth) 0 := .skip_fvar _ _ .refl
  obtain ⟨e₀, he, rfl⟩ := h2.restrictFV_inv henv hs W hΔ H4
  obtain ⟨A₀, hA, rfl⟩ := h3.restrictFV_inv henv hs W hΔ (h1 _ (upSet_tail hΔ) H4)
  have h4 := (HasType.weakN_iff henv hs hΔ.toCtx W.toCtx).1 h4
  exact ⟨_, _, fvarsBelow_tail hΔ h1 he.fvarsIn, he, hA, h4⟩

variable! (henv : VEnv.WF env) (hs : env.Strengthening) in
theorem ConditionallyWHNF.weakN_inv
    (hΔ : VLCtx.WF env Us.length ((some fv, d) :: Δ))
    (H : ConditionallyWHNF ngen env Us ((some fv, d) :: Δ) e e₁) :
    ConditionallyWHNF ngen env Us Δ e e₁ := by
  obtain ⟨fv, deps⟩ := fv
  have ⟨c1, f1, c2, f2, H⟩ := H
  refine ⟨c1, f1, c2, f2, fun H4 => ?_⟩
  have ⟨e', h1, h2, ⟨_, h3, h4⟩, h5⟩ := H H4.fvars_cons
  have W : VLCtx.FVLift Δ ((some (fv, deps), d) :: Δ) 0 (0 + d.depth) 0 := .skip_fvar _ _ .refl
  obtain ⟨e₀, he, rfl⟩ := h2.restrictFV_inv henv hs W hΔ H4
  obtain ⟨e₁', he₁, rfl⟩ := h3.restrictFV_inv henv hs W hΔ (h1 _ (upSet_tail hΔ) H4)
  have h4 := (IsDefEqU.weakN_iff henv hs hΔ.toCtx W.toCtx).1 h4
  exact ⟨_, fvarsBelow_tail hΔ h1 he.fvarsIn, he, ⟨_, he₁, h4⟩, h5⟩
