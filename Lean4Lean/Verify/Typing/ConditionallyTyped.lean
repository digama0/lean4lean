import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.Typing.LevelEquiv
import Lean4Lean.WHNFCacheKey
import Lean4Lean.Verify.Typing.Syntactic.Typed

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
    (henv : OrderedStrong env) (hΔ : VLCtx.WF env Us.length ((some (⟨ngen.curr⟩, deps), d) :: Δ))
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
    (henv : OrderedStrong env)
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

/-! ### Leaving a binder

The conditional cache entries stay valid when a free variable is removed from the context: an
entry whose key does not mention the variable was, by the condition, derived in the larger
context, and context strengthening (`IsDefEqU.weakN_iff`, `Theory/Typing/UniqueTyping.lean`)
moves it to the smaller one. The syntax of a translation is restricted by `TrSyn`; only its typing
needs strengthening. -/

/-- Context strengthening for definitional equality: an equation between two lifted expressions
in a context extended by `n` binders (inserted below `k` binders) already holds in the smaller
context. -/
def VEnv.Strengthening (env : VEnv) : Prop :=
  ∀ ⦃U n k Γ Γ' e1 e2⦄, Ctx.LiftN n k Γ Γ' → OnCtx Γ' (env.IsType U) →
    env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) → env.IsDefEqU U Γ e1 e2

/-- Every well-formed environment admits context strengthening: master's
`IsDefEqU.weakN_iff`. This is the one strengthening principle of the checker verification. -/
theorem VEnv.WF.strengthening {env : VEnv} (henv : env.WF) : env.Strengthening :=
  fun _ _ _ _ _ _ _ W hΓ h => (IsDefEqU.weakN_iff henv hΓ W).1 h

theorem VLCtx.FVLift'.cons_vlam (W : VLCtx.FVLift' Δ Δ' dk l k)
    (h : ty₀.lift' (l.consN k) = ty') :
    VLCtx.FVLift' ((none, .vlam ty₀) :: Δ) ((none, .vlam ty') :: Δ') (dk + 1) l (k + 1) := by
  subst h; exact W.cons_bvar (.vlam ty₀)

theorem VLCtx.FVLift'.cons_vlet (W : VLCtx.FVLift' Δ Δ' dk l k)
    (h1 : ty₀.lift' (l.consN k) = ty') (h2 : val₀.lift' (l.consN k) = val') :
    VLCtx.FVLift' ((none, .vlet ty₀ val₀) :: Δ) ((none, .vlet ty' val') :: Δ') (dk + 1) l k := by
  subst h1 h2; exact W.cons_bvar (.vlet ty₀ val₀)

variable! (henv : VEnv.WF env) in
/-- The residual obligations of a typed translation in an extension `Δ'` of `Δ` by free
variables hold in `Δ`, for a source scoped by `Δ`. -/
theorem TrExprS.residual_restrictFV' {Us : List Name}
    (W : VLCtx.FVLift' Δ Δ' dk l k) (hΔ' : Δ'.WF env Us.length)
    (H : TrExprS env Us Δ' e e') (hsyn : TrSyn Us Δ e e₀) : TrResidual env Us Δ e := by
  induction H generalizing Δ dk k e₀ with
  | bvar => exact .bvar
  | fvar => exact .fvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ _ _ ih1 ih2 => let .app s1 s2 := hsyn; exact .app (ih1 W hΔ' s1) (ih2 W hΔ' s2)
  | lam h1 a1 _ ih1 ih2 =>
    let .lam s1 s2 := hsyn
    have W' := W.cons_vlam ((s1.weakFV' W hΔ'.fvars_nodup).unique a1.toTrSyn)
    exact .lam s1 (ih1 W hΔ' s1) (ih2 W' ⟨hΔ', nofun, h1⟩ s2)
  | forallE h1 _ a1 _ ih1 ih2 =>
    let .forallE s1 s2 := hsyn
    have W' := W.cons_vlam ((s1.weakFV' W hΔ'.fvars_nodup).unique a1.toTrSyn)
    exact .forallE s1 (ih1 W hΔ' s1) (ih2 W' ⟨hΔ', nofun, h1⟩ s2)
  | letE h1 a1 a2 _ ih1 ih2 ih3 =>
    let .letE s1 s2 s3 := hsyn
    have e1 := (s1.weakFV' W hΔ'.fvars_nodup).unique a1.toTrSyn
    have e2 := (s2.weakFV' W hΔ'.fvars_nodup).unique a2.toTrSyn
    have W' := W.cons_vlet e1 e2
    have h1' := (HasType.weak'_iff henv hΔ'.toCtx W.toCtx).1 (by rw [← e1, ← e2] at h1; exact h1)
    exact .letE s1 s2 h1' (ih1 W hΔ' s1) (ih2 W hΔ' s2) (ih3 W' ⟨hΔ', nofun, h1⟩ s3)
  | lit h1 _ ih => let .lit s := hsyn; exact .lit h1 (ih W hΔ' s)
  | mdata _ ih => let .mdata s := hsyn; exact .mdata (ih W hΔ' s)
  | proj _ _ ih => let .proj s := hsyn; exact .proj (ih W hΔ' s)

variable! (henv : VEnv.WF env) in
/-- **Strengthening of a typed translation**: a source scoped by `Δ` that has a typed translation
in an extension `Δ'` of `Δ` by free variables has one in `Δ`, of which the larger one is the lift.
The syntax is `TrSyn`-style restriction; the typing is `VExpr.WF.weak'_iff`. -/
theorem TrExprS.restrictFV'_inv {Us : List Name}
    (W : VLCtx.FVLift' Δ Δ' dk l k) (hΔ' : Δ'.WF env Us.length) (hΔ : Δ.WF env Us.length)
    (H : TrExprS env Us Δ' e e') (hfv : FVarsIn (· ∈ Δ.fvars) e) :
    ∃ e₀, TrExprS env Us Δ e e₀ ∧ e' = e₀.lift' (l.consN k) := by
  have hc : Closed e Δ.bvars := W.bvars_eq ▸ H.closed
  obtain ⟨e₀, s⟩ := TrSyn.exists_of_scoped hc hfv H.toTrSyn.levelParamsIn
  have heq : e' = e₀.lift' (l.consN k) := H.toTrSyn.unique (s.weakFV' W hΔ'.fvars_nodup)
  refine ⟨e₀, s.toTrExprS henv.orderedStrong hΔ ?_ (H.residual_restrictFV' henv W hΔ' s), heq⟩
  exact (VExpr.WF.weak'_iff henv hΔ'.toCtx W.toCtx).1 (heq ▸ H.wf henv.orderedStrong hΔ')

variable! (henv : VEnv.WF env) in
/-- `TrExprS.restrictFV'_inv` for the removal of free variables only. -/
theorem TrExprS.restrictFV_inv {Us : List Name}
    (W : VLCtx.FVLift Δ Δ' 0 n 0) (hΔ' : Δ'.WF env Us.length)
    (H : TrExprS env Us Δ' e e') (hfv : FVarsIn (· ∈ Δ.fvars) e) :
    ∃ e₀, TrExprS env Us Δ e e₀ ∧ e' = e₀.liftN n := by
  obtain ⟨e₀, h, rfl⟩ := H.restrictFV'_inv henv W.toFVLift' hΔ' (W.wf henv hΔ') hfv
  exact ⟨e₀, h, by simpa using VExpr.lift'_consN_skipN (e := e₀) (n := n) (k := 0)⟩

private theorem upSet_tail {env : VEnv} {Us : List Name} {Δ : VLCtx} (hΔ : VLCtx.WF env Us.length ((some (fv, deps), d) :: Δ)) :
    IsFVarUpSet (· ∈ VLCtx.fvars Δ) ((some (fv, deps), d) :: Δ) :=
  ⟨.fvars hΔ.1.fvwf, (hΔ.2.1 _ _ rfl).1.elim⟩

private theorem fvarsBelow_tail {env : VEnv} {Us : List Name} {Δ : VLCtx} (hΔ : VLCtx.WF env Us.length ((some (fv, deps), d) :: Δ))
    (h1 : FVarsBelow ((some (fv, deps), d) :: Δ) e A) (he : FVarsIn (· ∈ Δ.fvars) e) :
    FVarsBelow Δ e A := fun P hP he' =>
  h1 _ ⟨(IsFVarUpSet.and_fvars hΔ.1.fvwf).1 hP, fun h => (hΔ.2.1 _ _ rfl).1.elim h.2⟩
    (he'.mp (fun _ => .intro) he) |>.mono fun _ => (·.1)

variable! (henv : VEnv.WF env) in
theorem ConditionallyTyped.weakN_inv
    (hΔ : VLCtx.WF env Us.length ((some fv, d) :: Δ))
    (H : ConditionallyTyped ngen env Us ((some fv, d) :: Δ) e) :
    ConditionallyTyped ngen env Us Δ e := by
  refine ⟨H.1, H.2.1, fun H2 => ?_⟩
  have ⟨_, h⟩ := H.2.2 H2.fvars_cons
  obtain ⟨_, h, -⟩ := h.restrictFV_inv henv (.skip_fvar _ _ .refl) hΔ H2
  exact ⟨_, h⟩

variable! (henv : VEnv.WF env) in
theorem ConditionallyHasType.weakN_inv
    (hΔ : VLCtx.WF env Us.length ((some fv, d) :: Δ))
    (H : ConditionallyHasType ngen env Us ((some fv, d) :: Δ) e A) :
    ConditionallyHasType ngen env Us Δ e A := by
  obtain ⟨fv, deps⟩ := fv
  have ⟨c1, f1, c2, f2, H⟩ := H
  refine ⟨c1, f1, c2, f2, fun H4 => ?_⟩
  have ⟨e', A', h1, h2, h3, h4⟩ := H H4.fvars_cons
  have W : VLCtx.FVLift Δ ((some (fv, deps), d) :: Δ) 0 (0 + d.depth) 0 := .skip_fvar _ _ .refl
  obtain ⟨e₀, he, rfl⟩ := h2.restrictFV_inv henv W hΔ H4
  obtain ⟨A₀, hA, rfl⟩ := h3.restrictFV_inv henv W hΔ (h1 _ (upSet_tail hΔ) H4)
  have h4 := (HasType.weakN_iff henv hΔ.toCtx W.toCtx).1 h4
  exact ⟨_, _, fvarsBelow_tail hΔ h1 he.fvarsIn, he, hA, h4⟩

variable! (henv : VEnv.WF env) in
theorem ConditionallyWHNF.weakN_inv
    (hΔ : VLCtx.WF env Us.length ((some fv, d) :: Δ))
    (H : ConditionallyWHNF ngen env Us ((some fv, d) :: Δ) e e₁) :
    ConditionallyWHNF ngen env Us Δ e e₁ := by
  obtain ⟨fv, deps⟩ := fv
  have ⟨c1, f1, c2, f2, H⟩ := H
  refine ⟨c1, f1, c2, f2, fun H4 => ?_⟩
  have ⟨e', h1, h2, ⟨_, h3, h4⟩, h5⟩ := H H4.fvars_cons
  have W : VLCtx.FVLift Δ ((some (fv, deps), d) :: Δ) 0 (0 + d.depth) 0 := .skip_fvar _ _ .refl
  obtain ⟨e₀, he, rfl⟩ := h2.restrictFV_inv henv W hΔ H4
  obtain ⟨e₁', he₁, rfl⟩ := h3.restrictFV_inv henv W hΔ (h1 _ (upSet_tail hΔ) H4)
  have h4 := (IsDefEqU.weakN_iff henv hΔ.toCtx W.toCtx).1 h4
  exact ⟨_, fvarsBelow_tail hΔ h1 he.fvarsIn, he, ⟨_, he₁, h4⟩, h5⟩
