import Lean4Lean.Verify.Typing.Lemmas

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

theorem ConditionallyTyped.weakN_inv
    (henv : VEnv.WF env) (hΔ : VLCtx.WF env Us.length ((some fv, d) :: Δ))
    (H : ConditionallyTyped ngen env Us ((some fv, d) :: Δ) e) :
    ConditionallyTyped ngen env Us Δ e := by
  refine ⟨H.1, H.2.1, fun H2 => ?_⟩
  have := H.2.2
  have ⟨e', h⟩ := H.2.2 H2.fvars_cons
  exact TrExprS.weakFV_inv henv (.skip_fvar _ _ .refl) (.refl henv hΔ) h H.1 H2

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

theorem ConditionallyHasType.weakN_inv
    (henv : VEnv.WF env) (hΔ : VLCtx.WF env Us.length ((some fv, d) :: Δ))
    (H : ConditionallyHasType ngen env Us ((some fv, d) :: Δ) e A) :
    ConditionallyHasType ngen env Us Δ e A := by
  have ⟨c1, f1, c2, f2, H⟩ := H
  refine ⟨c1, f1, c2, f2, fun H4 => ?_⟩
  have ⟨e', A', h1, h2, h3, h4⟩ := H H4.fvars_cons
  have W : VLCtx.FVLift Δ ((some fv, d) :: Δ) 0 (0 + d.depth) 0 := .skip_fvar _ _ .refl
  have ⟨e'', he⟩ := TrExprS.weakFV_inv henv W (.refl henv hΔ) h2 c1 H4
  have ee := h2.uniq henv (.refl henv hΔ) <| he.weakFV henv W hΔ
  have := hΔ.2.1 _ _ rfl
  have : IsFVarUpSet (· ∈ VLCtx.fvars Δ) ((some fv, d) :: Δ) :=
    ⟨.fvars hΔ.1.fvwf, (hΔ.2.1 _ _ rfl).1.elim⟩
  have ⟨_, hA⟩ := TrExprS.weakFV_inv henv W (.refl henv hΔ) h3 c2 <| h1 _ this H4
  have AA := h3.uniq henv (.refl henv hΔ) <| hA.weakFV henv W hΔ
  have h4 := h4.defeqU_r henv hΔ.toCtx AA |>.defeqU_l henv hΔ.toCtx ee
  have h4 := (HasType.weakN_iff henv hΔ.toCtx W.toCtx).1 h4
  refine ⟨_, _, fun P hP he' => ?_, he, hA, h4⟩
  exact h1 _
    ⟨(IsFVarUpSet.and_fvars hΔ.1.fvwf).1 hP, fun h => (hΔ.2.1 _ _ rfl).1.elim h.2⟩
    (he'.mp (fun _ => .intro) he.fvarsIn) |>.mono fun _ => (·.1)

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
