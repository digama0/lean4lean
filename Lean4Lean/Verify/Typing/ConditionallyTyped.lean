import Lean4Lean.Verify.Typing.Lemmas

namespace Lean4Lean
open VEnv Lean

def ConditionallyTyped
    (ngen : NameGenerator) (env : VEnv) (Us : List Name) (Δ : VLCtx) (e : Expr) : Prop :=
  InScope ngen.Reserves e ∧ (InScope (· ∈ Δ.fvars) e → ∃ e', TrExpr env Us Δ e e')

theorem ConditionallyTyped.mono (H : ngen₁ ≤ ngen₂) :
    ConditionallyTyped ngen₁ env Us Δ e → ConditionallyTyped ngen₂ env Us Δ e
  | ⟨h1, h2⟩ => ⟨h1.mono fun _ h => h.mono H, h2⟩

theorem ConditionallyTyped.weakN_inv
    (henv : Ordered env) (hΔ : VLCtx.WF env Us.length ((some fv, d) :: Δ))
    (H : ConditionallyTyped ngen env Us ((some fv, d) :: Δ) e) :
    ConditionallyTyped ngen env Us Δ e := by
  refine H.imp_right fun H1 H2 => ?_
  have ⟨e', H⟩ := H1 H2.fvars_cons
  exact TrExpr.weakN_inv henv (.skip_fvar _ _ .refl) (.refl henv hΔ) H H2

theorem ConditionallyTyped.fresh
    (henv : Ordered env) (hΔ : VLCtx.WF env Us.length ((some ⟨ngen.curr⟩, d) :: Δ))
    (H : ConditionallyTyped ngen env Us Δ e) :
    ConditionallyTyped ngen env Us ((some ⟨ngen.curr⟩, d) :: Δ) e := by
  refine have ⟨H1, H2⟩ := H; ⟨H1, fun H3 => ?_⟩
  refine have ⟨_, h⟩ := H2 (H3.mp ?_ H1); ⟨_, h.weakN henv (.skip_fvar _ _ .refl) hΔ⟩
  intro _ h1 h2; simp at h1; rcases h1 with rfl | h1
  · cases Nat.lt_irrefl _ (h2 _ rfl)
  · exact h1

def TrHasType (env : VEnv) (Us : List Name) (Δ : VLCtx) (e A : Expr) : Prop :=
  (∀ P, IsFVarUpSet P Δ → InScope P e → InScope P A) ∧
  ∃ e' A', TrExpr env Us Δ e e' ∧ TrExpr env Us Δ A A' ∧ env.HasType Us.length Δ.toCtx e' A'

def ConditionallyHasType
    (ngen : NameGenerator) (env : VEnv) (Us : List Name) (Δ : VLCtx) (e A : Expr) : Prop :=
  InScope ngen.Reserves e ∧ InScope ngen.Reserves A ∧
    (InScope (· ∈ Δ.fvars) e → TrHasType env Us Δ e A)

theorem ConditionallyHasType.typed :
    ConditionallyHasType ngen env Us Δ e A → ConditionallyTyped ngen env Us Δ e
  | ⟨h1, _, h3⟩ => ⟨h1, fun h => let ⟨_, _, _, h, _⟩ := h3 h; ⟨_, h⟩⟩

theorem ConditionallyHasType.mono (H : ngen₁ ≤ ngen₂) :
    ConditionallyHasType ngen₁ env Us Δ e A → ConditionallyHasType ngen₂ env Us Δ e A
  | ⟨h1, h2, h3⟩ => ⟨h1.mono fun _ h => h.mono H, h2.mono fun _ h => h.mono H, h3⟩

theorem ConditionallyHasType.weakN_inv
    (henv : Ordered env) (hΔ : VLCtx.WF env Us.length ((some fv, d) :: Δ))
    (H : ConditionallyHasType ngen env Us ((some fv, d) :: Δ) e A) :
    ConditionallyHasType ngen env Us Δ e A := by
  have ⟨H1, H2, H3⟩ := H
  refine ⟨H1, H2, fun H4 => ?_⟩
  have ⟨h1, e', A', h2, h3, h4⟩ := H3 H4.fvars_cons
  have W : VLCtx.LiftN Δ ((some fv, d) :: Δ) 0 (0 + d.depth) 0 := .skip_fvar _ _ .refl
  have ⟨e'', he⟩ := TrExpr.weakN_inv henv W (.refl henv hΔ) h2 H4
  have ee := h2.uniq henv (.refl henv hΔ) <| he.weakN henv W hΔ
  have : IsFVarUpSet (· ∈ VLCtx.fvars Δ) ((some fv, d) :: Δ) := ⟨(hΔ.2.1 _ rfl).elim, .fvars⟩
  have ⟨_, hA⟩ := TrExpr.weakN_inv henv W (.refl henv hΔ) h3 <| h1 _ this H4
  have AA := h3.uniq henv (.refl henv hΔ) <| hA.weakN henv W hΔ
  have h4 := h4.defeqU_r henv hΔ.toCtx AA |>.defeqU_l henv hΔ.toCtx ee
  have h4 := (HasType.weakN_iff henv hΔ.toCtx W.toCtx).1 h4
  refine ⟨fun P hP he' => ?_, _, _, he, hA, h4⟩
  exact h1 _
    ⟨fun h => (hΔ.2.1 _ rfl).elim h.2, IsFVarUpSet.and_fvars.1 hP⟩
    (he'.mp (fun _ => .intro) (he.inScope.mix he')) |>.mono fun _ => (·.1)

theorem ConditionallyHasType.fresh
    (henv : Ordered env) (hΔ : VLCtx.WF env Us.length ((some ⟨ngen.curr⟩, d) :: Δ))
    (H : ConditionallyHasType ngen env Us Δ e A) :
    ConditionallyHasType ngen env Us ((some ⟨ngen.curr⟩, d) :: Δ) e A := by
  refine have ⟨H1, H2, H3⟩ := H; ⟨H1, H2, fun H4 => ?_⟩
  have ⟨h1, _, _, h2, h3, h4⟩ := H3 (H4.mp ?_ H1)
  · have W : VLCtx.LiftN Δ ((some ⟨ngen.curr⟩, d) :: Δ) 0 (0 + d.depth) 0 := .skip_fvar _ _ .refl
    refine ⟨fun P hP => h1 _ hP.2, ?_⟩
    exact ⟨_, _, h2.weakN henv W hΔ, h3.weakN henv W hΔ, h4.weakN henv W.toCtx⟩
  · intro _ h1 h2; simp at h1; rcases h1 with rfl | h1
    · cases Nat.lt_irrefl _ (h2 _ rfl)
    · exact h1
