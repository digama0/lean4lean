import Lean4Lean.Verify.Typing.LetErasure

namespace Lean4Lean
open VEnv Lean

theorem FVarsIn.not_curr {ngen : NameGenerator} (H : FVarsIn ngen.Reserves e) : FVarsIn (· ≠ ⟨ngen.curr⟩) e :=
  H.mono fun _ reserved equal => ngen.not_reserves_self (equal ▸ reserved)

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

/-- A local definition has already been inlined into the semantic context. -/
theorem ConditionallyTyped.weakLet_inv
    (hΔ : VLCtx.WF env Us.length ((some fv, .vlet domain value) :: Δ))
    (H : ConditionallyTyped ngen env Us ((some fv, .vlet domain value) :: Δ) e) :
    ConditionallyTyped ngen env Us Δ e := by
  refine ⟨H.1, H.2.1, fun sourceScope => ?_⟩
  obtain ⟨e', translated⟩ := H.2.2 sourceScope.fvars_cons
  exact ⟨e', translated.eraseLet .zero <| sourceScope.mono fun _ member equal =>
    (hΔ.2.1 _ _ rfl).1 (equal ▸ member)⟩

theorem ConditionallyTyped.fresh
    (henv : Ordered env) (hΔ : VLCtx.WF env Us.length ((some (⟨ngen.curr⟩, deps), d) :: Δ))
    (H : ConditionallyTyped ngen env Us Δ e) :
    ConditionallyTyped ngen env Us ((some (⟨ngen.curr⟩, deps), d) :: Δ) e := by
  refine have ⟨H1, H2, H3⟩ := H; ⟨H1, H2, fun H4 => ?_⟩
  refine have ⟨_, h⟩ := H3 (H4.mp ?_ H2); ⟨_, h.weakFV henv (.skip_fvar _ _ .refl) hΔ⟩
  intro _ h1 h2; simp at h1; rcases h1 with rfl | h1
  · cases Nat.lt_irrefl _ (h2 _ rfl)
  · exact h1

theorem ConditionallyTyped.freshLet
    (H : ConditionallyTyped ngen env Us Δ e) :
    ConditionallyTyped ngen env Us
      ((some (⟨ngen.curr⟩, deps), .vlet domain value) :: Δ) e := by
  obtain ⟨closed, reserved, H⟩ := H
  refine ⟨closed, reserved, fun sourceScope => ?_⟩
  have ⟨e', translated⟩ := H (sourceScope.mp ?_ reserved)
  · exact ⟨e', translated.insertLet .zero reserved.not_curr⟩
  · intro _ member reserved
    simp at member
    rcases member with rfl | member
    · exact (ngen.not_reserves_self reserved).elim
    · exact member

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

theorem ConditionallyHasType.weakLet_inv
    (hΔ : VLCtx.WF env Us.length ((some fv, .vlet domain value) :: Δ))
    (H : ConditionallyHasType ngen env Us ((some fv, .vlet domain value) :: Δ) e A) :
    ConditionallyHasType ngen env Us Δ e A := by
  obtain ⟨c1, f1, c2, f2, H⟩ := H
  refine ⟨c1, f1, c2, f2, fun sourceScope => ?_⟩
  obtain ⟨e', A', below, he, hA, typed⟩ := H sourceScope.fvars_cons
  have up : IsFVarUpSet (· ∈ VLCtx.fvars Δ) ((some fv, .vlet domain value) :: Δ) :=
    ⟨.fvars hΔ.1.fvwf, (hΔ.2.1 _ _ rfl).1.elim⟩
  have unused {a} (ha : FVarsIn (· ∈ VLCtx.fvars Δ) a) : FVarsIn (· ≠ fv.1) a :=
    ha.mono fun _ member equal => (hΔ.2.1 _ _ rfl).1 (equal ▸ member)
  have he := he.eraseLet .zero (unused sourceScope)
  have hA := hA.eraseLet .zero (unused (below _ up sourceScope))
  refine ⟨e', A', fun P hP source => ?_, he, hA, typed⟩
  exact below _
    ⟨(IsFVarUpSet.and_fvars hΔ.1.fvwf).1 hP, fun h => (hΔ.2.1 _ _ rfl).1.elim h.2⟩
    (source.mp (fun _ => .intro) he.fvarsIn) |>.mono fun _ => (·.1)

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

theorem ConditionallyHasType.freshLet
    (H : ConditionallyHasType ngen env Us Δ e A) :
    ConditionallyHasType ngen env Us
      ((some (⟨ngen.curr⟩, deps), .vlet domain value) :: Δ) e A := by
  obtain ⟨c1, f1, c2, f2, H⟩ := H
  refine ⟨c1, f1, c2, f2, fun sourceScope => ?_⟩
  have ⟨e', A', below, he, hA, typed⟩ := H (sourceScope.mp ?_ f1)
  · exact ⟨e', A', fun P up => below P up.1,
      he.insertLet .zero f1.not_curr, hA.insertLet .zero f2.not_curr, typed⟩
  · intro _ member reserved
    simp at member
    rcases member with rfl | member
    · exact (ngen.not_reserves_self reserved).elim
    · exact member

def ConditionallyWHNF
    (ngen : NameGenerator) (env : VEnv) (Us : List Name) (Δ : VLCtx) (e e₁ : Expr) : Prop :=
  Closed e ∧ FVarsIn ngen.Reserves e ∧ Closed e₁ ∧ FVarsIn ngen.Reserves e₁ ∧
    (FVarsIn (· ∈ Δ.fvars) e → ∃ e',
      FVarsBelow Δ e e₁ ∧ TrExprS env Us Δ e e' ∧ TrExpr env Us Δ e₁ e')

theorem ConditionallyWHNF.mk {Δ : VLCtx}
    (noBV : Δ.NoBV) (hb : FVarsBelow Δ e e₁)
    (he : TrExprS env Us Δ e e') (he₁ : TrExpr env Us Δ e₁ e')
    (re : FVarsIn ngen.Reserves e) (re₁ : FVarsIn ngen.Reserves e₁) :
    ConditionallyWHNF ngen env Us Δ e e₁ := by
  refine ⟨noBV ▸ he.closed, re, noBV ▸ he₁.closed, re₁, fun _ => ⟨_, hb, he, he₁⟩⟩

theorem ConditionallyWHNF.mono (H : ngen₁ ≤ ngen₂) :
    ConditionallyWHNF ngen₁ env Us Δ e A → ConditionallyWHNF ngen₂ env Us Δ e A
  | ⟨c1, f1, c2, f2, h'⟩ => ⟨c1, f1.mono fun _ h => h.mono H, c2, f2.mono fun _ h => h.mono H, h'⟩

theorem ConditionallyWHNF.weakN_inv
    (henv : VEnv.WF env) (hΔ : VLCtx.WF env Us.length ((some fv, d) :: Δ))
    (H : ConditionallyWHNF ngen env Us ((some fv, d) :: Δ) e e₁) :
    ConditionallyWHNF ngen env Us Δ e e₁ := by
  have ⟨c1, f1, c2, f2, H⟩ := H
  refine ⟨c1, f1, c2, f2, fun H4 => ?_⟩
  have ⟨e', h1, h2, _, h3, h4⟩ := H H4.fvars_cons
  have W : VLCtx.FVLift Δ ((some fv, d) :: Δ) 0 (0 + d.depth) 0 := .skip_fvar _ _ .refl
  have ⟨e'', he⟩ := TrExprS.weakFV_inv henv W (.refl henv hΔ) h2 c1 H4
  have ee := h2.uniq henv (.refl henv hΔ) <| he.weakFV henv W hΔ
  have := hΔ.2.1 _ _ rfl
  have : IsFVarUpSet (· ∈ VLCtx.fvars Δ) ((some fv, d) :: Δ) :=
    ⟨.fvars hΔ.1.fvwf, (hΔ.2.1 _ _ rfl).1.elim⟩
  have ⟨_, he₁⟩ := TrExprS.weakFV_inv henv W (.refl henv hΔ) h3 c2 <| h1 _ this H4
  have ee₁ := h3.uniq henv (.refl henv hΔ) <| he₁.weakFV henv W hΔ
  have h4 := ee₁.symm.trans henv hΔ.toCtx h4 |>.trans henv hΔ.toCtx ee
  have h4 := (IsDefEqU.weakN_iff henv hΔ.toCtx W.toCtx).1 h4
  refine ⟨_, fun P hP he' => ?_, he, _, he₁, h4⟩
  exact h1 _
    ⟨(IsFVarUpSet.and_fvars hΔ.1.fvwf).1 hP, fun h => (hΔ.2.1 _ _ rfl).1.elim h.2⟩
    (he'.mp (fun _ => .intro) he.fvarsIn) |>.mono fun _ => (·.1)

theorem ConditionallyWHNF.weakLet_inv
    (hΔ : VLCtx.WF env Us.length ((some fv, .vlet domain value) :: Δ))
    (H : ConditionallyWHNF ngen env Us ((some fv, .vlet domain value) :: Δ) e result) :
    ConditionallyWHNF ngen env Us Δ e result := by
  obtain ⟨c1, f1, c2, f2, H⟩ := H
  refine ⟨c1, f1, c2, f2, fun sourceScope => ?_⟩
  obtain ⟨e', below, he, hr⟩ := H sourceScope.fvars_cons
  have up : IsFVarUpSet (· ∈ VLCtx.fvars Δ) ((some fv, .vlet domain value) :: Δ) :=
    ⟨.fvars hΔ.1.fvwf, (hΔ.2.1 _ _ rfl).1.elim⟩
  have unused {a} (ha : FVarsIn (· ∈ VLCtx.fvars Δ) a) : FVarsIn (· ≠ fv.1) a :=
    ha.mono fun _ member equal => (hΔ.2.1 _ _ rfl).1 (equal ▸ member)
  have he := he.eraseLet .zero (unused sourceScope)
  have hr := hr.eraseLet .zero (unused (below _ up sourceScope))
  refine ⟨e', fun P hP source => ?_, he, hr⟩
  exact below _
    ⟨(IsFVarUpSet.and_fvars hΔ.1.fvwf).1 hP, fun h => (hΔ.2.1 _ _ rfl).1.elim h.2⟩
    (source.mp (fun _ => .intro) he.fvarsIn) |>.mono fun _ => (·.1)

theorem ConditionallyWHNF.fresh
    (henv : env.WF)
    (hΔ : VLCtx.WF env Us.length ((some (⟨ngen.curr⟩, deps), d) :: Δ))
    (H : ConditionallyWHNF ngen env Us Δ e e₁) :
    ConditionallyWHNF ngen env Us ((some (⟨ngen.curr⟩, deps), d) :: Δ) e e₁ := by
  refine have ⟨c1, f1, c2, f2, H⟩ := H; ⟨c1, f1, c2, f2, fun H4 => ?_⟩
  have ⟨_, h1, h2, h3⟩ := H (H4.mp ?_ f1)
  · have W : VLCtx.FVLift Δ ((some (⟨ngen.curr⟩, deps), d) :: Δ) 0 (0 + d.depth) 0 :=
      .skip_fvar _ _ .refl
    exact ⟨_, fun P hP => h1 _ hP.1, h2.weakFV henv W hΔ, h3.weakFV henv W hΔ⟩
  · intro _ h1 h2; simp at h1; rcases h1 with rfl | h1
    · cases Nat.lt_irrefl _ (h2 _ rfl)
    · exact h1

theorem ConditionallyWHNF.freshLet
    (H : ConditionallyWHNF ngen env Us Δ e result) :
    ConditionallyWHNF ngen env Us
      ((some (⟨ngen.curr⟩, deps), .vlet domain value) :: Δ) e result := by
  obtain ⟨c1, f1, c2, f2, H⟩ := H
  refine ⟨c1, f1, c2, f2, fun sourceScope => ?_⟩
  have ⟨e', below, he, hr⟩ := H (sourceScope.mp ?_ f1)
  · exact ⟨e', fun P up => below P up.1,
      he.insertLet .zero f1.not_curr, hr.insertLet .zero f2.not_curr⟩
  · intro _ member reserved
    simp at member
    rcases member with rfl | member
    · exact (ngen.not_reserves_self reserved).elim
    · exact member
