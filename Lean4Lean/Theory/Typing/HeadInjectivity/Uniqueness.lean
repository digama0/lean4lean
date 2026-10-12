import Lean4Lean.Theory.Typing.HeadInjectivity.FieldType
import Lean4Lean.Theory.Typing.ProjectionRigidity

/-! # Uniqueness of types from chain-level head injectivity

From `ChainHeadInjectivity` (no `HeadInversion`), by one induction on the first strong
typing, prove simultaneously

* (i) uniqueness of types up to `TypeChain` (`HasTypeStrong.uniq_chain_of_chainHeadInjectivity`), and
* (ii) `CongrUB`-congruence: a typed term is definitionally equal, at its type, to every
  term `CongrUB`-related to it (`HasTypeStrong.congrUB_defeq`).

The `app` case uses `forallE_chain` and `TypeChain.instN` on the codomain chain; the `proj`
case uses `rigid_rigid` on the major types, `fieldType_congr`, and (ii) for the strong
sub-derivation typing the first field type. (ii) at a `CongrUB` leaf uses (i) at the
current node to align the leaf's type. -/

namespace Lean4Lean
open Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}

theorem _root_.Lean4Lean.Ctx.LiftN.cons0 (W : Ctx.LiftN k 0 Γ₀ Γ) : Ctx.LiftN (k+1) 0 Γ₀ (A :: Γ) := by
  cases W with
  | zero As h => exact .zero (A :: As) (by simp [h])

theorem forall₂_append_left {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₁' : List β} {l₂ l₂'}, l₁.length = l₁'.length →
      List.Forall₂ R (l₁ ++ l₂) (l₁' ++ l₂') → List.Forall₂ R l₁ l₁'
  | [], [], _, _, _, _ => .nil
  | _ :: _, _ :: _, _, _, h, .cons hab H =>
    .cons hab (forall₂_append_left (Nat.succ.inj h) H)
  | [], _ :: _, _, _, h, _ => nomatch h
  | _ :: _, [], _, _, h, _ => nomatch h

/-- To relate a type to every type of `e`, it suffices to relate it to the
syntax-directed ones: conversions on the second typing are appended as links. -/
theorem HasTypeStrong.chain_peel
    (H : ∀ {B}, env.HasTypeStrong U Γ e B false → env.TypeChain U Γ A B)
    (h2 : env.HasTypeStrong U Γ e B b) : env.TypeChain U Γ A B := by
  cases b with
  | false => exact H h2
  | true =>
    generalize hb : true = b at h2
    induction h2 with
    | base h => exact H h
    | defeq _ h1 _ _ _ _ _ ih => exact (ih H rfl).tail h1.defeq
    | _ => cases hb

/-- The leaf case of (ii): a leaf is definitionally equal at some type in the base context;
weaken it and align the type with (i) at the current node. -/
theorem congrUB_leaf (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hi : ∀ {B b₂}, env.HasTypeStrong U Γ e B b₂ → env.TypeChain U Γ A B)
    (W : Ctx.LiftN k 0 Γ₀ Γ) (he : e = a₁.liftN k) (h : env.IsDefEqU U Γ₀ a₁ a₂) :
    env.IsDefEq U Γ (a₁.liftN k) (a₂.liftN k) A := by
  subst he
  obtain ⟨Y, hY⟩ := h
  have hY' := hY.weakN henv.ordered W
  exact (hi (hY'.strong henv hΓ).hasType'.1).symm.defeqDF hY'

theorem HasTypeStrong.uniq_congr (henv : env.WF) (core : env.ChainHeadInjectivity)
    (h1 : env.HasTypeStrong U Γ e A b) : OnCtx Γ (env.IsType U) →
    (∀ {B b₂}, env.HasTypeStrong U Γ e B b₂ → env.TypeChain U Γ A B) ∧
    (∀ {Γ₀ k e'}, Ctx.LiftN k 0 Γ₀ Γ → CongrUB env U Γ₀ k e e' →
      env.IsDefEq U Γ e e' A) := by
  induction h1 with
  | base _ ih =>
    intro hΓ
    exact ⟨fun h2 => (ih hΓ).1 h2, fun W hc => (ih hΓ).2 W hc⟩
  | defeq _ hAB _ _ _ _ _ ih =>
    intro hΓ
    exact ⟨fun h2 => TypeChain.head hAB.defeq.symm ((ih hΓ).1 h2),
      fun W hc => .defeqDF hAB.defeq ((ih hΓ).2 W hc)⟩
  | @bvar Γ i A' u a1 a2 a3 _ =>
    intro hΓ
    have hi : ∀ {B b₂}, env.HasTypeStrong U Γ (.bvar i) B b₂ → env.TypeChain U Γ A' B := by
      intro B b₂ h2
      refine HasTypeStrong.chain_peel (fun h2 => ?_) h2
      cases h2 with
      | bvar b1 _ _ => cases a1.uniq b1; exact .refl a3.hasType
    refine ⟨hi, fun {Γ₀ k e'} W hc => ?_⟩
    generalize hx : VExpr.bvar i = x at hc
    cases hc with
    | leaf h => exact congrUB_leaf henv hΓ hi W hx h
    | bvar => cases hx; exact .bvar a1
    | sort | const | app | proj | lam | forallE => cases hx
  | @sort' l l' Γ a1 a2 a3 =>
    intro hΓ
    have hi : ∀ {B b₂}, env.HasTypeStrong U Γ (.sort l) B b₂ →
        env.TypeChain U Γ (.sort (.succ l')) B := by
      intro B b₂ h2
      refine HasTypeStrong.chain_peel (fun h2 => ?_) h2
      cases h2 with
      | sort' _ b2 b3 => exact .single (.sortDF a2 b2 (VLevel.succ_congr (a3.symm.trans b3)))
    refine ⟨hi, fun {Γ₀ k e'} W hc => ?_⟩
    generalize hx : VExpr.sort l = x at hc
    cases hc with
    | leaf h => exact congrUB_leaf henv hΓ hi W hx h
    | sort h1 h2 =>
      cases hx
      exact .defeqDF (.sortDF (l := .succ _) (l' := .succ _) a1 a2 (VLevel.succ_congr a3))
        (.sortDF a1 h1 h2)
    | bvar | const | app | proj | lam | forallE => cases hx
  | @const c ci ls u Γ a1 a2 a3 _ _ a6 _ _ =>
    intro hΓ
    have hi : ∀ {B b₂}, env.HasTypeStrong U Γ (.const c ls) B b₂ →
        env.TypeChain U Γ (ci.type.instL ls) B := by
      intro B b₂ h2
      refine HasTypeStrong.chain_peel (fun h2 => ?_) h2
      cases h2 with
      | const b1 _ _ _ _ _ => cases a1.symm.trans b1; exact .refl a6.hasType
    refine ⟨hi, fun {Γ₀ k e'} W hc => ?_⟩
    generalize hx : VExpr.const c ls = x at hc
    cases hc with
    | leaf h => exact congrUB_leaf henv hΓ hi W hx h
    | const h1 h2 => cases hx; exact .constDF a1 a2 h1 a3 h2
    | bvar | sort | app | proj | lam | forallE => cases hx
  | @app Γ A u B v f a a1 a2 _ _ _ _ a7 _ _ _ _ ih6 ih7 _ =>
    intro hΓ
    have hi : ∀ {B' b₂}, env.HasTypeStrong U Γ (.app f a) B' b₂ →
        env.TypeChain U Γ (B.inst a) B' := by
      intro B' b₂ h2
      refine HasTypeStrong.chain_peel (fun h2 => ?_) h2
      cases h2 with
      | app _ _ _ _ _ b6 _ _ =>
        have ⟨_, hB⟩ := core.forallE_chain hΓ ((ih6 hΓ).1 b6)
        exact hB.instN henv.ordered a7.hasType .zero
    refine ⟨hi, fun {Γ₀ k e'} W hc => ?_⟩
    generalize hx : VExpr.app f a = x at hc
    cases hc with
    | leaf h => exact congrUB_leaf henv hΓ hi W hx h
    | app h1 h2 => cases hx; exact .appDF ((ih6 hΓ).2 W h1) ((ih7 hΓ).2 W h2)
    | bvar | sort | const | proj | lam | forallE => cases hx
  | @proj typeName info levels params index sourceMajor fieldType Γ fieldLevel major indexArgs
      a1 a2 a3 a4 a5 a6 _ a8 a9 _ a11 a12 ih8 ih10 =>
    intro hΓ
    have hi : ∀ {B b₂}, env.HasTypeStrong U Γ (.proj typeName index major) B b₂ →
        env.TypeChain U Γ fieldType B := by
      intro B b₂ h2
      refine HasTypeStrong.chain_peel (fun h2 => ?_) h2
      cases h2 with
      | proj b1 b2 b3 b4 b5 b6 _ b8 b9 b10 _ b12 =>
        cases henv.ordered.projections_unique a1 b1
        have hmajor := (ih10 hΓ).1 b10
        have hsource := a9.defeq.trans (hmajor.symm.defeqDF b9.defeq).symm
        have hrig := henv.projectionRigid a1
        obtain ⟨-, hls, hargs⟩ := core.rigid_rigid hΓ hrig hrig hmajor
        have hps := forall₂_append_left (a4.trans b4.symm) hargs
        have hc := fieldType_congr henv.ordered a1 hls b2 hps ⟨_, hsource⟩ a6 b6
        exact .single ((ih8 hΓ).2 (.zero []) hc)
    refine ⟨hi, fun {Γ₀ k e'} W hc => ?_⟩
    generalize hx : VExpr.proj typeName index major = x at hc
    cases hc with
    | leaf h => exact congrUB_leaf henv hΓ hi W hx h
    | proj h =>
      cases hx
      exact .projDF a1 a2 a3 a4 a5 a6 a8.hasType a9.defeq
        (a9.defeq.trans ((ih10 hΓ).2 W h)) a11 a12
    | bvar | sort | const | app | lam | forallE => cases hx
  | @lam Γ A u B v body a1 a2 a3 _ _ _ ih3 _ ih5 _ =>
    intro hΓ
    have hΓ' : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, _, a3.hasType⟩
    have hi : ∀ {B' b₂}, env.HasTypeStrong U Γ (.lam A body) B' b₂ →
        env.TypeChain U Γ (.forallE A B) B' := by
      intro B' b₂ h2
      refine HasTypeStrong.chain_peel (fun h2 => ?_) h2
      cases h2 with
      | lam _ _ _ _ b5 _ =>
        exact ((ih5 hΓ').1 b5).map (f := VExpr.forallE _)
          fun h => ⟨_, .forallEDF a3.hasType h⟩
    refine ⟨hi, fun {Γ₀ k e'} W hc => ?_⟩
    generalize hx : VExpr.lam A body = x at hc
    cases hc with
    | leaf h => exact congrUB_leaf henv hΓ hi W hx h
    | lam h1 h2 =>
      cases hx; exact .lamDF ((ih3 hΓ).2 W h1) ((ih5 hΓ').2 W.cons0 h2)
    | bvar | sort | const | app | proj | forallE => cases hx
  | @forallE Γ A u body v a1 a2 a3 _ ih3 ih4 =>
    intro hΓ
    have hΓ' : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, _, a3.hasType⟩
    have hi : ∀ {B b₂}, env.HasTypeStrong U Γ (.forallE A body) B b₂ →
        env.TypeChain U Γ (.sort (.imax u v)) B := by
      intro B b₂ h2
      refine HasTypeStrong.chain_peel (fun h2 => ?_) h2
      cases h2 with
      | forallE b1 b2 b3 b4 =>
        have e1 := core.sort_sort hΓ ((ih3 hΓ).1 b3)
        have e2 := core.sort_sort hΓ' ((ih4 hΓ').1 b4)
        exact .single (.sortDF (l := .imax _ _) (l' := .imax _ _) ⟨a1, a2⟩ ⟨b1, b2⟩
          (VLevel.imax_congr e1 e2))
    refine ⟨hi, fun {Γ₀ k e'} W hc => ?_⟩
    generalize hx : VExpr.forallE A body = x at hc
    cases hc with
    | leaf h => exact congrUB_leaf henv hΓ hi W hx h
    | forallE h1 h2 =>
      cases hx; exact .forallEDF ((ih3 hΓ).2 W h1) ((ih4 hΓ').2 W.cons0 h2)
    | bvar | sort | const | app | proj | lam => cases hx

/-- Uniqueness of types up to a chain, from chain-level head injectivity. -/
theorem HasTypeStrong.uniq_chain_of_chainHeadInjectivity (henv : env.WF) (core : env.ChainHeadInjectivity)
    (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.HasTypeStrong U Γ e A b₁) (h2 : env.HasTypeStrong U Γ e B b₂) :
    env.TypeChain U Γ A B :=
  (h1.uniq_congr henv core hΓ).1 h2

/-- A strongly typed term is definitionally equal, at its type, to every
`CongrUB`-related term. -/
theorem HasTypeStrong.congrUB_defeq (henv : env.WF) (core : env.ChainHeadInjectivity)
    (hΓ : OnCtx Γ (env.IsType U)) (h1 : env.HasTypeStrong U Γ e A b)
    (W : Ctx.LiftN k 0 Γ₀ Γ) (hc : CongrUB env U Γ₀ k e e') :
    env.IsDefEq U Γ e e' A :=
  (h1.uniq_congr henv core hΓ).2 W hc

/-- A chain starting at a type of sort `u` collapses to one definitional equality at
`sort u`: each link is retyped at `sort u` using `uniq_chain_of_chainHeadInjectivity` on its
left endpoint and `sort_sort`. -/
theorem TypeChain.collapse_of_chainHeadInjectivity (henv : env.WF) (core : env.ChainHeadInjectivity)
    (hΓ : OnCtx Γ (env.IsType U)) (H : env.TypeChain U Γ A B)
    (hA : env.HasType U Γ A (.sort u)) : env.IsDefEq U Γ A B (.sort u) := by
  have retype {X Y w} (hX : env.HasType U Γ X (.sort u))
      (h : env.IsDefEq U Γ X Y (.sort w)) : env.IsDefEq U Γ X Y (.sort u) := by
    have s1 := (hX.strong henv hΓ).hasType'.1
    have s2 := (h.strong henv hΓ).hasType'.1
    have e := core.sort_sort hΓ (s2.uniq_chain_of_chainHeadInjectivity henv core hΓ s1)
    exact .defeqDF (.sortDF (h.sort_r henv.ordered hΓ) (hX.sort_r henv.ordered hΓ) e) h
  induction H with
  | single h => let ⟨_, h⟩ := h; exact retype hA h
  | tail _ h ih => let ⟨_, h⟩ := h; exact ih.trans (retype ih.hasType.2 h)

end VEnv
end Lean4Lean
