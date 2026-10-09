import Lean4Lean.Verify.Typing.Syntactic.Typed

/-!
# The `TrTyped` interface

`TrTyped env Us Δ e e'` (`Syntactic/Typed.lean`) is equivalent to `TrExprS` over an ordered
environment and a well-formed context (`TrExprS.iff_typed`). This file gives it the interface of
an inductive relation with `TrExprS`'s rules, so that a consumer can switch between the two
mechanically:

* smart constructors with the premises of the `TrExprS` constructors (`TrTyped.app h1 h2 hf ha`,
  ...); only `bvar` and `fvar` take the environment and the context's well-formedness in
  addition, because the typing of a looked-up value comes from the context;
* inversion lemmas (`TrTyped.app_inv`, ...) returning the premises of the matching `TrExprS`
  constructor; the syntactic ones (`bvar`, `fvar`, `sort`, `lit`, `mdata`) need no hypothesis,
  the others recover their typing premises by inverting the typing of the result and need the
  environment and the context;
* an induction principle `TrTyped.induction` whose cases are exactly `TrExprS`'s, with `TrTyped`
  subderivations. It takes the environment's order and the well-formedness of the context, so it
  is not an `@[induction_eliminator]` (whose arguments must all be targets or cases); it is
  applied as `TrTyped.induction henv (motive := ...) ... hΔ H`.
-/

namespace Lean4Lean
open Lean4Lean VEnv Lean

namespace TrTyped
variable {env : VEnv} {Us : List Name}

theorem toTrSyn (H : TrTyped env Us Δ e e') : TrSyn Us Δ e e' := H.1

theorem wf (H : TrTyped env Us Δ e e') : VExpr.WF env Us.length Δ.toCtx e' := H.2.1

theorem residual (H : TrTyped env Us Δ e e') : TrResidual env Us Δ e := H.2.2

theorem unique (H1 : TrTyped env Us Δ e e₁) (H2 : TrTyped env Us Δ e e₂) : e₁ = e₂ :=
  H1.1.unique H2.1

theorem toTrExprS (henv : env.Ordered) (hΔ : Δ.WF env Us.length) (H : TrTyped env Us Δ e e') :
    TrExprS env Us Δ e e' := (TrExprS.iff_typed henv hΔ).2 H

theorem _root_.Lean4Lean.TrExprS.toTrTyped (henv : env.Ordered) (hΔ : Δ.WF env Us.length)
    (H : TrExprS env Us Δ e e') : TrTyped env Us Δ e e' := (TrExprS.iff_typed henv hΔ).1 H

/-! ### Constructors -/

theorem bvar (henv : env.Ordered) (hΔ : Δ.WF env Us.length)
    (h : Δ.find? (.inl i) = some (e, A)) : TrTyped env Us Δ (.bvar i) e :=
  ⟨.bvar h, ⟨_, hΔ.find?_wf henv h⟩, .bvar⟩

theorem fvar (henv : env.Ordered) (hΔ : Δ.WF env Us.length)
    (h : Δ.find? (.inr fv) = some (e, A)) : TrTyped env Us Δ (.fvar fv) e :=
  ⟨.fvar h, ⟨_, hΔ.find?_wf henv h⟩, .fvar⟩

theorem sort (h : VLevel.ofLevel Us u = some u') : TrTyped env Us Δ (.sort u) (.sort u') :=
  ⟨.sort h, ⟨_, HasType.sort (.of_ofLevel h)⟩, .sort⟩

theorem const (h1 : env.constants c = some ci) (h2 : us.mapM (VLevel.ofLevel Us) = some us')
    (h3 : us.length = ci.uvars) : TrTyped env Us Δ (.const c us) (.const c us') :=
  ⟨.const h2, ⟨_, HasType.const h1 (.of_mapM_ofLevel h2)
    ((List.mapM_eq_some.1 h2).length_eq.symm.trans h3)⟩, .const⟩

theorem app (h1 : env.HasType Us.length Δ.toCtx f' (.forallE A B))
    (h2 : env.HasType Us.length Δ.toCtx a' A)
    (hf : TrTyped env Us Δ f f') (ha : TrTyped env Us Δ a a') :
    TrTyped env Us Δ (.app f a) (.app f' a') :=
  ⟨.app hf.1 ha.1, ⟨_, h1.app h2⟩, .app hf.2.2 ha.2.2⟩

theorem lam (h1 : env.IsType Us.length Δ.toCtx ty')
    (hty : TrTyped env Us Δ ty ty') (hbody : TrTyped env Us ((none, .vlam ty') :: Δ) body body') :
    TrTyped env Us Δ (.lam name ty body bi) (.lam ty' body') :=
  let ⟨_, h1⟩ := h1
  let ⟨_, h2⟩ := hbody.2.1
  ⟨.lam hty.1 hbody.1, ⟨_, h1.lam h2⟩, .lam hty.1 hty.2.2 hbody.2.2⟩

theorem forallE (h1 : env.IsType Us.length Δ.toCtx ty')
    (h2 : env.IsType Us.length (ty' :: Δ.toCtx) body')
    (hty : TrTyped env Us Δ ty ty') (hbody : TrTyped env Us ((none, .vlam ty') :: Δ) body body') :
    TrTyped env Us Δ (.forallE name ty body bi) (.forallE ty' body') :=
  let ⟨_, h1⟩ := h1
  let ⟨_, h2⟩ := h2
  ⟨.forallE hty.1 hbody.1, ⟨_, h1.forallE h2⟩, .forallE hty.1 hty.2.2 hbody.2.2⟩

theorem letE (h1 : env.HasType Us.length Δ.toCtx val' ty')
    (hty : TrTyped env Us Δ ty ty') (hval : TrTyped env Us Δ val val')
    (hbody : TrTyped env Us ((none, .vlet ty' val') :: Δ) body body') :
    TrTyped env Us Δ (.letE name ty val body nd) body' :=
  ⟨.letE hty.1 hval.1 hbody.1, hbody.2.1, .letE hty.1 hval.1 h1 hty.2.2 hval.2.2 hbody.2.2⟩

theorem lit (h1 : env.ContainsLits l) (h : TrTyped env Us Δ l.toConstructor e) :
    TrTyped env Us Δ (.lit l) e :=
  ⟨.lit h.1, h.2.1, .lit h1 h.2.2⟩

theorem mdata (h : TrTyped env Us Δ e e') : TrTyped env Us Δ (.mdata d e) e' :=
  ⟨.mdata h.1, h.2.1, .mdata h.2.2⟩

theorem proj (h : TrTyped env Us Δ e e') (h2 : VExpr.WF env Us.length Δ.toCtx (.proj s i e')) :
    TrTyped env Us Δ (.proj s i e) (.proj s i e') :=
  ⟨.proj h.1, h2, .proj h.2.2⟩

/-! ### Inversion -/

theorem bvar_inv (H : TrTyped env Us Δ (.bvar i) e') : ∃ A, Δ.find? (.inl i) = some (e', A) :=
  let ⟨.bvar h, _⟩ := H; ⟨_, h⟩

theorem fvar_inv (H : TrTyped env Us Δ (.fvar fv) e') : ∃ A, Δ.find? (.inr fv) = some (e', A) :=
  let ⟨.fvar h, _⟩ := H; ⟨_, h⟩

theorem sort_inv (H : TrTyped env Us Δ (.sort u) e') :
    ∃ u', VLevel.ofLevel Us u = some u' ∧ e' = .sort u' :=
  let ⟨.sort h, _⟩ := H; ⟨_, h, rfl⟩

theorem const_inv (henv : env.Ordered) (hΔ : Δ.WF env Us.length)
    (H : TrTyped env Us Δ (.const c us) e') :
    ∃ ci us', env.constants c = some ci ∧ us.mapM (VLevel.ofLevel Us) = some us' ∧
      us.length = ci.uvars ∧ e' = .const c us' :=
  let .const h1 h2 h3 := H.toTrExprS henv hΔ
  ⟨_, _, h1, h2, h3, rfl⟩

theorem app_inv (henv : env.Ordered) (hΔ : Δ.WF env Us.length)
    (H : TrTyped env Us Δ (.app f a) e') :
    ∃ f' a' A B, e' = .app f' a' ∧ env.HasType Us.length Δ.toCtx f' (.forallE A B) ∧
      env.HasType Us.length Δ.toCtx a' A ∧
      TrTyped env Us Δ f f' ∧ TrTyped env Us Δ a a' :=
  let .app h1 h2 hf ha := H.toTrExprS henv hΔ
  ⟨_, _, _, _, rfl, h1, h2, hf.toTrTyped henv hΔ, ha.toTrTyped henv hΔ⟩

theorem lam_inv (henv : env.Ordered) (hΔ : Δ.WF env Us.length)
    (H : TrTyped env Us Δ (.lam name ty body bi) e') :
    ∃ ty' body', e' = .lam ty' body' ∧ env.IsType Us.length Δ.toCtx ty' ∧
      TrTyped env Us Δ ty ty' ∧ TrTyped env Us ((none, .vlam ty') :: Δ) body body' :=
  let .lam h1 hty hbody := H.toTrExprS henv hΔ
  ⟨_, _, rfl, h1, hty.toTrTyped henv hΔ, hbody.toTrTyped henv ⟨hΔ, nofun, h1⟩⟩

theorem forallE_inv (henv : env.Ordered) (hΔ : Δ.WF env Us.length)
    (H : TrTyped env Us Δ (.forallE name ty body bi) e') :
    ∃ ty' body', e' = .forallE ty' body' ∧ env.IsType Us.length Δ.toCtx ty' ∧
      env.IsType Us.length (ty' :: Δ.toCtx) body' ∧
      TrTyped env Us Δ ty ty' ∧ TrTyped env Us ((none, .vlam ty') :: Δ) body body' :=
  let .forallE h1 h2 hty hbody := H.toTrExprS henv hΔ
  ⟨_, _, rfl, h1, h2, hty.toTrTyped henv hΔ, hbody.toTrTyped henv ⟨hΔ, nofun, h1⟩⟩

theorem letE_inv (henv : env.Ordered) (hΔ : Δ.WF env Us.length)
    (H : TrTyped env Us Δ (.letE name ty val body nd) e') :
    ∃ ty' val', env.HasType Us.length Δ.toCtx val' ty' ∧
      TrTyped env Us Δ ty ty' ∧ TrTyped env Us Δ val val' ∧
      TrTyped env Us ((none, .vlet ty' val') :: Δ) body e' :=
  let .letE h1 hty hval hbody := H.toTrExprS henv hΔ
  ⟨_, _, h1, hty.toTrTyped henv hΔ, hval.toTrTyped henv hΔ,
    hbody.toTrTyped henv ⟨hΔ, nofun, h1⟩⟩

theorem lit_inv (H : TrTyped env Us Δ (.lit l) e') :
    env.ContainsLits l ∧ TrTyped env Us Δ l.toConstructor e' :=
  let ⟨.lit s, h, .lit hl r⟩ := H; ⟨hl, s, h, r⟩

theorem mdata_inv (H : TrTyped env Us Δ (.mdata d e) e') : TrTyped env Us Δ e e' :=
  let ⟨.mdata s, h, .mdata r⟩ := H; ⟨s, h, r⟩

theorem proj_inv (henv : env.Ordered) (hΔ : Δ.WF env Us.length)
    (H : TrTyped env Us Δ (.proj s i e) e') :
    ∃ e₀', e' = .proj s i e₀' ∧ TrTyped env Us Δ e e₀' ∧
      VExpr.WF env Us.length Δ.toCtx (.proj s i e₀') :=
  let .proj h h2 := H.toTrExprS henv hΔ
  ⟨_, rfl, h.toTrTyped henv hΔ, h2⟩

theorem mvar_inv (H : TrTyped env Us Δ (.mvar m) e') : False := nomatch H.1

/-! ### Induction -/

/-- Induction on a typed translation with the cases of `TrExprS`. The subderivations are
`TrTyped`, and every context the motive is applied to is well formed. -/
theorem induction (henv : env.Ordered)
    {motive : VLCtx → Expr → VExpr → Prop}
    (bvar : ∀ {e A Δ i}, Δ.WF env Us.length → Δ.find? (.inl i) = some (e, A) →
      motive Δ (.bvar i) e)
    (fvar : ∀ {e A Δ fv}, Δ.WF env Us.length → Δ.find? (.inr fv) = some (e, A) →
      motive Δ (.fvar fv) e)
    (sort : ∀ {u u' Δ}, Δ.WF env Us.length → VLevel.ofLevel Us u = some u' →
      motive Δ (.sort u) (.sort u'))
    (const : ∀ {c ci us us' Δ}, Δ.WF env Us.length → env.constants c = some ci →
      us.mapM (VLevel.ofLevel Us) = some us' → us.length = ci.uvars →
      motive Δ (.const c us) (.const c us'))
    (app : ∀ {Δ f' A B a' f a}, Δ.WF env Us.length →
      env.HasType Us.length Δ.toCtx f' (.forallE A B) →
      env.HasType Us.length Δ.toCtx a' A →
      TrTyped env Us Δ f f' → TrTyped env Us Δ a a' →
      motive Δ f f' → motive Δ a a' → motive Δ (.app f a) (.app f' a'))
    (lam : ∀ {Δ ty' ty body body' name bi}, Δ.WF env Us.length →
      env.IsType Us.length Δ.toCtx ty' →
      TrTyped env Us Δ ty ty' → TrTyped env Us ((none, .vlam ty') :: Δ) body body' →
      motive Δ ty ty' → motive ((none, .vlam ty') :: Δ) body body' →
      motive Δ (.lam name ty body bi) (.lam ty' body'))
    (forallE : ∀ {Δ ty' body' ty body name bi}, Δ.WF env Us.length →
      env.IsType Us.length Δ.toCtx ty' →
      env.IsType Us.length (ty' :: Δ.toCtx) body' →
      TrTyped env Us Δ ty ty' → TrTyped env Us ((none, .vlam ty') :: Δ) body body' →
      motive Δ ty ty' → motive ((none, .vlam ty') :: Δ) body body' →
      motive Δ (.forallE name ty body bi) (.forallE ty' body'))
    (letE : ∀ {Δ val' ty' ty val body body' name nd}, Δ.WF env Us.length →
      env.HasType Us.length Δ.toCtx val' ty' →
      TrTyped env Us Δ ty ty' → TrTyped env Us Δ val val' →
      TrTyped env Us ((none, .vlet ty' val') :: Δ) body body' →
      motive Δ ty ty' → motive Δ val val' → motive ((none, .vlet ty' val') :: Δ) body body' →
      motive Δ (.letE name ty val body nd) body')
    (lit : ∀ {l Δ e}, Δ.WF env Us.length → env.ContainsLits l →
      TrTyped env Us Δ l.toConstructor e → motive Δ l.toConstructor e → motive Δ (.lit l) e)
    (mdata : ∀ {Δ e e' d}, Δ.WF env Us.length → TrTyped env Us Δ e e' → motive Δ e e' →
      motive Δ (.mdata d e) e')
    (proj : ∀ {Δ e e' s i}, Δ.WF env Us.length → TrTyped env Us Δ e e' →
      VExpr.WF env Us.length Δ.toCtx (.proj s i e') → motive Δ e e' →
      motive Δ (.proj s i e) (.proj s i e'))
    {Δ e e'} (hΔ : Δ.WF env Us.length) (H : TrTyped env Us Δ e e') : motive Δ e e' := by
  replace H := H.toTrExprS henv hΔ
  induction H with
  | bvar h => exact bvar hΔ h
  | fvar h => exact fvar hΔ h
  | sort h => exact sort hΔ h
  | const h1 h2 h3 => exact const hΔ h1 h2 h3
  | app h1 h2 hf ha ih1 ih2 =>
    exact app hΔ h1 h2 (hf.toTrTyped henv hΔ) (ha.toTrTyped henv hΔ) (ih1 hΔ) (ih2 hΔ)
  | lam h1 hty hbody ih1 ih2 =>
    have hΔ' : VLCtx.WF env Us.length ((none, .vlam _) :: _) := ⟨hΔ, nofun, h1⟩
    exact lam hΔ h1 (hty.toTrTyped henv hΔ) (hbody.toTrTyped henv hΔ') (ih1 hΔ) (ih2 hΔ')
  | forallE h1 h2 hty hbody ih1 ih2 =>
    have hΔ' : VLCtx.WF env Us.length ((none, .vlam _) :: _) := ⟨hΔ, nofun, h1⟩
    exact forallE hΔ h1 h2 (hty.toTrTyped henv hΔ) (hbody.toTrTyped henv hΔ') (ih1 hΔ)
      (ih2 hΔ')
  | letE h1 hty hval hbody ih1 ih2 ih3 =>
    have hΔ' : VLCtx.WF env Us.length ((none, .vlet _ _) :: _) := ⟨hΔ, nofun, h1⟩
    exact letE hΔ h1 (hty.toTrTyped henv hΔ) (hval.toTrTyped henv hΔ)
      (hbody.toTrTyped henv hΔ') (ih1 hΔ) (ih2 hΔ) (ih3 hΔ')
  | lit h1 h ih => exact lit hΔ h1 (h.toTrTyped henv hΔ) (ih hΔ)
  | mdata h ih => exact mdata hΔ (h.toTrTyped henv hΔ) (ih hΔ)
  | proj h h2 ih => exact proj hΔ (h.toTrTyped henv hΔ) h2 (ih hΔ)

end TrTyped

end Lean4Lean
