import Lean4Lean.Verify.Typing.Syntactic.Typed
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Theory.Typing.Strengthening.Lift

/-!
# The strengthening boundary

With translation split into syntax and typing, strengthening splits the same way:

* restricting the *syntax* of a translation is elementary: a source that does not use some
  binders or free variables translates without them, and its translation in the larger context
  is the lift (`TrSyn.lowerBV`, `TrSyn.restrictFV`);
* restricting the *typing* is not (section 5.1 of the design notes): what remains of a
  typed translation in the smaller context is exactly the typing of the restricted result and the
  residual of the restricted source (`TrExprS.lowerBV_iff`).

The projection walk's certificate (`TelTrN`, `Verify/Typing/TelescopeTranslation.lean`) is built
the same way: a syntactic translation together with the typing-only certificate `TelWF`, which
records the typing of each residual telescope in its smaller context.
-/

namespace Lean4Lean
open Lean4Lean VEnv Lean

/-- **The strengthening boundary.** A typed translation of a source that does not use some
bound variables is the lift of a syntactic translation in the smaller context, for free; it is a
typed translation there exactly when its result is well typed there and the source's residual
obligations hold there. Neither of the latter follows from the larger context in general. -/
theorem TrExprS.lowerBV_iff (henv : env.Ordered) (W : VLCtx.BVLift Δ Δ' dn dk n k)
    (hΔ : Δ.WF env Us.length) (H : TrExprS env Us Δ' (Expr.liftLooseBVars' e₀ dk dn) e') :
    ∃ e₀', e' = e₀'.liftN n k ∧ TrSyn Us Δ e₀ e₀' ∧
      (TrExprS env Us Δ e₀ e₀' ↔
        VExpr.WF env Us.length Δ.toCtx e₀' ∧ TrResidual env Us Δ e₀) := by
  obtain ⟨e₀', s, rfl⟩ := H.toTrSyn.lowerBV W
  exact ⟨e₀', rfl, s, fun h => ⟨h.wf henv hΔ, h.residual⟩, fun ⟨h1, h2⟩ => s.toTrExprS henv hΔ h1 h2⟩

/-- The same for free variables: no typing is involved in the syntactic part. -/
theorem TrExprS.restrictFV_iff (henv : env.Ordered) (W : VLCtx.FVLift Δ Δ' dk n k)
    (hΔ' : Δ'.WF env Us.length) (hΔ : Δ.WF env Us.length)
    (H : TrExprS env Us Δ' e e') (hfv : FVarsIn (· ∈ Δ.fvars) e) :
    ∃ e₀', e' = e₀'.liftN n k ∧ TrSyn Us Δ e e₀' ∧
      (TrExprS env Us Δ e e₀' ↔
        VExpr.WF env Us.length Δ.toCtx e₀' ∧ TrResidual env Us Δ e) := by
  obtain ⟨e₀', s, rfl⟩ := H.toTrSyn.restrictFV W hΔ'.fvars_nodup hfv
  exact ⟨e₀', rfl, s, fun h => ⟨h.wf henv hΔ, h.residual⟩, fun ⟨h1, h2⟩ => s.toTrExprS henv hΔ h1 h2⟩

/-! ### Under a strengthening hypothesis

When the environment satisfies `VEnv.Strengthening` the typing part of the boundary can be
crossed as well. These are used only by the verification of the checker's global cache mode,
where the hypothesis comes from a `GlobalCacheLicense`. -/

theorem VLCtx.FVLift'.cons_vlam (W : VLCtx.FVLift' Δ Δ' dk l k)
    (h : ty₀.lift' (l.consN k) = ty') :
    VLCtx.FVLift' ((none, .vlam ty₀) :: Δ) ((none, .vlam ty') :: Δ') (dk + 1) l (k + 1) := by
  subst h; exact W.cons_bvar (.vlam ty₀)

theorem VLCtx.FVLift'.cons_vlet (W : VLCtx.FVLift' Δ Δ' dk l k)
    (h1 : ty₀.lift' (l.consN k) = ty') (h2 : val₀.lift' (l.consN k) = val') :
    VLCtx.FVLift' ((none, .vlet ty₀ val₀) :: Δ) ((none, .vlet ty' val') :: Δ') (dk + 1) l k := by
  subst h1 h2; exact W.cons_bvar (.vlet ty₀ val₀)

variable! (henv : VEnv.WF env) (hs : env.Strengthening) in
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
    have h1' := (HasType.weak'_iff henv hs hΔ'.toCtx W.toCtx).1 (by rw [← e1, ← e2] at h1; exact h1)
    exact .letE s1 s2 h1' (ih1 W hΔ' s1) (ih2 W hΔ' s2) (ih3 W' ⟨hΔ', nofun, h1⟩ s3)
  | lit h1 _ ih => let .lit s := hsyn; exact .lit h1 (ih W hΔ' s)
  | mdata _ ih => let .mdata s := hsyn; exact .mdata (ih W hΔ' s)
  | proj _ _ ih => let .proj s := hsyn; exact .proj (ih W hΔ' s)

variable! (henv : VEnv.WF env) (hs : env.Strengthening) in
/-- **Strengthening of a typed translation**: a source scoped by `Δ` that has a typed translation
in an extension `Δ'` of `Δ` by free variables has one in `Δ`, of which the larger one is the lift.
The syntax is `TrSyn.restrictFV'`-style restriction; the typing is `VExpr.WF.weak'_iff`. -/
theorem TrExprS.restrictFV'_inv {Us : List Name}
    (W : VLCtx.FVLift' Δ Δ' dk l k) (hΔ' : Δ'.WF env Us.length) (hΔ : Δ.WF env Us.length)
    (H : TrExprS env Us Δ' e e') (hfv : FVarsIn (· ∈ Δ.fvars) e) :
    ∃ e₀, TrExprS env Us Δ e e₀ ∧ e' = e₀.lift' (l.consN k) := by
  have hc : Closed e Δ.bvars := W.bvars_eq ▸ H.closed
  obtain ⟨e₀, s⟩ := TrSyn.exists_of_scoped hc hfv H.toTrSyn.levelParamsIn
  have heq : e' = e₀.lift' (l.consN k) := H.toTrSyn.unique (s.weakFV' W hΔ'.fvars_nodup)
  refine ⟨e₀, s.toTrExprS henv.ordered hΔ ?_ (H.residual_restrictFV' henv hs W hΔ' s), heq⟩
  exact (VExpr.WF.weak'_iff henv hs hΔ'.toCtx W.toCtx).1 (heq ▸ H.wf henv.ordered hΔ')

variable! (henv : VEnv.WF env) (hs : env.Strengthening) in
/-- `TrExprS.restrictFV'_inv` for the removal of free variables only. -/
theorem TrExprS.restrictFV_inv {Us : List Name}
    (W : VLCtx.FVLift Δ Δ' 0 n 0) (hΔ' : Δ'.WF env Us.length)
    (H : TrExprS env Us Δ' e e') (hfv : FVarsIn (· ∈ Δ.fvars) e) :
    ∃ e₀, TrExprS env Us Δ e e₀ ∧ e' = e₀.liftN n := by
  obtain ⟨e₀, h, rfl⟩ := H.restrictFV'_inv henv hs W.toFVLift' hΔ' (W.wf henv hΔ') hfv
  exact ⟨e₀, h, by simpa using VExpr.lift'_consN_skipN (e := e₀) (n := n) (k := 0)⟩

end Lean4Lean
