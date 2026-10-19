import Lean4Lean.Verify.Typing.Lemmas

namespace Lean4Lean
open Lean

/-- Erasing a named local definition preserves the semantic context. Anonymous
native binders may be retained above it while traversing a translated expression. -/
inductive VLCtx.EraseLet (removed : FVarId) : VLCtx → VLCtx → Prop
  | zero : EraseLet removed Δ ((some (removed, support), .vlet domain value) :: Δ)
  | cons_bvar (d) : EraseLet removed Δ Δ' →
      EraseLet removed ((none, d) :: Δ) ((none, d) :: Δ')

theorem VLCtx.EraseLet.toCtx_eq (W : EraseLet removed Δ Δ') : Δ'.toCtx = Δ.toCtx := by
  induction W with
  | zero => rfl
  | cons_bvar d _ ih => cases d <;> simp only [toCtx, ih]

theorem VLCtx.EraseLet.find?_eq (W : EraseLet removed Δ Δ')
    (unused : v ≠ .inr removed) : Δ'.find? v = Δ.find? v := by
  induction W generalizing v with
  | @zero Δ support domain value =>
    cases v with
    | inl i =>
      simp only [find?, next, VLocalDecl.depth, VExpr.liftN_zero]
      cases Δ.find? (.inl i) <;> rfl
    | inr fv =>
      have ne : removed ≠ fv := fun h => unused (by simp [h])
      simp only [find?, next, beq_eq_false_iff_ne.mpr ne, Bool.false_eq_true,
        ↓reduceIte, VLocalDecl.depth, VExpr.liftN_zero]
      cases Δ.find? (.inr fv) <;> rfl
  | cons_bvar d _ ih =>
    cases v with
    | inl i =>
      cases i with
      | zero => rfl
      | succ i => simp only [find?, next]; rw [ih (v := .inl i) (by simp)]
    | inr fv => simp only [find?, next]; rw [ih unused]

/-- An unused native local let adds no model binder, so erasure keeps exactly the
same translated expression. This requires no semantic strengthening principle. -/
theorem TrExprS.eraseLet (W : VLCtx.EraseLet removed Δ Δ')
    (H : TrExprS env Us Δ' e e') (unused : FVarsIn (· ≠ removed) e) :
    TrExprS env Us Δ e e' := by
  induction H generalizing Δ with
  | @bvar Δ' _ _ i h => exact .bvar ((W.find?_eq (v := .inl i) (by simp)) ▸ h)
  | @fvar Δ' _ _ fv h =>
    exact .fvar ((W.find?_eq (v := .inr fv) (by simpa [FVarsIn] using unused)) ▸ h)
  | sort h => exact .sort h
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (W.toCtx_eq ▸ h1) (W.toCtx_eq ▸ h2) (ih1 W unused.1) (ih2 W unused.2)
  | lam h _ _ ih1 ih2 =>
    exact .lam (W.toCtx_eq ▸ h) (ih1 W unused.1) (ih2 (W.cons_bvar _) unused.2)
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (W.toCtx_eq ▸ h1) (W.toCtx_eq ▸ h2)
      (ih1 W unused.1) (ih2 (W.cons_bvar _) unused.2)
  | letE h _ _ _ ih1 ih2 ih3 =>
    exact .letE (W.toCtx_eq ▸ h) (ih1 W unused.1) (ih2 W unused.2.1)
      (ih3 (W.cons_bvar _) unused.2.2)
  | lit h _ ih => exact .lit h (ih W .toConstructor)
  | mdata _ ih => exact .mdata (ih W unused)
  | proj _ h ih => exact .proj (ih W unused) (W.toCtx_eq ▸ h)

/-- Reconstructing a telescope may drop a let whose abstraction mentions no
bound occurrence. Erasure keeps the exact model context and result; the let
value is never substituted beneath retained binders. -/
theorem TrExprS.eraseAbstractedLet
    (H : TrExprS env Us ((some (removed, support), .vlet domain value) :: Δ) e e')
    (closed : Closed e)
    (unused : (e.abstract1 removed).hasLooseBVar' 0 = false) :
    TrExprS env Us Δ ((e.abstract1 removed).lowerLooseBVars' 1 1) e' := by
  have scope := closed.looseBVarRange_le
  have unchanged : e.abstract1 removed = e := by
    rw [Expr.abstract1_eq_liftLooseBVars unused, Expr.liftLooseBVars_eq_self scope]
  have free : FVarsIn (· ≠ removed) e := (H.fvarsIn.of_abstract1 (v := removed) (k := 0)
    (by simpa only [unchanged] using scope)).mono
    (fun _ member => member.2)
  rw [Expr.lowerLooseBVars_eq_instantiate unused (v := e)]
  simpa only [unchanged, Expr.instantiate1'_eq_self scope] using H.eraseLet .zero free


theorem TrExpr.eraseLet (W : VLCtx.EraseLet removed Δ Δ')
    (H : TrExpr env Us Δ' e e') (unused : FVarsIn (· ≠ removed) e) :
    TrExpr env Us Δ e e' :=
  let ⟨_, translated, equal⟩ := H
  ⟨_, translated.eraseLet W unused, W.toCtx_eq ▸ equal⟩

/-- Inserting an unused native let also preserves the exact model expression. -/
theorem TrExprS.insertLet (W : VLCtx.EraseLet removed Δ Δ')
    (H : TrExprS env Us Δ e e') (unused : FVarsIn (· ≠ removed) e) :
    TrExprS env Us Δ' e e' := by
  induction H generalizing Δ' with
  | @bvar Δ _ _ i h => exact .bvar ((W.find?_eq (v := .inl i) (by simp)).symm ▸ h)
  | @fvar Δ _ _ fv h =>
    exact .fvar ((W.find?_eq (v := .inr fv) (by simpa [FVarsIn] using unused)).symm ▸ h)
  | sort h => exact .sort h
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (W.toCtx_eq.symm ▸ h1) (W.toCtx_eq.symm ▸ h2)
      (ih1 W unused.1) (ih2 W unused.2)
  | lam h _ _ ih1 ih2 =>
    exact .lam (W.toCtx_eq.symm ▸ h) (ih1 W unused.1) (ih2 (W.cons_bvar _) unused.2)
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (W.toCtx_eq.symm ▸ h1) (W.toCtx_eq.symm ▸ h2)
      (ih1 W unused.1) (ih2 (W.cons_bvar _) unused.2)
  | letE h _ _ _ ih1 ih2 ih3 =>
    exact .letE (W.toCtx_eq.symm ▸ h) (ih1 W unused.1) (ih2 W unused.2.1)
      (ih3 (W.cons_bvar _) unused.2.2)
  | lit h _ ih => exact .lit h (ih W .toConstructor)
  | mdata _ ih => exact .mdata (ih W unused)
  | proj _ h ih => exact .proj (ih W unused) (W.toCtx_eq.symm ▸ h)

theorem TrExpr.insertLet (W : VLCtx.EraseLet removed Δ Δ')
    (H : TrExpr env Us Δ e e') (unused : FVarsIn (· ≠ removed) e) :
    TrExpr env Us Δ' e e' :=
  let ⟨_, translated, equal⟩ := H
  ⟨_, translated.insertLet W unused, W.toCtx_eq.symm ▸ equal⟩

end Lean4Lean
