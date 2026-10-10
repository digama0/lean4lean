import Lean4Lean.Verify.Typing.Syntactic.Levels

/-!
# Syntactic translation

`TrSyn Us Δ e e'` is the translation of a kernel expression `e` to a `VExpr` `e'` with no typing
at all: it is `TrExprS` with every typing premise removed and without the environment. It is the
graph of the function `trSyn?`, so it is functional, decidable and computable by `rfl`.

The environment is not needed: the translation of a constant does not look it up (its presence and
universe arity are consequences of the typing of the result, `VExpr.WF.const_inv`), a projection is
translated to the primitive `.proj` node without resolving its structure, and the encoding of a
literal (`Literal.toConstructor`, `VExpr.trLiteral`) does not depend on the environment. The
context is only used for de Bruijn and free-variable resolution (`VLCtx.find?`), including the
inlining of let-bound values.

This file proves that `TrSyn` is a function (`TrSyn.iff_trSyn?`, `TrSyn.unique`), that every typed
translation is one (`TrExprS.toTrSyn`), and that it is defined exactly on the expressions scoped
by the context (`TrSyn.exists_iff`): bound variables below `Δ.bvars`, free variables of `Δ`,
universe parameters in `Us`, and no metavariables.
-/

namespace Lean4Lean
open Lean

/-- Syntactic translation: `TrExprS` without its typing premises and without the environment. -/
inductive TrSyn (Us : List Name) : VLCtx → Expr → VExpr → Prop
  | bvar : Δ.find? (.inl i) = some (e, A) → TrSyn Us Δ (.bvar i) e
  | fvar : Δ.find? (.inr fv) = some (e, A) → TrSyn Us Δ (.fvar fv) e
  | sort : VLevel.ofLevel Us u = some u' → TrSyn Us Δ (.sort u) (.sort u')
  | const : us.mapM (VLevel.ofLevel Us) = some us' → TrSyn Us Δ (.const c us) (.const c us')
  | app : TrSyn Us Δ f f' → TrSyn Us Δ a a' → TrSyn Us Δ (.app f a) (.app f' a')
  | lam : TrSyn Us Δ ty ty' → TrSyn Us ((none, .vlam ty') :: Δ) body body' →
    TrSyn Us Δ (.lam name ty body bi) (.lam ty' body')
  | forallE : TrSyn Us Δ ty ty' → TrSyn Us ((none, .vlam ty') :: Δ) body body' →
    TrSyn Us Δ (.forallE name ty body bi) (.forallE ty' body')
  | letE : TrSyn Us Δ ty ty' → TrSyn Us Δ val val' →
    TrSyn Us ((none, .vlet ty' val') :: Δ) body body' →
    TrSyn Us Δ (.letE name ty val body nd) body'
  | lit : TrSyn Us Δ l.toConstructor e → TrSyn Us Δ (.lit l) e
  | mdata : TrSyn Us Δ e e' → TrSyn Us Δ (.mdata d e) e'
  | proj : TrSyn Us Δ e e' → TrSyn Us Δ (.proj s i e) (.proj s i e')

/-- The syntactic translation as a function. Literals are translated by their closed encoding
`VExpr.trLiteral`, which `TrSyn.lit_iff` shows is the translation of `Literal.toConstructor`. -/
def trSyn? (Us : List Name) : VLCtx → Expr → Option VExpr
  | Δ, .bvar i => (Δ.find? (.inl i)).map (·.1)
  | Δ, .fvar fv => (Δ.find? (.inr fv)).map (·.1)
  | _, .sort u => (VLevel.ofLevel Us u).map .sort
  | _, .const c us => (us.mapM (VLevel.ofLevel Us)).map (.const c)
  | Δ, .app f a => do some (.app (← trSyn? Us Δ f) (← trSyn? Us Δ a))
  | Δ, .lam _ ty body _ => do
    let ty' ← trSyn? Us Δ ty
    some (.lam ty' (← trSyn? Us ((none, .vlam ty') :: Δ) body))
  | Δ, .forallE _ ty body _ => do
    let ty' ← trSyn? Us Δ ty
    some (.forallE ty' (← trSyn? Us ((none, .vlam ty') :: Δ) body))
  | Δ, .letE _ ty val body _ => do
    let ty' ← trSyn? Us Δ ty
    let val' ← trSyn? Us Δ val
    trSyn? Us ((none, .vlet ty' val') :: Δ) body
  | _, .lit l => some (.trLiteral l)
  | Δ, .mdata _ e => trSyn? Us Δ e
  | Δ, .proj s i e => (trSyn? Us Δ e).map (.proj s i)
  | _, .mvar _ => none

/-! ### Literals -/

theorem TrSyn.natLit {Us : List Name} {Δ : VLCtx} :
    ∀ n, TrSyn Us Δ (.lit (.natVal n)) (.natLit n)
  | 0 => .lit (.const rfl)
  | n + 1 => .lit (.app (.const rfl) (natLit n))

theorem TrSyn.listCharLit {Us : List Name} {Δ : VLCtx} (s : List Char) :
    TrSyn Us Δ (s.foldr
      (init := .app (.const ``List.nil [.zero]) (.const ``Char []))
      (fun c e => .app (.app
        (.app (.const ``List.cons [.zero]) (.const ``Char []))
        (.app (.const ``Char.ofNat []) (.lit (.natVal c.toNat)))) e)) (.listCharLit s) := by
  induction s with
  | nil => exact .app (.const rfl) (.const rfl)
  | cons c s ih =>
    exact .app (.app (.app (.const rfl) (.const rfl)) (.app (.const rfl) (natLit _))) ih

theorem TrSyn.trLiteral {Us : List Name} {Δ : VLCtx} :
    ∀ l, TrSyn Us Δ (.lit l) (.trLiteral l)
  | .natVal n => natLit n
  | .strVal s => .lit (.app (.const rfl) (listCharLit s.toList))

/-! ### The function and its graph -/

theorem trSyn?_natLit {Us : List Name} {Δ : VLCtx} :
    ∀ n, trSyn? Us Δ (Expr.natLitToConstructor n) = some (.natLit n)
  | 0 => rfl
  | _ + 1 => rfl

theorem trSyn?_listCharLit {Us : List Name} {Δ : VLCtx} (s : List Char) :
    trSyn? Us Δ (s.foldr
      (init := .app (.const ``List.nil [.zero]) (.const ``Char []))
      (fun c e => .app (.app
        (.app (.const ``List.cons [.zero]) (.const ``Char []))
        (.app (.const ``Char.ofNat []) (.lit (.natVal c.toNat)))) e)) = some (.listCharLit s) := by
  induction s with
  | nil => rfl
  | cons c s ih =>
    simp only [List.foldr_cons, trSyn?, ih]; rfl

theorem trSyn?_toConstructor {Us : List Name} {Δ : VLCtx} :
    ∀ l, trSyn? Us Δ l.toConstructor = some (.trLiteral l)
  | .natVal n => trSyn?_natLit n
  | .strVal s => by
    simp only [Literal.toConstructor, Expr.strLitToConstructor, trSyn?]
    rw [trSyn?_listCharLit]; rfl

theorem TrSyn.eval {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (H : TrSyn Us Δ e e') : trSyn? Us Δ e = some e' := by
  induction H with
  | bvar h | fvar h => simp [trSyn?, h]
  | sort h | const h => simp [trSyn?, h]
  | app _ _ ih1 ih2 => simp [trSyn?, ih1, ih2]
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => simp [trSyn?, ih1, ih2]
  | letE _ _ _ ih1 ih2 ih3 => simp [trSyn?, ih1, ih2, ih3]
  | lit _ ih => rw [trSyn?_toConstructor] at ih; cases ih; rfl
  | mdata _ ih => simpa [trSyn?] using ih
  | proj _ ih => simp [trSyn?, ih]

theorem TrSyn.of_eval {Us : List Name} :
    ∀ {Δ : VLCtx} {e : Expr} {e' : VExpr}, trSyn? Us Δ e = some e' → TrSyn Us Δ e e'
  | Δ, .bvar i, e', h => by
    simp only [trSyn?, Option.map_eq_some_iff] at h
    obtain ⟨⟨_, _⟩, h, rfl⟩ := h; exact .bvar h
  | Δ, .fvar fv, e', h => by
    simp only [trSyn?, Option.map_eq_some_iff] at h
    obtain ⟨⟨_, _⟩, h, rfl⟩ := h; exact .fvar h
  | Δ, .sort u, e', h => by
    simp only [trSyn?, Option.map_eq_some_iff] at h
    obtain ⟨_, h, rfl⟩ := h; exact .sort h
  | Δ, .const c us, e', h => by
    simp only [trSyn?, Option.map_eq_some_iff] at h
    obtain ⟨_, h, rfl⟩ := h; exact .const h
  | Δ, .app f a, e', h => by
    simp only [trSyn?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨_, h1, _, h2, rfl⟩ := h; exact .app (of_eval h1) (of_eval h2)
  | Δ, .lam _ ty body _, e', h => by
    simp only [trSyn?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨_, h1, _, h2, rfl⟩ := h; exact .lam (of_eval h1) (of_eval h2)
  | Δ, .forallE _ ty body _, e', h => by
    simp only [trSyn?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨_, h1, _, h2, rfl⟩ := h; exact .forallE (of_eval h1) (of_eval h2)
  | Δ, .letE _ ty val body _, e', h => by
    simp only [trSyn?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, _, h2, h3⟩ := h; exact .letE (of_eval h1) (of_eval h2) (of_eval h3)
  | Δ, .lit l, e', h => by
    simp only [trSyn?, Option.some.injEq] at h; subst h; exact .trLiteral l
  | Δ, .mdata _ e, e', h => .mdata (of_eval h)
  | Δ, .proj s i e, e', h => by
    simp only [trSyn?, Option.map_eq_some_iff] at h
    obtain ⟨_, h, rfl⟩ := h; exact .proj (of_eval h)
  | Δ, .mvar _, e', h => by simp [trSyn?] at h

/-- `TrSyn` is the graph of `trSyn?`. -/
theorem TrSyn.iff_eval {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr} :
    TrSyn Us Δ e e' ↔ trSyn? Us Δ e = some e' := ⟨eval, of_eval⟩

/-- Syntactic translation is a function. -/
theorem TrSyn.unique {Us : List Name} {Δ : VLCtx} {e : Expr} {e₁ e₂ : VExpr}
    (H1 : TrSyn Us Δ e e₁) (H2 : TrSyn Us Δ e e₂) : e₁ = e₂ :=
  Option.some.inj (H1.eval.symm.trans H2.eval)

/-- Typing erasure: every typed translation is a syntactic one. -/
theorem TrExprS.toTrSyn {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (H : TrExprS env Us Δ e e') : TrSyn Us Δ e e' := by
  induction H with
  | bvar h => exact .bvar h
  | fvar h => exact .fvar h
  | sort h => exact .sort h
  | const _ h _ => exact .const h
  | app _ _ _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | lit _ _ ih => exact .lit ih
  | mdata _ ih => exact .mdata ih
  | proj _ _ ih => exact .proj ih

theorem TrSyn.uniqueCtx {Us : List Name} {Δ₁ Δ₂ : VLCtx} {e : Lean.Expr}
    {e₁ e₂ : VExpr} (hΔ : TrExprS.IsUniqueCtx Δ₁ Δ₂)
    (H1 : TrSyn Us Δ₁ e e₁) (H2 : TrSyn Us Δ₂ e e₂) : e₁ = e₂ := by
  induction H1 generalizing Δ₂ e₂ with cases H2
  | bvar => exact hΔ.find?_uniq ‹_› ‹_›
  | fvar => exact hΔ.find?_uniq ‹_› ‹_›
  | sort h1
  | const h1 => cases h1.symm.trans ‹_›; rfl
  | app _ _ ih1 ih2 => cases ih1 hΔ ‹_›; cases ih2 hΔ ‹_›; rfl
  | lam _ _ ih1 ih2
  | forallE _ _ ih1 ih2 => cases ih1 hΔ ‹_›; cases ih2 (hΔ.cons .vlam) ‹_›; rfl
  | letE _ _ _ ih1 ih2 ih3 => cases ih1 hΔ ‹_›; cases ih2 hΔ ‹_›; exact ih3 (hΔ.cons .vlet) ‹_›
  | lit _ ih => exact ih hΔ ‹_›
  | mdata _ ih => exact ih hΔ ‹_›
  | proj _ ih => cases ih hΔ ‹_›; rfl

/-- Two typed translations of one source in one context are equal: a corollary of the
syntactic statement, with no typing argument. -/
theorem TrExprS.unique_of_syn {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr}
    {e₁ e₂ : VExpr} (H1 : TrExprS env Us Δ e e₁) (H2 : TrExprS env Us Δ e e₂) : e₁ = e₂ :=
  H1.toTrSyn.unique H2.toTrSyn

/-! ### Scoping: where the translation is defined -/

theorem VLCtx.find?_inl_iff {Δ : VLCtx} {i : Nat} :
    (∃ x, Δ.find? (.inl i) = some x) ↔ i < Δ.bvars := by
  induction Δ generalizing i with
  | nil => simp [VLCtx.find?, VLCtx.bvars]
  | cons d Δ ih =>
    obtain ⟨_ | _, d⟩ := d
    · cases i with
      | zero => simp [VLCtx.find?, VLCtx.next, VLCtx.bvars]
      | succ i =>
        simp only [VLCtx.find?, VLCtx.next, VLCtx.bvars, Option.bind_eq_bind]
        rw [Nat.add_lt_add_iff_right, ← ih]
        constructor
        · rintro ⟨_, h⟩; simp only [Option.bind_eq_some_iff] at h
          obtain ⟨x, h, -⟩ := h; exact ⟨x, h⟩
        · rintro ⟨x, h⟩; simp [h]
    · simp only [VLCtx.find?, VLCtx.next, VLCtx.bvars, Option.bind_eq_bind]
      rw [← ih]
      constructor
      · rintro ⟨_, h⟩; simp only [Option.bind_eq_some_iff] at h
        obtain ⟨x, h, -⟩ := h; exact ⟨x, h⟩
      · rintro ⟨x, h⟩; simp [h]

theorem TrSyn.closed {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (H : TrSyn Us Δ e e') : Closed e Δ.bvars := by
  induction H with
  | bvar h => exact VLCtx.find?_inl_iff.1 ⟨_, h⟩
  | fvar | sort | const | lit | mdata => trivial
  | app _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | letE _ _ _ ih1 ih2 ih3 => exact ⟨ih1, ih2, ih3⟩
  | proj _ ih => exact ih

theorem TrSyn.fvarsIn {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (H : TrSyn Us Δ e e') : FVarsIn (· ∈ Δ.fvars) e := by
  induction H with
  | fvar h1 => exact VLCtx.find?_eq_some.1 ⟨_, h1⟩
  | sort h => exact ofLevel_hasMVar h
  | const h =>
    rw [List.mapM_eq_some] at h
    intro _ hl
    have ⟨_, _, h⟩ := Lean4Lean.List.Forall₂.forall_exists_l h _ hl
    exact ofLevel_hasMVar h
  | bvar | lit | mdata => trivial
  | app _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | letE _ _ _ ih1 ih2 ih3 => exact ⟨ih1, ih2, ih3⟩
  | proj _ ih => exact ih

theorem TrSyn.levelParamsIn {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (H : TrSyn Us Δ e e') : e.levelParamsIn Us = true := by
  induction H with
  | sort hu => exact VLevel.ofLevel_paramsIn hu
  | const hlevels =>
    simp only [Expr.levelParamsIn, List.all_eq_true]
    intro level hlevel
    obtain ⟨target, _, htarget⟩ := Lean4Lean.List.Forall₂.forall_exists_l
      (List.mapM_eq_some.mp hlevels) _ hlevel
    exact VLevel.ofLevel_paramsIn htarget
  | bvar | fvar | lit => rfl
  | app _ _ ih1 ih2 | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    simp [Expr.levelParamsIn, ih1, ih2]
  | letE _ _ _ ih1 ih2 ih3 => simp [Expr.levelParamsIn, ih1, ih2, ih3]
  | mdata _ ih | proj _ ih => exact ih

theorem VLevel.ofLevel_of_paramsIn {Us : List Name} :
    ∀ {level : Level}, level.paramsIn Us = true → ∃ t, VLevel.ofLevel Us level = some t
  | .zero, _ => ⟨_, rfl⟩
  | .succ u, h => by
    obtain ⟨t, ht⟩ := ofLevel_of_paramsIn (level := u) h
    exact ⟨.succ t, by simp [VLevel.ofLevel, ht]⟩
  | .max u v, h => by
    simp only [Level.paramsIn, Bool.and_eq_true] at h
    obtain ⟨t, ht⟩ := ofLevel_of_paramsIn h.1
    obtain ⟨t', ht'⟩ := ofLevel_of_paramsIn h.2
    exact ⟨.max t t', by simp [VLevel.ofLevel, ht, ht']⟩
  | .imax u v, h => by
    simp only [Level.paramsIn, Bool.and_eq_true] at h
    obtain ⟨t, ht⟩ := ofLevel_of_paramsIn h.1
    obtain ⟨t', ht'⟩ := ofLevel_of_paramsIn h.2
    exact ⟨.imax t t', by simp [VLevel.ofLevel, ht, ht']⟩
  | .param n, h => by
    simp only [Level.paramsIn, List.contains_iff_mem] at h
    exact ⟨.param (Us.idxOf n), by simp [VLevel.ofLevel, List.idxOf_lt_length_iff.2 h]⟩
  | .mvar _, h => by simp [Level.paramsIn] at h

theorem List.mapM_ofLevel_of_paramsIn {Us : List Name} :
    ∀ {us : List Level}, us.all (Level.paramsIn Us) = true →
      ∃ us', us.mapM (VLevel.ofLevel Us) = some us'
  | [], _ => ⟨[], rfl⟩
  | u :: us, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨t, ht⟩ := VLevel.ofLevel_of_paramsIn h.1
    obtain ⟨ts, hts⟩ := mapM_ofLevel_of_paramsIn h.2
    exact ⟨t :: ts, by simp [List.mapM_cons, ht, hts]⟩

/-- Totality: an expression has a syntactic translation as soon as it is scoped by the
context. -/
theorem TrSyn.exists_of_scoped {Us : List Name} :
    ∀ {Δ : VLCtx} {e : Expr}, Closed e Δ.bvars → FVarsIn (· ∈ Δ.fvars) e →
      e.levelParamsIn Us = true → ∃ e', TrSyn Us Δ e e'
  | Δ, .bvar i, hc, _, _ => by
    obtain ⟨⟨_, _⟩, h⟩ := VLCtx.find?_inl_iff.2 hc; exact ⟨_, .bvar h⟩
  | Δ, .fvar fv, _, hf, _ => by
    obtain ⟨⟨_, _⟩, h⟩ := VLCtx.find?_eq_some.2 hf; exact ⟨_, .fvar h⟩
  | Δ, .sort u, _, _, hl => by
    obtain ⟨_, h⟩ := VLevel.ofLevel_of_paramsIn hl; exact ⟨_, .sort h⟩
  | Δ, .const c us, _, _, hl => by
    obtain ⟨_, h⟩ := List.mapM_ofLevel_of_paramsIn hl; exact ⟨_, .const h⟩
  | Δ, .app f a, hc, hf, hl => by
    simp only [Expr.levelParamsIn, Bool.and_eq_true] at hl
    obtain ⟨_, h1⟩ := exists_of_scoped hc.1 hf.1 hl.1
    obtain ⟨_, h2⟩ := exists_of_scoped hc.2 hf.2 hl.2
    exact ⟨_, .app h1 h2⟩
  | Δ, .lam _ ty body _, hc, hf, hl => by
    simp only [Expr.levelParamsIn, Bool.and_eq_true] at hl
    obtain ⟨ty', h1⟩ := exists_of_scoped hc.1 hf.1 hl.1
    obtain ⟨_, h2⟩ := exists_of_scoped (Δ := (none, .vlam ty') :: Δ) hc.2 hf.2 hl.2
    exact ⟨_, .lam h1 h2⟩
  | Δ, .forallE _ ty body _, hc, hf, hl => by
    simp only [Expr.levelParamsIn, Bool.and_eq_true] at hl
    obtain ⟨ty', h1⟩ := exists_of_scoped hc.1 hf.1 hl.1
    obtain ⟨_, h2⟩ := exists_of_scoped (Δ := (none, .vlam ty') :: Δ) hc.2 hf.2 hl.2
    exact ⟨_, .forallE h1 h2⟩
  | Δ, .letE _ ty val body _, hc, hf, hl => by
    simp only [Expr.levelParamsIn, Bool.and_eq_true] at hl
    obtain ⟨ty', h1⟩ := exists_of_scoped hc.1 hf.1 hl.1.1
    obtain ⟨val', h2⟩ := exists_of_scoped hc.2.1 hf.2.1 hl.1.2
    obtain ⟨_, h3⟩ := exists_of_scoped (Δ := (none, .vlet ty' val') :: Δ) hc.2.2 hf.2.2 hl.2
    exact ⟨_, .letE h1 h2 h3⟩
  | Δ, .lit l, _, _, _ => ⟨_, .trLiteral l⟩
  | Δ, .mdata _ e, hc, hf, hl => by
    obtain ⟨_, h⟩ := exists_of_scoped (e := e) hc hf hl; exact ⟨_, .mdata h⟩
  | Δ, .proj _ _ e, hc, hf, hl => by
    obtain ⟨_, h⟩ := exists_of_scoped (e := e) hc hf hl; exact ⟨_, .proj h⟩
  | Δ, .mvar _, hc, _, _ => hc.elim

/-- The syntactic translation is defined exactly on the expressions scoped by the context. -/
theorem TrSyn.exists_iff {Us : List Name} {Δ : VLCtx} {e : Expr} :
    (∃ e', TrSyn Us Δ e e') ↔
      Closed e Δ.bvars ∧ FVarsIn (· ∈ Δ.fvars) e ∧ e.levelParamsIn Us = true :=
  ⟨fun ⟨_, H⟩ => ⟨H.closed, H.fvarsIn, H.levelParamsIn⟩,
   fun ⟨h1, h2, h3⟩ => exists_of_scoped h1 h2 h3⟩

end Lean4Lean
