import Lean4Lean.Verify.Typing.Syntactic.Transport

/-!
# Typed translation as syntactic translation plus typing

`TrExprS` carries a typing premise at `app`, `lam`, `forallE`, `letE`, `lit`, `proj` and
`const`. Over an ordered environment and a well-formed context, all of them except two are
consequences of the typing of the *result* of the translation, by inversion
(`HasType.app_inv`, `HasType.lam_inv`, `HasType.forallE_inv`, `HasType.proj_inv`,
`HasType.const_inv`). The two exceptions are about source syntax that the translation erases:

* a let-bound value is inlined, so the typing of the value at the declared type
  (`TrExprS.letE`) is not visible in the result when the variable is unused;
* a literal is translated to its constructor encoding, and the presence of the literal's
  primitive types (`TrExprS.lit`, `VEnv.ContainsLits`) is not visible in the result: the
  encoding of `""` mentions neither `Char.ofNat` nor `Nat`.

`TrResidual` collects exactly these two obligations, and

  `TrExprS env Us Δ e e' ↔ TrSyn Us Δ e e' ∧ VExpr.WF env Us.length Δ.toCtx e' ∧ TrResidual env Us Δ e`

(`TrExprS.iff_typed`). `TrTyped` is the right-hand side. The residual is trivial on let-free
syntax without literals (`TrResidual.of_simple`).
-/

namespace Lean4Lean
open Lean4Lean VEnv Lean

variable (env : VEnv) (Us : List Name) in
/-- The typing obligations of `TrExprS` that the typing of the translated term does not
witness: let-bound values are typed at their declared types, and literals have their primitive
types present. Binders record the syntactic translation of their domain, to know the context of
the body. -/
inductive TrResidual : VLCtx → Expr → Prop
  | bvar : TrResidual Δ (.bvar i)
  | fvar : TrResidual Δ (.fvar fv)
  | sort : TrResidual Δ (.sort u)
  | const : TrResidual Δ (.const c us)
  | app : TrResidual Δ f → TrResidual Δ a → TrResidual Δ (.app f a)
  | lam : TrSyn Us Δ ty ty' → TrResidual Δ ty → TrResidual ((none, .vlam ty') :: Δ) body →
    TrResidual Δ (.lam name ty body bi)
  | forallE : TrSyn Us Δ ty ty' → TrResidual Δ ty → TrResidual ((none, .vlam ty') :: Δ) body →
    TrResidual Δ (.forallE name ty body bi)
  | letE : TrSyn Us Δ ty ty' → TrSyn Us Δ val val' →
    env.HasType Us.length Δ.toCtx val' ty' →
    TrResidual Δ ty → TrResidual Δ val → TrResidual ((none, .vlet ty' val') :: Δ) body →
    TrResidual Δ (.letE name ty val body nd)
  | lit : env.ContainsLits l → TrResidual Δ l.toConstructor → TrResidual Δ (.lit l)
  | mdata : TrResidual Δ e → TrResidual Δ (.mdata d e)
  | proj : TrResidual Δ e → TrResidual Δ (.proj s i e)

/-- Typed translation: a syntactic translation whose result is well typed, with the residual
obligations on erased syntax. Equivalent to `TrExprS` (`TrExprS.iff_typed`). -/
def TrTyped (env : VEnv) (Us : List Name) (Δ : VLCtx) (e : Expr) (e' : VExpr) : Prop :=
  TrSyn Us Δ e e' ∧ VExpr.WF env Us.length Δ.toCtx e' ∧ TrResidual env Us Δ e

/-! ### From `TrExprS` -/

variable! (henv : Ordered env) {Us : List Name} (hΔ : VLCtx.WF env Us.length Δ) in
theorem TrExprS.wf (H : TrExprS env Us Δ e e') : VExpr.WF env Us.length Δ.toCtx e' := by
  induction H with
  | bvar h1 | fvar h1 => exact ⟨_, hΔ.find?_wf henv h1⟩
  | sort h1 => exact ⟨_, HasType.sort (.of_ofLevel h1)⟩
  | const h1 h2 h3 => exact ⟨_,
    HasType.const h1 (.of_mapM_ofLevel h2) ((List.mapM_eq_some.1 h2).length_eq.symm.trans h3)⟩
  | app h1 h2 => exact ⟨_, h1.app h2⟩
  | lam h1 _ _ _ ih2 =>
    have ⟨_, h1'⟩ := h1
    have ⟨_, h2'⟩ := ih2 ⟨hΔ, nofun, h1⟩
    refine ⟨_, h1'.lam h2'⟩
  | forallE h1 h2 => have ⟨_, h1'⟩ := h1; have ⟨_, h2'⟩ := h2; exact ⟨_, h1'.forallE h2'⟩
  | letE h1 _ _ _ _ _ ih3 => exact ih3 ⟨hΔ, nofun, h1⟩
  | lit _ _ ih | mdata _ ih => exact ih hΔ
  | proj _ h2 => exact h2

theorem TrExprS.residual (H : TrExprS env Us Δ e e') : TrResidual env Us Δ e := by
  induction H with
  | bvar | fvar | sort | const => constructor
  | app _ _ _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ h1 _ _ ih2 => exact .lam h1.toTrSyn (by assumption) ih2
  | forallE _ _ h1 _ _ ih2 => exact .forallE h1.toTrSyn (by assumption) ih2
  | letE h0 h1 h2 _ ih1 ih2 ih3 => exact .letE h1.toTrSyn h2.toTrSyn h0 ih1 ih2 ih3
  | lit h _ ih => exact .lit h ih
  | mdata _ ih => exact .mdata ih
  | proj _ _ ih => exact .proj ih

/-! ### To `TrExprS` -/

/-- A syntactic translation with a well-typed result and the residual obligations is a typed
translation. The typing premises of `TrExprS` at applications, binders, projections and
constants are recovered by inversion from the typing of the result. -/
theorem TrSyn.toTrExprS (henv : env.Ordered) (H : TrSyn Us Δ e e')
    (hΔ : Δ.WF env Us.length) (hwf : VExpr.WF env Us.length Δ.toCtx e')
    (hr : TrResidual env Us Δ e) : TrExprS env Us Δ e e' := by
  induction H with
  | bvar h => exact .bvar h
  | fvar h => exact .fvar h
  | sort h => exact .sort h
  | const h =>
    obtain ⟨ci, hci, -, hlen⟩ := hwf.const_inv henv hΔ.toCtx
    exact .const hci h ((List.mapM_eq_some.1 h).length_eq.trans hlen)
  | app _ _ ih1 ih2 =>
    let .app r1 r2 := hr
    obtain ⟨A, B, h1, h2⟩ := hwf.app_inv henv hΔ.toCtx
    exact .app h1 h2 (ih1 hΔ ⟨_, h1⟩ r1) (ih2 hΔ ⟨_, h2⟩ r2)
  | lam s1 _ ih1 ih2 =>
    let .lam s1' r1 r2 := hr
    cases s1.unique s1'
    obtain ⟨hty, hbody⟩ := hwf.lam_inv henv hΔ.toCtx
    have ⟨_, hty'⟩ := hty
    exact .lam hty (ih1 hΔ ⟨_, hty'⟩ r1) (ih2 ⟨hΔ, nofun, hty⟩ hbody r2)
  | forallE s1 _ ih1 ih2 =>
    let .forallE s1' r1 r2 := hr
    cases s1.unique s1'
    obtain ⟨_, hT⟩ := hwf
    obtain ⟨hty, hbody⟩ := HasType.forallE_inv henv hT
    have ⟨_, hty'⟩ := hty
    have ⟨_, hbody'⟩ := hbody
    exact .forallE hty hbody (ih1 hΔ ⟨_, hty'⟩ r1) (ih2 ⟨hΔ, nofun, hty⟩ ⟨_, hbody'⟩ r2)
  | letE s1 s2 _ ih1 ih2 ih3 =>
    let .letE s1' s2' hv r1 r2 r3 := hr
    cases s1.unique s1'; cases s2.unique s2'
    obtain ⟨_, hty⟩ := IsDefEq.isType henv hΔ.toCtx hv
    exact .letE hv (ih1 hΔ ⟨_, hty⟩ r1) (ih2 hΔ ⟨_, hv⟩ r2) (ih3 ⟨hΔ, nofun, hv⟩ hwf r3)
  | lit _ ih =>
    let .lit hl r := hr
    exact .lit hl (ih hΔ hwf r)
  | mdata _ ih =>
    let .mdata r := hr
    exact .mdata (ih hΔ hwf r)
  | proj _ ih =>
    let .proj r := hr
    obtain ⟨_, hT⟩ := hwf
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ :=
      HasType.proj_inv henv hΔ.toCtx hT
    exact .proj (ih hΔ ⟨_, hmajor.hasType.2⟩ r) ⟨_, hT⟩

/-- **The decomposition of typed translation.** Over an ordered environment and a well-formed
context, a typed translation is exactly a syntactic translation whose result is well typed and
whose erased syntax meets the residual obligations. -/
theorem TrExprS.iff_typed (henv : env.Ordered) (hΔ : Δ.WF env Us.length) :
    TrExprS env Us Δ e e' ↔ TrTyped env Us Δ e e' :=
  ⟨fun H => ⟨H.toTrSyn, H.wf henv hΔ, H.residual⟩,
   fun ⟨H, hwf, hr⟩ => H.toTrExprS henv hΔ hwf hr⟩

/-! ### The residual on simple syntax -/

/-- Let-free syntax without literals and metavariables: the residual obligations are vacuous
on it. -/
def _root_.Lean.Expr.letLitFree : Expr → Bool
  | .bvar _ | .fvar _ | .sort _ | .const .. => true
  | .lit _ | .letE .. | .mvar _ => false
  | .app f a | .lam _ f a _ | .forallE _ f a _ => letLitFree f && letLitFree a
  | .mdata _ e | .proj _ _ e => letLitFree e

theorem TrResidual.of_simple : ∀ {Δ : VLCtx} {e : Expr} {e' : VExpr},
    Expr.letLitFree e = true → TrSyn Us Δ e e' → TrResidual env Us Δ e
  | _, .bvar _, _, _, _ => .bvar
  | _, .fvar _, _, _, _ => .fvar
  | _, .sort _, _, _, _ => .sort
  | _, .const .., _, _, _ => .const
  | _, .app .., _, h, .app s1 s2 => by
    simp only [Expr.letLitFree, Bool.and_eq_true] at h
    exact .app (of_simple h.1 s1) (of_simple h.2 s2)
  | _, .lam .., _, h, .lam s1 s2 => by
    simp only [Expr.letLitFree, Bool.and_eq_true] at h
    exact .lam s1 (of_simple h.1 s1) (of_simple h.2 s2)
  | _, .forallE .., _, h, .forallE s1 s2 => by
    simp only [Expr.letLitFree, Bool.and_eq_true] at h
    exact .forallE s1 (of_simple h.1 s1) (of_simple h.2 s2)
  | _, .mdata .., _, h, .mdata s => .mdata (of_simple h s)
  | _, .proj .., _, h, .proj s => .proj (of_simple h s)

/-- On let-free syntax without literals, a typed translation is a syntactic translation with a
well-typed result. -/
theorem TrExprS.iff_syn_wf (henv : env.Ordered) (hΔ : Δ.WF env Us.length)
    (hs : Expr.letLitFree e = true) :
    TrExprS env Us Δ e e' ↔ TrSyn Us Δ e e' ∧ VExpr.WF env Us.length Δ.toCtx e' :=
  ⟨fun H => ⟨H.toTrSyn, H.wf henv hΔ⟩,
   fun ⟨H, hwf⟩ => H.toTrExprS henv hΔ hwf (.of_simple hs H)⟩

/-! ### Transport of the typed layer

A typed lemma is the syntactic lemma, the typing lemma for the result, and the transport of the
residual, which only moves the typing of let-bound values. Bound-variable weakening as the
example: compare `TrExprS.weakBV`, which re-proves the syntax in every case. -/

theorem TrResidual.weakBV (henv : env.Ordered) (W : VLCtx.BVLift Δ Δ' dn dk n k)
    (H : TrResidual env Us Δ e) : TrResidual env Us Δ' (e.liftLooseBVars' dk dn) := by
  induction H generalizing Δ' dk k with
  | bvar | fvar | sort | const => constructor
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam s _ _ ih1 ih2 => exact .lam (s.weakBV W) (ih1 W) (ih2 (W.cons _))
  | forallE s _ _ ih1 ih2 => exact .forallE (s.weakBV W) (ih1 W) (ih2 (W.cons _))
  | letE s1 s2 hv _ _ _ ih1 ih2 ih3 =>
    exact .letE (s1.weakBV W) (s2.weakBV W) (hv.weakN henv W.toCtx) (ih1 W) (ih2 W)
      (ih3 (W.cons _))
  | lit hl _ ih =>
    refine .lit hl (Expr.liftLooseBVars_eq_self ?_ ▸ ih W :)
    exact Closed.toConstructor.looseBVarRange_le
  | mdata _ ih => exact .mdata (ih W)
  | proj _ ih => exact .proj (ih W)

theorem TrTyped.weakBV (henv : env.Ordered) (W : VLCtx.BVLift Δ Δ' dn dk n k)
    (H : TrTyped env Us Δ e e') :
    TrTyped env Us Δ' (e.liftLooseBVars' dk dn) (e'.liftN n k) :=
  let ⟨s, ⟨_, h⟩, r⟩ := H
  ⟨s.weakBV W, ⟨_, h.weakN henv W.toCtx⟩, r.weakBV henv W⟩

theorem TrResidual.weakFV' (henv : env.Ordered) (W : VLCtx.FVLift' Δ Δ' dk n k)
    (hnd : Δ'.fvars.Nodup) (H : TrResidual env Us Δ e) : TrResidual env Us Δ' e := by
  induction H generalizing Δ' dk k with
  | bvar | fvar | sort | const => constructor
  | app _ _ ih1 ih2 => exact .app (ih1 W hnd) (ih2 W hnd)
  | lam s _ _ ih1 ih2 => exact .lam (s.weakFV' W hnd) (ih1 W hnd) (ih2 (W.cons_bvar _) hnd)
  | forallE s _ _ ih1 ih2 =>
    exact .forallE (s.weakFV' W hnd) (ih1 W hnd) (ih2 (W.cons_bvar _) hnd)
  | letE s1 s2 hv _ _ _ ih1 ih2 ih3 =>
    exact .letE (s1.weakFV' W hnd) (s2.weakFV' W hnd) (hv.weak' henv W.toCtx) (ih1 W hnd)
      (ih2 W hnd) (ih3 (W.cons_bvar _) hnd)
  | lit hl _ ih => exact .lit hl (ih W hnd)
  | mdata _ ih => exact .mdata (ih W hnd)
  | proj _ ih => exact .proj (ih W hnd)

theorem TrResidual.weakFV (henv : env.Ordered) (W : VLCtx.FVLift Δ Δ' dk n k)
    (hnd : Δ'.fvars.Nodup) (H : TrResidual env Us Δ e) : TrResidual env Us Δ' e :=
  H.weakFV' henv W.toFVLift' hnd

theorem TrResidual.instN_bvar (henv : env.Ordered) (r₀ : TrResidual env Us Δ₀ e₀)
    (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) (i : Nat) :
    TrResidual env Us Δ (Expr.instantiate1' (.bvar i) e₀ dk) := by
  simp only [Expr.instantiate1']
  split; · exact .bvar
  split; · exact r₀.weakBV henv W.toBVLift
  exact .bvar

theorem TrResidual.instN {Δ₀ : VLCtx} (h₀ : TrSyn Us Δ₀ e₀ e₀')
    (r₀ : TrResidual env Us Δ₀ e₀) (henv : env.Ordered)
    (t₀ : env.HasType Us.length Δ₀.toCtx e₀' A₀)
    (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) (H : TrResidual env Us Δ₁ e) :
    TrResidual env Us Δ (Expr.instantiate1' e e₀ dk) := by
  induction H generalizing Δ dk k with
  | bvar => exact .instN_bvar henv r₀ W _
  | fvar | sort | const => constructor
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam s _ _ ih1 ih2 =>
    exact .lam (h₀.instN W s) (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | forallE s _ _ ih1 ih2 =>
    exact .forallE (h₀.instN W s) (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | letE s1 s2 hv _ _ _ ih1 ih2 ih3 =>
    exact .letE (h₀.instN W s1) (h₀.instN W s2) (hv.instN henv W.toCtx t₀) (ih1 W) (ih2 W)
      (ih3 (W.succ (d := .vlet ..)))
  | lit hl _ ih =>
    refine .lit hl (Expr.instantiate1'_eq_self ?_ ▸ ih W :)
    exact Closed.toConstructor.looseBVarRange_le
  | mdata _ ih => exact .mdata (ih W)
  | proj _ ih => exact .proj (ih W)

theorem TrResidual.instN_let_bvar (henv : env.Ordered) (r₀ : TrResidual env Us Δ₀ e₀)
    (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ) (i : Nat) :
    TrResidual env Us Δ (Expr.instantiate1' (.bvar i) e₀ dk) := by
  simp only [Expr.instantiate1']
  split; · exact .bvar
  split; · exact r₀.weakBV henv W.toBVLift
  exact .bvar

theorem TrResidual.instN_let {Δ₀ : VLCtx} (h₀ : TrSyn Us Δ₀ e₀ e₀')
    (r₀ : TrResidual env Us Δ₀ e₀) (henv : env.Ordered) (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ)
    (H : TrResidual env Us Δ₁ e) : TrResidual env Us Δ (Expr.instantiate1' e e₀ dk) := by
  induction H generalizing Δ dk k with
  | bvar => exact .instN_let_bvar henv r₀ W _
  | fvar | sort | const => constructor
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam s _ _ ih1 ih2 =>
    exact .lam (h₀.instN_let W s) (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | forallE s _ _ ih1 ih2 =>
    exact .forallE (h₀.instN_let W s) (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | letE s1 s2 hv _ _ _ ih1 ih2 ih3 =>
    exact .letE (h₀.instN_let W s1) (h₀.instN_let W s2) (W.toCtx ▸ hv) (ih1 W) (ih2 W)
      (ih3 (W.succ (d := .vlet ..)))
  | lit hl _ ih =>
    refine .lit hl (Expr.instantiate1'_eq_self ?_ ▸ ih W :)
    exact Closed.toConstructor.looseBVarRange_le
  | mdata _ ih => exact .mdata (ih W)
  | proj _ ih => exact .proj (ih W)

theorem TrResidual.abstract (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ)
    (H : TrResidual env Us Δ₁ e) : TrResidual env Us Δ (e.abstract1 v₀ dk) := by
  induction H generalizing dk k Δ with
  | bvar | sort | const => constructor
  | fvar => unfold Expr.abstract1; split <;> constructor
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam s _ _ ih1 ih2 => exact .lam (s.abstract W) (ih1 W) (ih2 W.succ)
  | forallE s _ _ ih1 ih2 => exact .forallE (s.abstract W) (ih1 W) (ih2 W.succ)
  | letE s1 s2 hv _ _ _ ih1 ih2 ih3 =>
    exact .letE (s1.abstract W) (s2.abstract W) (W.toCtx ▸ hv) (ih1 W) (ih2 W) (ih3 W.succ)
  | lit hl _ ih =>
    exact .lit hl (FVarsIn.toConstructor.abstract_eq_self .toConstructor ▸ ih W)
  | mdata _ ih => exact .mdata (ih W)
  | proj _ ih => exact .proj (ih W)

theorem TrResidual.uninstantiateN (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ)
    (H : TrResidual env Us Δ₁ (Expr.instantiate1' e (.fvar v₀) dk))
    (sc : FVarsIn (· ≠ v₀) e) : TrResidual env Us Δ e := by
  have := H.abstract W
  rwa [sc.abstract_instantiate1] at this

theorem TrResidual.inst_fvar (henv : env.Ordered)
    (hnd : (VLCtx.fvars ((some (a, deps), d) :: Δ)).Nodup)
    (H : TrResidual env Us ((none, d) :: Δ) e) :
    TrResidual env Us ((some (a, deps), d) :: Δ) (e.instantiate1' (.fvar a)) := by
  have W := VLCtx.FVLift.skip_fvar (a, deps) d (Δ := Δ) .refl
  have := H.weakFV henv (.cons_bvar _ W) hnd
  have hf : TrSyn Us ((some (a, deps), d) :: Δ) (.fvar a) d.value := .fvar (A := d.type) <| by
    simp [VLCtx.find?, VLCtx.next]
  match d with
  | .vlam A₀ => exact TrResidual.instN hf .fvar henv (.bvar .zero) .zero this
  | .vlet A₀ e₀ =>
    simp [VLocalDecl.depth, VLocalDecl.liftN] at this
    exact TrResidual.instN_let hf .fvar henv .zero this

theorem TrResidual.prependLevelParam (hfresh : fresh ∉ Us) (H : TrResidual env Us Δ e) :
    TrResidual env (fresh :: Us) (Δ.instL (VLevel.prependShift Us.length)) e := by
  have hshift : ∀ level ∈ VLevel.prependShift Us.length, level.WF (fresh :: Us).length := by
    simpa using VLevel.prependShift_wf (n := Us.length)
  induction H with
  | bvar | fvar | sort | const => constructor
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam s _ _ ih1 ih2 => exact .lam (s.prependLevelParam hfresh) ih1 ih2
  | forallE s _ _ ih1 ih2 => exact .forallE (s.prependLevelParam hfresh) ih1 ih2
  | letE s1 s2 hv _ _ _ ih1 ih2 ih3 =>
    exact .letE (s1.prependLevelParam hfresh) (s2.prependLevelParam hfresh)
      (VLCtx.instL_toCtx _ ▸ hv.instL hshift) ih1 ih2 ih3
  | lit hl _ ih => exact .lit hl ih
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

variable! {env env' : VEnv} (henv : env ≤ env') in
nonrec theorem VEnv.ContainsLits.mono : ∀ {l}, env.ContainsLits l → env'.ContainsLits l
  | .natVal _, ⟨_, H⟩ => ⟨_, henv.1 H⟩
  | .strVal _, ⟨⟨_, H1⟩, ⟨_, H2⟩⟩ => ⟨⟨_, henv.1 H1⟩, ⟨_, henv.1 H2⟩⟩

theorem TrResidual.mono {env env' : VEnv} (henv : env ≤ env') (H : TrResidual env Us Δ e) :
    TrResidual env' Us Δ e := by
  induction H with
  | bvar | fvar | sort | const => constructor
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam s _ _ ih1 ih2 => exact .lam s ih1 ih2
  | forallE s _ _ ih1 ih2 => exact .forallE s ih1 ih2
  | letE s1 s2 hv _ _ _ ih1 ih2 ih3 => exact .letE s1 s2 (hv.mono henv) ih1 ih2 ih3
  | lit hl _ ih => exact .lit (hl.mono henv) ih
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

/-! ### Transport of `TrTyped`

Each is the `TrSyn` lemma, the typing lemma for the result, and the residual lemma. None needs a
well-formed context. -/

theorem TrTyped.weakFV' (henv : env.Ordered) (W : VLCtx.FVLift' Δ Δ' dk n k)
    (hnd : Δ'.fvars.Nodup) (H : TrTyped env Us Δ e e') :
    TrTyped env Us Δ' e (e'.lift' (n.consN k)) :=
  let ⟨s, ⟨_, h⟩, r⟩ := H
  ⟨s.weakFV' W hnd, ⟨_, HasType.weak' henv W.toCtx h⟩, r.weakFV' henv W hnd⟩

theorem TrTyped.weakFV (henv : env.Ordered) (W : VLCtx.FVLift Δ Δ' dk n k)
    (hnd : Δ'.fvars.Nodup) (H : TrTyped env Us Δ e e') :
    TrTyped env Us Δ' e (e'.liftN n k) :=
  let ⟨s, ⟨_, h⟩, r⟩ := H
  ⟨s.weakFV W hnd, ⟨_, HasType.weakN henv W.toCtx h⟩, r.weakFV henv W hnd⟩

theorem TrTyped.instN {Δ₀ : VLCtx} (henv : env.Ordered) (h₀ : TrTyped env Us Δ₀ e₀ e₀')
    (t₀ : env.HasType Us.length Δ₀.toCtx e₀' A₀)
    (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) (H : TrTyped env Us Δ₁ e e') :
    TrTyped env Us Δ (Expr.instantiate1' e e₀ dk) (e'.inst e₀' k) :=
  let ⟨s₀, _, r₀⟩ := h₀
  let ⟨s, ⟨_, h⟩, r⟩ := H
  ⟨s₀.instN W s, ⟨_, HasType.instN henv W.toCtx h t₀⟩, TrResidual.instN s₀ r₀ henv t₀ W r⟩

theorem TrTyped.inst {Δ : VLCtx} (henv : env.Ordered) (t₀ : env.HasType Us.length Δ.toCtx e₀' A₀)
    (H : TrTyped env Us ((none, .vlam A₀) :: Δ) e e') (h₀ : TrTyped env Us Δ e₀ e₀') :
    TrTyped env Us Δ (e.instantiate1' e₀) (e'.inst e₀') :=
  h₀.instN henv t₀ .zero H

theorem TrTyped.instN_let {Δ₀ : VLCtx} (henv : env.Ordered) (h₀ : TrTyped env Us Δ₀ e₀ e₀')
    (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ) (H : TrTyped env Us Δ₁ e e') :
    TrTyped env Us Δ (Expr.instantiate1' e e₀ dk) e' :=
  let ⟨s₀, _, r₀⟩ := h₀
  let ⟨s, h, r⟩ := H
  ⟨s₀.instN_let W s, W.toCtx ▸ h, TrResidual.instN_let s₀ r₀ henv W r⟩

theorem TrTyped.inst_let {Δ : VLCtx} (henv : env.Ordered)
    (H : TrTyped env Us ((none, .vlet A₀ e₀') :: Δ) e e') (h₀ : TrTyped env Us Δ e₀ e₀') :
    TrTyped env Us Δ (e.instantiate1' e₀) e' :=
  h₀.instN_let henv .zero H

theorem TrTyped.abstract (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ)
    (H : TrTyped env Us Δ₁ e e') : TrTyped env Us Δ (e.abstract1 v₀ dk) e' :=
  let ⟨s, h, r⟩ := H
  ⟨s.abstract W, W.toCtx ▸ h, r.abstract W⟩

theorem TrTyped.uninstantiateN (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ)
    (H : TrTyped env Us Δ₁ (Expr.instantiate1' e (.fvar v₀) dk) e')
    (sc : FVarsIn (· ≠ v₀) e) : TrTyped env Us Δ e e' := by
  have := H.abstract W
  rwa [sc.abstract_instantiate1] at this

theorem TrTyped.uninstantiate
    (H : TrTyped env Us ((some (v, deps), d) :: Δ) (e.instantiate1' (.fvar v)) e')
    (sc : FVarsIn (· ≠ v) e) : TrTyped env Us ((none, d) :: Δ) e e' :=
  H.uninstantiateN .zero sc

theorem TrTyped.inst_fvar (henv : env.Ordered)
    (hnd : (VLCtx.fvars ((some (a, deps), d) :: Δ)).Nodup)
    (H : TrTyped env Us ((none, d) :: Δ) e e') :
    TrTyped env Us ((some (a, deps), d) :: Δ) (e.instantiate1' (.fvar a)) e' :=
  let ⟨s, h, r⟩ := H
  ⟨s.inst_fvar hnd, by cases d <;> exact h, r.inst_fvar henv hnd⟩

theorem TrTyped.prependLevelParam (hfresh : fresh ∉ Us) (H : TrTyped env Us Δ e e') :
    TrTyped env (fresh :: Us) (Δ.instL (VLevel.prependShift Us.length)) e
      (e'.instL (VLevel.prependShift Us.length)) :=
  have hshift : ∀ level ∈ VLevel.prependShift Us.length, level.WF (fresh :: Us).length := by
    simpa using VLevel.prependShift_wf (n := Us.length)
  let ⟨s, ⟨_, h⟩, r⟩ := H
  ⟨s.prependLevelParam hfresh, ⟨_, VLCtx.instL_toCtx _ ▸ HasType.instL hshift h⟩,
    r.prependLevelParam hfresh⟩

theorem TrTyped.mono {env env' : VEnv} (henv : env ≤ env') (H : TrTyped env Us Δ e e') :
    TrTyped env' Us Δ e e' :=
  let ⟨s, h, r⟩ := H
  ⟨s, h.mono henv, r.mono henv⟩

end Lean4Lean
