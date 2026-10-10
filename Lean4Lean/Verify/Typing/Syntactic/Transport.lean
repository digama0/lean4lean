import Lean4Lean.Verify.Typing.Syntactic.Basic

/-!
# Syntactic transport of the translation

Each lemma here is the typing-free core of a `TrExprS` lemma of `Verify/Typing/Lemmas.lean`,
or `Verify/Typing/LevelEquiv.lean`, stated for `TrSyn` and proved
without `HasType`, without an environment and without a well-formed context:

* weakening by free variables (`TrSyn.weakFV'`, `TrSyn.weakFV`; the context only needs distinct
  free variables) and by bound variables (`TrSyn.weakBV`);
* substitution of a term for a binder (`TrSyn.instN`, `TrSyn.inst`) and of a let value
  (`TrSyn.instN_let`, `TrSyn.inst_let`), and of a free variable for a binder (`TrSyn.inst_fvar`);
* abstraction of a free variable (`TrSyn.abstract`, `TrSyn.uninstantiate`);
* level instantiation, up to level equivalence (`TrSyn.instL_lequiv`), and prepending a fresh
  level parameter (`TrSyn.prependLevelParam`);
* equality up to binder names (`TrSyn.eqv`) and translation in a context differing in its binder
  domains (`TrSyn.transport`);
* restriction: deleting binders the source does not use (`TrSyn.lowerBV`) and free variables
  the source does not mention (`TrSyn.restrictFV`).

The last item is the syntactic half of strengthening. It is elementary here, and the typed half
is isolated in `Syntactic/Typed.lean`: restricting the *syntax* of a translation is free,
restricting its *typing* is not (section 5.1 of the design notes).
-/

namespace Lean4Lean
open Lean

/-! ### Weakening -/

theorem TrSyn.weakFV' {Us : List Name} (W : VLCtx.FVLift' Δ Δ' dk n k) (hnd : Δ'.fvars.Nodup)
    (H : TrSyn Us Δ e e') : TrSyn Us Δ' e (e'.lift' (n.consN k)) := by
  induction H generalizing Δ' dk k with
  | bvar h1 => exact .bvar (W.find? hnd h1)
  | fvar h1 => exact .fvar (W.find? hnd h1)
  | sort h1 => exact .sort h1
  | const h1 => exact .const h1
  | app _ _ ih1 ih2 => exact .app (ih1 W hnd) (ih2 W hnd)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W hnd) (ih2 (W.cons_bvar _) hnd)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W hnd) (ih2 (W.cons_bvar _) hnd)
  | letE _ _ _ ih1 ih2 ih3 => exact .letE (ih1 W hnd) (ih2 W hnd) (ih3 (W.cons_bvar _) hnd)
  | lit _ ih => exact .lit (ih W hnd)
  | mdata _ ih => exact .mdata (ih W hnd)
  | proj _ ih => exact .proj (ih W hnd)

theorem TrSyn.weakFV {Us : List Name} (W : VLCtx.FVLift Δ Δ' dk n k) (hnd : Δ'.fvars.Nodup)
    (H : TrSyn Us Δ e e') : TrSyn Us Δ' e (e'.liftN n k) := by
  simpa [VExpr.lift'_consN_skipN] using H.weakFV' W.toFVLift' hnd

theorem TrSyn.weakBV {Us : List Name} (W : VLCtx.BVLift Δ Δ' dn dk n k)
    (H : TrSyn Us Δ e e') : TrSyn Us Δ' (e.liftLooseBVars' dk dn) (e'.liftN n k) := by
  induction H generalizing Δ' dk k with
  | bvar h1 => exact .bvar (W.find? h1)
  | fvar h1 => exact .fvar (W.find? h1)
  | sort h1 => exact .sort h1
  | const h1 => exact .const h1
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 (W.cons _))
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 (W.cons _))
  | letE _ _ _ ih1 ih2 ih3 => exact .letE (ih1 W) (ih2 W) (ih3 (W.cons _))
  | lit _ ih =>
    refine .lit (Expr.liftLooseBVars_eq_self ?_ ▸ ih W :)
    exact Closed.toConstructor.looseBVarRange_le
  | mdata _ ih => exact .mdata (ih W)
  | proj _ ih => exact .proj (ih W)

/-! ### Substitution -/

section
variable {Us : List Name} {Δ₀ : VLCtx} {e₀ : Expr} {e₀' : VExpr} (h₀ : TrSyn Us Δ₀ e₀ e₀')
include h₀

theorem TrSyn.instN_var (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) (H : Δ₁.find? v = some (e', A)) :
    TrSyn Us Δ (Expr.instantiate1' (VLCtx.varToExpr v) e₀ dk) (e'.inst e₀' k) := by
  induction W generalizing v e' A with
  | zero =>
    obtain (_|i)|fv := v <;> simp [VLCtx.varToExpr, Expr.instantiate1', Expr.liftLooseBVars_zero]
    · cases H; simp [VLocalDecl.value, VExpr.inst]; exact h₀
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      simp [VLocalDecl.depth, VExpr.inst_liftN]
      exact .bvar H
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      simp [VLocalDecl.depth, VExpr.inst_liftN]
      exact .fvar H
  | @succ _ k _ _ d _ ih =>
    obtain (_|i)|fv := v <;> simp [VLCtx.varToExpr, Expr.instantiate1']
    · cases H
      cases d <;> exact .bvar <| by simp [VLocalDecl.value, VExpr.inst, VLocalDecl.depth]; rfl
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      have := ih H; revert this
      simp [VLCtx.varToExpr, Expr.instantiate1']; split <;> [skip; split]
      · intro | .bvar h => ?_
        exact .bvar <| by
          simp [VLCtx.find?, VLCtx.next]
          refine ⟨_, _, h, ?_, rfl⟩
          cases d <;> simp [VLocalDecl.depth, VLocalDecl.inst, VExpr.lift_instN_lo]
      · intro H
        have := Expr.liftLooseBVars_add ▸ H.weakBV (.skip (d.inst e₀' k) .refl)
        cases d <;> simpa [← VExpr.lift_instN_lo, VExpr.liftN_zero,
          VLocalDecl.inst, VLocalDecl.depth] using this
      · obtain _|i := i; · omega
        intro | .bvar h => ?_
        exact .bvar <| by
          simp [VLCtx.find?, VLCtx.next]
          refine ⟨_, _, h, ?_, rfl⟩
          cases d <;> simp [VLocalDecl.depth, VLocalDecl.inst, VExpr.lift_instN_lo]
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      have .fvar h := ih H
      exact .fvar <| by
        simp [VLCtx.find?, VLCtx.next]
        refine ⟨_, _, h, ?_, rfl⟩
        cases d <;> simp [VLocalDecl.depth, VLocalDecl.inst, VExpr.lift_instN_lo]

theorem TrSyn.instN (W : VLCtx.InstN Δ₀ e₀' A₀ dk k Δ₁ Δ) (H : TrSyn Us Δ₁ e e') :
    TrSyn Us Δ (Expr.instantiate1' e e₀ dk) (e'.inst e₀' k) := by
  induction H generalizing Δ dk k with
  | bvar h1 | fvar h1 => exact instN_var h₀ W h1
  | sort h1 => exact .sort h1
  | const h1 => exact .const h1
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | letE _ _ _ ih1 ih2 ih3 => exact .letE (ih1 W) (ih2 W) (ih3 (W.succ (d := .vlet ..)))
  | lit _ ih =>
    refine .lit (Expr.instantiate1'_eq_self ?_ ▸ ih W :)
    exact Closed.toConstructor.looseBVarRange_le
  | mdata _ ih => exact .mdata (ih W)
  | proj _ ih => exact .proj (ih W)

theorem TrSyn.instN_let_var (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ)
    (H : Δ₁.find? v = some (e', A)) :
    TrSyn Us Δ (Expr.instantiate1' (VLCtx.varToExpr v) e₀ dk) e' := by
  induction W generalizing v e' A with
  | zero =>
    obtain (_|i)|fv := v <;> simp [VLCtx.varToExpr, Expr.instantiate1', Expr.liftLooseBVars_zero]
    · cases H; simp [VLocalDecl.value]; exact h₀
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      simp [VLocalDecl.depth]
      exact .bvar H
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      simp [VLocalDecl.depth]
      exact .fvar H
  | @succ _ k _ _ d _ ih =>
    obtain (_|i)|fv := v <;> simp [VLCtx.varToExpr, Expr.instantiate1']
    · cases H
      cases d <;> exact .bvar <| by simp [VLocalDecl.value]; rfl
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      have := ih H; revert this
      simp [VLCtx.varToExpr, Expr.instantiate1']; split <;> [skip; split]
      · intro | .bvar h => ?_
        exact .bvar <| by
          simp [VLCtx.find?, VLCtx.next]
          refine ⟨_, _, h, ?_, rfl⟩
          cases d <;> simp [VLocalDecl.depth]
      · intro H
        have := Expr.liftLooseBVars_add ▸ H.weakBV (.skip d .refl)
        cases d <;> simpa [VLocalDecl.depth] using this
      · obtain _|i := i; · omega
        intro | .bvar h => ?_
        exact .bvar <| by
          simp [VLCtx.find?, VLCtx.next]
          refine ⟨_, _, h, ?_, rfl⟩
          cases d <;> simp [VLocalDecl.depth]
    · simp [VLCtx.find?, VLCtx.next] at H
      obtain ⟨e, A, H, rfl, rfl⟩ := H
      have .fvar h := ih H
      exact .fvar <| by
        simp [VLCtx.find?, VLCtx.next]
        refine ⟨_, _, h, ?_, rfl⟩
        cases d <;> simp [VLocalDecl.depth]

theorem TrSyn.instN_let (W : VLCtx.InstLet Δ₀ e₀' A₀ dk k Δ₁ Δ) (H : TrSyn Us Δ₁ e e') :
    TrSyn Us Δ (Expr.instantiate1' e e₀ dk) e' := by
  induction H generalizing Δ dk k with
  | bvar h1 | fvar h1 => exact instN_let_var h₀ W h1
  | sort h1 => exact .sort h1
  | const h1 => exact .const h1
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 (W.succ (d := .vlam _)))
  | letE _ _ _ ih1 ih2 ih3 => exact .letE (ih1 W) (ih2 W) (ih3 (W.succ (d := .vlet ..)))
  | lit _ ih =>
    refine .lit (Expr.instantiate1'_eq_self ?_ ▸ ih W :)
    exact Closed.toConstructor.looseBVarRange_le
  | mdata _ ih => exact .mdata (ih W)
  | proj _ ih => exact .proj (ih W)

end

theorem TrSyn.inst {Us : List Name} {Δ : VLCtx}
    (H : TrSyn Us ((none, .vlam A₀) :: Δ) e e') (h₀ : TrSyn Us Δ e₀ e₀') :
    TrSyn Us Δ (e.instantiate1' e₀) (e'.inst e₀') :=
  h₀.instN .zero H

theorem TrSyn.inst_let {Us : List Name} {Δ : VLCtx}
    (H : TrSyn Us ((none, .vlet A₀ e₀') :: Δ) e e') (h₀ : TrSyn Us Δ e₀ e₀') :
    TrSyn Us Δ (e.instantiate1' e₀) e' :=
  h₀.instN_let .zero H

/-! ### Abstraction -/

theorem TrSyn.abstract {Us : List Name} (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ)
    (H : TrSyn Us Δ₁ e e') : TrSyn Us Δ (e.abstract1 v₀ dk) e' := by
  induction H generalizing dk k Δ with
  | bvar h1 =>
    exact .bvar <| (W.find? (by nofun)).trans <| by
      simp; split <;> [skip; rw [if_neg (by omega), if_neg (by omega)]] <;> exact h1
  | @fvar _ _ _ fv h1 =>
    if h : fv = v₀ then
      rw [h, W.find?_self] at h1; cases h1
      rw [Expr.abstract1, if_pos (by simp [h])]
      exact .bvar <| (W.find? (by nofun)).trans (by simpa using W.find?_self)
    else
      have := W.find? (v := .inr fv) (by rintro ⟨⟩; trivial)
      simp at this
      rw [Expr.abstract1, if_neg]
      · exact .fvar (this.trans h1)
      · simp; rintro rfl; trivial
  | sort h1 => exact .sort h1
  | const h1 => exact .const h1
  | app _ _ ih1 ih2 => exact .app (ih1 W) (ih2 W)
  | lam _ _ ih1 ih2 => exact .lam (ih1 W) (ih2 W.succ)
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 W) (ih2 W.succ)
  | letE _ _ _ ih1 ih2 ih3 => exact .letE (ih1 W) (ih2 W) (ih3 W.succ)
  | lit _ ih => exact .lit (FVarsIn.toConstructor.abstract_eq_self .toConstructor ▸ ih W)
  | mdata _ ih => exact .mdata (ih W)
  | proj _ ih => exact .proj (ih W)

theorem TrSyn.uninstantiateN {Us : List Name} (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ)
    (H : TrSyn Us Δ₁ (Expr.instantiate1' e (.fvar v₀) dk) e')
    (sc : FVarsIn (· ≠ v₀) e) : TrSyn Us Δ e e' := by
  have := H.abstract W
  rwa [sc.abstract_instantiate1] at this

theorem TrSyn.uninstantiate {Us : List Name}
    (H : TrSyn Us ((some (v, deps), d) :: Δ) (e.instantiate1' (.fvar v)) e')
    (sc : FVarsIn (· ≠ v) e) : TrSyn Us ((none, d) :: Δ) e e' := H.uninstantiateN .zero sc

/-- Opening a binder with a fresh free variable. The typed version
(`TrExprS.inst_fvar`) needs the context to be well formed; here only its free variables need to
be distinct. -/
theorem TrSyn.inst_fvar {Us : List Name} {Δ : VLCtx}
    (hnd : (VLCtx.fvars ((some (a, deps), d) :: Δ)).Nodup)
    (H : TrSyn Us ((none, d) :: Δ) e e') :
    TrSyn Us ((some (a, deps), d) :: Δ) (e.instantiate1' (.fvar a)) e' := by
  have W := VLCtx.FVLift.skip_fvar (a, deps) d (Δ := Δ) .refl
  have := H.weakFV (.cons_bvar _ W) hnd
  have hf : TrSyn Us ((some (a, deps), d) :: Δ) (.fvar a) d.value := .fvar (A := d.type) <| by
    simp [VLCtx.find?, VLCtx.next]
  match d with
  | .vlam A₀ =>
    have := this.inst (Δ := (some (a, deps), .vlam _) :: Δ) hf
    simp only [VLocalDecl.depth, VLocalDecl.value, Nat.zero_add] at this
    rwa [VExpr.inst_liftN_bvar] at this
  | .vlet A₀ e₀ =>
    simp [VLocalDecl.depth, VLocalDecl.liftN] at this
    exact this.inst_let hf

/-! ### Level instantiation -/

theorem TrSyn.instL {Us Us' : List Name} {ls : List VLevel} {Δ : VLCtx} {e : Lean.Expr}
    {e' : VExpr}
    (hlev : ∀ u u', VLevel.ofLevel Us u = some u' → VLevel.ofLevel Us' u = some (u'.inst ls))
    (H : TrSyn Us Δ e e') : TrSyn Us' (Δ.instL ls) e (e'.instL ls) := by
  have hlevs : ∀ (us : List Level) us', us.mapM (VLevel.ofLevel Us) = some us' →
      us.mapM (VLevel.ofLevel Us') = some (us'.map (VLevel.inst ls)) := by
    intro us
    induction us with
    | nil => intro us' h; simp at h; subst h; rfl
    | cons u us ih =>
      intro us' h
      simp [List.mapM_cons] at h ⊢
      rcases h with ⟨u', hu, us'', hus, rfl⟩
      exact ⟨_, hlev _ _ hu, _, ih _ hus, rfl⟩
  induction H with
  | bvar h1 => exact .bvar (VLCtx.find?_instL h1)
  | fvar h1 => exact .fvar (VLCtx.find?_instL h1)
  | sort h1 => exact .sort (hlev _ _ h1)
  | const h1 => exact .const (hlevs _ _ h1)
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | lit _ ih => exact .lit ih
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

/-- Universe weakening: prepending a fresh level parameter. -/
theorem TrSyn.prependLevelParam {Us : List Name} (hfresh : fresh ∉ Us) (H : TrSyn Us Δ e e') :
    TrSyn (fresh :: Us) (Δ.instL (VLevel.prependShift Us.length)) e
      (e'.instL (VLevel.prependShift Us.length)) := by
  induction H with
  | bvar hfind => exact .bvar (VLCtx.find?_instL hfind)
  | fvar hfind => exact .fvar (VLCtx.find?_instL hfind)
  | sort hlevel => exact .sort (VLevel.ofLevel_fresh_cons hfresh hlevel)
  | const hlevels => exact .const (VLevel.mapM_ofLevel_fresh_cons hfresh hlevels)
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | lit _ ih => exact .lit ih
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

section
variable {Us ps : List Name} {ls : List Level} {ls' : List VLevel}
  (Hls : ls.mapM (VLevel.ofLevel Us) = some ls')
  (eq : ps.length = ls.length)
include Hls eq

/-- Level instantiation: the instantiated source translates, in any context level-equivalent to
the instantiated one, to a term level-equivalent to the instantiated translation. This is the
existence half that `TrExprS.instL` gets from typing; here it is purely syntactic. -/
theorem TrSyn.instL_lequiv (H : TrSyn ps Δ e e') :
    ∀ {Δ₂}, VLCtx.LEquiv Us.length Δ₂ (Δ.instL ls') →
    ∃ e₁, TrSyn Us Δ₂ (e.instantiateLevelParams ps ls) e₁ ∧
      VExpr.LEquiv Us.length e₁ (e'.instL ls') := by
  simp only [Expr.instantiateLevelParams_eq]
  generalize (_ && _) = red, eqF : (fun x : Name => _) = F
  have Hls' := VLevel.WF.of_mapM_ofLevel Hls
  induction H with
  | bvar h1 =>
    intro Δ₂ hΔ₂
    have ⟨_, _, h2, l1, _⟩ := hΔ₂.find? (VLCtx.find?_instL h1)
    exact ⟨_, .bvar h2, l1⟩
  | fvar h1 =>
    intro Δ₂ hΔ₂
    have ⟨_, _, h2, l1, _⟩ := hΔ₂.find? (VLCtx.find?_instL h1)
    exact ⟨_, .fvar h2, l1⟩
  | sort h1 =>
    intro Δ₂ _
    have ⟨_, a1, a2⟩ := substParams_wf Hls eq eqF red h1
    exact ⟨_, .sort a1, .sort a2 (.inst Hls')⟩
  | const h1 =>
    intro Δ₂ _
    have ⟨_, a1, a2⟩ := substParams_wf_list Hls eq eqF red h1
    refine ⟨_, .const a1, .const a2 ?_⟩
    simp; exact fun _ _ => .inst Hls'
  | app _ _ ih1 ih2 =>
    intro Δ₂ hΔ₂
    obtain ⟨_, s1, l1⟩ := ih1 hΔ₂
    obtain ⟨_, s2, l2⟩ := ih2 hΔ₂
    exact ⟨_, .app s1 s2, .app l1 l2⟩
  | lam _ _ ih1 ih2 =>
    intro Δ₂ hΔ₂
    obtain ⟨_, s1, l1⟩ := ih1 hΔ₂
    obtain ⟨_, s2, l2⟩ := ih2 (.cons hΔ₂ (.vlam l1))
    exact ⟨_, .lam s1 s2, .lam l1 l2⟩
  | forallE _ _ ih1 ih2 =>
    intro Δ₂ hΔ₂
    obtain ⟨_, s1, l1⟩ := ih1 hΔ₂
    obtain ⟨_, s2, l2⟩ := ih2 (.cons hΔ₂ (.vlam l1))
    exact ⟨_, .forallE s1 s2, .forallE l1 l2⟩
  | letE _ _ _ ih1 ih2 ih3 =>
    intro Δ₂ hΔ₂
    obtain ⟨_, s1, l1⟩ := ih1 hΔ₂
    obtain ⟨_, s2, l2⟩ := ih2 hΔ₂
    obtain ⟨_, s3, l3⟩ := ih3 (.cons hΔ₂ (.vlet l1 l2))
    exact ⟨_, .letE s1 s2 s3, l3⟩
  | lit _ ih =>
    intro Δ₂ hΔ₂
    obtain ⟨_, s, l⟩ := ih hΔ₂
    rw [Expr.instantiateLevelParamsCore_eq_self Literal.toConstructor_hasLevelParam] at s
    exact ⟨_, .lit s, l⟩
  | mdata _ ih =>
    intro Δ₂ hΔ₂
    obtain ⟨_, s, l⟩ := ih hΔ₂
    exact ⟨_, .mdata s, l⟩
  | proj _ ih =>
    intro Δ₂ hΔ₂
    obtain ⟨_, s, l⟩ := ih hΔ₂
    exact ⟨_, .proj s, .proj l⟩

/-- Any translation of the instantiated source is level-equivalent to the instantiated
translation: existence and uniqueness of syntactic translation. -/
theorem TrSyn.instL_lequiv_of (H : TrSyn ps Δ e e')
    (hΔ₂ : VLCtx.LEquiv Us.length Δ₂ (Δ.instL ls'))
    (H2 : TrSyn Us Δ₂ (e.instantiateLevelParams ps ls) e₁) :
    VExpr.LEquiv Us.length e₁ (e'.instL ls') :=
  let ⟨_, s, l⟩ := H.instL_lequiv Hls eq hΔ₂
  H2.unique s ▸ l

end

/-! ### Equality up to binder names, domains, and skeletons -/

theorem TrSyn.eqv {Us : List Name} (H : TrSyn Us Δ e₁ e') : e₁ == e₂ → TrSyn Us Δ e₂ e' := by
  simp [(· == ·)]
  induction H generalizing e₂ <;> (cases e₂ <;> try change false = _ → _; rintro ⟨⟩)
  all_goals simp [Expr.eqv']; grind [TrSyn]

/-- Syntactic translation ignores the domains recorded in the context. -/
theorem TrSyn.transport {Us : List Name} {Δ₁ Δ₂ : VLCtx} {e : Lean.Expr} {e' : VExpr}
    (hΔ : TrExprS.IsUniqueCtx Δ₁ Δ₂) (H : TrSyn Us Δ₁ e e') : TrSyn Us Δ₂ e e' := by
  induction H generalizing Δ₂ with
  | bvar h => obtain ⟨_, h⟩ := hΔ.find?_exists h; exact .bvar h
  | fvar h => obtain ⟨_, h⟩ := hΔ.find?_exists h; exact .fvar h
  | sort h => exact .sort h
  | const h => exact .const h
  | app _ _ ih1 ih2 => exact .app (ih1 hΔ) (ih2 hΔ)
  | lam _ _ ih1 ih2 => exact .lam (ih1 hΔ) (ih2 (hΔ.cons .vlam))
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 hΔ) (ih2 (hΔ.cons .vlam))
  | letE _ _ _ ih1 ih2 ih3 => exact .letE (ih1 hΔ) (ih2 hΔ) (ih3 (hΔ.cons .vlet))
  | lit _ ih => exact .lit (ih hΔ)
  | mdata _ ih => exact .mdata (ih hΔ)
  | proj _ ih => exact .proj (ih hΔ)

/-! ### Restriction: the syntactic half of strengthening -/

/-- Deleting bound variables the source does not use. The translation of a lifted source in
the larger context is the lift of a translation in the smaller one. -/
theorem TrSyn.lowerBV {Us : List Name} (W : VLCtx.BVLift Δ Δ' dn dk n k)
    (H : TrSyn Us Δ' (Expr.liftLooseBVars' e₀ dk dn) e') :
    ∃ e₀', TrSyn Us Δ e₀ e₀' ∧ e' = e₀'.liftN n k := by
  generalize he : Expr.liftLooseBVars' e₀ dk dn = e at H
  induction H generalizing e₀ Δ dk k with
  | bvar h1 =>
    cases e₀ <;> simp [Expr.liftLooseBVars'] at he
    subst he
    rename_i j
    have hv : VLCtx.liftVar dn dk (.inl j) = .inl (if j < dk then j else j + dn) := rfl
    obtain ⟨⟨x, A⟩, hx⟩ := W.find?_lift_inv (v := .inl j) (by rw [hv]; exact h1)
    have := W.find? hx
    rw [hv, h1] at this
    cases this; exact ⟨_, .bvar hx, rfl⟩
  | fvar h1 =>
    cases e₀ <;> simp [Expr.liftLooseBVars'] at he
    subst he
    obtain ⟨⟨x, A⟩, hx⟩ := W.find?_lift_inv (v := .inr _) h1
    have := W.find? hx
    rw [show VLCtx.liftVar dn dk (.inr _) = .inr _ from rfl, h1] at this
    cases this; exact ⟨_, .fvar hx, rfl⟩
  | sort h =>
    cases e₀ <;> simp [Expr.liftLooseBVars'] at he
    subst he; exact ⟨_, .sort h, rfl⟩
  | const h =>
    cases e₀ <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl⟩ := he; exact ⟨_, .const h, rfl⟩
  | app _ _ ih1 ih2 =>
    cases e₀ <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨f₀, s1, rfl⟩ := ih1 W rfl
    obtain ⟨a₀, s2, rfl⟩ := ih2 W rfl
    exact ⟨.app f₀ a₀, .app s1 s2, rfl⟩
  | lam _ _ ih1 ih2 =>
    cases e₀ <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    obtain ⟨t₀, s1, rfl⟩ := ih1 W rfl
    obtain ⟨b₀, s2, rfl⟩ := ih2 (W.cons (.vlam t₀)) rfl
    exact ⟨.lam t₀ b₀, .lam s1 s2, rfl⟩
  | forallE _ _ ih1 ih2 =>
    cases e₀ <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    obtain ⟨t₀, s1, rfl⟩ := ih1 W rfl
    obtain ⟨b₀, s2, rfl⟩ := ih2 (W.cons (.vlam t₀)) rfl
    exact ⟨.forallE t₀ b₀, .forallE s1 s2, rfl⟩
  | letE _ _ _ ih1 ih2 ih3 =>
    cases e₀ <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
    obtain ⟨t₀, s1, rfl⟩ := ih1 W rfl
    obtain ⟨v₀, s2, rfl⟩ := ih2 W rfl
    obtain ⟨b₀, s3, rfl⟩ := ih3 (W.cons (.vlet t₀ v₀)) rfl
    exact ⟨b₀, .letE s1 s2 s3, rfl⟩
  | lit _ ih =>
    cases e₀ <;> simp [Expr.liftLooseBVars'] at he
    subst he
    obtain ⟨x, s, rfl⟩ :=
      ih W (Expr.liftLooseBVars_eq_self Closed.toConstructor.looseBVarRange_le)
    exact ⟨x, .lit s, rfl⟩
  | mdata _ ih =>
    cases e₀ <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨x, s, rfl⟩ := ih W rfl
    exact ⟨x, .mdata s, rfl⟩
  | proj _ ih =>
    cases e₀ <;> simp [Expr.liftLooseBVars'] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨x₀, s, rfl⟩ := ih W rfl
    exact ⟨.proj _ _ x₀, .proj s, rfl⟩

/-- Deleting the innermost binder, when the body does not use it. -/
theorem TrSyn.lower {Us : List Name}
    (H : TrSyn Us ((none, d) :: Δ) (Expr.liftLooseBVars' e₀ 0 1) e') :
    ∃ e₀', TrSyn Us Δ e₀ e₀' ∧ e' = e₀'.liftN d.depth := by
  have := H.lowerBV (.skip d .refl)
  simpa using this

/-- Restricting free variables: a source mentioning only the free variables of `Δ` translates
in `Δ`, and its translation in an extension `Δ'` of `Δ` by free variables is the lift. It is
totality (`TrSyn.exists_of_scoped`), weakening and uniqueness. -/
theorem TrSyn.restrictFV {Us : List Name} (W : VLCtx.FVLift Δ Δ' dk n k)
    (hnd : Δ'.fvars.Nodup) (H : TrSyn Us Δ' e e') (hfv : FVarsIn (· ∈ Δ.fvars) e) :
    ∃ e₀', TrSyn Us Δ e e₀' ∧ e' = e₀'.liftN n k := by
  have hc : Closed e Δ.bvars := W.toFVLift'.bvars_eq ▸ H.closed
  obtain ⟨e₀', h⟩ := TrSyn.exists_of_scoped hc hfv H.levelParamsIn
  exact ⟨e₀', h, H.unique (h.weakFV W hnd)⟩

end Lean4Lean
