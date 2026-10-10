import Lean4Lean.Verify.LocalContext

/-!
# Parameter-uniform expressions (core definitions)

This file holds the syntactic predicates `Expr.ParamUniform`, `Expr.ParamUniformBV` and
`Expr.ParamUniformTele` together with their structural lemmas. An expression is
parameter-uniform for a set of head constants when every application of a head is applied to
exactly the block parameters at the block universe levels; restoration of a nested
declaration (section 3.3 of the design notes) copies the trailing arguments of such
an application verbatim. The generic constant-absence
judgment `Expr.AvoidsConsts` is in `Lean4Lean/Verify/Expr.lean`, and the binder-prefix
predicate `Expr.LeadingBinders` in `Lean4Lean/Verify/LocalContext.lean`. It depends only on the expression-level
verification library, so that the parameter-uniformity invariant of the verified type checker
(`Lean4Lean/Verify/TypeChecker/Basic.lean`) can mention it. The facts specific to nested
restoration are in `Lean4Lean/Verify/Inductive/Nested/Restoration/ParameterOpening.lean` (the
executable parameter opening `openRestoreParams`) and `Lean4Lean/Verify/Inductive/Nested/Restoration/Uniform/`.
-/

namespace Lean.Expr

open Lean4Lean

/-! ### Spine helpers -/

private theorem mkAppList_map {g : Expr → Expr} (hg : ∀ f a, g (.app f a) = .app (g f) (g a))
    (f : Expr) (l : List Expr) : g (mkAppList f l) = mkAppList (g f) (l.map g) := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih => simp only [mkAppList, List.map_cons]; rw [ih, hg]

private theorem map_fvars_eq_self {g : Expr → Expr} (hg : ∀ fv, g (.fvar fv) = .fvar fv)
    {params : List Expr} (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv) : params.map g = params := by
  conv => rhs; rw [← List.map_id params]
  refine List.map_congr_left fun p hmem => ?_
  obtain ⟨fv, rfl⟩ := hp p hmem
  exact hg fv

/-- The parameter variables at depth `d` of a closed parameter telescope of length `nparams`:
parameter `i` is `.bvar (d + (nparams - 1 - i))`. This is what `Expr.abstract As` produces for
`As[i]` under `d` binders when `As` are distinct fvars. -/
def paramBVars (nparams d : Nat) : List Expr :=
  (List.range nparams).map fun i => .bvar (d + (nparams - 1 - i))

@[simp] theorem length_paramBVars : (paramBVars nparams d).length = nparams := by
  simp [paramBVars]

/-! ### The free-variable form -/

/-- `ParamUniform heads params ls e`: every application spine of `e` whose head is `.const c us`
with `c ∈ heads` (a *head occurrence*) has `us = ls` and its first `params.length` arguments literally equal
to `params`; every other node is traversed structurally. Intended use: `params = As.toList`
where `As` are the fvars opened by `openRestoreParams`, `heads` are the auxiliary family and
auxiliary constructor names (for the checker invariant also the source constructor names), and `ls = lparams.map .param`.

Under binders `params` is unchanged (fvars are not shifted), so there is no depth index. The
parameter arguments of a head occurrence are not themselves required to have shape. -/
inductive ParamUniform (heads : List Name) (params : List Expr) (ls : List Level) : Expr → Prop
  /-- A head applied to exactly the parameters. Trailing arguments are added by `app`. -/
  | head {c : Name} : c ∈ heads →
      ParamUniform heads params ls (mkAppList (.const c ls) params)
  | app {f a : Expr} : ParamUniform heads params ls f → ParamUniform heads params ls a →
      ParamUniform heads params ls (.app f a)
  | const {c : Name} {us : List Level} : c ∉ heads → ParamUniform heads params ls (.const c us)
  | bvar (i : Nat) : ParamUniform heads params ls (.bvar i)
  | fvar (fv : FVarId) : ParamUniform heads params ls (.fvar fv)
  | mvar (mv : MVarId) : ParamUniform heads params ls (.mvar mv)
  | sort (u : Level) : ParamUniform heads params ls (.sort u)
  | lit (l : Literal) : ParamUniform heads params ls (.lit l)
  | lam {n : Name} {t b : Expr} {bi : BinderInfo} :
      ParamUniform heads params ls t → ParamUniform heads params ls b →
      ParamUniform heads params ls (.lam n t b bi)
  | forallE {n : Name} {t b : Expr} {bi : BinderInfo} :
      ParamUniform heads params ls t → ParamUniform heads params ls b →
      ParamUniform heads params ls (.forallE n t b bi)
  | letE {n : Name} {t v b : Expr} {nd : Bool} :
      ParamUniform heads params ls t → ParamUniform heads params ls v → ParamUniform heads params ls b →
      ParamUniform heads params ls (.letE n t v b nd)
  | mdata {m : MData} {e : Expr} : ParamUniform heads params ls e →
      ParamUniform heads params ls (.mdata m e)
  | proj {s : Name} {i : Nat} {e : Expr} : ParamUniform heads params ls e →
      ParamUniform heads params ls (.proj s i e)

/-! ### The bound-variable form -/

/-- `ParamUniformBV heads nparams ls d e`: the bound-variable twin of `ParamUniform`, for stored terms
whose parameter telescope of length `nparams` is closed. `d` is the number of binders passed
since the parameter telescope, so at a head occurrence the first `nparams` arguments must be
`paramBVars nparams d`, i.e. parameter `i` is `.bvar (d + (nparams - 1 - i))`. The index
increases by one under the bodies of `lam`, `forallE` and `letE`. -/
inductive ParamUniformBV (heads : List Name) (nparams : Nat) (ls : List Level) : Nat → Expr → Prop
  | head {c : Name} {d : Nat} : c ∈ heads →
      ParamUniformBV heads nparams ls d (mkAppList (.const c ls) (paramBVars nparams d))
  | app {d : Nat} {f a : Expr} : ParamUniformBV heads nparams ls d f →
      ParamUniformBV heads nparams ls d a → ParamUniformBV heads nparams ls d (.app f a)
  | const {d : Nat} {c : Name} {us : List Level} : c ∉ heads →
      ParamUniformBV heads nparams ls d (.const c us)
  | bvar {d : Nat} (i : Nat) : ParamUniformBV heads nparams ls d (.bvar i)
  | fvar {d : Nat} (fv : FVarId) : ParamUniformBV heads nparams ls d (.fvar fv)
  | mvar {d : Nat} (mv : MVarId) : ParamUniformBV heads nparams ls d (.mvar mv)
  | sort {d : Nat} (u : Level) : ParamUniformBV heads nparams ls d (.sort u)
  | lit {d : Nat} (l : Literal) : ParamUniformBV heads nparams ls d (.lit l)
  | lam {d : Nat} {n : Name} {t b : Expr} {bi : BinderInfo} :
      ParamUniformBV heads nparams ls d t → ParamUniformBV heads nparams ls (d + 1) b →
      ParamUniformBV heads nparams ls d (.lam n t b bi)
  | forallE {d : Nat} {n : Name} {t b : Expr} {bi : BinderInfo} :
      ParamUniformBV heads nparams ls d t → ParamUniformBV heads nparams ls (d + 1) b →
      ParamUniformBV heads nparams ls d (.forallE n t b bi)
  | letE {d : Nat} {n : Name} {t v b : Expr} {nd : Bool} :
      ParamUniformBV heads nparams ls d t → ParamUniformBV heads nparams ls d v →
      ParamUniformBV heads nparams ls (d + 1) b →
      ParamUniformBV heads nparams ls d (.letE n t v b nd)
  | mdata {d : Nat} {m : MData} {e : Expr} : ParamUniformBV heads nparams ls d e →
      ParamUniformBV heads nparams ls d (.mdata m e)
  | proj {d : Nat} {s : Name} {i : Nat} {e : Expr} : ParamUniformBV heads nparams ls d e →
      ParamUniformBV heads nparams ls d (.proj s i e)

/-! ### Construction -/

namespace ParamUniform

variable {heads : List Name} {params : List Expr} {ls : List Level}

/-- Shape is closed under applying shaped arguments. -/
theorem mkAppList {f : Expr} {args : List Expr} (hf : ParamUniform heads params ls f)
    (hargs : ∀ a ∈ args, ParamUniform heads params ls a) :
    ParamUniform heads params ls (f.mkAppList args) := by
  induction args generalizing f with
  | nil => exact hf
  | cons a args ih =>
    exact ih (.app hf (hargs a (.head _))) fun b hb => hargs b (.tail _ hb)

/-- A head occurrence: a head in `heads`, at the levels `ls`, applied to the parameters and then to shaped
trailing arguments. -/
theorem mkAppList_const_head {c : Name} {rest : List Expr} (hc : c ∈ heads)
    (hrest : ∀ a ∈ rest, ParamUniform heads params ls a) :
    ParamUniform heads params ls ((Expr.const c ls).mkAppList (params ++ rest)) := by
  rw [Expr.mkAppList_append]
  exact (head hc).mkAppList hrest

/-- An expression that mentions no constant of `heads` has shape (vacuously). -/
theorem of_avoidsConsts {e : Expr} (h : e.AvoidsConsts heads) : ParamUniform heads params ls e := by
  induction h with
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | const _ _ fresh => exact .const fresh
  | app _ _ _ _ ihf iha => exact .app ihf iha
  | lam _ _ _ _ _ _ iht ihb => exact .lam iht ihb
  | forallE _ _ _ _ _ _ iht ihb => exact .forallE iht ihb
  | letE _ _ _ _ _ _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | lit => exact .lit _
  | mdata _ _ _ ih => exact .mdata ih
  | proj _ _ _ _ ih => exact .proj ih

/-! ### Inversion -/

/-- Spine inversion at a head occurrence: a shaped expression whose application head is `.const c us`
with `c ∈ heads` has `us = ls`, and its argument list is `params ++ rest` with every trailing
argument shaped. -/
theorem getAppFn_const_head_inv {e : Expr} {c : Name} {us : List Level}
    (H : ParamUniform heads params ls e) (hfn : e.getAppFn = .const c us) (hc : c ∈ heads) :
    us = ls ∧ ∃ rest, e.getAppArgsList = params ++ rest ∧
      ∀ a ∈ rest, ParamUniform heads params ls a := by
  induction H with
  | head _ =>
    rw [getAppFn_mkAppList_const] at hfn
    cases hfn
    refine ⟨rfl, [], ?_, by simp⟩
    rw [getAppArgsList_mkAppList, getAppArgsList_const]; simp
  | @app f a hf ha ihf _ =>
    obtain ⟨hus, rest, hargs, hrest⟩ := ihf hfn
    refine ⟨hus, rest ++ [a], ?_, ?_⟩
    · rw [getAppArgsList_app, hargs, List.append_assoc]
    · intro b hb
      rcases List.mem_append.1 hb with hb | hb
      · exact hrest b hb
      · rw [List.mem_singleton.1 hb]; exact ha
  | const hnot => cases hfn; exact absurd hc hnot
  | _ => cases hfn

/-- Inversion at an application whose head is not in `heads`. -/
theorem app_inv {f a : Expr} (H : ParamUniform heads params ls (.app f a))
    (hnot : ∀ c us, f.getAppFn = .const c us → c ∉ heads) :
    ParamUniform heads params ls f ∧ ParamUniform heads params ls a := by
  generalize he : Expr.app f a = e at H
  cases H with
  | app hf ha => cases he; exact ⟨hf, ha⟩
  | @head c hc =>
    have := congrArg Expr.getAppFn he
    rw [getAppFn_mkAppList_const] at this
    exact absurd hc (hnot _ _ this)
  | _ => cases he

/-- Inversion of an application spine whose head is not in `heads`. -/
theorem mkAppList_inv {f : Expr} {args : List Expr}
    (H : ParamUniform heads params ls (f.mkAppList args))
    (hnot : ∀ c us, f.getAppFn = .const c us → c ∉ heads) :
    ParamUniform heads params ls f ∧ ∀ a ∈ args, ParamUniform heads params ls a := by
  rw [← List.reverse_reverse args] at H ⊢
  generalize args.reverse = rargs at H ⊢
  induction rargs with
  | nil => exact ⟨H, by simp⟩
  | cons a rargs ih =>
    rw [List.reverse_cons, Expr.mkAppList_append] at H
    have hnot' : ∀ c us, (f.mkAppList rargs.reverse).getAppFn = .const c us → c ∉ heads := by
      rw [getAppFn_mkAppList]; exact hnot
    obtain ⟨hf, ha⟩ := app_inv H hnot'
    obtain ⟨hf', hargs⟩ := ih hf
    refine ⟨hf', fun b hb => ?_⟩
    rw [List.reverse_cons] at hb
    rcases List.mem_append.1 hb with hb | hb
    · exact hargs b hb
    · rw [List.mem_singleton.1 hb]; exact ha

theorem const_inv {c : Name} {us : List Level} (H : ParamUniform heads params ls (.const c us)) :
    c ∉ heads ∨ (c ∈ heads ∧ us = ls ∧ params = []) := by
  by_cases hc : c ∈ heads
  · obtain ⟨hus, rest, hargs, -⟩ := H.getAppFn_const_head_inv rfl hc
    rw [getAppArgsList_const] at hargs
    exact .inr ⟨hc, hus, (List.append_eq_nil_iff.1 hargs.symm).1⟩
  · exact .inl hc

private theorem not_head_of_getAppFn {e : Expr} (hfn : ∀ c us, e.getAppFn ≠ .const c us)
    {c : Name} : e ≠ (Expr.const c ls).mkAppList params := by
  intro he
  have := congrArg Expr.getAppFn he
  rw [getAppFn_mkAppList_const] at this
  exact hfn _ _ this

theorem lam_inv {n : Name} {t b : Expr} {bi : BinderInfo}
    (H : ParamUniform heads params ls (.lam n t b bi)) :
    ParamUniform heads params ls t ∧ ParamUniform heads params ls b := by
  generalize he : Expr.lam n t b bi = e at H
  cases H with
  | lam ht hb => cases he; exact ⟨ht, hb⟩
  | head => exact absurd he (not_head_of_getAppFn (by intros; simp [getAppFn]))
  | _ => cases he

theorem forallE_inv {n : Name} {t b : Expr} {bi : BinderInfo}
    (H : ParamUniform heads params ls (.forallE n t b bi)) :
    ParamUniform heads params ls t ∧ ParamUniform heads params ls b := by
  generalize he : Expr.forallE n t b bi = e at H
  cases H with
  | forallE ht hb => cases he; exact ⟨ht, hb⟩
  | head => exact absurd he (not_head_of_getAppFn (by intros; simp [getAppFn]))
  | _ => cases he

theorem letE_inv {n : Name} {t v b : Expr} {nd : Bool}
    (H : ParamUniform heads params ls (.letE n t v b nd)) :
    ParamUniform heads params ls t ∧ ParamUniform heads params ls v ∧ ParamUniform heads params ls b := by
  generalize he : Expr.letE n t v b nd = e at H
  cases H with
  | letE ht hv hb => cases he; exact ⟨ht, hv, hb⟩
  | head => exact absurd he (not_head_of_getAppFn (by intros; simp [getAppFn]))
  | _ => cases he

theorem mdata_inv {m : MData} {e : Expr} (H : ParamUniform heads params ls (.mdata m e)) :
    ParamUniform heads params ls e := by
  generalize he : Expr.mdata m e = e' at H
  cases H with
  | mdata h => cases he; exact h
  | head => exact absurd he (not_head_of_getAppFn (by intros; simp [getAppFn]))
  | _ => cases he

theorem proj_inv {s : Name} {i : Nat} {e : Expr} (H : ParamUniform heads params ls (.proj s i e)) :
    ParamUniform heads params ls e := by
  generalize he : Expr.proj s i e = e' at H
  cases H with
  | proj h => cases he; exact h
  | head => exact absurd he (not_head_of_getAppFn (by intros; simp [getAppFn]))
  | _ => cases he

/-! ### Substitution

All of these assume the parameters are fvars (`hp`), so that bound-variable operations fix
them. -/

private theorem head_map {g : Expr → Expr} (hg : ∀ f a, g (.app f a) = .app (g f) (g a))
    (hc : ∀ c us, g (.const c us) = .const c us) (hfv : ∀ fv, g (.fvar fv) = .fvar fv)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv) (c : Name) :
    g ((Expr.const c ls).mkAppList params) = (Expr.const c ls).mkAppList params := by
  rw [mkAppList_map hg, hc, map_fvars_eq_self hfv hp]

/-- Shape is invariant under shifting loose bound variables. -/
theorem liftLooseBVars' {e : Expr} (H : ParamUniform heads params ls e)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv) (s d : Nat) :
    ParamUniform heads params ls (e.liftLooseBVars' s d) := by
  induction H generalizing s with
  | head hc =>
    rw [head_map (g := fun e => e.liftLooseBVars' s d) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ => rfl) hp]
    exact .head hc
  | app _ _ ihf iha => exact .app (ihf s) (iha s)
  | const hc => exact .const hc
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | lit => exact .lit _
  | lam _ _ iht ihb => exact .lam (iht s) (ihb (s + 1))
  | forallE _ _ iht ihb => exact .forallE (iht s) (ihb (s + 1))
  | letE _ _ _ iht ihv ihb => exact .letE (iht s) (ihv s) (ihb (s + 1))
  | mdata _ ih => exact .mdata (ih s)
  | proj _ ih => exact .proj (ih s)

/-- Shape is invariant under lowering loose bound variables. -/
theorem lowerLooseBVars' {e : Expr} (H : ParamUniform heads params ls e)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv) (s d : Nat) :
    ParamUniform heads params ls (e.lowerLooseBVars' s d) := by
  induction H generalizing s with
  | @head c hc =>
    have hid : ∀ e : Expr, s < d → e.lowerLooseBVars' s d = e := fun e h => by
      unfold Expr.lowerLooseBVars'; simp [h]
    have hg : ∀ f a, (Expr.app f a).lowerLooseBVars' s d =
        .app (f.lowerLooseBVars' s d) (a.lowerLooseBVars' s d) := by
      intro f a
      by_cases h : s < d
      · rw [hid _ h, hid _ h, hid _ h]
      · conv => lhs; unfold Expr.lowerLooseBVars'
        simp [h]
    have hleaf : ∀ e : Expr, (∀ s' d', Expr.lowerLooseBVars' e s' d' =
        if s' < d' then e else e) → e.lowerLooseBVars' s d = e := fun e h => by
      rw [h]; split <;> rfl
    rw [head_map (g := fun e => e.lowerLooseBVars' s d) hg
      (fun _ _ => hleaf _ fun _ _ => by unfold Expr.lowerLooseBVars'; split <;> rfl)
      (fun _ => hleaf _ fun _ _ => by unfold Expr.lowerLooseBVars'; split <;> rfl) hp]
    exact .head hc
  | app hf ha ihf iha =>
    unfold Expr.lowerLooseBVars'; split
    · exact .app hf ha
    · exact .app (ihf s) (iha s)
  | const hc => unfold Expr.lowerLooseBVars'; split <;> exact .const hc
  | bvar => unfold Expr.lowerLooseBVars'; split <;> exact .bvar _
  | fvar => unfold Expr.lowerLooseBVars'; split <;> exact .fvar _
  | mvar => unfold Expr.lowerLooseBVars'; split <;> exact .mvar _
  | sort => unfold Expr.lowerLooseBVars'; split <;> exact .sort _
  | lit => unfold Expr.lowerLooseBVars'; split <;> exact .lit _
  | lam ht hb iht ihb =>
    unfold Expr.lowerLooseBVars'; split
    · exact .lam ht hb
    · exact .lam (iht s) (ihb (s + 1))
  | forallE ht hb iht ihb =>
    unfold Expr.lowerLooseBVars'; split
    · exact .forallE ht hb
    · exact .forallE (iht s) (ihb (s + 1))
  | letE ht hv hb iht ihv ihb =>
    unfold Expr.lowerLooseBVars'; split
    · exact .letE ht hv hb
    · exact .letE (iht s) (ihv s) (ihb (s + 1))
  | mdata h ih =>
    unfold Expr.lowerLooseBVars'; split
    · exact .mdata h
    · exact .mdata (ih s)
  | proj h ih =>
    unfold Expr.lowerLooseBVars'; split
    · exact .proj h
    · exact .proj (ih s)

/-- Substituting a shaped term for a bound variable preserves shape. -/
theorem instantiate1' {e a : Expr} (H : ParamUniform heads params ls e)
    (ha : ParamUniform heads params ls a) (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv) (k : Nat) :
    ParamUniform heads params ls (e.instantiate1' a k) := by
  induction H generalizing k with
  | head hc =>
    rw [head_map (g := fun e => e.instantiate1' a k) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ => rfl) hp]
    exact .head hc
  | app _ _ ihf iha => exact .app (ihf k) (iha k)
  | const hc => exact .const hc
  | bvar i =>
    simp only [Expr.instantiate1']
    split
    · exact .bvar _
    · split
      · exact ha.liftLooseBVars' hp 0 k
      · exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | lit => exact .lit _
  | lam _ _ iht ihb => exact .lam (iht k) (ihb (k + 1))
  | forallE _ _ iht ihb => exact .forallE (iht k) (ihb (k + 1))
  | letE _ _ _ iht ihv ihb => exact .letE (iht k) (ihv k) (ihb (k + 1))
  | mdata _ ih => exact .mdata (ih k)
  | proj _ ih => exact .proj (ih k)

theorem instantiate1 {e a : Expr} (H : ParamUniform heads params ls e)
    (ha : ParamUniform heads params ls a) (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv) :
    ParamUniform heads params ls (e.instantiate1 a) := by
  rw [Expr.instantiate1_eq]; exact H.instantiate1' ha hp 0

theorem instantiateList {e : Expr} {subst : List Expr} (H : ParamUniform heads params ls e)
    (hs : ∀ a ∈ subst, ParamUniform heads params ls a) (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv)
    (k : Nat) : ParamUniform heads params ls (e.instantiateList subst k) := by
  induction subst generalizing e with
  | nil => exact H
  | cons a subst ih =>
    exact ih (H.instantiate1' (hs a (.head _)) hp k) fun b hb => hs b (.tail _ hb)

theorem instantiateRevList {e : Expr} {subst : List Expr} (H : ParamUniform heads params ls e)
    (hs : ∀ a ∈ subst, ParamUniform heads params ls a) (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv)
    (k : Nat) : ParamUniform heads params ls (e.instantiateRevList subst k) := by
  rw [← Expr.instantiateList_reverse]
  exact H.instantiateList (fun a ha => hs a (List.mem_reverse.1 ha)) hp k

/-! ### Changing the head set -/

/-! ### Abstraction -/

private theorem lastRevIdx?_getElem {xs : List FVarId} (hnd : xs.Nodup) {i : Nat}
    (hi : i < xs.length) : lastRevIdx? xs[i] xs = some (xs.length - 1 - i) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    obtain ⟨ha, hnd⟩ := List.nodup_cons.1 hnd
    cases i with
    | zero =>
      simp [lastRevIdx?, lastRevIdx?_eq_none_of_not_mem ha]
    | succ i =>
      have hi' : i < as.length := by simpa using hi
      simp only [lastRevIdx?, List.getElem_cons_succ, ih hnd hi', List.length_cons]
      congr 1; omega

private theorem map_abstractN_fvars {xs : List FVarId} (hnd : xs.Nodup) (d : Nat) :
    (xs.map Expr.fvar).map (fun e => e.abstractN xs d) = paramBVars xs.length d := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.map_map, List.getElem_map, Function.comp_apply, paramBVars,
    List.getElem_range]
  have hi : i < xs.length := by simpa using h1
  simp [Expr.abstractN, lastRevIdx?_getElem hnd hi]

/-- Abstracting the (distinct) parameter fvars turns the free-variable form into the
bound-variable form at the same depth. -/
theorem abstractN_params {xs : List FVarId} {e : Expr}
    (H : ParamUniform heads (xs.map .fvar) ls e) (hnd : xs.Nodup) (d : Nat) :
    ParamUniformBV heads xs.length ls d (e.abstractN xs d) := by
  induction H generalizing d with
  | head hc =>
    rw [mkAppList_map (g := fun e => e.abstractN xs d) (fun _ _ => rfl),
      map_abstractN_fvars hnd]
    exact .head hc
  | app _ _ ihf iha => exact .app (ihf d) (iha d)
  | const hc => exact .const hc
  | bvar => exact .bvar _
  | fvar fv =>
    simp only [Expr.abstractN]; split
    · exact .bvar _
    · exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | lit => exact .lit _
  | lam _ _ iht ihb => exact .lam (iht d) (ihb (d + 1))
  | forallE _ _ iht ihb => exact .forallE (iht d) (ihb (d + 1))
  | letE _ _ _ iht ihv ihb => exact .letE (iht d) (ihv d) (ihb (d + 1))
  | mdata _ ih => exact .mdata (ih d)
  | proj _ ih => exact .proj (ih d)

/-- Abstracting fvars that are not parameters keeps the free-variable form. -/
theorem abstractN_of_disjoint {ys : List FVarId} {e : Expr} (H : ParamUniform heads params ls e)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv ∧ fv ∉ ys) (d : Nat) :
    ParamUniform heads params ls (e.abstractN ys d) := by
  induction H generalizing d with
  | head hc =>
    rw [mkAppList_map (g := fun e => e.abstractN ys d) (fun _ _ => rfl)]
    have : params.map (fun e => e.abstractN ys d) = params := by
      conv => rhs; rw [← List.map_id params]
      refine List.map_congr_left fun p hmem => ?_
      obtain ⟨fv, rfl, hfv⟩ := hp p hmem
      simp [Expr.abstractN, lastRevIdx?_eq_none_of_not_mem hfv]
    rw [this]; exact .head hc
  | app _ _ ihf iha => exact .app (ihf d) (iha d)
  | const hc => exact .const hc
  | bvar => exact .bvar _
  | fvar fv =>
    simp only [Expr.abstractN]; split
    · exact .bvar _
    · exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | lit => exact .lit _
  | lam _ _ iht ihb => exact .lam (iht d) (ihb (d + 1))
  | forallE _ _ iht ihb => exact .forallE (iht d) (ihb (d + 1))
  | letE _ _ _ iht ihv ihb => exact .letE (iht d) (ihv d) (ihb (d + 1))
  | mdata _ ih => exact .mdata (ih d)
  | proj _ ih => exact .proj (ih d)

end ParamUniform

/-! ### Opening the bound-variable form -/

namespace ParamUniformBV

variable {heads : List Name} {ls : List Level}

/-- Reverse-instantiating the parameter block at depth `d` with fvars (as `instantiateRev`
does at depth `0`) turns the bound-variable form into the free-variable form. -/
theorem instantiateRevList_fvars {fvs : List FVarId} {d : Nat} {e : Expr}
    (H : ParamUniformBV heads fvs.length ls d e) :
    ParamUniform heads (fvs.map .fvar) ls (e.instantiateRevList (fvs.map .fvar) d) := by
  have hp : ∀ p ∈ fvs.map Expr.fvar, ∃ fv, p = .fvar fv := by simp
  have hleaf : ∀ {e : Expr} {k : Nat}, e.looseBVarRange' = 0 →
      e.instantiateRevList (fvs.map .fvar) k = e :=
    fun h => Expr.instantiateRevList'_eq_self (by omega)
  induction H with
  | @head c d hc =>
    rw [mkAppList_map (g := fun e => e.instantiateRevList (fvs.map .fvar) d)
      (fun _ _ => Expr.instantiateRevList_app)]
    have : (paramBVars fvs.length d).map
        (fun e => e.instantiateRevList (fvs.map .fvar) d) = fvs.map .fvar := by
      refine List.ext_getElem (by simp) fun i h1 h2 => ?_
      have hi : i < fvs.length := by simpa using h1
      simp only [paramBVars, List.map_map, List.getElem_map, List.getElem_range,
        Function.comp_apply]
      exact Expr.instantiateRevList_bvar_fvars_getElem fvs i d hi
    simp only [this, hleaf (e := .const c ls) rfl]
    exact .head hc
  | app _ _ ihf iha => rw [Expr.instantiateRevList_app]; exact .app ihf iha
  | const hc => rw [hleaf rfl]; exact .const hc
  | bvar i =>
    refine (ParamUniform.bvar i).instantiateRevList (fun a ha => ?_) hp _
    obtain ⟨fv, rfl⟩ := hp a ha; exact .fvar _
  | fvar => rw [hleaf rfl]; exact .fvar _
  | mvar => rw [hleaf rfl]; exact .mvar _
  | sort => rw [hleaf rfl]; exact .sort _
  | lit => rw [hleaf rfl]; exact .lit _
  | lam _ _ iht ihb => rw [Expr.instantiateRevList_lam]; exact .lam iht ihb
  | forallE _ _ iht ihb => rw [Expr.instantiateRevList_forallE]; exact .forallE iht ihb
  | letE _ _ _ iht ihv ihb => rw [Expr.instantiateRevList_letE]; exact .letE iht ihv ihb
  | mdata _ ih => rw [Expr.instantiateRevList_mdata]; exact .mdata ih
  | proj _ ih => rw [Expr.instantiateRevList_proj]; exact .proj ih

end ParamUniformBV

/-! ### Parameter telescopes -/

/-- `ParamUniformTele heads nparams ls e`: `e` is a closed parameter telescope of `nparams`
`forallE`/`lam` binders around a body in bound-variable form at depth `0`. This is the shape of
a stored term (recursor type, rule right-hand side) that `restoreNested` restores. -/
def ParamUniformTele (heads : List Name) (nparams : Nat) (ls : List Level) (e : Expr) : Prop :=
  ∃ body, LeadingBinders nparams e body ∧ ParamUniformBV heads nparams ls 0 body

/-! ### Closing telescopes with `LocalContext.mkBinding` -/


/-- Closing the opened parameters (distinct `cdecl` fvars) with `LocalContext.mkBinding` turns
the free-variable form into a parameter telescope (`ParamUniformTele`). This is the step
`restoreNested` and the lowering pass perform with `lctx.mkForall As` / `lctx.mkLambda As`. -/
theorem ParamUniform.mkBinding_params {heads : List Name} {ls : List Level} {isLambda : Bool}
    {lctx : LocalContext} {xs : List FVarId} {b : Expr}
    (H : ParamUniform heads (xs.map .fvar) ls b) (hnd : xs.Nodup)
    (hx : ∀ x ∈ xs, ∃ i fv n ty bi kind, lctx.find? x = some (.cdecl i fv n ty bi kind)) :
    ParamUniformTele heads xs.length ls (lctx.mkBinding isLambda ⟨xs.map .fvar⟩ b) := by
  rw [LocalContext.mkBinding_eqN]
  exact ⟨_, .mkBindingListN hx b, H.abstractN_params hnd 0⟩

theorem ParamUniform.mkForall_params {heads : List Name} {ls : List Level}
    {lctx : LocalContext} {As : Array Expr} {xs : List FVarId} {b : Expr}
    (H : ParamUniform heads As.toList ls b) (hAs : As.toList = xs.map .fvar) (hnd : xs.Nodup)
    (hx : ∀ x ∈ xs, ∃ i fv n ty bi kind, lctx.find? x = some (.cdecl i fv n ty bi kind)) :
    ParamUniformTele heads As.size ls (lctx.mkForall As b) := by
  obtain ⟨As⟩ := As
  simp only at hAs; subst hAs
  simpa [LocalContext.mkForall] using ParamUniform.mkBinding_params (isLambda := false) H hnd hx

theorem ParamUniform.mkLambda_params {heads : List Name} {ls : List Level}
    {lctx : LocalContext} {As : Array Expr} {xs : List FVarId} {b : Expr}
    (H : ParamUniform heads As.toList ls b) (hAs : As.toList = xs.map .fvar) (hnd : xs.Nodup)
    (hx : ∀ x ∈ xs, ∃ i fv n ty bi kind, lctx.find? x = some (.cdecl i fv n ty bi kind)) :
    ParamUniformTele heads As.size ls (lctx.mkLambda As b) := by
  obtain ⟨As⟩ := As
  simp only at hAs; subst hAs
  simpa [LocalContext.mkLambda] using ParamUniform.mkBinding_params (isLambda := true) H hnd hx

end Lean.Expr

namespace Lean.LocalDecl

/-- The declaration's type (and, for a `let`, its value) are parameter-uniform in the free-variable form. -/
def ParamUniform (heads : List Name) (params : List Expr) (ls : List Level) : LocalDecl → Prop
  | .cdecl _ _ _ ty _ _ => ty.ParamUniform heads params ls
  | .ldecl _ _ _ ty val _ _ => ty.ParamUniform heads params ls ∧ val.ParamUniform heads params ls

end Lean.LocalDecl

namespace Lean.Expr

private theorem paramUniform_go_disjoint {heads : List Name} {params : List Expr} {ls : List Level}
    {isLambda : Bool} {lctx : LocalContext} :
    ∀ {l : List FVarId}, (∀ p ∈ params, ∃ fv, p = .fvar fv ∧ fv ∉ l) →
    (∀ x ∈ l, ∃ d, lctx.find? x = some d ∧ d.ParamUniform heads params ls) →
    ∀ {b}, ParamUniform heads params ls b →
      ParamUniform heads params ls (LocalContext.mkBindingListN.go isLambda lctx l b)
  | [], _, _, _, H => H
  | x :: l, hp, hx, b, H => by
    have hp' : ∀ p ∈ params, ∃ fv, p = .fvar fv ∧ fv ∉ l.reverse := fun p hp'' => by
      obtain ⟨fv, rfl, hfv⟩ := hp p hp''
      exact ⟨fv, rfl, fun h => hfv (.tail _ (List.mem_reverse.1 h))⟩
    have hpf : ∀ p ∈ params, ∃ fv, p = .fvar fv := fun p hp'' => by
      obtain ⟨fv, rfl, -⟩ := hp p hp''; exact ⟨fv, rfl⟩
    obtain ⟨d, hfind, hd⟩ := hx x (.head _)
    simp only [LocalContext.mkBindingListN.go]
    refine paramUniform_go_disjoint (fun p hp'' => ?_) (fun y hy => hx y (.tail _ hy)) ?_
    · obtain ⟨fv, rfl, hfv⟩ := hp p hp''
      exact ⟨fv, rfl, fun h => hfv (.tail _ h)⟩
    · cases d with
      | cdecl _ _ _ ty _ _ =>
        simp only [LocalContext.mkBindingList1N, hfind]
        have hty := (show ty.ParamUniform heads params ls from hd).abstractN_of_disjoint hp' 0
        cases isLambda
        · exact .forallE hty H
        · exact .lam hty H
      | ldecl _ _ _ ty val _ _ =>
        obtain ⟨hty, hval⟩ := (show ty.ParamUniform heads params ls ∧ val.ParamUniform heads params ls
          from hd)
        simp only [LocalContext.mkBindingList1N, hfind]
        split
        · exact .letE (hty.abstractN_of_disjoint hp' 0) (hval.abstractN_of_disjoint hp' 0) H
        · exact H.lowerLooseBVars' hpf 1 1

/-- Closing a telescope of non-parameter fvars `ys` (for example field or index variables)
keeps the free-variable form, given shaped declarations. -/
theorem ParamUniform.mkBindingListN_of_disjoint {heads : List Name} {params : List Expr}
    {ls : List Level} {isLambda : Bool} {lctx : LocalContext} {ys : List FVarId} {b : Expr}
    (H : ParamUniform heads params ls b) (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv ∧ fv ∉ ys)
    (hdecl : ∀ y ∈ ys, ∃ d, lctx.find? y = some d ∧ d.ParamUniform heads params ls) :
    ParamUniform heads params ls (LocalContext.mkBindingListN isLambda lctx ys b) := by
  simp only [LocalContext.mkBindingListN, LocalContext.mkBindingListN.core]
  refine paramUniform_go_disjoint (fun p hp' => ?_) (fun y hy => hdecl y (List.mem_reverse.1 hy))
    (H.abstractN_of_disjoint hp 0)
  obtain ⟨fv, rfl, hfv⟩ := hp p hp'
  exact ⟨fv, rfl, fun h => hfv (List.mem_reverse.1 h)⟩

theorem ParamUniform.mkBinding_of_disjoint {heads : List Name} {params : List Expr}
    {ls : List Level} {isLambda : Bool} {lctx : LocalContext} {ys : List FVarId} {b : Expr}
    (H : ParamUniform heads params ls b) (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv ∧ fv ∉ ys)
    (hdecl : ∀ y ∈ ys, ∃ d, lctx.find? y = some d ∧ d.ParamUniform heads params ls) :
    ParamUniform heads params ls (lctx.mkBinding isLambda ⟨ys.map .fvar⟩ b) := by
  rw [LocalContext.mkBinding_eqN]; exact H.mkBindingListN_of_disjoint hp hdecl

/-! ### Unfolding `Expr.replace`

`Expr.replace` is modelled by `Expr.replaceNoCache` (`Expr.replace_eq`). A callback returning `some` stops the
traversal; otherwise the node is rebuilt from its replaced children. The relational form is
`VerifyInductive.ExprReplacement` (`Lean4Lean/Verify/Inductive/Nested/Restoration/ExprReplace.lean`). -/

theorem replace_of_some {f : Expr → Option Expr} {e r : Expr} (h : f e = some r) :
    e.replace f = r := by
  rw [replace_eq]; cases e <;> simp [replaceNoCache, h]

theorem replace_app_of_none {f : Expr → Option Expr} {fn arg : Expr}
    (h : f (.app fn arg) = none) :
    (Expr.app fn arg).replace f = .app (fn.replace f) (arg.replace f) := by
  simp [replace_eq, replaceNoCache, h, updateApp!]

theorem replace_lam_of_none {f : Expr → Option Expr} {n : Name} {t b : Expr} {bi : BinderInfo}
    (h : f (.lam n t b bi) = none) :
    (Expr.lam n t b bi).replace f = .lam n (t.replace f) (b.replace f) bi := by
  simp [replace_eq, replaceNoCache, h, updateLambdaE!, updateLambda!]

theorem replace_forallE_of_none {f : Expr → Option Expr} {n : Name} {t b : Expr}
    {bi : BinderInfo} (h : f (.forallE n t b bi) = none) :
    (Expr.forallE n t b bi).replace f = .forallE n (t.replace f) (b.replace f) bi := by
  simp [replace_eq, replaceNoCache, h, updateForallE!, updateForall!]

theorem replace_letE_of_none {f : Expr → Option Expr} {n : Name} {t v b : Expr} {nd : Bool}
    (h : f (.letE n t v b nd) = none) :
    (Expr.letE n t v b nd).replace f = .letE n (t.replace f) (v.replace f) (b.replace f) nd := by
  simp [replace_eq, replaceNoCache, h, updateLetE!]

theorem replace_mdata_of_none {f : Expr → Option Expr} {m : MData} {e : Expr}
    (h : f (.mdata m e) = none) : (Expr.mdata m e).replace f = .mdata m (e.replace f) := by
  simp [replace_eq, replaceNoCache, h, updateMData!]

theorem replace_proj_of_none {f : Expr → Option Expr} {s : Name} {i : Nat} {e : Expr}
    (h : f (.proj s i e) = none) : (Expr.proj s i e).replace f = .proj s i (e.replace f) := by
  simp [replace_eq, replaceNoCache, h, updateProj!]

theorem replace_bvar_of_none {f : Expr → Option Expr} {i : Nat} (h : f (.bvar i) = none) :
    (Expr.bvar i).replace f = .bvar i := by simp [replace_eq, replaceNoCache, h]

theorem replace_fvar_of_none {f : Expr → Option Expr} {fv : FVarId} (h : f (.fvar fv) = none) :
    (Expr.fvar fv).replace f = .fvar fv := by simp [replace_eq, replaceNoCache, h]

theorem replace_sort_of_none {f : Expr → Option Expr} {u : Level} (h : f (.sort u) = none) :
    (Expr.sort u).replace f = .sort u := by simp [replace_eq, replaceNoCache, h]

theorem replace_const_of_none {f : Expr → Option Expr} {c : Name} {us : List Level}
    (h : f (.const c us) = none) : (Expr.const c us).replace f = .const c us := by
  simp [replace_eq, replaceNoCache, h]

theorem replace_lit_of_none {f : Expr → Option Expr} {l : Literal} (h : f (.lit l) = none) :
    (Expr.lit l).replace f = .lit l := by simp [replace_eq, replaceNoCache, h]

end Lean.Expr
