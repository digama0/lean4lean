import Lean4Lean.Verify.Inductive.Nested.Restoration.RecursorRenaming
import Lean4Lean.Verify.Inductive.Nested.Restoration.TranslationPreservation

/-! # Input-side avoidance of the auxiliary constructor names by the lowered rules

The restored-equation lemma modulo the renamed auxiliary recursor names
(`restoredEquations_of_trModulo`, `Nested/Restoration/RecursorRenaming.lean`) needs the
premise `NestedRun.LoweredRulesAvoid heads X`: in the lowered
rule right-hand sides, the trailing arguments of the head occurrences, the literals and the
parameter domains avoid `X`. Only the restorable names of `X` matter
(`TrRestoredRulesModulo.filter_restorable`), and those are auxiliary
constructor names (`restorableRenamed_auxCtorNames`: lowered auxiliary recursor
names are never renamed, and auxiliary family names are numeric `_nested.i`
while renamed names are string extensions `Main.rec_k`).

`NestedRun.loweredRulesAvoid_auxCtorNames` proves the avoidance
of all auxiliary constructor names from the run alone. Auxiliary constructors do
occur in the lowered rules, as the constructor applications `c params fields`
of the minor premises, so complete avoidance is false; the argument is:

* `envParamUniform_auxCtorNames`, `whnfPreservesParamUniform_auxCtorNames`: the type checker's
  parameter-uniformity invariant (`TypeChecker.whnf.paramUniform`) instantiated at the head
  set `E.auxCtorNames`, without parameters, at the level list `foreignLevels
  lparams` of length `lparams.length + 1`. `Expr.ParamUniform names [] ls e` says
  that every occurrence of `names` in `e` carries the levels `ls`. Every
  constant of the recursor-pass environment has a type avoiding the auxiliary
  constructor names, so the environment condition holds at any level list.
* `RecursorConstruction.ruleRhsTrail`: the trailing-argument chain
  (the counterpart of `ruleRhsParamUniform`) for the predicate
  `Expr.TrailingArgs heads np (Expr.ParamUniform names [] ls)`: the `whnf` regions
  R1 to R3, the constructor field domains, the motives, the major premises and
  the recursive calls mention `names` only at `ls`; the minors' constructor
  applications are head occurrences whose trailing arguments are field variables. The
  parameter domains avoid `names`.
* `TrailingArgs.toTrailingArgsAvoid`: the parameter-uniformity chain at the declaration's
  levels (`recursorParamUniform_uniformHeads`) says that every occurrence of an
  auxiliary constructor is at `lparams.map Level.param`; at the trailing
  positions occurrences are also at `foreignLevels lparams`, which differs, so
  there are none.
-/

namespace Lean.Expr

open Lean4Lean

/-! ### Trailing-argument conditions at head occurrences -/

namespace TrailingArgs

variable {heads : List Name} {np : Nat} {Q : Expr → Prop}

/-- Spine arguments inherit `TrailingArgs`. -/
theorem of_mem_getAppArgsList {e : Expr} (H : TrailingArgs heads np Q e) :
    ∀ a ∈ e.getAppArgsList, TrailingArgs heads np Q a := by
  induction e with
  | app f a ihf _ =>
    cases H with
    | app hf ha _ =>
      intro x hx
      rw [getAppArgsList_app] at hx
      rcases List.mem_append.1 hx with hx | hx
      · exact ihf hf x hx
      · rw [List.mem_singleton.1 hx]; exact ha
  | _ => intro x hx; simp [getAppArgsList] at hx

/-- `consumeTypeAnnotationsVerified` returns a subterm reached through application
arguments, so it preserves `TrailingArgs`. -/
theorem consumeTypeAnnotationsVerified {e : Expr} (H : TrailingArgs heads np Q e) :
    TrailingArgs heads np Q (e.consumeTypeAnnotationsVerified annOk) := by
  fun_induction Expr.consumeTypeAnnotationsVerified _ e
  case case1 name us type v _ ih =>
    exact ih (H.of_mem_getAppArgsList type (by simp [getAppArgsList]))
  case case2 => exact H
  case case3 name us type _ ih =>
    exact ih (H.of_mem_getAppArgsList type (by simp [getAppArgsList]))
  case case4 => exact H
  case case5 => exact H

/-- An application whose function is not headed by a constant (a variable, say). -/
theorem app_of_not_const {f a : Expr} (hf : TrailingArgs heads np Q f)
    (ha : TrailingArgs heads np Q a) (hfn : ∀ c us, f.getAppFn ≠ .const c us) :
    TrailingArgs heads np Q (.app f a) :=
  .app hf ha fun c us h _ => absurd h (hfn c us)

/-- A spine with a `TrailingArgs` head whose arguments all satisfy `Q` and
`TrailingArgs`, and whose head arguments satisfy `Q` when its head is a constant. -/
theorem mkAppList_of_args {f : Expr} {args : List Expr} (hf : TrailingArgs heads np Q f)
    (hfargs : ∀ c us, f.getAppFn = .const c us → ∀ x ∈ f.getAppArgsList, Q x)
    (hargs : ∀ a ∈ args, TrailingArgs heads np Q a ∧ Q a) :
    TrailingArgs heads np Q (f.mkAppList args) := by
  induction args generalizing f with
  | nil => exact hf
  | cons a rest ih =>
    simp only [mkAppList]
    refine ih ?_ ?_ fun x hx => hargs x (.tail _ hx)
    · refine .app hf (hargs a (.head _)).1 fun c us hfn _ x hx => ?_
      rw [getAppArgsList_app] at hx
      rcases List.mem_append.1 (List.mem_of_mem_drop hx) with hx | hx
      · exact hfargs c us hfn x hx
      · rw [List.mem_singleton.1 hx]; exact (hargs a (.head _)).2
    · intro c us hfn x hx
      rw [getAppArgsList_app] at hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hfargs c us hfn x hx
      · rw [List.mem_singleton.1 hx]; exact (hargs a (.head _)).2

/-- A constant applied to arguments that all satisfy `Q` and `TrailingArgs`. -/
theorem const_mkAppList {c : Name} {us : List Level} {args : List Expr}
    (hargs : ∀ a ∈ args, TrailingArgs heads np Q a ∧ Q a) :
    TrailingArgs heads np Q ((Expr.const c us).mkAppList args) :=
  mkAppList_of_args (.const _ _) (fun _ _ _ x hx => by simp [getAppArgsList] at hx) hargs

/-! #### Abstraction -/

private theorem abstractN_fvar_cases (xs : List FVarId) (v : FVarId) (d : Nat) :
    (∃ j, abstractN xs (.fvar v) d = .bvar j) ∨ abstractN xs (.fvar v) d = .fvar v := by
  simp only [abstractN]
  split
  · exact .inl ⟨_, rfl⟩
  · exact .inr rfl

theorem getAppFn_abstractN (xs : List FVarId) :
    ∀ (e : Expr) (d : Nat), (abstractN xs e d).getAppFn = abstractN xs e.getAppFn d
  | .app f _, d => by
    simp only [abstractN, getAppFn]
    exact getAppFn_abstractN xs f d
  | .fvar v, d => by
    rcases abstractN_fvar_cases xs v d with ⟨j, h⟩ | h <;> simp [getAppFn, h]
  | .bvar _, _ | .mvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .lam .., _ | .forallE .., _ | .letE .., _ | .mdata .., _ | .proj .., _ => rfl

theorem getAppArgsList_abstractN (xs : List FVarId) :
    ∀ (e : Expr) (d : Nat),
      (abstractN xs e d).getAppArgsList = e.getAppArgsList.map (abstractN xs · d)
  | .app f a, d => by
    simp only [abstractN, getAppArgsList_app, List.map_append, List.map_cons, List.map_nil]
    rw [getAppArgsList_abstractN xs f d]
  | .fvar v, d => by
    rcases abstractN_fvar_cases xs v d with ⟨j, h⟩ | h <;> simp [getAppArgsList, h]
  | .bvar _, _ | .mvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .lam .., _ | .forallE .., _ | .letE .., _ | .mdata .., _ | .proj .., _ => rfl

theorem eq_const_of_abstractN {xs : List FVarId} {d : Nat} {c : Name} {us : List Level} :
    ∀ {x : Expr}, abstractN xs x d = .const c us → x = .const c us
  | .fvar v, h => by
    rcases abstractN_fvar_cases xs v d with ⟨j, h'⟩ | h' <;> rw [h'] at h <;> cases h
  | .const _ _, h => h
  | .bvar _, h | .mvar _, h | .sort _, h | .lit _, h => by cases h
  | .app .., h | .lam .., h | .forallE .., h | .letE .., h | .mdata .., h | .proj .., h => by
    simp [abstractN] at h

/-- Abstraction preserves `TrailingArgs` when it preserves `Q`. -/
theorem abstractN {xs : List FVarId} {e : Expr} (H : TrailingArgs heads np Q e)
    (hQ : ∀ x d, Q x → Q (x.abstractN xs d)) (d : Nat) :
    TrailingArgs heads np Q (e.abstractN xs d) := by
  induction H generalizing d with
  | bvar => exact .bvar _
  | fvar v =>
    rcases abstractN_fvar_cases xs v d with ⟨j, h⟩ | h <;> rw [h]
    · exact .bvar _
    · exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | const => exact .const _ _
  | lit => exact .lit _
  | @app f a _ _ htrail ihf iha =>
    refine .app (ihf d) (iha d) ?_
    intro c us hfn hc x hx
    have hfn' : (Expr.app f a).getAppFn = .const c us := by
      have h := getAppFn_abstractN xs (.app f a) d
      simp only [Expr.abstractN] at h
      rw [h] at hfn
      exact eq_const_of_abstractN hfn
    have hargs := getAppArgsList_abstractN xs (.app f a) d
    simp only [Expr.abstractN] at hargs
    rw [hargs, ← List.map_drop] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hQ y d (htrail c us hfn' hc y hy)
  | lam _ _ ihd ihb => exact .lam (ihd d) (ihb (d + 1))
  | forallE _ _ ihd ihb => exact .forallE (ihd d) (ihb (d + 1))
  | letE _ _ _ iht ihv ihb => exact .letE (iht d) (ihv d) (ihb (d + 1))
  | mdata _ ih => exact .mdata (ih d)
  | proj _ ih => exact .proj (ih d)

private theorem go_cdecls {isLambda : Bool} {lctx : LocalContext}
    (hQ : ∀ (ys : List FVarId) x d, Q x → Q (x.abstractN ys d)) :
    ∀ {l : List FVarId}, (∀ x ∈ l, ∃ i fv n ty bi kind,
      lctx.find? x = some (.cdecl i fv n ty bi kind) ∧ TrailingArgs heads np Q ty) →
    ∀ {b}, TrailingArgs heads np Q b →
      TrailingArgs heads np Q (LocalContext.mkBindingListN.go isLambda lctx l b)
  | [], _, _, H => H
  | x :: l, hx, b, H => by
    obtain ⟨i, fv, n, ty, bi, kind, hfind, hty⟩ := hx x (.head _)
    simp only [LocalContext.mkBindingListN.go]
    refine go_cdecls hQ (fun y hy => hx y (.tail _ hy)) ?_
    simp only [LocalContext.mkBindingList1N, hfind]
    have hty' := hty.abstractN (hQ l.reverse) 0
    cases isLambda
    · exact .forallE hty' H
    · exact .lam hty' H

/-- Closing a telescope of `cdecl` variables with `TrailingArgs` types. -/
theorem mkBinding {isLambda : Bool} {lctx : LocalContext} {ys : List FVarId} {b : Expr}
    (H : TrailingArgs heads np Q b) (hQ : ∀ (ys : List FVarId) x d, Q x → Q (x.abstractN ys d))
    (hdecl : ∀ y ∈ ys, ∃ i fv n ty bi kind,
      lctx.find? y = some (.cdecl i fv n ty bi kind) ∧ TrailingArgs heads np Q ty) :
    TrailingArgs heads np Q (lctx.mkBinding isLambda ⟨ys.map .fvar⟩ b) := by
  rw [LocalContext.mkBinding_eqN]
  simp only [LocalContext.mkBindingListN, LocalContext.mkBindingListN.core]
  exact go_cdecls hQ (fun y hy => hdecl y (List.mem_reverse.1 hy)) (H.abstractN (hQ ys) 0)

/-- `mkBinding` over `cdecl` variables, with the type condition read off any
declaration of the variables. -/
theorem mkBinding' {isLambda : Bool} {lctx : LocalContext} {ys : List FVarId} {b : Expr}
    (H : TrailingArgs heads np Q b) (hQ : ∀ (ys : List FVarId) x d, Q x → Q (x.abstractN ys d))
    (hcdecl : ∀ y ∈ ys, ∃ i fv n ty bi kind, lctx.find? y = some (.cdecl i fv n ty bi kind))
    (hty : ∀ y ∈ ys, ∀ d, lctx.find? y = some d → TrailingArgs heads np Q d.type) :
    TrailingArgs heads np Q (lctx.mkBinding isLambda ⟨ys.map .fvar⟩ b) := by
  refine mkBinding H hQ fun y hy => ?_
  obtain ⟨i, fv, n, ty, bi, kind, hfind⟩ := hcdecl y hy
  exact ⟨i, fv, n, ty, bi, kind, hfind, hty y hy _ hfind⟩

theorem mkForall' {lctx : LocalContext} {xs : Array Expr} {ys : List FVarId} {b : Expr}
    (hxs : xs = (ys.map Expr.fvar).toArray)
    (H : TrailingArgs heads np Q b) (hQ : ∀ (ys : List FVarId) x d, Q x → Q (x.abstractN ys d))
    (hcdecl : ∀ y ∈ ys, ∃ i fv n ty bi kind, lctx.find? y = some (.cdecl i fv n ty bi kind))
    (hty : ∀ y ∈ ys, ∀ d, lctx.find? y = some d → TrailingArgs heads np Q d.type) :
    TrailingArgs heads np Q (lctx.mkForall xs b) := by
  subst hxs
  simpa [LocalContext.mkForall] using mkBinding' (isLambda := false) H hQ hcdecl hty

theorem mkLambda' {lctx : LocalContext} {xs : Array Expr} {ys : List FVarId} {b : Expr}
    (hxs : xs = (ys.map Expr.fvar).toArray)
    (H : TrailingArgs heads np Q b) (hQ : ∀ (ys : List FVarId) x d, Q x → Q (x.abstractN ys d))
    (hcdecl : ∀ y ∈ ys, ∃ i fv n ty bi kind, lctx.find? y = some (.cdecl i fv n ty bi kind))
    (hty : ∀ y ∈ ys, ∀ d, lctx.find? y = some d → TrailingArgs heads np Q d.type) :
    TrailingArgs heads np Q (lctx.mkLambda xs b) := by
  subst hxs
  simpa [LocalContext.mkLambda] using mkBinding' (isLambda := true) H hQ hcdecl hty

end TrailingArgs

end Lean.Expr

namespace Lean.Expr

open Lean4Lean

/-! ### Parameter uniformity without parameters

`ParamUniform names [] ls e` says that every occurrence of a constant of `names` in
`e` carries the levels `ls`. Two such facts at different level lists exclude
the names altogether. -/

namespace ParamUniform

variable {heads : List Name} {ls : List Level}

theorem app_inv_nil {f a : Expr} (H : ParamUniform heads [] ls (.app f a)) :
    ParamUniform heads [] ls f ∧ ParamUniform heads [] ls a := by
  generalize he : Expr.app f a = e at H
  cases H with
  | app hf ha => cases he; exact ⟨hf, ha⟩
  | head => simp at he
  | _ => cases he

/-- Forgetting the parameters of the head occurrences. -/
theorem params_nil {params : List Expr} {e : Expr} (H : ParamUniform heads params ls e)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv) : ParamUniform heads [] ls e := by
  induction H with
  | head hc =>
    refine ParamUniform.mkAppList (by simpa [mkAppList] using (ParamUniform.head hc :
      ParamUniform heads [] ls ((Expr.const _ ls).mkAppList []))) fun p hpm => ?_
    obtain ⟨fv, rfl⟩ := hp p hpm
    exact .fvar _
  | app _ _ ihf iha => exact .app ihf iha
  | const hc => exact .const hc
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | lit => exact .lit _
  | lam _ _ iht ihb => exact .lam iht ihb
  | forallE _ _ iht ihb => exact .forallE iht ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

/-- Shrinking the head set of a parameterless uniform form. -/
theorem nil_mono {names : List Name} {e : Expr} (H : ParamUniform heads [] ls e)
    (hsub : ∀ n ∈ names, n ∈ heads) : ParamUniform names [] ls e := by
  induction H with
  | @head c hc =>
    by_cases hcn : c ∈ names
    · exact .head hcn
    · simpa [mkAppList] using (ParamUniform.const hcn : ParamUniform names [] ls (.const c ls))
  | app _ _ ihf iha => exact .app ihf iha
  | const hc => exact .const fun h => hc (hsub _ h)
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | lit => exact .lit _
  | lam _ _ iht ihb => exact .lam iht ihb
  | forallE _ _ iht ihb => exact .forallE iht ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

/-- Abstraction preserves a parameterless uniform form. -/
theorem nil_abstractN {e : Expr} (H : ParamUniform heads [] ls e) (ys : List FVarId) (d : Nat) :
    ParamUniform heads [] ls (e.abstractN ys d) :=
  H.abstractN_of_disjoint (by simp) d

/-- Two parameterless uniform forms at different levels exclude the heads. -/
theorem avoids_of_two {ls' : List Level} {e : Expr} (H : ParamUniform heads [] ls e)
    (H' : ParamUniform heads [] ls' e) (hne : ls ≠ ls')
    (hlit : ∀ l : Literal, (Expr.lit l).AvoidsConsts heads) : e.AvoidsConsts heads := by
  induction H with
  | @head c hc =>
    simp only [Expr.mkAppList] at H' ⊢
    rcases H'.const_inv with h | ⟨-, h, -⟩
    · exact absurd hc h
    · exact absurd h hne
  | app _ _ ihf iha =>
    obtain ⟨hf, ha⟩ := H'.app_inv_nil
    exact .app _ _ (ihf hf) (iha ha)
  | const hc => exact .const _ _ hc
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | lit => exact hlit _
  | lam _ _ iht ihb =>
    obtain ⟨ht, hb⟩ := H'.lam_inv
    exact .lam _ _ _ _ (iht ht) (ihb hb)
  | forallE _ _ iht ihb =>
    obtain ⟨ht, hb⟩ := H'.forallE_inv
    exact .forallE _ _ _ _ (iht ht) (ihb hb)
  | letE _ _ _ iht ihv ihb =>
    obtain ⟨ht, hv, hb⟩ := H'.letE_inv
    exact .letE _ _ _ _ _ (iht ht) (ihv hv) (ihb hb)
  | mdata _ ih => exact .mdata _ _ (ih H'.mdata_inv)
  | proj _ ih => exact .proj _ _ _ (ih H'.proj_inv)

end ParamUniform

/-- The bound-variable form forgets to a parameterless uniform form. -/
theorem ParamUniformBV.toNil {heads : List Name} {n : Nat} {ls : List Level} {d : Nat} {e : Expr}
    (H : ParamUniformBV heads n ls d e) : ParamUniform heads [] ls e := by
  induction H with
  | head hc =>
    refine ParamUniform.mkAppList (by simpa [mkAppList] using (ParamUniform.head hc :
      ParamUniform heads [] ls ((Expr.const _ ls).mkAppList []))) fun p hpm => ?_
    simp only [paramBVars, List.mem_map] at hpm
    obtain ⟨_, -, rfl⟩ := hpm
    exact .bvar _
  | app _ _ ihf iha => exact .app ihf iha
  | const hc => exact .const hc
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | lit => exact .lit _
  | lam _ _ iht ihb => exact .lam iht ihb
  | forallE _ _ iht ihb => exact .forallE iht ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

namespace TrailingArgs

variable {heads names : List Name} {np : Nat} {ls : List Level}

/-- A parameterless uniform form holds hereditarily, so in particular at trailing
arguments. -/
theorem of_paramUniform_nil {e : Expr} (H : ParamUniform names [] ls e) :
    TrailingArgs heads np (ParamUniform names [] ls) e := by
  induction e with
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | const => exact .const _ _
  | lit => exact .lit _
  | app f a ihf iha =>
    obtain ⟨hf, ha⟩ := H.app_inv_nil
    exact .app (ihf hf) (iha ha) fun _ _ _ _ x hx =>
      H.of_mem_getAppArgsList (by simp) (List.mem_of_mem_drop hx)
  | lam _ _ _ _ iht ihb => exact .lam (iht H.lam_inv.1) (ihb H.lam_inv.2)
  | forallE _ _ _ _ iht ihb => exact .forallE (iht H.forallE_inv.1) (ihb H.forallE_inv.2)
  | letE _ _ _ _ _ iht ihv ihb =>
    exact .letE (iht H.letE_inv.1) (ihv H.letE_inv.2.1) (ihb H.letE_inv.2.2)
  | mdata _ _ ih => exact .mdata (ih H.mdata_inv)
  | proj _ _ _ ih => exact .proj (ih H.proj_inv)

/-- **From trailing parameter uniformity at impossible levels to trailing avoidance.** If
the trailing arguments of the head occurrences of `e` mention `names` only at the levels
`ls`, while `e` mentions `names` only at the levels `ls' ≠ ls`, then the
trailing arguments avoid `names`, hence every `X ⊆ names`. -/
theorem toTrailingArgsAvoid {ls' : List Level} {X : List Name} {e : Expr}
    (H : TrailingArgs heads np (ParamUniform names [] ls) e) (H' : ParamUniform names [] ls' e)
    (hne : ls ≠ ls') (hX : ∀ n ∈ X, n ∈ names)
    (hlit : ∀ l : Literal, (Expr.lit l).AvoidsConsts names) :
    e.TrailingArgsAvoid heads X np := by
  induction H with
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | const => exact .const _ _
  | lit l => exact .lit _ ((hlit l).mono hX)
  | @app f a _ _ htrail ihf iha =>
    obtain ⟨hf, ha⟩ := H'.app_inv_nil
    refine .app (ihf hf) (iha ha) fun c us hfn hc x hx => ?_
    have hx' := H'.of_mem_getAppArgsList (by simp) (List.mem_of_mem_drop hx)
    exact ((htrail c us hfn hc x hx).avoids_of_two hx' hne hlit).mono hX
  | lam _ _ iht ihb => exact .lam (iht H'.lam_inv.1) (ihb H'.lam_inv.2)
  | forallE _ _ iht ihb => exact .forallE (iht H'.forallE_inv.1) (ihb H'.forallE_inv.2)
  | letE _ _ _ iht ihv ihb =>
    exact .letE (iht H'.letE_inv.1) (ihv H'.letE_inv.2.1) (ihb H'.letE_inv.2.2)
  | mdata _ ih => exact .mdata (ih H'.mdata_inv)
  | proj _ ih => exact .proj (ih H'.proj_inv)

end TrailingArgs

/-! ### Lambda prefixes -/

private theorem lamPrefix_go {names : List Name} {lctx : LocalContext} :
    ∀ {l : List FVarId}, (∀ x ∈ l, ∃ i fv n ty bi kind,
      lctx.find? x = some (.cdecl i fv n ty bi kind) ∧ ty.AvoidsConsts names) →
    ∀ {k b}, LamPrefixAvoids names k b →
      LamPrefixAvoids names (k + l.length) (LocalContext.mkBindingListN.go true lctx l b)
  | [], _, _, _, H => H
  | x :: l, hx, k, b, H => by
    obtain ⟨i, fv, n, ty, bi, kind, hfind, hty⟩ := hx x (.head _)
    simp only [LocalContext.mkBindingListN.go]
    have := lamPrefix_go (l := l) (fun y hy => hx y (.tail _ hy)) (k := k + 1)
      (b := LocalContext.mkBindingList1N true lctx l.reverse x b) (by
        simp only [LocalContext.mkBindingList1N, hfind, if_true]
        exact .succ (hty.abstractN _ 0) H)
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

/-- Closing `cdecl` variables whose types avoid `names` with `mkLambda` gives a
lambda prefix avoiding `names`. -/
theorem LamPrefixAvoids.mkLambda {names : List Name} {lctx : LocalContext}
    {ys : List FVarId} (b : Expr)
    (hdecl : ∀ y ∈ ys, ∃ i fv n ty bi kind,
      lctx.find? y = some (.cdecl i fv n ty bi kind) ∧ ty.AvoidsConsts names) :
    LamPrefixAvoids names ys.length (lctx.mkLambda ⟨ys.map .fvar⟩ b) := by
  simp only [LocalContext.mkLambda]
  rw [LocalContext.mkBinding_eqN]
  simp only [LocalContext.mkBindingListN, LocalContext.mkBindingListN.core]
  simpa using lamPrefix_go (l := ys.reverse) (fun y hy => hdecl y (List.mem_reverse.1 hy))
    (LamPrefixAvoids.zero (b.abstractN ys))

end Lean.Expr

namespace Lean.Expr

theorem LeadingBinders.avoidsConsts {names : List Name} {k : Nat} {e body : Expr}
    (H : LeadingBinders k e body) (h : e.AvoidsConsts names) : body.AvoidsConsts names := by
  induction H with
  | zero => exact h
  | forallE _ ih => cases h; exact ih ‹_›
  | lam _ ih => cases h; exact ih ‹_›

end Lean.Expr

namespace Lean.Expr

open Lean4Lean

/-! ### Instantiating a recursive-call template -/

/-- `ArgClosed k e`: the loose bound variables `≥ k` of `e` occur only as the
heads of application spines reached through lambda bodies and application
functions. A recursive-call template `fun ys => #n is (f ys)` is `ArgClosed 0`
when its binder domains and `is` are closed, so instantiating its placeholder
puts the recursor only at the head of the call spine. -/
inductive ArgClosed : Nat → Expr → Prop
  | bvar (k i : Nat) : ArgClosed k (.bvar i)
  | closed {k : Nat} {e : Expr} : e.looseBVarRange' ≤ k → ArgClosed k e
  | app {k : Nat} {f a : Expr} : ArgClosed k f → a.looseBVarRange' ≤ k →
      ArgClosed k (.app f a)
  | lam {k : Nat} {n : Name} {t b : Expr} {bi : BinderInfo} :
      t.looseBVarRange' ≤ k → ArgClosed (k + 1) b → ArgClosed k (.lam n t b bi)

theorem looseBVarRange_le_of_mem_getAppArgsList :
    ∀ {e x : Expr}, x ∈ e.getAppArgsList → x.looseBVarRange' ≤ e.looseBVarRange'
  | .app f a, x, hx => by
    rw [getAppArgsList_app] at hx
    simp only [Expr.looseBVarRange']
    rcases List.mem_append.1 hx with hx | hx
    · have := looseBVarRange_le_of_mem_getAppArgsList hx; omega
    · rw [List.mem_singleton.1 hx]; omega
  | .bvar _, _, hx | .fvar _, _, hx | .mvar _, _, hx | .sort _, _, hx | .const _ _, _, hx
  | .lit _, _, hx | .lam .., _, hx | .forallE .., _, hx | .letE .., _, hx
  | .mdata .., _, hx | .proj .., _, hx => by simp [getAppArgsList] at hx

/-- A spine with a bound-variable head and arguments below `k`. -/
theorem ArgClosed.mkAppList_bvar {k i : Nat} :
    ∀ {args : List Expr}, (∀ a ∈ args, a.looseBVarRange' ≤ k) →
      ∀ {f : Expr}, ArgClosed k f → ArgClosed k (mkAppList f args)
  | [], _, _, hf => hf
  | a :: args, h, _, hf => by
    simp only [mkAppList]
    exact mkAppList_bvar (k := k) (i := i) (fun x hx => h x (.tail _ hx))
      (.app hf (h a (.head _)))

private theorem argClosed_go {lctx : LocalContext} :
    ∀ {l : List FVarId}, (∀ x ∈ l, ∃ i fv n ty bi kind,
      lctx.find? x = some (.cdecl i fv n ty bi kind) ∧ ty.looseBVarRange' = 0) →
    ∀ {b}, ArgClosed l.length b →
      ArgClosed 0 (LocalContext.mkBindingListN.go true lctx l b)
  | [], _, _, H => H
  | x :: l, hx, b, H => by
    obtain ⟨i, fv, n, ty, bi, kind, hfind, hty⟩ := hx x (.head _)
    simp only [LocalContext.mkBindingListN.go]
    refine argClosed_go (fun y hy => hx y (.tail _ hy)) ?_
    simp only [LocalContext.mkBindingList1N, hfind, if_true]
    refine .lam ?_ H
    have := Lean4Lean.VerifyInductive.Expr.abstractN_looseBVarRange_le (e := ty)
      (fvs := l.reverse) (k := 0)
    simp only [hty, Nat.max_self, Nat.zero_add, List.length_reverse] at this
    exact this

/-- Closing `cdecl` variables with closed types around a body that is
`ArgClosed` at the telescope length after abstraction. -/
theorem ArgClosed.mkLambda {lctx : LocalContext} {ys : List FVarId} {b : Expr}
    (hdecl : ∀ y ∈ ys, ∃ i fv n ty bi kind,
      lctx.find? y = some (.cdecl i fv n ty bi kind) ∧ ty.looseBVarRange' = 0)
    (H : ArgClosed ys.length (b.abstractN ys)) :
    ArgClosed 0 (lctx.mkLambda ⟨ys.map .fvar⟩ b) := by
  simp only [LocalContext.mkLambda]
  rw [LocalContext.mkBinding_eqN]
  simp only [LocalContext.mkBindingListN, LocalContext.mkBindingListN.core]
  exact argClosed_go (fun y hy => hdecl y (List.mem_reverse.1 hy)) (by simpa using H)

private theorem abstractN_mkAppList_eq (fn : Expr) (args : List Expr) (xs : List FVarId)
    (k : Nat) :
    (mkAppList fn args).abstractN xs k =
      mkAppList (fn.abstractN xs k) (args.map fun a => a.abstractN xs k) := by
  induction args generalizing fn with
  | nil => rfl
  | cons a l ih => simp only [mkAppList, ih, List.map_cons]; rfl

/-- The body `#n is (f ys)` of a recursive-call template is `ArgClosed n`
after abstracting `ys`, when `is`, `f` and `ys` are closed. -/
theorem ArgClosed.callBody {ys : List FVarId} {idx args : List Expr} {f : Expr}
    (hidx : ∀ a ∈ idx, a.looseBVarRange' = 0) (hf : f.looseBVarRange' = 0)
    (hargs : ∀ a ∈ args, a.looseBVarRange' = 0) :
    ArgClosed ys.length
      ((Expr.app (mkAppList (.bvar ys.length) idx) (mkAppList f args)).abstractN ys) := by
  have hle : ∀ a : Expr, a.looseBVarRange' = 0 → (a.abstractN ys 0).looseBVarRange' ≤
      ys.length := by
    intro a ha
    have := Lean4Lean.VerifyInductive.Expr.abstractN_looseBVarRange_le (e := a)
      (fvs := ys) (k := 0)
    simpa [ha] using this
  simp only [Expr.abstractN]
  rw [abstractN_mkAppList_eq (Expr.bvar ys.length) idx]
  refine .app (ArgClosed.mkAppList_bvar (i := ys.length) ?_ (.bvar _ _)) (hle _ ?_)
  · intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact hle b (hidx b hb)
  · have hcl : ∀ a ∈ args, a.looseBVarRange' ≤ 0 := fun a ha => by simp [hargs a ha]
    have : (mkAppList f args).looseBVarRange' ≤ 0 := by
      clear hle hidx
      induction args generalizing f with
      | nil => simp [mkAppList, hf]
      | cons a args ih =>
        simp only [mkAppList]
        exact ih (by simp [Expr.looseBVarRange', hf, hargs a (.head _)])
          (fun x hx => hargs x (.tail _ hx)) (fun x hx => hcl x (.tail _ hx))
    omega

/-- A recursive-call template `lctx.mkLambda xs (#n is (f xs))` with closed
binder domains, closed `is` and closed `f` is `ArgClosed 0`. -/
theorem ArgClosed.callTemplate {lctx : LocalContext} {xs : Array Expr} {ys : List FVarId}
    (hxs : xs = (ys.map Expr.fvar).toArray)
    (hdecl : ∀ y ∈ ys, ∃ i fv n ty bi kind,
      lctx.find? y = some (.cdecl i fv n ty bi kind) ∧ ty.looseBVarRange' = 0)
    {idx : Array Expr} {f : Expr} (hidx : ∀ a ∈ idx.toList, a.looseBVarRange' = 0)
    (hf : f.looseBVarRange' = 0) :
    ArgClosed 0 (lctx.mkLambda xs ((Lean.mkAppN (.bvar xs.size) idx).app
      (Lean.mkAppN f xs))) := by
  subst hxs
  rw [Lean.Expr.mkAppN_eq_mkAppList,
    Lean.Expr.mkAppN_eq_mkAppList]
  have hsz : (List.map Expr.fvar ys).toArray.size = ys.length := by simp
  rw [hsz]
  refine ArgClosed.mkLambda hdecl (ArgClosed.callBody hidx hf ?_)
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨y, -, rfl⟩ := ha
  rfl

namespace TrailingArgs

variable {heads names : List Name} {np : Nat} {ls : List Level}

/-- **Instantiating the placeholder of an `ArgClosed` template.** If `e` is in
parameterless uniform form and `ArgClosed k`, and `v` is a closed expression
satisfying `TrailingArgs` whose spine arguments are in parameterless uniform form,
then `e[k := v]` satisfies `TrailingArgs` for the condition "mentions `names`
only at `ls`", and so do its spine arguments. The substituent itself need not
be parameter-uniform: it lands only at spine heads. -/
theorem instantiate1'_argClosed {v : Expr} (hv : v.looseBVarRange' = 0)
    (hvT : TrailingArgs heads np (ParamUniform names [] ls) v)
    (hvargs : ∀ x ∈ v.getAppArgsList, ParamUniform names [] ls x) :
    ∀ {k e}, ArgClosed k e → ParamUniform names [] ls e →
      TrailingArgs heads np (ParamUniform names [] ls) (e.instantiate1' v k) ∧
      ∀ x ∈ (e.instantiate1' v k).getAppArgsList, ParamUniform names [] ls x := by
  intro k e H
  induction H with
  | bvar k i =>
    intro _
    simp only [Expr.instantiate1']
    split
    · exact ⟨.bvar _, by simp [getAppArgsList]⟩
    · split
      · rw [Expr.liftLooseBVars_eq_self (by omega)]
        exact ⟨hvT, hvargs⟩
      · exact ⟨.bvar _, by simp [getAppArgsList]⟩
  | closed h =>
    intro hs
    rw [Expr.instantiate1'_eq_self h]
    exact ⟨of_paramUniform_nil hs, fun x hx => hs.of_mem_getAppArgsList (by simp) hx⟩
  | @app k f a _ ha ih =>
    intro hs
    obtain ⟨hf, ha'⟩ := hs.app_inv_nil
    obtain ⟨T, A⟩ := ih hf
    simp only [Expr.instantiate1']
    rw [Expr.instantiate1'_eq_self ha]
    have hargs : ∀ x ∈ (Expr.app (f.instantiate1' v k) a).getAppArgsList,
        ParamUniform names [] ls x := by
      intro x hx
      rw [getAppArgsList_app] at hx
      rcases List.mem_append.1 hx with hx | hx
      · exact A x hx
      · rw [List.mem_singleton.1 hx]; exact ha'
    exact ⟨.app T (of_paramUniform_nil ha') fun _ _ _ _ x hx => hargs x (List.mem_of_mem_drop hx),
      hargs⟩
  | @lam k n t b bi ht _ ih =>
    intro hs
    obtain ⟨hts, hbs⟩ := hs.lam_inv
    simp only [Expr.instantiate1']
    rw [Expr.instantiate1'_eq_self ht]
    exact ⟨.lam (of_paramUniform_nil hts) (ih hbs).1, by simp [getAppArgsList]⟩

/-- A spine headed by a non-constant (a free variable, say) whose arguments
satisfy `TrailingArgs`. -/
theorem mkAppList_of_not_const {Q : Expr → Prop} :
    ∀ {args : List Expr} {f : Expr}, TrailingArgs heads np Q f →
      (∀ c us, f.getAppFn ≠ .const c us) →
      (∀ a ∈ args, TrailingArgs heads np Q a) →
      TrailingArgs heads np Q (mkAppList f args)
  | [], _, hf, _, _ => hf
  | a :: args, f, hf, hfn, hargs => by
    simp only [mkAppList]
    exact mkAppList_of_not_const (app_of_not_const hf (hargs a (.head _)) hfn)
      (by simpa [getAppFn] using hfn) fun x hx => hargs x (.tail _ hx)

private theorem getAppArgsList_mkAppList_eq :
    ∀ (args : List Expr) (f : Expr),
      (mkAppList f args).getAppArgsList = f.getAppArgsList ++ args
  | [], f => by simp [mkAppList]
  | a :: args, f => by
    simp only [mkAppList]
    rw [getAppArgsList_mkAppList_eq args, getAppArgsList_app]
    simp

/-- A constant applied to free variables: the substituent of a recursive-call
template. -/
theorem constSpine_fvars {c : Name} {us : List Level} {args : List Expr}
    (h : ∀ a ∈ args, ∃ fv, a = .fvar fv) :
    (mkAppList (.const c us) args).looseBVarRange' = 0 ∧
      TrailingArgs heads np (ParamUniform names [] ls) (mkAppList (.const c us) args) ∧
      ∀ x ∈ (mkAppList (.const c us) args).getAppArgsList, ParamUniform names [] ls x := by
  have hargs : ∀ x ∈ (mkAppList (.const c us) args).getAppArgsList,
      ∃ fv, x = .fvar fv := by
    intro x hx
    rw [getAppArgsList_mkAppList_eq] at hx
    simp only [getAppArgsList, List.nil_append] at hx
    exact h x hx
  refine ⟨?_, const_mkAppList fun a ha => ?_, fun x hx => ?_⟩
  · have key : ∀ (args : List Expr) (f : Expr), f.looseBVarRange' = 0 →
        (∀ a ∈ args, ∃ fv, a = .fvar fv) → (mkAppList f args).looseBVarRange' = 0 := by
      intro args
      induction args with
      | nil => intro f hf _; simpa [mkAppList] using hf
      | cons a args ih =>
        intro f hf ha
        simp only [mkAppList]
        obtain ⟨fv, rfl⟩ := ha a (.head _)
        exact ih _ (by simp [Expr.looseBVarRange', hf]) fun x hx => ha x (.tail _ hx)
    exact key args _ rfl h
  · obtain ⟨fv, rfl⟩ := h a ha
    exact ⟨.fvar _, .fvar _⟩
  · obtain ⟨fv, rfl⟩ := hargs x hx
    exact .fvar _

end TrailingArgs

end Lean.Expr

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- `IndexTelescopeRun.paramUniform` at an arbitrary parameter list. -/
theorem IndexTelescopeRun.paramUniformAt
    {heads : List Name} {params : List Expr} {ls : List Level} {env : Environment}
    {stats : AddInductive.InductiveStats}
    (W : WhnfPreservesParamUniform heads params ls env)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv)
    (hsp : ∀ p ∈ stats.params.toList, ∃ fv, p = .fvar fv)
    {final : AddInductive.Context} (henv : final.env = env)
    (hparamDecls : ∀ fv ∈ ExprArrayFVarIds stats.params, ∀ d,
      final.lctx.find? fv = some d → d.ParamUniformIn env heads params ls)
    {header : Expr} (hheader : header.ParamUniformIn env heads params ls)
    {i : Nat} {type : Expr} {indices : Array Expr}
    (T : IndexTelescopeRun stats final header i type indices) :
    type.ParamUniformIn env heads params ls ∧
      ∀ fv ∈ ExprArrayFVarIds indices, ∀ d, final.lctx.find? fv = some d →
        d.ParamUniformIn env heads params ls := by
  induction T with
  | start call =>
    exact ⟨call.paramUniform W henv (fun _ h => h.elim) hheader,
      by simp [ExprArrayFVarIds]⟩
  | @param i name dom body normalized bi _ hi call ih =>
    obtain ⟨hty, -⟩ := ih
    obtain ⟨-, hbody⟩ := hty.forallE_inv
    have hparam : (stats.params[i]!).ParamUniformIn env heads params ls := by
      have hmem : stats.params[i]! ∈ stats.params.toList := by
        rw [getElem!_pos stats.params i hi]
        exact Array.getElem_mem_toList hi
      obtain ⟨fv, hfv⟩ := hsp _ hmem
      rw [hfv]
      exact Expr.ParamUniformIn.fvar
    exact ⟨call.paramUniform W henv hparamDecls (hbody.instantiate1 hp hparam),
      by simp [ExprArrayFVarIds]⟩
  | @index indices name dom body normalized bi x _ member declaration call ih =>
    obtain ⟨hty, hidx⟩ := ih
    obtain ⟨hdom, hbody⟩ := hty.forallE_inv
    have hall : ∀ fv ∈ ExprArrayFVarIds (indices.push (.fvar x)), ∀ d,
        final.lctx.find? fv = some d → d.ParamUniformIn env heads params ls := by
      rw [ExprArrayFVarIds_push_fvar]
      intro fv hfv d hfind
      rcases List.mem_append.mp hfv with h | h
      · exact hidx fv h d hfind
      · rw [List.mem_singleton.mp h] at hfind
        obtain ⟨index, userName, binderInfo, kind, hx⟩ := declaration
        rw [hx] at hfind
        cases hfind
        exact LocalDecl.ParamUniformIn.of_cdecl ((hdom.consumeTypeAnnotationsVerified) hp)
    refine ⟨call.paramUniform W henv (fun fv hfv d hfind => ?_)
      (hbody.instantiate1 hp Expr.ParamUniformIn.fvar), hall⟩
    rcases hfv with h | h
    · exact hparamDecls fv h d hfind
    · exact hall fv h d hfind

/-- Declarations of a recursor context have closed types. -/
theorem RecursorContextWF.declType_closed {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams) {fv : FVarId} {d : LocalDecl}
    (hfind : c.lctx.find? fv = some d) : d.type.looseBVarRange' = 0 := by
  have hfind' : R.mlctx.lctx.find? fv = some d := by rw [R.lctx_eq]; exact hfind
  rw [R.mlctx_wf.tr.1.find?_eq_find?_toList] at hfind'
  have hmem : d ∈ R.mlctx.lctx.toList := List.mem_of_find?_eq_some hfind'
  obtain ⟨_, _, _, _, _, _, htypeTr⟩ :=
    R.mlctx_wf.tr.find?_of_mem R.checking.tr.wf hmem
  have hcl := TrExprS.closed htypeTr
  have hbv : R.mlctx.vlctx.bvars = 0 := R.mlctx_wf.tr.2.noBV
  rw [hbv] at hcl
  exact hcl.looseBVarRange_zero

/-- **The pieces of a recursive-call template**: the declarations of its
higher-order arguments satisfy `ParamUniformIn` and have closed types, and its exposed
target type satisfies `ParamUniformIn` and is closed. The same chain as
`InductionHypothesisType.paramUniform`, retaining closedness. -/
theorem InductionHypothesisType.templateFacts
    {heads : List Name} {params : List Expr} {ls : List Level} {env : Environment}
    (W : WhnfPreservesParamUniform heads params ls env)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv)
    {stats : AddInductive.InductiveStats} {recInfos : Array AddInductive.RecInfo}
    {root : AddInductive.Context} {field type : Expr}
    (O : InductionHypothesisType stats recInfos root field type)
    (henv : root.env = env)
    {recLparams : List Name} (Rroot : RecursorContextWF root recLparams)
    {P : FVarId → Prop} (hscope : Rroot.ParamUniformScope env heads params ls P)
    (hfieldP : ∀ fv, field = .fvar fv → P fv) :
    (∀ x ∈ O.arguments_bound.fvars, ∀ decl, O.current.lctx.find? x = some decl →
        decl.ParamUniformIn env heads params ls ∧ decl.type.looseBVarRange' = 0) ∧
      O.exposedType.ParamUniformIn env heads params ls ∧ O.exposedType.looseBVarRange' = 0 := by
  have hinference := O.loopInput.inference
  have hnormalization := O.loopInput.normalization
  obtain ⟨fv, hfield, hfvRoot⟩ := O.field_fvar
  have hfvP : P fv := hfieldP fv hfield
  obtain ⟨fieldTarget, hfieldTr⟩ := Rroot.trFVar hfvRoot
  subst hfield
  obtain ⟨inferredTarget, hbelow, _, hinferredTr, hfieldTyping⟩ :=
    getTypeFVarInRecursorContext.WF Rroot hfieldTr _ hinference
  obtain ⟨index, dname, dtype, dbi, dkind, hdecl⟩ := Rroot.findCDecl (fv := fv) (by
    rw [← Rroot.mlctx_wf.tr.fvars_eq, Rroot.lctx_eq]; exact hfvRoot)
  have hty : O.loopInput.inferredType = (LocalDecl.cdecl index fv dname dtype dbi dkind).type := by
    have h := hinference
    rw [AddInductive.getType.run] at h
    simp only [LocalContext.get!, Expr.fvarId!, hdecl, Except.ok.injEq] at h
    exact h.symm
  obtain ⟨jF, hjF, ty₀, hlctxF, htr₀, _⟩ := O.loopInput.checkBase Rroot
  let RF := Rroot.withCheckLCtx (loopUArgsCheckLCtx root O.loopInput.prior)
    ((Rroot.check.below jF hjF).cast hlctxF)
  have hinferredEq : O.loopInput.inferredType = (root.lctx.get! fv).type := by
    have h := hinference.symm.trans (AddInductive.getType.run (.fvar fv) root)
    exact Except.ok.inj h
  have hinferred₀ : TrExprS RF.venv recLparams RF.chk.vlctx
      O.loopInput.inferredType ty₀ := by
    rw [hinferredEq]; exact htr₀
  have hdeclH : (LocalDecl.cdecl index fv dname dtype dbi dkind).ParamUniformIn env heads params ls :=
    hscope.2 fv _ hfvP (by rw [Rroot.lctx_eq]; exact hdecl)
  have hinferredH : O.loopInput.inferredType.ParamUniformIn env heads params ls := by
    rw [hty]
    exact hdeclH.1
  have hfieldPin : (Expr.fvar fv).FVarsIn P := by simpa [FVarsIn] using hfvP
  have hinferredP : O.loopInput.inferredType.FVarsIn P := hbelow P hscope.1 hfieldPin
  have hinferredType : Rroot.venv.IsType recLparams.length
      Rroot.mlctx.vlctx.toCtx inferredTarget :=
    hfieldTyping.isType Rroot.checking.tr.wf Rroot.mlctx_wf.tr.wf.toCtx
  obtain ⟨⟨hnormalizedBelow, hnormalizedTr⟩, _, hnormalized₀⟩ :=
    whnfInRecursorContext.dualWF RF hinferredTr hinferred₀ _ hnormalization
  have hnormalizedH : O.loopInput.normalizedType.ParamUniformIn env heads params ls :=
    W.whnf RF henv ⟨_, hinferred₀⟩ hscope hinferredP hinferredH
      hnormalization
  have hnormalizedP : O.loopInput.normalizedType.FVarsIn P :=
    hnormalizedBelow P hscope.1 hinferredP
  obtain ⟨Rcurrent, P', T, hexpTr, _, hsc', hexposedH, _, _, hargs, _⟩ :=
    O.loopTrace.paramUniform W hp recursorConsumeTypeAnnotationsCompat henv RF hscope
      hnormalizedTr hinferredType hnormalized₀ hnormalizedH hnormalizedP
  refine ⟨fun x hx decl hdecl => ⟨?_, Rcurrent.declType_closed hdecl⟩, hexposedH, ?_⟩
  · have hxArg : Expr.fvar x ∈ O.args.toList := by
      rw [O.arguments_bound.expressions]
      simpa using hx
    obtain ⟨y, hy, hyP⟩ := hargs _ hxArg
    cases hy
    exact hsc'.2 x decl hyP (by rw [Rcurrent.lctx_eq]; exact hdecl)
  · obtain ⟨e₂, htr, -⟩ := hexpTr
    have hcl := TrExprS.closed htr
    have hbv : Rcurrent.mlctx.vlctx.bvars = 0 := Rcurrent.mlctx_wf.tr.2.noBV
    rw [hbv] at hcl
    exact hcl.looseBVarRange_zero

section TrailAssembly

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
  {R : ConstructorCheck c stats decl nparams isUnsafe depth
    sourceEnv indTypes ctorEnv}

/-- **Inputs of the trailing-argument chain** of a recursor
construction, for a name list `names` and the levels `ls` (in the application,
the auxiliary constructor names at levels that no translated constant
carries): parameter declarations, family headers and constructor types avoid
`names` and satisfy the projection condition, constructor types have the
parameter telescope, and the family names of the majors are not in `names`.
The generated recursor names may be in `names`: they occur in the rule
right-hand sides only at the heads of the recursive calls. -/
structure RecursorConstruction.TrailingArgDeclarations
    (H : RecursorConstruction R) (names : List Name) (ls : List Level) : Prop where
  paramDecls : ∀ fv ∈ H.params.fvars, ∀ d, H.localContext.lctx.find? fv = some d →
    d.ParamUniformIn H.localContext.env names [] ls ∧ d.type.AvoidsConsts names
  familyHeaders : ∀ i, i < indTypes.size → (indTypes[i]!.type).AvoidsConsts names ∧
    (indTypes[i]!.type).ProjsOK (projAvoidsHeads H.localContext.env names)
  constructorTypes : ∀ i, i < indTypes.size → ∀ ctor ∈ indTypes[i]!.ctors,
    (∃ body, Expr.LeadingBinders stats.params.size ctor.type body) ∧
      ctor.type.AvoidsConsts names ∧
      ctor.type.ProjsOK (projAvoidsHeads H.localContext.env names)
  familyNames : ∀ i, i < H.recInfos.size → ∀ n lv, stats.indConsts[i]! = .const n lv →
    n ∉ names

namespace RecursorConstruction

variable (H : RecursorConstruction R)

private theorem hQ {names : List Name} {ls : List Level} :
    ∀ (ys : List FVarId) x d, Expr.ParamUniform names [] ls x →
      Expr.ParamUniform names [] ls (x.abstractN ys d) :=
  fun ys _ d h => h.nil_abstractN ys d

/-- **Trailing arguments of one generated minor**: its field declarations are
`cdecl`s whose types mention `names` only at `ls`; its declared type satisfies
`TrailingArgs` for the condition "mentions `names` only at `ls`" (the only
other occurrences are the minor's constructor application, whose trailing
arguments are fields); the call templates of its rule template mention
`names` only at `ls` and are `ArgClosed`. -/
theorem minorTrail {names : List Name} {ls : List Level} (I : H.TrailingArgDeclarations names ls)
    (W : WhnfPreservesParamUniform names [] ls H.localContext.env)
    (heads : List Name) (np : Nat)
    (owner : Nat) (howner : owner < H.recInfos.size) (localIndex : Nat)
    (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    (∀ y ∈ (H.origins.minorShapes owner howner localIndex hlocal).fields_bound.fvars,
      ∃ i fv n ty bi kind, (H.origins.minorShapes owner howner localIndex
          hlocal).sourceFullContext.lctx.find? y = some (.cdecl i fv n ty bi kind) ∧
        ty.ParamUniform names [] ls) ∧
    (H.origins.minorShapes owner howner localIndex hlocal).origin.TrailingArgs heads np
      (Expr.ParamUniform names [] ls) ∧
    (∀ j, j < (H.origins.minorShapes owner howner localIndex hlocal).hypotheses.size →
      (H.recInfos[owner]!.ruleTemplates[localIndex]!.recursiveCalls[j]!).template.ParamUniform
        names [] ls ∧
      (H.recInfos[owner]!.ruleTemplates[localIndex]!.recursiveCalls[j]!).targetTypeIdx <
        stats.indConsts.size ∧
      (H.recInfos[owner]!.ruleTemplates[localIndex]!.recursiveCalls[j]!).template.ArgClosed
        0) := by
  have hsourceOwner := H.sourceOwner howner
  have hsrc := H.minorSources.rows owner howner hsourceOwner localIndex hlocal
  have hcallRoots : RuleTemplateMatchesMinor stats
      (H.origins.minorShapes owner howner localIndex hlocal)
      H.recInfos[owner]!.minors[localIndex]!
      H.recInfos[owner]!.ruleTemplates[localIndex]! :=
    H.templates.entry owner howner localIndex hlocal
  obtain ⟨Hsem⟩ := H.templateTyping.entry owner howner localIndex hlocal
  generalize H.origins.minorShapes owner howner localIndex hlocal = S at hsrc hcallRoots Hsem ⊢
  generalize H.recInfos[owner]!.ruleTemplates[localIndex]! = B at hcallRoots Hsem ⊢
  obtain ⟨-, -, hsourceCtors, -, traversal, htrav, -, -, -, -, hvalid, hmotiveApp, -, -,
    hsrcLE⟩ := hsrc
  obtain ⟨origins, hshape, hstats, -, F, -⟩ := Hsem
  obtain ⟨-, -, -, -, -, callOrigins, -, hcallShape, -, -, Hcalls⟩ := hcallRoots
  have hcallOrigins : callOrigins = origins :=
    Option.some.inj (hcallShape.symm.trans hshape)
  subst callOrigins
  have hT : traversal = F.traversal := Option.some.inj (htrav.symm.trans F.traversal_eq)
  subst hT
  have hp : ∀ p ∈ ([] : List Expr), ∃ fv, p = .fvar fv := by simp
  have Hroot := F.rootWF.toBindingContextWF
  have hTL : BindingContextLE F.traversal.terminalContext H.localContext :=
    F.terminalExtension.contextLE
  -- Field declarations (the lowered constructor's syntactic domains).
  have Hprefix : ParameterPrefix stats 0 S.constructor.type
      F.traversal.parameterTail := by
    have := F.traversal.parameterPrefix
    rwa [F.traversal_stats, F.traversal_constructor] at this
  have hctorMem : S.constructor ∈ indTypes[owner]!.ctors := by
    rw [← hsourceCtors]; exact List.mem_of_getElem? S.sourceConstructor
  obtain ⟨⟨body, Hlead⟩, havoid, hproj⟩ := I.constructorTypes owner hsourceOwner _ hctorMem
  have Htail' := Hprefix.paramUniformIn (ls := ls) H.params.expressions
    ⟨body, Hlead, Expr.ParamUniformBV.of_avoidsConsts (Hlead.avoidsConsts havoid) 0⟩ hproj
  have Htail : F.traversal.parameterTail.ParamUniformIn H.localContext.env names [] ls :=
    ⟨Htail'.1.params_nil H.params_fvar, Htail'.2⟩
  obtain ⟨hterm, hfieldsTerm⟩ := F.traversal.decisions.paramUniformIn Hroot hp Htail
  rw [F.traversal_fields] at hfieldsTerm
  have hfieldDecls : ∀ y ∈ S.fields_bound.fvars, ∃ i fv n ty bi kind,
      S.sourceFullContext.lctx.find? y = some (.cdecl i fv n ty bi kind) ∧
        ty.ParamUniform names [] ls := by
    intro y hy
    obtain ⟨fv, index, name, type, bi, kind, hfv, hmem, hfind, htype⟩ :=
      hfieldsTerm _ (S.fields_bound.mem_fvars_iff.1 hy)
    cases hfv
    refine ⟨index, y, name, type, bi, kind, ?_, htype.1⟩
    rw [← hsrcLE.declarations y (S.fields_bound.members y hy),
      hTL.declarations y hmem, hfind]
  -- Parameters are variables of the field traversal's terminal context.
  have hparamTerm : ∀ pv, Expr.fvar pv ∈ stats.params →
      pv ∈ F.traversal.terminalContext.lctx.fvars := fun pv h =>
    (F.traversal.decisions.freshBindings Hroot).choose_spec.1.fvars
      (F.parameterSuffix.param_mem h)
  -- Induction hypotheses and recursive calls (regions R2 and R3).
  have hfr : origins.fieldRoot = F.traversal.terminalContext :=
    S.hypothesis_origins_fieldRoot origins F.traversal hshape F.traversal_eq
  have hper : ∀ j, j < S.hypotheses.size →
      (∃ D : FVarDeclAt S.sourceFullContext S.hypotheses j,
        D.type.ParamUniform names [] ls) ∧
      ((B.recursiveCalls[j]!).template.ParamUniform names [] ls ∧
        (B.recursiveCalls[j]!).targetTypeIdx < stats.indConsts.size ∧
        (B.recursiveCalls[j]!).template.ArgClosed 0) := by
    intro j hj
    obtain ⟨originRoot, sourceType, recL, Rorigin, O, D, hle, hup, hD, hcall⟩ :=
      Hcalls.rooted j hj
    rw [hstats] at hup
    rw [hfr] at hle
    have henv : originRoot.env = H.localContext.env := hle.env_eq.trans hTL.env_eq.symm
    have hscope : Rorigin.ParamUniformScope H.localContext.env names [] ls
        (fun fv => fv ∈ ExprArrayFVarIds S.fields ∨
          fv ∈ ExprArrayFVarIds stats.params) := by
      refine ⟨hup, fun fv decl hP hfind => ?_⟩
      rw [Rorigin.lctx_eq] at hfind
      rcases hP with hf | hpar
      · rw [S.fields_bound.exprArrayFVarIds] at hf
        obtain ⟨fv', index, name, type, bi, kind, hfv, hmem, hfind', htype⟩ :=
          hfieldsTerm _ (S.fields_bound.mem_fvars_iff.1 hf)
        cases hfv
        rw [hle.declarations fv hmem, hfind'] at hfind
        cases hfind
        exact LocalDecl.ParamUniformIn.of_cdecl htype
      · rw [H.params.exprArrayFVarIds] at hpar
        have hmemP := H.params.mem_fvars_iff.1 hpar
        rw [hle.declarations fv (hparamTerm fv hmemP),
          ← hTL.declarations fv (hparamTerm fv hmemP)] at hfind
        exact (I.paramDecls fv hpar decl hfind).1
    have hjr : j < S.recursiveFields.size := by rw [← S.hypotheses_size]; exact hj
    have hfieldMem : S.recursiveFields[j]! ∈ S.fields := by
      rw [← F.traversal_fields]
      apply F.traversal.decisions.selected_subset
      rw [F.traversal_recursiveFields, getElem!_pos S.recursiveFields j hjr]
      exact Array.getElem_mem hjr
    have hfieldP : ∀ fv, S.recursiveFields[j]! = .fvar fv →
        (fun fv => fv ∈ ExprArrayFVarIds S.fields ∨
          fv ∈ ExprArrayFVarIds stats.params) fv := by
      intro fv hfv
      left
      rw [hfv] at hfieldMem
      exact mem_exprArrayFVarIds_of_fvar_mem hfieldMem
    obtain ⟨hargs, hexp, htype⟩ :=
      O.paramUniform W hp henv Rorigin hscope hfieldP (by simp)
    refine ⟨⟨D, by rw [hD]; exact (htype.consumeTypeAnnotationsVerified) hp⟩, ?_⟩
    rw [hcall]
    obtain ⟨ffv, hffv, -⟩ := O.field_fvar
    refine ⟨?_, by
      have := (checkPositivityStep.isValidIndApp?_some O.owner_valid).1
      exact hstats ▸ this, ?_⟩
    rotate_left
    · obtain ⟨hcl, -, hexpCl⟩ := O.templateFacts W hp henv Rorigin hscope hfieldP
      refine Expr.ArgClosed.callTemplate O.arguments_bound.expressions (fun y hy => ?_) ?_
        (by rw [hffv]; rfl)
      · have hyCur : y ∈ O.current.lctx.fvars := O.arguments_bound.members y hy
        obtain ⟨index, name, ty, bi, kind, hfind⟩ := O.current_wf.findCDecl y hyCur
        exact ⟨_, _, _, _, _, _, hfind, (hcl y hy _ hfind).2⟩
      · intro a ha
        rw [Lean4Lean.VerifyInductive.Expr.getAppArgs_slice_toList] at ha
        exact Nat.le_zero.1 (hexpCl ▸
          Expr.looseBVarRange_le_of_mem_getAppArgsList (List.mem_of_mem_drop ha))
    refine Expr.ParamUniform.mkLambda_of_disjoint O.arguments_bound.expressions ?_ (by simp) ?_
    · refine .app (Expr.ParamUniform.mkAppN (.bvar _) (hexp.getAppArgs_slice hp _))
        (Expr.ParamUniform.mkAppN (by rw [hffv]; exact .fvar ffv) ?_)
      intro a ha
      rw [O.arguments_bound.expressions] at ha
      simp only [List.mem_map] at ha
      obtain ⟨y, -, rfl⟩ := ha
      exact .fvar y
    · intro y hy
      have hyCur : y ∈ O.current.lctx.fvars := O.arguments_bound.members y hy
      obtain ⟨index, name, ty, bi, kind, hfind⟩ := O.current_wf.findCDecl y hyCur
      exact ⟨_, hfind, hargs y hy _ hfind⟩
  refine ⟨hfieldDecls, ?_, fun j hj => (hper j hj).2⟩
  -- The minor premise type.
  rw [← S.unannotated_eq]
  refine (Expr.TrailingArgs.consumeTypeAnnotationsVerified) ?_
  rw [S.sourceType_eq, ← S.sourceContext_eq]
  refine Expr.TrailingArgs.mkForall' S.fields_bound.expressions ?_ hQ
    (fun y hy => by
      obtain ⟨i, fv, n, ty, bi, kind, hfind, -⟩ := hfieldDecls y hy
      exact ⟨i, fv, n, ty, bi, kind, hfind⟩)
    (fun y hy d hfind => by
      obtain ⟨i, fv, n, ty, bi, kind, hfind', hty⟩ := hfieldDecls y hy
      rw [hfind] at hfind'
      cases hfind'
      exact Expr.TrailingArgs.of_paramUniform_nil hty)
  refine Expr.TrailingArgs.mkForall' S.hypotheses_bound.expressions ?_ hQ ?_ ?_
  · rw [hmotiveApp]
    simp only [AddInductive.getIIndices]
    have hmo := (checkPositivityStep.isValidIndApp?_some hvalid).1
    obtain ⟨mfv, hmfv⟩ := H.motive_fvar hmo
    simp only [AddInductive.getIIndices] at hmfv
    refine Expr.TrailingArgs.app_of_not_const ?_ ?_ ?_
    · refine Expr.TrailingArgs.of_paramUniform_nil
        (Expr.ParamUniform.mkAppN ?_ (hterm.1.getAppArgs_slice hp _))
      rw [hmfv]; exact .fvar mfv
    · rw [Lean.Expr.mkAppN_eq_mkAppList,
        Lean.Expr.mkAppN_eq_mkAppList, ← Expr.mkAppList_append]
      refine Expr.TrailingArgs.const_mkAppList fun a ha => ?_
      have hfv : ∃ fv, a = .fvar fv := by
        rcases List.mem_append.1 ha with ha | ha
        · exact H.params_fvar a ha
        · obtain ⟨y, rfl, -⟩ := FVarArrayIn.fvar_of_mem S.fields_bound
            (Array.mem_toList_iff.1 ha)
          exact ⟨y, rfl⟩
      obtain ⟨fv, rfl⟩ := hfv
      exact ⟨.fvar _, .fvar _⟩
    · intro c us h
      rw [Lean.Expr.mkAppN_eq_mkAppList,
        Expr.getAppFn_mkAppList, hmfv] at h
      cases h
  · intro y hy
    obtain ⟨j, hjl, hjy⟩ := List.mem_iff_getElem.1 hy
    have hj : j < S.hypotheses.size := by
      have := congrArg Array.size S.hypotheses_bound.expressions
      simp at this; omega
    obtain ⟨D, -⟩ := (hper j hj).1
    have hDy : D.fvar = y := by
      obtain ⟨_, hget⟩ := S.hypotheses_bound.getElem_eq_fvar j hj
      have := D.expression.symm.trans hget
      rw [← hjy]; exact Expr.fvar.inj this
    subst hDy
    exact ⟨_, _, _, _, _, _, D.declaration⟩
  · intro y hy d hfind
    obtain ⟨j, hjl, hjy⟩ := List.mem_iff_getElem.1 hy
    have hj : j < S.hypotheses.size := by
      have := congrArg Array.size S.hypotheses_bound.expressions
      simp at this; omega
    obtain ⟨D, hDshape⟩ := (hper j hj).1
    have hDy : D.fvar = y := by
      obtain ⟨_, hget⟩ := S.hypotheses_bound.getElem_eq_fvar j hj
      have := D.expression.symm.trans hget
      rw [← hjy]; exact Expr.fvar.inj this
    subst hDy
    rw [D.declaration] at hfind
    cases hfind
    exact Expr.TrailingArgs.of_paramUniform_nil hDshape

end RecursorConstruction

end TrailAssembly

end VerifyInductive
end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

section TrailAssembly2

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
  {R : ConstructorCheck c stats decl nparams isUnsafe depth
    sourceEnv indTypes ctorEnv}

namespace RecursorConstruction

variable (H : RecursorConstruction R) {names : List Name} {ls : List Level}

/-- Index declarations of every family (region R1). -/
theorem indexDeclNil (I : H.TrailingArgDeclarations names ls)
    (W : WhnfPreservesParamUniform names [] ls H.localContext.env)
    {k : Nat} (hk : k < H.recInfos.size) {y : FVarId}
    (hy : Expr.fvar y ∈ H.recInfos[k]!.indices) :
    ∃ d, H.localContext.lctx.find? y = some d ∧ d.ParamUniform names [] ls := by
  obtain ⟨type, T⟩ := H.minorSources.traces k hk
  have hparamDecls : ∀ fv ∈ ExprArrayFVarIds stats.params, ∀ d,
      H.localContext.lctx.find? fv = some d →
        d.ParamUniformIn H.localContext.env names [] ls := by
    intro fv hfv d hfind
    rw [H.params.exprArrayFVarIds] at hfv
    exact (I.paramDecls fv hfv d hfind).1
  obtain ⟨-, hidx⟩ := T.paramUniformAt W (by simp) H.params_fvar rfl hparamDecls
    (Expr.ParamUniformIn.of_avoids (I.familyHeaders k (H.sourceOwner hk)).1
      (I.familyHeaders k (H.sourceOwner hk)).2)
  have hyMem : y ∈ (H.bindings.indices k hk).fvars :=
    (H.bindings.indices k hk).mem_fvars_iff.2 hy
  obtain ⟨index, name, ty, bi, kind, hfind⟩ :=
    H.localWF.findCDecl y ((H.bindings.indices k hk).members y hyMem)
  refine ⟨_, hfind, (hidx y ?_ _ hfind).paramUniform⟩
  rw [(H.bindings.indices k hk).exprArrayFVarIds]
  exact hyMem

/-- Major premise declarations: `I params indices` with `I ∉ names`. -/
theorem majorDeclNil (I : H.TrailingArgDeclarations names ls) {y : FVarId}
    (hy : Expr.fvar y ∈ H.recInfos.map (·.major)) :
    ∃ d, H.localContext.lctx.find? y = some d ∧ d.ParamUniform names [] ls := by
  refine H.origins.majors.declParamUniform (fun i hi => ?_) hy
  have hi' : i < H.recInfos.size := by simpa using hi
  rw [H.majorShapes.shape i hi']
  refine (Expr.ParamUniform.consumeTypeAnnotationsVerified) ?_ (by simp)
  obtain ⟨n, hn⟩ := H.indConst_eq hi'
  rw [hn]
  refine Expr.ParamUniform.mkAppN (Expr.ParamUniform.mkAppN (.const (I.familyNames i hi' n _ hn))
    fun a ha => ?_) fun a ha => ?_
  · obtain ⟨fv, rfl⟩ := H.params_fvar a ha
    exact .fvar fv
  · obtain ⟨fv, rfl, -⟩ := FVarArrayIn.fvar_of_mem (H.bindings.indices i hi')
      (Array.mem_toList_iff.1 ha)
    exact .fvar fv

/-- Motive declarations: `∀ indices, ∀ (t : I params indices), Sort u`. -/
theorem motiveDeclNil (I : H.TrailingArgDeclarations names ls)
    (W : WhnfPreservesParamUniform names [] ls H.localContext.env)
    {y : FVarId} (hy : Expr.fvar y ∈ H.recInfos.map (·.motive)) :
    ∃ d, H.localContext.lctx.find? y = some d ∧ d.ParamUniform names [] ls := by
  refine H.origins.motives.declParamUniform (fun i hi => ?_) hy
  have hi' : i < H.recInfos.size := by simpa using hi
  rw [H.motiveShapes.shape i hi']
  refine Expr.ParamUniform.mkForall_of_disjoint (H.bindings.indices i hi').expressions ?_
    (by simp) (fun y hy => H.indexDeclNil I W hi'
      ((H.bindings.indices i hi').mem_fvars_iff.1 hy))
  refine Expr.ParamUniform.mkForall_of_disjoint (H.bindings.major i hi').expressions (.sort _)
    (by simp) (fun y hy => H.majorDeclNil I ?_)
  have h := (H.bindings.major i hi').mem_fvars_iff.1 hy
  simp only [List.mem_toArray, List.mem_singleton] at h
  rw [h]
  exact Array.mem_map.2 ⟨_, H.mem_recInfos hi', rfl⟩

/-- Minor premise declarations. -/
theorem minorDeclTrail (I : H.TrailingArgDeclarations names ls)
    (W : WhnfPreservesParamUniform names [] ls H.localContext.env) (heads : List Name) (np : Nat)
    {y : FVarId} (hy : Expr.fvar y ∈ H.recInfos.flatMap (·.minors)) :
    ∃ d, H.localContext.lctx.find? y = some d ∧
      d.type.TrailingArgs heads np (Expr.ParamUniform names [] ls) := by
  obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp hy
  obtain ⟨D⟩ := H.bindings.flatMinors.declarationAt H.localWF i hi
  obtain ⟨Fm⟩ := H.origins.flatMinorBinderType D
  have hDy : D.fvar = y := Expr.fvar.inj (D.expression.symm.trans hget)
  subst hDy
  refine ⟨_, D.declaration, ?_⟩
  show D.type.TrailingArgs heads np (Expr.ParamUniform names [] ls)
  rw [Fm.originType_eq]
  have howner := Fm.owner_lt
  have hlocal : Fm.localIndex < H.origins.minorTypes[Fm.owner]!.size := by
    rw [(H.origins.minors Fm.owner howner).size_eq, getElem!_pos H.recInfos Fm.owner howner]
    exact Fm.local_lt
  have hsrc := H.minorSources.rows Fm.owner howner (H.sourceOwner howner) Fm.localIndex hlocal
  rw [← hsrc.1]
  exact (H.minorTrail I W heads np Fm.owner howner Fm.localIndex hlocal).2.1

private theorem cdecl_of_mem {xs : Array Expr} (B : FVarArrayIn H.localContext xs)
    {y : FVarId} (hy : y ∈ B.fvars) :
    ∃ i fv n ty bi kind, H.localContext.lctx.find? y = some (.cdecl i fv n ty bi kind) := by
  obtain ⟨index, name, type, bi, kind, hfind⟩ := H.localWF.findCDecl y (B.members y hy)
  exact ⟨index, y, name, type, bi, kind, hfind⟩

private theorem type_of_find {P : Expr → Prop} {y : FVarId}
    (h : ∃ d, H.localContext.lctx.find? y = some d ∧ P d.type) :
    ∀ d, H.localContext.lctx.find? y = some d → P d.type := by
  obtain ⟨d', hd', hP⟩ := h
  intro d hd
  rw [hd'] at hd
  cases hd
  exact hP

private theorem nil_type {y : FVarId}
    (h : ∃ d, H.localContext.lctx.find? y = some d ∧ d.ParamUniform names [] ls)
    (hc : ∃ i fv n ty bi kind, H.localContext.lctx.find? y = some (.cdecl i fv n ty bi kind)) :
    ∃ d, H.localContext.lctx.find? y = some d ∧ d.type.ParamUniform names [] ls := by
  obtain ⟨d, hd, hs⟩ := h
  obtain ⟨i, fv, n, ty, bi, kind, hc⟩ := hc
  rw [hc] at hd
  cases hd
  exact ⟨_, hc, hs⟩

/-- **Trailing arguments of the generated rule right-hand sides.** Every rule
right-hand side `blueprint.instantiate ...` of a rule template satisfies `TrailingArgs` for the
condition "mentions `names` only at `ls`", and its parameter domains avoid
`names`. -/
theorem ruleRhsTrail (I : H.TrailingArgDeclarations names ls)
    (W : WhnfPreservesParamUniform names [] ls H.localContext.env) (heads : List Name) (np : Nat)
    (owner : Nat) (howner : owner < H.recInfos.size) (lvls : List Level)
    (blueprint : AddInductive.RecRuleTemplate)
    (hmem : blueprint ∈ H.recInfos[owner]!.ruleTemplates.toList) :
    (blueprint.instantiate indTypes stats (H.recInfos.map (·.motive))
        (H.recInfos.flatMap (·.minors)) lvls H.localContext.lctx).rhs.TrailingArgs heads np
      (Expr.ParamUniform names [] ls) ∧
    (blueprint.instantiate indTypes stats (H.recInfos.map (·.motive))
        (H.recInfos.flatMap (·.minors)) lvls H.localContext.lctx).rhs.LamPrefixAvoids names
      stats.params.size := by
  have hp : ∀ p ∈ ([] : List Expr), ∃ fv, p = .fvar fv := by simp
  obtain ⟨localIndex, hlocalB, hget⟩ := List.mem_iff_getElem.1 hmem
  have hlocalB' : localIndex < H.recInfos[owner]!.ruleTemplates.size := by simpa using hlocalB
  have hlocal : localIndex < H.origins.minorTypes[owner]!.size := by
    rw [← H.templates.rows_size owner howner]; exact hlocalB'
  have hB : H.recInfos[owner]!.ruleTemplates[localIndex]! = blueprint := by
    rw [getElem!_pos _ localIndex hlocalB']; simpa using hget
  obtain ⟨hfieldDecls, -, hcalls⟩ := H.minorTrail I W heads np owner howner localIndex hlocal
  have hentry := H.templates.entry owner howner localIndex hlocal
  rw [hB] at hcalls hentry
  obtain ⟨-, hBfields, hBlctx, hBminor, traversal, origins, -, hshape, -, -, hcallOrigins⟩ :=
    hentry
  have hcallsSize := hcallOrigins.size_eq
  generalize H.origins.minorShapes owner howner localIndex hlocal = S at *
  -- the minor variable
  have hminorsSize : localIndex < H.recInfos[owner]!.minors.size := by
    rw [← (H.origins.minors owner howner).size_eq]; exact hlocal
  have hminorMem : blueprint.minor ∈ H.recInfos[owner]!.minors := by
    rw [hBminor, getElem!_pos _ localIndex hminorsSize]; exact Array.getElem_mem hminorsSize
  obtain ⟨minorFv, hminorFv, -⟩ :=
    FVarArrayIn.fvar_of_mem (H.bindings.minors owner howner) hminorMem
  simp only [AddInductive.RecRuleTemplate.instantiate]
  have hQ : ∀ (ys : List FVarId) x d, Expr.ParamUniform names [] ls x →
      Expr.ParamUniform names [] ls (x.abstractN ys d) :=
    fun ys _ d h => h.nil_abstractN ys d
  -- the body: the minor variable applied to fields and recursive calls
  have hbody : (mkAppN (mkAppN blueprint.minor blueprint.fields)
      (blueprint.recursiveCalls.map fun call =>
        call.instantiate indTypes stats (H.recInfos.map (·.motive))
          (H.recInfos.flatMap (·.minors)) lvls)).TrailingArgs heads np
          (Expr.ParamUniform names [] ls) := by
    rw [hBfields, Lean.Expr.mkAppN_eq_mkAppList,
      Lean.Expr.mkAppN_eq_mkAppList, ← Expr.mkAppList_append]
    refine Expr.TrailingArgs.mkAppList_of_not_const (by rw [hminorFv]; exact .fvar _)
      (by rw [hminorFv]; intro c us h; cases h) fun a ha => ?_
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨y, rfl, -⟩ := FVarArrayIn.fvar_of_mem S.fields_bound
        (Array.mem_toList_iff.1 ha)
      exact .fvar y
    · simp only [Array.toList_map, List.mem_map] at ha
      obtain ⟨call, hcall, rfl⟩ := ha
      obtain ⟨j, hj, hcallj⟩ := List.mem_iff_getElem.1 hcall
      have hj' : j < blueprint.recursiveCalls.size := by simpa using hj
      have hcallEq : blueprint.recursiveCalls[j]! = call := by
        rw [getElem!_pos _ j hj']; simpa using hcallj
      obtain ⟨htemplate, -, hargCl⟩ := hcalls j (by rw [← hcallsSize]; exact hj')
      rw [hcallEq] at htemplate hargCl
      simp only [AddInductive.RecCallTemplate.instantiate, Expr.instantiate1_eq]
      rw [Lean.Expr.mkAppN_eq_mkAppList,
        Lean.Expr.mkAppN_eq_mkAppList,
        Lean.Expr.mkAppN_eq_mkAppList, ← Expr.mkAppList_append,
        ← Expr.mkAppList_append]
      have hfv : ∀ a ∈ stats.params.toList ++ (H.recInfos.map (·.motive)).toList ++
          (H.recInfos.flatMap (·.minors)).toList, ∃ fv, a = .fvar fv := by
        intro a ha
        rcases List.mem_append.1 ha with ha | ha
        · rcases List.mem_append.1 ha with ha | ha
          · exact H.params_fvar a ha
          · obtain ⟨fv, rfl, -⟩ := FVarArrayIn.fvar_of_mem H.bindings.motives
              (Array.mem_toList_iff.1 ha)
            exact ⟨fv, rfl⟩
        · obtain ⟨fv, rfl, -⟩ := FVarArrayIn.fvar_of_mem H.bindings.flatMinors
            (Array.mem_toList_iff.1 ha)
          exact ⟨fv, rfl⟩
      obtain ⟨hv, hvT, hvargs⟩ := Expr.TrailingArgs.constSpine_fvars (heads := heads)
        (np := np) (names := names) (ls := ls)
        (c := Lean.mkRecName indTypes[call.targetTypeIdx]!.name) (us := lvls) hfv
      have := (Expr.TrailingArgs.instantiate1'_argClosed hv hvT hvargs hargCl htemplate).1
      simpa only [List.append_assoc] using this
  -- the fields lambda
  have hfields : (blueprint.lctx.mkLambda blueprint.fields
      (mkAppN (mkAppN blueprint.minor blueprint.fields)
        (blueprint.recursiveCalls.map fun call =>
          call.instantiate indTypes stats (H.recInfos.map (·.motive))
            (H.recInfos.flatMap (·.minors)) lvls))).TrailingArgs heads np
          (Expr.ParamUniform names [] ls) := by
    revert hbody
    rw [hBlctx, hBfields]
    intro hbody
    refine Expr.TrailingArgs.mkLambda' S.fields_bound.expressions hbody hQ
      (fun y hy => ?_) (fun y hy d hfind => ?_)
    · obtain ⟨i, fv, n, ty, bi, kind, hfind, -⟩ := hfieldDecls y hy
      exact ⟨i, fv, n, ty, bi, kind, hfind⟩
    · obtain ⟨i, fv, n, ty, bi, kind, hfind', hty⟩ := hfieldDecls y hy
      rw [hfind] at hfind'
      cases hfind'
      exact Expr.TrailingArgs.of_paramUniform_nil hty
  constructor
  · refine Expr.TrailingArgs.mkLambda' H.params.expressions ?_ hQ H.paramCDecls
      (fun y hy d hfind => Expr.TrailingArgs.of_paramUniform_nil
        (Expr.ParamUniform.of_avoidsConsts (I.paramDecls y hy d hfind).2))
    refine Expr.TrailingArgs.mkLambda' H.bindings.motives.expressions ?_ hQ
      (fun y hy => H.cdecl_of_mem H.bindings.motives hy)
      (fun y hy => H.type_of_find (P := fun t => t.TrailingArgs heads np
          (Expr.ParamUniform names [] ls)) (by
        obtain ⟨d, hd, hs⟩ := H.nil_type (H.motiveDeclNil I W
          (H.bindings.motives.mem_fvars_iff.1 hy)) (H.cdecl_of_mem H.bindings.motives hy)
        exact ⟨d, hd, Expr.TrailingArgs.of_paramUniform_nil hs⟩))
    refine Expr.TrailingArgs.mkLambda' H.bindings.flatMinors.expressions ?_ hQ
      (fun y hy => H.cdecl_of_mem H.bindings.flatMinors hy)
      (fun y hy => H.type_of_find (P := fun t => t.TrailingArgs heads np
          (Expr.ParamUniform names [] ls))
        (H.minorDeclTrail I W heads np (H.bindings.flatMinors.mem_fvars_iff.1 hy)))
    exact hfields
  · have key : ∀ (ps : Array Expr), ps = (H.params.fvars.map Expr.fvar).toArray → ∀ b,
        (H.localContext.lctx.mkLambda ps b).LamPrefixAvoids names ps.size := by
      intro ps hps b
      subst hps
      simpa using Expr.LamPrefixAvoids.mkLambda (lctx := H.localContext.lctx) b fun y hy => by
        obtain ⟨i, fv, n, ty, bi, kind, hfind⟩ := H.paramCDecls y hy
        exact ⟨i, fv, n, ty, bi, kind, hfind, (I.paramDecls y hy _ hfind).2⟩
    exact key _ H.params.expressions _

end RecursorConstruction

end TrailAssembly2

end VerifyInductive
end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Major family names are not constructor names. -/
theorem RecursorConstruction.familyNames_not_mem
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) {names : List Name}
    (hnames : ∀ n ∈ names, n ∈ decl.types.flatMap (fun t => t.ctors.map (·.name)))
    (hnodup : (InductiveSignature.familyNames decl.types).Nodup) :
    ∀ i, i < H.recInfos.size → ∀ n lv, stats.indConsts[i]! = .const n lv → n ∉ names := by
  intro i hi n lv hn hmem
  have hi' : i < decl.types.length := by rw [← H.recInfos_size_eq]; exact hi
  have h := H.validStats.indConstAt hi'
  rw [getElem!_def, h] at hn
  cases hn
  exact familyName_not_mem_ctorNames hnodup _ (List.getElem_mem hi') (hnames _ hmem)

/-- The parameter declarations of a recursor construction avoid every
name fresh in the source environment and satisfy the projection condition. -/
theorem RecursorConstruction.paramDecls_trail
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) {env : Environment} {heads : List Name}
    {ls : List Level}
    (hfresh : ∀ name ∈ heads, sourceEnv.constants name = none)
    (hproj : ∀ s info, sourceEnv.projections s info → projAvoidsHeads env heads s) :
    ∀ fv ∈ H.params.fvars, ∀ d, H.localContext.lctx.find? fv = some d →
      d.ParamUniformIn env heads [] ls ∧ d.type.AvoidsConsts heads := by
  intro fv hfv d hfind
  have hparam : Expr.fvar fv ∈ stats.params := H.params.mem_fvars_iff.1 hfv
  have hc : fv ∈ c.lctx.fvars := by
    obtain ⟨fvars, hparams, hdecls⟩ :=
      cachedParameterDecls_fvars R.sourceStatsWF.cachedScope
    have hmem : Expr.fvar fv ∈ stats.params.toList.reverse := by simpa using hparam
    rw [hparams] at hmem
    simp only [List.mem_map, Expr.fvar.injEq, exists_eq_right] at hmem
    rw [← R.sourceContext.lctx_eq, R.sourceContext.mlctx_wf.tr.fvars_eq,
      R.sourceStatsWF.scopeDecomposition, VLCtx.fvars_append, hdecls]
    exact List.mem_append_right _ hmem
  have hfind' : c.lctx.find? fv = some d := by
    rw [← hfind]; exact (H.localExtends.declarations fv hc).symm
  have hfresh' : ∀ name ∈ heads, R.sourceContext.venv.constants name = none := by
    rw [R.sourceContextVEnv]; exact hfresh
  have hproj' : ∀ s info, R.sourceContext.venv.projections s info →
      projAvoidsHeads env heads s := by
    rw [R.sourceContextVEnv]; exact hproj
  obtain ⟨htype, hvalue⟩ := R.sourceContext.declAvoids hfresh' hfind'
  obtain ⟨ptype, pvalue⟩ := R.sourceContext.declProjsOK hproj' hfind'
  refine ⟨⟨⟨Expr.ParamUniform.of_avoidsConsts htype, ptype⟩, fun v hv => ?_⟩, htype⟩
  cases d with
  | cdecl => simp [LocalDecl.value?] at hv
  | ldecl _ _ _ _ val nd _ =>
    have hval : val = v := by cases nd <;> simpa [LocalDecl.value?] using hv
    subst hval
    exact ⟨Expr.ParamUniform.of_avoidsConsts hvalue, pvalue⟩

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {safety : DefinitionSafety} {outEnv : Environment}

/-- The auxiliary constructor names of a nested run: the constructor names of
the lowered families after the source families. -/
def NestedRun.auxCtorNames
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) : List Name :=
  (E.lowered.loweredDecl.types.drop sourceDecl.types.length).flatMap
    fun t => t.ctors.map (·.name)

/-- A level list of length `lparams.length + 1`, carried by no well-formed
occurrence of a constant of the run's declaration. -/
def foreignLevels (lparams : List Name) : List Level :=
  List.replicate (lparams.length + 1) .zero

theorem badLevels_ne (lparams : List Name) : foreignLevels lparams ≠ lparams.map Level.param := by
  intro h
  have := congrArg List.length h
  simp [foreignLevels] at this

theorem NestedRun.auxCtorNames_auxHeads
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) :
    ∀ n ∈ E.auxCtorNames, n ∈ E.auxHeads := by
  intro n hn
  obtain ⟨t, ht, hn⟩ := List.mem_flatMap.1 hn
  exact List.mem_flatMap.2 ⟨t, ht, List.mem_cons_of_mem _ hn⟩

theorem NestedRun.auxCtorNames_uniformHeads
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) :
    ∀ n ∈ E.auxCtorNames, n ∈ E.uniformHeads :=
  fun n hn => E.auxHeads_subset_uniformHeads n (E.auxCtorNames_auxHeads n hn)

theorem NestedRun.auxCtorNames_ctor
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) :
    ∀ n ∈ E.auxCtorNames, ∃ t ∈ E.lowered.loweredDecl.types, ∃ c ∈ t.ctors, c.name = n := by
  intro n hn
  obtain ⟨t, ht, hn⟩ := List.mem_flatMap.1 hn
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hn
  exact ⟨t, List.mem_of_mem_drop ht, c, hc, rfl⟩

section RunEnvTrail

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}

/-- The auxiliary constructor names are absent from the header environment, so
every lowered constructor type avoids them. -/
theorem NestedRun.ctorType_avoids_auxCtorNames
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {owner : InductiveType} (howner : owner ∈ E.lowered.indTypes.toList)
    {ctor : Constructor} (hctor : ctor ∈ owner.ctors) :
    ctor.type.AvoidsConsts E.auxCtorNames := by
  obtain ⟨-, -, -, -, -, -, -, hnodupAll⟩ := E.auxHeadsFacts wf Hsources
  have hnodup : (InductiveSignature.familyNames E.lowered.loweredDecl.types).Nodup :=
    (List.nodup_append.1 hnodupAll).1
  obtain ⟨⟨e', htr⟩, -⟩ := E.ctorType_tr howner hctor
  refine checkPositivityStep.TrExprS.sourceAvoidsFresh (fun n hn => ?_) htr
  obtain ⟨t, ht, c, hc, rfl⟩ := E.auxCtorNames_ctor n hn
  exact E.ctorNames_fresh_headerVEnv wf hnodup ht hc

/-- **The environment condition of the type checker's parameter-uniformity invariant at
the auxiliary constructor names, without parameters, at `foreignLevels`.** Every
constant of the recursor-pass environment other than an auxiliary constructor
has a type avoiding the auxiliary constructor names (old constants: they are
fresh in the source; family headers: translated in the source; lowered
constructors: translated in the header environment, where every lowered
constructor name is fresh), and so do the auxiliary constructors themselves,
so their types are (parameterless) head types at any level list. -/
theorem NestedRun.envParamUniform_auxCtorNames
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    EnvParamUniform E.lowered.ctorEnv E.auxCtorNames 0 (foreignLevels lparams) := by
  have hfresh : ∀ n ∈ E.auxCtorNames, sourceProdEnv.find? n = none :=
    fun n hn => E.uniformHeads_fresh wf n (E.auxCtorNames_uniformHeads n hn)
  have hpres : ∀ {n ci}, sourceProdEnv.find? n = some ci →
      E.lowered.ctorEnv.find? n = some ci := E.ctorEnv_preserves wf
  have hwfP : E.lowered.c.env.constants.WF := by
    rw [E.lowered_c_env]; exact (wf.tr (safety := .unsafe)).map_wf
  have horigin : ∀ {n ci}, E.lowered.ctorEnv.find? n = some ci →
      sourceProdEnv.find? n = some ci ∨
      (∃ indType ∈ E.lowered.indTypes.toList, ∃ info : InductiveVal,
        ci = .inductInfo info ∧ n = indType.name ∧ info.type = indType.type ∧
        info.levelParams = lparams) ∨
      (∃ owner ∈ E.lowered.indTypes.toList, ∃ ctor ∈ owner.ctors, ∃ info : ConstructorVal,
        ci = .ctorInfo info ∧ n = ctor.name ∧ info.type = ctor.type ∧
        info.levelParams = lparams) := by
    intro n ci h
    have := E.lowered.ctorEnv_find_cases hwfP h
    rwa [E.lowered_c_env, E.lowered_c_lparams] at this
  have hfreshN : ∀ {n ci}, sourceProdEnv.find? n = some ci → n ∉ E.auxCtorNames :=
    fun h hn => by rw [hfresh _ hn] at h; cases h
  let sf : DefinitionSafety := if isUnsafe then .unsafe else .safe
  have hheaderV : E.lowered.headers.context.venv.Ordered :=
    E.lowered.headers.context.checking.tr.wf.ordered
  have hheaderSub : ∀ s info, E.lowered.headers.context.venv.projections s info →
      ∃ info', (ves.venv sf).projections s info' := by
    intro s info h
    rw [VEnv.addConstVals_projections_eq E.lowered.constructors.core.typesAdded,
      E.lowered_initialEnv] at h
    exact ⟨info, h⟩
  -- every new constant type avoids the auxiliary constructor names
  have hnewAvoids : ∀ {n ci}, E.lowered.ctorEnv.find? n = some ci →
      sourceProdEnv.find? n = none → ci.type.AvoidsConsts E.auxCtorNames := by
    intro n ci h hnew
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, rfl, htype, -⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, rfl, htype, -⟩
    · rw [hold] at hnew; cases hnew
    · show info.type.AvoidsConsts _
      rw [htype]
      obtain ⟨e', htr⟩ := E.familyType_tr hmem
      exact avoids_of_tr wf hfresh _ htr
    · show info.type.AvoidsConsts _
      rw [htype]
      exact E.ctorType_avoids_auxCtorNames wf Hsources howner hctor
  refine {
    prims := ?prims
    strs := ?strs
    type_avoids := ?type_avoids
    value_avoids := ?value_avoids
    rules_avoid := ?rules_avoid
    head_kind := ?head_kind
    head_type := ?head_type
    rec_major := ?rec_major
    type_projs := ?type_projs
    value_projs := ?value_projs
    rules_projs := ?rules_projs }
  case prims =>
    intro n hn hmem
    exact E.lowered.nonprimitive_familyNames (E.uniformHeads_subset (E.auxCtorNames_uniformHeads n hmem))
      (checkerPrimNames_primitive n hn)
  case strs =>
    intro hs n hn hmem
    exact (E.envParamUniform wf Hsources).strs hs n hn (E.auxCtorNames_uniformHeads n hmem)
  case type_avoids =>
    intro n ci h hn
    cases hold : sourceProdEnv.find? n with
    | some ci' =>
      have := hpres hold
      rw [h] at this
      cases this
      exact (old_type_avoids wf hfresh hold).1
    | none => exact hnewAvoids h hold
  case value_avoids =>
    intro n ci v h hv
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, -⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, -⟩
    · exact (old_value_avoids wf hfresh hold hv).1
    · cases hv
    · cases hv
  case rules_avoid =>
    intro n r h rule hrule
    rcases horigin h with hold | ⟨indType, hmem, info, heq, -⟩ |
        ⟨owner, howner, ctor, hctor, info, heq, -⟩
    · exact (old_rules_avoid wf hfresh hold hrule).1
    · cases heq
    · cases heq
  case head_kind =>
    intro n ci h hn
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, -⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, -⟩
    · exact absurd hn (hfreshN hold)
    · exact .inl ⟨info, rfl⟩
    · exact .inr ⟨info, rfl⟩
  case head_type =>
    intro n ci h hn
    have hnew : sourceProdEnv.find? n = none := by
      cases hold : sourceProdEnv.find? n with
      | none => rfl
      | some ci' => exact absurd hn (hfreshN hold)
    have hav := hnewAvoids h hnew
    refine ⟨_, .zero _, ?_⟩
    show Expr.ParamUniformBV _ _ _ _ (ci.type.instantiateLevelParams ci.levelParams _)
    rw [Expr.instantiateLevelParams_eq]
    refine (Expr.ParamUniformBV.of_avoidsConsts hav 0).instantiateLevelParamsCore' fun l hl => ?_
    simp only [foreignLevels, List.mem_replicate] at hl
    rw [hl.2]
    rfl
  case rec_major =>
    intro n r h
    rcases horigin h with hold | ⟨indType, hmem, info, heq, -⟩ |
        ⟨owner, howner, ctor, hctor, info, heq, -⟩
    · exact old_rec_major wf hpres hfresh hold
    · cases heq
    · cases heq
  case type_projs =>
    intro n ci h
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, -, htype, -⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, -, htype, -⟩
    · obtain ⟨e', htr⟩ := (old_type_avoids wf hfresh hold).2
      exact projsOK_of_unsafe_tr wf hpres hfresh htr
    · show info.type.ProjsOK _
      rw [htype]
      obtain ⟨e', htr⟩ := E.familyType_tr hmem
      exact projsOK_of_tr_sub wf hpres hfresh sf (wf.tr (safety := sf)).wf.ordered
        (fun s i h => ⟨i, h⟩) htr
    · show info.type.ProjsOK _
      rw [htype]
      obtain ⟨⟨e', htr⟩, -⟩ := E.ctorType_tr howner hctor
      exact projsOK_of_tr_sub wf hpres hfresh sf hheaderV hheaderSub htr
  case value_projs =>
    intro n ci v h hv
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, -⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, -⟩
    · obtain ⟨e', htr⟩ := (old_value_avoids wf hfresh hold hv).2
      exact projsOK_of_unsafe_tr wf hpres hfresh htr
    · cases hv
    · cases hv
  case rules_projs =>
    intro n r h rule hrule
    rcases horigin h with hold | ⟨indType, hmem, info, heq, -⟩ |
        ⟨owner, howner, ctor, hctor, info, heq, -⟩
    · obtain ⟨e', htr⟩ := (old_rules_avoid wf hfresh hold hrule).2
      exact projsOK_of_unsafe_tr wf hpres hfresh htr
    · cases heq
    · cases heq

/-- **`whnf` preserves "mentions the auxiliary constructors only at
`foreignLevels`"** in the recursor pass of a validated nested run. -/
theorem NestedRun.whnfPreservesParamUniform_auxCtorNames
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    WhnfPreservesParamUniform E.auxCtorNames [] (foreignLevels lparams)
      E.lowered.recursors.localContext.env := by
  refine .of_env ?_ (fun a ha => by simp at ha)
  rw [E.recursorPassEnv]
  exact E.envParamUniform_auxCtorNames wf Hsources

/-- **The inputs of the trailing-argument chain for a validated nested run** at the
auxiliary constructor names and `foreignLevels`. -/
theorem NestedRun.trailingArgDeclarations_of
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    E.lowered.recursors.toRecursorConstruction.TrailingArgDeclarations
      E.auxCtorNames (foreignLevels lparams) := by
  let sf : DefinitionSafety := if isUnsafe then .unsafe else .safe
  have hfresh : ∀ n ∈ E.auxCtorNames, sourceProdEnv.find? n = none :=
    fun n hn => E.uniformHeads_fresh wf n (E.auxCtorNames_uniformHeads n hn)
  have hpres : ∀ {n ci}, sourceProdEnv.find? n = some ci →
      E.lowered.recursors.toRecursorConstruction.localContext.env.find?
        n = some ci := by
    intro n ci h
    have := E.ctorEnv_preserves wf h
    rw [← E.recursorPassEnv] at this
    exact this
  obtain ⟨-, -, -, -, -, -, -, hnodup⟩ := E.auxHeadsFacts wf Hsources
  have hnp : result.nparams = nparams := by
    obtain ⟨_, Hrun, _, _⟩ := E.lowering
    exact Hrun.resultNParams
  have hheaderV : E.lowered.headers.context.venv.Ordered :=
    E.lowered.headers.context.checking.tr.wf.ordered
  have hheaderSub : ∀ s info, E.lowered.headers.context.venv.projections s info →
      ∃ info', (ves.venv sf).projections s info' := by
    intro s info h
    rw [VEnv.addConstVals_projections_eq E.lowered.constructors.core.typesAdded,
      E.lowered_initialEnv] at h
    exact ⟨info, h⟩
  have hmem : ∀ i, i < E.lowered.indTypes.size →
      E.lowered.indTypes[i]! ∈ E.lowered.indTypes.toList := by
    intro i hi
    rw [getElem!_pos E.lowered.indTypes i hi]
    exact Array.getElem_mem_toList hi
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine E.lowered.recursors.toRecursorConstruction.paramDecls_trail
      (fun n hn => ?_) (fun s info h => ?_)
    · rw [E.lowered_initialEnv]
      cases hc : (ves.venv sf).constants n with
      | none => rfl
      | some ci =>
        obtain ⟨ci', hfind, -⟩ := (wf.tr (safety := sf)).find?_iff.2 ⟨ci, hc⟩
        rw [hfresh n hn] at hfind; cases hfind
    · rw [E.lowered_initialEnv] at h
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hlookup, -⟩ :=
        (wf.tr (safety := sf)).wf.ordered.projectionShape h
      obtain ⟨ci, hci, -⟩ := (wf.tr (safety := sf)).find?_iff.2 ⟨_, hlookup⟩
      exact projParamUniformIn_of_old wf hpres hfresh hci
  · intro i hi
    obtain ⟨e', htr⟩ := E.familyType_tr (hmem i hi)
    exact ⟨avoids_of_tr wf hfresh _ htr,
      projsOK_of_tr_sub wf hpres hfresh sf (wf.tr (safety := sf)).wf.ordered
        (fun s i h => ⟨i, h⟩) htr⟩
  · intro i hi ctor hctor
    obtain ⟨⟨e', htr⟩, -⟩ := E.ctorType_tr (hmem i hi) hctor
    refine ⟨?_, E.ctorType_avoids_auxCtorNames wf Hsources (hmem i hi) hctor,
      projsOK_of_tr_sub wf hpres hfresh sf hheaderV hheaderSub htr⟩
    obtain ⟨body, hl, -⟩ := E.ctorTypes_headType wf Hsources _ (hmem i hi) ctor hctor
    rw [E.statsParamsSize, hnp]
    exact ⟨body, hl.leadingBinders⟩
  · refine E.lowered.recursors.toRecursorConstruction.familyNames_not_mem
      (fun n hn => ?_) (List.nodup_append.1 hnodup).1
    obtain ⟨t, ht, hn⟩ := List.mem_flatMap.1 hn
    exact List.mem_flatMap.2 ⟨t, List.mem_of_mem_drop ht, hn⟩

end RunEnvTrail

end VerifyInductive
end Lean4Lean

namespace Lean.Expr

/-- `LamPrefixAvoids` mono in the avoided names. -/
theorem LamPrefixAvoids.mono {names names' : List Name} {k : Nat} {e : Expr}
    (H : LamPrefixAvoids names k e) (hsub : ∀ n ∈ names', n ∈ names) :
    LamPrefixAvoids names' k e := by
  induction H with
  | zero => exact .zero _
  | succ hd _ ih => exact .succ (hd.mono hsub) ih

/-- `TrailingArgsAvoid` mono in the avoided names. -/
theorem TrailingArgsAvoid.mono {heads names names' : List Name} {np : Nat} {e : Expr}
    (H : e.TrailingArgsAvoid heads names np) (hsub : ∀ n ∈ names', n ∈ names) :
    e.TrailingArgsAvoid heads names' np := by
  induction H with
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | const => exact .const _ _
  | lit _ h => exact .lit _ (h.mono hsub)
  | app _ _ h ihf iha =>
    exact .app ihf iha fun c us hfn hc x hx => (h c us hfn hc x hx).mono hsub
  | lam _ _ ihd ihb => exact .lam ihd ihb
  | forallE _ _ ihd ihb => exact .forallE ihd ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

/-- A lambda prefix avoiding `names` around a body in parameterless uniform form
is in parameterless uniform form. -/
theorem LamPrefixAvoids.paramUniform_nil {names : List Name} {ls : List Level} {k : Nat}
    {e body : Expr} (H : LamPrefixAvoids names k e) (hl : LeadingBinders k e body)
    (hb : ParamUniform names [] ls body) : ParamUniform names [] ls e := by
  induction H generalizing body with
  | zero => cases hl; exact hb
  | succ hd _ ih =>
    cases hl with
    | lam hl' => exact .lam (.of_avoidsConsts hd) (ih hl' hb)

end Lean.Expr

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

theorem NestedRun.LoweredRulesAvoid.mono
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    {E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv}
    {heads X Y : List Name} (H : E.LoweredRulesAvoid heads X) (hsub : ∀ n ∈ Y, n ∈ X) :
    E.LoweredRulesAvoid heads Y :=
  fun owner rec hfind rule hrule =>
    ⟨(H owner rec hfind rule hrule).1.mono hsub, (H owner rec hfind rule hrule).2.mono hsub⟩

section RunTrail

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}

/-- The lowered recursor found at a generated owner's recursor name is the
owner's generated entry. -/
theorem NestedRun.generatedEntryOfFind
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (owner : Fin E.lowered.recursors.generationSignature.families.size)
    {rec : RecursorVal}
    (hfind : E.loweredEnv.find?
        (E.lowered.recursors.canonicalGeneration.recursorName owner) =
      some (.recInfo rec)) :
    ∃ hi : owner.val < E.lowered.recursors.entries.length,
      (E.lowered.recursors.generated.entry owner.val hi).info = rec := by
  rcases E.lowered.recursors.trMetadata owner with
    ⟨rec', hrec, _, M⟩
  have hlen : owner.val < E.lowered.recursors.entries.length := by
    rw [E.lowered.recursors.entries_length_eq]
    exact owner.isLt
  refine ⟨hlen, ?_⟩
  have hmem := List.getElem_mem (l := E.lowered.recursors.entries)
    (n := owner.val) hlen
  have hfind' := E.lowered.recursors.findRecursorOfMem
    (info := (E.lowered.recursors.entries[owner.val]'hlen).1) hmem
  have hrec' : (E.lowered.recursors.entries[owner.val]'hlen).1 = .recInfo rec' := hrec
  rw [hrec'] at hfind'
  change E.loweredEnv.find? rec'.name = some (.recInfo rec') at hfind'
  have h2 : some (ConstantInfo.recInfo rec') = some (.recInfo rec) := by
    rw [← hfind', M.name]
    exact hfind
  have heq : rec' = rec := by
    injection h2 with h
    injection h
  have hG := (E.lowered.recursors.generated.entry owner.val hlen).source_eq
  rw [hrec] at hG
  injection hG with hG
  rw [← heq, hG]

/-- **Input-side avoidance of the auxiliary constructor names by the lowered
recursor rules.** In every rule right-hand side of every lowered recursor of an
validated nested run, the trailing arguments of the head occurrences (of any head
list), the literals and the parameter domains avoid the auxiliary constructor
names.

The proof runs the trailing-argument chain (`ruleRhsTrail`) at the auxiliary
constructor names without parameters, at the impossible levels `foreignLevels`
(`whnfPreservesParamUniform_auxCtorNames`): the regions computed by `whnf`, the
constructor field domains, the index domains and the parameter domains mention
the auxiliary constructors only at `foreignLevels`, and the only other occurrences
are the minors' constructor applications, whose trailing arguments are fields.
The parameter-uniformity chain at the declaration's levels (`recursorParamUniform_uniformHeads`)
says that every occurrence is at `lparams.map Level.param ≠ foreignLevels`, so the
trailing occurrences do not exist. -/
theorem NestedRun.loweredRulesAvoid_auxCtorNames
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (heads : List Name) :
    E.LoweredRulesAvoid heads E.auxCtorNames := by
  intro owner rec hfind rule hrule
  obtain ⟨hi, hinfo⟩ := E.generatedEntryOfFind owner hfind
  let C := E.lowered.recursors
  have howner : owner.val < C.recInfos.size := by rw [← C.generated.length]; exact hi
  have hrule' : rule ∈ (C.generated.entry owner.val hi).info.rules := by rw [hinfo]; exact hrule
  -- the declaration-level parameter uniformity
  have W := E.whnfPreservesParamUniform wf Hsources
  rw [← E.statsLevels] at W
  have HS := (C.generatedParamUniform (E.paramUniformDeclarations_of wf Hsources) W owner.val hi).2 rule hrule'
  -- the trailing-argument chain at `foreignLevels`
  rw [(C.generated.entry owner.val hi).rules_eq] at hrule'
  simp only [List.mem_map] at hrule'
  obtain ⟨blueprint, hmem, rfl⟩ := hrule'
  obtain ⟨HT, HL⟩ := C.toRecursorConstruction.ruleRhsTrail
    (E.trailingArgDeclarations_of wf Hsources) (E.whnfPreservesParamUniform_auxCtorNames wf Hsources)
    heads result.nparams owner.val howner
    (AddInductive.getRecLevels C.elimLevel E.lowered.stats.levels) blueprint hmem
  have hsize : E.lowered.stats.params.size = result.nparams := E.statsParamsSize
  obtain ⟨body, hl, hb⟩ := HS
  rw [hsize] at HL hl
  rw [E.statsLevels] at hb
  have Hglob := HL.paramUniform_nil hl
    ((hb.toNil).nil_mono (fun n hn => E.auxCtorNames_uniformHeads n hn))
  obtain ⟨-, -, -, -, -, hreserved, -, -⟩ := E.auxHeadsFacts wf Hsources
  have hlit : ∀ l : Literal, (Expr.lit l).AvoidsConsts E.auxCtorNames :=
    avoidsConsts_lit_of_reserved fun n hn => hreserved n (E.auxCtorNames_auxHeads n hn)
  exact ⟨HT.toTrailingArgsAvoid Hglob (badLevels_ne lparams) (fun _ h => h) hlit, HL⟩

end RunTrail

end VerifyInductive
end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-! ### Shape of the auxiliary family names -/

private theorem nestedAuxFold_keys (P : Name → Prop) :
    ∀ (entries : List (Expr × Name)) (map : Std.TreeMap Name Expr Name.quickCmp),
      (∀ entry ∈ entries, P entry.2) →
      (∀ name nested, map[name]? = some nested → P name) →
      ∀ name nested, (entries.foldl
        (fun (map : Std.TreeMap Name Expr Name.quickCmp)
          (entry : Expr × Name) => map.insert entry.2 entry.1) map)[name]? = some nested →
        P name
  | [], _, _, Hmap => Hmap
  | entry :: entries, map, Hentries, Hmap => by
    simp only [List.foldl_cons]
    refine nestedAuxFold_keys P entries _ (fun e he => Hentries e (.tail _ he)) ?_
    intro query value hfind
    rw [Std.TreeMap.getElem?_insert] at hfind
    split at hfind
    next hcmp =>
      rw [← Std.LawfulEqCmp.eq_of_compare hcmp]
      exact Hentries entry (.head _)
    next => exact Hmap query value hfind

/-- **The auxiliary family names of a lowering run are numeric**:
`Name.mkNum `_nested i` (`mkUniqueName`). -/
theorem NestedLowering.resultFamilyNamesIndexedOfEmpty
    {env : Environment} {fuel nparams : Nat} {types : List InductiveType}
    {initialState finalState : Lean4Lean.ElimNestedInductive.State}
    {result : Lean4Lean.ElimNestedInductive.Result}
    (H : NestedLowering env fuel nparams types initialState (result, finalState))
    (hempty : initialState.nestedAux = #[]) :
    ∀ (name : Name) (nested : Expr),
      (show Std.TreeMap Name Expr Name.quickCmp from result.aux2nested)[name]? = some nested →
      ∃ i, name = Name.mkNum `_nested i := by
  have Hnames := H.resultNamesWF (NestedAuxNamesWF.empty initialState hempty)
  rw [H.resultAuxMap]
  change ∀ (name : Name) (nested : Expr), (finalState.nestedAux.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1) {})[name]? = some nested →
      ∃ i, name = Name.mkNum `_nested i
  rw [← Array.foldl_toList]
  refine nestedAuxFold_keys (fun name => ∃ i, name = Name.mkNum `_nested i) _ _ ?_ ?_
  · intro entry hentry
    obtain ⟨i, hi, -⟩ := Hnames.indexed entry.1 entry.2 (by simpa using hentry)
    exact ⟨i, hi⟩
  · intro name nested hfind; simp at hfind

/-- The lowered families after the source families are named by the
specializations. -/
theorem auxiliarySpecializations_familyNames
    {sourceEnv envTypes : VEnv} {paramCtx : List VExpr} {decl : VInductDecl}
    {env : VEnv} {leaf : Nat → VExpr → VExpr → Prop}
    {auxiliaries : List ContainerSpecialization} {generated targets : List VInductiveType}
    (H : List.Forall₂ (SpecializationGenerates sourceEnv envTypes paramCtx decl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion env decl leaf)
      generated targets) :
    ∀ t ∈ targets, ∃ a ∈ auxiliaries, t.name = a.auxiliary := by
  induction H generalizing targets with
  | nil => cases Hexpansion; simp
  | @cons a family _ _ h _ ih =>
    cases Hexpansion with
    | @cons _ target _ _ hexp htail =>
      intro t ht
      rcases List.mem_cons.1 ht with rfl | ht
      · refine ⟨a, .head _, ?_⟩
        rw [h.auxiliary]
        exact hexp.name
      · obtain ⟨b, hb, hname⟩ := ih htail t ht
        exact ⟨b, .tail _ hb, hname⟩

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}

/-- **The restorable renamed names are auxiliary constructor names.** A renamed
auxiliary recursor name `Main.rec_k` that is a restorable name is the name of
an auxiliary constructor: lowered auxiliary recursor names are never renamed
(`auxRecName_not_renamed`), and auxiliary family names are numeric
(`_nested.i`) while renamed names are string extensions. -/
theorem NestedRun.restorableRenamed_auxCtorNames
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (Haux : List.Forall₂ (SpecializationGenerates
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.lowered.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams) :
    ∀ n ∈ ((compilationRestoration sourceDecl auxiliaries).recursors.map Prod.snd).filter
        (· ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames),
      n ∈ E.auxCtorNames := by
  intro n hn
  simp only [List.mem_filter, decide_eq_true_eq] at hn
  obtain ⟨hX, hR⟩ := hn
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hX
  obtain ⟨s, hs⟩ := compilationRestoration_recursors_snd_str sourceDecl auxiliaries p hp
  simp only [Restoration.restorableNames, List.mem_append] at hR
  rcases hR with hhead | hfst
  · rw [compilationRestoration_heads_auxiliary,
      auxiliarySpecializations_headNames Haux Hexpansion] at hhead
    obtain ⟨t, ht, hmem⟩ := List.mem_flatMap.1 hhead
    rcases List.mem_cons.1 hmem with hname | hctor
    · exfalso
      obtain ⟨a, ha, hta⟩ := auxiliarySpecializations_familyNames Haux Hexpansion t ht
      obtain ⟨nested, hnested⟩ := D.familyLookup a ha
      rcases E.lowering with ⟨finalState, Hrun, -, -⟩
      obtain ⟨i, hi⟩ := Hrun.resultFamilyNamesIndexedOfEmpty rfl _ _ hnested
      rw [hname, hta, hi] at hs
      simp [Name.mkNum] at hs
    · exact List.mem_flatMap.2 ⟨t, ht, hctor⟩
  · exfalso
    rw [compilationRestoration_recursors_fst] at hfst
    obtain ⟨a, ha, heq⟩ := List.mem_map.1 hfst
    exact E.auxRecName_not_renamed wf Hsources D a ha (heq ▸ hX)

/-- **Input-side avoidance of the restorable renamed names by the lowered
rules**, for a restoration table of `restorationTablesRestoringAll`: the
premise `LoweredRulesAvoid` of the restored-equation lemma at the
restorable names among the renamed auxiliary recursor names, discharged from
the run alone (`loweredRulesAvoid_auxCtorNames`,
`restorableRenamed_auxCtorNames`). -/
theorem NestedRun.loweredRulesAvoid_renamed
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (Haux : List.Forall₂ (SpecializationGenerates
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.lowered.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams) :
    E.LoweredRulesAvoid E.auxHeads
      (((compilationRestoration sourceDecl auxiliaries).recursors.map Prod.snd).filter
        (· ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames)) :=
  (E.loweredRulesAvoid_auxCtorNames wf Hsources E.auxHeads).mono
    (E.restorableRenamed_auxCtorNames wf Hsources Haux Hexpansion D)

end VerifyInductive
end Lean4Lean
