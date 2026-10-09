import Lean4Lean.Verify.Inductive.Nested.Install.RunView
import Lean4Lean.Verify.TypeChecker.ParamUniformWHNF
import Lean4Lean.Verify.Inductive.Nested.Restoration.Uniform.Declarations

/-! # `whnf` preserves parameter uniformity in a nested run

`TypeChecker.whnf.paramUniform` (`Lean4Lean/Verify/TypeChecker/ParamUniform.lean`) says
that `whnf` preserves `Expr.ParamUniformIn` (parameter uniformity together with the
projection condition `ProjsOK (projAvoidsHeads env heads)`) under a parameter-uniform scope
whose environment satisfies `EnvParamUniform`. This file instantiates it for the recursor
pass of a validated nested run.

* `whnfInRecursorContext.paramUniformIn`: the lift to the inductive checker's
  `monadLift (TypeChecker.whnf e)` in a `RecursorContextWF` (mirrors
  `whnfInRecursorContext.levelsWF`).
* `NestedRun.envParamUniform`: `EnvParamUniform` of the constructor-phase
  environment (where the recursor pass runs) for the head set
  `E.uniformHeads = E.auxHeads ++ E.mainCtorNames`. The source constructors must be
  heads: their lowered types mention auxiliary families, so they cannot satisfy
  `type_avoids`. Base constants are handled through the unsafe model of the
  source environment (types, values and recursor rules translate there, the
  heads are fresh there, and registered projections name base structures);
  the installed family headers and constructors through the header and
  constructor translations and the lowering (`mkForall` telescopes).
* `NestedRun.paramsUngeneratedParams`: the run's parameters are never
  names of the checker's name generator (`RecursorContextWF.kernelFresh`; the
  checker's generator starts at index `0`).
* `NestedRun.whnfPreservesParamUniform`: the resulting `WhnfPreservesParamUniform`
  (`Nested/Restoration/Uniform/Recursors.lean`).
* `NestedRun.paramUniformDeclarations_of`: the non-`whnf` inputs
  `RecursorConstruction.ParamUniformDeclarations` at `E.uniformHeads`.
* `NestedRun.recursorParamUniform_of_wfCore`: the parameter uniformity of the lowered
  recursor types and rule right-hand sides at the auxiliary heads, from the run
  alone.

The chain of `Nested/Restoration/Uniform/Recursors.lean` runs at `E.uniformHeads`
rather than at the auxiliary heads, with the projection condition on inputs
and scope declarations, both forced by the invariant: the source constructors'
types mention auxiliary families, and the projection registry of the
recursor pass contains the block's own structures. `ParamUniform.shrink`,
`ParamUniformBV.shrink` and `ParamUniformTele.shrink` return from `E.uniformHeads` to
`E.auxHeads`. -/



/-! ### Generic syntactic lemmas -/

namespace Lean.Expr
open Lean4Lean

theorem LeadingForalls.trans {k m : Nat} {e mid body : Expr} (H₁ : LeadingForalls k e mid)
    (H₂ : LeadingForalls m mid body) : LeadingForalls (m + k) e body := by
  induction H₁ with
  | zero => exact H₂
  | forallE _ ih => exact .forallE (ih H₂)

theorem LeadingForalls.avoidsConsts {names : List Name} {k : Nat} {e body : Expr}
    (H : LeadingForalls k e body) (h : e.AvoidsConsts names) : body.AvoidsConsts names := by
  induction H with
  | zero => exact h
  | forallE _ ih => cases h; exact ih ‹_›

private theorem leadingForalls_go {lctx : LocalContext} :
    ∀ {l : List FVarId}, (∀ x ∈ l, ∃ i fv n ty bi kind,
      lctx.find? x = some (.cdecl i fv n ty bi kind)) →
    ∀ b, LeadingForalls l.length (LocalContext.mkBindingListN.go false lctx l b) b
  | [], _, b => .zero b
  | x :: l, hx, b => by
    obtain ⟨i, fv, n, ty, bi, kind, hfind⟩ := hx x (.head _)
    have ih := leadingForalls_go (lctx := lctx) (l := l) (fun y hy => hx y (.tail _ hy))
      (LocalContext.mkBindingList1N false lctx l.reverse x b)
    have hstep : LeadingForalls 1 (LocalContext.mkBindingList1N false lctx l.reverse x b) b := by
      simp only [LocalContext.mkBindingList1N, hfind]
      exact .forallE (.zero b)
    simpa [LocalContext.mkBindingListN.go, Nat.add_comm] using ih.trans hstep

/-- `mkForall` over distinct `cdecl` variables adds exactly one `forallE` per variable. -/
theorem LeadingForalls.mkBindingListN {lctx : LocalContext}
    {xs : List FVarId} (hx : ∀ x ∈ xs, ∃ i fv n ty bi kind,
      lctx.find? x = some (.cdecl i fv n ty bi kind)) (b : Expr) :
    LeadingForalls xs.length (LocalContext.mkBindingListN false lctx xs b) (b.abstractN xs) := by
  simp only [LocalContext.mkBindingListN, LocalContext.mkBindingListN.core]
  simpa using leadingForalls_go (l := xs.reverse) (fun x hx' => hx x (List.mem_reverse.1 hx'))
    (b.abstractN xs)

/-- Closing the opened parameters with `LocalContext.mkForall` yields a head type. -/
theorem ParamUniform.mkForall_headType {heads : List Name} {ls : List Level}
    {lctx : LocalContext} {As : Array Expr} {xs : List FVarId} {b : Expr}
    (H : ParamUniform heads As.toList ls b) (hAs : As.toList = xs.map .fvar) (hnd : xs.Nodup)
    (hx : ∀ x ∈ xs, ∃ i fv n ty bi kind, lctx.find? x = some (.cdecl i fv n ty bi kind)) :
    HeadType heads As.size ls (lctx.mkForall As b) := by
  obtain ⟨As⟩ := As
  simp only at hAs; subst hAs
  simp only [LocalContext.mkForall, List.size_toArray, List.length_map]
  rw [LocalContext.mkBinding_eqN]
  exact ⟨_, .mkBindingListN hx b, H.abstractN_params hnd 0⟩

/-! #### Growing and shrinking the head set -/

/-- Adding heads that do not occur. -/
theorem ParamUniformBV.grow {heads heads' extra : List Name} {n : Nat} {ls : List Level}
    {d : Nat} {e : Expr} (H : ParamUniformBV heads n ls d e) (hsub : ∀ c ∈ heads, c ∈ heads')
    (hnew : ∀ c ∈ heads', c ∉ heads → c ∈ extra) (havoid : e.AvoidsConsts extra) :
    ParamUniformBV heads' n ls d e := by
  induction H with
  | head hc => exact .head (hsub _ hc)
  | app _ _ ihf iha => cases havoid; exact .app (ihf ‹_›) (iha ‹_›)
  | @const _ c _ hc =>
    cases havoid with
    | const _ _ fresh => exact .const fun h => fresh (hnew c h hc)
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | lit => exact .lit _
  | lam _ _ iht ihb => cases havoid; exact .lam (iht ‹_›) (ihb ‹_›)
  | forallE _ _ iht ihb => cases havoid; exact .forallE (iht ‹_›) (ihb ‹_›)
  | letE _ _ _ iht ihv ihb => cases havoid; exact .letE (iht ‹_›) (ihv ‹_›) (ihb ‹_›)
  | mdata _ ih => cases havoid; exact .mdata (ih ‹_›)
  | proj _ ih => cases havoid; exact .proj (ih ‹_›)

private theorem paramUniformBV_mkAppList {heads : List Name} {n : Nat} {ls : List Level} {d : Nat}
    {f : Expr} {args : List Expr} (hf : ParamUniformBV heads n ls d f)
    (hargs : ∀ a ∈ args, ParamUniformBV heads n ls d a) :
    ParamUniformBV heads n ls d (f.mkAppList args) := by
  induction args generalizing f with
  | nil => exact hf
  | cons a args ih => exact ih (.app hf (hargs a (.head _))) fun b hb => hargs b (.tail _ hb)

/-- Dropping heads, bound-variable form. -/
theorem ParamUniformBV.shrink {heads heads' : List Name} {n : Nat} {ls : List Level} {d : Nat}
    {e : Expr} (H : ParamUniformBV heads' n ls d e) (hsub : ∀ c ∈ heads, c ∈ heads') :
    ParamUniformBV heads n ls d e := by
  induction H with
  | @head c d hc =>
    by_cases hc' : c ∈ heads
    · exact .head hc'
    · refine paramUniformBV_mkAppList (.const hc') fun p hmem => ?_
      simp only [paramBVars, List.mem_map] at hmem
      obtain ⟨_, _, rfl⟩ := hmem
      exact .bvar _
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

theorem ParamUniformTele.shrink {heads heads' : List Name} {n : Nat} {ls : List Level} {e : Expr}
    (H : ParamUniformTele heads' n ls e) (hsub : ∀ c ∈ heads, c ∈ heads') :
    ParamUniformTele heads n ls e :=
  let ⟨body, hl, hb⟩ := H; ⟨body, hl, hb.shrink hsub⟩

/-! #### Level instantiation at the identity -/

private theorem instantiateLevelParamsCore'_mkAppList {red : Bool} {s : Name → Level}
    (f : Expr) (args : List Expr) :
    (f.mkAppList args).instantiateLevelParamsCore' red s =
      (f.instantiateLevelParamsCore' red s).mkAppList
        (args.map (·.instantiateLevelParamsCore' red s)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih => simp only [mkAppList, List.map_cons]; rw [ih]; rfl

theorem LeadingForalls.instantiateLevelParamsCore' {red : Bool} {s : Name → Level} {k : Nat}
    {e body : Expr} (H : LeadingForalls k e body) :
    LeadingForalls k (e.instantiateLevelParamsCore' red s)
      (body.instantiateLevelParamsCore' red s) := by
  induction H with
  | zero => exact .zero _
  | forallE _ ih => exact .forallE ih

theorem ParamUniformBV.instantiateLevelParamsCore' {red : Bool} {s : Name → Level}
    {heads : List Name} {n : Nat} {ls : List Level} {d : Nat} {e : Expr}
    (H : ParamUniformBV heads n ls d e) (hls : ∀ l ∈ ls, l.substParams' s red = l) :
    ParamUniformBV heads n ls d (e.instantiateLevelParamsCore' red s) := by
  induction H with
  | @head c d hc =>
    rw [instantiateLevelParamsCore'_mkAppList]
    have hmap : ls.map (·.substParams' s red) = ls := by
      conv => rhs; rw [← List.map_id ls]
      exact List.map_congr_left hls
    have hargs : (paramBVars n d).map (·.instantiateLevelParamsCore' red s) =
        paramBVars n d := by
      simp [paramBVars, Function.comp_def, Expr.instantiateLevelParamsCore']
    simp only [Expr.instantiateLevelParamsCore', hmap, hargs]
    exact .head hc
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

private theorem idxOf?_bind_map_param {ps : List Name} {x : Name} :
    ((ps.idxOf? x).bind ((ps.map Level.param)[·]?)).getD (.param x) = .param x := by
  cases h : ps.idxOf? x with
  | none => rfl
  | some i =>
    have hi := List.idxOf?_eq_some_iff.1 h
    simp only [Option.bind_some, List.getElem?_map]
    rw [List.getElem?_eq_getElem hi.1]
    simp [hi.2.1]

/-- Instantiating the level parameters `ps` of a head type with `ps` themselves. -/
theorem _root_.Lean4Lean.HeadType.instantiateLevelParams_self {heads : List Name} {n : Nat} {ps : List Name}
    {t : Expr} (H : HeadType heads n (ps.map Level.param) t) :
    HeadType heads n (ps.map Level.param) (t.instantiateLevelParams ps (ps.map Level.param)) := by
  rw [Expr.instantiateLevelParams_eq]
  obtain ⟨body, hl, hb⟩ := H
  refine ⟨_, hl.instantiateLevelParamsCore', hb.instantiateLevelParamsCore' fun l hl' => ?_⟩
  simp only [List.mem_map] at hl'
  obtain ⟨p, -, rfl⟩ := hl'
  simp only [Level.substParams']
  exact idxOf?_bind_map_param

theorem ParamUniformBV.of_avoidsConsts {heads : List Name} {n : Nat} {ls : List Level}
    {e : Expr} (h : e.AvoidsConsts heads) : ∀ d, ParamUniformBV heads n ls d e := by
  induction h with
  | bvar => exact fun _ => .bvar _
  | fvar => exact fun _ => .fvar _
  | mvar => exact fun _ => .mvar _
  | sort => exact fun _ => .sort _
  | const _ _ fresh => exact fun _ => .const fresh
  | app _ _ _ _ ihf iha => exact fun d => .app (ihf d) (iha d)
  | lam _ _ _ _ _ _ iht ihb => exact fun d => .lam (iht d) (ihb (d + 1))
  | forallE _ _ _ _ _ _ iht ihb => exact fun d => .forallE (iht d) (ihb (d + 1))
  | letE _ _ _ _ _ _ _ _ iht ihv ihb => exact fun d => .letE (iht d) (ihv d) (ihb (d + 1))
  | lit => exact fun _ => .lit _
  | mdata _ _ _ ih => exact fun d => .mdata (ih d)
  | proj _ _ _ _ ih => exact fun d => .proj (ih d)

theorem _root_.Lean4Lean.HeadType.grow {heads heads' extra : List Name} {n : Nat} {ls : List Level} {t : Expr}
    (H : HeadType heads n ls t) (hsub : ∀ c ∈ heads, c ∈ heads')
    (hnew : ∀ c ∈ heads', c ∉ heads → c ∈ extra) (havoid : t.AvoidsConsts extra) :
    HeadType heads' n ls t :=
  let ⟨body, hl, hb⟩ := H; ⟨body, hl, hb.grow hsub hnew (hl.avoidsConsts havoid)⟩

end Lean.Expr

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! ### Base constants -/

section Old

variable {env₀ env₁ : Environment} {ves : VEnvs} {heads : List Name}

private theorem find_constants (wf : ves.WF env₀) {n : Name} {ci : ConstantInfo}
    (h : env₀.find? n = some ci) : env₀.constants.find? n = some ci := by
  have hwf := (wf.tr (safety := .unsafe)).map_wf
  rw [← hwf.find?'_eq_find?]; exact h

/-- A name absent from the kernel environment is absent from its unsafe
abstract model. -/
theorem _root_.Lean4Lean.VEnvs.WF.unsafe_fresh (wf : ves.WF env₀) {n : Name} (h : env₀.find? n = none) :
    (ves.venv .unsafe).constants n = none := by
  cases hc : (ves.venv .unsafe).constants n with
  | none => rfl
  | some ci =>
    obtain ⟨ci', hfind, -⟩ := (wf.tr (safety := .unsafe)).find?_iff.2 ⟨ci, hc⟩
    rw [h] at hfind; cases hfind

/-- A constant of the unsafe abstract model is a constant of the kernel environment. -/
theorem _root_.Lean4Lean.VEnvs.WF.unsafe_present (wf : ves.WF env₀) {n : Name} {ci : VConstant}
    (h : (ves.venv .unsafe).constants n = some ci) : ∃ ci', env₀.find? n = some ci' := by
  obtain ⟨ci', hfind, -⟩ := (wf.tr (safety := .unsafe)).find?_iff.2 ⟨ci, h⟩
  exact ⟨ci', hfind⟩

variable (wf : ves.WF env₀)
  (hpres : ∀ {n ci}, env₀.find? n = some ci → env₁.find? n = some ci)
  (hfresh : ∀ h ∈ heads, env₀.find? h = none)

include wf hpres hfresh in
/-- **Projections on base structures are compatible with the head set**: a base
structure is not a head, and its constructors (base constants as well) are not
heads. -/
theorem projParamUniformIn_of_old {s : Name} {ci : ConstantInfo} (hs : env₀.find? s = some ci) :
    projAvoidsHeads env₁ heads s := by
  refine ⟨fun hmem => (by rw [hfresh s hmem] at hs; cases hs), fun v hv c hc hmem => ?_⟩
  rw [hpres hs] at hv
  cases hv
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
  obtain ⟨C⟩ := wf.inductiveConstructorsCoherent s v hs i hi
  have hl := C.lookup
  rw [hfresh _ hmem] at hl
  cases hl

include wf hpres hfresh in
/-- Projections in syntax translated in the unsafe model of the base environment. -/
theorem projsOK_of_unsafe_tr {Us : List Name} {e : Expr} {e' : VExpr}
    (H : TrExprS (ves.venv .unsafe) Us [] e e') :
    e.ProjsOK (projAvoidsHeads env₁ heads) := by
  have hvwf := (wf.tr (safety := .unsafe)).wf
  refine (H.projsRegistered hvwf.ordered trivial).mono fun s ⟨info, hinfo⟩ => ?_
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hlookup, -⟩ :=
    hvwf.ordered.projectionShape hinfo
  obtain ⟨ci, hci⟩ := wf.unsafe_present hlookup
  exact projParamUniformIn_of_old wf hpres hfresh hci


include wf hpres hfresh in
/-- Projections in syntax translated in any abstract environment whose
registered projections are registered in some safety model of the base
environment. -/
theorem projsOK_of_tr_sub (sf : DefinitionSafety) {V : VEnv} (hV : V.Ordered)
    (hsub : ∀ s info, V.projections s info → ∃ info', (ves.venv sf).projections s info')
    {Us : List Name} {e : Expr} {e' : VExpr} (H : TrExprS V Us [] e e') :
    e.ProjsOK (projAvoidsHeads env₁ heads) := by
  have hvwf := (wf.tr (safety := sf)).wf
  refine (H.projsRegistered hV trivial).mono fun s ⟨info, hinfo⟩ => ?_
  obtain ⟨info', hinfo'⟩ := hsub s info hinfo
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hlookup, -⟩ :=
    hvwf.ordered.projectionShape hinfo'
  obtain ⟨ci, hci, -⟩ := (wf.tr (safety := sf)).find?_iff.2 ⟨_, hlookup⟩
  exact projParamUniformIn_of_old wf hpres hfresh hci

include wf hfresh in
theorem avoids_of_tr (sf : DefinitionSafety) {Us : List Name} {Δ : VLCtx} {e : Expr}
    {e' : VExpr} (H : TrExprS (ves.venv sf) Us Δ e e') : e.AvoidsConsts heads := by
  refine checkPositivityStep.TrExprS.sourceAvoidsFresh (fun h hh => ?_) H
  cases hc : (ves.venv sf).constants h with
  | none => rfl
  | some ci =>
    obtain ⟨ci', hfind, -⟩ := (wf.tr (safety := sf)).find?_iff.2 ⟨ci, hc⟩
    rw [hfresh h hh] at hfind; cases hfind

include wf hfresh in
theorem avoids_of_unsafe_tr {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (H : TrExprS (ves.venv .unsafe) Us Δ e e') : e.AvoidsConsts heads :=
  checkPositivityStep.TrExprS.sourceAvoidsFresh
    (fun h hh => wf.unsafe_fresh (hfresh h hh)) H

include wf hfresh in
/-- Base constant types translate in the unsafe model, so they avoid the heads. -/
theorem old_type_avoids {n : Name} {ci : ConstantInfo} (h : env₀.find? n = some ci) :
    ci.type.AvoidsConsts heads ∧ ∃ e', TrExprS (ves.venv .unsafe) ci.levelParams [] ci.type e' := by
  obtain ⟨ci', -, -, -, htr⟩ := (wf.tr (safety := .unsafe)).find? h DefinitionSafety.unsafe_le
  exact ⟨avoids_of_unsafe_tr wf hfresh htr, _, htr⟩

include wf hfresh in
theorem old_value_avoids {n : Name} {ci : ConstantInfo} {v : Expr}
    (h : env₀.find? n = some ci) (hv : ci.deltaValue? = some v) :
    v.AvoidsConsts heads ∧ ∃ e', TrExprS (ves.venv .unsafe) ci.levelParams [] v e' := by
  obtain ⟨e', htr, -⟩ := (wf.tr (safety := .unsafe)).of_value h DefinitionSafety.unsafe_le hv
  exact ⟨avoids_of_unsafe_tr wf hfresh htr, _, htr⟩

include wf hfresh in
theorem old_rules_avoid {n : Name} {r : RecursorVal}
    (h : env₀.find? n = some (.recInfo r)) {rule : RecursorRule} (hrule : rule ∈ r.rules) :
    rule.rhs.AvoidsConsts heads ∧
      ∃ e', TrExprS (ves.venv .unsafe) r.levelParams [] rule.rhs e' := by
  obtain ⟨⟨_, _, _, -, -, hrules⟩, -⟩ :=
    (wf.tr (safety := .unsafe)).recursorEnvCoherent.rules (find_constants wf h)
      DefinitionSafety.unsafe_le
  obtain ⟨df, hdf⟩ := hrules rule hrule
  exact ⟨avoids_of_unsafe_tr wf hfresh hdf.rhs, _, hdf.rhs⟩

include wf hpres hfresh in
/-- The major family of a base recursor is a base inductive, so neither it nor
its constructors are heads. -/
theorem old_rec_major {n : Name} {r : RecursorVal} (h : env₀.find? n = some (.recInfo r)) :
    r.getMajorInduct ∉ heads ∧
      ∀ v, env₁.find? r.getMajorInduct = some (.inductInfo v) → ∀ c ∈ v.ctors, c ∉ heads := by
  obtain ⟨info, hinfo⟩ :=
    (wf.tr (safety := .unsafe)).recursorEnvCoherent.majors (find_constants wf h)
      DefinitionSafety.unsafe_le
  have hinfo' : env₀.find? r.getMajorInduct = some (.inductInfo info) := by
    have hwf := (wf.tr (safety := .unsafe)).map_wf
    rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]; exact hinfo
  exact projParamUniformIn_of_old wf hpres hfresh hinfo'

end Old

/-! ### The environment of the recursor pass -/

section Production

private theorem mem_zipWith_left {f : α → β → γ} :
    ∀ {as : List α} {bs : List β} {x : γ}, x ∈ List.zipWith f as bs → ∃ a ∈ as, ∃ b, x = f a b
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, b :: bs, x, h => by
    simp only [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, List.mem_cons_self, b, rfl⟩
    · obtain ⟨a', ha', b', rfl⟩ := mem_zipWith_left h
      exact ⟨a', List.mem_cons_of_mem _ ha', b', rfl⟩

theorem mem_inductiveTypeInfos {stats : AddInductive.InductiveStats} {numParams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {lparams : List Name} {info : InductiveVal}
    (h : info ∈ (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
      isUnsafe lparams).toList) :
    ∃ indType ∈ indTypes.toList, info.name = indType.name ∧ info.type = indType.type ∧
      info.levelParams = lparams := by
  simp only [AddInductive.inductiveTypeInfos, Array.toList_zipWith] at h
  obtain ⟨indType, hmem, _, rfl⟩ := mem_zipWith_left h
  exact ⟨indType, hmem, rfl, rfl, rfl⟩

theorem ConstructorListEntries.entryInfo {mkInfo : Nat → Constructor → ConstructorVal}
    {start : Nat} {ctors : List Constructor} {entries : List (ConstantInfo × VConstVal)}
    (H : ConstructorListEntries mkInfo start ctors entries) {entry : ConstantInfo × VConstVal}
    (hentry : entry ∈ entries) :
    ∃ ctor ∈ ctors, ∃ k, entry.1 = .ctorInfo (mkInfo k ctor) := by
  induction H with
  | nil => simp at hentry
  | cons _ ih =>
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | htail
    · exact ⟨_, List.mem_cons_self, _, rfl⟩
    · obtain ⟨c, hc, k, he⟩ := ih htail
      exact ⟨c, List.mem_cons_of_mem _ hc, k, he⟩

theorem ConstructorTypeEntries.entryInfo
    {mkInfo : InductiveType → Nat → Constructor → ConstructorVal}
    {owners : List InductiveType} {entries : List (ConstantInfo × VConstVal)}
    (H : ConstructorTypeEntries mkInfo owners entries) {entry : ConstantInfo × VConstVal}
    (hentry : entry ∈ entries) :
    ∃ owner ∈ owners, ∃ ctor ∈ owner.ctors, ∃ k, entry.1 = .ctorInfo (mkInfo owner k ctor) := by
  induction H with
  | nil => simp at hentry
  | cons Hhead _ ih =>
    rcases List.mem_append.mp hentry with hhead | htail
    · obtain ⟨ctor, hctor, k, he⟩ := Hhead.entryInfo hhead
      exact ⟨_, List.mem_cons_self, ctor, hctor, k, he⟩
    · obtain ⟨owner, howner, ctor, hctor, k, he⟩ := ih htail
      exact ⟨owner, List.mem_cons_of_mem _ howner, ctor, hctor, k, he⟩

theorem AddConstants.entryNonprimitive
    (H : AddConstants safety env venv entries outEnv outVEnv)
    {entry : ConstantInfo × VConstVal} (hentry : entry ∈ entries) :
    ¬ Kernel.Environment.primitives.contains entry.1.name := by
  induction H with
  | nil => simp at hentry
  | cons _ hnprim _ _ _ _ _ ih =>
    rcases List.mem_cons.1 hentry with rfl | htail
    · exact hnprim
    · exact ih htail

variable {outEnv : Environment} (P : LoweredRun outEnv)

/-- **Lookups in the constructor-phase environment** (where the recursor pass
runs): either a base constant, an installed family header, or an installed
constructor. -/
theorem LoweredRun.ctorEnv_find_cases (hwf : P.c.env.constants.WF)
    {n : Name} {ci : ConstantInfo} (h : P.ctorEnv.find? n = some ci) :
    P.c.env.find? n = some ci ∨
      (∃ indType ∈ P.indTypes.toList, ∃ info : InductiveVal, ci = .inductInfo info ∧
        n = indType.name ∧ info.type = indType.type ∧ info.levelParams = P.c.lparams) ∨
      (∃ owner ∈ P.indTypes.toList, ∃ ctor ∈ owner.ctors, ∃ info : ConstructorVal,
        ci = .ctorInfo info ∧ n = ctor.name ∧ info.type = ctor.type ∧
        info.levelParams = P.c.lparams) := by
  have hwfH := P.headers.installed.targetMapWF hwf
  rcases P.constructors.declared.installed.entryOrigin hwfH h with hH | ⟨entry, hentry, hname, hfound⟩
  · rcases P.headers.installed.entryOrigin hwf hH with h0 | ⟨entry, hentry, hname, hfound⟩
    · exact .inl h0
    · obtain ⟨numNested, Hentries⟩ := P.headers.sourceAligned
      obtain ⟨info, hinfo, he⟩ := Hentries.originInfo hentry
      obtain ⟨indType, hmem, hn, ht, hl⟩ := mem_inductiveTypeInfos hinfo
      refine .inr (.inl ⟨indType, hmem, info, hfound.trans he, ?_, ht, hl⟩)
      rw [hname, he]; exact hn
  · obtain ⟨owner, howner, ctor, hctor, k, he⟩ :=
      P.constructors.declared.sourceAligned.entryInfo hentry
    refine .inr (.inr ⟨owner, howner, ctor, hctor, _, hfound.trans he, ?_, rfl, rfl⟩)
    rw [hname, he]; rfl

/-- Every family and constructor name of the installed declaration is fresh
in the environment before installation. -/
theorem LoweredRun.fresh_familyNames (hwf : P.c.env.constants.WF)
    {n : Name} (hn : n ∈ InductiveSignature.familyNames P.loweredDecl.types) : P.c.env.find? n = none := by
  obtain ⟨t, ht, hn⟩ := List.mem_flatMap.1 hn
  rcases List.mem_cons.1 hn with rfl | hctor
  · have hv : t.toVConstVal ∈ P.headers.entries.map Prod.snd := by
      rw [P.headers.values]; exact List.mem_map_of_mem ht
    obtain ⟨⟨ci, v⟩, hentry, rfl⟩ := List.mem_map.1 hv
    have hname := P.headers.installed.entryNames hentry
    have := P.headers.installed.entryFresh hwf hentry
    simpa [hname] using this
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hctor
    have hv : c ∈ P.constructors.declared.entries.map Prod.snd := by
      rw [P.constructors.declared.values]
      exact List.mem_flatMap.2 ⟨t, ht, hc⟩
    obtain ⟨⟨ci, v⟩, hentry, rfl⟩ := List.mem_map.1 hv
    have hname := P.constructors.declared.installed.entryNames hentry
    have hfreshH := P.constructors.declared.installed.entryFresh
      (P.headers.installed.targetMapWF hwf) hentry
    cases h0 : P.c.env.find? ci.name with
    | none => simpa [hname] using h0
    | some found =>
      have := P.headers.installed.preservesSourceFind hwf h0
      rw [hfreshH] at this; cases this

/-- Every family and constructor name of the installed declaration passed the
installation's `checkName` without primitive permission, so it is not a
reserved primitive name. -/
theorem LoweredRun.nonprimitive_familyNames
    {n : Name} (hn : n ∈ InductiveSignature.familyNames P.loweredDecl.types) :
    ¬ Kernel.Environment.primitives.contains n := by
  obtain ⟨t, ht, hn⟩ := List.mem_flatMap.1 hn
  rcases List.mem_cons.1 hn with rfl | hctor
  · have hv : t.toVConstVal ∈ P.headers.entries.map Prod.snd := by
      rw [P.headers.values]; exact List.mem_map_of_mem ht
    obtain ⟨⟨ci, v⟩, hentry, rfl⟩ := List.mem_map.1 hv
    have hname := P.headers.installed.entryNames hentry
    have := P.headers.installed.entryNonprimitive hentry
    simpa [hname] using this
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hctor
    have hv : c ∈ P.constructors.declared.entries.map Prod.snd := by
      rw [P.constructors.declared.values]
      exact List.mem_flatMap.2 ⟨t, ht, hc⟩
    obtain ⟨⟨ci, v⟩, hentry, rfl⟩ := List.mem_map.1 hv
    have hname := P.constructors.declared.installed.entryNames hentry
    have := P.constructors.declared.installed.entryNonprimitive hentry
    simpa [hname] using this

/-- A constant of the constructor-phase environment that is not a base
constant was installed by the run, hence is not a reserved primitive name. -/
theorem LoweredRun.ctorEnv_new_nonprimitive (hwf : P.c.env.constants.WF)
    {n : Name} {ci : ConstantInfo} (h : P.ctorEnv.find? n = some ci)
    (hold : P.c.env.find? n = none) :
    ¬ Kernel.Environment.primitives.contains n := by
  have hwfH := P.headers.installed.targetMapWF hwf
  rcases P.constructors.declared.installed.entryOrigin hwfH h with hH | ⟨entry, hentry, hname, -⟩
  · rcases P.headers.installed.entryOrigin hwf hH with h0 | ⟨entry, hentry, hname, -⟩
    · rw [hold] at h0; cases h0
    · rw [hname]; exact P.headers.installed.entryNonprimitive hentry
  · rw [hname]; exact P.constructors.declared.installed.entryNonprimitive hentry

end Production

/-- The checker's own primitive constants are reserved names. -/
theorem checkerPrimNames_primitive : ∀ n ∈ checkerPrimNames, Kernel.Environment.primitives.contains n := by
  intro n hn
  simp only [checkerPrimNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  simp only [Kernel.Environment.primitives, NameSet.ofList]
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [NameSet.contains]

/-! ### The head set of a nested run -/

section Heads

/-- In a duplicate-free list of family names, no family name is a constructor
name. -/
theorem familyName_not_mem_ctorNames :
    ∀ {L : List VInductiveType}, (InductiveSignature.familyNames L).Nodup →
      ∀ t ∈ L, t.name ∉ L.flatMap (fun t => t.ctors.map (·.name))
  | [], _, _, h => by simp at h
  | t0 :: L, hnd, t, ht => by
    simp only [InductiveSignature.familyNames, List.flatMap_cons] at hnd
    have hnd' := List.nodup_append.1 hnd
    have hL : (InductiveSignature.familyNames L).Nodup := hnd'.2.1
    have hsub : ∀ x ∈ L.flatMap (fun t => t.ctors.map (·.name)),
        x ∈ InductiveSignature.familyNames L := by
      intro x hx
      obtain ⟨t', ht', hx⟩ := List.mem_flatMap.1 hx
      exact List.mem_flatMap.2 ⟨t', ht', List.mem_cons_of_mem _ hx⟩
    simp only [List.flatMap_cons, List.mem_append, not_or]
    rcases List.mem_cons.1 ht with rfl | ht
    · refine ⟨fun h => (List.nodup_cons.1 hnd'.1).1 h, fun h => ?_⟩
      exact hnd'.2.2 _ List.mem_cons_self _ (hsub _ h) rfl
    · refine ⟨fun h => ?_, familyName_not_mem_ctorNames hL t ht⟩
      exact hnd'.2.2 _ (List.mem_cons_of_mem _ h) _
        (List.mem_flatMap.2 ⟨t, ht, List.mem_cons_self⟩) rfl

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {safety : DefinitionSafety} {outEnv : Environment}

/-- The constructor names of the source families of a nested run. Their
lowered types mention auxiliary families, so they are heads of the type
checker's parameter-uniformity invariant. -/
def NestedRun.mainCtorNames
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) : List Name :=
  (E.lowered.loweredDecl.types.take sourceDecl.types.length).flatMap
    fun t => t.ctors.map (·.name)

/-- The head set of the type checker's parameter-uniformity invariant at the recursor
pass: the auxiliary families and constructors together with the source
constructors. -/
def NestedRun.uniformHeads
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) : List Name :=
  E.auxHeads ++ E.mainCtorNames

theorem NestedRun.uniformHeads_subset
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) {n : Name}
    (hn : n ∈ E.uniformHeads) :
    n ∈ InductiveSignature.familyNames E.lowered.loweredDecl.types := by
  rcases List.mem_append.1 hn with hn | hn
  · exact familyNames_drop_subset hn
  · obtain ⟨t, ht, hn⟩ := List.mem_flatMap.1 hn
    exact List.mem_flatMap.2 ⟨t, List.mem_of_mem_take ht, List.mem_cons_of_mem _ hn⟩

theorem NestedRun.auxHeads_subset_uniformHeads
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) :
    ∀ c ∈ E.auxHeads, c ∈ E.uniformHeads := fun _ h => List.mem_append_left _ h

/-- Every lowered constructor name is a head. -/
theorem NestedRun.ctorName_mem_uniformHeads
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    {t : VInductiveType} (ht : t ∈ E.lowered.loweredDecl.types)
    {c : VConstVal} (hc : c ∈ t.ctors) : c.name ∈ E.uniformHeads := by
  have hsplit := List.take_append_drop sourceDecl.types.length E.lowered.loweredDecl.types
  rw [← hsplit] at ht
  rcases List.mem_append.1 ht with ht | ht
  · exact List.mem_append_right _
      (List.mem_flatMap.2 ⟨t, ht, List.mem_map_of_mem hc⟩)
  · exact List.mem_append_left _
      (List.mem_flatMap.2 ⟨t, ht, List.mem_cons_of_mem _ (List.mem_map_of_mem hc)⟩)

/-- A source family name is not a head. -/
theorem NestedRun.mainFamily_not_mem_uniformHeads
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (hnodup : (InductiveSignature.familyNames E.lowered.loweredDecl.types).Nodup)
    {t : VInductiveType} (ht : t ∈ E.lowered.loweredDecl.types.take sourceDecl.types.length) :
    t.name ∉ E.uniformHeads := by
  have hsplit := List.take_append_drop sourceDecl.types.length E.lowered.loweredDecl.types
  have hnd := hnodup
  rw [← hsplit, InductiveSignature.familyNames, List.flatMap_append] at hnd
  have hnd' := List.nodup_append.1 hnd
  intro hmem
  rcases List.mem_append.1 hmem with hmem | hmem
  · exact hnd'.2.2 _ (List.mem_flatMap.2 ⟨t, ht, List.mem_cons_self⟩) _ hmem rfl
  · exact familyName_not_mem_ctorNames hnd'.1 t ht hmem

end Heads

/-! ### Lowered constructor types are head types -/

section CtorTypes

/-- The lowering of a constructor closes its opened parameters with
`LocalContext.mkForall`, so its type is a head type. -/
theorem ConstructorLowering.Resolved.headType {heads : List Name} {ls : List Level}
    {env : Environment} {params : Array Expr} {nparams : Nat}
    {finalResult : Lean4Lean.ElimNestedInductive.Result}
    {source : Constructor} {state : Lean4Lean.ElimNestedInductive.State}
    {out : Constructor × Lean4Lean.ElimNestedInductive.State}
    (H : ConstructorLowering.Resolved env params nparams finalResult source state out)
    (hkeys : ∀ auxName nested, finalResult.aux2nested.find? auxName = some nested →
      auxName ∈ heads)
    (hsource : source.type.AvoidsConsts heads) (hlvls : state.lvls = ls) :
    HeadType heads nparams ls out.1.type := by
  obtain ⟨lctx, tail, As, lowered, openedState, Hopen, -, Hselection, hnodup, -, -, -,
    hsize, Hmap, htype⟩ := H.mapped
  have hopenedLvls : openedState.lvls = ls := by
    rw [← Hmap.lvls, H.lvls, hlvls]
  have Hlowered := Hmap.paramUniform hkeys (Hopen.tailAvoidsConsts hsource) hopenedLvls
  rw [htype, ← hsize]
  refine Expr.ParamUniform.mkForall_headType Hlowered
    (by have h := congrArg Array.toList Hselection.expressions; simpa using h)
    hnodup fun x hx => ?_
  obtain ⟨index, name, type, bi, kind, hfind⟩ := Hselection.declarations x hx
  exact ⟨index, x, name, type, bi, kind, hfind⟩

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}

/-- The constructor names of the lowered declaration are absent from the
environment in which its constructor types are translated (the source
environment extended by the lowered family headers). -/
theorem NestedRun.ctorNames_fresh_headerVEnv
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv)
    (hnodup : (InductiveSignature.familyNames E.lowered.loweredDecl.types).Nodup)
    {t : VInductiveType} (ht : t ∈ E.lowered.loweredDecl.types)
    {c : VConstVal} (hc : c ∈ t.ctors) :
    E.lowered.headers.context.venv.constants c.name = none := by
  have hcore := E.lowered.constructors.core
  have hadded := hcore.typesAdded
  have hwfP : E.lowered.c.env.constants.WF := by
    rw [E.lowered_c, E.context_env]; exact (wf.tr (safety := .unsafe)).map_wf
  have hfreshK : E.lowered.c.env.find? c.name = none :=
    E.lowered.fresh_familyNames hwfP
      (List.mem_flatMap.2 ⟨t, ht, List.mem_cons_of_mem _ (List.mem_map_of_mem hc)⟩)
  have hne : ∀ ci ∈ E.lowered.loweredDecl.typeConstants, ci.name ≠ c.name := by
    intro ci hci heq
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hci
    exact familyName_not_mem_ctorNames hnodup t' ht'
      (by rw [show t'.toVConstVal.name = t'.name from rfl] at heq; rw [heq]
          exact List.mem_flatMap.2 ⟨t, ht, List.mem_map_of_mem hc⟩)
  rw [VEnv.addConstVals_constants_of_forall_ne hadded hne]
  cases hv : E.lowered.initialEnv.constants c.name with
  | none => rfl
  | some ci =>
    exfalso
    rw [E.lowered_initialEnv] at hv
    obtain ⟨ci', hfind, -⟩ :=
      (wf.tr (safety := if isUnsafe then .unsafe else .safe)).find?_iff.2 ⟨ci, hv⟩
    rw [E.lowered_c, E.context_env] at hfreshK
    rw [hfreshK] at hfind; cases hfind

/-- **Every lowered constructor type is a head type for the run's head set**
(before level instantiation). -/
theorem NestedRun.ctorTypes_headType
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∀ owner ∈ E.lowered.indTypes.toList, ∀ ctor ∈ owner.ctors,
      HeadType E.uniformHeads nparams (lparams.map Level.param) ctor.type := by
  obtain ⟨-, -, -, -, -, -, hkeys, hnodupAll⟩ := E.auxHeadsFacts wf Hsources
  have hnodup : (InductiveSignature.familyNames E.lowered.loweredDecl.types).Nodup :=
    (List.nodup_append.1 hnodupAll).1
  have hmaps := E.loweredFamilyMappings wf Hsources
  intro owner howner ctor hctor
  -- head type for the auxiliary heads
  have hAux : HeadType E.auxHeads nparams (lparams.map Level.param) ctor.type := by
    have howner' : owner ∈ result.types := by
      rw [E.lowered_indTypes] at howner; simpa using howner
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 howner'
    obtain ⟨source, st, ls, havoid, -, hlv, M⟩ := hmaps i hi
    obtain ⟨src, hsrc, before, after, hbefore, Mc⟩ := M.constructors.forall_mem ctor hctor
    exact Mc.headType hkeys (havoid src hsrc) (hbefore.trans hlv)
  -- the constructor type avoids the source constructor names
  have hcore := E.lowered.constructors.core
  obtain ⟨t, ht, HT⟩ := Lean4Lean.List.Forall₂.forall_exists_l hcore.types owner howner
  obtain ⟨c', hc', HC⟩ := Lean4Lean.List.Forall₂.forall_exists_l HT.ctors ctor hctor
  have hfresh : ∀ n ∈ E.mainCtorNames, E.lowered.headers.context.venv.constants n = none := by
    intro n hn
    obtain ⟨t'', ht'', hn⟩ := List.mem_flatMap.1 hn
    obtain ⟨c'', hc'', rfl⟩ := List.mem_map.1 hn
    exact E.ctorNames_fresh_headerVEnv wf hnodup (List.mem_of_mem_take ht'') hc''
  have havoid : ctor.type.AvoidsConsts E.mainCtorNames :=
    checkPositivityStep.TrExprS.sourceAvoidsFresh hfresh HC.type
  exact hAux.grow (E.auxHeads_subset_uniformHeads) (fun c hc hnot => by
    rcases List.mem_append.1 hc with h | h
    · exact absurd h hnot
    · exact h) havoid

theorem LeadingForalls.mkForall_selection {lctx : LocalContext} {As : Array Expr}
    (S : CDeclArray lctx As) (b : Expr) :
    Expr.LeadingForalls As.size (lctx.mkForall As b) (b.abstractN S.fvars) := by
  obtain ⟨fvars, hAs, hdecl⟩ := S
  subst hAs
  simp only [LocalContext.mkForall, List.size_toArray, List.length_map]
  rw [LocalContext.mkBinding_eqN]
  exact Expr.LeadingForalls.mkBindingListN (fun x hx => by
    obtain ⟨index, name, type, bi, kind, hfind⟩ := hdecl x hx
    exact ⟨index, x, name, type, bi, kind, hfind⟩) b

/-- **Auxiliary family types are parameter telescopes**: the
lowering builds them as `LocalContext.mkForall As _` over the `nparams`
lowering parameters. -/
theorem NestedRun.generatedFamilyType_forall
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∀ i (hi : i < result.types.length), sourceTypes.length ≤ i →
      ∃ body, Expr.LeadingForalls nparams result.types[i].type body := by
  obtain ⟨-, -, -, -, -, -, -, hparamsSize, -, -⟩ := E.restorationTablesRestoring wf Hsources
  let safety := if isUnsafe then DefinitionSafety.unsafe else .safe
  let P := E.lowered
  have henv : P.c.env = sourceProdEnv := E.lowered_env
  have hlparams : P.c.lparams = lparams := E.lowered_lparams
  have hnparams : P.nparams = nparams := E.lowered_nparams
  have hinitial : P.initialEnv = ves.venv safety := by
    simpa only [safety] using E.lowered_initialEnv
  have hisUnsafe : P.isUnsafe = isUnsafe := E.lowered_isUnsafe_source
  have HcP : ContextWF P.c := E.loweredContextWF
  let initialState := E.initialState
  have Hlower : NestedLoweringOutputClosed P.c.env
      E.validationFuel.inductiveFuel P.nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result := E.loweringAtContext
  rcases Hlower with ⟨finalState, Hrun, Hcache, Hparams⟩
  let Hpack := E.phases
  let R := Hpack.constructors
  let Hprod := Hpack.recursors
  have Hsource : TrInductDeclCore P.initialEnv P.c.lparams P.nparams
      sourceTypes P.isUnsafe sourceDecl E.sourceCore.envTypes
        E.sourceCore.envCtors := by
    simpa only [hinitial, hlparams, hnparams, hisUnsafe, safety,
      E.sourceCoreDecl_eq] using E.sourceCore.core
  have Htarget : TrInductDeclCore P.initialEnv P.c.lparams P.nparams
      result.types P.isUnsafe P.loweredDecl Hpack.headers.context.venv
        R.declared.venvCtors := R.core
  have wfP : ves.WF P.c.env := by
    simpa only [henv] using wf
  have HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst P.initialEnv P.c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (P.loweredDecl.types.take sourceTypes.length) := by
    simpa only [hinitial, hlparams, safety] using E.sourceCore.sourceHeaders
  have HsourceAdded : P.initialEnv.addConstVals
      ((P.loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some E.sourceCore.envTypes := by
    simpa only [hinitial, safety] using E.sourceCore.sourceAdded
  have HbaseWF : P.initialEnv.WF := by
    simpa only [hinitial, safety] using (wf.tr (safety := safety)).wf
  have HsourceTypesWF : E.sourceCore.envTypes.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF Hsource HbaseWF
  have Htranslations : ClosedNestedOccurrenceTypings
      E.sourceCore.envTypes P.c.lparams result E.auxiliarySelection := by
    rw [← E.auxiliaryVEnv_eq_sourceCore]
    simpa only [hlparams] using E.auxiliaryTranslations
  have hempty : initialState.nestedAux = #[] := rfl
  rcases Hrun.auxiliaryFamilySources Hcache Hparams wfP
      hinitial HcP Hprod Hsources HsourceHeaders HsourceAdded HsourceTypesWF
      hempty E.auxiliarySelection Htranslations Htarget with ⟨N, -⟩
  intro i hi hge
  obtain ⟨k, rfl⟩ : ∃ k, i = sourceTypes.length + k := ⟨i - sourceTypes.length, by omega⟩
  have hloweredLength : result.types.length = P.loweredDecl.types.length :=
    TrInductDeclCore.types_length Htarget
  have hgeneratedLength := N.length
  have hgen : k < N.generated.length := by omega
  have htarget : sourceTypes.length + k < P.loweredDecl.types.length := by omega
  rcases N.sourceAt k hgen hi htarget with ⟨Horigin, -, -⟩
  obtain ⟨tail, -, htype⟩ := Horigin.generated.built.opening
  have hT : result.types[sourceTypes.length + k].type =
      Horigin.generated.data.type.type := by
    rw [Horigin.lowered.type]; exact congrArg InductiveType.type Horigin.generated.family_eq
  rw [hT, htype]
  have hsize : Horigin.generated.As.size = nparams := by
    rw [Horigin.generated.built.arity, hparamsSize, Hrun.resultNParams, hnparams]
  have hl := LeadingForalls.mkForall_selection Horigin.generated.selection
    (tail.instantiateRevRange 0 Horigin.generated.nestedNParams Horigin.generated.args)
  rw [hsize] at hl
  exact ⟨_, hl⟩

end CtorTypes

/-! ### The environment condition at the recursor pass -/

section RunEnv

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}

/-- The recursor pass runs in the constructor-phase environment. -/
theorem NestedRun.recursorPassEnv
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv) :
    E.lowered.recursors.localContext.env = E.lowered.ctorEnv :=
  E.lowered.recursors.localExtends.env_eq

theorem NestedRun.lowered_c_env
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv) :
    E.lowered.c.env = sourceProdEnv := by
  rw [E.lowered_c, E.context_env]

theorem NestedRun.lowered_c_lparams
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv) :
    E.lowered.c.lparams = lparams := by
  rw [E.lowered_c, E.context_lparams]

/-- The heads are absent from the source kernel environment. -/
theorem NestedRun.uniformHeads_fresh
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) :
    ∀ n ∈ E.uniformHeads, sourceProdEnv.find? n = none := by
  intro n hn
  have hwfP : E.lowered.c.env.constants.WF := by
    rw [E.lowered_c_env]; exact (wf.tr (safety := .unsafe)).map_wf
  have := E.lowered.fresh_familyNames hwfP (E.uniformHeads_subset hn)
  rwa [E.lowered_c_env] at this

/-- Lookups of base constants persist into the constructor-phase environment. -/
theorem NestedRun.ctorEnv_preserves
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) {n : Name} {ci : ConstantInfo}
    (h : sourceProdEnv.find? n = some ci) : E.lowered.ctorEnv.find? n = some ci := by
  have hwfP : E.lowered.c.env.constants.WF := by
    rw [E.lowered_c_env]; exact (wf.tr (safety := .unsafe)).map_wf
  rw [← E.lowered_c_env] at h
  exact E.lowered.constructors.declared.installed.preservesSourceFind
    (E.lowered.headers.installed.targetMapWF hwfP)
    (E.lowered.headers.installed.preservesSourceFind hwfP h)

/-- Family header types are translated in the source environment. -/
theorem NestedRun.familyType_tr
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {owner : InductiveType} (howner : owner ∈ E.lowered.indTypes.toList) :
    ∃ e', TrExprS (ves.venv (if isUnsafe then .unsafe else .safe)) lparams [] owner.type e' := by
  obtain ⟨t, -, HT⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    E.lowered.constructors.core.types owner howner
  have h := HT.header.type
  rw [E.lowered_initialEnv, E.lowered_c_lparams] at h
  exact ⟨_, h⟩

/-- Constructor types are translated in the header environment, and their
names are lowered constructor names. -/
theorem NestedRun.ctorType_tr
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {owner : InductiveType} (howner : owner ∈ E.lowered.indTypes.toList)
    {ctor : Constructor} (hctor : ctor ∈ owner.ctors) :
    (∃ e', TrExprS E.lowered.headers.context.venv E.lowered.c.lparams [] ctor.type e') ∧
      ∃ t ∈ E.lowered.loweredDecl.types, ∃ c ∈ t.ctors, c.name = ctor.name := by
  obtain ⟨t, ht, HT⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    E.lowered.constructors.core.types owner howner
  obtain ⟨c', hc', HC⟩ := Lean4Lean.List.Forall₂.forall_exists_l HT.ctors ctor hctor
  exact ⟨⟨_, HC.type⟩, t, ht, c', hc', HC.name⟩

/-- A family of the run whose name is a head is an auxiliary family, so its
type is a head type. -/
theorem NestedRun.familyType_headType
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {owner : InductiveType} (howner : owner ∈ E.lowered.indTypes.toList)
    (hname : owner.name ∈ E.uniformHeads) :
    HeadType E.uniformHeads nparams (lparams.map Level.param) owner.type := by
  obtain ⟨-, -, -, -, -, -, -, hnodupAll⟩ := E.auxHeadsFacts wf Hsources
  have hnodup : (InductiveSignature.familyNames E.lowered.loweredDecl.types).Nodup :=
    (List.nodup_append.1 hnodupAll).1
  have hcore := E.lowered.constructors.core
  have hlen := Lean4Lean.List.Forall₂.length_eq hcore.types
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 howner
  have hiD : i < E.lowered.loweredDecl.types.length := by omega
  have HT := Lean4Lean.List.forall₂_getElem hcore.types i hi hiD
  have hsrcLen : sourceTypes.length = sourceDecl.types.length := by
    have := TrInductDeclCore.types_length E.sourceCore.core
    rwa [E.sourceCoreDecl_eq] at this
  have hge : sourceTypes.length ≤ i := by
    refine Nat.le_of_not_gt fun hlt => E.mainFamily_not_mem_uniformHeads hnodup
      (t := E.lowered.loweredDecl.types[i]) ?_ ?_
    · rw [List.mem_iff_getElem]
      refine ⟨i, ?_, ?_⟩
      · rw [List.length_take]; omega
      · rw [List.getElem_take]
    · have hn : E.lowered.loweredDecl.types[i].name = E.lowered.indTypes.toList[i].name :=
        HT.header.name
      rw [hn]; exact hname
  have hres : E.lowered.indTypes.toList = result.types := by
    rw [E.lowered_indTypes]
  have hiR : i < result.types.length := by rw [← hres]; exact hi
  obtain ⟨body, hl⟩ := E.generatedFamilyType_forall wf Hsources i hiR hge
  have heq : E.lowered.indTypes.toList[i] = result.types[i] := List.getElem_of_eq hres hi
  obtain ⟨e', htr⟩ := E.familyType_tr (List.getElem_mem hi)
  rw [heq] at htr ⊢
  have havoid : result.types[i].type.AvoidsConsts E.uniformHeads :=
    avoids_of_tr wf (E.uniformHeads_fresh wf) _ htr
  exact ⟨body, hl, Expr.ParamUniformBV.of_avoidsConsts (hl.avoidsConsts havoid) 0⟩

/-- **The environment condition of the type checker's parameter-uniformity invariant
holds in the environment of the recursor pass** of a validated nested
run, for the head set `E.uniformHeads` (auxiliary families and constructors, and
the source constructors), `nparams` parameters and the declaration's level
parameters.

The constants the checker builds on its own are not heads: the reserved ones
(`checkerPrimNames`) because every head was installed by a `checkName` without
primitive permission (`LoweredRun.nonprimitive_familyNames`);
the other string-literal constants (`strLitNames`) because, once the
environment declares `Char.ofNat` and `String.ofList`, these two are base
constants (they are reserved, so the run did not install them), and then
`HasPrimitives` of the source model forces `String`, `Char`, `List.nil` and
`List.cons` to be base constants as well, while every head is fresh
(`uniformHeads_fresh`). -/
theorem NestedRun.envParamUniform
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    EnvParamUniform E.lowered.ctorEnv E.uniformHeads nparams (lparams.map Level.param) := by
  have hfresh := E.uniformHeads_fresh wf
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
  have hfreshN : ∀ {n ci}, sourceProdEnv.find? n = some ci → n ∉ E.uniformHeads :=
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
    exact E.lowered.nonprimitive_familyNames (E.uniformHeads_subset hmem)
      (checkerPrimNames_primitive n hn)
  case strs =>
    rintro ⟨⟨ci₁, h₁⟩, ⟨ci₂, h₂⟩⟩ n hn hmem
    have hold : ∀ {p ci}, Kernel.Environment.primitives.contains p →
        E.lowered.ctorEnv.find? p = some ci → ∃ ci', sourceProdEnv.find? p = some ci' := by
      intro p ci hp h
      cases h0 : sourceProdEnv.find? p with
      | some ci' => exact ⟨ci', rfl⟩
      | none =>
        refine absurd hp (E.lowered.ctorEnv_new_nonprimitive hwfP h ?_)
        rw [E.lowered_c_env]; exact h0
    obtain ⟨_, hc₁⟩ := hold (checkerPrimNames_primitive _ (by simp [checkerPrimNames])) h₁
    obtain ⟨_, hc₂⟩ := hold (checkerPrimNames_primitive _ (by simp [checkerPrimNames])) h₂
    have htr := wf.tr (safety := .unsafe)
    obtain ⟨_, hv₁, -⟩ := htr.find? hc₁ DefinitionSafety.unsafe_le
    obtain ⟨_, hv₂, -⟩ := htr.find? hc₂ DefinitionSafety.unsafe_le
    have hord : (ves.venv .unsafe).Ordered := htr.wf.ordered
    have hprimU : (ves.venv .unsafe).HasPrimitives := wf.hasPrimitives (safety := .unsafe)
    have hlits : (ves.venv .unsafe).ContainsLits (.strVal "") := ⟨⟨_, hv₁⟩, ⟨_, hv₂⟩⟩
    have hcontains : (ves.venv .unsafe).contains n := by
      simp only [strLitNames, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | hn
      · obtain ⟨_, H⟩ := (TrExprS.trLiteral hord hprimU (.strVal "") hlits
          (Us := []) (Δ := [])).2.isType hord trivial
        obtain ⟨_, h1, -⟩ := H.const_inv hord trivial
        exact ⟨_, h1⟩
      · exact unreservedLiteralConstructorsOfStringOfList hprimU hord hlits.2 n
          (by simpa [checkPositivityStep.unreservedLiteralConstructorNames] using hn)
    obtain ⟨_, hfind, -⟩ := htr.find?_iff.2 hcontains
    rw [hfresh n hmem] at hfind; cases hfind
  case type_avoids =>
    intro n ci h hn
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, rfl, htype, -⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, rfl, htype, -⟩
    · exact (old_type_avoids wf hfresh hold).1
    · show info.type.AvoidsConsts _
      rw [htype]
      obtain ⟨e', htr⟩ := E.familyType_tr hmem
      exact avoids_of_tr wf hfresh _ htr
    · exfalso
      obtain ⟨-, t, ht, c, hc, hcn⟩ := E.ctorType_tr howner hctor
      exact hn (hcn ▸ E.ctorName_mem_uniformHeads ht hc)
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
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, rfl, htype, hlp⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, rfl, htype, hlp⟩
    · exact absurd hn (hfreshN hold)
    · show HeadType _ _ _ (info.type.instantiateLevelParams info.levelParams _)
      rw [htype, hlp]
      exact (E.familyType_headType wf Hsources hmem hn).instantiateLevelParams_self
    · show HeadType _ _ _ (info.type.instantiateLevelParams info.levelParams _)
      rw [htype, hlp]
      exact (E.ctorTypes_headType wf Hsources owner howner ctor hctor).instantiateLevelParams_self
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

end RunEnv

/-- **`whnf` preserves parameter uniformity in a recursor context.** The lifted
`TypeChecker.whnf` call of the inductive checker, run from the empty checker
state, maps a parameter-uniform input (with projections respecting `projAvoidsHeads`)
whose free variables lie in a parameter-uniform scope to an output with the same property.
This is `TypeChecker.whnf.paramUniform` transported along the same lift as
`whnfInRecursorContext.levelsWF`. -/
theorem whnfInRecursorContext.paramUniformIn
    {c : AddInductive.Context} {recLparams : List Name}
    (Hc : RecursorContextWF c recLparams) {e : Expr}
    {e₀ : VExpr} (hn : TrExprS Hc.venv recLparams Hc.chk.vlctx e e₀)
    {heads : List Name} {As : List Expr} {ls : List Level} {P : FVarId → Prop}
    (henv : EnvParamUniform c.env heads As.length ls)
    (hAs : TypeChecker.UngeneratedParams `_kernel_fresh As)
    (hscope : Hc.ParamUniformScope c.env heads As ls P)
    (hin : e.ParamUniformIn c.env heads As ls) (hP : FVarsIn P e) :
    ((monadLift (TypeChecker.whnf e) : AddInductive.M Expr) c).WF fun e₁ =>
      e₁.ParamUniformIn c.env heads As ls := by
  -- the run is verified in the checker context, whose parameter-uniform scope is the part
  -- of `P` among the checker variables
  let P₀ : FVarId → Prop := fun fv => P fv ∧ fv ∈ Hc.chk.vlctx.fvars
  have hs : Hc.checkTC.ParamUniformScope `_kernel_fresh heads As ls P₀ := by
    refine ⟨henv, hAs, IsFVarUpSet.and _ (Hc.check.embed.isFVarUpSet hscope.1)
      (IsFVarUpSet.fvars Hc.check.wf.tr.wf.fvwf), ?_⟩
    intro fv d ⟨hPfv, _⟩ hfind
    change Hc.chk.lctx.find? fv = some d at hfind
    rw [Hc.check.lctx_eq] at hfind
    obtain ⟨d', hd', hdeq⟩ := Hc.check.sub fv d hfind
    have hmain : Hc.mlctx.lctx.find? fv = some d' := by rw [Hc.lctx_eq]; exact hd'
    have h' := hscope.2 fv d' hPfv hmain
    have e1 : ∀ x : LocalDecl, (x.setIndex 0).type = x.type := by
      intro x; cases x <;> rfl
    have e2 : ∀ x : LocalDecl, (x.setIndex 0).value? true = x.value? true := by
      intro x; cases x with
      | cdecl => rfl
      | ldecl _ _ _ _ _ nd => cases nd <;> rfl
    have htype : d'.type = d.type := by rw [← e1 d', hdeq, e1 d]
    have hvalue : d'.value? true = d.value? true := by rw [← e2 d', hdeq, e2 d]
    exact ⟨htype ▸ h'.1, fun v hv => h'.2 v (hvalue ▸ hv)⟩
  have hP₀ : FVarsIn P₀ e := by
    have hc := (fvarsIn_iff.mp hn.fvarsIn).1
    exact fvarsIn_iff.mpr ⟨fun fv hfv => ⟨(fvarsIn_iff.mp hP).1 fv hfv, hc fv hfv⟩,
      (fvarsIn_iff.mp hP).2⟩
  have Hx : TypeChecker.M.WF Hc.checkTC {}
      (TypeChecker.whnf e) (fun e₁ _ => e₁.ParamUniformIn c.env heads As ls) :=
    (TypeChecker.whnf.paramUniform hn).mono fun e₁ _ _ h => h.2 heads As ls P₀ hs hin hP₀
  exact liftTypeChecker.recursorWF Hc Hx

end VerifyInductive
end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- `whnf` facts from the environment condition and parameters that the
checker's name generator never produces. -/
theorem WhnfPreservesParamUniform.of_env {heads : List Name} {params : List Expr} {ls : List Level}
    {env : Environment} (henv : EnvParamUniform env heads params.length ls)
    (hparams : TypeChecker.UngeneratedParams `_kernel_fresh params) :
    WhnfPreservesParamUniform heads params ls env where
  whnf Hc _ _ _ hc hn hscope hP hin hrun := by
    subst hc
    obtain ⟨_, hn⟩ := hn
    exact whnfInRecursorContext.paramUniformIn Hc hn henv hparams hscope hin hP _ hrun

section Run

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}

/-- The parameters of the run are free variables of its recursor context,
which never carry names of the type checker's name generator. -/
theorem NestedRun.paramsUngeneratedParams
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv) :
    TypeChecker.UngeneratedParams `_kernel_fresh E.lowered.stats.params.toList := by
  intro a ha
  obtain ⟨fv, rfl, hmem⟩ :=
    FVarArrayIn.fvar_of_mem E.lowered.recursors.params (Array.mem_toList_iff.1 ha)
  refine ⟨fv, rfl, fun i heq => ?_⟩
  have hlctx : fv ∈ E.lowered.recursors.localContext.lctx.fvars :=
    E.lowered.recursors.params.members fv hmem
  have hv : fv ∈ E.lowered.recursors.recursorWF.mlctx.vlctx.fvars := by
    rw [← E.lowered.recursors.recursorWF.mlctx_wf.tr.fvars_eq,
      E.lowered.recursors.recursorWF.lctx_eq]
    exact hlctx
  have := E.lowered.recursors.recursorWF.kernelFresh fv hv i heq
  exact Nat.not_lt_zero _ this

/-- **`whnf` preserves parameter uniformity in a validated nested run**, at the head
set `E.uniformHeads` (auxiliary families and constructors, and the source
constructors), the run's parameters and the declaration's levels, in the
environment of the recursor pass. -/
theorem NestedRun.whnfPreservesParamUniform
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    WhnfPreservesParamUniform E.uniformHeads E.lowered.stats.params.toList (lparams.map Level.param)
      E.lowered.recursors.localContext.env := by
  refine .of_env ?_ E.paramsUngeneratedParams
  have hlen : E.lowered.stats.params.toList.length = nparams := by
    obtain ⟨_, Hrun, _, _⟩ := E.lowering
    rw [Array.length_toList, E.statsParamsSize, Hrun.resultNParams]
  rw [E.recursorPassEnv, hlen]
  exact E.envParamUniform wf Hsources

/-- **The non-`whnf` parameter-uniformity inputs of a validated nested run**, at the
head set `E.uniformHeads`, with the projection condition at the environment of the
recursor pass, derived from the run alone:

* parameter declarations: translated in the source environment, where the
  heads are fresh and every registered projection names a base structure
  (`RecursorConstruction.paramDecls_paramUniformIn`, `projParamUniformIn_of_old`);
* family headers: translated in the source environment
  (`NestedRun.familyType_tr`);
* constructor types: head types for `E.uniformHeads`
  (`NestedRun.ctorTypes_headType`), translated in the header
  environment, whose projections are the source environment's;
* recursor names: distinct from the family and constructor names. -/
theorem NestedRun.paramUniformDeclarations_of
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    E.lowered.recursors.toRecursorConstruction.ParamUniformDeclarations
      E.uniformHeads := by
  let sf : DefinitionSafety := if isUnsafe then .unsafe else .safe
  have hfresh := E.uniformHeads_fresh wf
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
  · refine E.lowered.recursors.toRecursorConstruction.paramDecls_paramUniformIn
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
    refine ⟨?_, projsOK_of_tr_sub wf hpres hfresh sf hheaderV hheaderSub htr⟩
    obtain ⟨body, hl, hb⟩ := E.ctorTypes_headType wf Hsources _ (hmem i hi) ctor hctor
    rw [E.statsLevels, E.statsParamsSize, hnp]
    exact ⟨body, hl.leadingBinders, hb⟩
  · exact E.lowered.recursors.toRecursorConstruction.recursorNames_not_mem
      (fun _ hh => E.uniformHeads_subset hh) hnodup

/-- **Parameter uniformity of the lowered recursor type and rule right-hand sides of a
validated nested run, at the checker's head set `E.uniformHeads`**:
`recursorParamUniform` with its two hypotheses discharged by
`paramUniformDeclarations_of` and `whnfPreservesParamUniform`. -/
theorem NestedRun.recursorParamUniform_uniformHeads
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (owner : Fin E.lowered.recursors.generationSignature.families.size)
    {auxRec : NameMap Name} {allIndNames : List Name}
    {stepSource stepTarget : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv auxRec allIndNames
      (E.lowered.recursors.canonicalGeneration.recursorName owner)
      stepSource stepTarget) :
    Expr.ParamUniformTele E.uniformHeads result.nparams (lparams.map Level.param)
        Hstep.oldInfo.type ∧
      ∀ rule ∈ Hstep.oldInfo.rules,
        Expr.ParamUniformTele E.uniformHeads result.nparams (lparams.map Level.param) rule.rhs :=
  E.recursorParamUniform (E.paramUniformDeclarations_of wf Hsources) (E.whnfPreservesParamUniform wf Hsources)
    owner Hstep

/-- **Parameter uniformity of the lowered recursor type and rule right-hand sides of a
validated nested run**, at the auxiliary heads `E.auxHeads`: for every
generated owner and every executable restoration step at the owner's lowered
recursor name, the stored recursor type and every stored rule right-hand side
are closed parameter telescopes of `result.nparams` binders whose body is
parameter-uniform in bound-variable form for the auxiliary heads at the levels
`lparams.map Level.param`.

The proof runs the parameter-uniformity chain at the checker's head set `E.uniformHeads`
(`recursorParamUniform_uniformHeads`) and drops the source constructors with
`ParamUniformTele.shrink`. -/
theorem NestedRun.recursorParamUniform_of_wfCore
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (owner : Fin E.lowered.recursors.generationSignature.families.size)
    {auxRec : NameMap Name} {allIndNames : List Name}
    {stepSource stepTarget : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv auxRec allIndNames
      (E.lowered.recursors.canonicalGeneration.recursorName owner)
      stepSource stepTarget) :
    Expr.ParamUniformTele E.auxHeads result.nparams (lparams.map Level.param)
        Hstep.oldInfo.type ∧
      ∀ rule ∈ Hstep.oldInfo.rules,
        Expr.ParamUniformTele E.auxHeads result.nparams (lparams.map Level.param) rule.rhs := by
  obtain ⟨htype, hrules⟩ := E.recursorParamUniform_uniformHeads wf Hsources owner Hstep
  exact ⟨htype.shrink E.auxHeads_subset_uniformHeads,
    fun rule hrule => (hrules rule hrule).shrink E.auxHeads_subset_uniformHeads⟩

end Run

end VerifyInductive
end Lean4Lean
