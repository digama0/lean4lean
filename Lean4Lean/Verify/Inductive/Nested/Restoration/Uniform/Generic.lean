import Lean4Lean.Verify.Inductive.Nested.Restoration.Uniform.Recursors
import Lean4Lean.Verify.TypeChecker.ParamUniformWHNF

/-! # Parameter uniformity: generic lemmas (owner: Restoration-A)

The parts of the source branch's `Nested/Restoration/Uniform/Whnf.lean` that do not read a
nested run: syntactic lemmas on `LeadingForalls`, `ParamUniformBV`/`ParamUniformTele` (`grow`,
`shrink`, level instantiation), and the
lift of `TypeChecker.whnf.paramUniform` to the inductive checker's recursor context
(`whnfInRecursorContext.paramUniformIn`). The `NestedRun` instances follow in
`Uniform/Whnf.lean`. -/
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
