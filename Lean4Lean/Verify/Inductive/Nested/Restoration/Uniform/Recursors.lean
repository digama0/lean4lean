import Lean4Lean.Verify.Inductive.Recursor.Installation
import Lean4Lean.Verify.Inductive.Recursor.Check
import Lean4Lean.Verify.Inductive.Constructor.Positivity
import Lean4Lean.Verify.ExprParamUniform
import Lean4Lean.Verify.Inductive.Recursor.Binders.FieldTypes
import Lean4Lean.Verify.Inductive.Recursor.Signature.HypothesisArgumentUniverses
import Lean4Lean.Verify.ParamUniformEnv

/-! # Parameter uniformity of generated recursor types and rule right-hand sides

The lowered recursor types and rule right-hand sides of a nested run are restored by
`restoreNested`, which agrees with the abstract restoration exactly when every node headed
by an auxiliary family or constructor (a *head occurrence*) has the parameter variables as its
first `nparams` arguments and the declaration's level parameters as its levels
(`Expr.ParamUniform`, `Lean4Lean/Verify/ExprParamUniform.lean`). This file proves that
the executable's generated recursors are parameter-uniform:

* `RecursorConstruction.recursorTypeParamUniform` and `ruleRhsParamUniform`: for every owner,
  the recursor type `(lctx.mkForall params motives minors indices major ...).inferImplicit`
  and every rule right-hand side `template.instantiate ...` are
  `Expr.ParamUniformTele heads nparams ls`.
* `RecursorInstallation.generatedParamUniform`: the same for each installed
  `GeneratedRecursorEntry`.
* `NestedRun.recursorParamUniform` (with projections `recursorTypeParamUniform`,
  `ruleRhsParamUniform`): the same for the recursor read back by any restoration step of a
  validated nested run, at `result.nparams` and `lparams.map Level.param`. (Ported from the
  source branch's file of the same name; the `NestedRun` section and the lowering-side lemmas
  follow in `Uniform/Run.lean`, over Restoration-B's `NestedRun`.)

The head occurrences come from three sources.

* (a) Head occurrences built by the recursor construction: the major premise domains
  `I params indices`, the motives' major binders, and the minor premises' constructor
  applications `c params fields`. These are read off `MajorPremiseTypes`, `MotiveTypes` and
  `MinorsAndIndicesMatchSource`; the application is a head occurrence exactly when its head
  is auxiliary, and `Expr.ParamUniform.mkAppN_const_params` treats both cases uniformly.
* (b) Constructor field domains (minor premises and rule field lambdas): the field loop does
  no `whnf`, so each declared field type is the unannotated domain of the lowered constructor
  type after instantiating its parameters (`ParameterPrefix.paramUniformIn`,
  `RecursorFieldDecisions.fieldDeclsSatisfy` in `Recursor/Binders/FieldTypes.lean`).
  The lowered constructor types themselves are parameter-uniform parameter telescopes by
  `ConstructorLowering.Resolved.paramUniformTele` (from `ExprLowering.Resolved.paramUniform`).
* (c) The `whnf`-produced regions: index domains (R1, `loopArgs1`), induction-hypothesis
  binder domains (R2) and their exposed indices (R3, `loopUArgs`). R1 follows along the
  `loopArgs1` runs (`IndexTelescopeRun.paramUniform`, from the family header), R2
  and R3 along the `loopUArgs` runs (`LoopUArgsRun.paramUniform`,
  `InductionHypothesisType.paramUniform`, rooted by
  `CallTemplatesMatch.rooted`), all from the single hypothesis
  `WhnfPreservesParamUniform` on the lifted `whnf` calls.

The `whnf` regions are tracked under `Expr.ParamUniformIn` (parameter uniformity together
with the projection condition `ProjsOK (projAvoidsHeads env heads)`) rather than plain
parameter uniformity, since that is the invariant the type checker preserves; the head set is
arbitrary here. For a nested run the chain is instantiated at the checker's
head set `E.uniformHeads` (auxiliary heads and source constructors) and shrunk back
to the auxiliary heads (`NestedRun.recursorParamUniform_of_wfCore` in
`Nested/Restoration/Uniform/Whnf.lean`).

Remaining hypotheses are collected in `RecursorConstruction.ParamUniformDeclarations`; see
its docstring. -/

namespace Lean.Expr

open Lean4Lean

/-! ### Generic parameter-uniformity lemmas -/

namespace ParamUniform

variable {heads : List Name} {params : List Expr} {ls : List Level}

/-- The trailing arguments `e.getAppArgs[n:]` of a parameter-uniform expression are
parameter-uniform. -/
theorem getAppArgs_slice {e : Expr} (H : ParamUniform heads params ls e)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv) (n : Nat) :
    ∀ a ∈ (e.getAppArgs[n:] : Array Expr).toList, ParamUniform heads params ls a := by
  intro a ha
  rw [Lean4Lean.VerifyInductive.Expr.getAppArgs_slice_toList] at ha
  exact H.of_mem_getAppArgsList hp (List.mem_of_mem_drop ha)

/-- `consumeTypeAnnotationsVerified` returns a subterm reached through
application arguments, so it preserves parameter uniformity. -/
theorem consumeTypeAnnotationsVerified {e : Expr} (H : ParamUniform heads params ls e)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv) :
    ParamUniform heads params ls (e.consumeTypeAnnotationsVerified annOk) := by
  fun_induction Expr.consumeTypeAnnotationsVerified _ e
  case case1 name us type v _ ih =>
    exact ih (H.of_mem_getAppArgsList hp (a := type) (by simp [getAppArgsList]))
  case case2 => exact H
  case case3 name us type _ ih =>
    exact ih (H.of_mem_getAppArgsList hp (a := type) (by simp [getAppArgsList]))
  case case4 => exact H
  case case5 => exact H

/-- `mkAppN` with parameter-uniform head and arguments. -/
theorem mkAppN {f : Expr} {args : Array Expr} (hf : ParamUniform heads params ls f)
    (hargs : ∀ a ∈ args.toList, ParamUniform heads params ls a) :
    ParamUniform heads params ls (Lean.mkAppN f args) := by
  rw [Lean.Expr.mkAppN_eq_mkAppList]
  exact hf.mkAppList hargs

/-- A spine `c params rest` headed by any constant at the levels `ls`: a head
occurrence if `c ∈ heads`, a traversed constant otherwise. -/
theorem mkAppN_const_params {c : Name} {rest : Array Expr}
    (hrest : ∀ a ∈ rest.toList, ParamUniform heads params ls a)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv) :
    ParamUniform heads params ls (Lean.mkAppN (Lean.mkAppN (.const c ls) params.toArray) rest) := by
  rw [Lean.Expr.mkAppN_eq_mkAppList,
    Lean.Expr.mkAppN_eq_mkAppList, ← Expr.mkAppList_append]
  by_cases hc : c ∈ heads
  · exact mkAppList_const_head hc hrest
  · refine (ParamUniform.const hc).mkAppList fun a ha => ?_
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨fv, rfl⟩ := hp a ha
      exact .fvar fv
    · exact hrest a ha

/-- `mkAppN_const_params` with the parameters given as an array. -/
theorem mkAppN_const_paramsArray {params : Array Expr} {c : Name} {rest : Array Expr}
    (hrest : ∀ a ∈ rest.toList, ParamUniform heads params.toList ls a)
    (hp : ∀ p ∈ params.toList, ∃ fv, p = .fvar fv) :
    ParamUniform heads params.toList ls (Lean.mkAppN (Lean.mkAppN (.const c ls) params) rest) := by
  have := mkAppN_const_params (c := c) hrest hp
  rwa [Array.toArray_toList] at this

/-- Closing a telescope of non-parameter free variables with `mkForall`. -/
theorem mkForall_of_disjoint {lctx : LocalContext} {xs : Array Expr} {ys : List FVarId}
    {b : Expr} (hxs : xs = (ys.map Expr.fvar).toArray) (H : ParamUniform heads params ls b)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv ∧ fv ∉ ys)
    (hdecl : ∀ y ∈ ys, ∃ d, lctx.find? y = some d ∧ d.ParamUniform heads params ls) :
    ParamUniform heads params ls (lctx.mkForall xs b) := by
  subst hxs
  simpa [LocalContext.mkForall] using
    H.mkBinding_of_disjoint (isLambda := false) (lctx := lctx) hp hdecl

/-- Closing a telescope of non-parameter free variables with `mkLambda`. -/
theorem mkLambda_of_disjoint {lctx : LocalContext} {xs : Array Expr} {ys : List FVarId}
    {b : Expr} (hxs : xs = (ys.map Expr.fvar).toArray) (H : ParamUniform heads params ls b)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv ∧ fv ∉ ys)
    (hdecl : ∀ y ∈ ys, ∃ d, lctx.find? y = some d ∧ d.ParamUniform heads params ls) :
    ParamUniform heads params ls (lctx.mkLambda xs b) := by
  subst hxs
  simpa [LocalContext.mkLambda] using
    H.mkBinding_of_disjoint (isLambda := true) (lctx := lctx) hp hdecl

end ParamUniform

namespace ParamUniformIn

variable {env : Lean.Kernel.Environment} {heads : List Name} {params : List Expr}
  {ls : List Level}

/-- `consumeTypeAnnotationsVerified` returns a subterm reached through
application arguments, so it preserves `ParamUniformIn`. -/
theorem consumeTypeAnnotationsVerified {e : Expr} (H : ParamUniformIn env heads params ls e)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv) :
    ParamUniformIn env heads params ls (e.consumeTypeAnnotationsVerified annOk) := by
  fun_induction Expr.consumeTypeAnnotationsVerified _ e
  case case1 name us type v _ ih =>
    exact ih (H.of_mem_getAppArgsList hp (a := type) (by simp [getAppArgsList]))
  case case2 => exact H
  case case3 name us type _ ih =>
    exact ih (H.of_mem_getAppArgsList hp (a := type) (by simp [getAppArgsList]))
  case case4 => exact H
  case case5 => exact H

end ParamUniformIn

/-- The body of a binder telescope keeps the projection condition. -/
theorem LeadingBinders.projsOK {ok : Name → Prop} {n : Nat} {e body : Expr}
    (H : LeadingBinders n e body) (h : e.ProjsOK ok) : body.ProjsOK ok := by
  induction H with
  | zero => exact h
  | forallE _ ih => exact ih (ProjsOK.forallE_iff.1 h).2
  | lam _ ih => exact ih (ProjsOK.lam_iff.1 h).2

/-- A `forallE` telescope is a binder telescope. -/
theorem LeadingForalls.leadingBinders {n : Nat} {e body : Expr}
    (H : LeadingForalls n e body) : LeadingBinders n e body := by
  induction H with
  | zero => exact .zero _
  | forallE _ ih => exact .forallE ih

/-! ### `inferImplicit` changes binder annotations only -/

namespace ParamUniformBV

variable {heads : List Name} {n : Nat} {ls : List Level}

theorem inferImplicit {d : Nat} {e : Expr} (H : ParamUniformBV heads n ls d e)
    (k : Nat) (f : Bool) : ParamUniformBV heads n ls d (e.inferImplicit k f) := by
  induction k generalizing e d with
  | zero => cases e <;> simpa [Expr.inferImplicit] using H
  | succ k ih =>
    cases e with
    | forallE nm t b bi =>
      obtain ⟨ht, hb⟩ := H.forallE_inv
      simp only [Expr.inferImplicit, mkForall]
      exact .forallE ht (ih hb)
    | _ => simpa [Expr.inferImplicit] using H

end ParamUniformBV

theorem LeadingBinders.inferImplicit_paramUniform {heads : List Name} {n : Nat}
    {ls : List Level} {m : Nat} {e body : Expr} (H : LeadingBinders m e body)
    (Hb : ParamUniformBV heads n ls 0 body) (k : Nat) (f : Bool) :
    ∃ body', LeadingBinders m (e.inferImplicit k f) body' ∧
      ParamUniformBV heads n ls 0 body' := by
  induction H generalizing k with
  | zero => exact ⟨_, .zero _, Hb.inferImplicit k f⟩
  | @forallE m nm t b body bi Hb' ih =>
    cases k with
    | zero => exact ⟨body, by simpa [Expr.inferImplicit] using LeadingBinders.forallE Hb', Hb⟩
    | succ k =>
      obtain ⟨b', hl, hs⟩ := ih Hb k
      exact ⟨b', by simp only [Expr.inferImplicit, mkForall]; exact .forallE hl, hs⟩
  | @lam m nm t b body bi Hb' _ =>
    exact ⟨body, by cases k <;> simpa [Expr.inferImplicit] using LeadingBinders.lam Hb', Hb⟩

theorem ParamUniformTele.inferImplicit {heads : List Name} {n : Nat} {ls : List Level}
    {e : Expr} (H : ParamUniformTele heads n ls e) (k : Nat) (f : Bool) :
    ParamUniformTele heads n ls (e.inferImplicit k f) := by
  obtain ⟨body, hl, hb⟩ := H
  exact hl.inferImplicit_paramUniform hb k f

end Lean.Expr

namespace Lean.LocalDecl

open Lean4Lean

/-- The declaration's type and (visible) value satisfy `Expr.ParamUniformIn`: the form in
which the type checker's parameter-uniformity invariant constrains a scope declaration
(`TypeChecker.ParamUniformScopeAt`). -/
def ParamUniformIn (env : Lean.Kernel.Environment) (heads : List Name) (params : List Expr)
    (ls : List Level) (d : LocalDecl) : Prop :=
  d.type.ParamUniformIn env heads params ls ∧
    ∀ v, d.value? true = some v → v.ParamUniformIn env heads params ls

variable {env : Lean.Kernel.Environment} {heads : List Name} {params : List Expr}
  {ls : List Level}

theorem ParamUniformIn.paramUniform {d : LocalDecl} (H : d.ParamUniformIn env heads params ls) :
    d.ParamUniform heads params ls := by
  cases d with
  | cdecl => exact H.1.1
  | ldecl _ _ _ _ v nd _ => exact ⟨H.1.1, (H.2 v (by cases nd <;> rfl)).1⟩

theorem ParamUniformIn.of_cdecl {i : Nat} {fv : FVarId} {n : Name} {ty : Expr} {bi : BinderInfo}
    {k : LocalDeclKind} (h : ty.ParamUniformIn env heads params ls) :
    (LocalDecl.cdecl i fv n ty bi k).ParamUniformIn env heads params ls :=
  ⟨h, fun v hv => by simp [LocalDecl.value?] at hv⟩

end Lean.LocalDecl

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! ### The whnf hypothesis -/

/-- A parameter-uniform scope of a recursor-local context in the form used by the type
checker's invariant (`TypeChecker.ParamUniformScopeAt`): `P` is closed under the
dependencies of its declarations (`IsFVarUpSet`, as for
`TypeChecker.VContext.UniverseScope`) and every declaration of a member of `P`
satisfies `LocalDecl.ParamUniformIn` (parameter uniformity together with the projection condition
`ProjsOK (projAvoidsHeads env heads)`). -/
def RecursorContextWF.ParamUniformScope {c : AddInductive.Context} {recLparams : List Name}
    (Hc : RecursorContextWF c recLparams) (env : Environment) (heads : List Name)
    (params : List Expr) (ls : List Level) (P : FVarId → Prop) : Prop :=
  IsFVarUpSet P Hc.mlctx.vlctx ∧ ∀ fv decl, P fv → Hc.mlctx.lctx.find? fv = some decl →
    decl.ParamUniformIn env heads params ls

/-- **`whnf` preserves parameter uniformity in the recursor contexts of an environment**,
in the form provided by the type checker's invariant: an input (well-typed in
the recursor-local context `c`) that satisfies `Expr.ParamUniformIn` and whose free
variables lie in a parameter-uniform scope `P` of `c` is normalized to an expression
satisfying `Expr.ParamUniformIn`. It is the parameter-uniformity counterpart of
`whnfInRecursorContext.levelsWF` (`TypeChecker.VContext.LevelsBelow`),
quantified over the same data; the scope of the output is already provided by
`whnfInRecursorContext.scopeWF`.

`heads` are the head names (for a nested run `E.uniformHeads`: the auxiliary
families and constructors and the source constructors), `params` the common
parameter free variables `stats.params`, and `ls` the declaration's universe
parameters. Compared with plain parameter uniformity, the input and the scope carry the
projection condition `ProjsOK (projAvoidsHeads env heads)`: in the recursor pass the
projection registry already contains the block's structures, so `.proj S i x`
with `S` a source structure whose constructor mentions an auxiliary family
translates, and its inferred type exposes the auxiliary family at the
parameters of `x`'s type rather than at the parameter variables. The
instance for a nested run is `NestedRun.whnfPreservesParamUniform`
(`Nested/Restoration/Uniform/Whnf.lean`).

`inferType` is not needed as a separate hypothesis: `loopUArgs` reads the type
of a constructor field free variable by local-context lookup (`AddInductive.getType`),
which returns the field's declared type (`getTypeFVarRun.WF`). -/
structure WhnfPreservesParamUniform (heads : List Name) (params : List Expr) (ls : List Level)
    (env : Environment) : Prop where
  whnf : ∀ {c : AddInductive.Context} {recLparams : List Name}
      (Hc : RecursorContextWF c recLparams) {P : FVarId → Prop} {e e' : Expr},
    c.env = env →
    (∃ target₀, TrExprS Hc.venv recLparams Hc.chk.vlctx e target₀) →
    Hc.ParamUniformScope env heads params ls P →
    e.FVarsIn P → e.ParamUniformIn env heads params ls →
    (monadLift (TypeChecker.whnf e) : AddInductive.M Expr) c = .ok e' →
    e'.ParamUniformIn env heads params ls

/-! ### The `loopUArgs` traversal (regions R2 and R3) -/

/-- `ParamUniformIn` along a `loopUArgs.loop` run: mirrors
`LoopUArgsRun.universeSupport`. If the normalized input type
satisfies `ParamUniformIn` and lies in a parameter-uniform scope `P` of a recursor context,
then at the terminal context there is a parameter-uniform scope containing every opened argument,
and the exposed type satisfies `ParamUniformIn` and lies in that scope. -/
theorem LoopUArgsRun.paramUniform
    {heads : List Name} {params : List Expr} {ls : List Level} {env : Environment}
    (W : WhnfPreservesParamUniform heads params ls env)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    {root : AddInductive.Context} {l : LocalContext} {source : Expr}
    {current : AddInductive.Context} {exposed : Expr} {args : Array Expr}
    (trace : LoopUArgsRun root l source current exposed args)
    (henv : root.env = env)
    {recLparams : List Name}
    (Rroot : RecursorContextWF { root with checkLCtx := l } recLparams)
    {P : FVarId → Prop} (hscope : Rroot.ParamUniformScope env heads params ls P)
    {sourceTarget : VExpr}
    (hsource : TrExpr Rroot.venv recLparams Rroot.mlctx.vlctx source sourceTarget)
    (hsourceType : Rroot.venv.IsType recLparams.length Rroot.mlctx.vlctx.toCtx
      sourceTarget)
    {sourceTarget₀ : VExpr}
    (hsource₀ : TrExpr Rroot.venv recLparams Rroot.chk.vlctx source sourceTarget₀)
    (hsourceH : source.ParamUniformIn env heads params ls) (hsourceP : source.FVarsIn P) :
    ∃ (Rcurrent : RecursorContextWF current recLparams) (P' : FVarId → Prop)
      (T : VExpr),
      TrExpr Rcurrent.venv recLparams Rcurrent.mlctx.vlctx exposed T ∧
      Rcurrent.venv.IsType recLparams.length Rcurrent.mlctx.vlctx.toCtx T ∧
      Rcurrent.ParamUniformScope env heads params ls P' ∧
      exposed.ParamUniformIn env heads params ls ∧ exposed.FVarsIn P' ∧
      current.env = env ∧
      (∀ a ∈ args.toList, ∃ fv, a = .fvar fv ∧ P' fv) ∧
      ∃ T₀, TrExpr Rcurrent.venv recLparams Rcurrent.chk.vlctx exposed T₀ := by
  induction trace with
  | root =>
    exact ⟨Rroot, P, _, hsource, hsourceType, hscope, hsourceH,
      hsourceP, henv, by simp, _, hsource₀⟩
  | @push current next args name domain body normalized bi _previous next_eq
      normalization ih =>
    obtain ⟨R, P', T, htype, htypeType, hsc, hH, hP, hcenv, hargs, T₀, htype₀⟩ := ih
    subst next_eq
    rcases TrExpr.forallE_source htype with
      ⟨sourceDom, sourceBody, hdom, hbody, hdomType, hbodyType, hforallEq⟩
    rcases hconsume current recLparams R hdom hdomType with ⟨consumedDom, Hdom⟩
    rcases Hdom.body R hbody with ⟨consumedBody, hbodyConsumed, hbodyEq⟩
    rcases TrExpr.forallE_source htype₀ with
      ⟨dom₀, bodyN₀, hdom₀, hbodyN₀, hdom₀Type, _, _⟩
    rcases hconsume _ recLparams R.atCheckLCtx hdom₀ hdom₀Type with
      ⟨consumedDom₀, Hdom₀⟩
    rcases Hdom₀.body R.atCheckLCtx hbodyN₀ with ⟨consumedBody₀, hbodyConsumed₀, _⟩
    let x : FVarId := ⟨current.ngen.curr⟩
    let R' := R.withCheckedLocalDecl (name := name) (bi := bi) Hdom.unannotated Hdom.isType
      Hdom₀.unannotated Hdom₀.isType
    have hopened := R.instantiateFresh (name := name) (bi := bi)
      Hdom.unannotated Hdom.isType hbodyConsumed
    have hopened₀ := R.atCheckLCtx.instantiateFresh (name := name) (bi := bi)
      Hdom₀.unannotated Hdom₀.isType hbodyConsumed₀
    obtain ⟨hdomH, hbodyH⟩ := hH.forallE_inv
    have hdomP : domain.FVarsIn P' := hP.1
    have hbodyP : body.FVarsIn P' := hP.2
    let P'' : FVarId → Prop := fun fv => fv = x ∨ P' fv
    have hsc' : R'.ParamUniformScope env heads params ls P'' := by
      refine ⟨?_, ?_⟩
      · have hΔ : R'.mlctx.vlctx =
            (some (x, (domain.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper).fvarsList),
              .vlam consumedDom) :: R.mlctx.vlctx := rfl
        rw [hΔ]
        refine ⟨(IsFVarUpSet.congr (P := P') (Q := P'') R.mlctx_wf.tr.wf.fvwf
          (fun fv h => ⟨Or.inr, fun hq => hq.resolve_left (by
            rintro rfl; exact R.current_not_mem h)⟩)).1 hsc.1,
          fun _ dep hdep => .inr ?_⟩
        exact (fvarsIn_iff.mp
            (Expr.consumeTypeAnnotationsVerified_fvarsIn hdomP)).1 dep hdep
      · intro fv decl hfv hdecl
        by_cases hx : fv = x
        · subst hx
          have hself := R'.mlctx_wf.find?_vlam_self
          change (TypeChecker.MLCtx.vlam x name (domain.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper)
            consumedDom bi R.mlctx).lctx.find? x = some decl at hdecl
          rw [hself] at hdecl
          cases hdecl
          exact LocalDecl.ParamUniformIn.of_cdecl ((hdomH.consumeTypeAnnotationsVerified) hp)
        · have hfind : R'.mlctx.lctx.find? fv = R.mlctx.lctx.find? fv := by
            change (TypeChecker.MLCtx.vlam x name (domain.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper)
              consumedDom bi R.mlctx).lctx.find? fv = R.mlctx.lctx.find? fv
            have hwf : (TypeChecker.MLCtx.vlam x name (domain.consumeTypeAnnotationsVerified current.env.isTypeAnnotationWrapper)
                consumedDom bi R.mlctx).WF R.venv recLparams := R'.mlctx_wf
            rw [hwf.find?_eq, R.mlctx_wf.find?_eq]
            have hbeq : (fv == x) = false := by simpa using hx
            simp [TypeChecker.MLCtx.decls, LocalDecl.fvarId, hbeq]
          exact hsc.2 fv decl (hfv.resolve_left hx) (hfind ▸ hdecl)
    have hinstH : (body.instantiate1 (.fvar x)).ParamUniformIn env heads params ls :=
      hbodyH.instantiate1 hp Expr.ParamUniformIn.fvar
    have hinstP : (body.instantiate1 (.fvar x)).FVarsIn P'' := by
      rw [Expr.instantiate1_eq]
      exact (hbodyP.mono fun _ h => Or.inr h).instantiate1 (by
        simp [FVarsIn])
    have hdualRun := (whnfInRecursorContext.dualWF R' hopened hopened₀) normalized
      normalization
    have hscopeRun := hdualRun.1
    have hnormH : normalized.ParamUniformIn env heads params ls :=
      W.whnf R' hcenv ⟨_, hopened₀⟩ hsc' hinstP hinstH normalization
    have hbodyEq' := Hdom.bodyDefEqUnannotated R hbodyEq
    have hsourceBodyType : R'.venv.IsType recLparams.length
        R'.mlctx.vlctx.toCtx sourceBody := by
      let hctxEq : VLCtx.IsDefEq R.venv recLparams.length
          ((none, .vlam sourceDom) :: R.mlctx.vlctx)
          ((none, .vlam consumedDom) :: R.mlctx.vlctx) :=
        VLCtx.IsDefEq.cons
          (.refl R.checking.tr.wf R.mlctx_wf.tr.wf) nofun
          (.vlam Hdom.source_defeq.choose_spec)
      simpa only [R', RecursorContextWF.withCheckedLocalDecl_venv,
        RecursorContextWF.withCheckedLocalDecl_toCtx, VLCtx.toCtx] using
        hbodyType.defeqDFC R.checking.tr.wf.ordered hctxEq.defeqCtx
    have hconsumedBodyType : R'.venv.IsType recLparams.length
        R'.mlctx.vlctx.toCtx consumedBody := by
      apply hsourceBodyType.defeqU_l R'.checking.tr.wf
        R'.mlctx_wf.tr.wf.toCtx
      simpa only [R', RecursorContextWF.withCheckedLocalDecl_venv,
        RecursorContextWF.withCheckedLocalDecl_toCtx, VLCtx.toCtx] using hbodyEq'
    refine ⟨R', P'', consumedBody, hscopeRun.2, hconsumedBodyType, hsc',
      hnormH, hscopeRun.1 P'' hsc'.1 hinstP, hcenv, ?_, _, hdualRun.2.2⟩
    intro a ha
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · obtain ⟨fv, rfl, hfv⟩ := hargs a ha
      exact ⟨fv, rfl, Or.inr hfv⟩
    · exact ⟨x, rfl, Or.inl rfl⟩

/-- The type of a free variable of a recursor context translates. -/
theorem RecursorContextWF.trFVar {c : AddInductive.Context} {recLparams : List Name}
    (Hc : RecursorContextWF c recLparams) {fv : FVarId} (hfv : fv ∈ c.lctx.fvars) :
    ∃ target, TrExprS Hc.venv recLparams Hc.mlctx.vlctx (.fvar fv) target := by
  have hmem : fv ∈ Hc.mlctx.vlctx.fvars := by
    rw [← Hc.mlctx_wf.tr.fvars_eq, Hc.lctx_eq]; exact hfv
  obtain ⟨⟨e, A⟩, hfind⟩ := VLCtx.find?_eq_some.2 hmem
  exact ⟨e, .fvar hfind⟩

/-- **Parameter uniformity of one induction-hypothesis type** (regions R2 and R3). Given
a recursor-context certificate for the root context of `InductionHypothesisType`, a
parameter-uniform scope `P` containing the recursive field, and the parameters among the
root's variables, every argument declaration opened by `loopUArgs`, the exposed family
application and the hypothesis type are parameter-uniform. -/
theorem InductionHypothesisType.paramUniform
    {heads : List Name} {params : List Expr} {ls : List Level} {env : Environment}
    (W : WhnfPreservesParamUniform heads params ls env)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv)
    {stats : AddInductive.InductiveStats} {recInfos : Array AddInductive.RecInfo}
    {root : AddInductive.Context} {field type : Expr}
    (O : InductionHypothesisType stats recInfos root field type)
    (henv : root.env = env)
    {recLparams : List Name} (Rroot : RecursorContextWF root recLparams)
    {P : FVarId → Prop} (hscope : Rroot.ParamUniformScope env heads params ls P)
    (hfieldP : ∀ fv, field = .fvar fv → P fv)
    (hparamsRoot : ∀ p ∈ params, ∃ fv, p = .fvar fv ∧ fv ∈ root.lctx.fvars) :
    (∀ x ∈ O.arguments_bound.fvars, ∀ decl, O.current.lctx.find? x = some decl →
        decl.ParamUniform heads params ls) ∧
      O.exposedType.ParamUniform heads params ls ∧
      type.ParamUniform heads params ls := by
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
  obtain ⟨Rcurrent, P', _, _, _, hsc', hexposedH, _, _, hargs, _⟩ :=
    O.loopTrace.paramUniform W hp recursorConsumeTypeAnnotationsCompat henv RF hscope
      hnormalizedTr hinferredType hnormalized₀ hnormalizedH hnormalizedP
  have hargDecls : ∀ x ∈ O.arguments_bound.fvars, ∀ decl,
      O.current.lctx.find? x = some decl → decl.ParamUniform heads params ls := by
    intro x hx decl hdecl
    have hxArg : Expr.fvar x ∈ O.args.toList := by
      rw [O.arguments_bound.expressions]
      simpa using hx
    obtain ⟨y, hy, hyP⟩ := hargs _ hxArg
    cases hy
    exact (hsc'.2 x decl hyP (by rw [Rcurrent.lctx_eq]; exact hdecl)).paramUniform
  refine ⟨hargDecls, hexposedH.1, ?_⟩
  obtain ⟨m, hm, _⟩ := O.motive_is_fvar
  rw [O.type_eq]
  refine Expr.ParamUniform.mkForall_of_disjoint O.arguments_bound.expressions ?_ ?_ ?_
  · refine .app (Expr.ParamUniform.mkAppN (by rw [hm]; exact .fvar m)
      (hexposedH.1.getAppArgs_slice hp _)) (Expr.ParamUniform.mkAppN (.fvar fv) ?_)
    intro a ha
    rw [O.arguments_bound.expressions] at ha
    simp only [List.mem_map] at ha
    obtain ⟨y, -, rfl⟩ := ha
    exact .fvar y
  · intro p hp'
    obtain ⟨pv, rfl, hpv⟩ := hparamsRoot p hp'
    exact ⟨pv, rfl, fun h => O.arguments_bound.fresh pv h hpv⟩
  · intro y hy
    have hyCur : y ∈ O.current.lctx.fvars := O.arguments_bound.members y hy
    obtain ⟨index, name, ty, bi, kind, hfind⟩ := O.current_wf.findCDecl y hyCur
    exact ⟨_, hfind, hargDecls y hy _ hfind⟩

/-! ### The `loopArgs1` traversal (region R1) -/

/-- `ParamUniformIn` of the output of one recursor `whnf` call, given that
the declarations of every variable admitted by `Q` (read in `final`) and the
input satisfy it. -/
theorem WhnfRunAt.paramUniform
    {heads : List Name} {params : List Expr} {ls : List Level} {env : Environment}
    (W : WhnfPreservesParamUniform heads params ls env)
    {final : AddInductive.Context} (henv : final.env = env)
    {Q : FVarId → Prop} {input output : Expr}
    (H : WhnfRunAt final Q input output)
    (hQ : ∀ fv, Q fv → ∀ d, final.lctx.find? fv = some d →
      d.ParamUniformIn env heads params ls)
    (hin : input.ParamUniformIn env heads params ls) :
    output.ParamUniformIn env heads params ls := by
  obtain ⟨ctx, recLparams, Rc, P, target, hle, htr, hup, hP, hinP, hrun, htr₀⟩ := H
  refine W.whnf Rc (hle.env_eq.symm.trans henv) htr₀
    ⟨hup, fun fv decl hPfv hfind => ?_⟩ hinP hin hrun
  rw [Rc.lctx_eq] at hfind
  obtain ⟨hQfv, hmem⟩ := hP fv hPfv
  exact hQ fv hQfv decl (by rw [hle.declarations fv hmem]; exact hfind)

/-- **`ParamUniformIn` along a `loopArgs1` run** (region R1). If the
family header and the parameter declarations of `final` satisfy `ParamUniformIn`, then
so does every normalized type of the run and every opened index
declaration. -/
theorem IndexTelescopeRun.paramUniform
    {heads : List Name} {ls : List Level} {env : Environment}
    {stats : AddInductive.InductiveStats}
    (W : WhnfPreservesParamUniform heads stats.params.toList ls env)
    (hp : ∀ p ∈ stats.params.toList, ∃ fv, p = .fvar fv)
    {final : AddInductive.Context} (henv : final.env = env)
    (hparamDecls : ∀ fv ∈ ExprArrayFVarIds stats.params, ∀ d,
      final.lctx.find? fv = some d → d.ParamUniformIn env heads stats.params.toList ls)
    {header : Expr} (hheader : header.ParamUniformIn env heads stats.params.toList ls)
    {i : Nat} {type : Expr} {indices : Array Expr}
    (T : IndexTelescopeRun stats final header i type indices) :
    type.ParamUniformIn env heads stats.params.toList ls ∧
      ∀ fv ∈ ExprArrayFVarIds indices, ∀ d, final.lctx.find? fv = some d →
        d.ParamUniformIn env heads stats.params.toList ls := by
  induction T with
  | start call =>
    exact ⟨call.paramUniform W henv (fun _ h => h.elim) hheader,
      by simp [ExprArrayFVarIds]⟩
  | @param i name dom body normalized bi _ hi call ih =>
    obtain ⟨hty, -⟩ := ih
    obtain ⟨-, hbody⟩ := hty.forallE_inv
    have hparam : (stats.params[i]!).ParamUniformIn env heads stats.params.toList ls := by
      have hmem : stats.params[i]! ∈ stats.params.toList := by
        rw [getElem!_pos stats.params i hi]
        exact Array.getElem_mem_toList hi
      obtain ⟨fv, hfv⟩ := hp _ hmem
      rw [hfv]
      exact Expr.ParamUniformIn.fvar
    exact ⟨call.paramUniform W henv hparamDecls (hbody.instantiate1 hp hparam),
      by simp [ExprArrayFVarIds]⟩
  | @index indices name dom body normalized bi x _ member declaration call ih =>
    obtain ⟨hty, hidx⟩ := ih
    obtain ⟨hdom, hbody⟩ := hty.forallE_inv
    have hall : ∀ fv ∈ ExprArrayFVarIds (indices.push (.fvar x)), ∀ d,
        final.lctx.find? fv = some d → d.ParamUniformIn env heads stats.params.toList ls := by
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

/-! ### Constructor fields (the lowered constructor's syntactic domains) -/

/-- The executable common-parameter prefix replay instantiates the parameter
telescope with the parameter free variables, all at once. -/
theorem ParameterPrefix.tail_eq_instantiateRevList
    {stats : AddInductive.InductiveStats} {pfvs : List FVarId}
    (hparams : stats.params = (pfvs.map Expr.fvar).toArray) :
    ∀ {i : Nat} {src tail : Expr}, ParameterPrefix stats i src tail →
      ∀ {body : Expr}, Expr.LeadingBinders (pfvs.length - i) src body →
        tail = body.instantiateRevList ((pfvs.drop i).map Expr.fvar) 0 := by
  intro i src tail H
  induction H with
  | @done i tail hi =>
    intro body Hlead
    have hlen : pfvs.length = i := by
      rw [hi, hparams]; simp
    rw [hlen, Nat.sub_self] at Hlead
    cases Hlead
    rw [← hlen, List.drop_length]
    rfl
  | @step i param body tail name dom bi hparam _ ih =>
    intro body' Hlead
    have hi : i < pfvs.length := by
      have := (Array.getElem?_eq_some_iff.mp hparam).1
      rw [hparams] at this; simpa using this
    have hparamEq : param = .fvar pfvs[i] := by
      rw [hparams] at hparam
      simp only [List.getElem?_toArray, List.getElem?_map] at hparam
      rw [List.getElem?_eq_getElem hi] at hparam
      simp only [Option.map_some, Option.some.injEq] at hparam
      exact hparam.symm
    subst hparamEq
    rw [show pfvs.length - i = (pfvs.length - (i + 1)) + 1 by omega] at Hlead
    cases Hlead with
    | forallE Hb =>
      have Hb' := Hb.instantiate1' (.fvar pfvs[i]) 0
      rw [← Expr.instantiate1_eq] at Hb'
      rw [ih Hb', List.drop_eq_getElem_cons hi, List.map_cons]
      have hlenDrop : (pfvs.drop (i + 1)).length = pfvs.length - (i + 1) := by simp
      have := Expr.instantiateRevList_instantiate1'_fvars body' pfvs[i] (pfvs.drop (i + 1)) 0 0
      simp only [Nat.zero_add, Nat.add_zero, hlenDrop] at this
      rw [Nat.zero_add, this]
      rfl

/-- The parameter-instantiated tail of a parameter-uniform parameter telescope
(a lowered constructor type) is parameter-uniform over the parameter free variables. -/
theorem ParameterPrefix.paramUniform {heads : List Name} {ls : List Level}
    {stats : AddInductive.InductiveStats} {pfvs : List FVarId} {src tail : Expr}
    (H : ParameterPrefix stats 0 src tail)
    (hparams : stats.params = (pfvs.map Expr.fvar).toArray)
    (Hsrc : Expr.ParamUniformTele heads stats.params.size ls src) :
    tail.ParamUniform heads stats.params.toList ls := by
  obtain ⟨body, Hlead, Hbody⟩ := Hsrc
  have hsize : stats.params.size = pfvs.length := by rw [hparams]; simp
  rw [hsize] at Hlead Hbody
  rw [H.tail_eq_instantiateRevList hparams (by simpa using Hlead), hparams]
  simpa using Hbody.instantiateRevList_fvars

/-- `ParameterPrefix.paramUniform` together with the projection condition. -/
theorem ParameterPrefix.paramUniformIn {env : Environment} {heads : List Name}
    {ls : List Level} {stats : AddInductive.InductiveStats} {pfvs : List FVarId}
    {src tail : Expr}
    (H : ParameterPrefix stats 0 src tail)
    (hparams : stats.params = (pfvs.map Expr.fvar).toArray)
    (Hsrc : Expr.ParamUniformTele heads stats.params.size ls src)
    (Hproj : src.ProjsOK (projAvoidsHeads env heads)) :
    tail.ParamUniformIn env heads stats.params.toList ls := by
  refine ⟨H.paramUniform hparams Hsrc, ?_⟩
  obtain ⟨body, Hlead, -⟩ := Hsrc
  have hsize : stats.params.size = pfvs.length := by rw [hparams]; simp
  rw [hsize] at Hlead
  rw [H.tail_eq_instantiateRevList hparams (by simpa using Hlead)]
  refine (Hlead.projsOK Hproj).instantiateRevList (fun a ha => ?_) 0
  simp only [List.mem_map] at ha
  obtain ⟨_, _, rfl⟩ := ha
  exact Expr.ProjsOK.fvar

/-- Every field declaration opened along a field-decision run, and the
terminal expression, are parameter-uniform when the traversed tail is. -/
theorem RecursorFieldDecisions.paramUniform {heads : List Name} {params : List Expr}
    {ls : List Level}
    (H : RecursorFieldDecisions stats root source current terminal fields
      selected positions)
    (Hroot : BindingContextWF root) (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv)
    (Hsource : source.ParamUniform heads params ls) :
    terminal.ParamUniform heads params ls ∧
      FieldDeclsSatisfy (fun e => e.ParamUniform heads params ls) current fields :=
  H.fieldDeclsSatisfy Hroot _ (fun h =>
    ⟨(h.forallE_inv.1.consumeTypeAnnotationsVerified) hp,
      fun fv => h.forallE_inv.2.instantiate1 (.fvar fv) hp⟩) Hsource

/-- `RecursorFieldDecisions.paramUniform` together with the projection condition. -/
theorem RecursorFieldDecisions.paramUniformIn {env : Environment} {heads : List Name}
    {params : List Expr} {ls : List Level}
    (H : RecursorFieldDecisions stats root source current terminal fields
      selected positions)
    (Hroot : BindingContextWF root) (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv)
    (Hsource : source.ParamUniformIn env heads params ls) :
    terminal.ParamUniformIn env heads params ls ∧
      FieldDeclsSatisfy (fun e => e.ParamUniformIn env heads params ls) current fields :=
  H.fieldDeclsSatisfy Hroot _ (fun h =>
    ⟨(h.forallE_inv.1.consumeTypeAnnotationsVerified) hp,
      fun _ => h.forallE_inv.2.instantiate1 hp Expr.ParamUniformIn.fvar⟩) Hsource

/-! ### Bound free-variable arrays -/

theorem FVarArrayIn.mem_fvars_iff {c : AddInductive.Context} {xs : Array Expr}
    (B : FVarArrayIn c xs) {fv : FVarId} : fv ∈ B.fvars ↔ Expr.fvar fv ∈ xs := by
  rcases B with ⟨fvars, rfl, _⟩
  simp

theorem FVarArrayIn.fvar_of_mem {c : AddInductive.Context} {xs : Array Expr}
    (B : FVarArrayIn c xs) {e : Expr} (he : e ∈ xs) : ∃ fv, e = .fvar fv ∧ fv ∈ B.fvars := by
  rcases B with ⟨fvars, rfl, _⟩
  simp only [List.mem_toArray, List.mem_map] at he
  obtain ⟨fv, hfv, rfl⟩ := he
  exact ⟨fv, rfl, hfv⟩

theorem mem_exprArrayFVarIds_of_fvar_mem {xs : Array Expr} {fv : FVarId}
    (h : Expr.fvar fv ∈ xs) : fv ∈ ExprArrayFVarIds xs := by
  simp only [ExprArrayFVarIds, List.mem_map]
  exact ⟨_, Array.mem_toList_iff.2 h, rfl⟩

/-- Parameter uniformity of the declarations of a bound free-variable array, from
that of the binder types passed to `withLocalDecl`. -/
theorem FVarArrayBinderTypes.declParamUniform {heads : List Name} {params : List Expr}
    {ls : List Level} {c : AddInductive.Context} {xs origins : Array Expr}
    (Ho : FVarArrayBinderTypes c xs origins)
    (hQ : ∀ i, i < xs.size → origins[i]!.ParamUniform heads params ls)
    {fv : FVarId} (hfv : Expr.fvar fv ∈ xs) :
    ∃ d, c.lctx.find? fv = some d ∧ d.ParamUniform heads params ls := by
  obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp hfv
  obtain ⟨D, hD⟩ := Ho.declaration i hi
  have hfvD : D.fvar = fv := by
    have := D.expression.symm.trans hget
    exact (Expr.fvar.inj this)
  subst hfvD
  refine ⟨_, D.declaration, ?_⟩
  show D.type.ParamUniform heads params ls
  rw [hD]; exact hQ i hi

/-! ### Hypotheses on the recursor construction -/

/-- The cached parameters are variables of the context carrying the suffix. -/
theorem RecursorParameterContextSuffix.param_mem {r : AddInductive.Context}
    {recLparams : List Name} {Rr : RecursorContextWF r recLparams}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (P : RecursorParameterContextSuffix Rr stats depth) {pv : FVarId}
    (h : Expr.fvar pv ∈ stats.params) : pv ∈ r.lctx.fvars := by
  obtain ⟨fvars, hparams, hdecls⟩ := cachedParameterDecls_fvars P.cached
  have hmem : Expr.fvar pv ∈ stats.params.toList.reverse := by simpa using h
  rw [hparams] at hmem
  simp only [List.mem_map, Expr.fvar.injEq, exists_eq_right] at hmem
  rw [← Rr.lctx_eq, Rr.mlctx_wf.tr.fvars_eq, P.context, VLCtx.fvars_append, hdecls]
  exact List.mem_append_right _ hmem

/-- Selected (recursive) fields are among the opened fields. -/
theorem RecursorFieldDecisions.selected_subset
    (H : RecursorFieldDecisions stats root source current terminal fields
      selected positions) : ∀ e ∈ selected, e ∈ fields := by
  induction H with
  | nil => intro e he; simp at he
  | nonrecursive _ _ ih =>
    intro e he
    exact Array.mem_push.2 (.inl (ih e he))
  | recursive _ _ ih =>
    intro e he
    rcases Array.mem_push.1 he with he | rfl
    · exact Array.mem_push.2 (.inl (ih e he))
    · exact Array.mem_push.2 (.inr rfl)

section Assembly

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
  {R : RecursorInput c stats decl nparams isUnsafe depth
    sourceEnv indTypes ctorEnv}

/-- **Non-`whnf` hypotheses** for the parameter uniformity of a
recursor construction, relative to the head set `heads`, the parameter free
variables `stats.params` and the levels `stats.levels`. The inputs of the
recursor pass's `whnf` calls are built from the parameter declarations, the family
headers and the constructor types, so these carry the projection condition
`ProjsOK (projAvoidsHeads env heads)` of `WhnfPreservesParamUniform`, at the environment `env`
of the recursor context.

* `paramDecls`: the parameter declarations of the recursor context satisfy
  `LocalDecl.ParamUniformIn`. They are the source parameter domains (opened by the
  header check in the pre-declaration environment), which mention no head and
  project only out of structures of that environment.
* `familyHeaders`: the family headers `indTypes[i].type` mention no head and
  satisfy the projection condition. The header is the input of the first
  `whnf` call of `mkRecInfos.loopInd1`, so this is what `WhnfPreservesParamUniform.whnf`
  needs at the start of the `loopArgs1` run (`IndexTelescopeRuns`,
  recorded in `RecursorConstruction.minorSources`).
* `constructorTypes`: the lowered constructor types are parameter-uniform parameter
  telescopes (from lowering: every head occurrence is
  `mkAppN (.const auxI lvls) As` with untouched source trailing arguments) and
  satisfy the projection condition.
* `recursorNames`: generated recursor names are not heads.

The index domains (region R1) and the induction-hypothesis regions (R2, R3)
need no hypothesis beyond these and `WhnfPreservesParamUniform`: they follow along the
`IndexTelescopeRun`s and the rooted call templates
(`CallTemplatesMatch.rooted`). -/
structure RecursorConstruction.ParamUniformDeclarations
    (H : RecursorConstruction R) (heads : List Name) : Prop where
  paramDecls : ∀ fv ∈ H.params.fvars, ∀ d, H.localContext.lctx.find? fv = some d →
    d.ParamUniformIn H.localContext.env heads stats.params.toList stats.levels
  familyHeaders : ∀ i, i < indTypes.size → (indTypes[i]!.type).AvoidsConsts heads ∧
    (indTypes[i]!.type).ProjsOK (projAvoidsHeads H.localContext.env heads)
  constructorTypes : ∀ i, i < indTypes.size → ∀ ctor ∈ indTypes[i]!.ctors,
    Expr.ParamUniformTele heads stats.params.size stats.levels ctor.type ∧
      ctor.type.ProjsOK (projAvoidsHeads H.localContext.env heads)
  recursorNames : ∀ i, i < stats.indConsts.size → Lean.mkRecName indTypes[i]!.name ∉ heads

namespace RecursorConstruction

variable (H : RecursorConstruction R)

include H in
theorem params_fvar : ∀ p ∈ stats.params.toList, ∃ fv, p = .fvar fv := by
  intro p hp
  obtain ⟨fv, rfl, -⟩ := FVarArrayIn.fvar_of_mem H.params (Array.mem_toList_iff.1 hp)
  exact ⟨fv, rfl⟩

theorem params_toList : stats.params.toList = H.params.fvars.map Expr.fvar := by
  have h := congrArg Array.toList H.params.expressions
  simpa using h

theorem allFvars_nodup :
    (H.params.fvars ++ (H.bindings.motives.fvars ++ (H.bindings.flatMinors.fvars ++
      (H.bindings.flatIndices.fvars ++ H.bindings.majors.fvars)))).Nodup := by
  have := H.noAlias
  unfold RecInfoBindings.NoAlias at this
  rwa [H.bindings.allFvars_eq H.params] at this

theorem params_nodup : H.params.fvars.Nodup :=
  (List.nodup_append.1 H.allFvars_nodup).1

/-- A parameter is none of the other outer recursor binders. -/
theorem param_not_outer {pv : FVarId} (hpv : pv ∈ H.params.fvars) {e : Expr}
    (he : e ∈ H.recInfos.map (·.motive) ∨ e ∈ H.recInfos.flatMap (·.minors) ∨
      e ∈ H.recInfos.flatMap (·.indices) ∨ e ∈ H.recInfos.map (·.major)) :
    e ≠ .fvar pv := by
  rintro rfl
  have hdisj := (List.nodup_append.1 H.allFvars_nodup).2.2 pv hpv pv
  apply hdisj _ rfl
  simp only [List.mem_append]
  rcases he with he | he | he | he
  · exact .inl (H.bindings.motives.mem_fvars_iff.2 he)
  · exact .inr (.inl (H.bindings.flatMinors.mem_fvars_iff.2 he))
  · exact .inr (.inr (.inl (H.bindings.flatIndices.mem_fvars_iff.2 he)))
  · exact .inr (.inr (.inr (H.bindings.majors.mem_fvars_iff.2 he)))

/-- Disjointness in the form used by `ParamUniform.mkForall_of_disjoint`. -/
theorem params_disjoint {ys : List FVarId}
    (hys : ∀ y ∈ ys, Expr.fvar y ∈ H.recInfos.map (·.motive) ∨
      Expr.fvar y ∈ H.recInfos.flatMap (·.minors) ∨
      Expr.fvar y ∈ H.recInfos.flatMap (·.indices) ∨
      Expr.fvar y ∈ H.recInfos.map (·.major)) :
    ∀ p ∈ stats.params.toList, ∃ fv, p = .fvar fv ∧ fv ∉ ys := by
  intro p hp
  rw [H.params_toList] at hp
  simp only [List.mem_map] at hp
  obtain ⟨pv, hpv, rfl⟩ := hp
  exact ⟨pv, rfl, fun hy => H.param_not_outer hpv (hys pv hy) rfl⟩

theorem recInfos_size_eq : H.recInfos.size = decl.types.length := H.cardinality.records

theorem indConst_eq {i : Nat} (hi : i < H.recInfos.size) :
    ∃ n, stats.indConsts[i]! = .const n stats.levels := by
  have hi' : i < decl.types.length := by rw [← H.recInfos_size_eq]; exact hi
  have h := H.validStats.indConstAt hi'
  refine ⟨decl.types[i].name, ?_⟩
  rw [getElem!_def, h]

theorem sourceOwner {owner : Nat} (howner : owner < H.recInfos.size) :
    owner < indTypes.size := by
  have htypes : H.recInfos.size = indTypes.size := by
    rw [H.cardinality.records]
    simpa using (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core).symm
  omega

theorem motive_fvar {k : Nat} (hk : k < stats.indConsts.size) :
    ∃ fv, H.recInfos[k]!.motive = .fvar fv := by
  have hk' : k < H.recInfos.size := by
    rw [H.recInfos_size_eq, ← H.validStats.types_size]; exact hk
  have hmem : H.recInfos[k]!.motive ∈ H.recInfos.map (·.motive) := by
    rw [getElem!_pos H.recInfos k hk']
    exact Array.mem_map.2 ⟨_, Array.getElem_mem hk', rfl⟩
  obtain ⟨fv, h, -⟩ := FVarArrayIn.fvar_of_mem H.bindings.motives hmem
  exact ⟨fv, h⟩

/-- **Parameter uniformity of one generated minor**: its field declarations (in the
minor's source context), its declared type, and the call templates of its rule
template. -/
theorem minorParamUniform {heads : List Name} (I : H.ParamUniformDeclarations heads)
    (W : WhnfPreservesParamUniform heads stats.params.toList stats.levels H.localContext.env)
    (owner : Nat) (howner : owner < H.recInfos.size) (localIndex : Nat)
    (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    (∀ y ∈ (H.origins.minorShapes owner howner localIndex hlocal).fields_bound.fvars,
      ∃ d, (H.origins.minorShapes owner howner localIndex
          hlocal).sourceFullContext.lctx.find? y = some d ∧
        d.ParamUniform heads stats.params.toList stats.levels) ∧
    (H.origins.minorShapes owner howner localIndex hlocal).origin.ParamUniform heads
      stats.params.toList stats.levels ∧
    (∀ j, j < (H.origins.minorShapes owner howner localIndex hlocal).hypotheses.size →
      (H.recInfos[owner]!.ruleTemplates[localIndex]!.recursiveCalls[j]!).template.ParamUniform
        heads stats.params.toList stats.levels ∧
      (H.recInfos[owner]!.ruleTemplates[localIndex]!.recursiveCalls[j]!).targetTypeIdx <
        stats.indConsts.size) := by
  have hsourceOwner := H.sourceOwner howner
  have hsrc := H.minorSources.rows owner howner hsourceOwner localIndex hlocal
  have hcallRoots : RuleTemplateMatchesMinor stats
      (H.origins.minorShapes owner howner localIndex hlocal)
      H.recInfos[owner]!.minors[localIndex]!
      H.recInfos[owner]!.ruleTemplates[localIndex]! :=
    H.templates.entry owner howner localIndex hlocal
  have hfresh := H.templates.fields_outer_fresh owner howner localIndex hlocal
  obtain ⟨Hsem⟩ := H.templateTyping.entry owner howner localIndex hlocal
  generalize H.origins.minorShapes owner howner localIndex hlocal = S at hsrc hcallRoots hfresh Hsem ⊢
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
  have hp := H.params_fvar
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
  have Htail := Hprefix.paramUniformIn H.params.expressions
    (I.constructorTypes owner hsourceOwner _ hctorMem).1
    (I.constructorTypes owner hsourceOwner _ hctorMem).2
  obtain ⟨hterm, hfieldsTerm⟩ := F.traversal.decisions.paramUniformIn Hroot hp Htail
  rw [F.traversal_fields] at hfieldsTerm
  have hfieldDecls : ∀ y ∈ S.fields_bound.fvars, ∃ d,
      S.sourceFullContext.lctx.find? y = some d ∧
        d.ParamUniform heads stats.params.toList stats.levels := by
    intro y hy
    obtain ⟨fv, index, name, type, bi, kind, hfv, hmem, hfind, htype⟩ :=
      hfieldsTerm _ (S.fields_bound.mem_fvars_iff.1 hy)
    cases hfv
    refine ⟨.cdecl index y name type bi kind, ?_, htype.1⟩
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
        D.type.ParamUniform heads stats.params.toList stats.levels) ∧
      ((B.recursiveCalls[j]!).template.ParamUniform heads stats.params.toList stats.levels ∧
        (B.recursiveCalls[j]!).targetTypeIdx < stats.indConsts.size) := by
    intro j hj
    obtain ⟨originRoot, sourceType, recL, Rorigin, O, D, hle, hup, hD, hcall⟩ :=
      Hcalls.rooted j hj
    rw [hstats] at hup
    rw [hfr] at hle
    have henv : originRoot.env = H.localContext.env := hle.env_eq.trans hTL.env_eq.symm
    have hscope : Rorigin.ParamUniformScope H.localContext.env heads stats.params.toList
        stats.levels
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
        exact I.paramDecls fv hpar decl hfind
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
    have hparamsRoot : ∀ p ∈ stats.params.toList, ∃ fv, p = .fvar fv ∧
        fv ∈ originRoot.lctx.fvars := by
      intro p hpm
      obtain ⟨pv, rfl, -⟩ := FVarArrayIn.fvar_of_mem H.params (Array.mem_toList_iff.1 hpm)
      exact ⟨pv, rfl, hle.fvars (hparamTerm pv (Array.mem_toList_iff.1 hpm))⟩
    obtain ⟨hargs, hexp, htype⟩ :=
      O.paramUniform W hp henv Rorigin hscope hfieldP hparamsRoot
    refine ⟨⟨D, by rw [hD]; exact (htype.consumeTypeAnnotationsVerified) hp⟩, ?_⟩
    rw [hcall]
    refine ⟨?_, by
      have := (checkPositivityStep.isValidIndApp?_some O.owner_valid).1
      exact hstats ▸ this⟩
    obtain ⟨ffv, hffv, -⟩ := O.field_fvar
    refine Expr.ParamUniform.mkLambda_of_disjoint O.arguments_bound.expressions ?_ ?_ ?_
    · refine .app (Expr.ParamUniform.mkAppN (.bvar _) (hexp.getAppArgs_slice hp _))
        (Expr.ParamUniform.mkAppN (by rw [hffv]; exact .fvar ffv) ?_)
      intro a ha
      rw [O.arguments_bound.expressions] at ha
      simp only [List.mem_map] at ha
      obtain ⟨y, -, rfl⟩ := ha
      exact .fvar y
    · intro p hpm
      obtain ⟨pv, rfl, hpv⟩ := hparamsRoot p hpm
      exact ⟨pv, rfl, fun h => O.arguments_bound.fresh pv h hpv⟩
    · intro y hy
      have hyCur : y ∈ O.current.lctx.fvars := O.arguments_bound.members y hy
      obtain ⟨index, name, ty, bi, kind, hfind⟩ := O.current_wf.findCDecl y hyCur
      exact ⟨_, hfind, hargs y hy _ hfind⟩
  refine ⟨hfieldDecls, ?_, fun j hj => (hper j hj).2⟩
  -- The minor premise type.
  rw [← S.unannotated_eq]
  refine (Expr.ParamUniform.consumeTypeAnnotationsVerified) ?_ hp
  rw [S.sourceType_eq, ← S.sourceContext_eq]
  refine Expr.ParamUniform.mkForall_of_disjoint S.fields_bound.expressions ?_ ?_ hfieldDecls
  · refine Expr.ParamUniform.mkForall_of_disjoint S.hypotheses_bound.expressions ?_ ?_ ?_
    · rw [hmotiveApp]
      simp only [AddInductive.getIIndices]
      have hmo := (checkPositivityStep.isValidIndApp?_some hvalid).1
      obtain ⟨mfv, hmfv⟩ := H.motive_fvar hmo
      refine .app (Expr.ParamUniform.mkAppN ?_ (hterm.1.getAppArgs_slice hp _))
        (Expr.ParamUniform.mkAppN_const_paramsArray ?_ hp)
      · simp only [AddInductive.getIIndices] at hmfv
        rw [hmfv]; exact .fvar mfv
      · intro a ha
        obtain ⟨y, rfl, -⟩ := FVarArrayIn.fvar_of_mem S.fields_bound
          (Array.mem_toList_iff.1 ha)
        exact .fvar y
    · intro p hpm
      obtain ⟨pv, rfl, -⟩ := FVarArrayIn.fvar_of_mem H.params (Array.mem_toList_iff.1 hpm)
      refine ⟨pv, rfl, fun hy => ?_⟩
      have hpvP : pv ∈ ExprArrayFVarIds origins.stats.params := by
        rw [hstats]; exact mem_exprArrayFVarIds_of_fvar_mem (Array.mem_toList_iff.1 hpm)
      apply origins.hypotheses_outer_fresh pv (List.mem_append_left _ hpvP)
      rw [S.hypotheses_bound.exprArrayFVarIds]; exact hy
    · intro y hy
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
      exact ⟨_, D.declaration, hDshape⟩
  · intro p hpm
    obtain ⟨pv, rfl, -⟩ := FVarArrayIn.fvar_of_mem H.params (Array.mem_toList_iff.1 hpm)
    refine ⟨pv, rfl, fun hy => hfresh pv hy ?_⟩
    exact List.mem_append_left _ (List.mem_append_left _
      (mem_exprArrayFVarIds_of_fvar_mem (Array.mem_toList_iff.1 hpm)))

section Outer

variable {heads : List Name}

theorem paramCDecls : ∀ x ∈ H.params.fvars, ∃ i fv n ty bi kind,
    H.localContext.lctx.find? x = some (.cdecl i fv n ty bi kind) := by
  intro x hx
  obtain ⟨index, name, type, bi, kind, hfind⟩ :=
    H.localWF.findCDecl x (H.params.members x hx)
  exact ⟨index, x, name, type, bi, kind, hfind⟩

theorem mem_recInfos {k : Nat} (hk : k < H.recInfos.size) : H.recInfos[k]! ∈ H.recInfos := by
  rw [getElem!_pos H.recInfos k hk]; exact Array.getElem_mem hk

/-- Index declarations of every family (region R1): along the
`loopArgs1` run of the family, from the header. -/
theorem indexDeclParamUniform (I : H.ParamUniformDeclarations heads)
    (W : WhnfPreservesParamUniform heads stats.params.toList stats.levels H.localContext.env)
    {k : Nat} (hk : k < H.recInfos.size) {y : FVarId}
    (hy : Expr.fvar y ∈ H.recInfos[k]!.indices) :
    ∃ d, H.localContext.lctx.find? y = some d ∧
      d.ParamUniform heads stats.params.toList stats.levels := by
  obtain ⟨type, T⟩ := H.minorSources.traces k hk
  have hparamDecls : ∀ fv ∈ ExprArrayFVarIds stats.params, ∀ d,
      H.localContext.lctx.find? fv = some d →
        d.ParamUniformIn H.localContext.env heads stats.params.toList stats.levels := by
    intro fv hfv d hfind
    rw [H.params.exprArrayFVarIds] at hfv
    exact I.paramDecls fv hfv d hfind
  obtain ⟨-, hidx⟩ := T.paramUniform W H.params_fvar rfl hparamDecls
    (Expr.ParamUniformIn.of_avoids (I.familyHeaders k (H.sourceOwner hk)).1
      (I.familyHeaders k (H.sourceOwner hk)).2)
  have hyMem : y ∈ (H.bindings.indices k hk).fvars :=
    (H.bindings.indices k hk).mem_fvars_iff.2 hy
  obtain ⟨index, name, ty, bi, kind, hfind⟩ :=
    H.localWF.findCDecl y ((H.bindings.indices k hk).members y hyMem)
  refine ⟨_, hfind, (hidx y ?_ _ hfind).paramUniform⟩
  rw [(H.bindings.indices k hk).exprArrayFVarIds]
  exact hyMem

/-- Major premise declarations: `I params indices`, a head occurrence exactly for
auxiliary families. -/
theorem majorDeclParamUniform {y : FVarId} (hy : Expr.fvar y ∈ H.recInfos.map (·.major)) :
    ∃ d, H.localContext.lctx.find? y = some d ∧
      d.ParamUniform heads stats.params.toList stats.levels := by
  refine H.origins.majors.declParamUniform (fun i hi => ?_) hy
  have hi' : i < H.recInfos.size := by simpa using hi
  rw [H.majorShapes.shape i hi']
  refine (Expr.ParamUniform.consumeTypeAnnotationsVerified) ?_ H.params_fvar
  obtain ⟨n, hn⟩ := H.indConst_eq hi'
  rw [hn]
  refine Expr.ParamUniform.mkAppN_const_paramsArray (fun a ha => ?_) H.params_fvar
  obtain ⟨fv, rfl, -⟩ := FVarArrayIn.fvar_of_mem (H.bindings.indices i hi')
    (Array.mem_toList_iff.1 ha)
  exact .fvar fv

theorem indices_outer {k : Nat} (hk : k < H.recInfos.size) :
    ∀ y ∈ (H.bindings.indices k hk).fvars,
      Expr.fvar y ∈ H.recInfos.map (·.motive) ∨
      Expr.fvar y ∈ H.recInfos.flatMap (·.minors) ∨
      Expr.fvar y ∈ H.recInfos.flatMap (·.indices) ∨
      Expr.fvar y ∈ H.recInfos.map (·.major) := by
  intro y hy
  exact .inr (.inr (.inl (Array.mem_flatMap.2 ⟨_, H.mem_recInfos hk,
    (H.bindings.indices k hk).mem_fvars_iff.1 hy⟩)))

theorem major_outer {k : Nat} (hk : k < H.recInfos.size) :
    ∀ y ∈ (H.bindings.major k hk).fvars,
      Expr.fvar y ∈ H.recInfos.map (·.motive) ∨
      Expr.fvar y ∈ H.recInfos.flatMap (·.minors) ∨
      Expr.fvar y ∈ H.recInfos.flatMap (·.indices) ∨
      Expr.fvar y ∈ H.recInfos.map (·.major) := by
  intro y hy
  have h := (H.bindings.major k hk).mem_fvars_iff.1 hy
  simp only [List.mem_toArray, List.mem_singleton] at h
  refine .inr (.inr (.inr ?_))
  rw [h]
  exact Array.mem_map.2 ⟨_, H.mem_recInfos hk, rfl⟩

/-- Motive declarations: `∀ indices, ∀ (t : I params indices), Sort u`. -/
theorem motiveDeclParamUniform (I : H.ParamUniformDeclarations heads)
    (W : WhnfPreservesParamUniform heads stats.params.toList stats.levels H.localContext.env)
    {y : FVarId}
    (hy : Expr.fvar y ∈ H.recInfos.map (·.motive)) :
    ∃ d, H.localContext.lctx.find? y = some d ∧
      d.ParamUniform heads stats.params.toList stats.levels := by
  refine H.origins.motives.declParamUniform (fun i hi => ?_) hy
  have hi' : i < H.recInfos.size := by simpa using hi
  rw [H.motiveShapes.shape i hi']
  refine Expr.ParamUniform.mkForall_of_disjoint (H.bindings.indices i hi').expressions ?_
    (H.params_disjoint (H.indices_outer hi')) (fun y hy => H.indexDeclParamUniform I W hi'
      ((H.bindings.indices i hi').mem_fvars_iff.1 hy))
  refine Expr.ParamUniform.mkForall_of_disjoint (H.bindings.major i hi').expressions (.sort _)
    (H.params_disjoint (H.major_outer hi')) (fun y hy => H.majorDeclParamUniform ?_)
  have h := (H.bindings.major i hi').mem_fvars_iff.1 hy
  simp only [List.mem_toArray, List.mem_singleton] at h
  rw [h]
  exact Array.mem_map.2 ⟨_, H.mem_recInfos hi', rfl⟩

/-- Minor premise declarations. -/
theorem minorDeclParamUniform (I : H.ParamUniformDeclarations heads)
    (W : WhnfPreservesParamUniform heads stats.params.toList stats.levels H.localContext.env)
    {y : FVarId} (hy : Expr.fvar y ∈ H.recInfos.flatMap (·.minors)) :
    ∃ d, H.localContext.lctx.find? y = some d ∧
      d.ParamUniform heads stats.params.toList stats.levels := by
  obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp hy
  obtain ⟨D⟩ := H.bindings.flatMinors.declarationAt H.localWF i hi
  obtain ⟨Fm⟩ := H.origins.flatMinorBinderType D
  have hDy : D.fvar = y := Expr.fvar.inj (D.expression.symm.trans hget)
  subst hDy
  refine ⟨_, D.declaration, ?_⟩
  show D.type.ParamUniform heads stats.params.toList stats.levels
  rw [Fm.originType_eq]
  have howner := Fm.owner_lt
  have hlocal : Fm.localIndex < H.origins.minorTypes[Fm.owner]!.size := by
    rw [(H.origins.minors Fm.owner howner).size_eq, getElem!_pos H.recInfos Fm.owner howner]
    exact Fm.local_lt
  have hsrc := H.minorSources.rows Fm.owner howner (H.sourceOwner howner) Fm.localIndex hlocal
  rw [← hsrc.1]
  exact (H.minorParamUniform I W Fm.owner howner Fm.localIndex hlocal).2.1

end Outer

/-- **Generated recursor types are parameter-uniform parameter telescopes.** For
every owner, the executable recursor type
`(declareRecursors.recursorType stats recInfos lctx owner).inferImplicit 1000 false`
(as recorded in `GeneratedRecursorEntry.type`) is `ParamUniformTele heads nparams ls`. -/
theorem recursorTypeParamUniform {heads : List Name} (I : H.ParamUniformDeclarations heads)
    (W : WhnfPreservesParamUniform heads stats.params.toList stats.levels H.localContext.env)
    (owner : Nat) (howner : owner < H.recInfos.size) :
    Expr.ParamUniformTele heads stats.params.size stats.levels
      ((H.localContext.lctx.mkForall stats.params <|
        H.localContext.lctx.mkForall (H.recInfos.map (·.motive)) <|
        H.localContext.lctx.mkForall (H.recInfos.flatMap (·.minors)) <|
        H.localContext.lctx.mkForall H.recInfos[owner]!.indices <|
        H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
          (.app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices)
            H.recInfos[owner]!.major)).inferImplicit 1000 false) := by
  have hp := H.params_fvar
  refine Expr.ParamUniformTele.inferImplicit ?_ 1000 false
  refine Expr.ParamUniform.mkForall_params ?_ H.params_toList H.params_nodup H.paramCDecls
  have hownerC : owner < stats.indConsts.size := by
    rw [H.validStats.types_size, ← H.recInfos_size_eq]; exact howner
  obtain ⟨mfv, hmfv⟩ := H.motive_fvar hownerC
  have hmajorMem : H.recInfos[owner]!.major ∈ #[H.recInfos[owner]!.major] := by simp
  obtain ⟨jfv, hjfv, -⟩ := FVarArrayIn.fvar_of_mem (H.bindings.major owner howner) hmajorMem
  -- body
  have hbody : (Expr.app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices)
      H.recInfos[owner]!.major).ParamUniform heads stats.params.toList stats.levels := by
    refine .app (Expr.ParamUniform.mkAppN (by rw [hmfv]; exact .fvar mfv) fun a ha => ?_)
      (by rw [hjfv]; exact .fvar jfv)
    obtain ⟨fv, rfl, -⟩ := FVarArrayIn.fvar_of_mem (H.bindings.indices owner howner)
      (Array.mem_toList_iff.1 ha)
    exact .fvar fv
  refine Expr.ParamUniform.mkForall_of_disjoint H.bindings.motives.expressions ?_
    (H.params_disjoint fun y hy => .inl (H.bindings.motives.mem_fvars_iff.1 hy))
    (fun y hy => H.motiveDeclParamUniform I W (H.bindings.motives.mem_fvars_iff.1 hy))
  refine Expr.ParamUniform.mkForall_of_disjoint H.bindings.flatMinors.expressions ?_
    (H.params_disjoint fun y hy => .inr (.inl (H.bindings.flatMinors.mem_fvars_iff.1 hy)))
    (fun y hy => H.minorDeclParamUniform I W (H.bindings.flatMinors.mem_fvars_iff.1 hy))
  refine Expr.ParamUniform.mkForall_of_disjoint (H.bindings.indices owner howner).expressions ?_
    (H.params_disjoint (H.indices_outer howner))
    (fun y hy => H.indexDeclParamUniform I W howner
      ((H.bindings.indices owner howner).mem_fvars_iff.1 hy))
  refine Expr.ParamUniform.mkForall_of_disjoint (H.bindings.major owner howner).expressions hbody
    (H.params_disjoint (H.major_outer howner)) (fun y hy => H.majorDeclParamUniform ?_)
  have h := (H.bindings.major owner howner).mem_fvars_iff.1 hy
  simp only [List.mem_toArray, List.mem_singleton] at h
  rw [h]
  exact Array.mem_map.2 ⟨_, H.mem_recInfos howner, rfl⟩

/-- **Generated rule right-hand sides are parameter-uniform parameter telescopes.**
For every owner and every rule template `blueprint` of the owner, the executable rule
right-hand side `(blueprint.instantiate indTypes stats motives minors lvls lctx).rhs`
(as recorded in `GeneratedRecursorEntry.rules_eq`) is
`ParamUniformTele heads nparams ls`: a `lam` telescope over the parameters around
`fun motives minors fields => minor fields (calls)`, parameter-uniform in bound-variable form.
The generated recursor heads `.const (mkRecName I) lvls` of the recursive calls
are not heads (`ParamUniformDeclarations.recursorNames`), so `lvls` is arbitrary. -/
theorem ruleRhsParamUniform {heads : List Name} (I : H.ParamUniformDeclarations heads)
    (W : WhnfPreservesParamUniform heads stats.params.toList stats.levels H.localContext.env)
    (owner : Nat) (howner : owner < H.recInfos.size) (lvls : List Level)
    (blueprint : AddInductive.RecRuleTemplate)
    (hmem : blueprint ∈ H.recInfos[owner]!.ruleTemplates.toList) :
    Expr.ParamUniformTele heads stats.params.size stats.levels
      (blueprint.instantiate indTypes stats (H.recInfos.map (·.motive))
        (H.recInfos.flatMap (·.minors)) lvls H.localContext.lctx).rhs := by
  have hp := H.params_fvar
  obtain ⟨localIndex, hlocalB, hget⟩ := List.mem_iff_getElem.1 hmem
  have hlocalB' : localIndex < H.recInfos[owner]!.ruleTemplates.size := by simpa using hlocalB
  have hlocal : localIndex < H.origins.minorTypes[owner]!.size := by
    rw [← H.templates.rows_size owner howner]; exact hlocalB'
  have hB : H.recInfos[owner]!.ruleTemplates[localIndex]! = blueprint := by
    rw [getElem!_pos _ localIndex hlocalB']; simpa using hget
  obtain ⟨hfieldDecls, -, hcalls⟩ := H.minorParamUniform I W owner howner localIndex hlocal
  have hentry := H.templates.entry owner howner localIndex hlocal
  rw [hB] at hcalls hentry
  obtain ⟨-, hBfields, hBlctx, hBminor, traversal, origins, -, hshape, -, -, hcallOrigins⟩ :=
    hentry
  have hcallsSize := hcallOrigins.size_eq
  have hfresh := H.templates.fields_outer_fresh owner howner localIndex hlocal
  generalize H.origins.minorShapes owner howner localIndex hlocal = S at *
  -- the minor variable
  have hminorsSize : localIndex < H.recInfos[owner]!.minors.size := by
    rw [← (H.origins.minors owner howner).size_eq]; exact hlocal
  have hminorMem : blueprint.minor ∈ H.recInfos[owner]!.minors := by
    rw [hBminor, getElem!_pos _ localIndex hminorsSize]; exact Array.getElem_mem hminorsSize
  obtain ⟨minorFv, hminorFv, -⟩ :=
    FVarArrayIn.fvar_of_mem (H.bindings.minors owner howner) hminorMem
  simp only [AddInductive.RecRuleTemplate.instantiate]
  refine Expr.ParamUniform.mkLambda_params ?_ H.params_toList H.params_nodup H.paramCDecls
  refine Expr.ParamUniform.mkLambda_of_disjoint H.bindings.motives.expressions ?_
    (H.params_disjoint fun y hy => .inl (H.bindings.motives.mem_fvars_iff.1 hy))
    (fun y hy => H.motiveDeclParamUniform I W (H.bindings.motives.mem_fvars_iff.1 hy))
  refine Expr.ParamUniform.mkLambda_of_disjoint H.bindings.flatMinors.expressions ?_
    (H.params_disjoint fun y hy => .inr (.inl (H.bindings.flatMinors.mem_fvars_iff.1 hy)))
    (fun y hy => H.minorDeclParamUniform I W (H.bindings.flatMinors.mem_fvars_iff.1 hy))
  rw [hBlctx, hBfields]
  refine Expr.ParamUniform.mkLambda_of_disjoint S.fields_bound.expressions ?_ ?_ hfieldDecls
  · refine Expr.ParamUniform.mkAppN (Expr.ParamUniform.mkAppN (by rw [hminorFv]; exact .fvar _)
      fun a ha => ?_) fun a ha => ?_
    · obtain ⟨y, rfl, -⟩ := FVarArrayIn.fvar_of_mem S.fields_bound
        (Array.mem_toList_iff.1 ha)
      exact .fvar y
    · simp only [Array.toList_map, List.mem_map] at ha
      obtain ⟨call, hcall, rfl⟩ := ha
      obtain ⟨j, hj, hcallj⟩ := List.mem_iff_getElem.1 hcall
      have hj' : j < blueprint.recursiveCalls.size := by simpa using hj
      have hcallEq : blueprint.recursiveCalls[j]! = call := by
        rw [getElem!_pos _ j hj']; simpa using hcallj
      obtain ⟨htemplate, htarget⟩ := hcalls j (by rw [← hcallsSize]; exact hj')
      rw [hcallEq] at htemplate htarget
      simp only [AddInductive.RecCallTemplate.instantiate]
      refine htemplate.instantiate1 ?_ hp
      refine Expr.ParamUniform.mkAppN (Expr.ParamUniform.mkAppN
        (Expr.ParamUniform.mkAppN (.const (I.recursorNames _ htarget)) fun a ha => ?_)
          fun a ha => ?_) fun a ha => ?_
      · obtain ⟨fv, rfl⟩ := hp a ha
        exact .fvar fv
      · obtain ⟨fv, rfl, -⟩ := FVarArrayIn.fvar_of_mem H.bindings.motives
          (Array.mem_toList_iff.1 ha)
        exact .fvar fv
      · obtain ⟨fv, rfl, -⟩ := FVarArrayIn.fvar_of_mem H.bindings.flatMinors
          (Array.mem_toList_iff.1 ha)
        exact .fvar fv
  · intro p hpm
    obtain ⟨pv, rfl, -⟩ := FVarArrayIn.fvar_of_mem H.params (Array.mem_toList_iff.1 hpm)
    exact ⟨pv, rfl, fun hy => hfresh pv hy (List.mem_append_left _ (List.mem_append_left _
      (mem_exprArrayFVarIds_of_fvar_mem (Array.mem_toList_iff.1 hpm))))⟩

end RecursorConstruction

/-! ### Installed generated recursors -/

/-- Parameter uniformity of the type and of every rule right-hand side of each generated
recursor entry of a recursor installation. -/
theorem RecursorInstallation.generatedParamUniform
    {outEnv : Environment} (C : RecursorInstallation R outEnv)
    {heads : List Name} (I : C.toRecursorConstruction.ParamUniformDeclarations heads)
    (W : WhnfPreservesParamUniform heads stats.params.toList stats.levels C.localContext.env)
    (i : Nat) (hi : i < C.entries.length) :
    Expr.ParamUniformTele heads stats.params.size stats.levels (C.generated.entry i hi).info.type ∧
      ∀ rule ∈ (C.generated.entry i hi).info.rules,
        Expr.ParamUniformTele heads stats.params.size stats.levels rule.rhs := by
  have howner : i < C.recInfos.size := by rw [← C.generated.length]; exact hi
  refine ⟨?_, ?_⟩
  · rw [(C.generated.entry i hi).type]
    exact C.toRecursorConstruction.recursorTypeParamUniform I W i howner
  · intro rule hrule
    rw [(C.generated.entry i hi).rules_eq] at hrule
    simp only [List.mem_map] at hrule
    obtain ⟨blueprint, hmem, rfl⟩ := hrule
    exact C.toRecursorConstruction.ruleRhsParamUniform I W i howner _ blueprint hmem

end Assembly

end VerifyInductive
end Lean4Lean
