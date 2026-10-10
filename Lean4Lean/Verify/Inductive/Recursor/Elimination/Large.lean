import Lean4Lean.Verify.Inductive.Recursor.Binders.RecursiveFields
import Lean4Lean.Verify.Inductive.Header.CheckedHeaders

/-! The executable's elimination-universe decision (`getElimLevel`, `isLargeEliminator`).
A large elimination level is returned only after a successful large-eliminator check. The
cached result-universe flag is linked to the checked headers, and the singleton check is
mirrored by the loop relation `LargeEliminationCheck`, which exposes every parameter, proof
field and required result argument. This supplies the elimination level of the recursor
construction (section 3.2 of the design notes).
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A nonzero elimination level returned by `getElimLevel` comes from a successful
`isLargeEliminator` check in the same context. -/
theorem AddInductive.getElimLevel.large_of_checked
    {stats : AddInductive.InductiveStats} {indTypes : Array InductiveType}
    {c : AddInductive.Context} {level : Level}
    (H : AddInductive.getElimLevel stats indTypes c = .ok level)
    (hlevel : level ≠ .zero) :
    AddInductive.isLargeEliminator stats indTypes c = .ok true := by
  unfold AddInductive.getElimLevel at H
  cases hlarge : AddInductive.isLargeEliminator stats indTypes c with
  | error e => simp [bind, ReaderT.bind, hlarge, Except.bind] at H
  | ok large =>
    cases large with
    | false =>
      simp [bind, ReaderT.bind, hlarge, Except.bind, Except.pure, pure, ReaderT.pure] at H
      exact False.elim (hlevel H.symm)
    | true => rfl

/-- The executable large-elimination decision either uses the cached nonzero
universe or checks the sole constructor of a singleton family. -/
theorem AddInductive.isLargeEliminator.shape_of_checked
    {stats : AddInductive.InductiveStats} {indTypes : Array InductiveType}
    {c : AddInductive.Context}
    (H : AddInductive.isLargeEliminator stats indTypes c = .ok true) :
    stats.isNotZero = true ∨ ∃ ind,
      indTypes = #[ind] ∧
      (ind.ctors = [] ∨ ∃ ctor, ind.ctors = [ctor] ∧
        AddInductive.isLargeEliminator.loop stats ctor.type 0 #[]
          c.fuel.inductiveFuel { c with checkLCtx := {} } = .ok true) := by
  by_cases hnonzero : stats.isNotZero = true
  · exact .inl hnonzero
  right
  rcases indTypes with ⟨xs⟩
  cases xs with
  | nil =>
      unfold AddInductive.isLargeEliminator AddInductive.isLargeEliminator.match_4 at H
      simp [hnonzero, pure, ReaderT.pure, Except.pure, Array.size] at H
  | cons ind rest =>
    cases rest with
    | cons ind' rest =>
        unfold AddInductive.isLargeEliminator AddInductive.isLargeEliminator.match_4 at H
        simp [hnonzero, pure, ReaderT.pure, Except.pure, Array.size] at H
    | nil =>
      refine ⟨ind, rfl, ?_⟩
      unfold AddInductive.isLargeEliminator at H
      unfold AddInductive.isLargeEliminator.match_4 at H
      simp only [hnonzero, Array.size, List.length_cons,
        List.length_nil, ↓reduceDIte, Array.getLit] at H
      cases hctors : ind.ctors with
      | nil => exact .inl rfl
      | cons ctor ctors =>
        cases ctors with
        | nil =>
          exact .inr ⟨ctor, rfl, by
            simpa [hctors, bind, ReaderT.bind, readThe, read,
              MonadReaderOf.read, ReaderT.read, Except.bind, pure,
              Except.pure, ReaderT.pure, AddInductive.withCheckLCtx_apply]
              using H⟩
        | cons ctor' ctors => simp [hctors, pure, ReaderT.pure, Except.pure] at H

/-- The nonzero shortcut is justified: the common result universe checked by the header
phase is never zero for every family of the source block. -/
theorem checkInductiveTypes.loopInd.HeaderStatsWF.familyNeverZero
    (H : checkInductiveTypes.loopInd.HeaderStatsWF env Us Δ
      stats decl depth)
    (hnotzero : stats.isNotZero = true)
    {family : VInductiveType} (hfamily : family ∈ decl.types) :
    family.resultLevel.IsNeverZero := by
  have hnz : stats.resultLevel.isNeverZero = true := H.isNotZero.symm.trans hnotzero
  exact (ofLevel_isNeverZero H.commonLevel hnz).of_equiv
    (H.headers.commonLevels family hfamily).symm



/-- A successful `ensureType` whose sort level is always zero shows that the translated
type is a proposition. The argument goes through uniqueness of typing, so it holds for any
translation of the type, not only the one produced by the check. -/
theorem ensureTypeInContext.proof_of_isAlwaysZero
    (Hc : ContextWF c)
    (Htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type')
    (Htype₀ : TrExprS Hc.venv c.lparams Hc.chk.vlctx type type₀)
    (Hrun : (monadLift (TypeChecker.ensureType type) : AddInductive.M Expr) c =
      .ok result)
    (Hzero : result.sortLevel!.isAlwaysZero = true) :
    Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx type' (.sort .zero) := by
  rcases ensureTypeInContext.WF Hc Htype Htype₀ result Hrun with
    ⟨type'', Htype'', u, u', rfl, Hu, Htyped⟩
  have Heq := Htype''.uniq Hc.checking.tr.wf
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) Htype
  have Hu0 : u' ≈ .zero := ofLevel_isAlwaysZero Hu Hzero
  have Hprop : Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
      type'' (.sort .zero) :=
    (VEnv.IsDefEq.sortDF (l' := .zero) (.of_ofLevel Hu) trivial Hu0).defeq Htyped
  exact Hprop.defeqU_l Hc.checking.tr.wf Hc.mlctx_wf.tr.wf.toCtx Heq



/-- The exact fresh local context used by the singleton-field traversal. -/
def eliminationFieldContext (c : AddInductive.Context) (name : Name)
    (dom : Expr) (bi : BinderInfo) : AddInductive.Context :=
  { c with
    ngen := c.ngen.next
    lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
      (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
    checkLCtx := c.checkLCtx.mkLocalDecl ⟨c.ngen.curr⟩ name
      (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi }

/-- Loop relation of the singleton decision (`isLargeEliminator.loop`). Each field is either
checked to be a proof or added to the result arguments required at the leaf. -/
inductive LargeEliminationCheck (stats : AddInductive.InductiveStats) :
    AddInductive.Context → Expr → Nat → Array Expr → Prop where
  | done {c type i required} : type.isForall = false →
      required.all type.getAppArgs.contains = true →
      LargeEliminationCheck stats c type i required
  | param {c name dom body bi i required} : i < stats.params.size →
      LargeEliminationCheck stats (eliminationFieldContext c name dom bi)
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1) required →
      LargeEliminationCheck stats c (.forallE name dom body bi) i required
  | proof {c name dom body bi i required result} : stats.params.size ≤ i →
      (monadLift (TypeChecker.ensureType dom) : AddInductive.M Expr)
        (eliminationFieldContext c name dom bi) = .ok result →
      result.sortLevel!.isAlwaysZero = true →
      LargeEliminationCheck stats (eliminationFieldContext c name dom bi)
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1) required →
      LargeEliminationCheck stats c (.forallE name dom body bi) i required
  | index {c name dom body bi i required result} : stats.params.size ≤ i →
      (monadLift (TypeChecker.ensureType dom) : AddInductive.M Expr)
        (eliminationFieldContext c name dom bi) = .ok result →
      result.sortLevel!.isAlwaysZero = false →
      LargeEliminationCheck stats (eliminationFieldContext c name dom bi)
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1)
        (required.push (.fvar ⟨c.ngen.curr⟩)) →
      LargeEliminationCheck stats c (.forallE name dom body bi) i required

/-- A successful executable singleton check satisfies `LargeEliminationCheck`. -/
theorem AddInductive.isLargeEliminator.loop.trace
    {stats : AddInductive.InductiveStats} {c : AddInductive.Context}
    {type : Expr} {i : Nat} {required : Array Expr} {fuel : Nat}
    (H : AddInductive.isLargeEliminator.loop stats type i required fuel c = .ok true) :
    LargeEliminationCheck stats c type i required := by
  induction fuel generalizing c type i required with
  | zero => simp [AddInductive.isLargeEliminator.loop] at H
  | succ fuel ih =>
    cases type with
    | forallE name dom body bi =>
      rw [AddInductive.isLargeEliminator.loop] at H
      let next := eliminationFieldContext c name dom bi
      let arg := Expr.fvar ⟨c.ngen.curr⟩
      change ((do
        let mut toCheck := required
        if i ≥ stats.params.size then
          if !(← TypeChecker.ensureType dom).sortLevel!.isAlwaysZero then
            toCheck := toCheck.push arg
        AddInductive.isLargeEliminator.loop stats (body.instantiate1 arg)
          (i + 1) toCheck fuel : AddInductive.M Bool) next) = .ok true at H
      by_cases hparam : i < stats.params.size
      · have hnot : ¬i ≥ stats.params.size := by omega
        simp only [hnot, ↓reduceIte] at H
        exact .param hparam (ih H)
      · have hfield : i ≥ stats.params.size := by omega
        simp only [hfield, ↓reduceIte] at H
        cases hcheck : (monadLift (TypeChecker.ensureType dom) : AddInductive.M Expr) next with
        | error e => simp [bind, ReaderT.bind, hcheck, Except.bind] at H
        | ok result =>
          cases hz : result.sortLevel!.isAlwaysZero with
          | false =>
            apply LargeEliminationCheck.index hfield hcheck hz
            apply ih
            simpa [bind, ReaderT.bind, hcheck, Except.bind, hz] using H
          | true =>
            apply LargeEliminationCheck.proof hfield hcheck hz
            apply ih
            simpa [bind, ReaderT.bind, hcheck, Except.bind, hz] using H
    | _ =>
      simp only [AddInductive.isLargeEliminator.loop] at H
      apply LargeEliminationCheck.done rfl
      exact Except.ok.inj H



/-- A field classified as a proof by the singleton check has an unannotated domain that is a
proposition in the field-prefix context, not only beneath the newly opened field. -/
theorem ContextWF.UnannotatedDomain.proof_of_largeEliminationCheck
    {c : AddInductive.Context} {name : Name} {bi : BinderInfo}
    (Hc : ContextWF c) (Hdom : Hc.UnannotatedDomain dom source' consumed')
    (Hdom₀ : Hc.atCheckLCtx.UnannotatedDomain dom source₀ consumed₀)
    (Hrun : (monadLift (TypeChecker.ensureType dom) : AddInductive.M Expr)
      (eliminationFieldContext c name dom bi) = .ok result)
    (Hzero : result.sortLevel!.isAlwaysZero = true) :
    Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx consumed' (.sort .zero) := by
  let Hnext := Hc.withCheckedLocalDecl (name := name) (bi := bi)
    Hdom.unannotated Hdom.isType Hdom₀.unannotated Hdom₀.isType
  have W : VLCtx.FVLift Hc.mlctx.vlctx Hnext.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  have Hraw := Hdom.source.weakFV Hc.checking.tr.wf.orderedStrong W Hnext.mlctx_wf.tr.wf
  have W₀ : VLCtx.FVLift Hc.chk.vlctx Hnext.chk.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  have Hraw₀ := Hdom₀.source.weakFV Hc.checking.tr.wf.orderedStrong W₀
    Hnext.check.wf.tr.wf
  have Hprop := ensureTypeInContext.proof_of_isAlwaysZero Hnext Hraw Hraw₀
    Hrun Hzero
  have Wctx : Ctx.LiftN 1 0 Hc.mlctx.vlctx.toCtx
      Hnext.mlctx.vlctx.toCtx := .zero [consumed'] rfl
  -- `source'` is already a type in the field-prefix context; uniqueness of
  -- typing beneath the new binder identifies its sort with `Prop`.
  rcases Hdom.source_defeq with ⟨u, Hu⟩
  have Hsrc : Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
      source' (.sort u) := Hu.hasType.1
  have Hweak := Hsrc.weakN Hc.checking.tr.wf.ordered Wctx
  have Hsort : Hc.venv.IsDefEqU c.lparams.length Hnext.mlctx.vlctx.toCtx
      (.sort u) (.sort .zero) :=
    VEnv.IsDefEq.uniqU Hc.checking.tr.wf Hnext.mlctx_wf.tr.wf.toCtx Hweak Hprop
  have hu : u ≈ .zero :=
    VEnv.IsDefEqU.sort_inv Hc.checking.tr.wf Hnext.mlctx_wf.tr.wf.toCtx Hsort
  rcases Hsrc.isType Hc.checking.tr.wf Hc.mlctx_wf.tr.wf.toCtx with ⟨_, HsortTy⟩
  have Hbase : Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
      source' (.sort .zero) :=
    .defeqDF (.sortDF (HsortTy.sort_inv Hc.checking.tr.wf.ordered) trivial hu) Hsrc
  exact Hbase.defeqU_l Hc.checking.tr.wf Hc.mlctx_wf.tr.wf.toCtx ⟨_, Hu⟩


/-- Boolean argument containment recognizes a literal field variable even
though executable expression equality is alpha equivalence. -/
theorem LargeEliminationCheck.contains_bvar_of_fvar
    (Hargs : List.Forall₂ (TrExprS env Us Δ) args args')
    (Hcontains : args.contains (.fvar fv) = true)
    (Hfind : Δ.find? (.inr fv) = some (.bvar i, type)) :
    VExpr.bvar i ∈ args' := by
  rcases List.contains_iff_exists_mem_beq.mp Hcontains with ⟨arg, harg, heq⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_l Hargs arg harg with
    ⟨target, htarget, Htr⟩
  have Hvar := Htr.eqv (BEq.symm heq)
  cases Hvar with
  | fvar Hlookup =>
    cases Hfind.symm.trans Hlookup
    exact htarget

end VerifyInductive
end Lean4Lean
