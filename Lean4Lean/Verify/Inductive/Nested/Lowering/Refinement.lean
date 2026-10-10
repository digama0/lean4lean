import Lean4Lean.Verify.Inductive.Recursor.Entries.AddConstants
import Lean4Lean.Verify.Inductive.Nested.Lowering.ParameterOpening

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-! # Nested lowering: occurrence typing, fresh names and restoration premises

Basic definitions for the verification of `ElimNestedInductive` (section 3.3 of
the design notes): the typing of the nested applications validated by
`validateNestedAuxiliaries` (`ClosedNestedOccurrencesTyped`), the fresh local context and
fresh auxiliary names used by lowering, the auxiliary family construction
(`AuxiliaryFamilySpec`), the source syntax checks, and the disjointness and freshness premises
of restoration. -/

/-- Fresh local-context invariant for the `_nested_fresh` name generator used
by `ElimNestedInductive.withParams`. -/
structure NestedBindingContextWF (lctx : LocalContext)
    (ngen : NameGenerator) where
  wf : lctx.WF
  fresh : ∀ fv ∈ lctx.fvars, ngen.Reserves fv
  generated : ∀ fv ∈ lctx.fvars,
    ∃ i, fv = ⟨.num ngen.namePrefix i⟩
  findCDecl : ∀ fv ∈ lctx.fvars, ∃ index name type bi kind,
    lctx.find? fv = some (.cdecl index fv name type bi kind)

theorem NestedBindingContextWF.empty (ngen : NameGenerator) :
    NestedBindingContextWF {} ngen :=
  ⟨.nil, by
    intro fv hmem
    have hempty :
        ((.empty : PersistentArray (Option LocalDecl)).toList') = [] := rfl
    have htoList : ({} : LocalContext).toList = [] := by
      unfold LocalContext.toList
      change ((.empty : PersistentArray (Option LocalDecl)).toList').reverse.filterMap id = []
      rw [hempty]
      rfl
    rw [LocalContext.fvars, htoList] at hmem
    simp at hmem, by
    intro fv hmem
    have hempty :
        ((.empty : PersistentArray (Option LocalDecl)).toList') = [] := rfl
    have htoList : ({} : LocalContext).toList = [] := by
      unfold LocalContext.toList
      change ((.empty : PersistentArray (Option LocalDecl)).toList').reverse.filterMap id = []
      rw [hempty]
      rfl
    rw [LocalContext.fvars, htoList] at hmem
    simp at hmem, by
    intro fv hmem
    have hempty :
        ((.empty : PersistentArray (Option LocalDecl)).toList') = [] := rfl
    have htoList : ({} : LocalContext).toList = [] := by
      unfold LocalContext.toList
      change ((.empty : PersistentArray (Option LocalDecl)).toList').reverse.filterMap id = []
      rw [hempty]
      rfl
    rw [LocalContext.fvars, htoList] at hmem
    simp at hmem⟩

theorem NestedBindingContextWF.withLocalDecl
    (H : NestedBindingContextWF lctx ngen)
    (name : Name) (type : Expr) (bi : BinderInfo) :
    NestedBindingContextWF
      (lctx.mkLocalDecl ⟨ngen.curr⟩ name type bi) ngen.next where
  wf := H.wf.mkLocalDecl <| by
    rw [H.wf.find?_eq_find?_toList]
    by_contra hne
    rcases Option.ne_none_iff_exists.mp hne with ⟨d, hfind⟩
    exact ngen.not_reserves_self (H.fresh _ <| by
      rw [LocalContext.fvars]
      apply List.mem_map.mpr
      have hp := List.find?_some hfind.symm
      have heq : ⟨ngen.curr⟩ = d.fvarId := by simpa using hp
      exact ⟨d, List.mem_of_find?_eq_some hfind.symm, heq.symm⟩)
  fresh := by
    intro fv hmem
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact ngen.next_reserves_self
    · exact (H.fresh _ hmem).mono NameGenerator.LE.next
  generated := by
    intro fv hmem
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact ⟨ngen.idx, rfl⟩
    · rcases H.generated _ hmem with ⟨i, hi⟩
      exact ⟨i, by simpa [NameGenerator.next] using hi⟩
  findCDecl := by
    intro fv hmem
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · refine ⟨lctx.decls.size, name, type, bi, .default, ?_⟩
      simp [LocalContext.mkLocalDecl, LocalContext.find?,
        H.wf.map_wf.find?_insert]
    · rcases H.findCDecl fv hmem with
        ⟨index, oldName, oldType, oldBi, kind, hfind⟩
      refine ⟨index, oldName, oldType, oldBi, kind, ?_⟩
      simp only [LocalContext.mkLocalDecl, LocalContext.find?,
        H.wf.map_wf.find?_insert]
      rw [if_neg]
      · exact hfind
      · intro heq
        have : fv = ⟨ngen.curr⟩ :=
          (LawfulBEq.eq_of_beq heq).symm
        subst fv
        exact ngen.not_reserves_self (H.fresh _ hmem)

/-- A binding context produced by nested lowering is reserved by the
independent kernel type-checker generator whenever the two generator
prefixes are distinct. -/
theorem NestedBindingContextWF.kernelFreshOfPrefix
    (H : NestedBindingContextWF lctx ngen)
    (hprefix : ngen.namePrefix = `_nested_fresh) :
    ∀ fv ∈ lctx.fvars,
      ({} : TypeChecker.State).ngen.Reserves fv := by
  intro fv hfv
  rcases H.generated fv hfv with ⟨i, rfl⟩
  apply NameGenerator.Reserves.num_of_prefix_ne
  rw [hprefix]
  simp

/-- Exact free-variable array threaded alongside the nested local context. -/
structure NestedBoundParams (lctx : LocalContext) (params : Array Expr) where
  fvars : List FVarId
  expressions : params = (fvars.map Expr.fvar).toArray
  members : ∀ fv ∈ fvars, fv ∈ lctx.fvars
  nodup : fvars.Nodup

def NestedBoundParams.empty : NestedBoundParams {} #[] :=
  ⟨[], by simp, by simp, by simp⟩

def NestedBoundParams.push
    (H : NestedBoundParams lctx params)
    (Hctx : NestedBindingContextWF lctx ngen)
    (name : Name) (type : Expr) (bi : BinderInfo) :
    NestedBoundParams (lctx.mkLocalDecl ⟨ngen.curr⟩ name type bi)
      (params.push (.fvar ⟨ngen.curr⟩)) where
  fvars := H.fvars ++ [⟨ngen.curr⟩]
  expressions := by simp [H.expressions]
  members := by
    intro fv hmem
    simp only [List.mem_append, List.mem_singleton] at hmem
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons]
    rcases hmem with hold | rfl
    · exact Or.inr (H.members fv hold)
    · exact Or.inl rfl
  nodup := by
    apply List.nodup_append.mpr
    refine ⟨H.nodup, by simp, ?_⟩
    intro fv hfv fresh hfresh
    simp only [List.mem_singleton] at hfresh
    subst fresh
    intro heq
    subst fv
    exact ngen.not_reserves_self <| Hctx.fresh _ (H.members _ hfv)

def NestedBoundParams.toSelection
    (H : NestedBoundParams lctx params) (Hctx : NestedBindingContextWF lctx ngen) :
    CDeclArray lctx params where
  fvars := H.fvars
  expressions := H.expressions
  declarations fv hfv := Hctx.findCDecl fv (H.members fv hfv)

/-- Parameter contexts opened by nested lowering can close any expression
whose free variables are among the opened parameters. This strengthens the
plain local-context/selection invariants with the exact fact needed when a
generated auxiliary family is itself processed by the dynamic queue. -/
structure NestedClosingContext (lctx : LocalContext) (params : Array Expr)
    (ngen : NameGenerator) where
  binding : NestedBindingContextWF lctx ngen
  selection : CDeclArray lctx params
  nodup : selection.fvars.Nodup
  close : ∀ body, body.FVarsIn (· ∈ selection.fvars) →
    (lctx.mkForall params body).FVarsIn fun _ => False

def NestedClosingContext.empty (ngen : NameGenerator) :
    NestedClosingContext {} #[] ngen where
  binding := NestedBindingContextWF.empty ngen
  selection := {
    fvars := []
    expressions := by simp
    declarations := by simp }
  nodup := by simp
  close := by
    intro body Hbody
    have Hbody' : body.FVarsIn (fun _ => False) := by
      simpa [Lean4Lean.FVarsIn] using Hbody
    rw [show (#[] : Array Expr) = ([].map Expr.fvar).toArray from rfl,
      LocalContext.mkForall, LocalContext.mkBinding_eqN]
    simpa only [LocalContext.mkBindingListN_nil] using Hbody'

def NestedClosingContext.push
    (H : NestedClosingContext lctx params ngen)
    (name : Name) (dom : Expr) (bi : BinderInfo)
    (Hdom : dom.FVarsIn (· ∈ H.selection.fvars)) :
    NestedClosingContext
      (lctx.mkLocalDecl ⟨ngen.curr⟩ name dom bi)
      (params.push (.fvar ⟨ngen.curr⟩)) ngen.next := by
  let id : FVarId := ⟨ngen.curr⟩
  let nextLctx := lctx.mkLocalDecl id name dom bi
  let nextParams := params.push (.fvar id)
  have hidNotMem : id ∉ H.selection.fvars := by
    intro hid
    rcases H.selection.declarations id hid with
      ⟨index, oldName, oldType, oldBi, kind, hfind⟩
    exact ngen.not_reserves_self (H.binding.fresh id <| by
      rw [LocalContext.fvars]
      apply List.mem_map.mpr
      rw [H.binding.wf.find?_eq_find?_toList] at hfind
      exact ⟨.cdecl index id oldName oldType oldBi kind,
        List.mem_of_find?_eq_some hfind, rfl⟩)
  let nextSelection : CDeclArray nextLctx nextParams := {
    fvars := H.selection.fvars ++ [id]
    expressions := by
      simp [nextParams, H.selection.expressions]
    declarations := by
      intro fv hfv
      simp only [List.mem_append, List.mem_singleton] at hfv
      rcases hfv with hold | rfl
      · rcases H.selection.declarations fv hold with
          ⟨index, oldName, oldType, oldBi, kind, hfind⟩
        refine ⟨index, oldName, oldType, oldBi, kind, ?_⟩
        simp only [nextLctx, LocalContext.mkLocalDecl, LocalContext.find?,
          H.binding.wf.map_wf.find?_insert]
        rw [if_neg]
        · exact hfind
        · intro heq
          exact hidNotMem (by
            have heq' : id = fv := beq_iff_eq.mp heq
            exact heq' ▸ hold)
      · refine ⟨lctx.decls.size, name, dom, bi, .default, ?_⟩
        simp [nextLctx, LocalContext.mkLocalDecl, LocalContext.find?,
          H.binding.wf.map_wf.find?_insert] }
  refine {
    binding := H.binding.withLocalDecl name dom bi
    selection := nextSelection
    nodup := by
      simp only [nextSelection]
      apply List.nodup_append.mpr
      refine ⟨H.nodup, by simp, ?_⟩
      intro fv hfv fv' hfv'
      simp only [List.mem_singleton] at hfv'
      subst fv'
      exact fun heq => hidNotMem (heq ▸ hfv)
    close := ?_ }
  intro body Hbody
  have hnextDecls : ∀ fv ∈ nextSelection.fvars, ∃ decl,
      nextLctx.find? fv = some decl := by
    intro fv hfv
    rcases nextSelection.declarations fv hfv with
      ⟨index, declName, type, declBi, kind, hfind⟩
    exact ⟨.cdecl index fv declName type declBi kind, hfind⟩
  have holdDecls : ∀ fv ∈ H.selection.fvars, ∃ decl,
      nextLctx.find? fv = some decl := by
    intro fv hfv
    exact hnextDecls fv (by simp [nextSelection, hfv])
  have hfindOld : ∀ fv ∈ H.selection.fvars,
      nextLctx.find? fv = lctx.find? fv := by
    intro fv hfv
    simp only [nextLctx, LocalContext.mkLocalDecl, LocalContext.find?,
      H.binding.wf.map_wf.find?_insert]
    rw [if_neg]
    intro heq
    exact hidNotMem (by
      have heq' : id = fv := beq_iff_eq.mp heq
      exact heq' ▸ hfv)
  have happend :
      LocalContext.mkBindingListN false nextLctx nextSelection.fvars body =
        LocalContext.mkBindingListN false nextLctx H.selection.fvars
          (.forallE name dom (body.abstractN [id]) bi) := by
    rw [LocalContext.mkBindingListN_eq_fold hnextDecls (by
      simp only [nextSelection]
      apply List.nodup_append.mpr
      refine ⟨H.nodup, by simp, ?_⟩
      intro fv hfv fv' hfv'
      simp only [List.mem_singleton] at hfv'
      subst fv'
      exact fun heq => hidNotMem (heq ▸ hfv))]
    rw [LocalContext.mkBindingListN_eq_fold holdDecls H.nodup]
    simp only [nextSelection, List.foldr_append, List.foldr_cons,
      List.foldr_nil]
    simp [LocalContext.mkBindingList1N, nextLctx,
      LocalContext.mkLocalDecl, LocalContext.find?,
      H.binding.wf.map_wf.find?_insert, Expr.abstractN_nil]
  have hcloseEq :
      nextLctx.mkForall nextParams body =
        lctx.mkForall params (.forallE name dom (body.abstractN [id]) bi) := by
    rw [show nextParams = (nextSelection.fvars.map Expr.fvar).toArray from
      nextSelection.expressions]
    rw [show params = (H.selection.fvars.map Expr.fvar).toArray from
      H.selection.expressions]
    rw [LocalContext.mkForall, LocalContext.mkBinding_eqN,
      LocalContext.mkForall, LocalContext.mkBinding_eqN, happend]
    exact LocalContext.mkBindingListN_congr hfindOld
  rw [hcloseEq]
  apply H.close
  constructor
  · exact Hdom
  · apply FVarsIn.abstractN_of
    exact Hbody.mono fun fv hfv => by
      simp only [nextSelection, List.mem_append, List.mem_singleton] at hfv
      rcases hfv with hfv | hfv
      · exact Or.inr hfv
      · exact Or.inl (by simp [hfv])

theorem LoweringParamOpening.forallTelescope
    (H : LoweringParamOpening lctx As e n outLctx tail outAs) :
    ∃ residual, Expr.ForallTelescope e n residual := by
  induction H with
  | done => exact ⟨_, .nil _⟩
  | step Hnext ih =>
    rcases ih with ⟨openedResidual, Hopened⟩
    rw [Expr.instantiate1_eq] at Hopened
    rcases Hopened.reflect_instantiate1'_fvar with
      ⟨sourceResidual, Hsource⟩
    exact ⟨sourceResidual, .cons Hsource⟩

theorem LoweringParamOpening.tailFVarsIn
    (H : LoweringParamOpening lctx params type n outLctx tail outParams)
    (Hselection : CDeclArray outLctx outParams)
    (Htype : type.FVarsIn (· ∈ Hselection.fvars)) :
    tail.FVarsIn (· ∈ Hselection.fvars) := by
  induction H with
  | done => exact Htype
  | @step lctx params name dom body bi id n outLctx tail outParams Hnext ih =>
    apply ih Hselection
    rw [Expr.instantiate1_eq]
    apply Htype.2.instantiate1
    simp only [Lean4Lean.FVarsIn]
    apply Hselection.fvar_mem
    rcases Hnext.params_extension with ⟨suffix, hsuffix, _⟩
    apply Array.mem_toList_iff.mp
    rw [hsuffix]
    simp

/-- Opening the parameter telescope of a closed type yields a closed tail. -/
theorem LoweringParamOpening.tailClosed
    (H : LoweringParamOpening lctx params source n outLctx tail outParams)
    (hsource : Closed source) : Closed tail := by
  induction H with
  | done => exact hsource
  | step _ ih =>
    apply ih
    rw [Expr.instantiate1_eq]
    exact hsource.2.instantiate1 trivial

theorem LoweringParamOpening.initial_size
    (H : LoweringParamOpening {} #[] type n outLctx tail outParams) :
    outParams.size = n := by simpa using H.params_size

/-- Strengthened parameter opening for a closed source telescope.  Besides
the parameter opening relation, the continuation receives a certificate that
re-closing an expression open over exactly those parameters is closed. -/
private theorem nestedWithParamsLoop_refinesClosing {α : Type}
    (k : LocalContext → Expr → Array Expr →
      Lean4Lean.ElimNestedInductive.M α)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (Hclosing : NestedClosingContext lctx params state.ngen)
    (Htype : type.FVarsIn (· ∈ Hclosing.selection.fvars))
    (Q : α × Lean4Lean.ElimNestedInductive.State → Prop)
    (Hk : ∀ outLctx tail outParams outState,
      LoweringParamOpening lctx params type n outLctx tail outParams →
      (HoutClosing :
        NestedClosingContext outLctx outParams outState.ngen) →
      tail.FVarsIn (· ∈ HoutClosing.selection.fvars) →
      outState.newTypes = state.newTypes →
      outState.nestedAux = state.nestedAux →
      outState.nextIdx = state.nextIdx →
      outState.ngen.namePrefix = state.ngen.namePrefix →
      outState.lvls = state.lvls →
      (k outLctx tail outParams env outState).WF Q) :
    (Lean4Lean.ElimNestedInductive.withParams.loop
      k lctx type params n env state).WF Q := by
  induction n generalizing lctx type params state with
  | zero =>
    simpa [Lean4Lean.ElimNestedInductive.withParams.loop] using
      Hk lctx type params state .done Hclosing Htype rfl rfl rfl
        rfl rfl
  | succ n ih =>
    cases type with
    | forallE name dom body bi =>
      simp only [Lean4Lean.ElimNestedInductive.withParams.loop]
      simp only [mkFreshId, getNGen, setNGen,
        bind, StateT.bind, ReaderT.bind, pure, StateT.pure, ReaderT.pure]
      let HnextClosing := Hclosing.push name dom bi Htype.1
      have HnextType :
          (body.instantiate1 (.fvar ⟨state.ngen.curr⟩)).FVarsIn
            (· ∈ HnextClosing.selection.fvars) := by
        rw [Expr.instantiate1_eq]
        have HbodyNext :
            body.FVarsIn (· ∈ HnextClosing.selection.fvars) := by
          apply Htype.2.mono
          intro fv hfv
          change fv ∈ Hclosing.selection.fvars ++ [⟨state.ngen.curr⟩]
          simp [hfv]
        apply HbodyNext.instantiate1
        simp only [Lean4Lean.FVarsIn]
        change (⟨state.ngen.curr⟩ : FVarId) ∈
          Hclosing.selection.fvars ++ [⟨state.ngen.curr⟩]
        simp
      apply ih (Hclosing := HnextClosing) (Htype := HnextType)
      intro outLctx tail outParams outState Hresult HresultClosing Htail
        hnewTypes hnestedAux hnextIdx hprefix hlvls
      exact Hk outLctx tail outParams outState (.step Hresult)
        HresultClosing Htail (by simpa using hnewTypes)
        (by simpa using hnestedAux) (by simpa using hnextIdx)
        (by simpa [NameGenerator.next] using hprefix) (by simpa using hlvls)
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
      | proj => exact Except.WF.throw

theorem ElimNestedInductive.withParams.refinesClosing {α : Type}
    (type : Expr) (nparams : Nat)
    (k : LocalContext → Expr → Array Expr →
      Lean4Lean.ElimNestedInductive.M α)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (Htype : type.FVarsIn fun _ => False)
    (Q : α × Lean4Lean.ElimNestedInductive.State → Prop)
    (Hk : ∀ lctx tail params outState,
      LoweringParamOpening {} #[] type nparams lctx tail params →
      (HoutClosing : NestedClosingContext lctx params outState.ngen) →
      tail.FVarsIn (· ∈ HoutClosing.selection.fvars) →
      outState.newTypes = state.newTypes →
      outState.nestedAux = state.nestedAux →
      outState.nextIdx = state.nextIdx →
      outState.ngen.namePrefix = state.ngen.namePrefix →
      outState.lvls = state.lvls →
      (k lctx tail params env outState).WF Q) :
    (Lean4Lean.ElimNestedInductive.withParams
      type nparams k env state).WF Q := by
  let Hclosing := NestedClosingContext.empty state.ngen
  apply nestedWithParamsLoop_refinesClosing k env state Hclosing
  · exact Htype.mono fun fv hfalse => False.elim hfalse
  · exact Hk

/-- Successful parameter instantiation has removed exactly the requested
number of leading forall binders; the returned term is precisely the exposed
residual instantiated with the supplied parameter array. -/
private theorem stripForallList_refines
    (indices : List Nat) (e : Expr) :
    ((forIn indices e fun _ current =>
      match current with
      | .forallE _ _ body _ => pure (ForInStep.yield body)
      | _ => do
        throw Lean4Lean.ElimNestedInductive.illFormed
        pure (ForInStep.yield current)) :
        Except Exception Expr).WF
      fun tail => Expr.ForallTelescope e indices.length tail := by
  induction indices generalizing e with
  | nil => exact Except.WF.pure (Expr.ForallTelescope.nil e)
  | cons i indices ih =>
    cases e with
    | forallE name dom body bi =>
      have Hrest := (ih body).mono fun tail H =>
        Expr.ForallTelescope.cons (name := name) (dom := dom) (bi := bi) H
      rw [List.forIn_cons]
      exact Except.WF.pureBind Hrest
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
      | proj => exact Except.WF.throw

theorem instantiateForallParams_refines
    (e : Expr) (n : Nat) (params : Array Expr) :
    (Lean4Lean.ElimNestedInductive.instantiateForallParams e n params).WF
      fun out => ∃ tail, Expr.ForallTelescope e n tail ∧
        out = tail.instantiateRevRange 0 n params := by
  unfold Lean4Lean.ElimNestedInductive.instantiateForallParams
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  change (((fun tail =>
      tail.instantiateRevRange 0 n params) <$>
    (forIn (List.range' 0 n) e fun _ current =>
      match current with
      | .forallE _ _ body _ => pure (ForInStep.yield body)
      | _ => do
        throw Lean4Lean.ElimNestedInductive.illFormed
        pure (ForInStep.yield current))) : Except Exception Expr).WF _
  exact Except.WF.map
    (f := fun tail => tail.instantiateRevRange 0 n params)
    (R := fun out => ∃ residual, Expr.ForallTelescope e n residual ∧
      out = residual.instantiateRevRange 0 n params)
    (stripForallList_refines (List.range' 0 n) e)
    (fun tail Htail =>
      (⟨tail, by simpa using Htail, rfl⟩ :
        ∃ residual, Expr.ForallTelescope e n residual ∧
          tail.instantiateRevRange 0 n params =
            residual.instantiateRevRange 0 n params))

theorem replaceNestedParamsCore_refines
    (params : Array Expr) (e : Expr) (args : Array Expr)
    (hsize : args.size = params.size) :
    (Lean4Lean.ElimNestedInductive.replaceParamsCore params e args).WF
      fun out => out = (e.abstract args).instantiateRev params := by
  unfold Lean4Lean.ElimNestedInductive.replaceParamsCore
  simp [hsize]
  exact Except.WF.pure rfl

theorem replaceNestedParams_state_refines
    (params : Array Expr) (e : Expr) (args : Array Expr)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hsize : args.size = params.size) :
    (Lean4Lean.ElimNestedInductive.replaceParams params e args env state).WF
      fun out => out = ((e.abstract args).instantiateRev params, state) := by
  unfold Lean4Lean.ElimNestedInductive.replaceParams
    Lean4Lean.ElimNestedInductive.replaceParamsCore
  simp [hsize]
  exact Except.WF.pure rfl

/-- The executable fresh-name search records the numeric suffix it selected,
never moves backwards from its initial counter, and returns a name absent from
the current environment. -/
structure FreshNestedName (env : Environment) (base : Name) (start : Nat)
    (name : Name) (nextIdx : Nat) : Prop where
  index : ∃ i, start ≤ i ∧ name = base.mkNum i ∧ nextIdx = i + 1
  fresh : env.contains name = false

/-- Generated cache names are unique and each retained name records a suffix
index strictly below the state's next fresh-name counter. -/
structure NestedAuxNamesWF
    (state : Lean4Lean.ElimNestedInductive.State) : Prop where
  nodup : (state.nestedAux.toList.map Prod.snd).Nodup
  indexed : ∀ (nested : Expr) (name : Name),
    (nested, name) ∈ state.nestedAux →
    ∃ index : Nat, name = Name.mkNum `_nested index ∧ index < state.nextIdx
  reserved : ∀ (nested : Expr) (name : Name),
    (nested, name) ∈ state.nestedAux →
    (`_nested).isPrefixOf name = true

def NestedAuxNamesFresh (env : Environment)
    (state : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∀ nested name, (nested, name) ∈ state.nestedAux →
    env.contains name = false

theorem NestedAuxNamesFresh.empty
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hempty : state.nestedAux = #[]) : NestedAuxNamesFresh env state := by
  intro nested name hentry
  rw [hempty] at hentry
  simp at hentry

theorem NestedAuxNamesFresh.ofCacheEq
    (H : NestedAuxNamesFresh env source)
    (haux : target.nestedAux = source.nestedAux) :
    NestedAuxNamesFresh env target := by
  intro nested name hentry
  apply H nested name
  simpa [haux] using hentry

@[simp] theorem nested_isPrefix_mkNum (index : Nat) :
    (`_nested).isPrefixOf (Name.mkNum `_nested index) = true := by
  simp [Name.isPrefixOf]

theorem NestedAuxNamesWF.empty
    (state : Lean4Lean.ElimNestedInductive.State)
    (hempty : state.nestedAux = #[]) : NestedAuxNamesWF state := by
  constructor
  · simp [hempty]
  · intro nested name hentry
    rw [hempty] at hentry
    simp at hentry
  · intro nested name hentry
    rw [hempty] at hentry
    simp at hentry

theorem NestedAuxNamesWF.ofCacheCounterEq
    (H : NestedAuxNamesWF source)
    (haux : target.nestedAux = source.nestedAux)
    (hnext : target.nextIdx = source.nextIdx) : NestedAuxNamesWF target := by
  constructor
  · simpa [haux] using H.nodup
  · intro nested name hentry
    have hold : (nested, name) ∈ source.nestedAux := by
      simpa [haux] using hentry
    rcases H.indexed nested name hold with ⟨index, hname, hindex⟩
    exact ⟨index, hname, by simpa [hnext] using hindex⟩
  · intro nested name hentry
    apply H.reserved nested name
    simpa [haux] using hentry

theorem findUniqueName_refines
    (env : Environment) (base : Name) (start fuel : Nat) :
    (Lean4Lean.ElimNestedInductive.findUniqueName env base start fuel).WF
      fun out => FreshNestedName env base start out.1 out.2 := by
  induction fuel generalizing start with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [Lean4Lean.ElimNestedInductive.findUniqueName]
    split
    next hcontains =>
      exact (ih (start := start + 1)).mono fun out H => ⟨
        ⟨H.index.choose, Nat.le_trans (Nat.le_add_right start 1)
          H.index.choose_spec.1, H.index.choose_spec.2⟩,
        H.fresh⟩
    next hcontains =>
      have hfresh : env.contains (base.mkNum start) = false := by
        cases h : env.contains (base.mkNum start) <;> simp_all
      exact Except.WF.pure ⟨⟨start, Nat.le_refl _, rfl, rfl⟩, hfresh⟩

/-- `mkUniqueName` is a state-preserving wrapper around the pure search: only
the fresh-name counter changes. -/
theorem mkUniqueName_refines
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (base : Name) :
    (Lean4Lean.ElimNestedInductive.mkUniqueName base env state).WF fun out =>
      ∃ nextIdx,
        FreshNestedName env base state.nextIdx out.1 nextIdx ∧
        out.2 = { state with nextIdx } := by
  unfold Lean4Lean.ElimNestedInductive.mkUniqueName
  exact (findUniqueName_refines env base state.nextIdx
    (env.constants.toList.length + 1)).bind fun out H =>
      Except.WF.pure ⟨out.2, H, rfl⟩

private theorem environmentGet_refines (env : Environment) (name : Name) :
    (env.get name).WF fun info => env.find? name = some info := by
  unfold Lean.Kernel.Environment.get
  split
  next h => exact Except.WF.pure h
  next => exact Except.WF.throw

/-- Every declared type of `env` has no free variables; this holds in every
environment modelled by `VEnvs.WF` (`VEnvs.WF.environmentTypesClosed`). -/
def EnvironmentTypesClosed (env : Environment) : Prop :=
  ∀ name info, env.find? name = some info →
    info.type.FVarsIn fun _ => False

theorem VEnvs.WF.environmentTypesClosed
    (H : VEnvs.WF env ves) : EnvironmentTypesClosed env := by
  intro name info hfind
  rcases (H.tr (safety := .unsafe)).find? hfind
      DefinitionSafety.unsafe_le with ⟨vinfo, _hvfind, Htr⟩
  exact Htr.2.2.fvarsIn.mono fun fv hfv => by simp at hfv

/-- Every declared type of `env` has no loose bound variables; this holds in every
environment modelled by `VEnvs.WF` (`VEnvs.WF.environmentTypesBVarClosed`). -/
def EnvironmentTypesBVarClosed (env : Environment) : Prop :=
  ∀ name info, env.find? name = some info → Closed info.type

theorem VEnvs.WF.environmentTypesBVarClosed
    (H : VEnvs.WF env ves) : EnvironmentTypesBVarClosed env := by
  intro name info hfind
  rcases (H.tr (safety := .unsafe)).find? hfind
      DefinitionSafety.unsafe_le with ⟨vinfo, _hvfind, Htr⟩
  have h := Htr.2.2.closed
  simpa [VLCtx.bvars] using h

theorem Expr.ForallTelescope.resultFVarsIn
    (H : Expr.ForallTelescope outer arity result)
    (Houter : outer.FVarsIn P) : result.FVarsIn P := by
  induction H with
  | nil => exact Houter
  | cons _ ih => exact ih Houter.2

structure AuxiliaryConstructorSpec
    (env : Environment) (lctx : LocalContext) (As : Array Expr)
    (levels : List Level) (nparams : Nat) (args : Array Expr)
    (sourceFamily auxFamily sourceName : Name) (target : Constructor) : Prop where
  source : ∃ sourceInfo sourceTail,
    env.find? sourceName = some sourceInfo ∧
    Expr.ForallTelescope
      (sourceInfo.type.instantiateLevelParams sourceInfo.levelParams levels)
      nparams sourceTail ∧
    target.name = sourceName.replacePrefix sourceFamily auxFamily ∧
    target.type = lctx.mkForall As
      (sourceTail.instantiateRevRange 0 nparams args)

theorem AuxiliaryConstructorSpec.closed
    (H : AuxiliaryConstructorSpec env lctx As levels nparams args sourceFamily
      auxFamily sourceName target)
    (Henv : EnvironmentTypesClosed env)
    (Hclosing : NestedClosingContext lctx As ngen)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (· ∈ Hclosing.selection.fvars)) :
    target.type.FVarsIn fun _ => False := by
  rcases H.source with
    ⟨sourceInfo, sourceTail, hfind, Htelescope, _hname, htype⟩
  rw [htype]
  apply Hclosing.close
  apply FVarsIn.instantiateRevRange
  · apply Htelescope.resultFVarsIn
    apply ((Henv sourceName sourceInfo hfind).mono fun fv hfalse =>
      False.elim hfalse).instantiateLevelParams
    exact Hlevels
  · exact Hargs

inductive AuxiliaryConstructorSpecs
    (env : Environment) (lctx : LocalContext) (As : Array Expr)
    (levels : List Level) (nparams : Nat) (args : Array Expr)
    (sourceFamily auxFamily : Name) : List Name → List Constructor → Prop
  | nil : AuxiliaryConstructorSpecs env lctx As levels nparams args
      sourceFamily auxFamily [] []
  | cons : AuxiliaryConstructorSpec env lctx As levels nparams args sourceFamily
      auxFamily sourceName target →
      AuxiliaryConstructorSpecs env lctx As levels nparams args sourceFamily
        auxFamily sourceNames targets →
      AuxiliaryConstructorSpecs env lctx As levels nparams args sourceFamily
        auxFamily (sourceName :: sourceNames) (target :: targets)

theorem AuxiliaryConstructorSpecs.length_eq
    (H : AuxiliaryConstructorSpecs env lctx As levels nparams args sourceFamily
      auxFamily sourceNames targets) :
    sourceNames.length = targets.length := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Select the matching source and target constructor specifications by position.  The
generated auxiliary builder traverses the mutual constructor-name list and
target list in lockstep; later restoration proofs need the corresponding
single-constructor specialization without falling back to name search. -/
theorem AuxiliaryConstructorSpecs.entryAt
    (H : AuxiliaryConstructorSpecs env lctx As levels nparams args sourceFamily
      auxFamily sourceNames targets)
    (i : Nat) (hi : i < sourceNames.length) :
    ∃ htarget : i < targets.length,
      AuxiliaryConstructorSpec env lctx As levels nparams args sourceFamily
        auxFamily sourceNames[i] targets[i] := by
  induction H generalizing i with
  | nil => simp at hi
  | @cons sourceName target sourceNames targets Hhead Htail ih =>
    cases i with
    | zero => exact ⟨by simp, Hhead⟩
    | succ i =>
      have hi' : i < sourceNames.length := by simpa using hi
      rcases ih i hi' with ⟨htarget, Hentry⟩
      exact ⟨by simpa using htarget, Hentry⟩

theorem AuxiliaryConstructorSpecs.closed
    (H : AuxiliaryConstructorSpecs env lctx As levels nparams args sourceFamily
      auxFamily sourceNames targets)
    (Henv : EnvironmentTypesClosed env)
    (Hclosing : NestedClosingContext lctx As ngen)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (· ∈ Hclosing.selection.fvars)) :
    ∀ target ∈ targets, target.type.FVarsIn fun _ => False := by
  induction H with
  | nil => simp
  | cons Hhead Htail ih =>
    intro target htarget
    simp only [List.mem_cons] at htarget
    rcases htarget with rfl | htail
    · exact Hhead.closed Henv Hclosing Hlevels Hargs
    · exact ih target htail

private theorem buildAuxConstructors_refines
    (env : Environment) (lctx : LocalContext) (As : Array Expr)
    (levels : List Level) (nparams : Nat) (args : Array Expr)
    (sourceFamily auxFamily : Name) (sourceNames : List Name) :
    (sourceNames.mapM fun sourceName => do
      let sourceInfo ← env.get sourceName
      let targetName := sourceName.replacePrefix sourceFamily auxFamily
      let sourceType := sourceInfo.type.instantiateLevelParams
        sourceInfo.levelParams levels
      let targetType ← Lean4Lean.ElimNestedInductive.instantiateForallParams
        sourceType nparams args
      return ({ name := targetName, type := lctx.mkForall As targetType } :
        Constructor)).WF fun targets =>
          AuxiliaryConstructorSpecs env lctx As levels nparams args sourceFamily
            auxFamily sourceNames targets := by
  induction sourceNames with
  | nil => exact Except.WF.pure .nil
  | cons sourceName sourceNames ih =>
    rw [List.mapM_cons]
    have Hhead : (do
        let sourceInfo ← env.get sourceName
        let targetName := sourceName.replacePrefix sourceFamily auxFamily
        let sourceType := sourceInfo.type.instantiateLevelParams
          sourceInfo.levelParams levels
        let targetType ←
          Lean4Lean.ElimNestedInductive.instantiateForallParams
            sourceType nparams args
        return ({ name := targetName, type := lctx.mkForall As targetType } :
          Constructor)).WF fun target =>
            AuxiliaryConstructorSpec env lctx As levels nparams args sourceFamily
              auxFamily sourceName target :=
      (environmentGet_refines env sourceName).bind fun sourceInfo hlookup =>
      (instantiateForallParams_refines
        (sourceInfo.type.instantiateLevelParams sourceInfo.levelParams levels)
        nparams args).bind fun targetType Htype => Except.WF.pure
          ⟨⟨sourceInfo, Htype.choose, hlookup, Htype.choose_spec.1,
            rfl, congrArg (lctx.mkForall As) Htype.choose_spec.2⟩⟩
    exact Hhead.bind fun _ Htarget =>
      ih.bind fun _ Htargets => Except.WF.pure (.cons Htarget Htargets)

/-- Pure auxiliary construction retains an independently inspectable account
of the source family, its opened family type, parameter substitution, and every
generated constructor. -/
structure AuxiliaryFamilySpec
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (levels : List Level) (nparams : Nat) (args : Array Expr)
    (sourceName auxName : Name) (sourceInfo : InductiveVal)
    (data : Lean4Lean.ElimNestedInductive.AuxiliaryData) : Prop where
  lookup : env.find? sourceName = some (.inductInfo sourceInfo)
  opening : ∃ sourceTail,
    Expr.ForallTelescope
      (sourceInfo.type.instantiateLevelParams sourceInfo.levelParams levels)
      nparams sourceTail ∧
    data.type.type = lctx.mkForall As
      (sourceTail.instantiateRevRange 0 nparams args)
  arity : As.size = params.size
  nested : data.nested =
    ((mkAppRange (.const sourceName levels) 0 nparams args).abstract As).instantiateRev params
  name : data.type.name = auxName
  constructors : AuxiliaryConstructorSpecs env lctx As levels nparams args
    sourceName auxName sourceInfo.ctors data.type.ctors

theorem AuxiliaryFamilySpec.constructors_length
    (H : AuxiliaryFamilySpec env lctx params As levels nparams args sourceName
      auxName sourceInfo data) :
    sourceInfo.ctors.length = data.type.ctors.length :=
  H.constructors.length_eq

/-- Select the source constructor and generated auxiliary constructor at the
same position in an auxiliary-family construction. -/
theorem AuxiliaryFamilySpec.constructorAt
    (H : AuxiliaryFamilySpec env lctx params As levels nparams args sourceName
      auxName sourceInfo data)
    (i : Nat) (hi : i < sourceInfo.ctors.length) :
    ∃ htarget : i < data.type.ctors.length,
      AuxiliaryConstructorSpec env lctx As levels nparams args sourceName auxName
        sourceInfo.ctors[i] data.type.ctors[i] :=
  H.constructors.entryAt i hi

/-- Auxiliary construction removes exactly the common-parameter prefix of the
container family and keeps its residual telescope (its indices and result sort).
This theorem exposes that residual, instantiated at the specialization arguments,
as the post-parameter tail of the auxiliary family's type. -/
theorem AuxiliaryFamilySpec.generatedFamilyTelescope
    (H : AuxiliaryFamilySpec env lctx params As levels nparams args sourceName
      auxName sourceInfo data)
    (Hselection : CDeclArray lctx As) :
    ∃ sourceTail,
      Expr.ForallTelescope
        (sourceInfo.type.instantiateLevelParams sourceInfo.levelParams levels)
        nparams sourceTail ∧
      Expr.ForallTelescope data.type.type params.size
        ((sourceTail.instantiateRevRange 0 nparams args).abstractN
          Hselection.fvars) := by
  rcases H.opening with ⟨sourceTail, Hsource, htype⟩
  refine ⟨sourceTail, Hsource, ?_⟩
  rw [htype, ← H.arity]
  exact Hselection.forallTelescope
    (sourceTail.instantiateRevRange 0 nparams args)

def InductiveConstructorsClosed (type : InductiveType) : Prop :=
  ∀ ctor ∈ type.ctors, ctor.type.FVarsIn fun _ => False

/-- Loose-bound-variable closedness of one source inductive type's
constructors.  The executable source precheck only rejects metavariables and
free variables; lowering then re-closes every constructor type over the
opened parameters, which silently repairs loose bound variables instead of
reporting them.  Source-facing statements therefore carry this as a genuine
hypothesis. -/
def InductiveConstructorsBVarClosed (type : InductiveType) : Prop :=
  ∀ ctor ∈ type.ctors, Closed ctor.type

/-- Loose-bound-variable closedness of a whole source block. Lowering re-closes constructor
types over the opened parameters, which would silently repair loose bound variables, so the
source-facing statements carry this as a hypothesis. -/
def SourceBVarClosed (types : List InductiveType) : Prop :=
  ∀ type ∈ types, type.type.Closed ∧ ∀ ctor ∈ type.ctors, ctor.type.Closed

theorem SourceBVarClosed.constructorsClosed
    (H : SourceBVarClosed types) (hmem : type ∈ types) :
    InductiveConstructorsBVarClosed type :=
  (H type hmem).2

theorem AuxiliaryFamilySpec.constructorsClosed
    (H : AuxiliaryFamilySpec env lctx params As levels nparams args sourceName
      auxName sourceInfo data)
    (Henv : EnvironmentTypesClosed env)
    (Hclosing : NestedClosingContext lctx As ngen)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (· ∈ Hclosing.selection.fvars)) :
    InductiveConstructorsClosed data.type := by
  exact H.constructors.closed Henv Hclosing Hlevels Hargs

/-- Every cached nested application is open only over the retained outer
parameter context selected by the lowering run. -/
def NestedAuxFVarsIn (P : FVarId → Prop)
    (state : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∀ nested name, (nested, name) ∈ state.nestedAux → nested.FVarsIn P

theorem AuxiliaryFamilySpec.nestedFVarsIn
    (H : AuxiliaryFamilySpec env lctx params As levels nparams args sourceName
      auxName sourceInfo data)
    (HAs : CDeclArray lctx As)
    (hnparams : nparams ≤ args.size)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (fun fv => fv ∈ HAs.fvars ∨ P fv))
    (Hparams : ∀ param ∈ params, param.FVarsIn P) :
    data.nested.FVarsIn P := by
  rw [H.nested]
  apply FVarsIn.instantiateRev
  · apply FVarsIn.abstract_fvarArray_of HAs.fvars As HAs.expressions
    apply FVarsIn.mkAppRange_zero hnparams
    · simpa [Lean4Lean.FVarsIn] using Hlevels
    · exact Hargs
  · exact Hparams

theorem buildAuxiliary_refines
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (levels : List Level) (nparams : Nat) (args : Array Expr)
    (sourceName auxName : Name) (sourceInfo : InductiveVal)
    (hlookup : env.find? sourceName = some (.inductInfo sourceInfo)) :
    As.size = params.size →
    (Lean4Lean.ElimNestedInductive.buildAuxiliary env lctx params As levels
      nparams args sourceName auxName).WF fun data =>
        AuxiliaryFamilySpec env lctx params As levels nparams args sourceName auxName
          sourceInfo data := by
  intro hsize
  unfold Lean4Lean.ElimNestedInductive.buildAuxiliary
  simp only [Lean.Kernel.Environment.get, hlookup]
  exact (instantiateForallParams_refines
    (sourceInfo.type.instantiateLevelParams sourceInfo.levelParams levels)
    nparams args).bind fun targetType Htype =>
      (replaceNestedParamsCore_refines params
        (mkAppRange (.const sourceName levels) 0 nparams args) As hsize).bind
        fun nested Hnested =>
          (buildAuxConstructors_refines env lctx As levels nparams args
            sourceName auxName sourceInfo.ctors).bind fun targets Htargets =>
              Except.WF.pure ⟨hlookup,
                ⟨Htype.choose, Htype.choose_spec.1,
                  congrArg (lctx.mkForall As) Htype.choose_spec.2⟩,
                hsize, Hnested, rfl, Htargets⟩

/-- A single fresh-family generation step pairs the cache entry and generated
family through the same fresh name, and otherwise changes only the fresh-name
counter and the two append-only arrays. -/
structure AuxiliaryGenerationStep
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (targetName : Name) (levels : List Level) (nparams : Nat)
    (args : Array Expr) (sourceName : Name) (sourceInfo : InductiveVal)
    (state : Lean4Lean.ElimNestedInductive.State)
    (out : Option Expr × Lean4Lean.ElimNestedInductive.State) : Prop where
  generated : ∃ auxName nextIdx data,
    FreshNestedName env `_nested state.nextIdx auxName nextIdx ∧
    AuxiliaryFamilySpec env lctx params As levels nparams args sourceName auxName
      sourceInfo data ∧
    out.1 = (if sourceName == targetName then
      some (mkAppRange (mkAppN (.const auxName state.lvls) As)
        nparams args.size args)
    else none) ∧
    out.2 = { state with
      nextIdx := nextIdx
      nestedAux := state.nestedAux.push (data.nested, auxName)
      newTypes := state.newTypes.push data.type }

theorem generateAuxiliary_refines
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (targetName : Name) (levels : List Level) (nparams : Nat)
    (args : Array Expr) (sourceName : Name) (sourceInfo : InductiveVal)
    (state : Lean4Lean.ElimNestedInductive.State)
    (hlookup : env.find? sourceName = some (.inductInfo sourceInfo))
    (hsize : As.size = params.size) :
    (Lean4Lean.ElimNestedInductive.generateAuxiliary lctx params As targetName
      levels nparams args sourceName env state).WF fun out =>
        AuxiliaryGenerationStep env lctx params As targetName levels nparams args
          sourceName sourceInfo state out := by
  unfold Lean4Lean.ElimNestedInductive.generateAuxiliary
  simp only [read, bind, ReaderT.bind]
  exact (mkUniqueName_refines env state `_nested).bind
    fun unique Hunique => by
      rcases unique with ⟨auxName, nextState⟩
      simp only at Hunique ⊢
      rcases Hunique with ⟨nextIdx, Hfresh, hstate⟩
      subst nextState
      simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
        StateT.lift, modify, get, bind, StateT.bind, pure]
      have Hbuild :
          ((Lean4Lean.ElimNestedInductive.buildAuxiliary env lctx params As
            levels nparams args sourceName auxName).bind fun data =>
              Except.pure (data, { state with nextIdx })).WF fun out =>
            AuxiliaryFamilySpec env lctx params As levels nparams args sourceName
              auxName sourceInfo out.1 ∧ out.2 = { state with nextIdx } :=
        (buildAuxiliary_refines env lctx params As levels nparams args
          sourceName auxName sourceInfo hlookup hsize).bind fun _ Hdata =>
            Except.WF.pure ⟨Hdata, rfl⟩
      exact Hbuild.bind fun built Hbuilt => by
        rcases built with ⟨data, buildState⟩
        rcases Hbuilt with ⟨Hdata, hbuildState⟩
        simp only at Hdata hbuildState ⊢
        subst buildState
        simp only [modifyGet, getThe]
        split <;> rename_i heq <;>
          exact Except.WF.pure ⟨⟨auxName, nextIdx, data, Hfresh, Hdata,
            by simp [heq], rfl⟩⟩

theorem AuxiliaryGenerationStep.auxFVarsIn
    (H : AuxiliaryGenerationStep env lctx params As targetName levels nparams args
      sourceName sourceInfo state out)
    (HAs : CDeclArray lctx As)
    (hnparams : nparams ≤ args.size)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (fun fv => fv ∈ HAs.fvars ∨ P fv))
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 := by
  rcases H.generated with
    ⟨auxName, nextIdx, data, _Hfresh, Hbuilt, _hresult, hstate⟩
  rw [hstate]
  intro nested name hentry
  simp only [Array.mem_push] at hentry
  rcases hentry with hold | hnew
  · exact Hstate nested name hold
  · cases hnew
    exact Hbuilt.nestedFVarsIn HAs hnparams Hlevels Hargs Hparams

/-- Constructor closedness for every queue entry at or beyond a cursor.  Slots
strictly behind the cursor have already been lowered and need not be processed
again; newly appended auxiliary families must satisfy this invariant. -/
def PendingNewTypesClosed (cursor : Nat)
    (state : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∀ j, cursor ≤ j → (hj : j < state.newTypes.size) →
    InductiveConstructorsClosed state.newTypes[j]

/-- Loose-bound-variable twin of `PendingNewTypesClosed`. -/
def PendingNewTypesBVarClosed (cursor : Nat)
    (state : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∀ j, cursor ≤ j → (hj : j < state.newTypes.size) →
    InductiveConstructorsBVarClosed state.newTypes[j]

theorem AuxiliaryGenerationStep.pendingNewTypesClosed
    (H : AuxiliaryGenerationStep env lctx params As targetName levels nparams args
      sourceName sourceInfo state out)
    (Henv : EnvironmentTypesClosed env)
    (Hclosing : NestedClosingContext lctx As ngen)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (· ∈ Hclosing.selection.fvars))
    (Hstate : PendingNewTypesClosed cursor state) :
    PendingNewTypesClosed cursor out.2 := by
  rcases H.generated with
    ⟨auxName, nextIdx, data, _Hfresh, Hbuilt, _hresult, hstate⟩
  rw [hstate]
  intro j hcursor hj
  simp only [Array.size_push] at hj
  by_cases hold : j < state.newTypes.size
  · simpa [Array.getElem_push, hold] using Hstate j hcursor hold
  · have heq : j = state.newTypes.size := by omega
    subst j
    simpa [Array.getElem_push] using
      Hbuilt.constructorsClosed Henv Hclosing Hlevels Hargs

/-- A successful cache lookup is backed by an actual previously recorded
auxiliary entry with the requested nested expression and returned name. -/
structure AuxiliaryCacheEntry
    (nestedAux : Array (Expr × Name)) (nested : Expr) (auxName : Name) : Prop where
  entry : ∃ item ∈ nestedAux, (item.1 == nested) = true ∧ item.2 = auxName

theorem findCachedAux?_refines
    (nestedAux : Array (Expr × Name)) (nested : Expr) (auxName : Name)
    (hfind : Lean4Lean.ElimNestedInductive.findCachedAux?
      nestedAux nested = some auxName) :
    AuxiliaryCacheEntry nestedAux nested auxName := by
  unfold Lean4Lean.ElimNestedInductive.findCachedAux? at hfind
  rcases Array.exists_of_findSome?_eq_some hfind with
    ⟨⟨found, foundName⟩, hmem, hentry⟩
  by_cases heq : (found == nested) = true
  · simp [heq] at hentry
    cases hentry
    exact ⟨⟨(found, auxName), hmem, heq, rfl⟩⟩
  · have heqFalse : (found == nested) = false := by
      cases h : found == nested <;> simp_all
    simp [heqFalse] at hentry

/-- Source constructors may not mention the private namespace used for
lowering-generated auxiliary families or projections. -/
def NoNestedAux (e : Expr) : Prop :=
  e.findAny (fun
    | .const c _ => (`_nested).isPrefixOf c
    | .proj s _ _ => (`_nested).isPrefixOf s
    | _ => false) = false

/-- Source-side disjointness required by restoration: no constant occurring
in the source expression is already an auxiliary family or an auxiliary
constructor in the final lowered environment. -/
def RestoreSourceDisjoint
    (result : Lean4Lean.ElimNestedInductive.Result) (env : Environment) :
    Expr → Prop
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => True
  | .const name _ =>
      result.aux2nested.find? name = none ∧
      result.getNestedIfAuxCtor env name = none
  | .app fn arg =>
      RestoreSourceDisjoint result env fn ∧
      RestoreSourceDisjoint result env arg
  | .lam _ dom body _ | .forallE _ dom body _ =>
      RestoreSourceDisjoint result env dom ∧
      RestoreSourceDisjoint result env body
  | .letE _ type value body _ =>
      RestoreSourceDisjoint result env type ∧
      RestoreSourceDisjoint result env value ∧
      RestoreSourceDisjoint result env body
  | .mdata _ body | .proj _ _ body =>
      RestoreSourceDisjoint result env body

/-- Every concrete constant occurring syntactically in an expression resolves
in the abstract environment used to translate it. Projections deliberately
follow the translated body only, matching `RestoreSourceDisjoint`. -/
def _root_.Lean.Expr.ConstantsDefined (env : VEnv) : Expr → Prop
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => True
  | .const name _ => env.constants name ≠ none
  | .app fn arg => fn.ConstantsDefined env ∧ arg.ConstantsDefined env
  | .lam _ dom body _ | .forallE _ dom body _ =>
      dom.ConstantsDefined env ∧ body.ConstantsDefined env
  | .letE _ type value body _ =>
      type.ConstantsDefined env ∧ value.ConstantsDefined env ∧
        body.ConstantsDefined env
  | .mdata _ body | .proj _ _ body => body.ConstantsDefined env

theorem _root_.Lean4Lean.TrExprS.constantsDefined
    (H : TrExprS env Us Δ source target) : source.ConstantsDefined env := by
  induction H <;> simp_all [Expr.ConstantsDefined]

/-- Any name recognized as an auxiliary constructor was absent from the
abstract environment in which the independent source expression was
translated. -/
def RestoreAuxConstructorsFresh
    (result : Lean4Lean.ElimNestedInductive.Result)
    (prodEnv : Environment) (sourceVEnv : VEnv) : Prop :=
  ∀ name nested auxFamily,
    result.getNestedIfAuxCtor prodEnv name = some (nested, auxFamily) →
    sourceVEnv.constants name = none

/-- Every auxiliary family recorded by lowering was fresh in the kernel
environment from which the inductive block was built. -/
def RestoreAuxFamiliesFresh
    (result : Lean4Lean.ElimNestedInductive.Result)
    (sourceEnv : Environment) : Prop :=
  ∀ name nested, result.aux2nested.find? name = some nested →
    sourceEnv.find? name = none

theorem NoNestedAux.findAny_false (H : NoNestedAux e) :
    e.findAny (fun
      | .const c _ => (`_nested).isPrefixOf c
      | .proj s _ _ => (`_nested).isPrefixOf s
      | _ => false) = false := by
  exact H

/-- Derive restoration disjointness without assuming auxiliary
constructor names live below `_nested`. Family collisions are rejected by
the source syntax namespace check; constructor collisions contradict source
translation and freshness of the lowered block. -/
theorem NoNestedAux.restoreSourceDisjointOfFresh
    (H : NoNestedAux e)
    (Hdefined : e.ConstantsDefined sourceVEnv)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result prodEnv sourceVEnv) :
    RestoreSourceDisjoint result prodEnv e := by
  let p : Expr → Bool := fun
    | .const c _ => (`_nested).isPrefixOf c
    | .proj s _ _ => (`_nested).isPrefixOf s
    | _ => false
  have orFalse : ∀ a b : Bool, (a || b) = false →
      a = false ∧ b = false := by
    intro a b h
    cases a <;> cases b <;> simp_all
  have go : ∀ source, source.findAny p = false →
      source.ConstantsDefined sourceVEnv →
      RestoreSourceDisjoint result prodEnv source := by
    intro source
    induction source with
    | bvar | fvar | mvar | sort | lit =>
      intro _Hfind _HsourceDefined
      trivial
    | const name levels =>
      intro Hfind HsourceDefined
      have hprefix : (`_nested).isPrefixOf name = false := by
        simpa [Expr.findAny, p] using Hfind
      constructor
      · cases hfamily : result.aux2nested.find? name with
        | none => rfl
        | some nested =>
          have hreserved := Hfamilies name nested hfamily
          simp_all
      · cases hctor : result.getNestedIfAuxCtor prodEnv name with
        | none => rfl
        | some pair =>
          rcases pair with ⟨nested, auxFamily⟩
          have hfresh := Hconstructors name nested auxFamily hctor
          exact False.elim (HsourceDefined hfresh)
    | app fn arg ihFn ihArg =>
      intro Hfind HsourceDefined
      simp only [Expr.findAny, p, Bool.false_or] at Hfind
      rcases orFalse _ _ Hfind with ⟨hfn, harg⟩
      exact ⟨ihFn hfn HsourceDefined.1, ihArg harg HsourceDefined.2⟩
    | lam name dom body bi ihDom ihBody
        | forallE name dom body bi ihDom ihBody =>
      intro Hfind HsourceDefined
      simp only [Expr.findAny, p, Bool.false_or] at Hfind
      rcases orFalse _ _ Hfind with ⟨hdom, hbody⟩
      exact ⟨ihDom hdom HsourceDefined.1,
        ihBody hbody HsourceDefined.2⟩
    | letE name type value body nondep ihType ihValue ihBody =>
      intro Hfind HsourceDefined
      simp only [Expr.findAny, p, Bool.false_or] at Hfind
      rcases orFalse _ _ Hfind with ⟨htypeValue, hbody⟩
      rcases orFalse _ _ htypeValue with ⟨htype, hvalue⟩
      exact ⟨ihType htype HsourceDefined.1,
        ihValue hvalue HsourceDefined.2.1,
        ihBody hbody HsourceDefined.2.2⟩
    | mdata data body ihBody =>
      intro Hfind HsourceDefined
      simpa only [RestoreSourceDisjoint] using
        ihBody Hfind HsourceDefined
    | proj structName idx body ihBody =>
      intro Hfind HsourceDefined
      simp only [Expr.findAny, p] at Hfind
      exact ihBody (orFalse _ _ Hfind).2 HsourceDefined
  apply go e
  · simpa only [p] using H.findAny_false
  · exact Hdefined

theorem RestoreSourceDisjoint.getAppFn
    (H : RestoreSourceDisjoint result env e)
    (hhead : e.getAppFn = .const name levels) :
    result.aux2nested.find? name = none ∧
      result.getNestedIfAuxCtor env name = none := by
  induction e with
  | const sourceName sourceLevels =>
    change (Expr.const sourceName sourceLevels) = .const name levels at hhead
    cases hhead
    exact H
  | app fn arg ihFn ihArg =>
    exact ihFn H.1 (by simpa [Expr.getAppFn] using hhead)
  | bvar | fvar | mvar | sort | lam | forallE | letE | lit | mdata | proj =>
    simp [Expr.getAppFn] at hhead

theorem RestoreSourceDisjoint.instantiate1'_fvar
    (H : RestoreSourceDisjoint result env e) (fv : FVarId) (k : Nat) :
    RestoreSourceDisjoint result env (e.instantiate1' (.fvar fv) k) := by
  induction e generalizing k with
  | bvar i =>
    by_cases hlt : i < k
    · simp [Expr.instantiate1', hlt, RestoreSourceDisjoint]
    · by_cases heq : i = k
      · simp only [Expr.instantiate1', heq, ↓reduceIte]
        simp only [Nat.lt_irrefl, ↓reduceIte]
        change RestoreSourceDisjoint result env (.fvar fv)
        trivial
      · simp [Expr.instantiate1', hlt, heq, RestoreSourceDisjoint]
  | fvar | mvar | sort | lit =>
    simp [Expr.instantiate1', RestoreSourceDisjoint]
  | const => exact H
  | app fn arg ihFn ihArg =>
    simp only [Expr.instantiate1', RestoreSourceDisjoint] at H ⊢
    exact ⟨ihFn H.1 k, ihArg H.2 k⟩
  | lam name dom body bi ihDom ihBody =>
    simp only [Expr.instantiate1', RestoreSourceDisjoint] at H ⊢
    exact ⟨ihDom H.1 k, ihBody H.2 (k + 1)⟩
  | forallE name dom body bi ihDom ihBody =>
    simp only [Expr.instantiate1', RestoreSourceDisjoint] at H ⊢
    exact ⟨ihDom H.1 k, ihBody H.2 (k + 1)⟩
  | letE name type value body nondep ihType ihValue ihBody =>
    simp only [Expr.instantiate1', RestoreSourceDisjoint] at H ⊢
    exact ⟨ihType H.1 k, ihValue H.2.1 k, ihBody H.2.2 (k + 1)⟩
  | mdata data body ihBody =>
    simpa only [Expr.instantiate1', RestoreSourceDisjoint] using ihBody H k
  | proj name idx body ihBody =>
    simpa only [Expr.instantiate1', RestoreSourceDisjoint] using ihBody H k

theorem RestoreSourceDisjoint.instantiate1_fvar
    (H : RestoreSourceDisjoint result env e) (fv : FVarId) :
    RestoreSourceDisjoint result env (e.instantiate1 (.fvar fv)) := by
  rw [Expr.instantiate1_eq]
  exact H.instantiate1'_fvar fv 0

theorem LoweringParamOpening.tailRestoreSourceDisjoint
    (Hopen : LoweringParamOpening lctx params source n outLctx tail outParams)
    (Hsource : RestoreSourceDisjoint result env source) :
    RestoreSourceDisjoint result env tail := by
  induction Hopen with
  | done => exact Hsource
  | step Hnext ih =>
    apply ih
    exact Hsource.2.instantiate1_fvar _

theorem checkNoNestedAux_refines (name : Name) (e : Expr) :
    (Lean4Lean.checkNoNestedAux name e).WF fun _ => NoNestedAux e := by
  unfold Lean4Lean.checkNoNestedAux NoNestedAux
  cases hfind : e.findAny fun
    | .const c _ => (`_nested).isPrefixOf c
    | .proj s _ _ => (`_nested).isPrefixOf s
    | _ => false
  · exact Except.WF.pure rfl
  · exact Except.WF.throw

/-- Source constructor syntax retained before nested lowering rewrites its type. -/
structure SourceConstructorSyntax (ctor : Constructor) : Prop where
  closed : ctor.type.FVarsIn fun _ => False
  noNestedAux : NoNestedAux ctor.type

/-- Pointwise source-syntax certificates for a constructor list. -/
inductive SourceConstructorSyntaxes : List Constructor → Prop where
  | nil : SourceConstructorSyntaxes []
  | cons : SourceConstructorSyntax ctor → SourceConstructorSyntaxes ctors →
      SourceConstructorSyntaxes (ctor :: ctors)

/-- Source inductive syntax retained before nested lowering rewrites the declaration. -/
structure SourceInductiveSyntax (type : InductiveType) : Prop where
  closed : type.type.FVarsIn fun _ => False
  constructors : SourceConstructorSyntaxes type.ctors

/-- The source-level closure and reserved-prefix checks for a mutual block. -/
inductive SourceSyntaxChecked : List InductiveType → Prop where
  | nil : SourceSyntaxChecked []
  | cons : SourceInductiveSyntax type → SourceSyntaxChecked types →
      SourceSyntaxChecked (type :: types)

theorem SourceConstructorSyntaxes.getElem
    (H : SourceConstructorSyntaxes ctors) (i : Nat)
    (hi : i < ctors.length) : SourceConstructorSyntax ctors[i] := by
  induction H generalizing i with
  | nil => simp at hi
  | cons Hhead Htail ih =>
    cases i with
    | zero => exact Hhead
    | succ i =>
      apply ih i

theorem SourceConstructorSyntaxes.of_mem
    (H : SourceConstructorSyntaxes ctors) (hctor : ctor ∈ ctors) :
    SourceConstructorSyntax ctor := by
  induction H with
  | nil => simp at hctor
  | cons Hhead Htail ih =>
    rcases List.mem_cons.mp hctor with rfl | htail
    · exact Hhead
    · exact ih htail

theorem SourceSyntaxChecked.getElem
    (H : SourceSyntaxChecked types) (i : Nat)
    (hi : i < types.length) : SourceInductiveSyntax types[i] := by
  induction H generalizing i with
  | nil => simp at hi
  | cons Hhead Htail ih =>
    cases i with
    | zero => exact Hhead
    | succ i =>
      apply ih i

theorem SourceConstructorSyntaxes.closed
    (H : SourceConstructorSyntaxes ctors) :
    ∀ ctor ∈ ctors, ctor.type.FVarsIn fun _ => False := by
  induction H with
  | nil => simp
  | cons Hhead Htail ih =>
    intro ctor hctor
    simp only [List.mem_cons] at hctor
    rcases hctor with rfl | htail
    · exact Hhead.closed
    · exact ih ctor htail

theorem SourceSyntaxChecked.typeClosed
    (H : SourceSyntaxChecked types) (hmem : type ∈ types) :
    type.type.FVarsIn fun _ => False := by
  induction H with
  | nil => simp at hmem
  | cons Hhead Htail ih =>
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | htail
    · exact Hhead.closed
    · exact ih htail

theorem SourceSyntaxChecked.constructorsClosed
    (H : SourceSyntaxChecked types) (hmem : type ∈ types) :
    InductiveConstructorsClosed type := by
  induction H with
  | nil => simp at hmem
  | cons Hhead Htail ih =>
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | htail
    · exact Hhead.constructors.closed
    · exact ih htail





private theorem checkConstructorSources_refines
    (env : Environment) (ctors : List Constructor) :
    (Lean4Lean.checkConstructorSources env ctors).WF fun _ =>
      SourceConstructorSyntaxes ctors := by
  induction ctors with
  | nil => exact Except.WF.pure .nil
  | cons ctor ctors ih =>
    rw [Lean4Lean.checkConstructorSources]
    have Hclosed : (env.checkNoMVarNoFVar ctor.name ctor.type).WF
        fun _ => ctor.type.FVarsIn fun _ => False := by
      intro _ h
      exact checkNoMVarNoFVar.closed (env := env) (name := ctor.name) h
    exact Hclosed.bind fun _ hclosed =>
      (checkNoNestedAux_refines ctor.name ctor.type).bind fun _ hreserved =>
        ih.mono fun _ htail =>
          .cons ⟨hclosed, hreserved⟩ htail

theorem checkInductiveSources_refines
    (env : Environment) (types : List InductiveType) :
    (Lean4Lean.checkInductiveSources env types).WF fun _ =>
      SourceSyntaxChecked types := by
  induction types with
  | nil => exact Except.WF.pure .nil
  | cons type types ih =>
    rw [Lean4Lean.checkInductiveSources]
    have Hclosed : (env.checkNoMVarNoFVar type.name type.type).WF
        fun _ => type.type.FVarsIn fun _ => False := by
      intro _ h
      exact checkNoMVarNoFVar.closed (env := env) (name := type.name) h
    exact Hclosed.bind fun _ hclosed =>
      (checkConstructorSources_refines env type.ctors).bind fun _ hctors =>
        ih.mono fun _ htail =>
          .cons ⟨hclosed, hctors⟩ htail

/-- Independent lookup contract used when restoring a generated auxiliary
constructor to its source constructor family. -/
structure AuxiliaryConstructorLookup
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (ctor : Name) (nested : Expr) (auxFamily : Name) : Prop where
  exists_info : ∃ info : ConstructorVal,
    env.find? ctor = some (.ctorInfo info) ∧
    auxFamily = info.induct ∧
    result.aux2nested.find? info.induct = some nested

theorem getNestedIfAuxCtor_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (ctor : Name) :
    ∀ nested auxFamily,
      result.getNestedIfAuxCtor env ctor = some (nested, auxFamily) →
      AuxiliaryConstructorLookup result env ctor nested auxFamily := by
  intro nested auxFamily hout
  unfold Lean4Lean.ElimNestedInductive.Result.getNestedIfAuxCtor at hout
  cases hfound : env.find? ctor with
  | none => simp [hfound] at hout
  | some info =>
    cases info with
    | ctorInfo ctorInfo =>
      simp only [hfound] at hout
      cases hnested : result.aux2nested.find? ctorInfo.induct with
      | none => simp [hnested] at hout
      | some restored =>
        have hp : (restored, ctorInfo.induct) = (nested, auxFamily) := by
          simpa [hnested] using hout
        cases hp
        exact ⟨⟨ctorInfo, hfound, rfl, hnested⟩⟩
    | _ => simp_all

theorem restoreCtorName_eq
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (ctor auxFamily sourceFamily : Name)
    (nested : Expr) (levels : List Level)
    (hlookup : result.getNestedIfAuxCtor env ctor =
      some (nested, auxFamily))
    (hhead : nested.getAppFn = .const sourceFamily levels) :
    result.restoreCtorName env ctor =
      ctor.replacePrefix auxFamily sourceFamily := by
  unfold Lean4Lean.ElimNestedInductive.Result.restoreCtorName
  simp [hlookup, hhead]
  rfl

theorem restoreNestedNode_recursor
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (As : Array Expr) (auxRec : NameMap Name)
    (name restored : Name) (levels : List Level)
    (hrec : auxRec.find? name = some restored) :
    result.restoreNestedNode env As auxRec (.const name levels) =
      some (.const restored levels) := by
  simp [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode, hrec]

theorem restoreNestedNode_family
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (As : Array Expr) (auxRec : NameMap Name)
    (t nested : Expr) (family : Name) (levels : List Level)
    (happ : t.isApp = true)
    (hhead : t.getAppFn = .const family levels)
    (hfamily : result.aux2nested.find? family = some nested)
    (harity : result.nparams ≤ t.getAppArgs.size) :
    result.restoreNestedNode env As auxRec t = some
      (mkAppRange ((nested.abstract result.params).instantiateRev As)
        result.nparams t.getAppArgs.size t.getAppArgs) := by
  cases t with
  | app fn arg =>
    simp only [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode]
    simp [hhead, hfamily, harity]
  | bvar | fvar | mvar | sort | const | lam | forallE | letE | lit | mdata
      | proj => cases happ

/-- Family restoration including the zero-argument case, where the lowered
family is represented by a bare constant. In that case the executable
consults the auxiliary-recursor map first, so disjointness is an explicit
premise. -/
theorem restoreNestedNode_family_general
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (As : Array Expr) (auxRec : NameMap Name)
    (t nested : Expr) (family : Name) (levels : List Level)
    (hhead : t.getAppFn = .const family levels)
    (hrec : auxRec.find? family = none)
    (hfamily : result.aux2nested.find? family = some nested)
    (harity : result.nparams ≤ t.getAppArgs.size) :
    result.restoreNestedNode env As auxRec t = some
      (mkAppRange ((nested.abstract result.params).instantiateRev As)
        result.nparams t.getAppArgs.size t.getAppArgs) := by
  cases t with
  | const name constLevels =>
    change (.const name constLevels : Expr) = .const family levels at hhead
    cases hhead
    have hargs : (.const family levels : Expr).getAppArgs = #[] := rfl
    rw [hargs] at harity ⊢
    have hnparams : result.nparams = 0 := by simpa using harity
    unfold Lean4Lean.ElimNestedInductive.Result.restoreNestedNode
    simp only [hrec]
    have hfn : (.const family levels : Expr).getAppFn =
        .const family levels := rfl
    rw [hfn]
    simp only
    rw [hfamily, hargs, hnparams]
    rfl
  | app fn arg =>
    exact restoreNestedNode_family result env As auxRec (.app fn arg) nested
      family levels rfl hhead hfamily harity
  | bvar i => cases hhead
  | fvar i => cases hhead
  | mvar i => cases hhead
  | sort level => cases hhead
  | lam name dom body bi => cases hhead
  | forallE name dom body bi => cases hhead
  | letE name type value body nondep => cases hhead
  | lit literal => cases hhead
  | mdata data body => cases hhead
  | proj name idx body => cases hhead

end VerifyInductive
end Lean4Lean
