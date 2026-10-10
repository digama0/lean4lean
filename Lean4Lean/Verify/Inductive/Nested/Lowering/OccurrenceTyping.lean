import Lean4Lean.Verify.Inductive.Nested.Lowering.Output

/-! # The typing of the cached nested occurrences

What the validation pass `validateNestedAuxiliaries` establishes about the cache
(`NestedOccurrencesTyped`, in the lowering's parameter metacontext), closed over the lowering
parameters (`ClosedNestedOccurrencesTyped`, `NestedLowering.closeNestedOccurrencesTyped`) and
in de Bruijn form (`ClosedNestedOccurrenceTyping`), as the lowering expansion and the
restoration read it. From the source branch's `Nested/Lowering/{Basic,Queue}.lean` and
`Nested/Restoration/SourceTranslations.lean`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- Postcondition of the executable nested-auxiliary validation pass:
every nested application stored in `aux2nested` has a translated typing derivation in the
restored parameter context.  Such an application is a nested occurrence `I Ds` applied
to its parameters only, so for an indexed family `I` it is a type family, not
a type; like the C++ kernel, validation only type-checks it. -/
def NestedOccurrencesTyped (venv : VEnv) (lparams : List Name)
    (vlctx : VLCtx) (res : Lean4Lean.ElimNestedInductive.Result) : Prop :=
  ∀ name e, res.aux2nested.find? name = some e →
    ∃ ty e' ty', TrTyping venv lparams vlctx e ty e' ty'

/-- Context-independent form of nested-auxiliary validation.  Each open
nested application `e : T` is closed with lambdas over the exact parameter telescope
retained by lowering, and its inferred type `T` with foralls over the same
telescope, so that the closed application `fun params => e` has type
`∀ params, T`; both closures share one list of translated parameter domains.
Later restoration may choose fresh binder names without changing the
statement that must be translated.  Closing the application with lambdas, rather
than with foralls, is what admits nested occurrences of indexed families:
there `T` is `∀ indices, Sort u`, not a sort, and `∀ params, e` would be
ill-typed. -/
def ClosedNestedOccurrencesTyped (venv : VEnv) (lparams : List Name)
    (res : Lean4Lean.ElimNestedInductive.Result) : Prop :=
  ∀ name e, res.aux2nested.find? name = some e →
    Closed e ∧ ∃ type domains body bodyType, Closed type ∧
      domains.length = res.params.size ∧
      TrExprS venv lparams [] (res.lctx.mkLambda res.params e)
        (VExpr.wrapLams domains body) ∧
      TrExprS venv lparams [] (res.lctx.mkForall res.params type)
        (VExpr.wrapForalls domains bodyType) ∧
      venv.HasType lparams.length [] (VExpr.wrapLams domains body)
        (VExpr.wrapForalls domains bodyType)

/-- De-Bruijn form of one closed nested application.  It records the closed
translation of the application's parameter-closed type, whose forall telescope
fixes the translated parameter domains, and the residual translation and
typing of the application itself in those domains, so no kernel free-variable
identifier occurs in the semantic context.  The residual is typed, not
required to be a type: for a nested indexed family it is a type family. -/
structure ClosedNestedOccurrenceTyping
    (venv : VEnv) (lparams : List Name)
    (res : Lean4Lean.ElimNestedInductive.Result)
    (selection : CDeclArray res.lctx res.params)
    (e : Expr) where
  /-- The type inferred for the open application by validation. -/
  type : Expr
  typeClosed : Closed type
  domains : List VExpr
  residualTarget : VExpr
  residualType : VExpr
  arity : domains.length = res.params.size
  closed : TrExprS venv lparams []
    (res.lctx.mkForall res.params type)
    (VExpr.wrapForalls domains residualType)
  residual : TrExprS venv lparams (abstractForallContext domains [])
    (e.abstractList selection.fvars) residualTarget
  residualTyping : venv.HasType lparams.length
    (abstractForallContext domains []).toCtx residualTarget residualType

/-- Over a telescope of local assumptions, `mkLambda'` and `mkForall'` wrap
one common list of translated domains, one per opened variable. -/
theorem nestedMLCtxSharedBinderDomains {c : TypeChecker.MLCtx}
    (wf : c.WF env Us) (n : Nat) (hn : n ≤ c.length)
    (hcdecl : ∀ fv ∈ c.fvarRevList n hn, ∃ index name type bi kind,
      c.lctx.find? fv = some (.cdecl index fv name type bi kind)) :
    ∃ domains : List VExpr, domains.length = n ∧
      (∀ e, c.mkLambda' n hn e = VExpr.wrapLams domains e) ∧
      (∀ e, c.mkForall' n hn e = VExpr.wrapForalls domains e) := by
  induction n generalizing c with
  | zero => exact ⟨[], rfl, fun _ => rfl, fun _ => rfl⟩
  | succ n ih =>
    match c, wf, hn, hcdecl with
    | .nil, _, hn, _ => simp at hn
    | .vlam id name ty ty' bi c, wf, hn, hcdecl =>
      have hrest : ∀ fv ∈ c.fvarRevList n (Nat.le_of_succ_le_succ hn),
          ∃ index name type bi kind,
            c.lctx.find? fv = some (.cdecl index fv name type bi kind) := by
        intro fv hfv
        have hne : fv ≠ id := by
          rintro rfl
          exact wf.1.tr.find?_eq_none.1 wf.2.1
            (c.fvarRevList_prefix.subset hfv)
        rcases hcdecl fv (by simp [hfv]) with
          ⟨index, name', type, bi', kind, hfind⟩
        refine ⟨index, name', type, bi', kind, ?_⟩
        rw [wf.find?_eq] at hfind
        rw [wf.1.find?_eq]
        have hbeq : (fv == id) = false := by simpa using hne
        simpa [TypeChecker.MLCtx.decls, LocalDecl.fvarId, hbeq] using hfind
      rcases ih wf.1 (Nat.le_of_succ_le_succ hn) hrest with
        ⟨domains, hlength, hlam, hforall⟩
      exact ⟨domains ++ [ty'], by simp [hlength],
        fun e => by simp [hlam, VExpr.wrapLams],
        fun e => by simp [hforall, VExpr.wrapForalls]⟩
    | .vlet id name ty v ty' v' c, wf, hn, hcdecl =>
      exfalso
      rcases hcdecl id (by simp) with ⟨index, name', type, bi', kind, hfind⟩
      rw [wf.find?_eq] at hfind
      simp [TypeChecker.MLCtx.decls, LocalDecl.fvarId] at hfind

/-- The open nested application contains no pre-existing loose bound
variables.  This is derived from the residual translation's scoping theorem,
not imposed as an additional executable validation condition. -/
theorem ClosedNestedOccurrenceTyping.sourceClosed
    (H : ClosedNestedOccurrenceTyping venv lparams res selection e) :
    Closed e 0 := by
  have HresidualClosed := H.residual.closed
  have hmap : ∀ domains : List VExpr,
      VLCtx.bvars (domains.map fun type =>
        ((none, VLocalDecl.vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) = domains.length := by
    intro domains
    induction domains with
    | nil => rfl
    | cons domain domains ih => simp [VLCtx.bvars, ih]
  have hbvars : (abstractForallContext H.domains []).bvars =
      H.domains.length := by
    simp only [abstractForallContext,
      VLCtx.bvars_append, VLCtx.bvars, Nat.add_zero]
    rw [hmap]
    simp
  apply Expr.closed_of_abstractList
  rw [hbvars] at HresidualClosed
  simpa [H.arity, selection.size] using HresidualClosed

def ClosedNestedOccurrenceTypings
    (venv : VEnv) (lparams : List Name)
    (res : Lean4Lean.ElimNestedInductive.Result)
    (selection : CDeclArray res.lctx res.params) : Prop :=
  ∀ name e, res.aux2nested.find? name = some e →
    Nonempty (ClosedNestedOccurrenceTyping venv lparams res selection e)

/-- Telescope inversion turns every context-independent validated nested application
into the bound-variable representation used beneath restored
recursor parameter binders. -/
theorem ClosedNestedOccurrencesTyped.residualTranslations
    (H : ClosedNestedOccurrencesTyped venv lparams res)
    (henv : venv.WF)
    (selection : CDeclArray res.lctx res.params)
    (hnodup : selection.fvars.Nodup) :
    ClosedNestedOccurrenceTypings venv lparams res selection := by
  intro name e hfind
  rcases H name e hfind with
    ⟨hclosedE, type, domains, body, bodyType, htypeClosed, harity, Hlambda,
      Hforall, Htyping⟩
  have Htel : Expr.LambdaTelescope (res.lctx.mkLambda res.params e)
      domains.length (e.abstractList selection.fvars) := by
    have Htel := LocalContext.mkLambda_fvars_lambdaTelescopeList
      (lctx := res.lctx) selection.declarations hnodup hclosedE
    have hlambda : res.lctx.mkLambda res.params e =
        res.lctx.mkLambda (selection.fvars.map Expr.fvar).toArray e :=
      congrArg (res.lctx.mkLambda · e) selection.expressions
    rw [hlambda, harity, selection.size]
    exact Htel
  have Hresidual := TrExprS.lambdaTelescope_exact_residual Htel rfl Hlambda
  have Hbody := (VEnv.HasType.wrapLams_inv henv (by trivial) Htyping).2
  exact ⟨⟨type, htypeClosed, domains, body, bodyType, harity, Hforall,
    Hresidual, by simpa [abstractForallContext_toCtx, VLCtx.toCtx] using Hbody⟩⟩



/-- The executable auxiliary checks can be closed over lowering's retained
parameter telescope: each nested application with lambdas, its inferred type with
foralls.  This removes the concrete free-variable names from the typing
facts before restoration reopens the same telescope with its own fresh
names.  Every variable of the telescope is a local assumption of lowering's
context, so both closures wrap the same translated parameter domains. -/
theorem NestedLowering.closeNestedOccurrencesTyped
    (H : NestedLowering sourceEnv fuel nparams types initialState
      (res, finalState))
    (henv : venv.WF)
    (mlctx : TypeChecker.MLCtx) (hmlctx : mlctx.WF venv lparams)
    (hlctx : mlctx.lctx = res.lctx)
    (Hvalidated : NestedOccurrencesTyped venv lparams mlctx.vlctx res) :
    ClosedNestedOccurrencesTyped venv lparams res := by
  have hfull : mlctx.fvarRevList mlctx.length (Nat.le_refl _) =
      mlctx.vlctx.fvars := mlctx.fvarRevList_all
  have hparams : res.params.toList.reverse =
      (mlctx.fvarRevList mlctx.length (Nat.le_refl _)).map Expr.fvar := by
    rw [hfull, ← hmlctx.tr.fvars_eq, hlctx]
    exact H.resultParams_reverse_fvars
  rcases H.resultContextSelection with ⟨selection⟩
  have hcdecl : ∀ fv ∈ mlctx.fvarRevList mlctx.length (Nat.le_refl _),
      ∃ index name type bi kind,
        mlctx.lctx.find? fv = some (.cdecl index fv name type bi kind) := by
    intro fv hfv
    have hmem : Expr.fvar fv ∈ res.params.toList := by
      rw [← List.mem_reverse, hparams]
      exact List.mem_map_of_mem hfv
    have hsel : fv ∈ selection.fvars := by
      rw [selection.expressions] at hmem
      simpa using hmem
    rw [hlctx]
    exact selection.declarations fv hsel
  rcases nestedMLCtxSharedBinderDomains hmlctx mlctx.length (Nat.le_refl _)
      hcdecl with ⟨domains, hlength, hlam, hforall⟩
  have hsize : res.params.size = mlctx.length := by
    have := congrArg List.length hparams
    simpa using this
  intro name e hfind
  rcases Hvalidated name e hfind with
    ⟨ty, e', ty', ⟨_hfvars, Hexpr, Htype, Htyping⟩⟩
  have hclosedE : Closed e := by
    simpa [TypeChecker.MLCtx.noBV] using Hexpr.closed
  have hclosedTy : Closed ty := by
    simpa [TypeChecker.MLCtx.noBV] using Htype.closed
  have HtyType : venv.IsType lparams.length mlctx.vlctx.toCtx ty' :=
    Htyping.isType henv.ordered hmlctx.tr.wf.toCtx
  have Hlambda := hmlctx.mkLambda_trS henv Hexpr Htyping
    mlctx.length (Nat.le_refl _)
  have Hforall := hmlctx.mkForall_trS henv Htype HtyType
    mlctx.length (Nat.le_refl _)
  rw [mlctx.dropN_all] at Hlambda Hforall
  have hlambdaEq : res.lctx.mkLambda res.params e =
      mlctx.mkLambda mlctx.length (Nat.le_refl _) e := by
    rw [← hlctx]
    exact hmlctx.mkLambda_eq mlctx.length (Nat.le_refl _) hparams hclosedE
  have hforallEq : res.lctx.mkForall res.params ty =
      mlctx.mkForall mlctx.length (Nat.le_refl _) ty := by
    rw [← hlctx]
    exact hmlctx.mkForall_eq mlctx.length (Nat.le_refl _) hparams hclosedTy
  refine ⟨hclosedE, ty, domains, e', ty', hclosedTy,
    hlength.trans hsize.symm, ?_, ?_, ?_⟩
  · rw [hlambdaEq, ← hlam]
    exact Hlambda.1
  · rw [hforallEq, ← hforall]
    exact Hforall.1
  · rw [← hlam, ← hforall]
    exact Hlambda.2

/-- Name-independent typing of the validated nested applications:
the free variables selected by lowering are abstracted into the
de-Bruijn parameter context before restoration is inspected. -/
theorem NestedLowering.validatedAuxiliaryResidualTranslations
    (H : NestedLowering sourceEnv fuel nparams types initialState
      (res, finalState))
    (henv : venv.WF)
    (mlctx : TypeChecker.MLCtx) (hmlctx : mlctx.WF venv lparams)
    (hlctx : mlctx.lctx = res.lctx)
    (Hvalidated : NestedOccurrencesTyped venv lparams mlctx.vlctx res) :
    ∃ selection : CDeclArray res.lctx res.params,
      ClosedNestedOccurrenceTypings venv lparams res selection := by
  rcases H.resultContextSelection with ⟨selection⟩
  have hparams : res.params.toList.reverse =
      (mlctx.fvarRevList mlctx.length (Nat.le_refl _)).map Expr.fvar := by
    rw [mlctx.fvarRevList_all, ← hmlctx.tr.fvars_eq, hlctx]
    exact H.resultParams_reverse_fvars
  have hnodup : selection.fvars.Nodup := by
    have h1 : res.params.toList = selection.fvars.map Expr.fvar := by
      simpa using congrArg Array.toList selection.expressions
    have h2 : selection.fvars.reverse = mlctx.fvarRevList mlctx.length (Nat.le_refl _) := by
      apply (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp
      rw [List.map_reverse, ← h1]
      exact hparams
    have := hmlctx.fvarRevList_nodup mlctx.length (Nat.le_refl _)
    rw [← h2] at this
    simpa using this
  exact ⟨selection,
    (H.closeNestedOccurrencesTyped henv mlctx hmlctx hlctx Hvalidated
      ).residualTranslations henv selection hnodup⟩

/-- An `AuxiliaryFamilySpecialization` selects exactly the validated auxiliary
translation associated with its cache entry. -/
theorem AuxiliaryFamilySpecialization.closedAuxiliaryTranslation
    (H : AuxiliaryFamilySpecialization sourceEnv params finalState.nestedAux family)
    (Hmap : NestedAuxMapModels result finalState)
    {selection : CDeclArray result.lctx result.params}
    (Htranslations : ClosedNestedOccurrenceTypings venv lparams result
      selection) :
    Nonempty (ClosedNestedOccurrenceTyping venv lparams result selection
      H.data.nested) :=
  Htranslations H.auxName H.data.nested (Hmap _ _ H.cached)

/-- Rebase a validated auxiliary residual along a definitional conversion from
the caller's parameter telescope to the domains recovered by validation.
This is the syntax-independent part needed by nested restoration: once the
two dependent parameter contexts have been related, neither a dummy residual
nor the concrete free variables used by either opening remain relevant. -/
theorem ClosedNestedOccurrenceTyping.residualAtDefEqParameterDomains
    (H : ClosedNestedOccurrenceTyping venv lparams res selection e)
    (henv : venv.WF) (parameterDomains : List VExpr)
    (Hcontexts : VEnv.IsDefEqCtx venv lparams.length []
      parameterDomains.reverse H.domains.reverse) :
    ∃ target targetType,
      TrExprS venv lparams (abstractForallContext parameterDomains [])
        (e.abstractList selection.fvars) target ∧
      venv.HasType lparams.length
        (abstractForallContext parameterDomains []).toCtx target
        targetType := by
  have Hvlctx := abstractForallContext.isDefEq Hcontexts
  rcases H.residual.defeqDFC henv (Hvlctx.symm henv.orderedStrong) with
    ⟨target, Hresidual⟩
  refine ⟨target, H.residualType, Hresidual, ?_⟩
  have HctxSymm := Hvlctx.symm henv.orderedStrong
  have Htyping := H.residualTyping.defeqDFC henv.ordered
    HctxSymm.defeqCtx
  have HtargetEq := H.residual.uniq henv HctxSymm Hresidual
  have HtargetEq' := HtargetEq.defeqDFC henv.ordered HctxSymm.defeqCtx
  exact (HtargetEq'.of_l henv Hvlctx.wf.toCtx Htyping).hasType.2

end VerifyInductive
end Lean4Lean
