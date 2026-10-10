import Lean4Lean.Verify.Inductive.Nested.Lowering.Expression
import Lean4Lean.Verify.Inductive.Rules.Alignment

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- `Environment.contains` is `find?` on a well-formed constant map (from the source branch's
`Restoration/Steps.lean`; lowering's freshness reads it). -/
theorem find?_none_of_contains_false
    {env : Environment} {name : Name} (hwf : env.constants.WF)
    (hfresh : env.contains name = false) : env.find? name = none := by
  change env.constants.contains name = false at hfresh
  rw [SMap.find?_isSome] at hfresh
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]
  cases hfind : env.constants.find? name <;> simp_all

/-! # The lowering queue

Relational specification of the lowering of constructors (`ConstructorLowering`), families
(`FamilyLowering`) and of the dynamically growing queue of families (`LoweringQueue`,
`NestedLowering`) performed by `ElimNestedInductive.run`. The resolved forms connect every
replacement to the final `aux2nested` map; with them the file proves that restoring a lowered
constructor gives back its source constructor type
(`ConstructorRestorationInverse.restoredType_eqv_source`), that the executable checks keep
every cached nested application closed over the lowering parameters
(`ElimNestedInductive.run.translationClosed`), and that the validated nested applications are
typed in the de Bruijn parameter context (`NestedLowering.validatedAuxiliaryResidualTranslations`). -/

/-- Constructor-lowering certificate.  In addition to the rebuilt
telescope shape, it records the complete stateful nested-expression
translation from the opened source tail to the installed constructor type. -/
structure ConstructorLowering
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (source : Constructor) (state : Lean4Lean.ElimNestedInductive.State)
    (out : Constructor × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  translated : ∃ lctx tail As lowered openedState,
    LoweringParamOpening {} #[] source.type nparams lctx tail As ∧
    NestedBindingContextWF lctx openedState.ngen ∧
    ∃ Hselection : CDeclArray lctx As,
      Hselection.fvars.Nodup ∧
      openedState.newTypes = state.newTypes ∧
      openedState.nestedAux = state.nestedAux ∧
      openedState.nextIdx = state.nextIdx ∧
      As.size = nparams ∧
      ExprLowering env lctx params As tail openedState
        (lowered, out.2) ∧
      out.1.type = lctx.mkForall As lowered
  /-- Lowering never modifies the universe arguments `lvls` of the state. -/
  lvls : out.2.lvls = state.lvls

/-- The selected opening of a closed source telescope retains enough
information to reconstruct the closing context used by the stronger
execution invariant. -/
def LoweringParamOpening.closingContext
    (H : LoweringParamOpening {} #[] source n lctx tail As)
    (Hbinding : NestedBindingContextWF lctx ngen)
    (Hselection : CDeclArray lctx As)
    (hnodup : Hselection.fvars.Nodup)
    (Hsource : source.FVarsIn fun _ => False) :
    NestedClosingContext lctx As ngen := by
  refine {
    binding := Hbinding
    selection := Hselection
    nodup := hnodup
    close := ?_ }
  intro body Hbody
  rcases H.forallTelescope with ⟨residual, Htelescope⟩
  exact H.toParamOpening.root_mkForall_fvarsClosed Hbinding.wf
    Htelescope Hsource Hselection Hbody

theorem ConstructorLowering.targetRestoreTelescope
    (H : ConstructorLowering env params nparams source state out) :
    RestoreTelescope out.1.type nparams := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, Hopening, _hlctxWF, Hselection,
      _hnodup, hopenedTypes, _hopenedAux, _hopenedNext, hsize, Hreplace, htype⟩
  rw [htype, ← hsize]
  exact (Hselection.forallTelescope lowered).restorePrefix (Nat.le_refl _)

theorem ConstructorLowering.newTypesLE
    (H : ConstructorLowering env params nparams source state out) :
    NestedNewTypesLE state out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, _, _, _, _, hopenedTypes, _, _,
      _, Hreplace, _⟩
  rcases Hreplace.newTypesLE with ⟨suffix, hsuffix⟩
  exact ⟨suffix, by simpa [hopenedTypes] using hsuffix⟩

theorem ConstructorLowering.nestedAuxLE
    (H : ConstructorLowering env params nparams source state out) :
    NestedAuxLE state out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, _, _, _, _, _, hopenedAux, _, _,
      Hreplace, _⟩
  rcases Hreplace.nestedAuxLE with ⟨suffix, hsuffix, -⟩
  exact ⟨suffix, by simpa [hopenedAux] using hsuffix, H.lvls⟩

theorem ConstructorLowering.namesWF
    (H : ConstructorLowering env params nparams source state out)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, _, _, _, _, _, hopenedAux,
      hopenedNext, _, Hreplace, _⟩
  exact Hreplace.namesWF
    (Hstate.ofCacheCounterEq hopenedAux hopenedNext)

theorem ConstructorLowering.namesFresh
    (H : ConstructorLowering env params nparams source state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, _, _, _, _, _, hopenedAux,
      _, _, Hreplace, _⟩
  exact Hreplace.namesFresh (Hstate.ofCacheEq hopenedAux)

theorem ConstructorLowering.auxFVarsIn
    (H : ConstructorLowering env params nparams source state out)
    (Hsource : source.type.FVarsIn fun _ => False)
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, Hopening, _hlctxWF, Hselection,
      _hnodup, _hopenedTypes, hopenedAux, _hopenedNext, _hsize, Hreplace,
      _htype⟩
  have Htail : tail.FVarsIn (· ∈ Hselection.fvars) :=
    Hopening.tailFVarsIn Hselection
      (Hsource.mono fun _ hfalse => False.elim hfalse)
  have Hinput : tail.FVarsIn
      (fun fv => fv ∈ Hselection.fvars ∨ P fv) :=
    Htail.mono fun _ hfv => Or.inl hfv
  have Hopened : NestedAuxFVarsIn P openedState := by
    intro nested name hentry
    apply Hstate nested name
    rwa [hopenedAux] at hentry
  exact Hreplace.auxFVarsIn Hselection Hinput Hparams Hopened

theorem ConstructorLowering.pendingNewTypesClosed
    (H : ConstructorLowering env params nparams source state out)
    (Henv : EnvironmentTypesClosed env)
    (Hsource : source.type.FVarsIn fun _ => False)
    (Hstate : PendingNewTypesClosed cursor state) :
    PendingNewTypesClosed cursor out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, Hopening, Hbinding, Hselection,
      hnodup, hopenedTypes, _hopenedAux, _hopenedNext, _hsize, Hreplace,
      _htype⟩
  let Hclosing := Hopening.closingContext Hbinding Hselection hnodup Hsource
  have Htail : tail.FVarsIn (· ∈ Hselection.fvars) :=
    Hopening.tailFVarsIn Hselection
      (Hsource.mono fun _ hfalse => False.elim hfalse)
  have Hopened : PendingNewTypesClosed cursor openedState := by
    intro j hcursor hj
    have hjState : j < state.newTypes.size := by
      simpa [hopenedTypes] using hj
    have hvalue : openedState.newTypes[j] = state.newTypes[j] := by
      have heq := congrArg
        (fun xs : Array InductiveType => xs[j]!) hopenedTypes
      simpa [Array.getElem!_eq_getD, Array.getD, hj, hjState] using heq
    rw [hvalue]
    exact Hstate j hcursor hjState
  apply Hreplace.pendingNewTypesClosed Henv Hclosing
  · simpa only [Hclosing, LoweringParamOpening.closingContext] using Htail
  · exact Hopened

/-- Constructor lowering interpreted against the final restoration map. The
opened source telescope and rebuilt target telescope are retained verbatim,
while the body traversal is promoted from `ExprLowering` to
`ExprLowering.Resolved`. -/
structure ConstructorLowering.Resolved
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (source : Constructor) (state : Lean4Lean.ElimNestedInductive.State)
    (out : Constructor × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  mapped : ∃ lctx tail As lowered openedState,
    LoweringParamOpening {} #[] source.type nparams lctx tail As ∧
    lctx.WF ∧
    ∃ Hselection : CDeclArray lctx As,
      Hselection.fvars.Nodup ∧
      openedState.newTypes = state.newTypes ∧
      openedState.nestedAux = state.nestedAux ∧
      openedState.nextIdx = state.nextIdx ∧
      As.size = nparams ∧
      ExprLowering.Resolved env lctx params As finalResult tail openedState
        (lowered, out.2) ∧
      out.1.type = lctx.mkForall As lowered
  /-- Lowering never modifies the universe arguments `lvls` of the state. -/
  lvls : out.2.lvls = state.lvls

/-- Constructor lowering with its expression mapping upgraded pointwise to
reopening under a restoration parameter array. -/
structure ConstructorLowering.Reopened
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (restoreAs : Array Expr)
    (source : Constructor) (state : Lean4Lean.ElimNestedInductive.State)
    (out : Constructor × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  reopened : ∃ lctx tail As lowered openedState,
    LoweringParamOpening {} #[] source.type nparams lctx tail As ∧
    ∃ Hselection : CDeclArray lctx As,
      Hselection.fvars.Nodup ∧
      openedState.newTypes = state.newTypes ∧
      openedState.nestedAux = state.nestedAux ∧
      openedState.nextIdx = state.nextIdx ∧
      As.size = nparams ∧
      ExprLowering.Reopened env lctx params As finalResult restoreAs tail
        openedState (lowered, out.2) ∧
      out.1.type = lctx.mkForall As lowered

/-- A mapped lowered constructor type contains no free-variable IDs: the
translated body remains scoped by the copied source parameters, and the
rebuilt forall telescope closes exactly those parameters. -/
theorem ConstructorLowering.Resolved.targetFVarIdsClosed
    (H : ConstructorLowering.Resolved env params nparams finalResult source state
      out)
    (Hsource : source.type.FVarsIn fun _ => False) :
    out.1.type.FVarIdsIn fun _ => False := by
  rcases H.mapped with
    ⟨lctx, tail, As, lowered, openedState, Hopening, hlctxWF, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hmapping, htype⟩
  have Htail : tail.FVarsIn (· ∈ Hselection.fvars) :=
    Hopening.tailFVarsIn Hselection
      (Hsource.mono fun fv hfalse => False.elim hfalse)
  have Hlowered : lowered.FVarIdsIn (· ∈ Hselection.fvars) :=
    Hmapping.outputFVarIdsIn Hselection (FVarsIn_to_FVarIdsIn Htail)
  rcases Hopening.forallTelescope with ⟨residual, Htelescope⟩
  rw [htype]
  exact Hopening.toParamOpening.root_mkForall_fvarIdsClosed hlctxWF
    Htelescope (FVarsIn_to_FVarIdsIn Hsource) Hselection Hlowered

/-- Source and lowered constructor types have exactly the same retained
forall prefix; lowering changes only the residual constructor body. -/
theorem ConstructorLowering.Resolved.sourceTargetSameForallPrefix
    (H : ConstructorLowering.Resolved env params nparams finalResult source state
      out)
    (Hsource : source.type.FVarsIn fun _ => False)
    (hsourceBVar : Closed source.type) :
    Expr.SameForallPrefix nparams source.type out.1.type := by
  rcases H.mapped with
    ⟨lctx, tail, As, lowered, openedState, Hopening, hlctxWF, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hmapping, htype⟩
  rcases Hopening.forallTelescope with ⟨residual, Htelescope⟩
  have hsource : lctx.mkForall As tail = source.type :=
    Hopening.toParamOpening.root_mkForall_tail hlctxWF Htelescope
      (FVarsIn_to_FVarIdsIn Hsource) hsourceBVar
  have hsame := Hselection.sameForallPrefix hnodupAs tail lowered
  rw [hsize, hsource, ← htype] at hsame
  exact hsame

theorem ConstructorLowering.Resolved.reopens
    (H : ConstructorLowering.Resolved env params nparams finalResult source state
      out)
    (hresultParams : finalResult.params = params)
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup)
    (Hsource : source.type.FVarsIn fun _ => False)
    (hparamsSize : params.size = nparams) :
    ConstructorLowering.Reopened env params nparams finalResult restoreAs source
      state out := by
  refine ⟨H.name, ?_⟩
  rcases H.mapped with
    ⟨lctx, tail, As, lowered, openedState, Hopening, _hlctxWF, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hmapping, htype⟩
  have Htail : tail.FVarsIn (· ∈ Hselection.fvars) :=
    Hopening.tailFVarsIn Hselection
      (Hsource.mono fun fv hfalse => False.elim hfalse)
  exact ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
    hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize,
    Hmapping.reopens hresultParams fvars hparams hnodup Hselection (by
      have h1 : Hselection.fvars.length = As.size := by
        simpa using (congrArg Array.size Hselection.expressions).symm
      have h2 : fvars.length = params.size := by simp [hparams]
      omega) Htail,
    htype⟩

/-- Opening the lowered constructor with restoration's fresh parameters
produces the lowering body renamed from lowering's parameter selection to
the concrete restoration array. -/
theorem ConstructorLowering.Reopened.restoreTail
    (H : ConstructorLowering.Reopened env params nparams finalResult targetAs
      source state out)
    (restoreLctx : LocalContext) (restoreAs : Array Expr)
    (restoredTail : Expr)
    (Hrestore : ParamOpening {} #[] out.1.type nparams restoreLctx
      restoreAs restoredTail) :
    ∃ lctx tail As lowered openedState,
      LoweringParamOpening {} #[] source.type nparams lctx tail As ∧
      ∃ Hselection : CDeclArray lctx As,
        Hselection.fvars.Nodup ∧
        openedState.newTypes = state.newTypes ∧
        openedState.nestedAux = state.nestedAux ∧
        openedState.nextIdx = state.nextIdx ∧
        As.size = nparams ∧
        ExprLowering.Reopened env lctx params As finalResult targetAs tail
          openedState (lowered, out.2) ∧
        out.1.type = lctx.mkForall As lowered ∧
        restoredTail = (lowered.abstract As).instantiateRev restoreAs := by
  rcases H.reopened with
    ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hreopening, htype⟩
  have Htelescope := Hselection.forallTelescope lowered
  rw [hsize, ← htype] at Htelescope
  have htail := Hrestore.forallResidual Htelescope
  refine ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
    hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hreopening, htype,
    ?_⟩
  simpa only [Hselection.expressions, Expr.abstractN_eq] using htail

/-- The body exposed by restoration is the source constructor body with
the restoration parameters substituted for lowering's fresh parameters.
This is the constructor-scoped inverse theorem: it combines the exact two
telescope traversals with the structural inverse for nested replacement. -/
theorem ConstructorLowering.Reopened.restoreTail_inverse
    (H : ConstructorLowering.Reopened env params nparams finalResult targetAs
      source state out)
    (restoreLctx : LocalContext) (restoreAs : Array Expr)
    (restoredTail : Expr)
    (Hrestore : ParamOpening {} #[] out.1.type nparams restoreLctx
      restoreAs restoredTail)
    (restoreEnv : Environment)
    (htargetAs : targetAs = restoreAs)
    (hresultNParams : finalResult.nparams = nparams)
    (Hsource : RestoreSourceDisjoint finalResult restoreEnv source.type)
    (hsourceBVar : Closed source.type) :
    ∃ lctx tail As lowered openedState,
      LoweringParamOpening {} #[] source.type nparams lctx tail As ∧
      ∃ Hselection : CDeclArray lctx As,
        Hselection.fvars.Nodup ∧
        openedState.newTypes = state.newTypes ∧
        openedState.nestedAux = state.nestedAux ∧
        openedState.nextIdx = state.nextIdx ∧
        As.size = nparams ∧
        ExprLowering.Reopened env lctx params As finalResult targetAs tail
          openedState (lowered, out.2) ∧
        out.1.type = lctx.mkForall As lowered ∧
        restoredTail = (lowered.abstract As).instantiateRev restoreAs ∧
        ((restoredTail.replace
            (finalResult.restoreNestedNode restoreEnv restoreAs {})) ==
          Expr.reopenParams tail As restoreAs) = true := by
  rcases H.restoreTail restoreLctx restoreAs restoredTail Hrestore with
    ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hreopening,
      htype, hrestoredTail⟩
  rcases Hrestore.params_fvars_extension with
    ⟨restoreFvars, hrestoreList, hrestoreLength⟩
  have hrestoreArray :
      restoreAs = (restoreFvars.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simpa using hrestoreList
  have hselectionLength : Hselection.fvars.length = As.size := by
    simpa using (congrArg Array.size Hselection.expressions).symm
  have hrestoreSize :
      restoreFvars.length = Hselection.fvars.length := by
    rw [hrestoreLength, hselectionLength, hsize]
  have hresultSize : finalResult.nparams = As.size := by
    rw [hresultNParams, hsize]
  have HtailSource : RestoreSourceDisjoint finalResult restoreEnv tail :=
    Hopening.tailRestoreSourceDisjoint Hsource
  have hinverse := Hreopening.restore_eqv restoreEnv Hselection hnodupAs
    restoreFvars
    (by simpa [htargetAs] using hrestoreArray) hrestoreSize hresultSize
    HtailSource 0
  have htailClosed : Closed tail := Hopening.tailClosed hsourceBVar
  have hloweredClosed : Closed lowered :=
    Hreopening.closed Hselection htailClosed
  have hloweredOpen := Expr.reopenFVarsAt_eq_reopenParams hnodupAs
    hrestoreSize Hselection.expressions hrestoreArray lowered 0
    hloweredClosed.looseBVarRange_zero
  have hsourceOpen := Expr.reopenFVarsAt_eq_reopenParams hnodupAs
    hrestoreSize Hselection.expressions hrestoreArray tail 0
    htailClosed.looseBVarRange_zero
  have hrestoredOpen :
      restoredTail = Expr.reopenParams lowered As restoreAs := by
    simpa [Expr.reopenParams] using hrestoredTail
  rw [htargetAs, hloweredOpen, hsourceOpen, ← hrestoredOpen] at hinverse
  exact ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
    hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hreopening,
    htype, hrestoredTail, hinverse⟩

/-- Operational constructor restoration consumes a mapped lowering body and
produces the correspondingly renamed source body.  Unlike
`restoreTail_inverse`, this theorem starts from the mapping certificate
available before restoration chooses its fresh variables and concludes about
the `restoredBody` retained by `NestedRestoration`. -/
theorem ConstructorLowering.Resolved.restoredBody_inverse
    (H : ConstructorLowering.Resolved env params nparams finalResult source state
      out)
    (hresultParams : finalResult.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (hsourceBVar : Closed source.type)
    (hparamsSize : params.size = nparams)
    (restoreLctx : LocalContext) (restoreAs : Array Expr)
    (openedBody restoredBody : Expr)
    (Hrestore : ParamOpening {} #[] out.1.type nparams restoreLctx
      restoreAs openedBody)
    (restoreEnv : Environment)
    (Hbody : ExprReplacement
      (finalResult.restoreNestedNode restoreEnv restoreAs {}) openedBody
        restoredBody)
    (hresultNParams : finalResult.nparams = nparams)
    (Hsource : RestoreSourceDisjoint finalResult restoreEnv source.type) :
    ∃ lctx tail As,
      LoweringParamOpening {} #[] source.type nparams lctx tail As ∧
      ∃ Hselection : CDeclArray lctx As,
        Hselection.fvars.Nodup ∧ As.size = nparams ∧
        (restoredBody == Expr.reopenParams tail As restoreAs) = true := by
  have Hreopening : ConstructorLowering.Reopened env params nparams finalResult
      restoreAs source state out :=
    H.reopens hresultParams paramFvars hparams hnodup HsourceClosed hparamsSize
  rcases Hreopening.restoreTail_inverse restoreLctx restoreAs openedBody
      Hrestore restoreEnv rfl hresultNParams Hsource hsourceBVar with
    ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
      hnodupAs, _hopenedTypes, _hopenedAux, _hopenedNext, hsize,
      _Hreopening, _htype, _hopenedBody, hinverse⟩
  have hrestoredInverse :
      (restoredBody == Expr.reopenParams tail As restoreAs) = true := by
    rw [Hbody.eq_replace]
    exact hinverse
  exact ⟨lctx, tail, As, Hopening, Hselection, hnodupAs, hsize,
    hrestoredInverse⟩

/-- A whole operational `NestedRestoration` of a lowered constructor, with
its restored body related back to the independently checked source
constructor body.  The outer telescope equations are retained explicitly;
the next abstraction layer can therefore prove alpha-equivalence without
replaying either executable traversal. -/
structure ConstructorRestorationInverse
    (result : Lean4Lean.ElimNestedInductive.Result) (env : Environment)
    (nparams : Nat) (source lowered : Constructor) (restoredType : Expr) where
  restoreLctx : LocalContext
  restoreAs : Array Expr
  openedBody : Expr
  restoredBody : Expr
  loweredOpening : ParamOpening {} #[] lowered.type nparams
    restoreLctx restoreAs openedBody
  restoreLctxWF : restoreLctx.WF
  restoreSelection : CDeclArray restoreLctx restoreAs
  restoreNodup : restoreSelection.fvars.Nodup
  bodyRestoration : ExprReplacement
    (result.restoreNestedNode env restoreAs {}) openedBody restoredBody
  output : restoredType = if lowered.type.isForall then
    restoreLctx.mkForall restoreAs restoredBody
    else restoreLctx.mkLambda restoreAs restoredBody
  sourceLctx : LocalContext
  sourceTail : Expr
  sourceAs : Array Expr
  sourceClosed : source.type.FVarsIn fun _ => False
  sourceBVarClosed : Closed source.type
  loweredFVarIdsClosed : lowered.type.FVarIdsIn fun _ => False
  sourceLoweredPrefix :
    Expr.SameForallPrefix nparams source.type lowered.type
  sourceOpening : LoweringParamOpening {} #[] source.type nparams sourceLctx
    sourceTail sourceAs
  sourceSelection : CDeclArray sourceLctx sourceAs
  sourceNodup : sourceSelection.fvars.Nodup
  sourceArity : sourceAs.size = nparams
  bodyInverse :
    (restoredBody == Expr.reopenParams sourceTail sourceAs restoreAs) = true

/-- Whole-constructor restoration inverse with source disjointness
(`RestoreSourceDisjoint`) as a premise.
This form does not assume any naming convention for auxiliary
constructors; callers may establish source disjointness from typing and
freshness instead. -/
theorem ConstructorLowering.Resolved.nestedRestoration_inverse
    (H : ConstructorLowering.Resolved env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (hsourceBVar : Closed source.type)
    (hparamsSize : params.size = nparams)
    (restoreEnv : Environment)
    (HsourceDisjoint : RestoreSourceDisjoint result restoreEnv source.type)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : NestedRestoration result restoreEnv {} out.1.type
      restoredType) :
    Nonempty (ConstructorRestorationInverse result restoreEnv nparams source
      out.1 restoredType) := by
  rcases Hrestored with
    ⟨restoreLctx, restoreAs, openedBody, restoredBody, Hopening,
      Hbody, houtput⟩
  rcases Hopening.2 with ⟨hrestoreLctxWF, HrestoreSelection,
    hrestoreNodup⟩
  have Hopening' := Hopening.1
  rw [hresultNParams] at Hopening'
  rcases H.restoredBody_inverse hresultParams paramFvars hparams hnodup
      HsourceClosed hsourceBVar hparamsSize restoreLctx restoreAs openedBody
      restoredBody Hopening'
      restoreEnv Hbody hresultNParams HsourceDisjoint with
    ⟨sourceLctx, sourceTail, sourceAs, HsourceOpening, Hselection,
      hsourceNodup, hsourceArity, hinverse⟩
  exact ⟨{
    restoreLctx := restoreLctx
    restoreAs := restoreAs
    openedBody := openedBody
    restoredBody := restoredBody
    loweredOpening := Hopening'
    restoreLctxWF := hrestoreLctxWF
    restoreSelection := HrestoreSelection
    restoreNodup := hrestoreNodup
    bodyRestoration := Hbody
    output := houtput
    sourceLctx := sourceLctx
    sourceTail := sourceTail
    sourceAs := sourceAs
    sourceClosed := HsourceClosed
    sourceBVarClosed := hsourceBVar
    loweredFVarIdsClosed := H.targetFVarIdsClosed HsourceClosed
    sourceLoweredPrefix := H.sourceTargetSameForallPrefix HsourceClosed hsourceBVar
    sourceOpening := HsourceOpening
    sourceSelection := Hselection
    sourceNodup := hsourceNodup
    sourceArity := hsourceArity
    bodyInverse := hinverse }⟩

/-- Eliminate the source-opening free variables from the body inverse.  The
restored body is the ordinary residual of the source constructor telescope,
instantiated only with restoration's fresh parameter array. -/
theorem ConstructorRestorationInverse.restoredBody_residual
    (H : ConstructorRestorationInverse result env nparams source lowered
      restoredType) :
    ∃ residual,
      Expr.ForallTelescope source.type nparams residual ∧
      (H.restoredBody == residual.instantiateRev H.restoreAs) = true := by
  rcases H.sourceOpening.forallTelescope with ⟨residual, Htelescope⟩
  have htail : H.sourceTail = residual.instantiateRev H.sourceAs :=
    H.sourceOpening.toParamOpening.forallResidual Htelescope
  have hfree : residual.FVarsIn
      (fun fv => fv ∉ H.sourceSelection.fvars) :=
    (Htelescope.resultFVarsIn H.sourceClosed).mono fun fv hfalse =>
      False.elim hfalse
  have hlb : residual.looseBVarRange' ≤ H.sourceSelection.fvars.length := by
    have hres := (Htelescope.closed_result (depth := 0)
      H.sourceBVarClosed).looseBVarRange_le
    have hlen : H.sourceSelection.fvars.length = H.sourceAs.size := by
      simpa using (congrArg Array.size H.sourceSelection.expressions).symm
    rw [hlen, H.sourceArity]
    simpa using hres
  have hcancel := hfree.reabstract_instantiateRev_fvarArray H.sourceAs
    H.restoreAs H.sourceSelection.fvars H.sourceSelection.expressions
    H.sourceNodup hlb
  have hopen : Expr.reopenParams H.sourceTail H.sourceAs H.restoreAs =
      residual.instantiateRev H.restoreAs := by
    rw [htail]
    simpa [Expr.reopenParams] using hcancel
  have hinverse := H.bodyInverse
  rw [hopen] at hinverse
  exact ⟨residual, Htelescope, hinverse⟩

/-- Whole-constructor inverse: rebuilding the restored body under the copied
parameter telescope yields a constructor type equivalent to the independent
source constructor type. -/
theorem ConstructorRestorationInverse.restoredType_eqv_source
    (H : ConstructorRestorationInverse result env nparams source lowered
      restoredType) :
    (restoredType == source.type) = true := by
  rcases H.sourceLoweredPrefix.transferRestoreOpening H.loweredOpening with
    ⟨sourceOpened, HsourceRestore⟩
  rcases H.restoredBody_residual with
    ⟨residual, Htelescope, hbodyResidual⟩
  have hsourceOpened :
      sourceOpened = residual.instantiateRev H.restoreAs :=
    HsourceRestore.forallResidual Htelescope
  have hbodyOpened : (H.restoredBody == sourceOpened) = true := by
    rw [hsourceOpened]
    exact hbodyResidual
  have hclosedSource : source.type.FVarIdsIn fun _ => False :=
    FVarsIn_to_FVarIdsIn H.sourceClosed
  have hsourceRebuild :
      H.restoreLctx.mkForall H.restoreAs sourceOpened = source.type :=
    HsourceRestore.root_mkForall_tail H.restoreLctxWF Htelescope hclosedSource
      H.sourceBVarClosed
  have hwrapped := H.restoreSelection.mkForall_eqv H.restoreNodup hbodyOpened
  rw [hsourceRebuild] at hwrapped
  have houtput : restoredType =
      H.restoreLctx.mkForall H.restoreAs H.restoredBody := by
    refine H.output.trans ?_
    by_cases hzero : nparams = 0
    · have hsize : H.restoreAs.size = 0 :=
        H.loweredOpening.initial_size.trans hzero
      have hempty : H.restoreAs = #[] :=
        Array.eq_empty_of_size_eq_zero hsize
      rw [hempty]
      split
      · rfl
      · rw [LocalContext.mkForall, LocalContext.mkLambda]
        rw [show (#[] : Array Expr) =
            (([] : List FVarId).map Expr.fvar).toArray from rfl,
          LocalContext.mkBinding_eqN, LocalContext.mkBinding_eqN]
        simp only [LocalContext.mkBindingListN_nil]
    · have hpos : 0 < nparams := Nat.pos_of_ne_zero hzero
      have hisForall :=
        H.sourceLoweredPrefix.target_isForall_of_pos hpos
      simp [hisForall]
  rw [houtput]
  exact hwrapped

theorem ConstructorLowering.resolvedMapping
    (H : ConstructorLowering env params nparams source state out)
    (Hlater : NestedAuxLE out.2 finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    ConstructorLowering.Resolved env params nparams finalResult source state out := by
  refine ⟨H.name, ?_, H.lvls⟩
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, Hopening, hlctxWF, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hreplace, htype⟩
  exact ⟨lctx, tail, As, lowered, openedState, Hopening, hlctxWF.wf, Hselection,
    hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize,
    Hreplace.resolvedMapping Hlater Hmap, htype⟩

theorem ElimNestedInductive.lowerConstructor.translationPending
    (params : Array Expr) (nparams : Nat) (ctor : Constructor)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hctor : ctor.type.FVarsIn fun _ => False)
    (Hstate : PendingNewTypesClosed cursor state) :
    (Lean4Lean.ElimNestedInductive.lowerConstructor params nparams ctor
      env state).WF fun out =>
        ConstructorLowering env params nparams ctor state out ∧
        PendingNewTypesClosed cursor out.2 := by
  unfold Lean4Lean.ElimNestedInductive.lowerConstructor
  apply ElimNestedInductive.withParams.refinesClosing (Htype := Hctor)
  intro lctx tail As openedState Hopening Hclosing Htail hopenedTypes
    hopenedAux hopenedNext _hprefix hopenedLvls
  have hsize : As.size = nparams := Hopening.initial_size
  simp only [hsize, beq_self_eq_true, if_true]
  have hsubst : As.size = params.size := by omega
  refine nestedBind.WF
    (replaceAllNested_refines env lctx params As tail openedState
      hsubst hclosures) ?_
  intro lowered outState Hlowered
  have HopenedPending : PendingNewTypesClosed cursor openedState := by
    intro j hcursor hj
    have hjState : j < state.newTypes.size := by
      simpa [hopenedTypes] using hj
    have hvalue : openedState.newTypes[j] = state.newTypes[j] := by
      have heq := congrArg
        (fun xs : Array InductiveType => xs[j]!) hopenedTypes
      simpa [Array.getElem!_eq_getD, Array.getD, hj, hjState] using heq
    rw [hvalue]
    exact Hstate j hcursor hjState
  exact Except.WF.pure ⟨
    ⟨rfl, ⟨lctx, tail, As, lowered, openedState, Hopening,
      Hclosing.binding, Hclosing.selection, Hclosing.nodup,
      hopenedTypes, hopenedAux, hopenedNext, hsize,
      Hlowered, rfl⟩, Hlowered.nestedAuxLE.lvls.trans hopenedLvls⟩,
    Hlowered.pendingNewTypesClosed Henv Hclosing Htail HopenedPending⟩

/-- Stateful positional correspondence for an entire constructor list. -/
inductive ConstructorLowerings
    (env : Environment) (params : Array Expr) (nparams : Nat) :
    List Constructor → Lean4Lean.ElimNestedInductive.State →
      List Constructor × Lean4Lean.ElimNestedInductive.State → Prop
  | nil : ConstructorLowerings env params nparams [] state ([], state)
  | cons : ConstructorLowering env params nparams source state step →
      ConstructorLowerings env params nparams sources step.2 out →
      ConstructorLowerings env params nparams (source :: sources)
        state (step.1 :: out.1, out.2)

theorem ConstructorLowerings.newTypesLE
    (H : ConstructorLowerings env params nparams sources state out) :
    NestedNewTypesLE state out.2 := by
  induction H with
  | nil => exact .refl _
  | cons Hhead Htail ih => exact Hhead.newTypesLE.trans ih

theorem ConstructorLowerings.nestedAuxLE
    (H : ConstructorLowerings env params nparams sources state out) :
    NestedAuxLE state out.2 := by
  induction H with
  | nil => exact .refl _
  | cons Hhead Htail ih => exact Hhead.nestedAuxLE.trans ih

theorem ConstructorLowerings.pendingNewTypesClosed
    (H : ConstructorLowerings env params nparams sources state out)
    (Henv : EnvironmentTypesClosed env)
    (Hsources : ∀ source ∈ sources,
      source.type.FVarsIn fun _ => False)
    (Hstate : PendingNewTypesClosed cursor state) :
    PendingNewTypesClosed cursor out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hhead Htail ih =>
    exact ih (fun source hsource => Hsources source (by simp [hsource]))
      (Hhead.pendingNewTypesClosed Henv (Hsources _ (by simp)) Hstate)

theorem ConstructorLowerings.namesWF
    (H : ConstructorLowerings env params nparams sources state out)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hhead Htail ih => exact ih (Hhead.namesWF Hstate)

theorem ConstructorLowerings.namesFresh
    (H : ConstructorLowerings env params nparams sources state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hhead Htail ih => exact ih (Hhead.namesFresh Hstate)

theorem ConstructorLowerings.auxFVarsIn
    (H : ConstructorLowerings env params nparams sources state out)
    (Hsources : ∀ source ∈ sources,
      source.type.FVarsIn fun _ => False)
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hhead Htail ih =>
    apply ih
    · intro source hsource
      exact Hsources source (by simp [hsource])
    · exact Hhead.auxFVarsIn (Hsources _ (by simp)) Hparams Hstate

inductive ConstructorLowerings.Resolved
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result) :
    List Constructor → Lean4Lean.ElimNestedInductive.State →
      List Constructor × Lean4Lean.ElimNestedInductive.State → Prop
  | nil : ConstructorLowerings.Resolved env params nparams finalResult [] state
      ([], state)
  | cons : ConstructorLowering.Resolved env params nparams finalResult source
      state step →
      ConstructorLowerings.Resolved env params nparams finalResult sources step.2
        out →
      ConstructorLowerings.Resolved env params nparams finalResult
        (source :: sources) state (step.1 :: out.1, out.2)

theorem ConstructorLowerings.Resolved.length
    (H : ConstructorLowerings.Resolved env params nparams finalResult sources
      state out) : out.1.length = sources.length := by
  induction H with
  | nil => rfl
  | cons Hhead Htail ih => simp [ih]

/-- Positional projection of the state-threaded constructor mapping.  Both
the source and target list lookups are retained, so subsequent restoration
folds can align their metadata without a name-based uniqueness assumption. -/
theorem ConstructorLowerings.Resolved.mappingAt
    (H : ConstructorLowerings.Resolved env params nparams finalResult sources
      state out) (i : Nat) (hi : i < sources.length) :
    ∃ source target before after,
      sources[i]? = some source ∧
      out.1[i]? = some target ∧
      ConstructorLowering.Resolved env params nparams finalResult source before
        (target, after) := by
  induction H generalizing i with
  | nil => simp at hi
  | @cons source state step sources out Hhead Htail ih =>
    cases i with
    | zero => exact ⟨source, step.1, state, step.2, by simp, by simp, Hhead⟩
    | succ i =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
      rcases ih i hi with
        ⟨tailSource, tailTarget, before, after, hsource, htarget, Hmapping⟩
      exact ⟨tailSource, tailTarget, before, after, by simpa, by simpa,
        Hmapping⟩

theorem ConstructorLowerings.resolvedMapping
    (H : ConstructorLowerings env params nparams sources state out)
    (Hlater : NestedAuxLE out.2 finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    ConstructorLowerings.Resolved env params nparams finalResult sources state out := by
  induction H generalizing finalState with
  | nil => exact .nil
  | cons Hhead Htail ih =>
    exact .cons
      (Hhead.resolvedMapping (Htail.nestedAuxLE.trans Hlater) Hmap)
      (ih Hlater Hmap)

theorem ConstructorLowerings.targetsRestoreTelescope
    (H : ConstructorLowerings env params nparams sources state out) :
    ∀ ctor ∈ out.1, RestoreTelescope ctor.type nparams := by
  induction H with
  | nil => simp
  | cons Hhead Htail ih =>
    intro ctor hctor
    simp only [List.mem_cons] at hctor
    rcases hctor with rfl | htail
    · exact Hhead.targetRestoreTelescope
    · exact ih ctor htail

theorem ElimNestedInductive.lowerConstructors.translationsPending
    (params : Array Expr) (nparams : Nat) (ctors : List Constructor)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hctors : ∀ ctor ∈ ctors, ctor.type.FVarsIn fun _ => False)
    (Hstate : PendingNewTypesClosed cursor state) :
    (ctors.mapM (Lean4Lean.ElimNestedInductive.lowerConstructor params nparams)
      env state).WF fun out =>
        ConstructorLowerings env params nparams ctors state out ∧
        PendingNewTypesClosed cursor out.2 := by
  induction ctors generalizing state with
  | nil => exact Except.WF.pure ⟨.nil, Hstate⟩
  | cons ctor ctors ih =>
    rw [List.mapM_cons]
    refine nestedBind.WF
      (ElimNestedInductive.lowerConstructor.translationPending params nparams
        ctor env state hparams hclosures Henv (Hctors ctor (by simp)) Hstate) ?_
    intro lowered nextState Hlowered
    refine nestedBind.WF (ih nextState
      (fun tail htail => Hctors tail (by simp [htail])) Hlowered.2) ?_
    intro loweredTail finalState Htail
    exact Except.WF.pure ⟨.cons Hlowered.1 Htail.1, Htail.2⟩

/-- Family-level lowering: headers are preserved and the constructor
list carries the full state-threaded nested-expression translation. -/
structure FamilyLowering
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (source : InductiveType) (state : Lean4Lean.ElimNestedInductive.State)
    (out : InductiveType × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  type : out.1.type = source.type
  constructors : ConstructorLowerings env params nparams source.ctors
    state (out.1.ctors, out.2)

structure FamilyLowering.Resolved
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (source : InductiveType) (state : Lean4Lean.ElimNestedInductive.State)
    (out : InductiveType × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  type : out.1.type = source.type
  constructors : ConstructorLowerings.Resolved env params nparams finalResult
    source.ctors state (out.1.ctors, out.2)

theorem FamilyLowering.newTypesLE
    (H : FamilyLowering env params nparams source state out) :
    NestedNewTypesLE state out.2 := H.constructors.newTypesLE

theorem FamilyLowering.nestedAuxLE
    (H : FamilyLowering env params nparams source state out) :
    NestedAuxLE state out.2 := H.constructors.nestedAuxLE

theorem FamilyLowering.pendingNewTypesClosed
    (H : FamilyLowering env params nparams source state out)
    (Henv : EnvironmentTypesClosed env)
    (Hsource : InductiveConstructorsClosed source)
    (Hstate : PendingNewTypesClosed cursor state) :
    PendingNewTypesClosed cursor out.2 :=
  H.constructors.pendingNewTypesClosed Henv Hsource Hstate

theorem FamilyLowering.namesWF
    (H : FamilyLowering env params nparams source state out)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 :=
  H.constructors.namesWF Hstate

theorem FamilyLowering.namesFresh
    (H : FamilyLowering env params nparams source state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 :=
  H.constructors.namesFresh Hstate

theorem FamilyLowering.auxFVarsIn
    (H : FamilyLowering env params nparams source state out)
    (Hsource : ∀ ctor ∈ source.ctors,
      ctor.type.FVarsIn fun _ => False)
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 :=
  H.constructors.auxFVarsIn Hsource Hparams Hstate

theorem FamilyLowering.resolvedMapping
    (H : FamilyLowering env params nparams source state out)
    (Hlater : NestedAuxLE out.2 finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    FamilyLowering.Resolved env params nparams finalResult source state out :=
  ⟨H.name, H.type, H.constructors.resolvedMapping Hlater Hmap⟩

theorem FamilyLowering.targetRestoreTelescope
    (H : FamilyLowering env params nparams source state out) :
    ∀ ctor ∈ out.1.ctors, RestoreTelescope ctor.type nparams :=
  H.constructors.targetsRestoreTelescope

def RestorableInductiveType (nparams : Nat) (type : InductiveType) : Prop :=
  ∀ ctor ∈ type.ctors, RestoreTelescope ctor.type nparams

def RestorableNewTypesPrefix (nparams i : Nat)
    (state : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∀ j, j < i → (hj : j < state.newTypes.size) →
    RestorableInductiveType nparams state.newTypes[j]

theorem RestorableNewTypesPrefix.zero
    (state : Lean4Lean.ElimNestedInductive.State) :
    RestorableNewTypesPrefix nparams 0 state := by
  intro j hj
  omega

def NewTypeNamePresent (state : Lean4Lean.ElimNestedInductive.State)
    (name : Name) : Prop :=
  ∃ type ∈ state.newTypes.toList, type.name = name

theorem ElimNestedInductive.lowerInductive.translationPending
    (params : Array Expr) (nparams : Nat) (indType : InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hsource : InductiveConstructorsClosed indType)
    (Hstate : PendingNewTypesClosed cursor state) :
    (Lean4Lean.ElimNestedInductive.lowerInductive params nparams indType
      env state).WF fun out =>
        FamilyLowering env params nparams indType state out ∧
        PendingNewTypesClosed cursor out.2 := by
  unfold Lean4Lean.ElimNestedInductive.lowerInductive
  refine nestedBind.WF
    (ElimNestedInductive.lowerConstructors.translationsPending params nparams
      indType.ctors env state hparams hclosures Henv Hsource Hstate) ?_
  intro ctors nextState Hctors
  exact Except.WF.pure ⟨⟨rfl, rfl, Hctors.1⟩, Hctors.2⟩

/-- State transition for one iteration of the dynamic lowering queue. -/
inductive LowerNextStep
    (env : Environment) (params : Array Expr) (nparams i : Nat)
    (state : Lean4Lean.ElimNestedInductive.State) :
    Option InductiveType × Lean4Lean.ElimNestedInductive.State → Prop
  | done (hbound : state.newTypes.size ≤ i) :
      LowerNextStep env params nparams i state (none, state)
  | step (hidx : i < state.newTypes.size)
      (Hlowered : FamilyLowering env params nparams
        state.newTypes[i] state (target, loweredState)) :
      LowerNextStep env params nparams i state
        (some state.newTypes[i], { loweredState with
          newTypes := loweredState.newTypes.set! i target })

theorem LowerNextStep.restorablePrefix
    (H : LowerNextStep env params nparams i state
      (some source, nextState))
    (Hprefix : RestorableNewTypesPrefix nparams i state) :
    RestorableNewTypesPrefix nparams (i + 1) nextState := by
  cases H with
  | step hidx Hlowered =>
    rename_i target loweredState
    have Hle := Hlowered.newTypesLE
    have hiLowered := (Hle.getElem hidx).choose
    intro j hj hjNext
    have hjLowered : j < loweredState.newTypes.size := by
      simpa [Array.size_set!] using hjNext
    by_cases hji : j = i
    · subst j
      change RestorableInductiveType nparams
        (loweredState.newTypes.set! i target)[i]
      simpa [Array.getElem_setIfInBounds, hiLowered,
        RestorableInductiveType] using Hlowered.targetRestoreTelescope
    · have hjlt : j < i := by omega
      rcases Hle.getElem (show j < state.newTypes.size by omega) with
        ⟨hjInLowered, hsame⟩
      change RestorableInductiveType nparams
        (loweredState.newTypes.set! i target)[j]
      rw [show (loweredState.newTypes.set! i target)[j] =
          loweredState.newTypes[j] by
        have hget := Array.getElem_setIfInBounds
          (xs := loweredState.newTypes) (i := i) (a := target)
          (j := j) hjInLowered
        rw [if_neg (fun h : i = j => hji h.symm)] at hget
        exact hget]
      rw [hsame]
      exact Hprefix j hjlt _

theorem LowerNextStep.nestedAuxLE
    (H : LowerNextStep env params nparams i state out) :
    NestedAuxLE state out.2 := by
  cases H with
  | done => exact .refl _
  | step _ Hlowered => exact Hlowered.nestedAuxLE

theorem LowerNextStep.namesWF
    (H : LowerNextStep env params nparams i state out)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  cases H with
  | done => exact Hstate
  | step _ Hlowered =>
    exact (Hlowered.namesWF Hstate).ofCacheCounterEq rfl rfl

theorem LowerNextStep.namesFresh
    (H : LowerNextStep env params nparams i state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  cases H with
  | done => exact Hstate
  | step _ Hlowered => exact (Hlowered.namesFresh Hstate).ofCacheEq rfl

theorem LowerNextStep.preservesTypeName
    (H : LowerNextStep env params nparams i state
      (some source, nextState))
    (Hname : NewTypeNamePresent state name) :
    NewTypeNamePresent nextState name := by
  cases H with
  | step hidx Hlowered =>
    rename_i target loweredState
    rcases Hname with ⟨type, htype, hname⟩
    rcases List.mem_iff_getElem.mp htype with ⟨j, hj, htypeEq⟩
    have hjState : j < state.newTypes.size := by simpa using hj
    rcases Hlowered.newTypesLE.getElem hjState with
      ⟨hjLowered, hpreserved⟩
    have hjNext : j < (loweredState.newTypes.set! i target).size := by
      simpa [Array.size_set!] using hjLowered
    let finalType := (loweredState.newTypes.set! i target)[j]
    refine ⟨finalType, by
      exact List.getElem_mem hjNext, ?_⟩
    by_cases hji : j = i
    · subst j
      have hset : finalType = target := by
        simp [finalType]
      rw [hset, Hlowered.name]
      have hsource : state.newTypes[i] = type := by
        simpa using htypeEq
      rw [hsource]
      exact hname
    · have hset : finalType = loweredState.newTypes[j] := by
        have hget := Array.getElem_setIfInBounds
          (xs := loweredState.newTypes) (i := i) (a := target)
          (j := j) hjLowered
        rw [if_neg (fun h : i = j => hji h.symm)] at hget
        exact hget
      rw [hset, hpreserved]
      have : state.newTypes[j] = type := by simpa using htypeEq
      rw [this]
      exact hname

/-- A queue step changes only its selected slot. Auxiliary discovery may
append new families before that slot is overwritten, but every distinct
pre-existing index retains its exact family record. -/
theorem LowerNextStep.getElem_ne
    (H : LowerNextStep env params nparams i state
      (some source, nextState))
    (hj : j < state.newTypes.size) (hne : j ≠ i) :
    ∃ hjNext : j < nextState.newTypes.size,
      nextState.newTypes[j] = state.newTypes[j] := by
  cases H with
  | step hi Hlowered =>
    rename_i target loweredState
    rcases Hlowered.newTypesLE.getElem hj with
      ⟨hjLowered, hsame⟩
    have hjNext : j <
        ({ loweredState with
          newTypes := loweredState.newTypes.set! i target }).newTypes.size := by
      simpa [Array.size_set!] using hjLowered
    refine ⟨hjNext, ?_⟩
    change (loweredState.newTypes.set! i target)[j] = state.newTypes[j]
    have hget := Array.getElem_setIfInBounds
      (xs := loweredState.newTypes) (i := i) (a := target)
      (j := j) hjLowered
    rw [if_neg (fun h : i = j => hne h.symm)] at hget
    simpa [Array.set!] using hget.trans hsame

/-- The selected queue slot contains the just-lowered target after the step,
even when lowering appended auxiliary families along the way. -/
theorem LowerNextStep.getElem_selected
    (H : LowerNextStep env params nparams i state
      (some source, nextState)) (hi : i < state.newTypes.size) :
    ∃ target loweredState,
      FamilyLowering env params nparams
        state.newTypes[i] state
        (target, loweredState) ∧
      nextState.nestedAux = loweredState.nestedAux ∧
      ∃ hiNext : i < nextState.newTypes.size,
        nextState.newTypes[i] = target := by
  cases H with
  | step hi Hlowered =>
    rename_i target loweredState
    have hiLowered := Hlowered.newTypesLE.getElem hi |>.choose
    have hiNext : i <
        ({ loweredState with
          newTypes := loweredState.newTypes.set! i target }).newTypes.size := by
      simpa [Array.size_set!] using hiLowered
    refine ⟨target, loweredState, Hlowered, rfl, hiNext, ?_⟩
    change (loweredState.newTypes.set! i target)[i] = target
    simp

theorem LowerNextStep.pendingNewTypesClosed
    (H : LowerNextStep env params nparams i state out)
    (Henv : EnvironmentTypesClosed env)
    (Hpending : PendingNewTypesClosed i state) :
    PendingNewTypesClosed (i + 1) out.2 := by
  cases H with
  | done hbound =>
    intro j hcursor hj
    exact Hpending j (by omega) hj
  | step hi Hlowered =>
    rename_i target loweredState
    have HloweredPending := Hlowered.pendingNewTypesClosed Henv
      (Hpending i (Nat.le_refl _) hi) Hpending
    intro j hcursor hj
    have hjLowered : j < loweredState.newTypes.size := by
      simpa [Array.size_set!] using hj
    have hne : j ≠ i := by omega
    have hvalue := Array.getElem_setIfInBounds
      (xs := loweredState.newTypes) (i := i) (a := target)
      (j := j) hjLowered
    rw [if_neg (fun heq : i = j => hne heq.symm)] at hvalue
    change InductiveConstructorsClosed
      (loweredState.newTypes.set! i target)[j]
    rw [show (loweredState.newTypes.set! i target)[j] =
      loweredState.newTypes[j] by simpa [Array.set!] using hvalue]
    exact HloweredPending j (by omega) hjLowered

theorem ElimNestedInductive.lowerNext.translationPending
    (params : Array Expr) (nparams i : Nat)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hstate : PendingNewTypesClosed i state) :
    (Lean4Lean.ElimNestedInductive.lowerNext params nparams i env state).WF
      fun out =>
        LowerNextStep env params nparams i state out ∧
        PendingNewTypesClosed (i + 1) out.2 := by
  unfold Lean4Lean.ElimNestedInductive.lowerNext
  simp only [get, bind, StateT.bind, ReaderT.bind]
  have hget : ((getThe Lean4Lean.ElimNestedInductive.State :
      Lean4Lean.ElimNestedInductive.M Lean4Lean.ElimNestedInductive.State)
      env state) = Except.ok (state, state) := rfl
  rw [hget]
  simp only [Except.bind]
  by_cases hidx : i < state.newTypes.size
  · rw [dif_pos hidx]
    refine nestedBind.WF
      (ElimNestedInductive.lowerInductive.translationPending params nparams
        state.newTypes[i] env state hparams hclosures Henv
        (Hstate i (Nat.le_refl _) hidx) Hstate) ?_
    intro target loweredState Htarget
    simp only [modify, pure, StateT.pure, ReaderT.pure,
      bind, StateT.bind, ReaderT.bind]
    have HnextPending : PendingNewTypesClosed (i + 1)
        { loweredState with
          newTypes := loweredState.newTypes.set! i target } := by
      intro j hcursor hj
      have hjLowered : j < loweredState.newTypes.size := by
        simpa [Array.size_set!] using hj
      have hne : j ≠ i := by omega
      have hvalue := Array.getElem_setIfInBounds
        (xs := loweredState.newTypes) (i := i) (a := target)
        (j := j) hjLowered
      rw [if_neg (fun heq : i = j => hne heq.symm)] at hvalue
      change InductiveConstructorsClosed
        (loweredState.newTypes.set! i target)[j]
      rw [show (loweredState.newTypes.set! i target)[j] =
        loweredState.newTypes[j] by simpa [Array.set!] using hvalue]
      exact Htarget.2 j (by omega) hjLowered
    exact Except.WF.pure ⟨.step hidx Htarget.1, HnextPending⟩
  · rw [dif_neg hidx]
    exact Except.WF.pure ⟨.done (Nat.le_of_not_gt hidx),
      fun j hcursor hj => Hstate j (by omega) hj⟩

/-- Big-step relation of the dynamically growing lowering queue.  The
queue stops only once the index reaches the then-current array size; each
preceding step contains its family lowering, including any new
auxiliary families appended while processing it. -/
inductive LoweringQueue
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (lctx : LocalContext) : Nat → Nat →
      Lean4Lean.ElimNestedInductive.State →
      Lean4Lean.ElimNestedInductive.Result ×
        Lean4Lean.ElimNestedInductive.State → Prop
  | done (hbound : state.newTypes.size ≤ i) :
      LoweringQueue env params nparams lctx i (fuel + 1) state
        ({ state with
          nparams := params.size
          lctx
          params
          aux2nested := state.nestedAux.foldl
            (fun map (nested, name) => map.insert name nested) {}
          types := state.newTypes.toList }, state)
  | step :
      LowerNextStep env params nparams i state (some source, nextState) →
      LoweringQueue env params nparams lctx (i + 1) fuel nextState out →
      LoweringQueue env params nparams lctx i (fuel + 1) state out

theorem LoweringQueue.resultContext
    (H : LoweringQueue env params nparams lctx i fuel state out) :
    out.1.lctx = lctx ∧ out.1.params = params := by
  induction H with
  | done => exact ⟨rfl, rfl⟩
  | step _ _ ih => exact ih

theorem LoweringQueue.resultNParams
    (H : LoweringQueue env params nparams lctx i fuel state out) :
    out.1.nparams = params.size := by
  induction H with
  | done => rfl
  | step _ _ ih => exact ih

theorem LoweringQueue.resultAuxMap
    (H : LoweringQueue env params nparams lctx i fuel state out) :
    out.1.aux2nested = out.2.nestedAux.foldl
      (fun map (entry : Expr × Name) => map.insert entry.2 entry.1) {} := by
  induction H with
  | done => rfl
  | step _ _ ih => exact ih

theorem LoweringQueue.resultNestedAuxLE
    (H : LoweringQueue env params nparams lctx i fuel state out) :
    NestedAuxLE state out.2 := by
  induction H with
  | done => exact .refl _
  | step Hnext _ ih => exact Hnext.nestedAuxLE.trans ih

theorem LoweringQueue.resultNamesWF
    (H : LoweringQueue env params nparams lctx i fuel state out)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  induction H with
  | done => exact Hstate
  | step Hnext Htail ih => exact ih (Hnext.namesWF Hstate)

theorem LoweringQueue.resultNamesFresh
    (H : LoweringQueue env params nparams lctx i fuel state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  induction H with
  | done => exact Hstate
  | step Hnext Htail ih => exact ih (Hnext.namesFresh Hstate)

/-- Once an index lies strictly behind the queue cursor, later lowering
steps preserve the exact family stored there through to the final result. -/
theorem LoweringQueue.getElem_before
    (H : LoweringQueue env params nparams lctx i fuel state out)
    (hj : j < i) (hbound : j < state.newTypes.size) :
    out.1.types[j]? = some state.newTypes[j] := by
  induction H with
  | done =>
    simp only
    rw [List.getElem?_eq_getElem (by simpa using hbound)]
    rfl
  | step Hnext Htail ih =>
    rcases Hnext.getElem_ne hbound (by omega) with
      ⟨hnextBound, hsame⟩
    simpa [hsame] using ih (by omega) hnextBound

/-- Every not-yet-processed family within the current queue has a unique
future lowering step. The theorem returns that family lowering
and identifies its target at the same index in the final result list. -/
theorem LoweringQueue.translationAt
    (H : LoweringQueue env params nparams lctx i fuel state out)
    (hij : i ≤ j) (hj : j < state.newTypes.size) :
    ∃ stepState target loweredState,
      FamilyLowering env params nparams state.newTypes[j]
        stepState (target, loweredState) ∧
      out.1.types[j]? = some target ∧
      NestedAuxLE loweredState out.2 := by
  revert j
  induction H with
  | done hdone =>
    intro j hij hj
    omega
  | @step iStep stateStep sourceStep nextStateStep fuelStep outStep
      Hnext Htail ih =>
    intro j hij hj
    by_cases hji : j = iStep
    · subst j
      rcases Hnext.getElem_selected hj with
        ⟨target, loweredState, Htranslated, hnextAux, hiNext, htarget⟩
      refine ⟨stateStep, target, loweredState, Htranslated, ?_, ?_⟩
      have hfinal := Htail.getElem_before (j := iStep) (by omega) hiNext
      simpa [htarget] using hfinal
      rcases Htail.resultNestedAuxLE with ⟨suffix, hsuffix, hlvls⟩
      exact ⟨suffix, by simpa [hnextAux] using hsuffix,
        hlvls.trans (Hnext.nestedAuxLE.lvls.trans Htranslated.nestedAuxLE.lvls.symm)⟩
    · have hij' : iStep + 1 ≤ j := by omega
      rcases Hnext.getElem_ne hj hji with ⟨hjNext, hsame⟩
      rcases ih hij' hjNext with
        ⟨stepState, target, loweredState, Htranslated, hfinal, Haux⟩
      rw [hsame] at Htranslated
      exact ⟨stepState, target, loweredState, Htranslated, hfinal, Haux⟩

theorem LoweringQueue.resultRestorable
    (H : LoweringQueue env params nparams lctx i fuel state out)
    (Hprefix : RestorableNewTypesPrefix nparams i state) :
    ∀ type ∈ out.1.types, RestorableInductiveType nparams type := by
  induction H with
  | @done iDone fuelDone stateDone hbound =>
    intro type htype
    simp only at htype
    rcases List.mem_iff_getElem.mp htype with ⟨j, hj, rfl⟩
    apply Hprefix j
    · have hjSize : j < stateDone.newTypes.size := by simpa using hj
      omega
  | step Hnext Htail ih =>
    exact ih (Hnext.restorablePrefix Hprefix)

theorem LoweringQueue.preservesTypeName
    (H : LoweringQueue env params nparams lctx i fuel state out)
    (Hname : NewTypeNamePresent state name) :
    ∃ type ∈ out.1.types, type.name = name := by
  induction H with
  | done => simpa [NewTypeNamePresent] using Hname
  | step Hnext Htail ih => exact ih (Hnext.preservesTypeName Hname)

/-- The dynamic queue invariant used by auxiliary validation. Every pending
family has closed constructor types, so processing it preserves the cache
free-variable invariant and proves every newly appended family closed before
the cursor can reach it. -/
private theorem loweringQueueLoop_refinesClosed
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (lctx : LocalContext) (i fuel : Nat)
    (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hpending : PendingNewTypesClosed i state)
    (Hcache : NestedAuxFVarsIn P state) :
    (Lean4Lean.ElimNestedInductive.run.loop nparams lctx params i fuel
      env state).WF fun out =>
        LoweringQueue env params nparams lctx i fuel state out ∧
        NestedAuxFVarsIn P out.2 := by
  induction fuel generalizing i state with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [Lean4Lean.ElimNestedInductive.run.loop]
    refine nestedBind.WF
      (ElimNestedInductive.lowerNext.translationPending params nparams i env
        state hparams hclosures Henv Hpending) ?_
    intro next nextState Hnext
    rcases Hnext with ⟨Htranslation, HpendingNext⟩
    cases Htranslation with
    | done hbound =>
      simp only [pure]
      exact Except.WF.pure ⟨.done hbound, Hcache⟩
    | step hidx Hlowered =>
      rename_i target loweredState
      have HcacheNext : NestedAuxFVarsIn P
          { loweredState with
            newTypes := loweredState.newTypes.set! i target } := by
        have HcacheLower := Hlowered.auxFVarsIn
          (Hpending i (Nat.le_refl _) hidx) Hparams Hcache
        intro nested name hentry
        exact HcacheLower nested name hentry
      exact (ih (i := i + 1)
        (state := { loweredState with
          newTypes := loweredState.newTypes.set! i target })
        HpendingNext HcacheNext).mono fun _ Htail =>
          ⟨LoweringQueue.step (.step hidx Hlowered) Htail.1,
            Htail.2⟩

/-- End-to-end relational specification of nested lowering from the source
parameter telescope through the complete dynamic family queue. -/
structure NestedLowering
    (env : Environment) (fuel nparams : Nat) (types : List InductiveType)
    (initialState : Lean4Lean.ElimNestedInductive.State)
    (out : Lean4Lean.ElimNestedInductive.Result ×
      Lean4Lean.ElimNestedInductive.State) : Prop where
  source : ∃ first rest tail paramsState lctx params,
    types = first :: rest ∧
    LoweringParamOpening {} #[] first.type nparams
      lctx tail params ∧
    paramsState.newTypes = initialState.newTypes ∧
    paramsState.nestedAux = initialState.nestedAux ∧
    paramsState.nextIdx = initialState.nextIdx ∧
    paramsState.ngen.namePrefix = initialState.ngen.namePrefix ∧
    NestedBindingContextWF lctx paramsState.ngen ∧
    Nonempty (CDeclArray lctx params) ∧
    LoweringQueue env params nparams lctx 0 fuel
      paramsState out
  /-- The run never modifies the universe arguments `lvls` of the state. -/
  lvls : out.2.lvls = initialState.lvls

theorem NestedLowering.resultRestorable
    (H : NestedLowering env fuel nparams types initialState out) :
    ∀ type ∈ out.1.types, RestorableInductiveType nparams type := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, _, _, _, _, _, Hqueue⟩
  exact Hqueue.resultRestorable (.zero paramsState)

theorem NestedLowering.resultNParams
    (H : NestedLowering env fuel nparams types initialState out) :
    out.1.nparams = nparams := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, Hopening, _, _, _, _, _, _, Hqueue⟩
  exact Hqueue.resultNParams.trans Hopening.initial_size

theorem NestedLowering.resultParamsSize
    (H : NestedLowering env fuel nparams types initialState out) :
    out.1.params.size = nparams := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, Hopening, _, _, _, _, _, _, Hqueue⟩
  rw [Hqueue.resultContext.2]
  exact Hopening.initial_size

/-- The final restoration context is exactly the source parameter selection
opened before the dynamic lowering queue starts. -/
theorem NestedLowering.resultContextSelection
    (H : NestedLowering env fuel nparams types initialState out) :
    Nonempty (CDeclArray out.1.lctx out.1.params) := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, _, _,
      _hprefix, _Hctx, Hselection, Hqueue⟩
  rcases Hqueue.resultContext with ⟨hlctx, hparams⟩
  rw [hlctx, hparams]
  exact Hselection

theorem NestedLowering.resultContextWF
    (H : NestedLowering env fuel nparams types initialState out) :
    out.1.lctx.WF := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, _, _, _hprefix, Hctx,
      _Hselection, Hqueue⟩
  rw [Hqueue.resultContext.1]
  exact Hctx.wf

/-- Every restoration-context free variable was allocated by nested
lowering's own generator, whose prefix is disjoint from the type checker's
private generator. -/
theorem NestedLowering.resultContextKernelFresh
    (H : NestedLowering env fuel nparams types initialState out)
    (hprefix : initialState.ngen.namePrefix = `_nested_fresh) :
    ∀ fv ∈ out.1.lctx.fvars,
      ({} : TypeChecker.State).ngen.Reserves fv := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _htypes, _Hopening,
      _hnewTypes, _hnestedAux, _hnextIdx, hparamsPrefix, Hctx,
      _Hselection, Hqueue⟩
  rw [Hqueue.resultContext.1]
  exact Hctx.kernelFreshOfPrefix (hparamsPrefix.trans hprefix)

/-- Lowering stores common parameters in source binder order, whereas its
local context (and therefore every `MLCtx.vlctx`) stores free variables in
most-recent-first order. -/
theorem NestedLowering.resultParams_reverse_fvars
    (H : NestedLowering env fuel nparams types initialState out) :
    out.1.params.toList.reverse = out.1.lctx.fvars.map Expr.fvar := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _htypes, Hopening,
      _hnewTypes, _hnestedAux, _hnextIdx, _hprefix, _Hctx, _Hselection, Hqueue⟩
  rcases Hqueue.resultContext with ⟨hlctx, hparams⟩
  rw [hlctx, hparams]
  exact Hopening.toParamOpening.root_params_reverse_fvars

theorem NestedLowering.resultAuxMap
    (H : NestedLowering env fuel nparams types initialState out) :
    out.1.aux2nested = out.2.nestedAux.foldl
      (fun map (entry : Expr × Name) => map.insert entry.2 entry.1) {} := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, _, _, _, _, _, Hqueue⟩
  exact Hqueue.resultAuxMap

theorem NestedLowering.resultAuxFVarsIn
    (H : NestedLowering env fuel nparams types initialState out)
    (Hcache : NestedAuxFVarsIn P out.2) :
    NestedAuxMapFVarsIn P
      (show Std.TreeMap Name Expr Name.quickCmp from out.1.aux2nested) := by
  rw [H.resultAuxMap]
  change NestedAuxMapFVarsIn P
    (out.2.nestedAux.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1) {})
  rw [← Array.foldl_toList]
  apply nestedAuxFold_fvarsIn out.2.nestedAux.toList
  · intro entry hentry
    exact Hcache entry.1 entry.2 (by simpa using hentry)
  · unfold NestedAuxMapFVarsIn
    intro name nested hfind
    simp at hfind

theorem NestedLowering.resultAuxNamesReserved
    (H : NestedLowering env fuel nparams types initialState
      (result, finalState))
    (Hnames : NestedAuxNamesWF finalState) :
    NestedAuxMapNamesReserved
      (show Std.TreeMap Name Expr Name.quickCmp from result.aux2nested) := by
  rw [H.resultAuxMap]
  change NestedAuxMapNamesReserved
    (finalState.nestedAux.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1) {})
  rw [← Array.foldl_toList]
  apply nestedAuxFold_namesReserved finalState.nestedAux.toList
  · intro entry hentry
    exact Hnames.reserved entry.1 entry.2 (by simpa using hentry)
  · intro name nested hfind
    simp at hfind

theorem NestedLowering.resultAuxNamesFresh
    (H : NestedLowering env fuel nparams types initialState
      (result, finalState))
    (Hnames : NestedAuxNamesFresh env finalState) :
    NestedAuxMapNamesFresh env
      (show Std.TreeMap Name Expr Name.quickCmp from result.aux2nested) := by
  rw [H.resultAuxMap]
  change NestedAuxMapNamesFresh env
    (finalState.nestedAux.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1) {})
  rw [← Array.foldl_toList]
  apply nestedAuxFold_namesFresh finalState.nestedAux.toList
  · intro entry hentry
    exact Hnames entry.1 entry.2 (by simpa using hentry)
  · intro name nested hfind
    simp at hfind

/-- Under the separately stated fresh-name invariant, every final cache entry
is retrieved exactly by the executable `aux2nested` map. -/
theorem NestedLowering.resultAuxLookup
    (H : NestedLowering env fuel nparams types initialState
      (result, finalState))
    (hnodup : (finalState.nestedAux.toList.map Prod.snd).Nodup)
    (hentry : (nested, name) ∈ finalState.nestedAux) :
    result.aux2nested.find? name = some nested := by
  rw [H.resultAuxMap]
  change (finalState.nestedAux.foldl
    (fun (map : Std.TreeMap Name Expr Name.quickCmp)
      (entry : Expr × Name) => map.insert entry.2 entry.1)
    {})[name]? = some nested
  rw [← Array.foldl_toList]
  exact nestedAuxFold_find finalState.nestedAux.toList {} hnodup
    (by simpa using hentry)

theorem NestedLowering.resultAuxMapModels
    (H : NestedLowering env fuel nparams types initialState
      (result, finalState))
    (hnodup : (finalState.nestedAux.toList.map Prod.snd).Nodup) :
    NestedAuxMapModels result finalState := by
  intro nested name hentry
  exact H.resultAuxLookup hnodup hentry

theorem NestedLowering.resultNamesWF
    (H : NestedLowering env fuel nparams types initialState out)
    (Hstate : NestedAuxNamesWF initialState) : NestedAuxNamesWF out.2 := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, hinitialAux,
      hinitialNext, _hprefix, _Hctx, _Hselection, Hqueue⟩
  exact Hqueue.resultNamesWF
    (Hstate.ofCacheCounterEq hinitialAux hinitialNext)

theorem NestedLowering.resultNamesFresh
    (H : NestedLowering env fuel nparams types initialState out)
    (Hstate : NestedAuxNamesFresh env initialState) :
    NestedAuxNamesFresh env out.2 := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, hinitialAux,
      _hinitialNext, _hprefix, _Hctx, _Hselection, Hqueue⟩
  exact Hqueue.resultNamesFresh (Hstate.ofCacheEq hinitialAux)

theorem NestedLowering.resultFamilyNamesFreshOfEmpty
    (H : NestedLowering env fuel nparams types initialState
      (result, finalState))
    (hwf : env.constants.WF)
    (hempty : initialState.nestedAux = #[]) :
    RestoreAuxFamiliesFresh result env := by
  have Hnames := H.resultNamesFresh
    (NestedAuxNamesFresh.empty env initialState hempty)
  have Hmap := H.resultAuxNamesFresh Hnames
  intro name nested hfind
  exact find?_none_of_contains_false hwf (Hmap name nested hfind)


theorem NestedLowering.resultNamesNodupOfEmpty
    (H : NestedLowering env fuel nparams types initialState out)
    (hempty : initialState.nestedAux = #[]) :
    (out.2.nestedAux.toList.map Prod.snd).Nodup :=
  (H.resultNamesWF (NestedAuxNamesWF.empty initialState hempty)).nodup

theorem NestedLowering.resultFamilyNamesReservedOfEmpty
    (H : NestedLowering env fuel nparams types initialState
      (result, finalState))
    (hempty : initialState.nestedAux = #[]) :
    NestedAuxMapNamesReserved
      (show Std.TreeMap Name Expr Name.quickCmp from result.aux2nested) :=
  H.resultAuxNamesReserved
    (H.resultNamesWF (NestedAuxNamesWF.empty initialState hempty))

theorem NestedLowering.resultFamilyNamesReservedFresh
    (H : NestedLowering env fuel nparams types initialState
      (result, finalState))
    (hempty : initialState.nestedAux = #[]) :
    NestedAuxMapNamesReserved
      (show Std.TreeMap Name Expr Name.quickCmp from result.aux2nested) :=
  H.resultFamilyNamesReservedOfEmpty hempty

theorem NestedLowering.resultAuxMapModelsOfEmpty
    (H : NestedLowering env fuel nparams types initialState
      (result, finalState))
    (hempty : initialState.nestedAux = #[]) :
    NestedAuxMapModels result finalState :=
  H.resultAuxMapModels (H.resultNamesNodupOfEmpty hempty)

theorem NestedLowering.resultAuxMapModelsFresh
    (H : NestedLowering env fuel nparams types initialState
      (result, finalState))
    (hempty : initialState.nestedAux = #[]) :
    NestedAuxMapModels result finalState :=
  H.resultAuxMapModelsOfEmpty hempty

/-- Positional lowering step for any family present in the initial queue.
Unlike name preservation, this exposes the complete constructor-expression
translation performed at that family's actual dynamic queue step. -/
theorem NestedLowering.translationAtInitial
    (H : NestedLowering env fuel nparams types initialState out)
    (hj : j < initialState.newTypes.size) :
    ∃ params stepState target loweredState,
      params.size = nparams ∧
      FamilyLowering env params nparams
        initialState.newTypes[j] stepState (target, loweredState) ∧
      out.1.types[j]? = some target ∧
      NestedAuxLE loweredState out.2 := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _htypes, Hopening,
      hinitial, _hinitialAux, _hinitialNext, _hprefix, _Hctx, _Hselection, Hqueue⟩
  have hjParams : j < paramsState.newTypes.size := by
    simpa [hinitial] using hj
  rcases Hqueue.translationAt (Nat.zero_le j) hjParams with
    ⟨stepState, target, loweredState, Htranslated, htarget, Haux⟩
  have hvalue : paramsState.newTypes[j] = initialState.newTypes[j] := by
    have heq := congrArg
      (fun xs : Array InductiveType => xs[j]!) hinitial
    simpa [Array.getElem!_eq_getD, Array.getD, hjParams, hj] using heq
  rw [hvalue] at Htranslated
  exact ⟨params, stepState, target, loweredState,
    Hopening.initial_size, Htranslated, htarget, Haux⟩

/-- Once final cache-name uniqueness is supplied, every initially declared
family has a positional lowering certificate whose constructor bodies are
all interpreted by the actual final restoration map. -/
theorem NestedLowering.resolvedMappingAtInitial
    (H : NestedLowering env fuel nparams types initialState
      (result, finalState))
    (hauxNames : (finalState.nestedAux.toList.map Prod.snd).Nodup)
    (hj : j < initialState.newTypes.size) :
    ∃ params stepState target loweredState,
      params.size = nparams ∧
      FamilyLowering.Resolved env params nparams result
        initialState.newTypes[j] stepState (target, loweredState) ∧
      result.types[j]? = some target := by
  rcases H.translationAtInitial hj with
    ⟨params, stepState, target, loweredState, hparams, Htranslated,
      htarget, Hlater⟩
  exact ⟨params, stepState, target, loweredState, hparams,
    Htranslated.resolvedMapping Hlater (H.resultAuxMapModels hauxNames), htarget⟩

/-- Parameter-aligned form of `resolvedMappingAtInitial`.  The expression
mapping for each source family is performed with exactly the parameter array
stored in the final restoration record, rather than merely with an array of
the same size.  This identity is what later lets restoration cancel the
abstraction performed when a nested application was cached. -/
theorem NestedLowering.resolvedMappingAtInitialAligned
    (H : NestedLowering env fuel nparams types initialState
      (result, finalState))
    (hauxNames : (finalState.nestedAux.toList.map Prod.snd).Nodup)
    (hj : j < initialState.newTypes.size) :
    ∃ params stepState target loweredState,
      result.params = params ∧
      params.size = nparams ∧
      FamilyLowering.Resolved env params nparams result
        initialState.newTypes[j] stepState (target, loweredState) ∧
      result.types[j]? = some target := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _htypes, Hopening,
      hinitial, _hinitialAux, _hinitialNext, _hprefix, _Hctx, _Hselection, Hqueue⟩
  have hjParams : j < paramsState.newTypes.size := by
    simpa [hinitial] using hj
  rcases Hqueue.translationAt (Nat.zero_le j) hjParams with
    ⟨stepState, target, loweredState, Htranslated, htarget, Hlater⟩
  have hvalue : paramsState.newTypes[j] = initialState.newTypes[j] := by
    have heq := congrArg
      (fun xs : Array InductiveType => xs[j]!) hinitial
    simpa [Array.getElem!_eq_getD, Array.getD, hjParams, hj] using heq
  rw [hvalue] at Htranslated
  exact ⟨params, stepState, target, loweredState,
    Hqueue.resultContext.2, Hopening.initial_size,
    Htranslated.resolvedMapping Hlater (H.resultAuxMapModels hauxNames), htarget⟩

/-- `resolvedMappingAtInitialAligned`, additionally recording that the lowering
step of the family starts from the universe arguments of the initial state. -/
theorem NestedLowering.resolvedMappingAtInitialAlignedLvls
    (H : NestedLowering env fuel nparams types initialState
      (result, finalState))
    (hauxNames : (finalState.nestedAux.toList.map Prod.snd).Nodup)
    (hj : j < initialState.newTypes.size) :
    ∃ params stepState target loweredState,
      result.params = params ∧
      params.size = nparams ∧
      FamilyLowering.Resolved env params nparams result
        initialState.newTypes[j] stepState (target, loweredState) ∧
      result.types[j]? = some target ∧
      stepState.lvls = initialState.lvls := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _htypes, Hopening,
      hinitial, _hinitialAux, _hinitialNext, _hprefix, _Hctx, _Hselection, Hqueue⟩
  have hjParams : j < paramsState.newTypes.size := by
    simpa [hinitial] using hj
  rcases Hqueue.translationAt (Nat.zero_le j) hjParams with
    ⟨stepState, target, loweredState, Htranslated, htarget, Hlater⟩
  have hvalue : paramsState.newTypes[j] = initialState.newTypes[j] := by
    have heq := congrArg
      (fun xs : Array InductiveType => xs[j]!) hinitial
    simpa [Array.getElem!_eq_getD, Array.getD, hjParams, hj] using heq
  rw [hvalue] at Htranslated
  exact ⟨params, stepState, target, loweredState,
    Hqueue.resultContext.2, Hopening.initial_size,
    Htranslated.resolvedMapping Hlater (H.resultAuxMapModels hauxNames), htarget,
    (Htranslated.nestedAuxLE.lvls.symm.trans Hlater.lvls.symm).trans H.lvls⟩

theorem NestedLowering.preservesInitialTypeName
    (H : NestedLowering env fuel nparams types initialState out)
    (Hname : NewTypeNamePresent initialState name) :
    ∃ type ∈ out.1.types, type.name = name := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, hnewTypes,
      _hnewAux, _hnextIdx, _hprefix, _Hctx, _Hselection, Hqueue⟩
  apply Hqueue.preservesTypeName
  unfold NewTypeNamePresent at Hname ⊢
  rwa [hnewTypes]

/-- The final restoration parameter array is an ordered array of distinct
free variables. -/
def NestedResultParamsNodup
    (result : Lean4Lean.ElimNestedInductive.Result) : Prop :=
  ∃ fvars : List FVarId,
    result.params = (fvars.map Expr.fvar).toArray ∧ fvars.Nodup

/-- End-to-end queue safety from the executable source checks.  This closes
the dynamic-generation loop: source constructors are closed, every generated
auxiliary constructor is re-closed over the verified parameter context, and
therefore every cached nested application is open only over the retained result
context. -/
theorem ElimNestedInductive.run.translationClosed
    (fuel nparams : Nat) (types : List InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hsources : SourceSyntaxChecked types)
    (hinitial : state.newTypes = types.toArray)
    (hempty : state.nestedAux = #[]) :
    (Lean4Lean.ElimNestedInductive.run fuel nparams types env state).WF
      fun out =>
        NestedLowering env fuel nparams types state out ∧
        NestedAuxFVarsIn (· ∈ out.1.lctx.fvars) out.2 ∧
        NestedResultParamsNodup out.1 := by
  cases types with
  | nil => exact Except.WF.throw
  | cons first rest =>
    unfold Lean4Lean.ElimNestedInductive.run
    apply ElimNestedInductive.withParams.refinesClosing
      (Htype := Hsources.typeClosed (by simp))
    intro lctx tail params paramsState Hopening Hclosing Htail hnewTypes
      hnestedAux hnextIdx hprefix hlvls
    have hparams : params.size = nparams := Hopening.initial_size
    have Hparams : ∀ param ∈ params,
        param.FVarsIn (· ∈ lctx.fvars) :=
      Hclosing.selection.fvarsIn Hclosing.binding.wf
    have Hpending : PendingNewTypesClosed 0 paramsState := by
      intro j _hj hj
      have hjState : j < state.newTypes.size := by
        simpa [hnewTypes] using hj
      have hvalue : paramsState.newTypes[j] = state.newTypes[j] := by
        have heq := congrArg
          (fun xs : Array InductiveType => xs[j]!) hnewTypes
        simpa [Array.getElem!_eq_getD, Array.getD, hj, hjState] using heq
      rw [hvalue]
      have hmember : state.newTypes[j] ∈ first :: rest := by
        have hmemState : state.newTypes[j] ∈ state.newTypes :=
          Array.getElem_mem hjState
        simp [hinitial]
      exact Hsources.constructorsClosed hmember
    have Hcache : NestedAuxFVarsIn (· ∈ lctx.fvars) paramsState := by
      intro nested name hentry
      rw [hnestedAux, hempty] at hentry
      simp at hentry
    exact (loweringQueueLoop_refinesClosed env params nparams lctx 0 fuel
      paramsState hparams hclosures Henv Hparams Hpending Hcache).mono
        fun _ Hqueue => by
          refine ⟨⟨⟨first, rest, tail, paramsState, lctx, params,
            rfl, Hopening, hnewTypes, hnestedAux, hnextIdx,
            hprefix, Hclosing.binding, ⟨Hclosing.selection⟩, Hqueue.1⟩,
            Hqueue.1.resultNestedAuxLE.lvls.trans hlvls⟩, ?_, ?_⟩
          · rw [Hqueue.1.resultContext.1]
            exact Hqueue.2
          · exact ⟨Hclosing.selection.fvars,
              Hqueue.1.resultContext.2.trans Hclosing.selection.expressions,
              Hclosing.nodup⟩

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

end VerifyInductive
end Lean4Lean
