import Lean4Lean.Verify.Inductive.Nested.Lowering.Queue

/-! The lowering run as a relation on its result (`NestedLoweringRun`, the source branch's
`NestedLoweringRun`, renamed because `NestedLoweringRun` is the interface structure of
`Verify/Inductive/Lowering.lean`), its closed form `NestedLoweringOutputClosed` (the final cache
mentions only the returned parameters, which are distinct free variables), and the syntactic
consequences the restoration side reads. From the source branch's
`Nested/Restoration/SourceTranslations.lean`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- The result of the lowering run, as returned through the `StateT.run'` used
by `Environment.addInductive`. -/
def NestedLoweringRun
    (env : Environment) (fuel nparams : Nat) (types : List InductiveType)
    (initialState : Lean4Lean.ElimNestedInductive.State)
    (result : Lean4Lean.ElimNestedInductive.Result) : Prop :=
  ∃ finalState, NestedLowering env fuel nparams types initialState
    (result, finalState)

/-- Lowering result whose final cache mentions only free variables of the local
context returned in the executable restoration record, and whose parameters are
duplicate-free. -/
def NestedLoweringOutputClosed
    (env : Environment) (fuel nparams : Nat) (types : List InductiveType)
    (initialState : Lean4Lean.ElimNestedInductive.State)
    (result : Lean4Lean.ElimNestedInductive.Result) : Prop :=
  ∃ finalState,
    NestedLowering env fuel nparams types initialState
      (result, finalState) ∧
    NestedAuxFVarsIn (· ∈ result.lctx.fvars) finalState ∧
    NestedResultParamsNodup result

theorem NestedLoweringOutputClosed.toResult
    (H : NestedLoweringOutputClosed env fuel nparams types initialState result) :
    NestedLoweringRun env fuel nparams types initialState result := by
  rcases H with ⟨finalState, Hrun, _Hcache, _Hparams⟩
  exact ⟨finalState, Hrun⟩

/-- An `AuxiliaryFamilySpecialization` selects exactly the validated auxiliary
translation associated with its cache entry. -/
theorem NestedLoweringOutputClosed.resultParamsNodup
    (H : NestedLoweringOutputClosed env fuel nparams types initialState result) :
    NestedResultParamsNodup result := by
  rcases H with ⟨_finalState, _Hrun, _Hcache, Hparams⟩
  exact Hparams

theorem NestedLoweringOutputClosed.selectionNodup
    (H : NestedLoweringOutputClosed env fuel nparams types initialState result)
    (selection : CDeclArray result.lctx result.params) :
    selection.fvars.Nodup := by
  rcases H.resultParamsNodup with ⟨fvars, hparams, hnodup⟩
  have harrays : (selection.fvars.map Expr.fvar).toArray =
      (fvars.map Expr.fvar).toArray := by
    rw [← selection.expressions, ← hparams]
  have hlists : selection.fvars.map Expr.fvar =
      fvars.map Expr.fvar := by
    simpa using congrArg Array.toList harrays
  have heq : selection.fvars = fvars :=
    (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hlists
  rw [heq]
  exact hnodup

theorem NestedLoweringOutputClosed.resultParamsSize
    (H : NestedLoweringOutputClosed env fuel nparams types initialState result) :
    result.params.size = result.nparams := by
  rcases H with ⟨_finalState, Hrun, _Hcache, _Hparams⟩
  exact Hrun.resultParamsSize.trans Hrun.resultNParams.symm

/-- The final lowering parameter selection closes the same raw source-header
prefix with any residual body. This is the syntactic part, before the abstract
header normalization; it does not compare lowering's raw domains with the
checker's unannotated domains. -/
theorem NestedLoweringOutputClosed.sourceParameterPrefix
    (H : NestedLoweringOutputClosed env fuel nparams types initialState result)
    (Hclosed : ∀ source ∈ types,
      source.type.FVarsIn fun _ => False)
    (HbClosed : ∀ source ∈ types, Closed source.type)
    (body : Expr) :
    ∃ first rest residual,
      types = first :: rest ∧
      Expr.ForallTelescope first.type nparams residual ∧
      Expr.SameForallPrefix nparams
        (result.lctx.mkForall result.params body) first.type := by
  rcases H with ⟨finalState, Hrun, Hcache, Hparams⟩
  have Hwhole : NestedLoweringOutputClosed env fuel nparams types
      initialState result := ⟨finalState, Hrun, Hcache, Hparams⟩
  rcases Hrun.source with
    ⟨first, rest, tail, paramsState, lctx, params, htypes, Hopening,
      _hnewTypes, _hnestedAux, _hnextIdx, _hprefix, Hctx, Hselection, Hqueue⟩
  rcases Hselection with ⟨Hselection⟩
  rcases Hopening.forallTelescope with ⟨residual, Htelescope⟩
  have hsourceClosed : first.type.FVarsIn fun _ => False :=
    Hclosed first (by rw [htypes]; simp)
  have hclosed := Hopening.toParamOpening.root_mkForall_tail Hctx.wf
    Htelescope (FVarsIn_to_FVarIdsIn hsourceClosed)
    (HbClosed first (by rw [htypes]; simp))
  have HselectionResult : CDeclArray result.lctx result.params := by
    rcases Hqueue.resultContext with ⟨hlctx, hparams⟩
    rw [hlctx, hparams]
    exact Hselection
  have Hsame := HselectionResult.sameForallPrefix
    (Hwhole.selectionNodup HselectionResult) body tail
  have hclosedResult : result.lctx.mkForall result.params tail =
      first.type := by
    rcases Hqueue.resultContext with ⟨hlctx, hparams⟩
    rw [hlctx, hparams]
    exact hclosed
  rw [Hrun.resultParamsSize, hclosedResult] at Hsame
  exact ⟨first, rest, residual, htypes, Htelescope, Hsame⟩
theorem NestedLoweringRun.resultRestorable
    (H : NestedLoweringRun env fuel nparams types initialState result) :
    ∀ type ∈ result.types, RestorableInductiveType nparams type := by
  rcases H with ⟨finalState, Hrun⟩
  exact Hrun.resultRestorable

theorem NestedLoweringRun.resultNParams
    (H : NestedLoweringRun env fuel nparams types initialState result) :
    result.nparams = nparams := by
  rcases H with ⟨finalState, Hrun⟩
  exact Hrun.resultNParams

theorem NestedLoweringRun.sourceTranslationAt
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringRun env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hj : j < sourceTypes.length) :
    ∃ params stepState target loweredState,
      params.size = nparams ∧
      FamilyLowering env params nparams sourceTypes[j]
        stepState (target, loweredState) ∧
      result.types[j]? = some target ∧
      ∃ finalState,
        NestedLowering env fuel nparams sourceTypes
          { initialState with newTypes := sourceTypes.toArray }
          (result, finalState) ∧
        NestedAuxLE loweredState finalState := by
  rcases H with ⟨finalState, Hrun⟩
  have hjInitial : j <
      ({ initialState with
        newTypes := sourceTypes.toArray }).newTypes.size := by
    simpa using hj
  rcases Hrun.translationAtInitial hjInitial with
    ⟨params, stepState, target, loweredState, hparams, Htranslated,
      htarget, Haux⟩
  exact ⟨params, stepState, target, loweredState, hparams,
    by simpa using Htranslated, htarget, finalState, Hrun, Haux⟩

/-- Source-family mapping of the lowering run, under the premise that the
auxiliary names of the final cache are distinct (discharged for an empty initial
cache by `sourceResolvedMappingAtOfEmpty`). -/
theorem NestedLoweringRun.sourceResolvedMappingAt
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringRun env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hj : j < sourceTypes.length) :
    ∃ finalState,
      NestedLowering env fuel nparams sourceTypes
        { initialState with newTypes := sourceTypes.toArray }
        (result, finalState) ∧
      ((finalState.nestedAux.toList.map Prod.snd).Nodup →
        ∃ params stepState target loweredState,
          params.size = nparams ∧
          FamilyLowering.Resolved env params nparams result sourceTypes[j]
            stepState (target, loweredState) ∧
          result.types[j]? = some target) := by
  rcases H with ⟨finalState, Hrun⟩
  refine ⟨finalState, Hrun, ?_⟩
  intro hauxNames
  have hjInitial : j <
      ({ initialState with
        newTypes := sourceTypes.toArray }).newTypes.size := by
    simpa using hj
  rcases Hrun.resolvedMappingAtInitial hauxNames hjInitial with
    ⟨params, stepState, target, loweredState, hparams, Hmapped, htarget⟩
  exact ⟨params, stepState, target, loweredState, hparams,
    by simpa using Hmapped, htarget⟩

/-- The source-family mapping with cache uniqueness discharged from an empty
initial cache. -/
theorem NestedLoweringRun.sourceResolvedMappingAtOfEmpty
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringRun env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[])
    (hj : j < sourceTypes.length) :
    ∃ params stepState target loweredState,
      params.size = nparams ∧
      FamilyLowering.Resolved env params nparams result sourceTypes[j]
        stepState (target, loweredState) ∧
      result.types[j]? = some target := by
  rcases H.sourceResolvedMappingAt hj with ⟨finalState, Hrun, Hmapped⟩
  apply Hmapped
  apply Hrun.resultNamesNodupOfEmpty
  simpa using hempty

theorem NestedLoweringRun.sourceResolvedMappingAtFresh
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringRun env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[])
    (hj : j < sourceTypes.length) :
    ∃ params stepState target loweredState,
      params.size = nparams ∧
      FamilyLowering.Resolved env params nparams result sourceTypes[j]
        stepState (target, loweredState) ∧
      result.types[j]? = some target :=
  H.sourceResolvedMappingAtOfEmpty hempty hj

/-- Fresh-cache source mapping with the lowering parameters identified with
the parameters recorded in the executable restoration record. -/
theorem NestedLoweringRun.sourceResolvedMappingAtFreshAligned
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringRun env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[])
    (hj : j < sourceTypes.length) :
    ∃ params stepState target loweredState,
      result.params = params ∧
      params.size = nparams ∧
      FamilyLowering.Resolved env params nparams result sourceTypes[j]
        stepState (target, loweredState) ∧
      result.types[j]? = some target := by
  rcases H with ⟨finalState, Hrun⟩
  have hjInitial : j <
      ({ initialState with
        newTypes := sourceTypes.toArray }).newTypes.size := by
    simpa using hj
  apply Hrun.resolvedMappingAtInitialAligned _ hjInitial
  apply Hrun.resultNamesNodupOfEmpty
  simpa using hempty

/-- Every source family retains its positional slot in the expanded
lowering result, so the source mutual block is no longer than that result. -/
theorem NestedLoweringRun.sourceTypes_length_le
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringRun env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result) :
    sourceTypes.length ≤ result.types.length := by
  by_contra hle
  have hj : result.types.length < sourceTypes.length := Nat.lt_of_not_ge hle
  rcases H.sourceTranslationAt (j := result.types.length) hj with
    ⟨_params, _stepState, _target, _loweredState, _hparams, _Htranslation,
      htarget, _finalState, _Hrun, _Haux⟩
  exact (Nat.lt_irrefl result.types.length)
    (_root_.getElem?_eq_some_iff.mp htarget).1

/-- Lowering preserves the constructor count of every source family and
only appends auxiliary families.  Consequently the source constructor batch
is a cardinality prefix of the expanded lowered batch. -/
theorem NestedLoweringRun.sourceOwnedConstructors_length_le
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringRun env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[]) :
    (Lean4Lean.VerifyInductive.ownedConstructors sourceTypes).length ≤
      (Lean4Lean.VerifyInductive.ownedConstructors result.types).length := by
  have htypes := H.sourceTypes_length_le
  have hprefix :
      (result.types.take sourceTypes.length).map
          (fun type => type.ctors.length) =
        sourceTypes.map (fun type => type.ctors.length) := by
    apply List.ext_getElem
    · simp [List.length_take, htypes]
    · intro i hresult hsource
      rw [List.getElem_map, List.getElem_take, List.getElem_map]
      rcases H.sourceResolvedMappingAtFresh hempty (j := i) (by simpa using hsource)
          with ⟨_params, _stepState, target, _loweredState, _hparams,
            Hmapping, htarget⟩
      obtain ⟨hiResult, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp htarget
      rw [htargetEq]
      exact Hmapping.constructors.length
  have hsplit := congrArg
    (fun types : List InductiveType =>
      (types.map (fun type => type.ctors.length)).sum)
    (List.take_append_drop sourceTypes.length result.types)
  simp only [List.map_append, List.sum_append] at hsplit
  rw [hprefix] at hsplit
  simp only [Lean4Lean.VerifyInductive.ownedConstructors,
    List.length_flatMap, List.length_map]
  omega

/-- Closed-lowering specialization of the aligned source mapping. It gives the
final parameter array as distinct free variables, as needed by
abstraction/instantiation cancellation. -/
theorem NestedLoweringOutputClosed.sourceResolvedMappingAtFreshAligned
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[])
    (hj : j < sourceTypes.length) :
    ∃ fvars : List FVarId, ∃ stepState target loweredState,
      result.params = (fvars.map Expr.fvar).toArray ∧
      fvars.Nodup ∧
      result.params.size = nparams ∧
      FamilyLowering.Resolved env result.params nparams result sourceTypes[j]
        stepState (target, loweredState) ∧
      result.types[j]? = some target := by
  rcases H.resultParamsNodup with ⟨fvars, hresultParams, hnodup⟩
  rcases H.toResult.sourceResolvedMappingAtFreshAligned hempty hj with
    ⟨params, stepState, target, loweredState, hparams, hsize,
      Hmapping, htarget⟩
  rw [← hparams] at Hmapping
  exact ⟨fvars, stepState, target, loweredState, hresultParams, hnodup,
    by simpa [hparams] using hsize, Hmapping, htarget⟩

/-- Source family headers need no restoration: lowering preserves them
verbatim, so the positional translation proved for the lowered block is
already the checked translation of the corresponding source header. The list
position is the one fixed by lowering; the owner is not recovered by name. -/

theorem NestedLoweringRun.sourceTypeName
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringRun env fuel nparams types
      { initialState with newTypes := types.toArray } result)
    (hsource : source ∈ types) :
    ∃ lowered ∈ result.types, lowered.name = source.name := by
  rcases H with ⟨finalState, Hrun⟩
  apply Hrun.preservesInitialTypeName
  exact ⟨source, by simpa using hsource, rfl⟩

theorem ElimNestedInductive.run'.translationClosed
    (fuel nparams : Nat) (types : List InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hsources : SourceSyntaxChecked types)
    (hinitial : state.newTypes = types.toArray)
    (hempty : state.nestedAux = #[]) :
    ((Lean4Lean.ElimNestedInductive.run fuel nparams types env).run'
      state).WF (NestedLoweringOutputClosed env fuel nparams types state) := by
  have Hrun := ElimNestedInductive.run.translationClosed fuel nparams types env
    state hclosures Henv Hsources hinitial hempty
  have Hprojected := Hrun.map fun out Hout =>
    show NestedLoweringOutputClosed env fuel nparams types state out.1 from
      ⟨out.2, Hout.1, Hout.2.1, Hout.2.2⟩
  simpa [StateT.run'] using Hprojected

/-- A successful lowering run necessarily began with a nonempty mutual
source block; this is fixed by the executable's first pattern match. -/
theorem NestedLoweringRun.sourceNonempty
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringRun env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result) :
    sourceTypes ≠ [] := by
  rcases H with ⟨_finalState, Hrun⟩
  rcases Hrun.source with
    ⟨first, rest, _tail, _paramsState, _lctx, _params, hsource, _⟩
  rw [hsource]
  simp

/-- The lowered declaration passed to `AddInductive.run` is nonempty whenever
the exact lowering execution succeeded. -/
theorem NestedLoweringRun.resultTypesSizePos
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringRun env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result) :
    0 < result.types.toArray.size := by
  have hsource := H.sourceNonempty
  have hsourcePos : 0 < sourceTypes.length := by
    cases sourceTypes with
    | nil => contradiction
    | cons => simp
  have hresultPos : 0 < result.types.length := by
    have hle := H.sourceTypes_length_le
    omega
  simpa using hresultPos


end VerifyInductive
end Lean4Lean
