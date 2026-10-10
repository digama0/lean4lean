import Lean4Lean.Verify.Inductive.Nested.Lowering.Output

/-! A lowering run that introduces no auxiliary family returns the source block literally
(from the source branch's `Install/OrdinaryExtension.lean`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

private theorem Constructor.eq_of_name_type {left right : Constructor}
    (hname : left.name = right.name) (htype : left.type = right.type) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem InductiveType.eq_of_fields {left right : InductiveType}
    (hname : left.name = right.name) (htype : left.type = right.type)
    (hctors : left.ctors = right.ctors) : left = right := by
  cases left
  cases right
  simp_all

/-- A zero-sized restoration map has no successful lookup, so on the ordinary
branch no lowering step replaces a nested occurrence. -/
theorem ElimNestedInductive.Result.auxFind?_eq_none_of_size_eq_zero
    {result : ElimNestedInductive.Result}
    (hsize : result.aux2nested.size = 0) (name : Name) :
    (show Std.TreeMap Name Expr Name.quickCmp from
      result.aux2nested)[name]? = none := by
  let map : Std.TreeMap Name Expr Name.quickCmp := result.aux2nested
  have hempty : map.isEmpty = true := by
    rw [Std.TreeMap.isEmpty_eq_size_eq_zero, hsize]
    rfl
  apply Std.TreeMap.getElem?_eq_none_of_contains_eq_false
  exact Std.TreeMap.contains_of_isEmpty hempty

/-- If the restoration map of the lowering result is empty, the
expression-lowering derivation contains no nested occurrence.  Every
remaining constructor is a structural identity and does not change the
lowering state. -/
theorem ExprLowering.Resolved.eq_of_aux2nested_size_eq_zero
    (H : ExprLowering.Resolved env lctx params As result input state out)
    (hsize : result.aux2nested.size = 0) :
    out = (input, state) := by
  induction H with
  | occurrence Hhit =>
      rcases Hhit.mapping with
        ⟨_value, _targetName, _levels, auxName, _auxLevels, nested,
          _Hcandidate, _hauxLevels, _hhead, _hlowered, _hnested, hlookup⟩
      change (show Std.TreeMap Name Expr Name.quickCmp from
        result.aux2nested)[auxName]? = some nested at hlookup
      rw [ElimNestedInductive.Result.auxFind?_eq_none_of_size_eq_zero
        hsize auxName] at hlookup
      contradiction
  | bvar | fvar | mvar | sort | const | lit => rfl
  | app _ _ _ ihFn ihArg =>
      cases ihFn
      cases ihArg
      rfl
  | lam _ _ _ ihDom ihBody =>
      cases ihDom
      cases ihBody
      rfl
  | forallE _ _ _ ihDom ihBody =>
      cases ihDom
      cases ihBody
      rfl
  | letE _ _ _ _ ihType ihValue ihBody =>
      cases ihType
      cases ihValue
      cases ihBody
      rfl
  | mdata _ _ ihBody =>
      cases ihBody
      rfl
  | proj _ _ ihBody =>
      cases ihBody
      rfl

/-- With no final auxiliary family to interpret, constructor lowering only
opens and recloses the source parameter telescope.  Closed source syntax
makes that round trip literal, not merely alpha-equivalent. -/
theorem ConstructorLowering.Resolved.eq_of_aux2nested_size_eq_zero
    (H : ConstructorLowering.Resolved env params nparams result source state out)
    (hsize : result.aux2nested.size = 0)
    (hclosed : source.type.FVarsIn fun _ => False)
    (hbclosed : Closed source.type) :
    out.1 = source ∧ out.2.newTypes = state.newTypes := by
  rcases H.mapped with
    ⟨lctx, tail, As, lowered, openedState, Hopening, hlctxWF, _Hselection,
      _hnodup, hopenedTypes, _hopenedAux, _hopenedNext, _hparams,
      Hmapping, htargetType⟩
  have hmapped := Hmapping.eq_of_aux2nested_size_eq_zero hsize
  have hlowered : lowered = tail := congrArg Prod.fst hmapped
  have houtState : out.2 = openedState := congrArg Prod.snd hmapped
  rcases Hopening.forallTelescope with ⟨residual, Htelescope⟩
  have hsourceType : lctx.mkForall As tail = source.type :=
    Hopening.toParamOpening.root_mkForall_tail hlctxWF Htelescope
      (FVarsIn_to_FVarIdsIn hclosed) hbclosed
  have houtType : out.1.type = source.type := by
    rw [htargetType, hlowered, hsourceType]
  have houtName : out.1.name = source.name := H.name
  have houtCtor : out.1 = source :=
    Constructor.eq_of_name_type houtName houtType
  exact ⟨houtCtor, by rw [houtState, hopenedTypes]⟩

/-- Pointwise constructor identity composes through the state-threaded
constructor list.  Only the dynamic family array is retained here; changes
to the private fresh-name generator are intentionally irrelevant. -/
theorem ConstructorLowerings.Resolved.eq_of_aux2nested_size_eq_zero
    (H : ConstructorLowerings.Resolved env params nparams result sources state out)
    (hsize : result.aux2nested.size = 0)
    (hclosed : ∀ source ∈ sources,
      source.type.FVarsIn fun _ => False)
    (hbclosed : ∀ source ∈ sources, Closed source.type) :
    out.1 = sources ∧ out.2.newTypes = state.newTypes := by
  induction H with
  | nil => exact ⟨rfl, rfl⟩
  | @cons source state step sources out Hhead Htail ih =>
      have hheadClosed : source.type.FVarsIn fun _ => False :=
        hclosed source (List.mem_cons_self)
      rcases Hhead.eq_of_aux2nested_size_eq_zero hsize hheadClosed
          (hbclosed source List.mem_cons_self) with
        ⟨htarget, hheadTypes⟩
      have htailClosed : ∀ (ctor : Constructor), ctor ∈ sources →
          ctor.type.FVarsIn fun _ => False := by
        intro ctor hctor
        exact hclosed ctor (List.mem_cons_of_mem _ hctor)
      have htailBClosed : ∀ (ctor : Constructor), ctor ∈ sources →
          Closed ctor.type := by
        intro ctor hctor
        exact hbclosed ctor (List.mem_cons_of_mem _ hctor)
      rcases ih htailClosed htailBClosed with
        ⟨htail, htailTypes⟩
      exact ⟨by simp [htarget, htail], htailTypes.trans hheadTypes⟩

/-- Hence an entire source family is unchanged whenever the final lowering
map is empty. -/
theorem FamilyLowering.Resolved.eq_of_aux2nested_size_eq_zero
    (H : FamilyLowering.Resolved env params nparams result source state out)
    (hsize : result.aux2nested.size = 0)
    (hclosed : InductiveConstructorsClosed source)
    (hbclosed : InductiveConstructorsBVarClosed source) :
    out.1 = source ∧ out.2.newTypes = state.newTypes := by
  rcases H.constructors.eq_of_aux2nested_size_eq_zero hsize hclosed hbclosed with
    ⟨hctors, houtTypes⟩
  have hname : out.1.name = source.name := H.name
  have htype : out.1.type = source.type := H.type
  have hout : out.1 = source :=
    InductiveType.eq_of_fields hname htype hctors
  exact ⟨hout, houtTypes⟩

/-- Once the final map is empty, every dynamic queue step rewrites its
selected slot with the very family already stored there and appends no new
family.  Thus exhausting the queue returns exactly its starting family
array. -/
theorem LoweringQueue.types_eq_of_aux2nested_size_eq_zero
    (H : LoweringQueue env params nparams lctx i fuel state out)
    (Hpending : PendingNewTypesClosed i state)
    (HpendingB : PendingNewTypesBVarClosed i state)
    (Hmap : NestedAuxMapModels out.1 out.2)
    (hsize : out.1.aux2nested.size = 0) :
    out.1.types = state.newTypes.toList := by
  induction H with
  | done => rfl
  | step Hnext Htail ih =>
      cases Hnext with
      | step hidx Hlowered =>
          rename_i iStep stateStep fuelStep outStep target loweredState
          have Hmapping := Hlowered.resolvedMapping
            Htail.resultNestedAuxLE Hmap
          have hclosed :
              InductiveConstructorsClosed stateStep.newTypes[iStep] :=
            Hpending iStep (Nat.le_refl _) hidx
          have hbclosed :
              InductiveConstructorsBVarClosed stateStep.newTypes[iStep] :=
            HpendingB iStep (Nat.le_refl _) hidx
          rcases Hmapping.eq_of_aux2nested_size_eq_zero hsize hclosed hbclosed with
            ⟨htarget, hloweredTypes⟩
          change target = stateStep.newTypes[iStep] at htarget
          change loweredState.newTypes = stateStep.newTypes at hloweredTypes
          have hnextTypes :
              ({ loweredState with
                newTypes := loweredState.newTypes.set! iStep target } :
                ElimNestedInductive.State).newTypes = stateStep.newTypes := by
            simp only
            rw [htarget, hloweredTypes]
            rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds,
              dif_pos hidx, Array.set_getElem_self hidx]
          have HpendingNext : PendingNewTypesClosed (iStep + 1)
              ({ loweredState with
                newTypes := loweredState.newTypes.set! iStep target } :
                ElimNestedInductive.State) := by
            intro j hjCursor hj
            have harray : loweredState.newTypes.set! iStep target =
                stateStep.newTypes := by simpa only using hnextTypes
            have hjState : j < stateStep.newTypes.size := by
              simpa only [harray] using hj
            simpa only [harray] using
              Hpending j (by omega) hjState
          have HpendingBNext : PendingNewTypesBVarClosed (iStep + 1)
              ({ loweredState with
                newTypes := loweredState.newTypes.set! iStep target } :
                ElimNestedInductive.State) := by
            intro j hjCursor hj
            have harray : loweredState.newTypes.set! iStep target =
                stateStep.newTypes := by simpa only using hnextTypes
            have hjState : j < stateStep.newTypes.size := by
              simpa only [harray] using hj
            simpa only [harray] using
              HpendingB j (by omega) hjState
          rw [ih HpendingNext HpendingBNext Hmap hsize, hnextTypes]

/-- Source syntax checked before lowering is therefore preserved literally
by every successful ordinary (zero-auxiliary) lowering result. -/
theorem NestedLoweringRun.types_eq_source_of_aux2nested_size_eq_zero
    {initialState : ElimNestedInductive.State}
    (H : NestedLoweringRun env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hsources : SourceSyntaxChecked sourceTypes)
    (HsourcesB : SourceBVarClosed sourceTypes)
    (hempty : initialState.nestedAux = #[])
    (hsize : result.aux2nested.size = 0) :
    result.types = sourceTypes := by
  rcases H with ⟨finalState, Hrun⟩
  rcases Hrun.source with
    ⟨first, rest, tail, paramsState, lctx, params, hsourceTypes, _Hopening,
      hinitialTypes, _hinitialAux, _hinitialNext, _Hprefix, _Hctx,
      _Hselection, Hqueue⟩
  have Hpending : PendingNewTypesClosed 0 paramsState := by
    intro j _hjCursor hj
    have hjSource : j < sourceTypes.length := by
      simpa [hinitialTypes] using hj
    have hvalue : paramsState.newTypes[j] = sourceTypes[j] := by
      have heq := congrArg (fun xs : Array InductiveType => xs[j]!)
        hinitialTypes
      simpa [Array.getElem!_eq_getD, Array.getD, hj, hjSource] using heq
    rw [hvalue]
    exact Hsources.constructorsClosed (List.getElem_mem hjSource)
  have HpendingB : PendingNewTypesBVarClosed 0 paramsState := by
    intro j _hjCursor hj
    have hjSource : j < sourceTypes.length := by
      simpa [hinitialTypes] using hj
    have hvalue : paramsState.newTypes[j] = sourceTypes[j] := by
      have heq := congrArg (fun xs : Array InductiveType => xs[j]!)
        hinitialTypes
      simpa [Array.getElem!_eq_getD, Array.getD, hj, hjSource] using heq
    rw [hvalue]
    exact HsourcesB.constructorsClosed (List.getElem_mem hjSource)
  have Hmap : NestedAuxMapModels result finalState :=
    Hrun.resultAuxMapModelsFresh (by simpa using hempty)
  have hresult := Hqueue.types_eq_of_aux2nested_size_eq_zero
    Hpending HpendingB Hmap hsize
  rw [hresult, hinitialTypes]

/-- The executable starts lowering from this exact fresh state.  This
specialization removes the generic cache premise from the declaration-facing
ordinary branch. -/
theorem NestedLoweringRun.ordinary_types_eq_source
    (H : NestedLoweringRun env fuel nparams sourceTypes
      { lvls := levels, newTypes := sourceTypes.toArray } result)
    (Hsources : SourceSyntaxChecked sourceTypes)
    (HsourcesB : SourceBVarClosed sourceTypes)
    (hsize : result.aux2nested.size = 0) :
    result.types = sourceTypes := by
  apply NestedLoweringRun.types_eq_source_of_aux2nested_size_eq_zero
    (initialState := { lvls := levels, newTypes := sourceTypes.toArray })
    H Hsources HsourcesB
  · rfl
  · exact hsize

end VerifyInductive
end Lean4Lean
