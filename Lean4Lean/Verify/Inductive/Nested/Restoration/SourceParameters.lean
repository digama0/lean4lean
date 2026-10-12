import Lean4Lean.Verify.Inductive.Nested.Restoration.HeaderRenaming
import Lean4Lean.Verify.Inductive.Nested.Lowering.Expansion.AuxiliarySources

/-! # Source parameter formation of a nested run
 `NestedRun.sourceCoreTypeShapes`, `NestedRun.sourceCoreParameterWF`: the source families inherit
the header shapes of the lowered prefix, and the parameter shape of every source constructor is the
lowered one's, transported to the source header environment by the header-stage restoration
interpretation (`NestedRun.headerInterpretationSound`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VExpr

/-- A telescope avoiding `names` has domains and body avoiding `names`. -/
theorem containsAnyConst_wrapForalls_inv {names : List Name} :
    ∀ {ds : List VExpr} {b : VExpr}, (VExpr.wrapForalls ds b).containsAnyConst names = false →
      (∀ d ∈ ds, d.containsAnyConst names = false) ∧ b.containsAnyConst names = false
  | [], _, h => ⟨by simp, h⟩
  | d :: ds, b, h => by
    simp only [VExpr.wrapForalls, List.foldr_cons, VExpr.containsAnyConst,
      Bool.or_eq_false_iff] at h
    obtain ⟨hds, hb⟩ := containsAnyConst_wrapForalls_inv (ds := ds) h.2
    refine ⟨fun x hx => ?_, hb⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact hds x hx

end VExpr

namespace VerifyInductive

section Run
variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment} {sourceVEnv : VEnv} {safety : DefinitionSafety}

/-- The source families reconstructed by restoration inherit the ordinary
header shapes of the exact lowered prefix.  The source-core builder retains
literal header values, while the header checks retain the separately checked
index count and result universe. -/
theorem NestedRun.sourceCoreTypeShapes
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes sourceVEnv
      sourceDecl lparams nparams isUnsafe safety outEnv L)
    {params : List VExpr}
    (Hshapes : ∀ target ∈ E.lowered.loweredDecl.types,
      E.lowered.loweredDecl.TypeShape E.lowered.Hc'.venv params target) :
    ∀ target ∈ sourceDecl.types,
      sourceDecl.TypeShape sourceVEnv params target := by
  let P := E.lowered
  have hinitial : P.Hc'.venv = sourceVEnv := E.lowered_initialEnv
  have Hsource : TrInductDeclCore sourceVEnv lparams nparams sourceTypes
      isUnsafe sourceDecl E.sourceCore.envTypes E.sourceCore.envCtors := by
    simpa only [E.sourceCoreDecl_eq] using E.sourceCore.core
  have hsourceLength : sourceDecl.types.length = sourceTypes.length :=
    (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource).symm
  have hloweredLength : P.loweredDecl.types.length = result.types.length :=
    by
      have harray : result.types.toArray.toList = result.types := by simp
      exact (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
        P.constructors.core).symm.trans (congrArg List.length harray)
  have hprefix : sourceDecl.types.length ≤ P.loweredDecl.types.length := by
    rw [hsourceLength, hloweredLength]
    let initialState : Lean4Lean.ElimNestedInductive.State :=
      { lvls := lparams.map .param, newTypes := #[] }
    have Hresult : NestedLoweringRun sourceProdEnv
        E.validationFuel.inductiveFuel nparams sourceTypes
        { initialState with newTypes := sourceTypes.toArray }
        result := E.lowering.toResult
    exact Hresult.sourceTypes_length_le
  have huvarsEq : sourceDecl.uvars = P.loweredDecl.uvars := by
    calc
      sourceDecl.uvars = lparams.length := Hsource.uvars
      _ = P.c.lparams.length := by rw [E.lowered_c,
        E.context_lparams]
      _ = P.loweredDecl.uvars := P.constructors.core.uvars.symm
  have hnparamsEq : sourceDecl.nparams = P.loweredDecl.nparams := by
    calc
      sourceDecl.nparams = nparams := Hsource.nparams
      _ = nparams := rfl
      _ = P.loweredDecl.nparams := P.constructors.core.nparams.symm
  intro target htarget
  rcases List.mem_iff_getElem.1 htarget with ⟨i, hi, rfl⟩
  have hiExpanded : i < P.loweredDecl.types.length :=
    Nat.lt_of_lt_of_le hi hprefix
  let sourceTarget := sourceDecl.types[i]
  let expandedTarget := P.loweredDecl.types[i]
  have hvalue : sourceTarget.toVConstVal = expandedTarget.toVConstVal := by
    have hvaluesAll : sourceDecl.typeConstants =
        (P.loweredDecl.types.take sourceTypes.length).map
          VInductiveType.toVConstVal := by
      simpa only [P, E.sourceCoreDecl_eq] using
        E.sourceCore.sourceTypeValues
    have hvalues := congrArg (fun values => values[i]?)
      hvaluesAll
    have hiTake : i <
        (P.loweredDecl.types.take sourceTypes.length).length := by
      simp only [List.length_take]
      rw [← hsourceLength]
      omega
    simp only [VInductDecl.typeConstants, List.getElem?_map,
      List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hiTake,
      List.getElem_take, Option.map_some] at hvalues
    simpa only [sourceTarget, expandedTarget] using Option.some.inj hvalues
  have htype : sourceTarget.type = expandedTarget.type :=
    congrArg (fun value : VConstVal => value.type) hvalue
  have Hmetadata : SourcePrefixOfLowered sourceDecl P.loweredDecl := by
    simpa only [E.sourceCoreDecl_eq] using E.sourceCore.checked
  have hnumIndices : sourceTarget.numIndices = expandedTarget.numIndices :=
    Hmetadata.numIndices hprefix i hi hiExpanded
  have hresultLevel : sourceTarget.resultLevel = expandedTarget.resultLevel :=
    Hmetadata.resultLevel hprefix i hi hiExpanded
  have Hshape : P.loweredDecl.TypeShape sourceVEnv params expandedTarget := by
    have H : P.loweredDecl.TypeShape P.Hc'.venv params expandedTarget :=
      Hshapes expandedTarget (List.getElem_mem hiExpanded)
    rw [hinitial] at H
    exact H
  rcases Hshape with
    ⟨normalized, ownParams, afterParams, indices, resultType, exprType,
      Hnormalized, Hparams, Hindices, HparamsDefEq, Hresult⟩
  exact ⟨normalized, ownParams, afterParams, indices, resultType, exprType,
    by simpa only [sourceTarget, expandedTarget, huvarsEq, htype] using
      Hnormalized,
    by simpa only [hnparamsEq] using Hparams,
    by simpa only [sourceTarget, expandedTarget, hnumIndices] using Hindices,
    by simpa [VInductDecl.ParamsDefEq, huvarsEq] using HparamsDefEq,
    by simpa only [sourceTarget, expandedTarget, huvarsEq, hresultLevel] using
      Hresult⟩

/-- Source parameter formation of a nested run, without a source-side
re-check. Lowering keeps the common-parameter prefix of every source
constructor verbatim (`ConstructorLowering.Resolved.sourceTargetSameForallPrefix`),
so the translated prefix of a source constructor is the one of its lowered
constructor, whose parameter shape the ordinary pipeline certified in the
lowered header environment. The header-stage restoration interpretation
(`headerInterpretationSound`) transports that certificate to the source header
environment: the parameters and the prefix mention no auxiliary family, so the
interpretation fixes them. -/
theorem NestedRun.sourceCoreParameterWF
    {ves : VEnvs}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    (Hraw : ∀ type ∈ sourceDecl.types, ∀ ctor ∈ type.ctors,
      sourceDecl.RawCtorShape type ctor) :
    sourceDecl.SourceParameterWF (ves.venv (if isUnsafe then .unsafe else .safe)) := by
  let P := E.lowered
  have hinitial : P.Hc'.venv = ves.venv (if isUnsafe then .unsafe else .safe) :=
    E.lowered_initialEnv
  obtain ⟨paramsL, envTypesL, haddedL, HtypeShapesL, HctorsL, -⟩ :=
    P.constructors.formation.formationWF.sourceParameterWF
  have hheaderL : envTypesL = P.constructors.headerVEnv := by
    have h := P.constructors.core.typesAdded
    rw [haddedL] at h
    exact Option.some.inj h
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, auxiliaries, hadded, henvTypes, Haux, Hexpansion, -, -,
      -, -, -⟩
  have hnodup : (InductiveSignature.familyNames P.loweredDecl.types ++
      P.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  have S := E.headerInterpretationSound wf hadded henvTypes Haux Hexpansion hnodup
    henvTypes.orderedStrong VEnv.LE.rfl
  have hfresh := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hbaseWF : (ves.venv (if isUnsafe then .unsafe else .safe)).WF := TrEnv'.wf wf.tr
  have hbaseFresh : ∀ n ∈ (InductiveSignature.compilationRestoration sourceDecl auxiliaries).restorableNames,
      (ves.venv (if isUnsafe then .unsafe else .safe)).constants n = none :=
    fun n hn => (VEnv.addConstVals_le hadded).constants_eq_none_left (hfresh n hn)
  have Hsource : TrInductDeclCore (ves.venv (if isUnsafe then .unsafe else .safe))
      lparams nparams sourceTypes isUnsafe sourceDecl E.sourceCore.envTypes
        E.sourceCore.envCtors := by
    simpa only [E.sourceCoreDecl_eq] using E.sourceCore.core
  have hnativeTypes : E.sourceCore.envTypes = envTypes := by
    have h := Hsource.typesAdded
    rw [hadded] at h
    exact (Option.some.inj h).symm
  have HtypeShapes := E.sourceCoreTypeShapes HtypeShapesL
  refine ⟨paramsL, envTypes, hadded, HtypeShapes, ?_, Hraw⟩
  intro target htarget ctor hctor
  rcases List.mem_iff_getElem.1 htarget with ⟨familyIdx, hfamily, rfl⟩
  rcases List.mem_iff_getElem.1 hctor with ⟨ctorIdx, hctorTarget, rfl⟩
  have hsourceFamily : familyIdx < sourceTypes.length := by
    rw [TrInductDeclCore.types_length Hsource]
    exact hfamily
  have HsourceType := TrInductDeclCore.typeAt Hsource familyIdx hsourceFamily hfamily
  have hsourceCtor : ctorIdx < sourceTypes[familyIdx].ctors.length := by
    rw [TrInductiveType.ctors_length HsourceType]
    exact hctorTarget
  have HsourceCtor := TrInductiveType.ctorAt HsourceType ctorIdx hsourceCtor hctorTarget
  -- The lowered constructor at the same position.
  rcases E.lowering.sourceResolvedMappingAtFreshAligned (initialState :=
      { lvls := lparams.map .param, newTypes := #[] }) rfl hsourceFamily with
    ⟨_, _, loweredType, _, _, _, _, Hmapping, hloweredType⟩
  rcases Hmapping.constructors.mappingAt ctorIdx hsourceCtor with
    ⟨sourceCtor, loweredCtor, _, _, hsourceCtorEq, hloweredCtorEq, HctorMapping⟩
  have hsourceCtorEq' : sourceCtor = sourceTypes[familyIdx].ctors[ctorIdx] := by
    rw [List.getElem?_eq_getElem hsourceCtor] at hsourceCtorEq
    exact (Option.some.inj hsourceCtorEq).symm
  subst hsourceCtorEq'
  have Hsame := HctorMapping.sourceTargetSameForallPrefix
    (by simpa using HsourceCtor.type.fvarsIn) HsourceCtor.type.closed
  -- Its translation in the lowered header environment.
  have hindTypes : result.types.toArray.toList = result.types := by
    simp
  have Hlowered := P.constructors.core
  have hloweredFamily : familyIdx < result.types.length := by
    rcases List.getElem?_eq_some_iff.1 hloweredType with ⟨h, _⟩
    exact h
  have hloweredFamily' : familyIdx < result.types.toArray.toList.length := by
    rw [hindTypes]; exact hloweredFamily
  have hloweredDeclFamily : familyIdx < P.loweredDecl.types.length := by
    rw [← TrInductDeclCore.types_length Hlowered]; exact hloweredFamily'
  have HloweredType := TrInductDeclCore.typeAt Hlowered familyIdx hloweredFamily'
    hloweredDeclFamily
  have hloweredTypeEq : result.types.toArray.toList[familyIdx] = loweredType := by
    have h : result.types.toArray.toList[familyIdx]? = some loweredType := by
      rw [hindTypes]; exact hloweredType
    rw [List.getElem?_eq_getElem hloweredFamily'] at h
    exact Option.some.inj h
  have hloweredCtorIdx : ctorIdx < loweredType.ctors.length := by
    rcases List.getElem?_eq_some_iff.1 hloweredCtorEq with ⟨h, _⟩
    exact h
  have hloweredCtorIdx' : ctorIdx < result.types.toArray.toList[familyIdx].ctors.length := by
    rw [hloweredTypeEq]; exact hloweredCtorIdx
  have hloweredDeclCtor : ctorIdx < P.loweredDecl.types[familyIdx].ctors.length := by
    rw [← TrInductiveType.ctors_length HloweredType]; exact hloweredCtorIdx'
  have HloweredCtor := TrInductiveType.ctorAt HloweredType ctorIdx hloweredCtorIdx'
    hloweredDeclCtor
  have hloweredCtorEq' : result.types.toArray.toList[familyIdx].ctors[ctorIdx] = loweredCtor := by
    have h : loweredType.ctors[ctorIdx]? = some loweredCtor := hloweredCtorEq
    rw [List.getElem?_eq_getElem hloweredCtorIdx] at h
    simp only [hloweredTypeEq]
    exact Option.some.inj h
  have HloweredCtorType : TrExprS P.headers.context.venv P.c.lparams []
      loweredCtor.type P.loweredDecl.types[familyIdx].ctors[ctorIdx].type := by
    have h := HloweredCtor.type
    rw [hloweredCtorEq'] at h
    exact h
  -- The certified parameter shape of the lowered constructor.
  rcases HctorsL _ (List.getElem_mem hloweredDeclFamily) _
      (List.getElem_mem hloweredDeclCtor) with ⟨own, tail, htake, hdefeq⟩
  have hlparams : P.c.lparams = lparams :=
    (congrArg AddInductive.Context.lparams E.lowered_c).trans
      E.context_lparams
  have hnparamsEq : P.loweredDecl.nparams = sourceDecl.nparams :=
    P.constructors.core.nparams.trans Hsource.nparams.symm
  rw [hnparamsEq] at htake
  have hnparams : sourceDecl.nparams = nparams := Hsource.nparams
  rw [hnparams] at htake
  obtain ⟨tail', htake'⟩ := Hsame.takeForalls_of_trExprS .base
    (by simpa only [hlparams] using HsourceCtor.type)
    (by simpa only [hlparams] using HloweredCtorType) htake
  refine ⟨own, tail', by rw [hnparams]; exact htake', ?_⟩
  -- The prefix mentions no restorable name.
  have hownClean : ∀ A ∈ own,
      A.containsAnyConst (InductiveSignature.compilationRestoration sourceDecl auxiliaries).restorableNames =
        false := by
    have hwf := HsourceCtor.wf
    rw [hnativeTypes] at hwf
    obtain ⟨u, hu⟩ := hwf
    have hclean := (hu.noFreshConsts henvTypes hfresh
      (fun _ h => by simp at h)).1
    rw [(VExpr.takeForalls_eq_wrapForalls htake').1] at hclean
    exact (VExpr.containsAnyConst_wrapForalls_inv hclean).1
  have huvars : P.loweredDecl.uvars = sourceDecl.uvars :=
    P.constructors.core.uvars.trans (by rw [hlparams, Hsource.uvars])
  have hdefeq' : P.constructors.headerVEnv.IsDefEqCtx sourceDecl.uvars []
      paramsL.reverse own.reverse := by
    rw [← hheaderL, ← huvars]; exact hdefeq
  have Htransported := (S.isDefEqCtx .any hdefeq' trivial).1
  -- The parameters and the prefix mention no restorable name.
  have hparamsClean : ∀ A ∈ paramsL,
      A.containsAnyConst (InductiveSignature.compilationRestoration sourceDecl auxiliaries).restorableNames =
        false := by
    rcases HtypeShapes _ htarget with ⟨_, _, _, _, _, _, _, _, _, hshape, _⟩
    have hctx := VEnv.WF.ctxNoFreshConsts hbaseWF hbaseFresh hshape.isType
    intro A hA
    exact hctx A (List.mem_reverse.mpr hA)
  have hmapParams : paramsL.reverse.map
      ((InductiveSignature.compilationRestoration sourceDecl auxiliaries).interpretation
        P.signature.params).expr = paramsL.reverse := by
    rw [List.map_congr_left (fun A hA => InductiveSignature.Restoration.interpretation_expr_eq_self
      (hparamsClean A (List.mem_reverse.mp hA))), List.map_id']
  have hmapOwn : own.reverse.map
      ((InductiveSignature.compilationRestoration sourceDecl auxiliaries).interpretation
        P.signature.params).expr = own.reverse := by
    rw [List.map_congr_left (fun A hA => InductiveSignature.Restoration.interpretation_expr_eq_self
      (hownClean A (List.mem_reverse.mp hA))), List.map_id']
  have Htransported' := Htransported
  rw [hmapParams, hmapOwn, List.map_nil] at Htransported'
  exact Htransported'


end Run

end VerifyInductive
end Lean4Lean
