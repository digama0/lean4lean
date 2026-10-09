import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceTranslations

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Source-family alignment of lowering and restoration, for the source iota rules -/

/-- For one source family: its lowered target, the lowering mapping of its
constructors, the restoration steps of the lowered constructors, and the
alignment of the restored recursor telescope with the generated recursor entry.
Typing the left-hand side of a restored source iota rule needs these together,
not only the source recursor and constructor translations, because the
translations do not record the telescope identities. -/
structure SourceFamilyRestorationAlignment
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlowering : NestedLoweringOutputClosed loweredSourceEnv fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (hentry : familyIdx < Hprod.entries.length)
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv) : Type where
  fvars : List FVarId
  stepState : Lean4Lean.ElimNestedInductive.State
  target : InductiveType
  loweredState : Lean4Lean.ElimNestedInductive.State
  params : result.params = (fvars.map Expr.fvar).toArray
  paramsNodup : fvars.Nodup
  paramsSize : result.params.size = nparams
  targetAt : result.types[familyIdx]? = some target
  oldRecName : Lean.mkRecName sourceTypes[familyIdx].name =
    Lean.mkRecName result.types.toArray[familyIdx]!.name
  constructorNames : Hstep.oldInfo.ctors =
    target.ctors.map (fun ctor => ctor.name)
  mappings : ConstructorLowerings.Resolved loweredSourceEnv result.params
    nparams result sourceTypes[familyIdx].ctors stepState
      (target.ctors, loweredState)
  restorationTrace : FoldSteps
    (RestoredConstructorStep result loweredEnv)
    (target.ctors.map (fun ctor => ctor.name)) Hstep.restored.headerEnv
      Hstep.restored.constructorEnv
  constructors : LoweredRestoredConstructors result loweredSourceEnv
    loweredEnv result.params nparams c.safety c.lparams
      sourceTypes[familyIdx].ctors stepState target.ctors loweredState
      Hstep.restored.headerEnv Hstep.restored.constructorEnv
  recursor : RestoredRecursorTelescopeAlignment result loweredEnv
    auxRec Hstep.restored.recursor.restored.newInfo
      (Hprod.generated.entry familyIdx hentry)

/-- The source-family alignment, from a closed lowering run and the family's
restoration step. -/
theorem NestedLoweringOutputClosed.sourceOperationalFamilyAlignmentAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (hentry : familyIdx < Hprod.entries.length)
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv) :
    Nonempty (SourceFamilyRestorationAlignment H Hprod familyIdx
      hfamily hentry Hstep) := by
  rcases H.sourceConstructorRestorationTraceAtFresh Hc Hprod hempty
      familyIdx hfamily Hstep with
    ⟨fvars, stepState, target, loweredState, hparams, hnodup, hsize,
      htarget, hnames, Hmappings, Htrace, Hconstructors⟩
  have holdRecName : Lean.mkRecName sourceTypes[familyIdx].name =
      Lean.mkRecName result.types.toArray[familyIdx]!.name := by
    rcases H.sourceResolvedMappingAtFreshAligned hempty hfamily with
      ⟨_fvars, _stepState, mappedTarget, _loweredState, _hparams, _hnodup,
        _hsize, Hmapping, hmappedTarget⟩
    obtain ⟨hresult, hmappedEq⟩ := _root_.getElem?_eq_some_iff.mp hmappedTarget
    have harray : result.types.toArray[familyIdx]! = mappedTarget := by
      simp [hresult, hmappedEq]
    rw [harray, Hmapping.name]
  have hresultNparams : result.nparams = nparams :=
    H.toResult.resultNParams
  have hresultParams : result.params.size = result.nparams :=
    H.resultParamsSize
  rcases Hprod.restoredSourceTelescopeAlignment familyIdx hentry
      Hstep.restored.recursor holdRecName hresultNparams hresultParams with
    ⟨Hrecursor⟩
  exact ⟨{
    fvars := fvars
    stepState := stepState
    target := target
    loweredState := loweredState
    params := hparams
    paramsNodup := hnodup
    paramsSize := hsize
    targetAt := htarget
    oldRecName := holdRecName
    constructorNames := hnames
    mappings := Hmappings
    restorationTrace := Htrace
    constructors := Hconstructors
    recursor := Hrecursor }⟩

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Constructor translations along lowering and restoration -/

/-- For each source constructor, in lockstep: its lowering mapping, the
restoration step of the lowered constructor, and the translation of the source
constructor at that restoration step. This is the constructor half of the
typing of the left-hand side of a restored source iota rule. -/
inductive RestoredConstructorMappingTranslations
    (result : Lean4Lean.ElimNestedInductive.Result)
    (mappingEnv loweredEnv : Environment) (params : Array Expr)
    (nparams : Nat) (safety : DefinitionSafety) (lparams : List Name)
    (canonicalEnv : VEnv) :
    List Constructor → Lean4Lean.ElimNestedInductive.State →
      List Constructor → Lean4Lean.ElimNestedInductive.State →
      Environment → Environment → List VConstVal → Prop
  | nil (state : Lean4Lean.ElimNestedInductive.State)
      (sourceProdEnv : Environment) :
      RestoredConstructorMappingTranslations result mappingEnv loweredEnv
        params nparams safety lparams canonicalEnv [] state [] state
          sourceProdEnv sourceProdEnv []
  | cons
      (Hmapping : ConstructorLowering.Resolved mappingEnv params nparams result
        source state (target, nextState))
      (Hstep : RestoredConstructorStep result loweredEnv target.name
        sourceProdEnv middleProdEnv)
      (hsafety : safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety)
      (hlevels : Hstep.oldInfo.levelParams = lparams)
      (hname : Hstep.oldInfo.name = target.name)
      (htype : Hstep.oldInfo.type = target.type)
      (Hsemantic : RestoredConstructorTranslation lparams safety
        canonicalEnv Hstep source)
      (Hrest : RestoredConstructorMappingTranslations result mappingEnv
        loweredEnv params nparams safety lparams canonicalEnv sources
          nextState targets finalState middleProdEnv targetProdEnv
            constructors) :
      RestoredConstructorMappingTranslations result mappingEnv loweredEnv
        params nparams safety lparams canonicalEnv (source :: sources) state
          (target :: targets) finalState sourceProdEnv targetProdEnv
            (Hsemantic.constructor :: constructors)

/-- The constructor translations of `LoweredRestoredConstructors`, together with
the lowering mapping step of each constructor. -/
theorem LoweredRestoredConstructors.sourceMapping
    (H : LoweredRestoredConstructors result mappingEnv loweredEnv params
      nparams safety lparams sources state targets finalState sourceProdEnv
        targetProdEnv)
    (Hsources : List.Forall₂ (fun source constructor =>
      TrSourceConst canonicalEnv lparams source.name source.type constructor)
      sources constructors)
    (Hsyntax : SourceConstructorSyntaxes sources)
    (Hdisjoint : ∀ source ∈ sources,
      RestoreSourceDisjoint result loweredEnv source.type)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (hresultNParams : result.nparams = nparams)
    (hparamsSize : params.size = nparams) :
    RestoredConstructorMappingTranslations result mappingEnv loweredEnv
      params nparams safety lparams canonicalEnv sources state targets
        finalState sourceProdEnv targetProdEnv constructors := by
  induction H generalizing constructors with
  | nil =>
    cases Hsources
    exact .nil _ _
  | @cons source state target nextState sourceProdEnv middleProdEnv sources
      finalState targets targetProdEnv Hmapping Hstep hsafety hlevels hname
      htype Hrest ih =>
    cases Hsources with
    | cons Hsource Hsources =>
      rename_i constructor constructors
      cases Hsyntax with
      | cons HsourceSyntax Hsyntax =>
        have HsourceType : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
            source.type constructor.type := by
          simpa [hlevels] using Hsource.type
        have HrestoredType : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
            Hstep.restored.newInfo.type constructor.type :=
          Hmapping.restoredType_translation hresultParams paramFvars hparams
            hnodup HsourceSyntax.closed
            (by simpa [VLCtx.bvars] using HsourceType.closed) hparamsSize loweredEnv
            (Hdisjoint source (by simp)) hresultNParams
            Hstep.restored.restoration htype HsourceType
        have Htranslated : TrConstVal safety canonicalEnv
            (.ctorInfo Hstep.restored.newInfo) constructor :=
          Hstep.restored.restoration.translatedOfMetadata hsafety (by
            rw [hlevels]
            exact Hsource.uvars.symm) (by
            exact (hname.trans Hmapping.name).trans Hsource.name.symm)
            HrestoredType
        apply RestoredConstructorMappingTranslations.cons Hmapping Hstep
          hsafety hlevels hname htype
          { constructor := constructor
            sourceTranslation := Hsource
            restoredTranslation := Htranslated }
        apply ih Hsources Hsyntax
        intro tail htail
        exact Hdisjoint tail (by simp [htail])

/-- The lowering mapping, restoration step and translation of the `i`-th
constructor, with the restoration step's name and the translated constructor. -/
theorem RestoredConstructorMappingTranslations.at
    (H : RestoredConstructorMappingTranslations result mappingEnv loweredEnv
      params nparams safety lparams canonicalEnv sources state targets
        finalState sourceProdEnv targetProdEnv constructors)
    (i : Nat) (hsource : i < sources.length)
    (htarget : i < targets.length) (hconstructor : i < constructors.length) :
    ∃ before after stepSource stepTarget,
      ∃ _Hmapping : ConstructorLowering.Resolved mappingEnv params nparams result
          sources[i] before (targets[i], after),
      ∃ Hstep : RestoredConstructorStep result loweredEnv targets[i].name
          stepSource stepTarget,
      ∃ Hsemantic : RestoredConstructorTranslation lparams safety
          canonicalEnv Hstep sources[i],
        Hstep.oldInfo.name = targets[i].name ∧
        Hsemantic.constructor = constructors[i] := by
  induction H generalizing i with
  | nil => simp at hsource
  | cons Hmapping Hstep hsafety hlevels hname htype Hsemantic Hrest ih =>
    cases i with
    | zero => exact ⟨_, _, _, _, Hmapping, Hstep, Hsemantic, hname, rfl⟩
    | succ i =>
      simpa using ih i (by simpa using hsource) (by simpa using htarget)
          (by simpa using hconstructor)

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Source translations indexed by the restoration steps

The source-family translations and the lowering and restoration steps are
joined at family scope, so that a translated abstract constructor is known to
come from the restoration step used by the corresponding source equation, with
a pointwise selector that keeps this link.
-/

/-- For one source family with its alignment `A` and recursor translation:
the lockstep constructor translations, indexed by the same lowering and
restoration steps. -/
structure SourceFamilyConstructorTranslations
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv canonicalEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {Hlowering : NestedLoweringOutputClosed loweredSourceEnv fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result}
    {Hprod : RecursorCheck R.toConstructorCheck loweredEnv}
    {familyIdx : Nat} {hfamily : familyIdx < sourceTypes.length}
    {hentry : familyIdx < Hprod.entries.length}
    {Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv}
    (A : SourceFamilyRestorationAlignment Hlowering Hprod familyIdx
      hfamily hentry Hstep)
    (owner : VInductiveType)
    (Hrecursor : SourceRecursorTranslation sourceDecl owner c.safety
      Hstep.restored.recursor canonicalEnv) : Prop where
  constructors : RestoredConstructorMappingTranslations result
    loweredSourceEnv loweredEnv result.params nparams c.safety c.lparams
      canonicalEnv sourceTypes[familyIdx].ctors A.stepState A.target.ctors
        A.loweredState Hstep.restored.headerEnv
          Hstep.restored.constructorEnv owner.ctors

/-- The `i`-th constructor with all three of: the source constructor, its
lowering mapping and restoration step, and its translated abstract source
constructor. -/
theorem SourceFamilyConstructorTranslations.constructorAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv canonicalEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {Hlowering : NestedLoweringOutputClosed loweredSourceEnv fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result}
    {Hprod : RecursorCheck R.toConstructorCheck loweredEnv}
    {familyIdx : Nat} {hfamily : familyIdx < sourceTypes.length}
    {hentry : familyIdx < Hprod.entries.length}
    {Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv}
    {A : SourceFamilyRestorationAlignment Hlowering Hprod familyIdx
      hfamily hentry Hstep}
    {owner : VInductiveType}
    {Hrecursor : SourceRecursorTranslation sourceDecl owner c.safety
      Hstep.restored.recursor canonicalEnv}
    (F : SourceFamilyConstructorTranslations A owner Hrecursor)
    (i : Nat) (hsource : i < sourceTypes[familyIdx].ctors.length)
    (htarget : i < A.target.ctors.length)
    (hconstructor : i < owner.ctors.length) :
    ∃ before after stepSource stepTarget,
      ∃ _Hmapping : ConstructorLowering.Resolved loweredSourceEnv result.params
          nparams result sourceTypes[familyIdx].ctors[i] before
            (A.target.ctors[i], after),
      ∃ HctorStep : RestoredConstructorStep result loweredEnv
          A.target.ctors[i].name stepSource stepTarget,
      ∃ Hsemantic : RestoredConstructorTranslation c.lparams c.safety
          canonicalEnv HctorStep sourceTypes[familyIdx].ctors[i],
        HctorStep.oldInfo.name = A.target.ctors[i].name ∧
        Hsemantic.constructor = owner.ctors[i] :=
  F.constructors.at i hsource htarget hconstructor

end VerifyInductive
end Lean4Lean
