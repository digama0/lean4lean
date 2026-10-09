import Lean4Lean.Verify.Inductive.Recursor.Binders.ParameterPrefixes
import Lean4Lean.Verify.Inductive.Nested.Restoration.ParameterOpening
import Lean4Lean.Verify.Inductive.Recursor.Binders.MinorAlignment
import Lean4Lean.Verify.Inductive.Recursor.Context.ForallTelescope
import Lean4Lean.Verify.Typing.EnvironmentRestriction
import Lean4Lean.Verify.Inductive.Nested.Install.ConstructorCoherence

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- The restored-family half of constructor parameter coherence.  This
is family-indexed (rather than constructor-indexed): every constructor of one
family is compared with the same executable cached parameter scope. -/
structure RestoredFamilyParameterScope
    (env : VEnv) (levelParams : List Name) (numParams : Nat)
    (scope : VLCtx) (familyTarget : VConstant) where
  domains : List VExpr
  tail : VExpr
  target_defeq : env.IsDefEqU levelParams.length [] familyTarget.type
    (VExpr.wrapForalls domains tail)
  length : domains.length = numParams
  context : env.IsDefEqCtx levelParams.length [] domains.reverse scope.toCtx

/-- Restored constructor-parameter coherence from the raw
constructor-formation judgment.

Both the restored family and the restored constructor are compared with the
same parameter list `params`.  The executable cached scope is used only to
relate that list to the family's normalized header; the theorem has no
derivation-locality or environment-restriction premise.
-/
theorem RestoredFamilyParameterScope.constructorDomains
    {decl : VInductDecl} {params : List VExpr} {constructor : VConstVal}
    (Hfamily : RestoredFamilyParameterScope env levelParams numParams scope
      familyTarget)
    (henv : env.WF)
    (Hctor : decl.CtorParameterShape env params constructor)
    (huvars : decl.uvars = levelParams.length)
    (hnparams : decl.nparams = numParams)
    (hparamsScope : env.IsDefEqCtx levelParams.length []
      params.reverse scope.toCtx) :
    Nonempty (ConstructorParameterDomainsDefEq env levelParams numParams
      familyTarget constructor.toVConstant) := by
  rcases Hctor with ⟨constructorDomains, constructorTail,
    hconstructorTake, hconstructorParams⟩
  rcases VExpr.takeForalls_rebuild hconstructorTake with
    ⟨hconstructorTarget, hconstructorLength⟩
  have hconstructorToParams : env.IsDefEqCtx levelParams.length []
      constructorDomains.reverse params.reverse := by
    have hparams : env.IsDefEqCtx levelParams.length []
        params.reverse constructorDomains.reverse := by
      simpa [VInductDecl.ParamsDefEq, huvars] using hconstructorParams
    exact hparams.symm henv.ordered
  have hconstructorScope : env.IsDefEqCtx levelParams.length []
      constructorDomains.reverse scope.toCtx :=
    VEnv.IsDefEqCtx.trans_empty henv hconstructorToParams hparamsScope
  exact ⟨{
    familyDomains := Hfamily.domains
    constructorDomains := constructorDomains
    familyTail := Hfamily.tail
    constructorTail := constructorTail
    familyTarget_defeq := Hfamily.target_defeq
    constructorTarget_eq := hconstructorTarget
    familyLength := Hfamily.length
    constructorLength := hconstructorLength.trans hnparams
    parameterDomains := VEnv.IsDefEqCtx.trans_empty henv Hfamily.context
      (hconstructorScope.symm henv.ordered) }⟩

/-- Family-indexed parameter scopes relating the lowered run's header check
to the restored constructors.  This chooses no constructor and contains no
constructor translation. -/
def NestedRestoredFamilyParameterScopes
    (E : NestedInstalledRun result sourceProdEnv sourceTypes sourceEnv
      decl lparams nparams isUnsafe safety outEnv) : Prop :=
  ∀ familyIdx (hfamily : familyIdx < decl.types.length),
    Nonempty (RestoredFamilyParameterScope E.assembly.install.venvCtors
      lparams nparams E.lowered.headers.statsWF.parameterScope
      decl.types[familyIdx].toVConstVal.toVConstant)

/-- The restored source family has the same abstract parameter telescope as
the lowered header checked by the executable.
The telescope need not be syntactically visible in the restored constant:
header checking normalizes before exposing `TypeShape`. -/
theorem NestedInstalledRun.restoredFamilyParameterScopes
    (E : NestedInstalledRun result sourceProdEnv sourceTypes sourceEnv
      decl lparams nparams isUnsafe safety outEnv)
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed E.context.env fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[]) :
    NestedRestoredFamilyParameterScopes E := by
  let Hsource : TrInductDeclCore sourceEnv lparams nparams sourceTypes
      isUnsafe decl E.assembly.install.venvTypes
        E.assembly.install.venvCtors :=
    E.assembly.sourceTranslations.core E.assembly.typesSource E.assembly.uvars
      E.assembly.numParams E.assembly.unsafeEq E.assembly.typesAdded
      E.assembly.constructorsAdded
  have hsourceWF : sourceEnv.WF := by
    have hwf := E.lowered.headers.sourceContext.checking.tr.wf
    rw [E.lowered.headers.sourceContextVEnv] at hwf
    simpa only [E.lowered_initialEnv] using hwf
  have hcanonicalWF : E.assembly.install.venvCtors.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envCtorsWF Hsource hsourceWF
  have hsourceLE : sourceEnv ≤ E.assembly.install.venvCtors :=
    (VEnv.addConstVals_le E.assembly.typesAdded).trans
      (VEnv.addConstVals_le E.assembly.constructorsAdded)
  have hlparams : E.lowered.c.lparams = lparams := by
    rw [E.lowered_c, E.context_lparams]
  intro familyIdx hfamily
  have hsourceFamily : familyIdx < sourceTypes.length := by
    rw [Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource]
    exact hfamily
  have hresultFamily : familyIdx < result.types.length :=
    Nat.lt_of_lt_of_le hsourceFamily Hlower.toResult.sourceTypes_length_le
  have hloweredFamily : familyIdx < E.lowered.loweredDecl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
      E.lowered.constructors.core]
    simpa only [E.lowered_indTypes] using hresultFamily
  let sourceTarget := decl.types[familyIdx]
  let loweredTarget := E.lowered.loweredDecl.types[familyIdx]
  have HsourceType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hsource
    familyIdx hsourceFamily hfamily
  have HproductionCore : TrInductDeclCore E.lowered.initialEnv lparams
      nparams result.types E.lowered.isUnsafe E.lowered.loweredDecl
      E.lowered.headers.context.venv
      E.lowered.constructors.declared.venvCtors := by
    simpa [hlparams, E.lowered_nparams, E.lowered_indTypes]
      using E.lowered.constructors.core
  rcases Hlower.sourceHeaderTranslationAtFresh hempty
      HproductionCore familyIdx hsourceFamily with
    ⟨_hdecl, HloweredHeader⟩
  have HtargetEq : sourceEnv.IsDefEqU lparams.length []
      sourceTarget.type loweredTarget.type := by
    exact HsourceType.header.type.uniq hsourceWF
      (.refl hsourceWF (by trivial)) (by
        simpa only [E.lowered_initialEnv, hlparams,
          sourceTarget, loweredTarget]
        using HloweredHeader.type)
  have HloweredShape : E.lowered.loweredDecl.TypeShape sourceEnv
      E.lowered.headers.sourceStatsWF.headers.params loweredTarget := by
    have Hshape :=
      E.lowered.headers.sourceStatsWF.headers.typeShapes loweredTarget
        (List.getElem_mem hloweredFamily)
    simpa only [E.lowered.headers.sourceContextVEnv,
      E.lowered_initialEnv] using Hshape
  rcases HloweredShape with
    ⟨normalized, ownParams, afterParams, _indices, _familyResult, exprType,
      Hnormalized, HparamsTake, _HindicesTake, Hparams, _Hresult⟩
  rcases VExpr.takeForalls_rebuild HparamsTake with
    ⟨HnormalizedEq, hownParams⟩
  have HsourceNormalized : sourceEnv.IsDefEq lparams.length []
      sourceTarget.type normalized exprType := by
    have HtargetEq' : sourceEnv.IsDefEqU E.lowered.loweredDecl.uvars []
        sourceTarget.type loweredTarget.type := by
      simpa [E.lowered.constructors.core.uvars, hlparams] using HtargetEq
    have Hnormalized' := VEnv.IsDefEq.transU_r hsourceWF (by trivial)
      HtargetEq' Hnormalized
    simpa [E.lowered.constructors.core.uvars, hlparams] using Hnormalized'
  have HtargetDefEq : E.assembly.install.venvCtors.IsDefEqU
      lparams.length [] sourceTarget.type
      (VExpr.wrapForalls ownParams afterParams) := by
    rw [← HnormalizedEq]
    exact ⟨exprType, HsourceNormalized.mono hsourceLE⟩
  have HownCommon : E.assembly.install.venvCtors.IsDefEqCtx
      lparams.length [] ownParams.reverse
      E.lowered.headers.sourceStatsWF.headers.params.reverse := by
    have Hparams' : sourceEnv.IsDefEqCtx lparams.length []
        E.lowered.headers.sourceStatsWF.headers.params.reverse
        ownParams.reverse := by
      simpa [VInductDecl.ParamsDefEq,
        E.lowered.constructors.core.uvars, hlparams] using Hparams
    exact (Hparams'.symm hsourceWF.ordered).mono hsourceLE
  have HcommonCached : E.assembly.install.venvCtors.IsDefEqCtx
      lparams.length []
      E.lowered.headers.sourceStatsWF.headers.params.reverse
      E.lowered.headers.sourceStatsWF.parameterScope.toCtx := by
    have Hcached₀ := E.lowered.headers.sourceStatsWF.paramsContext
    have Hcached : sourceEnv.IsDefEqCtx lparams.length []
        E.lowered.headers.sourceStatsWF.headers.params.reverse
        E.lowered.headers.sourceStatsWF.parameterScope.toCtx := by
      simpa only [E.lowered.headers.sourceContextVEnv,
        E.lowered_initialEnv, hlparams] using Hcached₀
    exact Hcached.mono hsourceLE
  have HownCached := VEnv.IsDefEqCtx.trans_empty hcanonicalWF HownCommon
    HcommonCached
  exact ⟨{
    domains := ownParams
    tail := afterParams
    target_defeq := by simpa [sourceTarget] using HtargetDefEq
    length := by
      calc
        ownParams.length = E.lowered.loweredDecl.nparams := hownParams
        _ = E.lowered.nparams := E.lowered.constructors.core.nparams
        _ = nparams := E.lowered_nparams
    context := by
      rw [E.lowered.headers.parameterScopeEq]
      exact HownCached }⟩

/-- Restored constructor-parameter coherence from the source
parameter-formation certificate of the nested run.  The source
certificate fixes one parameter list for every family and
constructor.  For each restored family, equal-length forall inversion aligns
that list with the executable cached parameter scope, so no
derivation-locality or environment-restriction premise is required. -/
theorem NestedInstalledRun.constructorParameterDomainsDefEqOfSource
    (E : NestedInstalledRun result sourceProdEnv sourceTypes sourceEnv
      decl lparams nparams isUnsafe safety outEnv)
    (Hfamilies : NestedRestoredFamilyParameterScopes E) :
    NestedConstructorParameterDomainsDefEq E.assembly := by
  rcases E.assembly.formationAssembly.sourceParameters with
    ⟨params, parameterEnv, hparameterEnv, Htypes, Hconstructors⟩
  have hcanonicalTypes : parameterEnv =
      E.assembly.install.venvTypes := by
    exact Option.some.inj (hparameterEnv.symm.trans
      E.assembly.typesAdded)
  subst parameterEnv
  have hsourceTypes : sourceEnv ≤ E.assembly.install.venvTypes :=
    VEnv.addConstVals_le E.assembly.typesAdded
  have htypesCtors : E.assembly.install.venvTypes ≤
      E.assembly.install.venvCtors :=
    VEnv.addConstVals_le E.assembly.install.abstract_ctors
  have hsourceCtors : sourceEnv ≤ E.assembly.install.venvCtors :=
    hsourceTypes.trans htypesCtors
  have hcanonicalWF : E.assembly.install.venvCtors.WF := by
    let Hsource : TrInductDeclCore sourceEnv lparams nparams sourceTypes
        isUnsafe decl E.assembly.install.venvTypes
          E.assembly.install.venvCtors :=
      E.assembly.sourceTranslations.core E.assembly.typesSource E.assembly.uvars
        E.assembly.numParams E.assembly.unsafeEq
        E.assembly.typesAdded E.assembly.constructorsAdded
    have hsourceWF : sourceEnv.WF := by
      have hwf := E.lowered.headers.sourceContext.checking.tr.wf
      rw [E.lowered.headers.sourceContextVEnv] at hwf
      simpa only [E.lowered_initialEnv] using hwf
    exact TrInductDeclCore.envCtorsWF Hsource hsourceWF
  intro familyIdx hfamily ctorIdx hctor
  let family := decl.types[familyIdx]
  let constructor := family.ctors[ctorIdx]
  have hfamilyMem : family ∈ decl.types :=
    List.getElem_mem hfamily
  have hctorMem : constructor ∈ family.ctors :=
    List.getElem_mem hctor
  have Hshape := Htypes family hfamilyMem
  have Hconstructor : decl.CtorParameterShape
      E.assembly.install.venvCtors params constructor :=
    (Hconstructors.1 family hfamilyMem constructor hctorMem).mono htypesCtors
  rcases Hfamilies familyIdx hfamily with ⟨Hfamily⟩
  rcases Hshape with
    ⟨normalized, ownParams, afterParams, indices, resultType, exprType,
      Hnormalized, HparamsTake, _HindicesTake, Hparams, _Hresult⟩
  rcases VExpr.takeForalls_rebuild HparamsTake with
    ⟨HnormalizedTarget, hownLength⟩
  have HsourcePresentation :
      E.assembly.install.venvCtors.IsDefEqU lparams.length []
        family.type (VExpr.wrapForalls ownParams afterParams) := by
    rw [← HnormalizedTarget]
    exact ⟨exprType, by
      simpa [E.assembly.uvars] using Hnormalized.mono hsourceCtors⟩
  have Hpresentations :
      E.assembly.install.venvCtors.IsDefEqU lparams.length []
        (VExpr.wrapForalls ownParams afterParams)
        (VExpr.wrapForalls Hfamily.domains Hfamily.tail) := by
    exact HsourcePresentation.symm.trans hcanonicalWF (by trivial)
      (by simpa [family] using Hfamily.target_defeq)
  have HownFamily := VEnv.IsDefEqU.wrapForalls_context hcanonicalWF
    (VEnv.IsDefEqCtx.refl (by trivial))
    (hownLength.trans (E.assembly.numParams.trans Hfamily.length.symm))
    Hpresentations
  have HparamsOwn : E.assembly.install.venvCtors.IsDefEqCtx
      lparams.length [] params.reverse ownParams.reverse := by
    simpa [VInductDecl.ParamsDefEq, E.assembly.uvars] using
      Hparams.mono hsourceCtors
  have HparamsFamily : E.assembly.install.venvCtors.IsDefEqCtx
      lparams.length [] params.reverse Hfamily.domains.reverse :=
    VEnv.IsDefEqCtx.trans_empty hcanonicalWF HparamsOwn (by
      simpa using HownFamily)
  have HparamsScope : E.assembly.install.venvCtors.IsDefEqCtx
      lparams.length [] params.reverse
        E.lowered.headers.statsWF.parameterScope.toCtx :=
    VEnv.IsDefEqCtx.trans_empty hcanonicalWF HparamsFamily Hfamily.context
  simpa [family, constructor] using
    Hfamily.constructorDomains hcanonicalWF Hconstructor
      E.assembly.uvars E.assembly.numParams HparamsScope

end VerifyInductive
end Lean4Lean
