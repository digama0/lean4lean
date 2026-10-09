import Lean4Lean.Verify.Inductive.Primitive.Headers
import Lean4Lean.Verify.Inductive.Primitive.ConstructorParams
import Lean4Lean.Verify.Inductive.Recursor.Context.Unannotated

/-!
# The primitive run

Composes the primitive header and constructor phases with the shared recursor phase: the
formation prefix rejoins the ordinary pipeline once the atomic batch has restored a valid
context (`AddInductive.runWithStats.primitiveWF`), and the whole executable run is verified
without a caller-supplied skeleton or header environment
(`AddInductive.run.primitiveSourceAlignedWF`).
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The skeleton-free primitive header path retains closure of the mutual
families of the kernel environment without claiming validity for the header-only abstract environment. -/
theorem AddInductive.declareInductiveTypes.primitiveHeadersClosedWF
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth nparams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    (Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList)
    (Hclosed : MutualInductivesClosed c.env)
    (Hpresent : ListedConstructorsPresent c.env)
    (hlevels : stats.levels.length = c.lparams.length)
    (hlevelParams : stats.levels = c.lparams.map .param)
    (hindicesSize : stats.nindices.size = indTypes.size)
    (hindices : stats.nindices.toList = Hsemantic.metadata.map Prod.fst)
    (hconsts : stats.indConsts =
      (indTypes.toList.map fun source =>
        .const source.name stats.levels).toArray)
    (hparams : stats.params.size = nparams)
    (hcommonParams : commonParams.length = nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc commonParams depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (hnotzero : stats.isNotZero = stats.resultLevel.isNeverZero)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      isUnsafe)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    (AddInductive.declareInductiveTypes stats nparams indTypes numNested
      isUnsafe c).WF fun outEnv =>
        ∃ decl, ∃ _envTypes : VEnv,
        ∃ _Hheaders : PrimitiveHeaderEnvironment c stats decl nparams
          isUnsafe depth Hc.venv indTypes outEnv,
          MutualInductivesClosed outEnv := by
  let infos := AddInductive.inductiveTypeInfos stats nparams indTypes
    numNested isUnsafe c.lparams
  have Hheaders :=
    AddInductive.declareInductiveTypes.primitiveHeadersWF
      (numNested := numNested) Hsemantic hlevels hlevelParams hindicesSize
      hindices hconsts hparams hcommonParams Hcache Hsuffix Hambient hcommon hnotzero
      Hshape hvisible Hpresent
  have Hproduction := declareInductiveTypeInfos_refines c.allowPrimitive
    infos.toList c.env Hc.checking.tr.map_wf
  change (AddInductive.declareInductiveTypeInfos c.allowPrimitive
    infos.toList c.env).WF _ at Hheaders ⊢
  intro outEnv hout
  rcases Hheaders outEnv hout with ⟨decl, envTypes, Hheader, _⟩
  have Hinfos := Hproduction outEnv hout
  exact ⟨decl, envTypes, Hheader,
    Hinfos.closesMutuals Hclosed
      (inductiveTypeInfos_uniformAll stats nparams indTypes numNested
        isUnsafe c.lparams hindicesSize)
      (inductiveTypeInfos_uniformNumParams stats nparams indTypes numNested
        isUnsafe c.lparams)⟩

/-- The executable primitive header, check and constructor prefix, with its
declaration synthesized from the successful semantic folds. -/
theorem AddInductive.formationCore.primitiveClosedWF
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth nparams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    (Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList)
    (Hclosed : MutualInductivesClosed c.env)
    (Hpresent : ListedConstructorsPresent c.env)
    (hlevels : stats.levels.length = c.lparams.length)
    (hlevelParams : stats.levels = c.lparams.map .param)
    (hindicesSize : stats.nindices.size = indTypes.size)
    (hindices : stats.nindices.toList = Hsemantic.metadata.map Prod.fst)
    (hconsts : stats.indConsts =
      (indTypes.toList.map fun source =>
        .const source.name stats.levels).toArray)
    (hparams : stats.params.size = nparams)
    (hcommonParams : commonParams.length = nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc commonParams depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (hnotzero : stats.isNotZero = stats.resultLevel.isNeverZero)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      isUnsafe)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    (AddInductive.constructorPhase stats nparams indTypes numNested isUnsafe c).WF
      fun out => ∃ decl, ∃ headerEnv : Environment,
        ∃ Hheaders : PrimitiveHeaderEnvironment c stats decl nparams
          isUnsafe depth Hc.venv indTypes headerEnv,
        ∃ R : PrimitiveConstructorCheck Hheaders out.1,
          R.classes = out.2 ∧ MutualInductivesClosed out.1 := by
  have Hheaders :=
    AddInductive.declareInductiveTypes.primitiveHeadersClosedWF
      (numNested := numNested) Hsemantic Hclosed Hpresent hlevels hlevelParams
      hindicesSize hindices hconsts hparams hcommonParams Hcache Hsuffix
      Hambient hcommon hnotzero Hshape hvisible
  unfold AddInductive.constructorPhase
  exact Hheaders.bind fun headerEnv Hheader => by
    rcases Hheader with ⟨decl, _envTypes, Hheader, hclosedHeader⟩
    exact (AddInductive.primitiveConstructorPhases.WF Hheader Hshape
      hvisible).mono fun out Hresult => by
        rcases Hresult with ⟨R, hclasses⟩
        exact ⟨decl, headerEnv, Hheader, R, hclasses,
          R.declared.closesMutuals hclosedHeader⟩

/-- Complete primitive run-with-stats result with no caller-provided abstract
declaration or header environment. -/
def PrimitiveInstallation
    (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (nparams depth : Nat) (sourceEnv : VEnv)
    (indTypes : Array InductiveType) (isUnsafe : Bool)
    (outEnv : Environment) : Prop :=
  ∃ decl, ∃ ctorEnv,
    ∃ R : ConstructorCheck c stats decl nparams isUnsafe depth
        sourceEnv indTypes ctorEnv,
      Nonempty (RecursorCheck R outEnv)

/-- Skeleton-free primitive formation rejoins the common recursor suffix only
after the atomic constructor installation has restored a valid context. -/
theorem AddInductive.runWithStats.primitiveWF
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth nparams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {commonParams : List VExpr} {commonLevel : VLevel}
    (Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList)
    (Hclosed : MutualInductivesClosed c.env)
    (Hpresent : ListedConstructorsPresent c.env)
    (hlevels : stats.levels.length = c.lparams.length)
    (hlevelParams : stats.levels = c.lparams.map .param)
    (hindicesSize : stats.nindices.size = indTypes.size)
    (hindices : stats.nindices.toList = Hsemantic.metadata.map Prod.fst)
    (hconsts : stats.indConsts =
      (indTypes.toList.map fun source =>
        .const source.name stats.levels).toArray)
    (hparams : stats.params.size = nparams)
    (hcommonParams : commonParams.length = nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc commonParams depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (hnotzero : stats.isNotZero = stats.resultLevel.isNeverZero)
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      isUnsafe)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hlparams : c.lparams.Nodup)
    {hsourceSafety : isUnsafe = (c.safety != .safe)}
    (hnotPartial : c.safety ≠ .partial) :
    (AddInductive.runWithStats stats nparams indTypes numNested isUnsafe c).WF
      (PrimitiveInstallation c stats nparams depth Hc.venv
        indTypes isUnsafe) := by
  unfold AddInductive.runWithStats
  have Hformation :=
    AddInductive.formationCore.primitiveClosedWF
      (numNested := numNested) Hsemantic Hclosed Hpresent hlevels hlevelParams
      hindicesSize hindices
      hconsts hparams hcommonParams Hcache Hsuffix Hambient hcommon hnotzero Hshape
      hvisible
  refine Hformation.bind fun out Hresult => ?_
  obtain ⟨ctorEnv, positivity⟩ := out
  rcases Hresult with ⟨decl, _headerEnv, Hheaders, R, hclasses, hclosed⟩
  have Hmaterialized := Hheaders.sourceStatsWF
  rw [Hheaders.sourceContextVEnv] at Hmaterialized
  exact (R.toConstructorCheck.recursorPhasesWF (hsourceSafety := hsourceSafety) hclosed hlparams
    (Hshape.checkedLiteralDisjoint Hheaders.translation
      Hmaterialized).available
    hnotPartial
    (fun _hallow owner howner =>
      Hshape.recursorsNonprimitive owner howner) hclasses.symm).mono
        fun outEnv Hrecursors =>
          show PrimitiveInstallation c stats nparams depth
              Hc.venv indTypes isUnsafe outEnv
          from ⟨decl, ctorEnv, R.toConstructorCheck, Hrecursors⟩

/-- Source-aligned primitive result, retaining the exact abstract model from
which the executable header traversal began. -/
def PrimitiveRunResult
    (source : AddInductive.Context) (sourceEnv : VEnv) (nparams : Nat)
    (types : List InductiveType)
    (outEnv : Environment) : Prop :=
  ∃ c' stats depth commonParams commonLevel,
    ∃ Hc' : ContextWF c',
    c'.env = source.env ∧
    c'.safety = source.safety ∧
    c'.lparams = source.lparams ∧
    c'.allowPrimitive = source.allowPrimitive ∧
    c'.fuel = source.fuel ∧
    Hc'.venv = sourceEnv ∧
    ∃ _Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        Hc'.venv c'.lparams nparams commonParams commonLevel
          types.toArray.toList,
    ∃ _Hshape : PrimitiveInductiveShape c'.lparams nparams
      types.toArray.toList (source.safety != .safe),
      PrimitiveInstallation c' stats nparams depth Hc'.venv
        types.toArray (source.safety != .safe) outEnv

/-- The complete executable primitive checker, with no caller-supplied
declaration skeleton, constructor targets, or abstract header environment. -/
theorem AddInductive.run.primitiveSourceAlignedWF
    (nparams numNested : Nat)
    (Hc : ContextWF c)
    (Hclosed : MutualInductivesClosed c.env)
    (Hpresent : ListedConstructorsPresent c.env)
    (Hshape : PrimitiveInductiveShape c.lparams nparams
      types.toArray.toList (c.safety != .safe))
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < types.toArray.size)
    (HnotPartial : c.safety ≠ .partial) :
    (AddInductive.run nparams types numNested c).WF
      (PrimitiveRunResult c Hc.venv
        nparams types) := by
  have Hduplicates :
      (Kernel.Environment.checkDuplicatedUnivParams c.lparams).WF
        fun _ => c.lparams.Nodup :=
    Kernel.Environment.checkDuplicatedUnivParams.WF c.lparams
  have Hcombined := Hduplicates.bind fun _ hnodup => by
    apply
      checkInductiveTypes.loopInd.checkInductiveTypes.accumulatesHeadersSourceAligned
        (fun stats => AddInductive.runWithStats stats nparams
          types.toArray numNested (c.safety != .safe))
        (PrimitiveRunResult c Hc.venv
          nparams types)
        Hc hctx hnonempty Lean4Lean.consumeTypeAnnotationsCompat
    intro c' stats depth commonParams commonLevel Hc' henv hsafety
      hlparams hallowPrimitive hfuel hvenv Hsemantic
      hlevels hlevelParams hindicesSize hindices _hconstsSize hconsts
      _hnonempty hparams hcommonParams Hcache Hsuffix Hambient hcommon hnotzero
    have Hclosed' : MutualInductivesClosed c'.env := by
      rw [henv]
      exact Hclosed
    have Hpresent' : ListedConstructorsPresent c'.env := by
      rw [henv]
      exact Hpresent
    have hvisible : c'.safety ≤
        (if c.safety != .safe then DefinitionSafety.unsafe else .safe) := by
      rw [hsafety]
      cases h : c.safety with
      | «unsafe» => simp
      | safe => simp
      | «partial» => exact (HnotPartial h).elim
    have Hshape' : PrimitiveInductiveShape c'.lparams nparams
        types.toArray.toList (c.safety != .safe) := by
      simpa [hlparams] using Hshape
    have hlparamsNodup : c'.lparams.Nodup := by
      rw [hlparams]
      exact hnodup
    have hnotPartial : c'.safety ≠ .partial := by
      simpa [hsafety] using HnotPartial
    exact (AddInductive.runWithStats.primitiveWF
      (hsourceSafety := by rw [hsafety]) (numNested := numNested) Hsemantic Hclosed' Hpresent' hlevels hlevelParams
      hindicesSize hindices hconsts hparams hcommonParams Hcache Hsuffix
      Hambient hcommon hnotzero Hshape' hvisible hlparamsNodup
      hnotPartial).mono
        fun outEnv Hrun =>
          ⟨c', stats, depth, commonParams, commonLevel, Hc', henv, hsafety,
            hlparams, hallowPrimitive, hfuel, hvenv, Hsemantic, Hshape',
            Hrun⟩
  simpa [AddInductive.run] using Hcombined

end VerifyInductive
end Lean4Lean
