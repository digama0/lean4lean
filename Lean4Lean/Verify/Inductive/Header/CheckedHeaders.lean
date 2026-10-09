import Lean4Lean.Verify.Inductive.Header.Translation
import Lean4Lean.Verify.Inductive.Header.Block

/-!
# The checked headers of a mutual block

`CheckedHeaders` is the ordered accumulator of the header phase: for each source family its
checked translation and its `HeaderFormation`, independent of any declaration skeleton. From
it the file builds the header-only declaration (`headerDecl`), its `HeaderCertificate`, and
the `HeaderStatsWF` result that the constructor phase starts from (`checkedResult`).
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive
namespace checkInductiveTypes.loopType

def headerSkeleton (target : VConstVal) : VInductiveTypeSkeleton where
  toVConstVal := target
  ctors := []

/-- Constructor payloads are irrelevant to header formation.  A synthesized
header can therefore be attached to the final skeleton once its constructor
targets have been recovered. -/
theorem HeaderFormation.retarget
    (H : HeaderFormation env Us uvars nparams params source
      nindices resultLevel)
    (htarget : target.toVConstVal = source.toVConstVal) :
    HeaderFormation env Us uvars nparams params target
      nindices resultLevel where
  parameterCount := H.parameterCount
  levelCount := H.levelCount
  normalizedSource := H.normalizedSource
  normalizedShape := by
    rcases source with ⟨sourceVal, sourceCtors⟩
    rcases target with ⟨targetVal, targetCtors⟩
    simp only at htarget
    subst targetVal
    exact H.normalizedShape
  typeShape decl huvars hnparams := by
    have Hshape := H.typeShape decl huvars hnparams
    rcases source with ⟨sourceVal, sourceCtors⟩
    rcases target with ⟨targetVal, targetCtors⟩
    simp only at htarget
    subst targetVal
    exact Hshape

/-- One source-aligned semantic header payload.  Its constructor list is
deliberately empty; `retarget` attaches the same proof to the final
constructor-bearing skeleton. -/
structure CheckedHeader
    (env : VEnv) (Us : List Name) (nparams : Nat)
    (params : List VExpr) (commonLevel : VLevel)
    (source : InductiveType) where
  target : VConstVal
  numIndices : Nat
  resultLevel : VLevel
  translation : TrSourceConst env Us source.name source.type target
  formation : HeaderFormation env Us Us.length nparams params
    (headerSkeleton target) numIndices resultLevel
  commonLevel : resultLevel ≈ commonLevel

def CheckedHeader.headerType
    (H : CheckedHeader env Us nparams params
      commonResultLevel source) : VInductiveType :=
  (headerSkeleton H.target).toVInductiveType H.numIndices H.resultLevel

/-- Ordered semantic outputs of the skeleton-free mutual-header traversal. -/
structure CheckedHeaders
    (env : VEnv) (Us : List Name) (nparams : Nat)
    (params : List VExpr) (commonLevel : VLevel)
    (sources : List InductiveType) where
  payloads : List (Sigma fun source =>
    CheckedHeader env Us nparams params commonLevel source)
  sourceOrder : payloads.map Sigma.fst = sources

namespace CheckedHeaders

/-- Retarget only the source-list index along an exact ordering equality.
The semantic payloads themselves are copied definitionally, so projections
such as `metadata` remain reducible across the reindexing. -/
def reindexSources
    (H : CheckedHeaders env Us nparams params
      commonLevel sources)
    (h : sources = sources') :
    CheckedHeaders env Us nparams params
      commonLevel sources' where
  payloads := H.payloads
  sourceOrder := H.sourceOrder.trans h

/-- Retarget universe-parameter names along equality without changing any
recovered semantic data. -/
def reindexUs
    (H : CheckedHeaders env Us nparams params
      commonLevel sources)
    (h : Us = Us') :
    CheckedHeaders env Us' nparams params
      commonLevel sources := by
  cases h
  exact H

def first (source : InductiveType) (target : VConstVal)
    (numIndices : Nat) (resultLevel : VLevel)
    (Htranslation : TrSourceConst env Us source.name source.type target)
    (Hsynthesized : HeaderFormation env Us Us.length nparams params
      (headerSkeleton target) numIndices resultLevel) :
    CheckedHeaders env Us nparams params
      resultLevel [source] where
  payloads := [⟨source, target, numIndices, resultLevel, Htranslation,
    Hsynthesized, by rfl⟩]
  sourceOrder := rfl

def snoc
    (H : CheckedHeaders env Us nparams params
      commonLevel sources)
    (source : InductiveType) (target : VConstVal)
    (numIndices : Nat) (resultLevel : VLevel)
    (Htranslation : TrSourceConst env Us source.name source.type target)
    (Hsynthesized : HeaderFormation env Us Us.length nparams params
      (headerSkeleton target) numIndices resultLevel)
    (hlevel : resultLevel ≈ commonLevel) :
    CheckedHeaders env Us nparams params
      commonLevel (sources ++ [source]) where
  payloads := H.payloads ++ [⟨source, target, numIndices, resultLevel,
    Htranslation, Hsynthesized, hlevel⟩]
  sourceOrder := by simp [H.sourceOrder]

def headers
    (H : CheckedHeaders env Us nparams params
      commonLevel sources) :
    HeaderTranslations env Us sources := by
  have go : ∀ payloads : List (Sigma fun source =>
      CheckedHeader env Us nparams params commonLevel
        source),
      List.Forall₂
        (fun source target =>
          TrSourceConst env Us source.name source.type target)
        (payloads.map Sigma.fst)
        (payloads.map fun payload => payload.2.target) := by
    intro payloads
    induction payloads with
    | nil => exact .nil
    | cons payload payloads ih =>
      rcases payload with ⟨source, payload⟩
      exact .cons payload.translation ih
  refine {
    targets := H.payloads.map fun payload => payload.2.target
    translations := ?_ }
  exact Eq.mp (congrArg (fun orderedSources =>
    List.Forall₂
      (fun source target =>
        TrSourceConst env Us source.name source.type target)
      orderedSources (H.payloads.map fun payload => payload.2.target))
    H.sourceOrder) (go H.payloads)

def metadata
    (H : CheckedHeaders env Us nparams params
      commonLevel sources) : List (Nat × VLevel) :=
  H.payloads.map fun payload =>
    (payload.2.numIndices, payload.2.resultLevel)

@[simp] theorem metadata_reindexSources
    (H : CheckedHeaders env Us nparams params
      commonLevel sources) (h : sources = sources') :
    (H.reindexSources h).metadata = H.metadata := rfl

@[simp] theorem metadata_reindexUs
    (H : CheckedHeaders env Us nparams params
      commonLevel sources) (h : Us = Us') :
    (H.reindexUs h).metadata = H.metadata := by cases h; rfl

@[simp] theorem metadata_snoc
    (H : CheckedHeaders env Us nparams params
      commonLevel sources)
    (source : InductiveType) (target : VConstVal)
    (nindices : Nat) (resultLevel : VLevel)
    (Htranslation : TrSourceConst env Us source.name source.type target)
    (Hsynthesized : HeaderFormation env Us Us.length nparams params
      (headerSkeleton target) nindices resultLevel)
    (hlevel : resultLevel ≈ commonLevel) :
    (H.snoc source target nindices resultLevel Htranslation Hsynthesized
      hlevel).metadata = H.metadata ++ [(nindices, resultLevel)] := by
  simp [snoc, metadata]

/-- The header-phase declaration has the final family constants and semantic
metadata, but deliberately no constructor constants yet. -/
def headerDecl
    (H : CheckedHeaders env Us nparams params
      commonLevel sources)
    (isUnsafe : Bool) : VInductDecl where
  uvars := Us.length
  nparams := nparams
  types := H.payloads.map fun payload => payload.2.headerType
  isUnsafe := isUnsafe

@[simp] theorem headerDecl_typeConstants
    (H : CheckedHeaders env Us nparams params
      commonLevel sources) :
    (H.headerDecl isUnsafe).typeConstants = H.headers.targets := by
  simp [headerDecl, VInductDecl.typeConstants,
    CheckedHeader.headerType, headerSkeleton, headers]
  intro payload _hpayload
  rcases payload with ⟨source, payload⟩
  rfl

/-- The retained per-family synthesis proofs assemble directly into the
abstract header certificate for the header-only declaration.  In particular
each `normalizedSource` remains available through the originating payload. -/
def headerCertificate
    (H : CheckedHeaders env Us nparams params
      commonLevel sources)
    (isUnsafe : Bool) : HeaderCertificate env (H.headerDecl isUnsafe) where
  params := params
  resultLevel := commonLevel
  commonLevels type htype := by
    simp only [headerDecl, List.mem_map] at htype
    rcases htype with ⟨payload, _hpayload, rfl⟩
    exact payload.2.commonLevel
  typeShapes type htype := by
    simp only [headerDecl, List.mem_map] at htype
    rcases htype with ⟨payload, _hpayload, rfl⟩
    exact payload.2.formation.typeShape (H.headerDecl isUnsafe) rfl rfl

/-- Attach the semantic payloads to any constructor-bearing skeleton with
the same ordered header constants. -/
theorem toFormationPrefix
    (H : CheckedHeaders env Us nparams params
      commonLevel sources)
    (skeleton : VInductDeclSkeleton)
    (huvars : skeleton.uvars = Us.length)
    (hnparams : skeleton.nparams = nparams)
    (hparams : params.length = skeleton.nparams)
    (htypes : skeleton.typeConstants = H.headers.targets) :
    HeaderFormations env Us skeleton params commonLevel H.metadata
      skeleton.types.length := by
  have hpayloadLength : H.payloads.length = skeleton.types.length := by
    have hlength := congrArg List.length htypes
    simpa [VInductDeclSkeleton.typeConstants, headers] using hlength.symm
  refine {
    parameterCount := hparams
    covered := Nat.le_refl _
    checked := ?_ }
  apply List.forall₂_of_getElem
  · simp [metadata, hpayloadLength]
  · intro i hiType hiData
    have hiSkeleton : i < skeleton.types.length := by simpa using hiType
    have hiPayload : i < H.payloads.length := by
      simpa [hpayloadLength] using hiSkeleton
    let payload := H.payloads[i]
    have htarget : skeleton.types[i].toVConstVal = payload.2.target := by
      have hget := congrArg (fun values => values[i]?) htypes
      simp [VInductDeclSkeleton.typeConstants, headers,
        hiPayload] at hget
      rcases hget with ⟨target, htarget, hvalue⟩
      rw [List.getElem?_eq_getElem hiSkeleton] at htarget
      have := Option.some.inj htarget
      subst target
      simpa [payload] using hvalue
    have hmetadata : H.metadata[i] =
        (payload.2.numIndices, payload.2.resultLevel) := by
      simp [metadata, payload]
    have Hheader := payload.2.formation.retarget htarget
    rw [hmetadata]
    exact {
      header := by simpa [huvars, hnparams] using Hheader
      commonLevel := payload.2.commonLevel }

end CheckedHeaders

end checkInductiveTypes.loopType
end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

namespace checkInductiveTypes.loopInd

/-- Retarget the runtime scope of a header result (`HeaderStatsWF`) along exact
scope equality.  Data projections are preserved definitionally after
eliminating the equality, which avoids opaque dependent casts at installed
environment boundaries. -/
def HeaderStatsWF.retargetScope
    (H : HeaderStatsWF env Us Δ stats decl depth)
    (h : Δ = Δ') : HeaderStatsWF env Us Δ' stats decl depth := by
  cases h
  exact H

@[simp] theorem HeaderStatsWF.retargetScope_headers_params
    (H : HeaderStatsWF env Us Δ stats decl depth)
    (h : Δ = Δ') :
    (H.retargetScope h).headers.params = H.headers.params := by
  cases h
  rfl

@[simp] theorem HeaderStatsWF.retargetScope_parameterScope
    (H : HeaderStatsWF env Us Δ stats decl depth)
    (h : Δ = Δ') :
    (H.retargetScope h).parameterScope = H.parameterScope := by
  cases h
  rfl

@[simp] theorem HeaderStatsWF.mono_parameterScope
    (H : HeaderStatsWF env Us Δ stats decl depth)
    (henv : env ≤ env') :
    (H.mono henv).parameterScope = H.parameterScope := rfl

@[simp] theorem HeaderStatsWF.mono_headers_params
    (H : HeaderStatsWF env Us Δ stats decl depth)
    (henv : env ≤ env') :
    (H.mono henv).headers.params = H.headers.params := rfl

end checkInductiveTypes.loopInd

namespace checkInductiveTypes.loopType

/-- Every source telescope retained by semantic accumulation is indexed by
the corresponding family of the header-only declaration. -/
theorem CheckedHeaders.normalizedSourceAt
    (H : CheckedHeaders env Us nparams params
      commonLevel sources)
    (i : Nat) (hi : i < (H.headerDecl isUnsafe).types.length) :
    Nonempty (HeaderSourceTelescope env Us params
      (H.headerDecl isUnsafe).nparams
      (H.headerDecl isUnsafe).types[i].numIndices) := by
  have hiPayload : i < H.payloads.length := by
    simpa [CheckedHeaders.headerDecl] using hi
  let payload := H.payloads[i]
  simpa [CheckedHeaders.headerDecl,
    CheckedHeader.headerType,
    VInductiveTypeSkeleton.toVInductiveType, payload, hiPayload] using
      payload.2.formation.normalizedSource

/-- The skeleton-free header fold retains the concrete source telescope and
its exact semantic family shape from the same checked replay. -/
theorem CheckedHeaders.normalizedShapeAt
    (H : CheckedHeaders env Us nparams params
      commonLevel sources)
    (i : Nat) (hi : i < (H.headerDecl isUnsafe).types.length) :
    ∃ sourceTelescope : HeaderSourceTelescope env Us params
        (H.headerDecl isUnsafe).nparams
        (H.headerDecl isUnsafe).types[i].numIndices,
      ∃ residual exprType,
        env.IsDefEq Us.length [] (H.headerDecl isUnsafe).types[i].type
          (VExpr.wrapForalls
            (sourceTelescope.ownParams ++ sourceTelescope.indices) residual)
          exprType ∧
        env.IsDefEq Us.length
          (sourceTelescope.indices.reverse ++
            sourceTelescope.ownParams.reverse)
          residual (.sort (H.headerDecl isUnsafe).types[i].resultLevel)
            (.sort (.succ (H.headerDecl isUnsafe).types[i].resultLevel)) := by
  have hiPayload : i < H.payloads.length := by
    simpa [CheckedHeaders.headerDecl] using hi
  let payload := H.payloads[i]
  have htarget : (H.headerDecl isUnsafe).types[i] =
      payload.2.headerType := by
    simp [CheckedHeaders.headerDecl,
      payload]
  rw [htarget]
  simpa [CheckedHeaders.headerDecl,
    CheckedHeader.headerType,
    VInductiveTypeSkeleton.toVInductiveType, headerSkeleton] using
      payload.2.formation.normalizedShape

/-- Recovered semantic metadata is exactly the index-count vector of the
header-only declaration. -/
theorem CheckedHeaders.metadata_numIndices
    (H : CheckedHeaders env Us nparams params
      commonLevel sources) :
    H.metadata.map Prod.fst =
      (H.headerDecl isUnsafe).types.map (·.numIndices) := by
  simp [CheckedHeaders.metadata,
    CheckedHeaders.headerDecl,
    CheckedHeader.headerType,
    VInductiveTypeSkeleton.toVInductiveType]

/-- Header-only family names remain in exact source order. -/
theorem CheckedHeaders.headerDecl_names
    (H : CheckedHeaders env Us nparams params
      commonLevel sources) :
    (H.headerDecl isUnsafe).types.map (·.name) =
      sources.map (·.name) := by
  calc
    (H.headerDecl isUnsafe).types.map (·.name) =
        H.payloads.map (fun payload => payload.2.target.name) := by
      simp [CheckedHeaders.headerDecl,
        CheckedHeader.headerType,
        VInductiveTypeSkeleton.toVInductiveType, headerSkeleton]
    _ = H.payloads.map (fun payload => payload.1.name) := by
      apply List.map_congr_left
      intro payload _hpayload
      exact payload.2.translation.name
    _ = (H.payloads.map Sigma.fst).map (·.name) := by
      simp [List.map_map, Function.comp_def]
    _ = sources.map (·.name) := congrArg (List.map (·.name)) H.sourceOrder

@[simp] theorem CheckedHeaders.headerDecl_types_length
    (H : CheckedHeaders env Us nparams params
      commonLevel sources) :
    (H.headerDecl isUnsafe).types.length = sources.length := by
  simp [CheckedHeaders.headerDecl,
    ← H.sourceOrder]

/-- Pointwise exact header translation projected from semantic accumulation.
This is the constructor-phase lookup interface: it does not expose the
payload sigma representation. -/
theorem CheckedHeaders.headerTranslationAt
    (H : CheckedHeaders env Us nparams params
      commonLevel sources)
    (i : Nat) (hi : i < sources.length) :
    TrSourceConst env Us sources[i].name sources[i].type
      ((H.headerDecl isUnsafe).types[i]'(by
        simpa using hi)).toVConstVal := by
  have hiPayload : i < H.payloads.length := by
    have hlength : H.payloads.length = sources.length := by
      simpa using congrArg List.length H.sourceOrder
    omega
  have hiDecl : i < (H.headerDecl isUnsafe).types.length := by
    simpa using hi
  let payload := H.payloads[i]
  have hsource : payload.1 = sources[i] := by
    have hget := congrArg (fun ordered => ordered[i]?) H.sourceOrder
    simp [hiPayload, hi] at hget
    exact hget
  have htarget :
      ((H.headerDecl isUnsafe).types[i]'hiDecl).toVConstVal =
        payload.2.target := by
    simp [CheckedHeaders.headerDecl,
      CheckedHeader.headerType,
      VInductiveTypeSkeleton.toVInductiveType, headerSkeleton,
      payload]
  rw [← hsource, htarget]
  exact payload.2.translation

/-- The skeleton-free header fold already determines a usable checked header
result before constructor targets are known.
Constructor checking can therefore run against this declaration and produce
those targets without circularly assuming a constructor-bearing skeleton. -/
def CheckedHeaders.checkedResult
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : CheckedHeaders Hc.venv c.lparams
      nparams params commonLevel sources)
    (hlevels : stats.levels.length = c.lparams.length)
    (hlevelParams : stats.levels = c.lparams.map .param)
    (hindices : stats.nindices.toList = H.metadata.map Prod.fst)
    (hconsts : stats.indConsts =
      (sources.map fun source =>
        .const source.name stats.levels).toArray)
    (hparams : stats.params.size = nparams)
    (hparamsLength : params.length = nparams)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats nparams depth)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (Hambient : AmbientParamContext Hc params depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (hnotzero : stats.isNotZero = stats.resultLevel.isNeverZero) :
    checkInductiveTypes.loopInd.HeaderStatsWF
      Hc.venv c.lparams Hc.mlctx.vlctx stats
        (H.headerDecl isUnsafe) depth where
  headers := H.headerCertificate isUnsafe
  normalizedSources := H.normalizedSourceAt
  normalizedShapes := H.normalizedShapeAt
  isNotZero := hnotzero
  commonLevel := hcommon
  levels := hlevels
  levelParams := hlevelParams
  uvars := rfl
  consts := hconsts.trans <| by
    have hnames := H.headerDecl_names (isUnsafe := isUnsafe)
    have := congrArg (fun names =>
      (names.map fun name => Expr.const name stats.levels).toArray)
      hnames.symm
    simpa [List.map_map, Function.comp_def] using this
  indices := hindices.trans H.metadata_numIndices
  params := Hcache.complete
  paramFVars := Hcache.paramFVars
  parameterScope := Hsuffix.parameterDecls
  ambientScope := Hsuffix.ambientDecls
  scopeDecomposition := Hsuffix.context
  ambientLength := Hsuffix.prefixLength
  cachedScope := Hsuffix.cached
  parameterEmbedding := FrontScopeEmbedding.ofParameterSuffix Hc Hsuffix
  paramsContext := Hsuffix.paramsDefEq Hambient <|
    hparamsLength.trans hparams.symm
  suffixParams := by
    rw [← cachedParamVars_eq_paramVars (H.headerDecl isUnsafe)]
    simpa [hparams, CheckedHeaders.headerDecl]
      using Hsuffix.suffixParams

end checkInductiveTypes.loopType
end VerifyInductive
end Lean4Lean
