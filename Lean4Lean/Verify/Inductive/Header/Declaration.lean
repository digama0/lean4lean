import Lean4Lean.Verify.Inductive.Header.Block
import Lean4Lean.Verify.Inductive.Header.CheckedHeaders
import Lean4Lean.Verify.Inductive.Constructor.RawTranslation
import Lean4Lean.Verify.Inductive.Formation

/-!
# The header declaration

Once the constructor phase has translated the constructor types in the header environment,
the checked headers and the constructor targets are joined into one abstract declaration
(`HeaderDeclaration`, `HeaderDeclaration.ofTargetsExact`): its skeleton, the `VInductDecl`
obtained with `withMetadata`, the header translation `TrInductDeclHeaders` and the
`HeaderCertificate`.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Final declaration assembled from the checked headers `Hsemantic` after the installed
header environment has made it possible to translate constructor types.  The semantic prefix
is retained alongside the ordinary header translation so nested lowering can still project
each exact normalized source telescope, and the exact header target list and metadata it was
built from are recorded (`typeConstants`, `metadata_eq`) so the header installation proofs
can be reused without reconstructing target uniqueness. -/
structure HeaderDeclaration
    (env envTypes : VEnv) (Us : List Name) (nparams : Nat)
    (sources : List InductiveType) (isUnsafe : Bool)
    (params : List VExpr) (commonLevel : VLevel)
    (Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        env Us nparams params commonLevel sources) where
  skeleton : VInductDeclSkeleton
  decl : VInductDecl
  metadata : List (Nat × VLevel)
  checked : skeleton.withMetadata metadata = some decl
  formations : checkInductiveTypes.loopType.HeaderFormations
    env Us skeleton params commonLevel metadata skeleton.types.length
  translation : TrInductDeclHeaders env Us nparams sources isUnsafe decl
    envTypes
  headers : HeaderCertificate env decl
  headers_eq : headers = formations.complete checked
  typeConstants : decl.typeConstants = Hsemantic.headers.targets
  metadata_eq : metadata = Hsemantic.metadata

/-- Join the skeleton-free semantic header traversal with the skeleton-free
constructor target traversal.  The only installation premise is precisely
the equation produced by `headersWF`. -/
theorem HeaderDeclaration.ofTargetsExact
    (Hsemantic :
      checkInductiveTypes.loopType.CheckedHeaders
        env Us nparams params commonLevel sources)
    (Hconstructors : RawBlockCtorTranslations envTypes Us sources)
    (hparams : params.length = nparams)
    (htypesAdded : env.addConstVals Hsemantic.headers.targets =
      some envTypes) :
    Nonempty (HeaderDeclaration env envTypes Us nparams sources
      isUnsafe params commonLevel Hsemantic) := by
  let skeleton : VInductDeclSkeleton := {
    uvars := Us.length
    nparams := nparams
    types := assembleInductiveSkeletonTypes Hsemantic.headers.targets
      Hconstructors.targets
    isUnsafe := isUnsafe }
  have htypeConstants : skeleton.typeConstants =
      Hsemantic.headers.targets := by
    change (assembleInductiveSkeletonTypes Hsemantic.headers.targets
      Hconstructors.targets).map
        VInductiveTypeSkeleton.toVConstVal = Hsemantic.headers.targets
    exact assembleInductiveSkeletonTypes_headers
      Hsemantic.headers.translations Hconstructors.translations
  have Hprefix := Hsemantic.toFormationPrefix skeleton rfl rfl
    (by simpa [skeleton] using hparams) htypeConstants
  have hmetadataLength : Hsemantic.metadata.length =
      skeleton.types.length := by
    have hpayloadLength : Hsemantic.payloads.length = sources.length := by
      simpa using congrArg List.length Hsemantic.sourceOrder
    have hheaderLength : Hsemantic.headers.targets.length = sources.length :=
      (List.Forall₂.length_eq
        Hsemantic.headers.translations).symm
    have hconstructorLength : Hconstructors.targets.length = sources.length :=
      (List.Forall₂.length_eq
        Hconstructors.translations).symm
    simp [checkInductiveTypes.loopType.CheckedHeaders.metadata,
      skeleton, assembleInductiveSkeletonTypes, hpayloadLength,
      hheaderLength, hconstructorLength]
  let decl : VInductDecl := {
    uvars := skeleton.uvars
    nparams := skeleton.nparams
    types := List.zipWith (fun type data =>
      type.toVInductiveType data.1 data.2) skeleton.types Hsemantic.metadata
    isUnsafe := skeleton.isUnsafe }
  have Hmaterialized : skeleton.withMetadata Hsemantic.metadata =
      some decl := by
    simp [VInductDeclSkeleton.withMetadata, hmetadataLength, decl]
  have hdeclTypeConstants : decl.typeConstants =
      Hsemantic.headers.targets := by
    rw [← VInductDecl.toSkeleton_typeConstants decl,
      VInductDeclSkeleton.withMetadata_toSkeleton Hmaterialized]
    exact htypeConstants
  exact ⟨{
    skeleton := skeleton
    decl := decl
    metadata := Hsemantic.metadata
    checked := Hmaterialized
    formations := Hprefix
    translation := {
      uvars := rfl
      nparams := rfl
      isUnsafe := rfl
      typesAdded := by rw [hdeclTypeConstants]; exact htypesAdded
      types := VInductDeclSkeleton.withMetadata_forall₂ Hmaterialized
        (assembleInductiveSkeletonTypes_translated
          Hsemantic.headers.translations Hconstructors.translations) }
    headers := Hprefix.complete Hmaterialized
    headers_eq := rfl
    typeConstants := hdeclTypeConstants
    metadata_eq := rfl }⟩

/-- The metadata passed to `withMetadata` is exactly the per-family
index-count vector of the resulting declaration.  This is the
declaration-wide counterpart of `withMetadata_typeAt`, used by the
skeleton-free assembly path. -/
theorem VInductDeclSkeleton.withMetadata_numIndices
    {skeleton : VInductDeclSkeleton} {metadata : List (Nat × VLevel)}
    {decl : VInductDecl}
    (H : skeleton.withMetadata metadata = some decl) :
    metadata.map Prod.fst = decl.types.map (·.numIndices) := by
  have zipIndices : ∀ (types : List VInductiveTypeSkeleton)
      (data : List (Nat × VLevel)), data.length = types.length →
      (List.zipWith (fun type datum =>
        type.toVInductiveType datum.1 datum.2) types data).map
          (·.numIndices) = data.map Prod.fst := by
    intro types data hlength
    induction types generalizing data with
    | nil => simpa using hlength
    | cons type types ih =>
      cases data with
      | nil => simp at hlength
      | cons datum data =>
        simp only [List.length_cons] at hlength
        change datum.1 ::
            (List.zipWith (fun type datum =>
              type.toVInductiveType datum.1 datum.2)
              types data).map (·.numIndices) =
            datum.1 :: data.map Prod.fst
        exact congrArg (List.cons datum.1) (ih data (by omega))
  have hlength := VInductDeclSkeleton.withMetadata_length H
  simp only [VInductDeclSkeleton.withMetadata] at H
  split at H
  · simp only [Option.some.injEq] at H
    subst decl
    exact (zipIndices skeleton.types metadata hlength).symm
  · contradiction

/-- A header-translated declaration preserves family names in source
order, independently of its constructor rows. -/
theorem TrInductDeclHeaders.typeNames
    (H : TrInductDeclHeaders env Us nparams sources isUnsafe decl envTypes) :
    decl.types.map (·.name) = sources.map (·.name) := by
  have go : ∀ {sourceTypes : List InductiveType}
      {targetTypes : List VInductiveType},
      List.Forall₂ (TrInductiveTypeHeaders env envTypes Us)
        sourceTypes targetTypes →
      targetTypes.map (·.name) = sourceTypes.map (·.name) := by
    intro sourceTypes targetTypes Htypes
    induction Htypes with
    | nil => rfl
    | cons Htype _ ih =>
      simp [Htype.header.name, ih]
  exact go H.types

/-- Repackage a header declaration (`HeaderDeclaration`) in the
`HeaderStatsWF` interface.  All executable statistics and context
facts are supplied by the outer fold; the declaration, header certificate and
normalized source telescopes come solely from semantic assembly. -/
def HeaderDeclaration.checkedResult
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    {Hsemantic : checkInductiveTypes.loopType.CheckedHeaders
      Hc.venv c.lparams nparams params commonLevel sources}
    (H : HeaderDeclaration Hc.venv envTypes c.lparams nparams
      sources isUnsafe params commonLevel Hsemantic)
    (hlevels : stats.levels.length = c.lparams.length)
    (hlevelParams : stats.levels = c.lparams.map .param)
    (hindices : stats.nindices.toList = H.metadata.map Prod.fst)
    (hconsts : stats.indConsts =
      (sources.map fun source =>
        .const source.name stats.levels).toArray)
    (hparams : stats.params.size = nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc params depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (hnotzero : stats.isNotZero = stats.resultLevel.isNeverZero) :
    checkInductiveTypes.loopInd.HeaderStatsWF
      Hc.venv c.lparams Hc.mlctx.vlctx
      stats H.decl depth := by
  have hfields := VInductDeclSkeleton.withMetadata_fields H.checked
  refine {
    headers := H.formations.complete H.checked
    normalizedSources :=
      H.formations.normalizedSourceAtChecked H.checked
    normalizedShapes :=
      H.formations.normalizedShapeAtChecked H.checked
    isNotZero := hnotzero
    commonLevel := hcommon
    levels := ?_
    levelParams := hlevelParams
    uvars := ?_
    consts := ?_
    indices := hindices.trans
      (VInductDeclSkeleton.withMetadata_numIndices H.checked)
    params := ?_
    paramFVars := Hcache.paramFVars
    parameterScope := Hsuffix.parameterDecls
    ambientScope := Hsuffix.ambientDecls
    scopeDecomposition := Hsuffix.context
    ambientLength := Hsuffix.prefixLength
    cachedScope := Hsuffix.cached
    parameterEmbedding :=
      checkInductiveTypes.loopType.FrontScopeEmbedding.ofParameterSuffix
        Hc Hsuffix
    paramsContext := ?_
    suffixParams := ?_ }
  · exact hlevels.trans H.translation.uvars.symm
  · exact H.translation.uvars.symm
  · calc
      stats.indConsts =
          (sources.map fun source =>
            .const source.name stats.levels).toArray := hconsts
      _ = (H.decl.types.map fun type =>
            .const type.name stats.levels).toArray := by
        have hnames :=
          Lean4Lean.VerifyInductive.TrInductDeclHeaders.typeNames
            H.translation
        have h := congrArg (fun names =>
          (names.map fun name => Expr.const name stats.levels).toArray)
          hnames.symm
        simpa [List.map_map, Function.comp_def] using h
  · have Hcache' : checkInductiveTypes.loopType.ParameterCachePrefix
        Hc.venv c.lparams Hc.mlctx.vlctx stats H.decl.nparams depth := by
      rw [H.translation.nparams]
      exact Hcache
    exact Hcache'.complete
  · apply Hsuffix.paramsDefEq Hambient
    exact H.formations.parameterCount.trans
      (hfields.2.1.symm.trans (H.translation.nparams.trans hparams.symm))
  · rw [← checkInductiveTypes.loopType.cachedParamVars_eq_paramVars H.decl]
    have hsize : stats.params.size = H.decl.nparams :=
      hparams.trans H.translation.nparams.symm
    simpa [hsize] using Hsuffix.suffixParams

end VerifyInductive
end Lean4Lean
