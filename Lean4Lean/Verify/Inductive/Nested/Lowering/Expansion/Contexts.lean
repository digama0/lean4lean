import Lean4Lean.Verify.Inductive.Nested.Lowering.OccurrenceTyping
import Lean4Lean.Verify.Inductive.Nested.Lowering.Expansion.Formation
import Lean4Lean.Verify.Inductive.Nested.Lowering.AuxiliaryFamilyPositions
import Lean4Lean.Verify.Inductive.Nested.Lowering.AuxiliaryFamilies

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Projection of the lowering relations to nested formation

The resolved lowering relations (`ExprLowering.Resolved`, `ConstructorLowering.Resolved`,
`FamilyLowering.Resolved`) are projected through the translation to the abstract nested
expansion (`VExpr.NestedExprExpansion`) required by `NestedFormationWF`: the lowered
translation of each source family and constructor is the nested expansion of its source
translation (`NestedLoweringOutputClosed.sourceExpansions`; the auxiliary-family counterpart
`LoweredAuxiliaryFamily.abstractExpansion` is stated in `Expansion/AuxiliarySources.lean`,
next to `AuxiliaryFamilySource`).

The ordinary expression translation erases concrete lets by interpreting
their bodies in a `vlet` context.  Consequently the projection induction must
relate those contexts by nested expansion, rather than by literal equality.
-/

/-- The metadata-prefix certificate preserves the result universe as well as
the index count.  `SourcePrefixOfLowered.numIndices` exposes the first
projection; formation needs this second projection at the same exact source
position. -/
theorem VInductDeclSkeleton.withMetadataPrefix_resultLevel
    (skeleton : VInductDeclSkeleton) (expanded source : VInductDecl)
    (hle : skeleton.types.length ≤ expanded.types.length)
    (Hmaterialize : skeleton.withMetadata
      ((expanded.types.take skeleton.types.length).map fun type =>
        (type.numIndices, type.resultLevel)) = some source)
    (i : Nat) (hi : i < skeleton.types.length)
    (hsource : i < source.types.length)
    (hexpanded : i < expanded.types.length) :
    (source.types[i]'hsource).resultLevel =
      (expanded.types[i]'hexpanded).resultLevel := by
  rcases VInductDeclSkeleton.withMetadata_typeAt Hmaterialize hi with
    ⟨data, hdata, hsourceLookup⟩
  have hmetadata :
      ((expanded.types.take skeleton.types.length).map fun type =>
        (type.numIndices, type.resultLevel))[i]? =
        some (expanded.types[i].numIndices,
          expanded.types[i].resultLevel) := by
    simp [hi, hle]
  have hdataEq : data =
      (expanded.types[i].numIndices, expanded.types[i].resultLevel) := by
    rw [hmetadata] at hdata
    exact Option.some.inj hdata.symm
  subst data
  have hsourceEq : source.types[i] =
      skeleton.types[i].toVInductiveType expanded.types[i].numIndices
        expanded.types[i].resultLevel := by
    rw [List.getElem?_eq_getElem hsource] at hsourceLookup
    exact Option.some.inj hsourceLookup
  have hresult := congrArg VInductiveType.resultLevel hsourceEq
  simpa [VInductiveTypeSkeleton.toVInductiveType] using hresult

theorem SourcePrefixOfLowered.resultLevel
    (H : SourcePrefixOfLowered source expanded)
    (hle : source.types.length ≤ expanded.types.length)
    (i : Nat) (hsource : i < source.types.length)
    (hexpanded : i < expanded.types.length) :
    (source.types[i]'hsource).resultLevel =
      (expanded.types[i]'hexpanded).resultLevel := by
  rcases H with ⟨skeleton, Hmaterialize⟩
  have hskeleton : skeleton.types.length = source.types.length :=
    (VInductDeclSkeleton.withMetadata_fields Hmaterialize).2.2.2.symm
  apply VInductDeclSkeleton.withMetadataPrefix_resultLevel skeleton expanded
    source
  · simpa [hskeleton] using hle
  · exact Hmaterialize
  · simpa [hskeleton] using hsource

/-- Compatibility of a leaf relation with entering one additional concrete
binder.  The cutoff records binders internal to the abstract expression. -/
def NestedExpansionLeafLiftCompat
    (leaf : Nat → VExpr → VExpr → Prop) : Prop :=
  ∀ {depth source target} (cutoff : Nat),
    cutoff ≤ depth →
    leaf depth source target →
    leaf (depth + 1) (source.liftN 1 cutoff) (target.liftN 1 cutoff)

/-- The formation leaf is stable under precisely the binder lift exercised by
the structural projection.  Its two trailing application spines are lifted
pointwise, while retaining their recursively nested correspondence. -/
theorem VInductDecl.NestedOccurrenceReplacement.liftDepth
    (H : VInductDecl.NestedOccurrenceReplacement env source generated depth input
      output)
    (cutoff : Nat) (Hcutoff : cutoff ≤ depth) :
    VInductDecl.NestedOccurrenceReplacement env source generated (depth + 1)
      (input.liftN 1 cutoff) (output.liftN 1 cutoff) := by
  exact VInductDecl.NestedOccurrenceReplacement.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun env source generated depth input output _ =>
      ∀ cutoff, cutoff ≤ depth →
        VInductDecl.NestedOccurrenceReplacement env source generated (depth + 1)
          (input.liftN 1 cutoff) (output.liftN 1 cutoff))
    (motive_4 := fun env source generated absoluteDepth input output _ =>
      ∀ relativeDepth, absoluteDepth = source.nparams + relativeDepth →
        ∀ cutoff, cutoff ≤ relativeDepth →
          VInductDecl.NestedExprWFExpansion env source generated
            (source.nparams + (relativeDepth + 1))
            (input.liftN 1 cutoff) (output.liftN 1 cutoff))
    (motive_5 := fun _ _ _ _ _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ => True)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (fun {env sourceTypesEnv source generated depth input output container containerFamily
        auxiliaryFamily sourceParams baseArgs levels auxiliaryLevels
        inputBaseArgs sourceTrailing targetTrailing} HsourceTypes Hinstalled HcontainerFamily
        HauxiliaryFamily HsourceParams HbaseArgs HbaseClosed Hlevels HlevelsWF
        HauxiliaryLevels HauxiliaryType Hconstructors HoutputLevels
        HbaseExpansion Htrailing Hinput Houtput _ihInstalled ihBase ihTrailing
        cutoff Hcutoff => by
      subst input
      subst output
      have Hbase' := ihBase depth rfl cutoff Hcutoff
      have hbaseLift :
          (baseArgs.map fun arg => arg.liftN depth 0).map
              (fun arg => arg.liftN 1 cutoff) =
            baseArgs.map (fun arg => arg.liftN (depth + 1) 0) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro arg _
        exact VExpr.liftN'_liftN' (Nat.zero_le cutoff) Hcutoff
      have Hbase'' :
          VInductDecl.NestedExprWFExpansion env source generated
            (source.nparams + (depth + 1))
            (VExpr.mkApps VInductDecl.nestedTrailingMarker
              (baseArgs.map fun arg => arg.liftN (depth + 1) 0))
            (VExpr.mkApps VInductDecl.nestedTrailingMarker
              (inputBaseArgs.map fun arg => arg.liftN 1 cutoff)) := by
        simpa only [VInductDecl.nestedTrailingMarker, VExpr.liftN_mkApps,
          VExpr.liftN, hbaseLift] using Hbase'
      have Htrailing' := ihTrailing depth rfl cutoff Hcutoff
      have Htrailing'' :
          VInductDecl.NestedExprWFExpansion env source generated
            (source.nparams + (depth + 1))
            (VExpr.mkApps VInductDecl.nestedTrailingMarker
              (sourceTrailing.map fun arg => arg.liftN 1 cutoff))
            (VExpr.mkApps VInductDecl.nestedTrailingMarker
              (targetTrailing.map fun arg => arg.liftN 1 cutoff)) := by
        simpa [VInductDecl.nestedTrailingMarker, VExpr.liftN_mkApps,
          VExpr.liftN] using Htrailing'
      refine .intro
        (inputBaseArgs := inputBaseArgs.map fun arg => arg.liftN 1 cutoff)
        (sourceTrailing := sourceTrailing.map fun arg => arg.liftN 1 cutoff)
        (targetTrailing := targetTrailing.map fun arg => arg.liftN 1 cutoff)
        HsourceTypes Hinstalled HcontainerFamily HauxiliaryFamily HsourceParams HbaseArgs
        HbaseClosed Hlevels HlevelsWF HauxiliaryLevels HauxiliaryType
        Hconstructors HoutputLevels Hbase'' Htrailing'' ?_ ?_
      · simp only [VExpr.liftN_mkApps, VExpr.liftN, List.map_append]
      · simp only [VExpr.liftN_mkApps, VExpr.liftN, List.map_append]
        congr 2
        simp only [VInductDecl.paramVars, List.map_map]
        apply List.map_congr_left
        intro index _
        have Hge : cutoff ≤ depth + index :=
          Nat.le_trans Hcutoff (Nat.le_add_right depth index)
        simp [VExpr.liftN, liftVar, Nat.not_lt_of_ge Hge]
        omega)
    (fun {env source generated depth relativeDepth input output} hdepth
        _Hleaf ihLeaf requestedDepth habsolute cutoff Hcutoff => by
      have hrelative : requestedDepth = relativeDepth := by omega
      subst requestedDepth
      exact .occurrence (by omega) (ihLeaf cutoff Hcutoff))
    (fun relativeDepth _ cutoff _ => .bvar)
    (fun relativeDepth _ cutoff _ => .sort)
    (fun relativeDepth _ cutoff _ => .const)
    (fun _ ihMajor relativeDepth habsolute cutoff Hcutoff => by
      simpa [VExpr.liftN] using
        VInductDecl.NestedExprWFExpansion.proj
          (ihMajor relativeDepth habsolute cutoff Hcutoff))
    (fun _ _ ihFn ihArg relativeDepth habsolute cutoff Hcutoff =>
      .app (ihFn relativeDepth habsolute cutoff Hcutoff)
        (ihArg relativeDepth habsolute cutoff Hcutoff))
    (fun _ _ ihDomain ihBody relativeDepth habsolute cutoff Hcutoff =>
      .lam (ihDomain relativeDepth habsolute cutoff Hcutoff)
        (ihBody (relativeDepth + 1) (by omega) (cutoff + 1) (by omega)))
    (fun _ _ ihDomain ihBody relativeDepth habsolute cutoff Hcutoff =>
      .forallE (ihDomain relativeDepth habsolute cutoff Hcutoff)
        (ihBody (relativeDepth + 1) (by omega) (cutoff + 1) (by omega)))
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    H cutoff Hcutoff

/-- The absolute wrapper is stable under a binder inserted among the
constructor fields.  The arithmetic premise says exactly that the cutoff is
below the common-parameter prefix, ruling out the semantically invalid lift
that would insert a binder inside that prefix. -/
theorem VInductDecl.NestedOccurrenceReplacementAbs.liftFieldDepth
    (H : VInductDecl.NestedOccurrenceReplacementAbs env source generated
      depth input output)
    (cutoff : Nat) (Hcutoff : source.nparams + cutoff ≤ depth) :
    VInductDecl.NestedOccurrenceReplacementAbs env source generated
      (depth + 1) (input.liftN 1 cutoff) (output.liftN 1 cutoff) := by
  rcases H with ⟨relativeDepth, hdepth, Hrelative⟩
  have hrelative : cutoff ≤ relativeDepth := by omega
  refine ⟨relativeDepth + 1, by omega, ?_⟩
  exact
    Lean4Lean.VerifyInductive.VInductDecl.NestedOccurrenceReplacement.liftDepth
      Hrelative cutoff hrelative

/-- Structural nested expansion is stable under entering one surrounding
binder whenever its successful leaves are. -/
theorem VExpr.NestedExprExpansion.liftDepth
    (Hlift : NestedExpansionLeafLiftCompat leaf)
    (H : VExpr.NestedExprExpansion leaf depth source target) (cutoff : Nat)
    (Hcutoff : cutoff ≤ depth) :
    VExpr.NestedExprExpansion leaf (depth + 1)
      (source.liftN 1 cutoff) (target.liftN 1 cutoff) := by
  induction H generalizing cutoff with
  | occurrence Hleaf => exact .occurrence (Hlift cutoff Hcutoff Hleaf)
  | bvar => exact VExpr.NestedExprExpansion.refl leaf _ _
  | sort => exact .sort
  | const => exact .const
  | proj _ ihMajor =>
    simpa [VExpr.liftN] using
      VExpr.NestedExprExpansion.proj
        (ihMajor cutoff Hcutoff)
  | app _ _ ihFn ihArg =>
    simpa [VExpr.liftN] using
      .app (ihFn cutoff Hcutoff) (ihArg cutoff Hcutoff)
  | lam _ _ ihDomain ihBody =>
    simpa [VExpr.liftN, Nat.add_assoc] using
      .lam (ihDomain cutoff Hcutoff)
        (ihBody (cutoff + 1) (Nat.add_le_add_right Hcutoff 1))
  | forallE _ _ ihDomain ihBody =>
    simpa [VExpr.liftN, Nat.add_assoc] using
      .forallE (ihDomain cutoff Hcutoff)
        (ihBody (cutoff + 1) (Nat.add_le_add_right Hcutoff 1))

/-- Translation contexts related by nested expansion.  Lambda declarations
advance concrete binder depth; let declarations retain it and relate the
stored values structurally. -/
inductive NestedExpansionCtx
    (leaf : Nat → VExpr → VExpr → Prop) :
    Nat → VLCtx → VLCtx → Prop
  | nil : NestedExpansionCtx leaf depth [] []
  | vlam
      (Hctx : NestedExpansionCtx leaf depth source target)
      (Htype : VExpr.NestedExprExpansion leaf depth sourceType targetType) :
      NestedExpansionCtx leaf (depth + 1)
        ((ofv, .vlam sourceType) :: source)
        ((ofv, .vlam targetType) :: target)
  | vlet
      (Hctx : NestedExpansionCtx leaf depth source target)
      (Htype : VExpr.NestedExprExpansion leaf depth sourceType targetType)
      (Hvalue : VExpr.NestedExprExpansion leaf depth sourceValue targetValue) :
      NestedExpansionCtx leaf depth
        ((ofv, .vlet sourceType sourceValue) :: source)
        ((ofv, .vlet targetType targetValue) :: target)

/-- The part of an expansion context actually used by expression
translation: corresponding lookups produce an expansion at the current
absolute depth.  Keeping this property explicit lets constructor traversal
start from a leaf-free parameter telescope without postulating that nested
leaves can be lifted through the common-parameter prefix. -/
def NestedExpansionLookupCtx
    (leaf : Nat → VExpr → VExpr → Prop)
    (depth : Nat) (sourceCtx targetCtx : VLCtx) : Prop :=
  ∀ {var sourceValue sourceType targetValue targetType},
    sourceCtx.find? var = some (sourceValue, sourceType) →
    targetCtx.find? var = some (targetValue, targetType) →
    VExpr.NestedExprExpansion leaf depth sourceValue targetValue

/-- Compatibility of a leaf relation with entering one additional concrete
binder below a fixed prefix of `np` binders (the common parameters). -/
def NestedExpansionLeafLiftAbove (np : Nat)
    (leaf : Nat → VExpr → VExpr → Prop) : Prop :=
  ∀ {depth source target} (cutoff : Nat),
    np + cutoff ≤ depth →
    leaf depth source target →
    leaf (depth + 1) (source.liftN 1 cutoff) (target.liftN 1 cutoff)

theorem nestedOccurrenceReplacementAbs_liftAbove :
    NestedExpansionLeafLiftAbove source.nparams
      (VInductDecl.NestedOccurrenceReplacementAbs env source generated) :=
  fun cutoff Hcutoff Hleaf =>
    VInductDecl.NestedOccurrenceReplacementAbs.liftFieldDepth Hleaf cutoff Hcutoff

/-- An expansion whose leaves lift below a prefix of `np` binders can be
lifted below that prefix. -/
theorem VExpr.NestedExprExpansion.liftAbove
    {leaf : Nat → VExpr → VExpr → Prop} (Hlift : NestedExpansionLeafLiftAbove np leaf)
    (H : VExpr.NestedExprExpansion leaf depth input output)
    (cutoff : Nat) (Hcutoff : np + cutoff ≤ depth) :
    VExpr.NestedExprExpansion leaf
      (depth + 1) (input.liftN 1 cutoff) (output.liftN 1 cutoff) := by
  induction H generalizing cutoff with
  | occurrence Hleaf => exact .occurrence (Hlift cutoff Hcutoff Hleaf)
  | bvar => exact VExpr.NestedExprExpansion.refl _ _ _
  | sort => exact .sort
  | const => exact .const
  | proj _ ihMajor =>
    simpa [VExpr.liftN] using
      VExpr.NestedExprExpansion.proj
        (ihMajor cutoff Hcutoff)
  | app _ _ ihFn ihArg =>
    simpa [VExpr.liftN] using
      VExpr.NestedExprExpansion.app (ihFn cutoff Hcutoff)
        (ihArg cutoff Hcutoff)
  | lam _ _ ihDomain ihBody =>
    simpa [VExpr.liftN, Nat.add_assoc] using
      VExpr.NestedExprExpansion.lam (ihDomain cutoff Hcutoff)
        (ihBody (cutoff + 1) (by omega))
  | forallE _ _ ihDomain ihBody =>
    simpa [VExpr.liftN, Nat.add_assoc] using
      VExpr.NestedExprExpansion.forallE (ihDomain cutoff Hcutoff)
        (ihBody (cutoff + 1) (by omega))

theorem NestedExpansionLookupCtx.vlamAbove
    {leaf : Nat → VExpr → VExpr → Prop} (Hlift : NestedExpansionLeafLiftAbove np leaf)
    (Hctx : NestedExpansionLookupCtx leaf depth sourceCtx targetCtx)
    (Hbase : np ≤ depth) :
    NestedExpansionLookupCtx leaf
      (depth + 1) ((ofv, .vlam sourceType) :: sourceCtx)
        ((ofv, .vlam targetType) :: targetCtx) := by
  intro var sourceValue sourceValueType targetValue targetValueType Hsource Htarget
  simp only [VLCtx.find?] at Hsource Htarget
  cases hnext : VLCtx.next ofv var with
  | none =>
    simp only [hnext] at Hsource Htarget
    have hs : (.bvar 0 : VExpr) = sourceValue := by
      simpa [VLocalDecl.value] using congrArg Prod.fst (Option.some.inj Hsource)
    have ht : (.bvar 0 : VExpr) = targetValue := by
      simpa [VLocalDecl.value] using congrArg Prod.fst (Option.some.inj Htarget)
    rw [← hs, ← ht]
    exact .bvar
  | some next =>
    simp [hnext] at Hsource Htarget
    rcases Hsource with ⟨sourceValue', sourceType', Hsource', rfl, rfl⟩
    rcases Htarget with ⟨targetValue', targetType', Htarget', rfl, rfl⟩
    simpa [VLocalDecl.depth] using
      (VExpr.NestedExprExpansion.liftAbove Hlift (Hctx Hsource' Htarget') 0
        (by simpa using Hbase))

theorem NestedExpansionLookupCtx.vlet
    (Hctx : NestedExpansionLookupCtx leaf depth sourceCtx targetCtx)
    (Hvalue : VExpr.NestedExprExpansion leaf depth sourceValue targetValue) :
    NestedExpansionLookupCtx leaf depth
      ((ofv, .vlet sourceType sourceValue) :: sourceCtx)
      ((ofv, .vlet targetType targetValue) :: targetCtx) := by
  intro var foundSource foundSourceType foundTarget foundTargetType Hsource Htarget
  simp only [VLCtx.find?] at Hsource Htarget
  cases hnext : VLCtx.next ofv var with
  | none =>
    simp only [hnext] at Hsource Htarget
    have hs : sourceValue = foundSource := by
      simpa [VLocalDecl.value] using congrArg Prod.fst (Option.some.inj Hsource)
    have ht : targetValue = foundTarget := by
      simpa [VLocalDecl.value] using congrArg Prod.fst (Option.some.inj Htarget)
    simpa [hs, ht] using Hvalue
  | some next =>
    simp [hnext] at Hsource Htarget
    rcases Hsource with ⟨sourceValue', sourceType', Hsource', rfl, rfl⟩
    rcases Htarget with ⟨targetValue', targetType', Htarget', rfl, rfl⟩
    simpa [VLocalDecl.depth] using Hctx Hsource' Htarget'

/-- Corresponding variable lookups in expansion-related contexts return
expansion-related values. -/
theorem NestedExpansionCtx.find?_expansion
    (Hlift : NestedExpansionLeafLiftCompat leaf)
    (Hctx : NestedExpansionCtx leaf depth sourceCtx targetCtx)
    (Hsource : sourceCtx.find? var = some (sourceValue, sourceType))
    (Htarget : targetCtx.find? var = some (targetValue, targetType)) :
    VExpr.NestedExprExpansion leaf depth sourceValue targetValue := by
  induction Hctx generalizing var sourceValue sourceType targetValue targetType with
  | nil => simp [VLCtx.find?] at Hsource
  | @vlam depth source target sourceType' targetType' ofv Hctx Htype ih =>
    simp only [VLCtx.find?] at Hsource Htarget
    cases hnext : VLCtx.next ofv var with
    | none =>
      simp only [hnext] at Hsource Htarget
      have hs : (.bvar 0 : VExpr) = sourceValue := by
        simpa [VLocalDecl.value] using
          congrArg Prod.fst (Option.some.inj Hsource)
      have ht : (.bvar 0 : VExpr) = targetValue := by
        simpa [VLocalDecl.value] using
          congrArg Prod.fst (Option.some.inj Htarget)
      rw [← hs, ← ht]
      exact .bvar
    | some next =>
      simp [hnext] at Hsource Htarget
      rcases Hsource with ⟨sourceValue', sourceType', Hsource', rfl, rfl⟩
      rcases Htarget with ⟨targetValue', targetType', Htarget', rfl, rfl⟩
      simpa [VLocalDecl.depth] using
        VExpr.NestedExprExpansion.liftDepth Hlift
          (ih Hsource' Htarget') 0 (Nat.zero_le _)
  | @vlet depth source target sourceType' targetType' sourceValue'
      targetValue' ofv Hctx Htype Hvalue ih =>
    simp only [VLCtx.find?] at Hsource Htarget
    cases hnext : VLCtx.next ofv var with
    | none =>
      simp only [hnext] at Hsource Htarget
      have hs : sourceValue' = sourceValue := by
        simpa [VLocalDecl.value] using
          congrArg Prod.fst (Option.some.inj Hsource)
      have ht : targetValue' = targetValue := by
        simpa [VLocalDecl.value] using
          congrArg Prod.fst (Option.some.inj Htarget)
      rwa [← hs, ← ht]
    | some next =>
      simp [hnext] at Hsource Htarget
      rcases Hsource with ⟨sourceValue'', sourceType'', Hsource', rfl, rfl⟩
      rcases Htarget with ⟨targetValue'', targetType'', Htarget', rfl, rfl⟩
      simpa [VLocalDecl.depth] using ih Hsource' Htarget'

theorem NestedExpansionLookupCtx.ofFalse
    (Hctx : NestedExpansionCtx (fun _ _ _ => False) depth sourceCtx
      targetCtx) :
    NestedExpansionLookupCtx leaf depth sourceCtx targetCtx := by
  intro var sourceValue sourceType targetValue targetType Hsource Htarget
  have Hfalse : VExpr.NestedExprExpansion (fun _ _ _ => False) depth
      sourceValue targetValue :=
    NestedExpansionCtx.find?_expansion
      (leaf := fun _ (_ : VExpr) (_ : VExpr) => False)
      (fun _ _ Hfalse => False.elim Hfalse) Hctx Hsource Htarget
  exact Hfalse.map (fun Hfalse => False.elim Hfalse)

/-- Expressions whose translation cannot inspect local declarations: no
variables, so translations are unique even when their source and target
contexts differ. -/
inductive TrExprS.ContextFree : Expr → Prop
  | sort : ContextFree (.sort level)
  | const : ContextFree (.const name levels)
  | app : ContextFree fn → ContextFree arg → ContextFree (.app fn arg)
  | lit : ContextFree literal.toConstructor → ContextFree (.lit literal)
  | mdata : ContextFree body → ContextFree (.mdata data body)

/-- The syntactic translation of a context-free expression does not look at the context. -/
theorem TrExprS.ContextFree.trSyn?_eq (Hfree : ContextFree expr) :
    trSyn? lparams Δ₁ expr = trSyn? lparams Δ₂ expr := by
  induction Hfree <;> simp_all [trSyn?]

/-- Translation of a context-free expression is independent of the local
context. -/
theorem TrExprS.ContextFree.translation_unique
    (Hfree : ContextFree expr)
    (Hsource : TrExprS sourceVEnv lparams sourceCtx expr sourceTarget)
    (Htarget : TrExprS targetVEnv lparams targetCtx expr targetTarget) :
    sourceTarget = targetTarget :=
  Option.some.inj <| Hsource.toTrSyn.eval.symm.trans <|
    Hfree.trSyn?_eq.trans Htarget.toTrSyn.eval

theorem TrExprS.ContextFree.natLitToConstructor :
    ∀ n, ContextFree (.natLitToConstructor n)
  | 0 => by
    simp [Expr.natLitToConstructor, Expr.natZero]
    exact .const
  | n + 1 => by
    simp [Expr.natLitToConstructor, Expr.natSucc]
    exact .app .const (.lit (natLitToConstructor n))

theorem TrExprS.ContextFree.strLitToConstructor (string : String) :
    ContextFree (.strLitToConstructor string) := by
  simp only [Expr.strLitToConstructor]
  apply ContextFree.app ContextFree.const
  induction string.toList with
  | nil =>
    simp
    exact .app .const .const
  | cons char chars ih =>
    simp only [List.foldr_cons]
    exact .app
      (.app
        (.app .const .const)
        (.app .const (.lit (natLitToConstructor char.toNat))))
      ih

theorem TrExprS.ContextFree.literal (literal : Literal) :
    ContextFree (.lit literal) := by
  apply ContextFree.lit
  cases literal with
  | natVal n => exact .natLitToConstructor n
  | strVal string => exact .strLitToConstructor string

/-- Two translations of the same concrete expression in expansion-related
contexts are themselves structurally expansion-related.  This is the
identity half of formation projection: it handles unchanged common-parameter
domains, including concrete lets, and delegates only opaque projections. -/
theorem TrExprS.abstractExpansionRelational
    (Hctx : NestedExpansionCtx leaf depth sourceCtx targetCtx)
    (Hlift : NestedExpansionLeafLiftCompat leaf)
    (Hsource : TrExprS sourceVEnv lparams sourceCtx expr sourceTarget)
    (Htarget : TrExprS targetVEnv lparams targetCtx expr targetTarget) :
    VExpr.NestedExprExpansion leaf depth sourceTarget targetTarget := by
  induction Hsource generalizing targetCtx targetTarget depth with
  | bvar HsourceLookup =>
    cases Htarget with
    | bvar HtargetLookup =>
      exact Hctx.find?_expansion Hlift HsourceLookup HtargetLookup
  | fvar HsourceLookup =>
    cases Htarget with
    | fvar HtargetLookup =>
      exact Hctx.find?_expansion Hlift HsourceLookup HtargetLookup
  | sort HsourceLevel =>
    cases Htarget with
    | sort HtargetLevel =>
      cases Option.some.inj (HsourceLevel.symm.trans HtargetLevel)
      exact .sort
  | const _ HsourceLevels _ =>
    cases Htarget with
    | const _ HtargetLevels _ =>
      cases Option.some.inj (HsourceLevels.symm.trans HtargetLevels)
      exact .const
  | app _ _ HsourceFn HsourceArg ihFn ihArg =>
    cases Htarget with
    | app _ _ HtargetFn HtargetArg =>
      exact .app (ihFn Hctx HtargetFn) (ihArg Hctx HtargetArg)
  | lam _ HsourceDomain HsourceBody ihDomain ihBody =>
    cases Htarget with
    | lam _ HtargetDomain HtargetBody =>
      have Hdomain := ihDomain Hctx HtargetDomain
      exact .lam Hdomain
        (ihBody (.vlam Hctx Hdomain) HtargetBody)
  | forallE _ _ HsourceDomain HsourceBody ihDomain ihBody =>
    cases Htarget with
    | forallE _ _ HtargetDomain HtargetBody =>
      have Hdomain := ihDomain Hctx HtargetDomain
      exact .forallE Hdomain
        (ihBody (.vlam Hctx Hdomain) HtargetBody)
  | letE _ HsourceType HsourceValue HsourceBody ihType ihValue ihBody =>
    cases Htarget with
    | letE _ HtargetType HtargetValue HtargetBody =>
      have Htype := ihType Hctx HtargetType
      have Hvalue := ihValue Hctx HtargetValue
      exact ihBody (.vlet Hctx Htype Hvalue) HtargetBody
  | lit _ _ ih =>
    cases Htarget with
    | lit _ HtargetConstructor => exact ih Hctx HtargetConstructor
  | mdata _ ih =>
    cases Htarget with
    | mdata HtargetBody => exact ih Hctx HtargetBody
  | proj HsourceBody HsourceProj ih =>
    cases Htarget with
    | proj HtargetBody HtargetProj =>
      cases HsourceProj
      cases HtargetProj
      exact .proj (ih Hctx HtargetBody)

/-- Relational translation projection at an absolute constructor depth. -/
theorem TrExprS.abstractExpansionAbove
    {source : VInductDecl} {leaf : Nat → VExpr → VExpr → Prop}
    (Hlift : NestedExpansionLeafLiftAbove source.nparams leaf)
    (Hctx : NestedExpansionLookupCtx
      leaf
      depth sourceCtx targetCtx)
    (Hbase : source.nparams ≤ depth)
    (Hsource : TrExprS sourceVEnv lparams sourceCtx expr sourceTarget)
    (Htarget : TrExprS targetVEnv lparams targetCtx expr targetTarget) :
    VExpr.NestedExprExpansion
      leaf
      depth sourceTarget targetTarget := by
  induction Hsource generalizing targetCtx targetTarget depth with
  | bvar HsourceLookup =>
    cases Htarget with
    | bvar HtargetLookup => exact Hctx HsourceLookup HtargetLookup
  | fvar HsourceLookup =>
    cases Htarget with
    | fvar HtargetLookup => exact Hctx HsourceLookup HtargetLookup
  | sort HsourceLevel =>
    cases Htarget with
    | sort HtargetLevel =>
      cases Option.some.inj (HsourceLevel.symm.trans HtargetLevel)
      exact .sort
  | const _ HsourceLevels _ =>
    cases Htarget with
    | const _ HtargetLevels _ =>
      cases Option.some.inj (HsourceLevels.symm.trans HtargetLevels)
      exact .const
  | app _ _ HsourceFn HsourceArg ihFn ihArg =>
    cases Htarget with
    | app _ _ HtargetFn HtargetArg =>
      exact .app (ihFn Hctx Hbase HtargetFn) (ihArg Hctx Hbase HtargetArg)
  | lam _ HsourceDomain HsourceBody ihDomain ihBody =>
    cases Htarget with
    | lam _ HtargetDomain HtargetBody =>
      have Hdomain := ihDomain Hctx Hbase HtargetDomain
      exact .lam Hdomain
        (ihBody (Hctx.vlamAbove Hlift Hbase) (by omega) HtargetBody)
  | forallE _ _ HsourceDomain HsourceBody ihDomain ihBody =>
    cases Htarget with
    | forallE _ _ HtargetDomain HtargetBody =>
      have Hdomain := ihDomain Hctx Hbase HtargetDomain
      exact .forallE Hdomain
        (ihBody (Hctx.vlamAbove Hlift Hbase) (by omega) HtargetBody)
  | letE _ HsourceType HsourceValue HsourceBody ihType ihValue ihBody =>
    cases Htarget with
    | letE _ HtargetType HtargetValue HtargetBody =>
      have Htype := ihType Hctx Hbase HtargetType
      have Hvalue := ihValue Hctx Hbase HtargetValue
      exact ihBody (Hctx.vlet Hvalue) Hbase HtargetBody
  | lit _ _ ih =>
    cases Htarget with
    | lit _ HtargetConstructor => exact ih Hctx Hbase HtargetConstructor
  | mdata _ ih =>
    cases Htarget with
    | mdata HtargetBody => exact ih Hctx Hbase HtargetBody
  | proj HsourceBody HsourceProj ih =>
    cases Htarget with
    | proj HtargetBody HtargetProj =>
      cases HsourceProj
      cases HtargetProj
      exact .proj (ih Hctx Hbase HtargetBody)

theorem TrExprS.forall₂_abstractExpansionAbove
    {source : VInductDecl} {leaf : Nat → VExpr → VExpr → Prop}
    (Hlift : NestedExpansionLeafLiftAbove source.nparams leaf)
    (Hctx : NestedExpansionLookupCtx
      leaf
      depth sourceCtx targetCtx)
    (Hbase : source.nparams ≤ depth)
    (Hsource : List.Forall₂ (TrExprS sourceVEnv lparams sourceCtx)
      concrete sourceTargets)
    (Htarget : List.Forall₂ (TrExprS targetVEnv lparams targetCtx)
      concrete targetTargets) :
    List.Forall₂ (VExpr.NestedExprExpansion
      leaf depth)
      sourceTargets targetTargets := by
  induction Hsource generalizing targetTargets with
  | nil =>
    cases Htarget
    exact .nil
  | cons HsourceHead _ ih =>
    cases Htarget with
    | cons HtargetHead HtargetTail =>
      exact .cons
        (TrExprS.abstractExpansionAbove Hlift Hctx Hbase HsourceHead HtargetHead)
        (ih HtargetTail)

theorem TrExprS.forall₂_abstractExpansionAbsolute
    (Hctx : NestedExpansionLookupCtx
      (VInductDecl.NestedOccurrenceReplacementAbs env source generated)
      depth sourceCtx targetCtx)
    (Hbase : source.nparams ≤ depth)
    (Hsource : List.Forall₂ (TrExprS sourceVEnv lparams sourceCtx)
      concrete sourceTargets)
    (Htarget : List.Forall₂ (TrExprS targetVEnv lparams targetCtx)
      concrete targetTargets) :
    List.Forall₂ (VExpr.NestedExprExpansion
      (VInductDecl.NestedOccurrenceReplacementAbs env source generated) depth)
      sourceTargets targetTargets :=
  TrExprS.forall₂_abstractExpansionAbove nestedOccurrenceReplacementAbs_liftAbove
    Hctx Hbase Hsource Htarget

/-- Pointwise expansion of an application spine lifts to expansion of the
whole application.  The accumulator-general form follows the actual
left-fold definition of `mkApps`. -/
theorem forall₂_mkApps_nestedExprExpansion
    (Hfn : VExpr.NestedExprExpansion leaf depth sourceFn targetFn)
    (Hargs : List.Forall₂ (VExpr.NestedExprExpansion leaf depth)
      sourceArgs targetArgs) :
    VExpr.NestedExprExpansion leaf depth
      (VExpr.mkApps sourceFn sourceArgs) (VExpr.mkApps targetFn targetArgs) := by
  induction Hargs generalizing sourceFn targetFn with
  | nil => simpa [VExpr.mkApps] using Hfn
  | cons Hhead _ ih =>
    simpa [VExpr.mkApps] using ih (.app Hfn Hhead)

/-- Package a structurally related trailing spine under the rigid marker used
by the mutually positive abstract formation judgment. -/
theorem forall₂_nestedTrailingExpansion
    (Hargs : List.Forall₂
      (VExpr.NestedExprExpansion
        (VInductDecl.NestedOccurrenceReplacementAbs env source generated)
        depth)
      sourceArgs targetArgs) :
    VInductDecl.NestedExprWFExpansion env source generated depth
      (VExpr.mkApps VInductDecl.nestedTrailingMarker sourceArgs)
      (VExpr.mkApps VInductDecl.nestedTrailingMarker targetArgs) :=
  nestedExprExpansion_toNestedExprWFExpansion
    (forall₂_mkApps_nestedExprExpansion (.const) Hargs)

/-- Add one selected concrete free variable as an abstract forall binder. -/
def pushSelectedForall (ctx : VLCtx) (binding : FVarId × VExpr) : VLCtx :=
  (some (binding.1, []), .vlam binding.2) :: ctx

@[simp] theorem pushSelectedForall_find_self
    (ctx : VLCtx) (binding : FVarId × VExpr) :
    (pushSelectedForall ctx binding).find? (.inr binding.1) =
      some (.bvar 0, binding.2.lift) := by
  simp [pushSelectedForall]

theorem pushSelectedForall_find_ne
    (hne : binding.1 ≠ fv) :
    (pushSelectedForall ctx binding).find? (.inr fv) =
      (ctx.find? (.inr fv)).map fun value =>
        (value.1.liftN 1 0, value.2.liftN 1 0) := by
  cases hfind : ctx.find? (.inr fv) <;>
    simp [pushSelectedForall, VLCtx.find?, VLCtx.next, hne,
      VLocalDecl.depth, hfind]

/-- Folding fresh selected binders over an existing bound-variable lookup
increments that variable by exactly the number of new forall binders. -/
theorem foldl_pushSelectedForall_find_bvar
    {base : VLCtx} {fv : FVarId} {k : Nat} {type : VExpr}
    (bindings : List (FVarId × VExpr))
    (Hbase : base.find? (.inr fv) = some (.bvar k, type))
    (Hfresh : ∀ binding ∈ bindings, binding.1 ≠ fv) :
    ∃ finalType,
      (bindings.foldl pushSelectedForall base).find? (.inr fv) =
        some (.bvar (k + bindings.length), finalType) := by
  induction bindings generalizing base k type with
  | nil => exact ⟨type, by simpa using Hbase⟩
  | cons binding bindings ih =>
      have hne : binding.1 ≠ fv := Hfresh binding (by simp)
      have Hnext : (pushSelectedForall base binding).find? (.inr fv) =
          some (.bvar (k + 1), type.liftN 1 0) := by
        rw [pushSelectedForall_find_ne hne, Hbase]
        simp [VExpr.liftN]
      rcases ih Hnext (fun next hnext => Hfresh next (by simp [hnext])) with
        ⟨finalType, Hfinal⟩
      exact ⟨finalType, by
        change
          (bindings.foldl pushSelectedForall
            (pushSelectedForall base binding)).find? (.inr fv) =
            some (.bvar (k + (bindings.length + 1)), finalType)
        rw [← show k + 1 + bindings.length =
          k + (bindings.length + 1) by omega]
        exact Hfinal⟩

/-- A selected binder can be recovered at its exact de Bruijn position after
the complete duplicate-free prefix is folded into the translation context. -/
theorem foldl_pushSelectedForall_find_getElem
    (bindings : List (FVarId × VExpr))
    (hnodup : (bindings.map Prod.fst).Nodup)
    (i : Nat) (hi : i < bindings.length) :
    ∃ finalType,
      (bindings.foldl pushSelectedForall base).find?
          (.inr bindings[i].1) =
        some (.bvar (bindings.length - 1 - i), finalType) := by
  induction bindings generalizing base i with
  | nil => simp at hi
  | cons binding bindings ih =>
      rcases List.nodup_cons.mp hnodup with ⟨hhead, htail⟩
      cases i with
      | zero =>
          have Hfresh : ∀ next ∈ bindings, next.1 ≠ binding.1 := by
            intro next hnext heq
            exact hhead (List.mem_map.mpr ⟨next, hnext, heq⟩)
          rcases foldl_pushSelectedForall_find_bvar bindings
              (pushSelectedForall_find_self base binding) Hfresh with
            ⟨finalType, Hfinal⟩
          exact ⟨finalType, by simpa using Hfinal⟩
      | succ i =>
          have hiTail : i < bindings.length := by simpa using hi
          rcases ih htail i hiTail (base := pushSelectedForall base binding)
              with ⟨finalType, Hfinal⟩
          exact ⟨finalType, by
            change
              (bindings.foldl pushSelectedForall
                (pushSelectedForall base binding)).find?
                  (.inr bindings[i].1) =
                some (.bvar (bindings.length - (i + 1)), finalType)
            rw [show bindings.length - (i + 1) =
              bindings.length - 1 - i by omega]
            exact Hfinal⟩

/-- Exact residual view of two translated concrete forall prefixes after
opening them with the same fresh free variables.  The `close` field is the
structural induction that reattaches all translated binder domains. -/
structure OpenedForallPrefixes
    (sourceVEnv targetVEnv : VEnv) (lparams : List Name)
    (leaf : Nat → VExpr → VExpr → Prop)
    (depth arity : Nat) (source target : Expr) (fvars : List FVarId)
    (sourceBaseCtx targetBaseCtx : VLCtx)
    (sourceTarget targetTarget : VExpr) where
  sourceResidual : Expr
  targetResidual : Expr
  sourceCtx : VLCtx
  targetCtx : VLCtx
  sourceResidualTarget : VExpr
  targetResidualTarget : VExpr
  contexts : NestedExpansionCtx leaf (depth + arity) sourceCtx targetCtx
  sourceTranslation : TrExprS sourceVEnv lparams sourceCtx sourceResidual
    sourceResidualTarget
  targetTranslation : TrExprS targetVEnv lparams targetCtx targetResidual
    targetResidualTarget
  sourceResidualData : ∃ residual,
    Expr.ForallTelescope source arity residual ∧
    sourceResidual = residual.instantiateRevList (fvars.map Expr.fvar)
  targetResidualData : ∃ residual,
    Expr.ForallTelescope target arity residual ∧
    targetResidual = residual.instantiateRevList (fvars.map Expr.fvar)
  sourceBindings : List (FVarId × VExpr)
  sourceBindinghostFreeVars : sourceBindings.map Prod.fst = fvars
  sourceContext_eq : sourceCtx =
    sourceBindings.foldl pushSelectedForall sourceBaseCtx
  targetBindings : List (FVarId × VExpr)
  targetBindinghostFreeVars : targetBindings.map Prod.fst = fvars
  targetContext_eq : targetCtx =
    targetBindings.foldl pushSelectedForall targetBaseCtx
  parameterPrefix :
    VExpr.NestedExprExpansion leaf (depth + arity)
        sourceResidualTarget targetResidualTarget →
      VExpr.NestedForallPrefixExpansion leaf depth arity
        sourceTarget targetTarget
  parameterPrefixMap : ∀
      (leaf' : Nat → VExpr → VExpr → Prop),
      (∀ {d source target}, leaf d source target → leaf' d source target) →
      VExpr.NestedExprExpansion leaf' (depth + arity)
        sourceResidualTarget targetResidualTarget →
      VExpr.NestedForallPrefixExpansion leaf' depth arity
        sourceTarget targetTarget

/-- The retained source-prefix equation exposes every selected concrete
parameter as its de Bruijn variable. -/
theorem OpenedForallPrefixes.sourceParameterLookup
    (H : OpenedForallPrefixes sourceVEnv targetVEnv lparams leaf
      depth arity source target fvars sourceBaseCtx targetBaseCtx sourceTarget
      targetTarget)
    (hnodup : fvars.Nodup)
    (i : Nat) (hi : i < fvars.length) :
    ∃ type,
      H.sourceCtx.find? (.inr fvars[i]) =
        some (.bvar (fvars.length - 1 - i), type) := by
  have hbindingsLength : H.sourceBindings.length = fvars.length := by
    simpa using congrArg List.length H.sourceBindinghostFreeVars
  have hiBindings : i < H.sourceBindings.length := by
    simpa [hbindingsLength] using hi
  have hnodupBindings : (H.sourceBindings.map Prod.fst).Nodup := by
    simpa [H.sourceBindinghostFreeVars] using hnodup
  rcases foldl_pushSelectedForall_find_getElem H.sourceBindings
      hnodupBindings i hiBindings (base := sourceBaseCtx) with
    ⟨type, Hlookup⟩
  have hname : H.sourceBindings[i].1 = fvars[i] := by
    have hiMap : i < (H.sourceBindings.map Prod.fst).length := by
      simpa using hiBindings
    have hgets := congrArg (fun names : List FVarId => names[i]?)
      H.sourceBindinghostFreeVars
    rw [List.getElem?_eq_getElem hiMap, List.getElem?_eq_getElem hi] at hgets
    simpa using hgets
  rw [H.sourceContext_eq, ← hname]
  exact ⟨type, by simpa [hbindingsLength] using Hlookup⟩

/-- The retained target-prefix equation exposes every selected concrete
parameter as its de Bruijn variable. -/
theorem OpenedForallPrefixes.targetParameterLookup
    (H : OpenedForallPrefixes sourceVEnv targetVEnv lparams leaf
      depth arity source target fvars sourceBaseCtx targetBaseCtx sourceTarget
      targetTarget)
    (hnodup : fvars.Nodup)
    (i : Nat) (hi : i < fvars.length) :
    ∃ type,
      H.targetCtx.find? (.inr fvars[i]) =
        some (.bvar (fvars.length - 1 - i), type) := by
  have hbindingsLength : H.targetBindings.length = fvars.length := by
    simpa using congrArg List.length H.targetBindinghostFreeVars
  have hiBindings : i < H.targetBindings.length := by
    simpa [hbindingsLength] using hi
  have hnodupBindings : (H.targetBindings.map Prod.fst).Nodup := by
    simpa [H.targetBindinghostFreeVars] using hnodup
  rcases foldl_pushSelectedForall_find_getElem H.targetBindings
      hnodupBindings i hiBindings (base := targetBaseCtx) with
    ⟨type, Hlookup⟩
  have hname : H.targetBindings[i].1 = fvars[i] := by
    have hiMap : i < (H.targetBindings.map Prod.fst).length := by
      simpa using hiBindings
    have hgets := congrArg (fun names : List FVarId => names[i]?)
      H.targetBindinghostFreeVars
    rw [List.getElem?_eq_getElem hiMap, List.getElem?_eq_getElem hi] at hgets
    simpa using hgets
  rw [H.targetContext_eq, ← hname]
  exact ⟨type, by simpa [hbindingsLength] using Hlookup⟩

/-- Exact lookup invariant for the constructor's common parameters while
the residual lowering traversal enters additional field binders. -/
def SelectedParameterTargets
    (fvars : List FVarId) (fieldDepth : Nat) (targetCtx : VLCtx) : Prop :=
  ∀ (i : Nat) (hi : i < fvars.length), ∃ type,
    targetCtx.find? (.inr fvars[i]) =
      some (.bvar (fieldDepth + (fvars.length - 1 - i)), type)

theorem OpenedForallPrefixes.selectedParameterTargets
    (H : OpenedForallPrefixes sourceVEnv targetVEnv lparams leaf
      depth arity source target fvars sourceBaseCtx targetBaseCtx sourceTarget
      targetTarget)
    (hnodup : fvars.Nodup) :
    SelectedParameterTargets fvars 0 H.targetCtx := by
  intro i hi
  simpa using H.targetParameterLookup hnodup i hi

theorem OpenedForallPrefixes.selectedParameterSources
    (H : OpenedForallPrefixes sourceVEnv targetVEnv lparams leaf
      depth arity source target fvars sourceBaseCtx targetBaseCtx sourceTarget
      targetTarget)
    (hnodup : fvars.Nodup) :
    SelectedParameterTargets fvars 0 H.sourceCtx := by
  intro i hi
  simpa using H.sourceParameterLookup hnodup i hi

theorem SelectedParameterTargets.vlam
    (H : SelectedParameterTargets fvars fieldDepth targetCtx) :
    SelectedParameterTargets fvars (fieldDepth + 1)
      ((none, .vlam targetType) :: targetCtx) := by
  intro i hi
  rcases H i hi with ⟨type, Hlookup⟩
  refine ⟨type.liftN 1 0, ?_⟩
  simp [VLCtx.find?, VLCtx.next, VLocalDecl.depth, Hlookup, VExpr.liftN]
  omega

theorem SelectedParameterTargets.vlet
    (H : SelectedParameterTargets fvars fieldDepth targetCtx) :
    SelectedParameterTargets fvars fieldDepth
      ((none, .vlet targetType targetValue) :: targetCtx) := by
  intro i hi
  rcases H i hi with ⟨type, Hlookup⟩
  refine ⟨type, ?_⟩
  simp [VLCtx.find?, VLCtx.next, VLocalDecl.depth, Hlookup]

/-- The executable opening selection, together with the retained target
context lookups, determines the abstract translation of the complete selected
parameter array.  This connects the concrete `As` to the
de-Bruijn prefix required by `NestedOccurrenceReplacement`. -/
theorem SelectedParameterTargets.translatedSelection
    {sourceDecl : VInductDecl}
    (Hselection : CDeclArray lctx As)
    (Hparams : SelectedParameterTargets Hselection.fvars fieldDepth targetCtx)
    (Htargets : List.Forall₂ (TrExprS targetVEnv lparams targetCtx)
      As.toList targets)
    (harity : As.size = sourceDecl.nparams) :
    targets = sourceDecl.paramVars fieldDepth := by
  have hfvarsLength : Hselection.fvars.length = As.size := by
    have hsize := congrArg Array.size Hselection.expressions
    simpa using hsize.symm
  have htargetsLength : targets.length = As.size := by
    simpa using (Lean4Lean.List.Forall₂.length_eq Htargets).symm
  apply List.ext_getElem
  · simp [VInductDecl.paramVars, htargetsLength, ← harity]
  · intro i hiTarget hiParam
    have hiAs : i < As.toList.length := by simpa [htargetsLength] using hiTarget
    have hiFVars : i < Hselection.fvars.length := by
      simpa [hfvarsLength] using hiAs
    have Htranslated := Lean4Lean.List.forall₂_getElem
      Htargets i hiAs hiTarget
    have hsource : As.toList[i] = .fvar Hselection.fvars[i] := by
      have harr : As.toList = Hselection.fvars.map Expr.fvar := by
        simpa using congrArg Array.toList Hselection.expressions
      have hiMap : i < (Hselection.fvars.map Expr.fvar).length := by
        simpa using hiFVars
      have hget := congrArg (fun xs : List Expr => xs[i]?) harr
      rw [List.getElem?_eq_getElem hiAs,
        List.getElem?_eq_getElem hiMap] at hget
      simpa using hget
    rw [hsource] at Htranslated
    cases Htranslated with
    | fvar Hlookup =>
      rcases Hparams i hiFVars with ⟨type, Hcanonical⟩
      have hvalue := congrArg Prod.fst <|
        Option.some.inj (Hlookup.symm.trans Hcanonical)
      simpa [VInductDecl.paramVars, List.getElem_reverse, hfvarsLength,
        harity] using hvalue

/-- Exact abstract output spine selected by one successful replacement.  The
replacement fixes the auxiliary name and universe arguments; the anchored
constructor context fixes the translated common-parameter prefix. -/
structure LoweredOccurrenceSpine
    (Htrace : NodeReplacementResolved prodEnv lctx result.params As input
      state output nextState result finalState)
    (Hselection : CDeclArray lctx As)
    (Htarget : TrExprS targetVEnv lparams targetCtx output targetValue)
    (sourceDecl : VInductDecl) (fieldDepth : Nat) where
  value : InductiveVal
  targetName : Name
  levels : List Level
  auxName : Name
  concreteAuxLevels : List Level
  concreteAuxLevels_eq : concreteAuxLevels = state.lvls
  nested : Expr
  candidate : NestedOccurrence prodEnv state input value
  inputHead : input.getAppFn = .const targetName levels
  replacement : output = mkAppRange
    (mkAppN (.const auxName concreteAuxLevels) As)
    value.numParams input.getAppArgs.size input.getAppArgs
  nested_eq : (nested ==
    ((mkAppRange (.const targetName levels) 0 value.numParams
      input.getAppArgs).abstract As).instantiateRev result.params) = true
  resultLookup : result.aux2nested.find? auxName = some nested
  auxiliaryLevels : List VLevel
  auxiliaryInfo : VConstant
  trailing : List VExpr
  auxiliaryLookup : targetVEnv.constants auxName = some auxiliaryInfo
  auxiliaryConcreteArity : concreteAuxLevels.length = auxiliaryInfo.uvars
  auxiliaryLevelsTranslation :
    concreteAuxLevels.mapM (VLevel.ofLevel lparams) = some auxiliaryLevels
  targetValue_eq : targetValue = VExpr.mkApps (.const auxName auxiliaryLevels)
    (sourceDecl.paramVars fieldDepth ++ trailing)
  trailingTranslation : List.Forall₂ (TrExprS targetVEnv lparams targetCtx)
    (input.getAppArgsList.drop value.numParams) trailing

theorem NodeReplacementResolved.targetSpine
    (Htrace : NodeReplacementResolved prodEnv lctx result.params As input
      state output nextState result finalState)
    (Hselection : CDeclArray lctx As)
    (Harity : As.size = result.params.size)
    (Hparams : SelectedParameterTargets Hselection.fvars fieldDepth targetCtx)
    (hsourceParams : result.params.size = sourceDecl.nparams)
    (Htarget : TrExprS targetVEnv lparams targetCtx output targetValue) :
    Nonempty (LoweredOccurrenceSpine Htrace Hselection Htarget sourceDecl
      fieldDepth) := by
  rcases Htrace.mapping with
    ⟨value, targetName, levels, auxName, concreteAuxLevels, nested,
      Hcandidate, hauxLevels, hhead, hreplacement, hnested, hlookup⟩
  have houtput : output = Expr.mkAppList (.const auxName concreteAuxLevels)
      (As.toList ++ input.getAppArgsList.drop value.numParams) := by
    rw [hreplacement]
    rw [Expr.mkAppRange_to_end _ _ _ Hcandidate.parameters.arity]
    rw [Expr.mkAppN_eq_mkAppList, ← Expr.mkAppList_append]
    simp only [Expr.getAppArgs_toList]
  rw [houtput] at Htarget
  rcases Lean4Lean.VerifyInductive.checkPositivityStep.TrExprS.mkAppList_append_inv
      Htarget with
    ⟨headTarget, parameterTargets, trailing, HheadTarget,
      HparameterTargets, Htrailing, htarget⟩
  cases HheadTarget with
  | const HauxLookup HauxLevels HauxArity =>
    have hparameters := Hparams.translatedSelection Hselection
      HparameterTargets (Harity.trans hsourceParams)
    exact ⟨{
      value := value
      targetName := targetName
      levels := levels
      auxName := auxName
      concreteAuxLevels := concreteAuxLevels
      concreteAuxLevels_eq := hauxLevels
      nested := nested
      candidate := Hcandidate
      inputHead := hhead
      replacement := hreplacement
      nested_eq := hnested
      resultLookup := hlookup
      auxiliaryLevels := _
      auxiliaryInfo := _
      trailing := trailing
      auxiliaryLookup := HauxLookup
      auxiliaryConcreteArity := HauxArity
      auxiliaryLevelsTranslation := HauxLevels
      targetValue_eq := by simpa [hparameters] using htarget
      trailingTranslation := Htrailing }⟩

/-- Source-side application spine at the same successful replacement.  This is
obtained solely by splitting the source application at the recognized
container's common-parameter arity. -/
structure SourceOccurrenceSpine
    (targetName : Name) (levels : List Level) (value : InductiveVal)
    (Hsource : TrExprS sourceVEnv lparams sourceCtx input sourceValue) where
  sourceLevels : List VLevel
  baseArgsAtDepth : List VExpr
  trailing : List VExpr
  sourceLevelsTranslation :
    levels.mapM (VLevel.ofLevel lparams) = some sourceLevels
  baseArgsTranslation : List.Forall₂ (TrExprS sourceVEnv lparams sourceCtx)
    (input.getAppArgsList.take value.numParams) baseArgsAtDepth
  trailingTranslation : List.Forall₂ (TrExprS sourceVEnv lparams sourceCtx)
    (input.getAppArgsList.drop value.numParams) trailing
  sourceValue_eq : sourceValue =
    VExpr.mkApps (.const targetName sourceLevels)
      (baseArgsAtDepth ++ trailing)

theorem LoweredOccurrenceSpine.sourceSpine
    {prodEnv : Environment} {lctx : LocalContext}
    {result : Lean4Lean.ElimNestedInductive.Result} {As : Array Expr}
    {input output : Expr} {state nextState finalState :
      Lean4Lean.ElimNestedInductive.State}
    {Htrace : NodeReplacementResolved prodEnv lctx result.params As input
      state output nextState result finalState}
    {Hselection : CDeclArray lctx As}
    {targetVEnv : VEnv} {lparams : List Name} {targetCtx : VLCtx}
    {targetValue : VExpr}
    {Htarget : TrExprS targetVEnv lparams targetCtx output targetValue}
    {sourceDecl : VInductDecl} {fieldDepth : Nat}
    (T : LoweredOccurrenceSpine Htrace Hselection Htarget sourceDecl
      fieldDepth)
    (Hsource : TrExprS sourceVEnv lparams sourceCtx input sourceValue) :
    Nonempty (SourceOccurrenceSpine
      (sourceVEnv := sourceVEnv) (sourceCtx := sourceCtx)
      (sourceValue := sourceValue) (lparams := lparams) (input := input)
      T.targetName T.levels T.value Hsource) := by
  have hinput : input = Expr.mkAppList (.const T.targetName T.levels)
      (input.getAppArgsList.take T.value.numParams ++
        input.getAppArgsList.drop T.value.numParams) := by
    rw [List.take_append_drop]
    exact (Expr.mkAppList_getAppArgsList input).symm.trans (by
      rw [T.inputHead])
  rw [hinput] at Hsource
  rcases Lean4Lean.VerifyInductive.checkPositivityStep.TrExprS.mkAppList_append_inv
      Hsource with
    ⟨headTarget, baseArgsAtDepth, trailing, Hhead, Hbase, Htrailing,
      hsource⟩
  cases Hhead with
  | const _ Hlevels _ =>
    exact ⟨{
      sourceLevels := _
      baseArgsAtDepth := baseArgsAtDepth
      trailing := trailing
      sourceLevelsTranslation := Hlevels
      baseArgsTranslation := Hbase
      trailingTranslation := Htrailing
      sourceValue_eq := hsource }⟩

/-- The exact auxiliary name selected by the translated target spine rejoins
the append-only queue of auxiliary families without any name/equality heuristic. -/
theorem LoweredOccurrenceSpine.resolvedAuxiliaryFamily
    {prodEnv : Environment} {lctx : LocalContext}
    {result : Lean4Lean.ElimNestedInductive.Result} {As : Array Expr}
    {input output : Expr} {state nextState finalState :
      Lean4Lean.ElimNestedInductive.State}
    {Htrace : NodeReplacementResolved prodEnv lctx result.params As input
      state output nextState result finalState}
    {Hselection : CDeclArray lctx As}
    {targetVEnv : VEnv} {lparams : List Name} {targetCtx : VLCtx}
    {targetValue : VExpr}
    {Htarget : TrExprS targetVEnv lparams targetCtx output targetValue}
    {sourceDecl : VInductDecl} {fieldDepth : Nat}
    (T : LoweredOccurrenceSpine Htrace Hselection Htarget sourceDecl
      fieldDepth)
    (Hrun : NestedLowering prodEnv fuel nparams sourceTypes initialState
      (result, runFinalState))
    (Henv : EnvironmentTypesClosed prodEnv)
    (hclosures : MutualInductivesClosed prodEnv)
    (Hsources : SourceSyntaxChecked sourceTypes)
    (hinitialTypes : initialState.newTypes = sourceTypes.toArray)
    (hempty : initialState.nestedAux = #[]) :
    Nonempty (CachedAuxiliaryFamily prodEnv result.params nparams
      initialState.newTypes.size runFinalState T.nested T.auxName) :=
  Hrun.cachedAuxiliaryFamilyOfLookup Henv hclosures Hsources hinitialTypes
    hempty T.resultLookup

/-- Translate a shared concrete forall prefix while replacing its anonymous
de Bruijn binders by one exact duplicate-free list of opening fvars.  This
relates the closed and opened telescopes for constructor lowering: the returned
residual translations live in contexts where `ExprLowering.Resolved`'s opened
tail can be projected directly. -/
theorem Expr.SameForallPrefix.openedAbstractProjection
    (Hsame : Expr.SameForallPrefix arity source target)
    (HsourceEnvWF : sourceVEnv.WF)
    (HtargetEnvWF : targetVEnv.WF)
    (HsourceCtxWF : sourceCtx.WF sourceVEnv lparams.length)
    (HtargetCtxWF : targetCtx.WF targetVEnv lparams.length)
    (Hctx : NestedExpansionCtx leaf depth sourceCtx targetCtx)
    (Hlift : NestedExpansionLeafLiftCompat leaf)
    (Hsource : TrExprS sourceVEnv lparams sourceCtx source sourceTarget)
    (Htarget : TrExprS targetVEnv lparams targetCtx target targetTarget)
    (fvars : List FVarId) (hfvars : fvars.length = arity)
    (hnodup : fvars.Nodup)
    (HsourceFresh : ∀ fv ∈ fvars, fv ∉ sourceCtx.fvars)
    (HtargetFresh : ∀ fv ∈ fvars, fv ∉ targetCtx.fvars) :
    Nonempty (OpenedForallPrefixes sourceVEnv targetVEnv lparams leaf
      depth arity source target fvars sourceCtx targetCtx sourceTarget
      targetTarget) := by
  induction arity generalizing source target depth sourceCtx targetCtx
      sourceTarget targetTarget fvars with
  | zero =>
    cases Hsame with
    | nil =>
    have hfvarsNil : fvars = [] := List.eq_nil_of_length_eq_zero hfvars
    subst fvars
    exact ⟨{
      sourceResidual := source
      targetResidual := target
      sourceCtx := sourceCtx
      targetCtx := targetCtx
      sourceResidualTarget := sourceTarget
      targetResidualTarget := targetTarget
      contexts := by simpa using Hctx
      sourceTranslation := Hsource
      targetTranslation := Htarget
      sourceResidualData := ⟨source, .nil source, by simp⟩
      targetResidualData := ⟨target, .nil target, by simp⟩
      sourceBindings := []
      sourceBindinghostFreeVars := rfl
      sourceContext_eq := rfl
      targetBindings := []
      targetBindinghostFreeVars := rfl
      targetContext_eq := rfl
      parameterPrefix := fun Htail => by simpa using
        VExpr.NestedForallPrefixExpansion.nil Htail
      parameterPrefixMap := by
        intro leaf' Hmap Htail
        simpa using VExpr.NestedForallPrefixExpansion.nil Htail }⟩
  | succ arity ih =>
    cases Hsame with
    | @cons _ sourceBody targetBody name domain bi Htail =>
    cases fvars with
    | nil => simp at hfvars
    | cons fv fvars =>
      cases Hsource with
      | @forallE sourceDomainTarget sourceBodyTarget _ _ _ _ _
          HsourceDomainType HsourceBodyType HsourceDomain HsourceBody =>
        cases Htarget with
        | @forallE targetDomainTarget targetBodyTarget _ _ _ _ _
            HtargetDomainType HtargetBodyType HtargetDomain HtargetBody =>
          have htailLength : fvars.length = arity := by simpa using hfvars
          have htailNodup : fvars.Nodup := (List.nodup_cons.mp hnodup).2
          have hsourceFv : fv ∉ sourceCtx.fvars :=
            HsourceFresh fv (by simp)
          have htargetFv : fv ∉ targetCtx.fvars :=
            HtargetFresh fv (by simp)
          let sourceCtx' : VLCtx :=
            (some (fv, []), .vlam sourceDomainTarget) :: sourceCtx
          let targetCtx' : VLCtx :=
            (some (fv, []), .vlam targetDomainTarget) :: targetCtx
          have HsourceCtxWF' : sourceCtx'.WF sourceVEnv lparams.length := by
            refine ⟨HsourceCtxWF, ?_, HsourceDomainType⟩
            intro other deps heq
            simp at heq
            rcases heq with ⟨rfl, rfl⟩
            exact ⟨hsourceFv, by simp⟩
          have HtargetCtxWF' : targetCtx'.WF targetVEnv lparams.length := by
            refine ⟨HtargetCtxWF, ?_, HtargetDomainType⟩
            intro other deps heq
            simp at heq
            rcases heq with ⟨rfl, rfl⟩
            exact ⟨htargetFv, by simp⟩
          have Hdomain : VExpr.NestedExprExpansion leaf depth
              sourceDomainTarget targetDomainTarget :=
            TrExprS.abstractExpansionRelational Hctx Hlift
              HsourceDomain HtargetDomain
          have Hctx' : NestedExpansionCtx leaf (depth + 1)
              sourceCtx' targetCtx' := by
            exact NestedExpansionCtx.vlam (ofv := some (fv, [])) Hctx Hdomain
          have HsourceBody' : TrExprS sourceVEnv lparams sourceCtx'
              (sourceBody.instantiate1' (.fvar fv)) sourceBodyTarget := by
            exact HsourceBody.inst_fvar HsourceEnvWF.orderedStrong HsourceCtxWF'
          have HtargetBody' : TrExprS targetVEnv lparams targetCtx'
              (targetBody.instantiate1' (.fvar fv)) targetBodyTarget := by
            exact HtargetBody.inst_fvar HtargetEnvWF.orderedStrong HtargetCtxWF'
          have Hsame' : Expr.SameForallPrefix arity
              (sourceBody.instantiate1' (.fvar fv))
              (targetBody.instantiate1' (.fvar fv)) :=
            Htail.instantiate1' (.fvar fv)
          have HsourceFresh' : ∀ other ∈ fvars,
              other ∉ sourceCtx'.fvars := by
            intro other hother
            have hne : other ≠ fv := fun heq =>
              (List.nodup_cons.mp hnodup).1 (heq ▸ hother)
            have hold : other ∉ sourceCtx.fvars :=
              HsourceFresh other (by simp [hother])
            change other ∉ fv :: sourceCtx.fvars
            simp [hne, hold]
          have HtargetFresh' : ∀ other ∈ fvars,
              other ∉ targetCtx'.fvars := by
            intro other hother
            have hne : other ≠ fv := fun heq =>
              (List.nodup_cons.mp hnodup).1 (heq ▸ hother)
            have hold : other ∉ targetCtx.fvars :=
              HtargetFresh other (by simp [hother])
            change other ∉ fv :: targetCtx.fvars
            simp [hne, hold]
          rcases ih Hsame' HsourceCtxWF' HtargetCtxWF'
            Hctx' HsourceBody' HtargetBody' fvars htailLength htailNodup
            HsourceFresh' HtargetFresh' with ⟨Hopened⟩
          rcases Hopened.sourceResidualData with
            ⟨sourceResidual, HsourceTelescope, hsourceResidual⟩
          rcases HsourceTelescope.reflect_instantiate1'_fvar with
            ⟨sourceResidual', HsourceTelescope'⟩
          have HsourceInstantiated :=
            HsourceTelescope'.instantiate1' (.fvar fv) 0
          have hsourceResidual' : sourceResidual =
              sourceResidual'.instantiate1' (.fvar fv) arity :=
            HsourceTelescope.residual_eq (by
              simpa using HsourceInstantiated)
          rcases Hopened.targetResidualData with
            ⟨targetResidual, HtargetTelescope, htargetResidual⟩
          rcases HtargetTelescope.reflect_instantiate1'_fvar with
            ⟨targetResidual', HtargetTelescope'⟩
          have HtargetInstantiated :=
            HtargetTelescope'.instantiate1' (.fvar fv) 0
          have htargetResidual' : targetResidual =
              targetResidual'.instantiate1' (.fvar fv) arity :=
            HtargetTelescope.residual_eq (by
              simpa using HtargetInstantiated)
          exact ⟨{
            sourceResidual := Hopened.sourceResidual
            targetResidual := Hopened.targetResidual
            sourceCtx := Hopened.sourceCtx
            targetCtx := Hopened.targetCtx
            sourceResidualTarget := Hopened.sourceResidualTarget
            targetResidualTarget := Hopened.targetResidualTarget
            contexts := by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                Hopened.contexts
            sourceTranslation := Hopened.sourceTranslation
            targetTranslation := Hopened.targetTranslation
            sourceResidualData := ⟨sourceResidual', .cons HsourceTelescope', by
              rw [hsourceResidual, hsourceResidual']
              have hcomm := Expr.instantiateRevList_instantiate1'_fvars
                sourceResidual' fv fvars 0 0
              simp only [Nat.zero_add, Nat.add_zero] at hcomm
              rw [htailLength] at hcomm
              simpa using hcomm⟩
            targetResidualData := ⟨targetResidual', .cons HtargetTelescope', by
              rw [htargetResidual, htargetResidual']
              have hcomm := Expr.instantiateRevList_instantiate1'_fvars
                targetResidual' fv fvars 0 0
              simp only [Nat.zero_add, Nat.add_zero] at hcomm
              rw [htailLength] at hcomm
              simpa using hcomm⟩
            sourceBindings := (fv, sourceDomainTarget) ::
              Hopened.sourceBindings
            sourceBindinghostFreeVars := by
              simp [Hopened.sourceBindinghostFreeVars]
            sourceContext_eq := by
              simpa [sourceCtx', pushSelectedForall] using
                Hopened.sourceContext_eq
            targetBindings := (fv, targetDomainTarget) ::
              Hopened.targetBindings
            targetBindinghostFreeVars := by
              simp [Hopened.targetBindinghostFreeVars]
            targetContext_eq := by
              simpa [targetCtx', pushSelectedForall] using
                Hopened.targetContext_eq
            parameterPrefix := fun Hresidual =>
              VExpr.NestedForallPrefixExpansion.cons Hdomain
                (Hopened.parameterPrefix (by
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    Hresidual))
            parameterPrefixMap := fun leaf' Hmap Hresidual =>
              VExpr.NestedForallPrefixExpansion.cons (Hdomain.map Hmap)
                (Hopened.parameterPrefixMap leaf' Hmap (by
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    Hresidual)) }⟩

/-- Correct absolute-depth projection used by inductive formation.  Parameter
lookups are supplied by the leaf-free opened telescope; once traversal enters
constructor fields, lookup lifting is justified only below the common
parameter prefix. -/
theorem ExprLowering.Resolved.abstractExpansionAbove
    {sourceDecl : VInductDecl} {leaf : Nat → VExpr → VExpr → Prop}
    {lvls₀ : List Level}
    (Hlift : NestedExpansionLeafLiftAbove sourceDecl.nparams leaf)
    (H : ExprLowering.Resolved prodEnv lctx params As result input state out)
    (hlvls : state.lvls = lvls₀)
    (Hctx : NestedExpansionLookupCtx
      leaf
      depth sourceCtx targetCtx)
    (Hbase : sourceDecl.nparams ≤ depth)
    (Hselection : CDeclArray lctx As)
    (HselectionNodup : Hselection.fvars.Nodup)
    (Harity : As.size = params.size)
    (Hdepth : depth = Hselection.fvars.length + fieldDepth)
    (HsourceParams : SelectedParameterTargets Hselection.fvars fieldDepth
      sourceCtx)
    (Hparams : SelectedParameterTargets Hselection.fvars fieldDepth targetCtx)
    (Hscope : input.FVarsIn (· ∈ Hselection.fvars))
    (Hhit : ∀ {input state output nextState finalState depth fieldDepth
        sourceTarget targetTarget sourceCtx targetCtx},
      NodeReplacementResolved prodEnv lctx params As input state output
        nextState result finalState →
      NestedExpansionLookupCtx
        leaf
        depth sourceCtx targetCtx →
      (selection : CDeclArray lctx As) →
      selection.fvars.Nodup →
      As.size = params.size →
      depth = selection.fvars.length + fieldDepth →
      SelectedParameterTargets selection.fvars fieldDepth sourceCtx →
      SelectedParameterTargets selection.fvars fieldDepth targetCtx →
      input.FVarsIn (· ∈ selection.fvars) →
      TrExprS sourceVEnv lparams sourceCtx input sourceTarget →
      TrExprS targetVEnv lparams targetCtx output targetTarget →
      state.lvls = lvls₀ →
      leaf
        depth sourceTarget targetTarget)
    (Hsource : TrExprS sourceVEnv lparams sourceCtx input sourceTarget)
    (Htarget : TrExprS targetVEnv lparams targetCtx out.1 targetTarget) :
    VExpr.NestedExprExpansion
      leaf
      depth sourceTarget targetTarget := by
  induction H generalizing sourceCtx targetCtx sourceTarget targetTarget depth
      fieldDepth with
  | occurrence Hnode =>
      exact .occurrence (Hhit Hnode Hctx Hselection HselectionNodup Harity Hdepth
        HsourceParams Hparams Hscope Hsource Htarget hlvls)
  | bvar =>
    cases Hsource with
    | bvar HsourceLookup =>
      cases Htarget with
      | bvar HtargetLookup => exact Hctx HsourceLookup HtargetLookup
  | fvar =>
    cases Hsource with
    | fvar HsourceLookup =>
      cases Htarget with
      | fvar HtargetLookup => exact Hctx HsourceLookup HtargetLookup
  | mvar => cases Hsource
  | sort =>
    cases Hsource with
    | sort HsourceLevel =>
      cases Htarget with
      | sort HtargetLevel =>
        cases Option.some.inj (HsourceLevel.symm.trans HtargetLevel)
        exact .sort
  | const =>
    cases Hsource with
    | const _ HsourceLevels _ =>
      cases Htarget with
      | const _ HtargetLevels _ =>
        cases Option.some.inj (HsourceLevels.symm.trans HtargetLevels)
        exact .const
  | lit =>
    have heq : sourceTarget = targetTarget :=
      (TrExprS.ContextFree.literal _).translation_unique Hsource Htarget
    subst targetTarget
    exact VExpr.NestedExprExpansion.refl _ depth sourceTarget
  | @app fn arg state fn' fnState arg' outState Hnode Hfn Harg ihFn ihArg =>
    simp only [Lean4Lean.FVarsIn] at Hscope
    have Htarget' : TrExprS targetVEnv lparams targetCtx (.app fn' arg')
        targetTarget := by simpa [Expr.updateApp!] using Htarget
    cases Hsource with
    | app _ _ HsourceFn HsourceArg =>
      cases Htarget' with
      | app _ _ HtargetFn HtargetArg =>
        exact .app
          (ihFn hlvls Hctx Hbase Hdepth HsourceParams Hparams Hscope.1 HsourceFn
            HtargetFn)
          (ihArg (Hfn.lvls.trans hlvls) Hctx Hbase Hdepth HsourceParams Hparams
            Hscope.2 HsourceArg HtargetArg)
  | @lam name dom body bi state dom' domState body' outState Hnode Hdom
      Hbody ihDom ihBody =>
    have Htarget' : TrExprS targetVEnv lparams targetCtx
        (.lam name dom' body' bi) targetTarget := by
      simpa [Expr.updateLambdaE!] using Htarget
    cases Hsource with
    | lam _ HsourceDom HsourceBody =>
      cases Htarget' with
      | lam _ HtargetDom HtargetBody =>
        simp only [Lean4Lean.FVarsIn] at Hscope
        have HdomExpansion := ihDom hlvls Hctx Hbase Hdepth HsourceParams Hparams
          Hscope.1 HsourceDom HtargetDom
        exact .lam HdomExpansion
          (ihBody (Hdom.lvls.trans hlvls) (Hctx.vlamAbove Hlift Hbase)
            (by omega) (by omega)
            HsourceParams.vlam Hparams.vlam Hscope.2 HsourceBody HtargetBody)
  | @forallE name dom body bi state dom' domState body' outState Hnode Hdom
      Hbody ihDom ihBody =>
    have Htarget' : TrExprS targetVEnv lparams targetCtx
        (.forallE name dom' body' bi) targetTarget := by
      simpa [Expr.updateForallE!] using Htarget
    cases Hsource with
    | forallE _ _ HsourceDom HsourceBody =>
      cases Htarget' with
      | forallE _ _ HtargetDom HtargetBody =>
        simp only [Lean4Lean.FVarsIn] at Hscope
        have HdomExpansion := ihDom hlvls Hctx Hbase Hdepth HsourceParams Hparams
          Hscope.1 HsourceDom HtargetDom
        exact .forallE HdomExpansion
          (ihBody (Hdom.lvls.trans hlvls) (Hctx.vlamAbove Hlift Hbase)
            (by omega) (by omega)
            HsourceParams.vlam Hparams.vlam Hscope.2 HsourceBody HtargetBody)
  | @letE name type value body nondep state type' typeState value'
      valueState body' outState Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    have Htarget' : TrExprS targetVEnv lparams targetCtx
        (.letE name type' value' body' nondep) targetTarget := by
      simpa [Expr.updateLet!] using Htarget
    cases Hsource with
    | letE _ HsourceType HsourceValue HsourceBody =>
      cases Htarget' with
      | letE _ HtargetType HtargetValue HtargetBody =>
        simp only [Lean4Lean.FVarsIn] at Hscope
        have HtypeExpansion := ihType hlvls Hctx Hbase Hdepth HsourceParams Hparams
          Hscope.1 HsourceType HtargetType
        have HvalueExpansion := ihValue (Htype.lvls.trans hlvls) Hctx Hbase Hdepth
          HsourceParams Hparams Hscope.2.1 HsourceValue HtargetValue
        exact ihBody (Hvalue.lvls.trans (Htype.lvls.trans hlvls))
          (Hctx.vlet HvalueExpansion) Hbase Hdepth
          HsourceParams.vlet Hparams.vlet Hscope.2.2 HsourceBody HtargetBody
  | @mdata data body state body' outState Hnode Hbody ihBody =>
    have Htarget' : TrExprS targetVEnv lparams targetCtx (.mdata data body')
        targetTarget := by simpa [Expr.updateMData!] using Htarget
    cases Hsource with
    | mdata HsourceBody =>
      cases Htarget' with
      | mdata HtargetBody =>
        exact ihBody hlvls Hctx Hbase Hdepth HsourceParams Hparams Hscope HsourceBody
          HtargetBody
  | @proj structName index body state body' outState Hnode Hbody ihBody =>
    have Htarget' : TrExprS targetVEnv lparams targetCtx
        (.proj structName index body') targetTarget := by
      simpa [Expr.updateProj!] using Htarget
    cases Hsource with
    | proj HsourceBody HsourceProj =>
      cases Htarget' with
      | proj HtargetBody HtargetProj =>
        cases HsourceProj
        cases HtargetProj
        exact .proj
          (ihBody hlvls Hctx Hbase Hdepth HsourceParams Hparams Hscope HsourceBody
            HtargetBody)

/-- Closing and reopening with the same duplicate-free fvar list is the
identity.  This is the transparent list-facing cancellation theorem needed
for the exact constructor body rebuilt by `LocalContext.mkForall`. -/
theorem _root_.Lean.Expr.reopenFVarsAt_self
    (hnodup : fvars.Nodup) (e : Expr) (k : Nat) :
    Expr.reopenFVarsAt e fvars fvars k = e := by
  induction e generalizing k with
  | bvar i => exact Expr.reopenFVarsAt_bvar rfl i k
  | fvar fv =>
    by_cases hfv : fv ∈ fvars
    · rcases List.mem_iff_getElem.mp hfv with ⟨i, hi, rfl⟩
      exact Expr.reopenFVarsAt_selected hnodup rfl i hi k
    · apply Expr.reopenFVarsAt_eq_self_of_abstract
        (fun depth => Expr.abstractList_fvar_of_not_mem hfv)
        (by simp [Expr.looseBVarRange']) k
  | mvar id | sort id | const id _ | lit id =>
    apply Expr.reopenFVarsAt_of_abstract1_eq_self
      (by intro fv depth; simp [Expr.abstract1])
      (by simp [Expr.looseBVarRange'])
  | app fn arg ihFn ihArg =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_app,
      Expr.instantiateRevList_app]
    change Expr.app (Expr.reopenFVarsAt fn fvars fvars k)
        (Expr.reopenFVarsAt arg fvars fvars k) = Expr.app fn arg
    rw [ihFn k, ihArg k]
  | lam name dom body bi ihDom ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_lam,
      Expr.instantiateRevList_lam]
    change Expr.lam name (Expr.reopenFVarsAt dom fvars fvars k)
        (Expr.reopenFVarsAt body fvars fvars (k + 1)) bi =
      Expr.lam name dom body bi
    rw [ihDom k, ihBody (k + 1)]
  | forallE name dom body bi ihDom ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_forallE,
      Expr.instantiateRevList_forallE]
    change Expr.forallE name (Expr.reopenFVarsAt dom fvars fvars k)
        (Expr.reopenFVarsAt body fvars fvars (k + 1)) bi =
      Expr.forallE name dom body bi
    rw [ihDom k, ihBody (k + 1)]
  | letE name type value body nondep ihType ihValue ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_letE,
      Expr.instantiateRevList_letE]
    change Expr.letE name (Expr.reopenFVarsAt type fvars fvars k)
        (Expr.reopenFVarsAt value fvars fvars k)
        (Expr.reopenFVarsAt body fvars fvars (k + 1)) nondep =
      Expr.letE name type value body nondep
    rw [ihType k, ihValue k, ihBody (k + 1)]
  | mdata data body ihBody =>
    simpa [Expr.reopenFVarsAt, Expr.abstractList_mdata,
      Expr.instantiateRevList_mdata] using congrArg (Expr.mdata data) (ihBody k)
  | proj name index body ihBody =>
    simpa [Expr.reopenFVarsAt, Expr.abstractList_proj,
      Expr.instantiateRevList_proj] using
      congrArg (Expr.proj name index) (ihBody k)

/-- Pointwise structural projection of one constructor lowering.  The exact
source opening, the rebuilt target telescope, and the shared translated
forall prefix determine the same opened residuals used by the operational
mapping; the expression traversal can therefore be projected without an
additional constructor-level semantic premise. -/
theorem ConstructorLowering.Resolved.abstractExpansionAbove
    {sourceDecl : VInductDecl} {leaf : Nat → VExpr → VExpr → Prop}
    {lvls₀ : List Level}
    (Hlift : NestedExpansionLeafLiftAbove sourceDecl.nparams leaf)
    (Hmapping : ConstructorLowering.Resolved prodEnv params nparams result
      sourceConcrete state (targetConcrete, nextState))
    (hlvls : state.lvls = lvls₀)
    (Hsource : TrSourceConstRaw sourceVEnv lparams sourceConcrete.name
      sourceConcrete.type sourceTarget)
    (Htarget : TrSourceConst targetVEnv lparams targetConcrete.name
      targetConcrete.type targetTarget)
    (HsourceEnvWF : sourceVEnv.WF)
    (HtargetEnvWF : targetVEnv.WF)
    (hparamsSize : params.size = nparams)
    (hnparams : nparams = sourceDecl.nparams)
    (HsourceClosed : sourceConcrete.type.FVarsIn fun _ => False)
    (HsourceBVar : Closed sourceConcrete.type)
    (Hhit : ∀ {lctx : LocalContext} {As : Array Expr}
        {input state output nextState finalState depth fieldDepth sourceValue
          targetValue sourceCtx targetCtx},
      NodeReplacementResolved prodEnv lctx params As input state output
        nextState result finalState →
      NestedExpansionLookupCtx
        leaf
        depth sourceCtx targetCtx →
      (selection : CDeclArray lctx As) →
      selection.fvars.Nodup →
      As.size = params.size →
      depth = selection.fvars.length + fieldDepth →
      SelectedParameterTargets selection.fvars fieldDepth sourceCtx →
      SelectedParameterTargets selection.fvars fieldDepth targetCtx →
      input.FVarsIn (· ∈ selection.fvars) →
      TrExprS sourceVEnv lparams sourceCtx input sourceValue →
      TrExprS targetVEnv lparams targetCtx output targetValue →
      state.lvls = lvls₀ →
      leaf
        depth sourceValue targetValue)
    :
    VInductDecl.NestedConstructorExpansion
      leaf
      nparams sourceTarget targetTarget := by
  rcases Hmapping.mapped with
    ⟨lctx, tail, As, lowered, openedState, Hopening, _hlctxWF, Hselection,
      hnodup, _hopenedTypes, _hopenedAux, _hopenedNext, hsize, Hbody,
      htargetType⟩
  have Hsame := Hmapping.sourceTargetSameForallPrefix HsourceClosed HsourceBVar
  rcases Hsame.openedAbstractProjection (depth := 0) HsourceEnvWF HtargetEnvWF
      (by trivial) (by trivial)
      (.nil : NestedExpansionCtx (fun _ _ _ => False) 0 [] [])
      (fun _ _ Hfalse => False.elim Hfalse)
      Hsource.type Htarget.type Hselection.fvars
      (by simpa [Hselection.expressions] using hsize) hnodup
      (by simp) (by simp) with ⟨Hopened⟩
  rcases Hopened.sourceResidualData with
    ⟨sourceResidual, HsourceTelescope, hsourceResidual⟩
  rcases Hopening.forallTelescope with
    ⟨openingResidual, HopeningTelescope⟩
  have hsourceTelescopeResidual : sourceResidual = openingResidual :=
    HsourceTelescope.residual_eq HopeningTelescope
  have htail : tail =
      openingResidual.instantiateRevList
        (Hselection.fvars.map Expr.fvar) := by
    have htail' := Hopening.toParamOpening.forallResidual
      HopeningTelescope
    rw [Hselection.expressions, Expr.instantiateRev_eq,
      Expr.instantiate_eq] at htail'
    simpa [Expr.instantiateList_reverse] using htail'
  have hsourceOpened : Hopened.sourceResidual = tail := by
    rw [hsourceResidual, hsourceTelescopeResidual, htail]
  have HtargetTelescope : Expr.ForallTelescope targetConcrete.type nparams
      (lowered.abstractList Hselection.fvars) := by
    rw [htargetType, ← hsize]
    have hloweredClosed : Closed lowered :=
      Hbody.closed Hselection (Hopening.tailClosed HsourceBVar)
    have h := Hselection.forallTelescope lowered
    rwa [Expr.abstractN_eq_abstractList_of_closed hnodup hloweredClosed] at h
  rcases Hopened.targetResidualData with
    ⟨targetResidual, HtargetTelescope', htargetResidual⟩
  have htargetTelescopeResidual : targetResidual =
      lowered.abstractList Hselection.fvars :=
    HtargetTelescope'.residual_eq HtargetTelescope
  have htargetOpened : Hopened.targetResidual = lowered := by
    rw [htargetResidual, htargetTelescopeResidual]
    exact Expr.reopenFVarsAt_self hnodup lowered 0
  have Hresidual : VExpr.NestedExprExpansion
      leaf
      nparams Hopened.sourceResidualTarget Hopened.targetResidualTarget := by
    have HsourceResidualTranslation : TrExprS sourceVEnv lparams
        Hopened.sourceCtx tail Hopened.sourceResidualTarget := by
      simpa [hsourceOpened] using Hopened.sourceTranslation
    have HtargetResidualTranslation : TrExprS targetVEnv lparams
        Hopened.targetCtx lowered Hopened.targetResidualTarget := by
      simpa [htargetOpened] using Hopened.targetTranslation
    have Hresidual' := Hbody.abstractExpansionAbove Hlift
      (sourceTarget := Hopened.sourceResidualTarget)
      (targetTarget := Hopened.targetResidualTarget)
      (Hbody.lvls.symm.trans (Hmapping.lvls.trans hlvls))
      (NestedExpansionLookupCtx.ofFalse Hopened.contexts)
      (by simp [hnparams]) Hselection hnodup
      (hsize.trans hparamsSize.symm)
      (by have := Hselection.size; omega)
      (Hopened.selectedParameterSources hnodup)
      (Hopened.selectedParameterTargets hnodup)
      (Hopening.tailFVarsIn Hselection
        (HsourceClosed.mono fun _ hfalse => False.elim hfalse)) Hhit
      HsourceResidualTranslation HtargetResidualTranslation
    simpa using Hresidual'
  exact {
    name := by
      calc
        targetTarget.name = targetConcrete.name := Htarget.name
        _ = sourceConcrete.name := Hmapping.name
        _ = sourceTarget.name := Hsource.name.symm
    uvars := Htarget.uvars.trans Hsource.uvars.symm
    parameters := Hopened.parameterPrefixMap _
      (fun Hfalse => False.elim Hfalse) (by simpa using Hresidual) }

/-- State threading is irrelevant after every exact constructor step has
been projected: source and lowered translation lists become an ordered
constructor expansion. -/
theorem ConstructorLowerings.Resolved.abstractExpansionsAbove
    {sourceDecl : VInductDecl} {leaf : Nat → VExpr → VExpr → Prop}
    {lvls₀ : List Level}
    (Hlift : NestedExpansionLeafLiftAbove sourceDecl.nparams leaf)
    (Hmapping : ConstructorLowerings.Resolved prodEnv params nparams result
      sources state out)
    (hlvls : state.lvls = lvls₀)
    (Hsource : List.Forall₂ (fun source target =>
      TrSourceConstRaw sourceVEnv lparams source.name source.type target)
      sources sourceTargets)
    (Htarget : List.Forall₂ (fun source target =>
      TrSourceConst targetVEnv lparams source.name source.type target)
      out.1 targetTargets)
    (Hclosed : ∀ source ∈ sources,
      source.type.FVarsIn fun _ => False)
    (HbClosed : ∀ source ∈ sources, Closed source.type)
    (HsourceEnvWF : sourceVEnv.WF)
    (HtargetEnvWF : targetVEnv.WF)
    (hparamsSize : params.size = nparams)
    (hnparams : nparams = sourceDecl.nparams)
    (Hhit : ∀ {lctx : LocalContext} {As : Array Expr}
        {input state output nextState finalState depth fieldDepth sourceValue
          targetValue sourceCtx targetCtx},
      NodeReplacementResolved prodEnv lctx params As input state output
        nextState result finalState →
      NestedExpansionLookupCtx
        leaf
        depth sourceCtx targetCtx →
      (selection : CDeclArray lctx As) →
      selection.fvars.Nodup →
      As.size = params.size →
      depth = selection.fvars.length + fieldDepth →
      SelectedParameterTargets selection.fvars fieldDepth sourceCtx →
      SelectedParameterTargets selection.fvars fieldDepth targetCtx →
      input.FVarsIn (· ∈ selection.fvars) →
      TrExprS sourceVEnv lparams sourceCtx input sourceValue →
      TrExprS targetVEnv lparams targetCtx output targetValue →
      state.lvls = lvls₀ →
      leaf
        depth sourceValue targetValue)
    :
    List.Forall₂ (VInductDecl.NestedConstructorExpansion
      leaf
      nparams) sourceTargets targetTargets := by
  induction Hmapping generalizing sourceTargets targetTargets with
  | nil =>
    cases Hsource
    cases Htarget
    exact .nil
  | cons Hhead Htail ih =>
    cases Hsource with
    | cons HsourceHead HsourceTail =>
      cases Htarget with
      | cons HtargetHead HtargetTail =>
        exact .cons
          (Hhead.abstractExpansionAbove Hlift hlvls HsourceHead HtargetHead HsourceEnvWF
            HtargetEnvWF hparamsSize hnparams (Hclosed _ (by simp))
            (HbClosed _ (by simp)) Hhit)
          (ih (Hhead.lvls.trans hlvls) HsourceTail HtargetTail (fun source hsource =>
            Hclosed source (by simp [hsource])) (fun source hsource =>
            HbClosed source (by simp [hsource])))

/-- The constructor-independent fields of one nested family expansion.  This
small carrier lets the lowering relation discharge family metadata
without obscuring the sole remaining constructor-expression join. -/
structure NestedTypeExpansionHeader
    (env : VEnv) (decl : VInductDecl)
    (source target : VInductiveType) : Prop where
  name : target.name = source.name
  uvars : target.uvars = source.uvars
  type : env.IsDefEqU decl.uvars [] source.type target.type
  numIndices : target.numIndices = source.numIndices
  resultLevel : target.resultLevel = source.resultLevel

/-- Two abstract headers translated from the exact source/lowered concrete
family pair inherit all family-level expansion fields from lowering. -/
theorem FamilyLowering.Resolved.abstractHeaderExpansion
    (Hmapping : FamilyLowering.Resolved prodEnv params nparams result
      sourceConcrete state (targetConcrete, nextState))
    (Hsource : TrInductiveTypeHeaders env envTypes lparams sourceConcrete source)
    (Htarget : TrInductiveType env targetEnvTypes lparams targetConcrete target)
    (henv : env.WF)
    (huvars : decl.uvars = lparams.length)
    (hnumIndices : target.numIndices = source.numIndices)
    (hresultLevel : target.resultLevel = source.resultLevel) :
    NestedTypeExpansionHeader env decl source target where
  name := by
    calc
      target.name = targetConcrete.name := Htarget.header.name
      _ = sourceConcrete.name := Hmapping.name
      _ = source.name := Hsource.header.name.symm
  uvars := by
    calc
      target.uvars = lparams.length := Htarget.header.uvars
      _ = source.uvars := Hsource.header.uvars.symm
  type := by
    rw [huvars]
    exact Hsource.header.type.uniq henv (.refl henv (by trivial)) (by
      rw [← Hmapping.type]
      exact Htarget.header.type)
  numIndices := hnumIndices
  resultLevel := hresultLevel

/-- Family-level projection packages the exact header with the ordered
constructor traversal. -/
theorem FamilyLowering.Resolved.abstractExpansionAbove
    {decl : VInductDecl} {leaf : Nat → VExpr → VExpr → Prop}
    {lvls₀ : List Level}
    (Hlift : NestedExpansionLeafLiftAbove decl.nparams leaf)
    (Hmapping : FamilyLowering.Resolved prodEnv params nparams result
      sourceConcrete state (targetConcrete, nextState))
    (hlvls : state.lvls = lvls₀)
    (Hsource : TrInductiveTypeHeaders headerVEnv sourceVEnv lparams sourceConcrete
      sourceTarget)
    (Htarget : TrInductiveType headerVEnv targetVEnv lparams targetConcrete
      targetTarget)
    (Hheader : NestedTypeExpansionHeader headerVEnv decl sourceTarget
      targetTarget)
    (Hclosed : InductiveConstructorsClosed sourceConcrete)
    (HsourceEnvWF : sourceVEnv.WF)
    (HtargetEnvWF : targetVEnv.WF)
    (hparamsSize : params.size = nparams)
    (hnparams : nparams = decl.nparams)
    (Hhit : ∀ {lctx : LocalContext} {As : Array Expr}
        {input state output nextState finalState depth fieldDepth sourceValue
          targetValue sourceCtx targetCtx},
      NodeReplacementResolved prodEnv lctx params As input state output
        nextState result finalState →
      NestedExpansionLookupCtx
        leaf
        depth sourceCtx targetCtx →
      (selection : CDeclArray lctx As) →
      selection.fvars.Nodup →
      As.size = params.size →
      depth = selection.fvars.length + fieldDepth →
      SelectedParameterTargets selection.fvars fieldDepth sourceCtx →
      SelectedParameterTargets selection.fvars fieldDepth targetCtx →
      input.FVarsIn (· ∈ selection.fvars) →
      TrExprS sourceVEnv lparams sourceCtx input sourceValue →
      TrExprS targetVEnv lparams targetCtx output targetValue →
      state.lvls = lvls₀ →
      leaf
        depth sourceValue targetValue)
    :
    VInductDecl.NestedTypeExpansion headerVEnv decl
      leaf
      sourceTarget targetTarget where
  name := Hheader.name
  uvars := Hheader.uvars
  type := Hheader.type
  numIndices := Hheader.numIndices
  resultLevel := Hheader.resultLevel
  constructors := by
    have HbClosed : ∀ source ∈ sourceConcrete.ctors, Closed source.type := by
      intro source hs
      rcases Lean4Lean.List.Forall₂.forall_exists_l Hsource.ctors source hs with
        ⟨target, _htarget, Htr⟩
      have h := Htr.type.closed
      simpa [VLCtx.bvars] using h
    simpa only [hnparams] using
      Hmapping.constructors.abstractExpansionsAbove Hlift hlvls Hsource.ctors Htarget.ctors
        Hclosed HbClosed HsourceEnvWF HtargetEnvWF hparamsSize hnparams Hhit

/-- `abstractExpansionAbove` at the formation leaf `NestedOccurrenceReplacementAbs`. -/
theorem FamilyLowering.Resolved.abstractExpansion
    (Hmapping : FamilyLowering.Resolved prodEnv params nparams result
      sourceConcrete state (targetConcrete, nextState))
    (Hsource : TrInductiveTypeHeaders headerVEnv sourceVEnv lparams sourceConcrete
      sourceTarget)
    (Htarget : TrInductiveType headerVEnv targetVEnv lparams targetConcrete
      targetTarget)
    (Hheader : NestedTypeExpansionHeader headerVEnv decl sourceTarget
      targetTarget)
    (Hclosed : InductiveConstructorsClosed sourceConcrete)
    (HsourceEnvWF : sourceVEnv.WF)
    (HtargetEnvWF : targetVEnv.WF)
    (hparamsSize : params.size = nparams)
    (hnparams : nparams = decl.nparams)
    (Hhit : ∀ {lctx : LocalContext} {As : Array Expr}
        {input state output nextState finalState depth fieldDepth sourceValue
          targetValue sourceCtx targetCtx},
      NodeReplacementResolved prodEnv lctx params As input state output
        nextState result finalState →
      NestedExpansionLookupCtx
        (VInductDecl.NestedOccurrenceReplacementAbs headerVEnv decl generated)
        depth sourceCtx targetCtx →
      (selection : CDeclArray lctx As) →
      selection.fvars.Nodup →
      As.size = params.size →
      depth = selection.fvars.length + fieldDepth →
      SelectedParameterTargets selection.fvars fieldDepth sourceCtx →
      SelectedParameterTargets selection.fvars fieldDepth targetCtx →
      input.FVarsIn (· ∈ selection.fvars) →
      TrExprS sourceVEnv lparams sourceCtx input sourceValue →
      TrExprS targetVEnv lparams targetCtx output targetValue →
      VInductDecl.NestedOccurrenceReplacementAbs headerVEnv decl generated
        depth sourceValue targetValue)
    :
    VInductDecl.NestedTypeExpansion headerVEnv decl
      (VInductDecl.NestedOccurrenceReplacementAbs headerVEnv decl generated)
      sourceTarget targetTarget :=
  FamilyLowering.Resolved.abstractExpansionAbove nestedOccurrenceReplacementAbs_liftAbove
    Hmapping rfl Hsource Htarget Hheader Hclosed HsourceEnvWF HtargetEnvWF hparamsSize hnparams
    (fun Htrace Hctx' sel nd ar dp hs ht hsc hsrc htgt _ =>
      Hhit Htrace Hctx' sel nd ar dp hs ht hsc hsrc htgt)

/-- Header expansion of a source family.  The source family remains at its
queue position; the independent source and kernel translations,
together with the declaration's metadata, determine the complete abstract
header expansion at that position. -/
theorem NestedLoweringOutputClosed.sourceHeaderExpansionAtFresh
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hsource : TrInductDeclCore sourceVEnv lparams nparams sourceTypes
      isUnsafe sourceDecl sourceEnvTypes sourceEnvCtors)
    (Htarget : TrInductDeclCore sourceVEnv lparams nparams result.types
      isUnsafe loweredDecl targetEnvTypes targetEnvCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (henv : sourceVEnv.WF)
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length) :
    ∃ hsourceDecl : familyIdx < sourceDecl.types.length,
      ∃ htargetDecl : familyIdx < loweredDecl.types.length,
      NestedTypeExpansionHeader sourceVEnv sourceDecl
        (sourceDecl.types[familyIdx]'hsourceDecl)
        (loweredDecl.types[familyIdx]'htargetDecl) := by
  have hresult : familyIdx < result.types.length :=
    Nat.lt_of_lt_of_le hfamily H.toResult.sourceTypes_length_le
  have hsourceDecl : familyIdx < sourceDecl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource]
    exact hfamily
  have htargetDecl : familyIdx < loweredDecl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Htarget]
    exact hresult
  have hdeclLength : sourceDecl.types.length ≤ loweredDecl.types.length := by
    calc
      sourceDecl.types.length = sourceTypes.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource).symm
      _ ≤ result.types.length := H.toResult.sourceTypes_length_le
      _ = loweredDecl.types.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Htarget
  rcases H.sourceResolvedMappingAtFreshAligned hempty hfamily with
    ⟨_fvars, _stepState, targetConcrete, nextState, _hparams, _hnodup,
      _hsize, Hmapping, htarget⟩
  obtain ⟨_hresult, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp htarget
  have HsourceType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
    Hsource familyIdx hfamily hsourceDecl
  have HtargetType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
    Htarget familyIdx hresult htargetDecl
  rw [htargetEq] at HtargetType
  refine ⟨hsourceDecl, htargetDecl, Hmapping.abstractHeaderExpansion
    (Lean4Lean.VerifyInductive.TrInductiveType.headers HsourceType)
      HtargetType henv Hsource.uvars ?_ ?_⟩
  · exact (Hmetadata.numIndices hdeclLength familyIdx hsourceDecl
      htargetDecl).symm
  · exact (Hmetadata.resultLevel hdeclLength familyIdx hsourceDecl
      htargetDecl).symm

/-- Exact interpretation of successful replacement leaves for one closed
lowering result and one independently translated source/expanded block.  In
contrast to a generic expression provider, every quantified replacement is
an actual `NodeReplacementHasResolvedMapping` into this exact final result,
and both translations use the exact mutual-header environments. -/
def NestedFormationReplacementCompat
    (prodEnv : Environment) (result : Lean4Lean.ElimNestedInductive.Result)
    (baseVEnv sourceVEnv targetVEnv : VEnv) (lparams : List Name)
    (sourceDecl : VInductDecl) (generated : List VInductiveType) : Prop :=
  ∀ {lctx : LocalContext} {As : Array Expr}
      {input state output nextState finalState depth fieldDepth sourceValue targetValue
        sourceCtx targetCtx},
    NodeReplacementResolved prodEnv lctx result.params As input state output
      nextState result finalState →
    NestedExpansionLookupCtx
      (VInductDecl.NestedOccurrenceReplacementAbs baseVEnv sourceDecl generated)
      depth sourceCtx targetCtx →
    (selection : CDeclArray lctx As) →
    selection.fvars.Nodup →
    As.size = result.params.size →
    depth = selection.fvars.length + fieldDepth →
    SelectedParameterTargets selection.fvars fieldDepth sourceCtx →
    SelectedParameterTargets selection.fvars fieldDepth targetCtx →
    input.FVarsIn (· ∈ selection.fvars) →
    TrExprS sourceVEnv lparams sourceCtx input sourceValue →
    TrExprS targetVEnv lparams targetCtx output targetValue →
    VInductDecl.NestedOccurrenceReplacementAbs baseVEnv sourceDecl generated depth
      sourceValue targetValue

/-- An exact family translation at the empty source context already proves
concrete constructor closure; retaining a second closure callback would
duplicate information in `TrInductiveType`. -/
theorem TrInductiveTypeHeaders.constructorsClosed
    (H : TrInductiveTypeHeaders env envTypes lparams concrete abstract) :
    InductiveConstructorsClosed concrete := by
  intro ctor hctor
  rcases Lean4Lean.List.Forall₂.forall_exists_l H.ctors ctor hctor with
    ⟨_target, _htarget, Hctor⟩
  simpa [Lean4Lean.FVarsIn] using Hctor.type.fvarsIn

/-- Expansion of a source family and its constructors.  All family and constructor
ordering is obtained from exact positional translations and the
state-threaded lowering mapping. -/
theorem NestedLoweringOutputClosed.sourceExpansionAtFreshAboveLvls
    {sourceDecl : VInductDecl} {leaf : Nat → VExpr → VExpr → Prop}
    (Hlift : NestedExpansionLeafLiftAbove sourceDecl.nparams leaf)
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hsource : TrInductDeclCore sourceVEnv lparams nparams sourceTypes
      isUnsafe sourceDecl sourceEnvTypes sourceEnvCtors)
    (Htarget : TrInductDeclCore sourceVEnv lparams nparams result.types
      isUnsafe loweredDecl targetEnvTypes targetEnvCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (Hsyntax : SourceSyntaxChecked sourceTypes)
    (hempty : initialState.nestedAux = #[])
    (henv : sourceVEnv.WF)
    (Hhit : ∀ {lctx : LocalContext} {As : Array Expr}
        {input state output nextState finalState depth fieldDepth sourceValue
          targetValue sourceCtx targetCtx},
      NodeReplacementResolved prodEnv lctx result.params As input state
        output nextState result finalState →
      NestedExpansionLookupCtx
        leaf depth sourceCtx targetCtx →
      (selection : CDeclArray lctx As) →
      selection.fvars.Nodup →
      As.size = result.params.size →
      depth = selection.fvars.length + fieldDepth →
      SelectedParameterTargets selection.fvars fieldDepth sourceCtx →
      SelectedParameterTargets selection.fvars fieldDepth targetCtx →
      input.FVarsIn (· ∈ selection.fvars) →
      TrExprS sourceEnvTypes lparams sourceCtx input sourceValue →
      TrExprS targetEnvTypes lparams targetCtx output targetValue →
      state.lvls = initialState.lvls →
      leaf
        depth sourceValue targetValue)
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length) :
    ∃ hsourceDecl : familyIdx < sourceDecl.types.length,
      ∃ htargetDecl : familyIdx < loweredDecl.types.length,
      VInductDecl.NestedTypeExpansion sourceVEnv sourceDecl
        leaf
        (sourceDecl.types[familyIdx]'hsourceDecl)
        (loweredDecl.types[familyIdx]'htargetDecl) := by
  rcases H.sourceHeaderExpansionAtFresh Hsource Htarget Hmetadata hempty henv
      familyIdx hfamily with ⟨hsourceDecl, htargetDecl, Hheader⟩
  have hresult : familyIdx < result.types.length :=
    Nat.lt_of_lt_of_le hfamily H.toResult.sourceTypes_length_le
  have hjInitial : familyIdx <
      ({ initialState with
        newTypes := sourceTypes.toArray }).newTypes.size := by
    simpa using hfamily
  rcases H with ⟨finalState, Hrun, Hcache, Hparams⟩
  rcases Hrun.resolvedMappingAtInitialAlignedLvls
      (Hrun.resultNamesNodupOfEmpty (by simpa using hempty)) hjInitial with
    ⟨params, stepState, targetConcrete, loweredState, hresultParams,
      _hsize, Hmapping, htarget, hstepLvls⟩
  subst hresultParams
  have H : NestedLoweringOutputClosed prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result :=
    ⟨finalState, Hrun, Hcache, Hparams⟩
  obtain ⟨_hresult, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp htarget
  have HsourceType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
    Hsource familyIdx hfamily hsourceDecl
  have HtargetType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
    Htarget familyIdx hresult htargetDecl
  rw [htargetEq] at HtargetType
  have HsourceTypesWF : sourceEnvTypes.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF Hsource henv
  have HtargetTypesWF : targetEnvTypes.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF Htarget henv
  have hparamsSize : result.params.size = nparams := by
    rcases H with ⟨_finalState, Hrun, _Hcache, _Hparams⟩
    exact Hrun.resultParamsSize
  exact ⟨hsourceDecl, htargetDecl,
    Hmapping.abstractExpansionAbove Hlift hstepLvls
      (Lean4Lean.VerifyInductive.TrInductiveType.headers HsourceType)
      HtargetType Hheader
      (Hsyntax.getElem familyIdx hfamily).constructors.closed
      HsourceTypesWF HtargetTypesWF hparamsSize Hsource.nparams.symm Hhit⟩

/-- Ordered expansion of all source families.  This is the
list-valued formation payload for the initial queue; no positional choice is
left to the caller. -/
theorem NestedLoweringOutputClosed.sourceExpansionsAboveLvls
    {sourceDecl : VInductDecl} {leaf : Nat → VExpr → VExpr → Prop}
    (Hlift : NestedExpansionLeafLiftAbove sourceDecl.nparams leaf)
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hsource : TrInductDeclCore sourceVEnv lparams nparams sourceTypes
      isUnsafe sourceDecl sourceEnvTypes sourceEnvCtors)
    (Htarget : TrInductDeclCore sourceVEnv lparams nparams result.types
      isUnsafe loweredDecl targetEnvTypes targetEnvCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (Hsyntax : SourceSyntaxChecked sourceTypes)
    (hempty : initialState.nestedAux = #[])
    (henv : sourceVEnv.WF)
    (Hhit : ∀ {lctx : LocalContext} {As : Array Expr}
        {input state output nextState finalState depth fieldDepth sourceValue
          targetValue sourceCtx targetCtx},
      NodeReplacementResolved prodEnv lctx result.params As input state
        output nextState result finalState →
      NestedExpansionLookupCtx leaf depth sourceCtx targetCtx →
      (selection : CDeclArray lctx As) →
      selection.fvars.Nodup →
      As.size = result.params.size →
      depth = selection.fvars.length + fieldDepth →
      SelectedParameterTargets selection.fvars fieldDepth sourceCtx →
      SelectedParameterTargets selection.fvars fieldDepth targetCtx →
      input.FVarsIn (· ∈ selection.fvars) →
      TrExprS sourceEnvTypes lparams sourceCtx input sourceValue →
      TrExprS targetEnvTypes lparams targetCtx output targetValue →
      state.lvls = initialState.lvls →
      leaf depth sourceValue targetValue)
    :
    List.Forall₂
      (VInductDecl.NestedTypeExpansion sourceVEnv sourceDecl
        leaf)
      sourceDecl.types (loweredDecl.types.take sourceDecl.types.length) := by
  have hsourceLength : sourceDecl.types.length = sourceTypes.length :=
    (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource).symm
  have htargetLength : loweredDecl.types.length = result.types.length :=
    (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Htarget).symm
  have hprefix : sourceDecl.types.length ≤ loweredDecl.types.length := by
    rw [hsourceLength, htargetLength]
    exact H.toResult.sourceTypes_length_le
  apply List.forall₂_of_getElem (by simp [hprefix])
  intro familyIdx hsourceDecl htargetDecl
  have hfamily : familyIdx < sourceTypes.length := by
    simpa [hsourceLength] using hsourceDecl
  have htargetFull : familyIdx < loweredDecl.types.length :=
    Nat.lt_of_lt_of_le hsourceDecl hprefix
  have htargetEq :
      (loweredDecl.types.take sourceDecl.types.length)[familyIdx] =
        loweredDecl.types[familyIdx] := by
    simp only [List.getElem_take]
  rcases H.sourceExpansionAtFreshAboveLvls Hlift Hsource Htarget Hmetadata Hsyntax hempty
      henv Hhit familyIdx hfamily
      with ⟨hsourceDecl', htargetDecl', Hfamily⟩
  have hsourceProof : hsourceDecl' = hsourceDecl := Subsingleton.elim _ _
  have htargetProof : htargetDecl' = htargetFull := Subsingleton.elim _ _
  subst hsourceDecl'
  subst htargetDecl'
  simpa only [htargetEq] using Hfamily

/-- `sourceExpansionsAboveLvls` without the universe-argument premise. -/
theorem NestedLoweringOutputClosed.sourceExpansionsAbove
    {sourceDecl : VInductDecl} {leaf : Nat → VExpr → VExpr → Prop}
    (Hlift : NestedExpansionLeafLiftAbove sourceDecl.nparams leaf)
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hsource : TrInductDeclCore sourceVEnv lparams nparams sourceTypes
      isUnsafe sourceDecl sourceEnvTypes sourceEnvCtors)
    (Htarget : TrInductDeclCore sourceVEnv lparams nparams result.types
      isUnsafe loweredDecl targetEnvTypes targetEnvCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (Hsyntax : SourceSyntaxChecked sourceTypes)
    (hempty : initialState.nestedAux = #[])
    (henv : sourceVEnv.WF)
    (Hhit : ∀ {lctx : LocalContext} {As : Array Expr}
        {input state output nextState finalState depth fieldDepth sourceValue
          targetValue sourceCtx targetCtx},
      NodeReplacementResolved prodEnv lctx result.params As input state
        output nextState result finalState →
      NestedExpansionLookupCtx leaf depth sourceCtx targetCtx →
      (selection : CDeclArray lctx As) →
      selection.fvars.Nodup →
      As.size = result.params.size →
      depth = selection.fvars.length + fieldDepth →
      SelectedParameterTargets selection.fvars fieldDepth sourceCtx →
      SelectedParameterTargets selection.fvars fieldDepth targetCtx →
      input.FVarsIn (· ∈ selection.fvars) →
      TrExprS sourceEnvTypes lparams sourceCtx input sourceValue →
      TrExprS targetEnvTypes lparams targetCtx output targetValue →
      leaf depth sourceValue targetValue)
    :
    List.Forall₂
      (VInductDecl.NestedTypeExpansion sourceVEnv sourceDecl
        leaf)
      sourceDecl.types (loweredDecl.types.take sourceDecl.types.length) :=
  H.sourceExpansionsAboveLvls Hlift Hsource Htarget Hmetadata Hsyntax hempty henv
    (fun Htrace Hctx' sel nd ar dp hs ht hsc hsrc htgt _ =>
      Hhit Htrace Hctx' sel nd ar dp hs ht hsc hsrc htgt)

/-- `sourceExpansionsAbove` at the formation leaf `NestedOccurrenceReplacementAbs`. -/
theorem NestedLoweringOutputClosed.sourceExpansions
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringOutputClosed prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hsource : TrInductDeclCore sourceVEnv lparams nparams sourceTypes
      isUnsafe sourceDecl sourceEnvTypes sourceEnvCtors)
    (Htarget : TrInductDeclCore sourceVEnv lparams nparams result.types
      isUnsafe loweredDecl targetEnvTypes targetEnvCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (Hsyntax : SourceSyntaxChecked sourceTypes)
    (hempty : initialState.nestedAux = #[])
    (henv : sourceVEnv.WF)
    (generated : List VInductiveType)
    (Hhit : NestedFormationReplacementCompat prodEnv result sourceVEnv
      sourceEnvTypes targetEnvTypes lparams sourceDecl generated)
    :
    List.Forall₂
      (VInductDecl.NestedTypeExpansion sourceVEnv sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs sourceVEnv sourceDecl
          generated))
      sourceDecl.types (loweredDecl.types.take sourceDecl.types.length) :=
  NestedLoweringOutputClosed.sourceExpansionsAbove
    nestedOccurrenceReplacementAbs_liftAbove
    H Hsource Htarget Hmetadata Hsyntax hempty henv Hhit

end VerifyInductive
end Lean4Lean
