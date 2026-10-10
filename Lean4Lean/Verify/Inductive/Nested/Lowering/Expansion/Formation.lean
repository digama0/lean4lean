import Lean4Lean.Verify.Inductive.Nested.Lowering.Expression
import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Verify.Inductive.RecursorInput

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Nested formation from lowering

The installed container of an auxiliary family (`AuxiliaryFamilyContainer`), the conversion of
ordered family expansions into the abstract nested formation judgment
(`VInductDecl.NestedFormationWF.ofForall₂`), and the data of a nested expansion of a source
declaration (`NestedExpansionData`), section 3.3 of the design notes. -/

/-- A finite installed-declaration derivation exposes the exact abstract
family constant at every source position. -/
theorem installedBelow_familyLookup
    (H : VEnv.InstalledBelow env decl)
    (i : Nat) (hi : i < decl.types.length) :
    env.constants decl.types[i].name = some decl.types[i].toVConstant :=
  H.familyConstant i hi

/-- The installed container declaration of an auxiliary family, obtained
from the kernel family lookup retained by lowering and the persistent
environment invariant.  In particular, `container` is not an arbitrary
declaration with a matching family name: it has a finite prior
well-formedness/compilation/installation derivation in the current abstract
environment. -/
structure AuxiliaryFamilyContainer
    (prodEnv : Environment) (venv : VEnv)
    (params : Array Expr) (nestedAux : Array (Expr × Name))
    (family : InductiveType)
    (H : AuxiliaryFamilySpecialization prodEnv params nestedAux family) where
  container : VInductDecl
  familyIdx : Nat
  familyIdx_lt : familyIdx < container.types.length
  installed : VEnv.InstalledBelow venv container
  lookupName : H.sourceName = H.sourceInfo.name
  familyName : H.sourceInfo.name = container.types[familyIdx].name
  numParams : H.sourceInfo.numParams = container.nparams
  levelParams : H.sourceInfo.levelParams.length = container.uvars
  constructors : H.sourceInfo.ctors.length =
    container.types[familyIdx].ctors.length
  constructorName : ∀ i (hi : i < H.sourceInfo.ctors.length),
    H.sourceInfo.ctors[i] = container.types[familyIdx].ctors[i].name
  familyLookup : venv.constants H.sourceName =
    some container.types[familyIdx].toVConstant
  familyTranslation : TrConstant .unsafe venv
    (.inductInfo H.sourceInfo) container.types[familyIdx].toVConstant
  /-- The concrete family's safety flag is the container declaration's. -/
  containerUnsafe : H.sourceInfo.isUnsafe = container.isUnsafe

/-- Recover the installed container in the exact abstract observer that
translated the recognized family.  Visibility is derived from the concrete
lookup and the supplied abstract lookup through environment alignment; it is
not an additional safety premise. -/
theorem AuxiliaryFamilySpecialization.installedContainerOfAbstractLookup
    {ves : VEnvs}
    (H : AuxiliaryFamilySpecialization prodEnv params nestedAux family)
    (wf : ves.WF prodEnv) (safety : DefinitionSafety)
    (abstractFamily : VConstant)
    (habstract : (ves.venv safety).constants H.sourceName =
      some abstractFamily) :
    Nonempty (AuxiliaryFamilyContainer prodEnv (ves.venv safety)
      params nestedAux family H) := by
  have Haligned := (wf.tr (safety := safety)).find?_uniq
    H.built.lookup habstract
  obtain ⟨hsourceName, ⟨P⟩⟩ := wf.inductFamiliesInstalled H.built.lookup Haligned.2.1
  have hfamily := P.familyIdx_lt
  have habstractLookup : (ves.venv safety).constants H.sourceName =
      some (P.decl.types[P.familyIdx]'hfamily).toVConstant := by
    calc
      (ves.venv safety).constants H.sourceName =
          (ves.venv safety).constants H.sourceInfo.name :=
        congrArg (ves.venv safety).constants hsourceName
      _ = (ves.venv safety).constants
          (P.decl.types[P.familyIdx]'hfamily).name :=
        congrArg (ves.venv safety).constants P.name
      _ = some (P.decl.types[P.familyIdx]'hfamily).toVConstant :=
        installedBelow_familyLookup P.installed.installedBelow P.familyIdx
          hfamily
  refine ⟨{
    container := P.decl
    familyIdx := P.familyIdx
    familyIdx_lt := P.familyIdx_lt
    installed := P.installed.installedBelow
    lookupName := hsourceName
    familyName := P.name
    numParams := P.numParams
    levelParams := P.levelParams
    constructors := P.constructors
    constructorName := P.constructorName
    familyLookup := habstractLookup
    familyTranslation := ?_
    containerUnsafe := P.isUnsafe }⟩
  exact ((wf.tr (safety := safety)).find?_uniq H.built.lookup
    habstractLookup).2.sf_mono DefinitionSafety.unsafe_le

/-- Repackage the reusable structural expression carrier into the specialized
strictly-positive carrier used by the finite formation derivation. -/
theorem nestedExprExpansion_toNestedExprWFExpansion
    (H : VExpr.NestedExprExpansion
      (VInductDecl.NestedOccurrenceReplacementAbs env source generated)
      depth input output) :
    VInductDecl.NestedExprWFExpansion env source generated depth input
      output := by
  induction H with
  | occurrence Hleaf =>
    rcases Hleaf with ⟨relativeDepth, hdepth, Hrelative⟩
    exact .occurrence hdepth Hrelative
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | proj _ ihMajor => exact .proj ihMajor
  | app _ _ ihFn ihArg => exact .app ihFn ihArg
  | lam _ _ ihDomain ihBody => exact .lam ihDomain ihBody
  | forallE _ _ ihDomain ihBody => exact .forallE ihDomain ihBody

/-- Repackage the retained common-parameter prefix into the mutually
strictly-positive formation carrier. -/
theorem nestedForallPrefixExpansion_toNestedForallPrefixWFExpansion
    (H : VExpr.NestedForallPrefixExpansion
      (VInductDecl.NestedOccurrenceReplacementAbs env source generated)
      depth arity input output) :
    VInductDecl.NestedForallPrefixWFExpansion env source generated depth
      arity input output := by
  induction H with
  | nil Hbody =>
    exact .nil (nestedExprExpansion_toNestedExprWFExpansion Hbody)
  | cons Hdomain _ ih =>
    exact .cons (nestedExprExpansion_toNestedExprWFExpansion Hdomain) ih

/-- Convert ordered generic constructor expansion into the mutual
strict-positivity encoding required by `NestedFormationWF`. -/
theorem nestedConstructorWFExpansions_ofForall₂
    (H : List.Forall₂
      (VInductDecl.NestedConstructorExpansion
        (VInductDecl.NestedOccurrenceReplacementAbs env source generated)
        source.nparams)
      sourceCtors targetCtors) :
    VInductDecl.NestedConstructorWFExpansions env source generated
      sourceCtors targetCtors := by
  induction H with
  | nil => exact .nil
  | cons Hhead _ ih =>
    exact .cons Hhead.name Hhead.uvars
      (nestedForallPrefixExpansion_toNestedForallPrefixWFExpansion
        Hhead.parameters) ih

/-- Convert ordered generic family expansion into the mutual
strict-positivity encoding required by `NestedFormationWF`. -/
theorem nestedTypeWFExpansions_ofForall₂
    (H : List.Forall₂
      (VInductDecl.NestedTypeExpansion env source
        (VInductDecl.NestedOccurrenceReplacementAbs env source generated))
      sourceTypes targetTypes) :
    VInductDecl.NestedTypeWFExpansions env source generated sourceTypes
      targetTypes := by
  induction H with
  | nil => exact .nil
  | cons Hhead _ ih =>
    exact .cons Hhead.name Hhead.uvars Hhead.type Hhead.numIndices
      Hhead.resultLevel
      (nestedConstructorWFExpansions_ofForall₂ Hhead.constructors) ih

/-- Build a nested formation derivation once the lowering
projection has supplied ordered family expansion for the source families and
every auxiliary family of the queue.  The expanded declaration alone supplies the
ordinary formation judgment; no executable callback enters the abstract
specification. -/
theorem VInductDecl.NestedFormationWF.ofForall₂
    {env : VEnv} {source expanded : VInductDecl}
    {generated : List VInductiveType}
    (Hsource : expanded.SourceWF env)
    (Hformation : expanded.OrdinaryFormationWF env)
    (HsourceParameters : source.SourceParameterWF env)
    (huvars : expanded.uvars = source.uvars)
    (hnparams : expanded.nparams = source.nparams)
    (hunsafe : expanded.isUnsafe = source.isUnsafe)
    (Htypes : List.Forall₂
      (VInductDecl.NestedTypeExpansion env source
        (VInductDecl.NestedOccurrenceReplacementAbs env source generated))
      (source.types ++ generated) expanded.types) :
    source.NestedFormationWF env :=
  .intro Hsource Hformation HsourceParameters huvars hnparams hunsafe
    (nestedTypeWFExpansions_ofForall₂ Htypes)

/-- Inputs to the nested-formation judgment.  The expanded
declaration is explicit, as is the exact ordered expansion of the source
families followed by the auxiliary families of the queue. -/
structure NestedExpansionData (env : VEnv) (source : VInductDecl) where
  expanded : VInductDecl
  generated : List VInductiveType
  expandedSource : expanded.SourceWF env
  expandedFormation : expanded.OrdinaryFormationWF env
  sourceParameters : source.SourceParameterWF env
  uvars : expanded.uvars = source.uvars
  nparams : expanded.nparams = source.nparams
  isUnsafe : expanded.isUnsafe = source.isUnsafe
  types : List.Forall₂
    (VInductDecl.NestedTypeExpansion env source
      (VInductDecl.NestedOccurrenceReplacementAbs env source generated))
    (source.types ++ generated) expanded.types

theorem NestedExpansionData.formation
    (H : NestedExpansionData env source) :
    source.NestedFormationWF env :=
  Lean4Lean.VerifyInductive.VInductDecl.NestedFormationWF.ofForall₂
    H.expandedSource H.expandedFormation H.sourceParameters H.uvars H.nparams
      H.isUnsafe H.types

/-- Constructor telescope lengths of the source families agree with those
of the expanded declaration. -/
theorem NestedExpansionData.constructorArityPrefix
    (H : NestedExpansionData env source) :
    source.ConstructorArityPrefix H.expanded := by
  have hnodup : (H.expanded.types.map (·.name)).Nodup := by
    have h := (List.nodup_append.mp H.expandedSource.2.1).1
    simpa [VInductDecl.typeConstants, VInductiveType.toVConstVal,
      Function.comp_def] using h
  exact VInductDecl.constructorArityPrefixOfNestedExpansions H.types
    H.expandedFormation.sourceParameterWF.rawCtorShape H.uvars H.nparams hnodup

/-- A successful ordinary header/constructor run supplies both independent
well-formedness judgments for the expanded block.  Thus the only genuinely
nested input left is the ordered lowering expansion itself
(plus the declaration metadata equalities fixed by lowering). -/
def NestedExpansionData.ofConstructorPhases
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {expanded source : VInductDecl} {nparams depth : Nat}
    {isUnsafe : Bool} {env : VEnv} {indTypes : Array InductiveType}
    {ctorEnv : Environment}
    (R : RecursorInput c stats expanded nparams isUnsafe depth env indTypes ctorEnv)
    (generated : List VInductiveType)
    (hnonempty : indTypes.toList ≠ [])
    (HsourceParameters : source.SourceParameterWF env)
    (huvars : expanded.uvars = source.uvars)
    (hnparams : expanded.nparams = source.nparams)
    (hunsafe : expanded.isUnsafe = source.isUnsafe)
    (Htypes : List.Forall₂
      (VInductDecl.NestedTypeExpansion env source
        (VInductDecl.NestedOccurrenceReplacementAbs env source generated))
      (source.types ++ generated) expanded.types) :
    NestedExpansionData env source where
  expanded := expanded
  generated := generated
  expandedSource :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.sourceWF_ofNonempty R.core
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty R.core hnonempty)
  expandedFormation := R.formation.formationWF
  sourceParameters := HsourceParameters
  uvars := huvars
  nparams := hnparams
  isUnsafe := hunsafe
  types := Htypes

end VerifyInductive
end Lean4Lean
