import Lean4Lean.Verify.Inductive.Nested.Restoration.Steps
import Lean4Lean.Verify.Inductive.Nested.Restoration.ConstructorTranslations
import Lean4Lean.Verify.Inductive.Nested.Lowering.Recognition
import Lean4Lean.Verify.Inductive.Install.Metadata

/-! Translations of the executable nested restoration folds: the source family
translations (`SourceFamilyTranslations`: header, constructors and source recursor of
each source family) and the auxiliary recursor fold (`AuxiliaryRecursorRuleBatches`),
the restored block `restoredBlock`, and the auxiliary-constructor freshness
consequence of installation. Shared lookup and mutual-header effects live in
`Install/Metadata.lean`. Section 3.3 of the design notes. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- One executable auxiliary recursor restoration step: the translated
recursor constant and the abstract rule batch of the step, of the restored
length. The record fixes no equation syntax; the rules are fixed by the
compilation of the nested installation. -/
structure AuxiliaryRecursorRuleBatch
    (safety : DefinitionSafety) (trEnv : VEnv)
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceEnv targetEnv) where
  recursor : VConstVal
  rules : List VDefEq
  translated : TrConstVal safety trEnv
    (.recInfo Hstep.restored.newInfo) recursor
  rulesLength : rules.length = Hstep.restored.newInfo.rules.length

/-- The steps of an auxiliary restoration fold, each with an
`AuxiliaryRecursorRuleBatch`. The rule batches are recorded explicitly, but this
judgment alone does not constrain their left-hand sides or their translation. -/
inductive AuxiliaryRecursorRuleBatches
    (safety : DefinitionSafety) (trEnv : VEnv) :
    ∀ {names sourceEnv targetEnv},
      FoldSteps
        (RestoredRecursorStep result loweredEnv auxRec allIndNames)
        names sourceEnv targetEnv →
      List VConstVal → List VDefEq →
      List VConstVal → List VDefEq → Prop
  | nil (sourceEnv) (recursors rules) :
      AuxiliaryRecursorRuleBatches safety trEnv
        (FoldSteps.nil (P :=
          RestoredRecursorStep result loweredEnv auxRec allIndNames)
          (source := sourceEnv)) recursors rules recursors rules
  | cons
      (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
        oldRecName sourceEnv middleEnv)
      (Htail : FoldSteps
        (RestoredRecursorStep result loweredEnv auxRec allIndNames)
        names middleEnv targetEnv)
      (Hsemantic : AuxiliaryRecursorRuleBatch safety trEnv
        Hstep)
      (Hrest : AuxiliaryRecursorRuleBatches safety trEnv
        Htail (priorRecursors ++ [Hsemantic.recursor])
          (priorRules ++ Hsemantic.rules) finalRecursors finalRules) :
      AuxiliaryRecursorRuleBatches safety trEnv
        (.cons Hstep Htail) priorRecursors priorRules
          finalRecursors finalRules

/-- Translation, typing and shape of one restored source recursor. -/
structure SourceRecursorTranslation
    (decl : VInductDecl) (owner : VInductiveType)
    (safety : DefinitionSafety)
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (sourceVEnv : VEnv) where
  recursor : VConstVal
  safety_le : safety ≤ (ConstantInfo.recInfo Hstep.oldInfo).safety
  uvars : Hstep.oldInfo.levelParams.length = recursor.uvars
  type : TrExprS sourceVEnv Hstep.oldInfo.levelParams []
    Hstep.restored.newInfo.type recursor.type
  name : recursor.name = Hstep.restored.newRecName
  wf : recursor.toVConstant.WF sourceVEnv
  shape : Nonempty (decl.NestedRecursorShape owner recursor)

/-- The abstract source recursor of one source family. It mentions neither the
lowered declaration nor any executable restoration step: it is the abstract
specification which the executable recursor construction must refine. -/
structure SourceRecursorSpec
    (sourceDecl : VInductDecl) (owner : VInductiveType)
    (canonicalEnv : VEnv) where
  recursor : VConstVal
  name : recursor.name = sourceDecl.recursorName owner
  isType : canonicalEnv.IsType recursor.uvars [] recursor.type
  shape : Nonempty (sourceDecl.NestedRecursorShape owner recursor)

/-- Executable-to-specification refinement for a restored source recursor.
The source recursor is fixed by `SourceRecursorSpec`; this record
states that the executable restoration step has exactly its universe arity and
translates its restored telescope to exactly its abstract type. -/
structure SourceRecursorRefinement
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (canonicalEnv : VEnv) (recursor : VConstVal) : Prop where
  uvars : Hstep.oldInfo.levelParams.length = recursor.uvars
  type : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
    Hstep.restored.newInfo.type recursor.type

/-- One abstract source recursor translating a particular restored executable
recursor. The equality field ties the source specification and the refinement
to the same constant. -/
structure TrSourceRecursor
    (sourceDecl : VInductDecl) (sourceOwner : VInductiveType)
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (canonicalEnv : VEnv) (recursor : VConstVal) where
  source : SourceRecursorSpec sourceDecl sourceOwner canonicalEnv
  recursor_eq : source.recursor = recursor
  refinement : SourceRecursorRefinement Hstep canonicalEnv recursor

/-- Source translations of the families along the source-family restoration fold. -/
inductive SourceFamilyTranslations
    (decl : VInductDecl) (lparams : List Name)
    (safety : DefinitionSafety)
    (sourceVEnv envTypes envCtors : VEnv) :
    ∀ {types sourceProdEnv targetProdEnv},
      FoldSteps
        (RestoredInductiveStep result loweredEnv auxRec allIndNames)
        types sourceProdEnv targetProdEnv →
      List VInductiveType → List VConstVal → Prop
  | nil (sourceProdEnv : Environment) :
      SourceFamilyTranslations decl lparams safety sourceVEnv
        envTypes envCtors
        (FoldSteps.nil (P :=
          RestoredInductiveStep result loweredEnv auxRec allIndNames)
          (source := sourceProdEnv)) [] []
  | cons
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        indType sourceProdEnv middleProdEnv)
      (Htail : FoldSteps
        (RestoredInductiveStep result loweredEnv auxRec allIndNames)
        types middleProdEnv targetProdEnv)
      (Hheader : TrSourceConst sourceVEnv lparams indType.name indType.type
        owner.toVConstVal)
      (Hconstructors : RestoredConstructorTranslations result loweredEnv lparams safety envTypes
        Hstep.oldInfo.ctors Hstep.restored.headerEnv
          Hstep.restored.constructorEnv indType.ctors owner.ctors)
      (Hrecursor : SourceRecursorTranslation decl owner safety
        Hstep.restored.recursor envCtors)
      (Hrest : SourceFamilyTranslations decl lparams safety
        sourceVEnv envTypes envCtors Htail owners recursors) :
      SourceFamilyTranslations decl lparams safety sourceVEnv
        envTypes envCtors (.cons Hstep Htail) (owner :: owners)
        (Hrecursor.recursor :: recursors)

/-- The source translations for one executable family restoration step: header,
constructors and source recursor. Bundling the fields keeps the mutual fold
independent of how each of them is proved. -/
structure SourceFamilyTranslation
    (decl : VInductDecl) (lparams : List Name)
    (safety : DefinitionSafety) (sourceVEnv envTypes envCtors : VEnv)
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      indType sourceProdEnv targetProdEnv) where
  owner : VInductiveType
  header : TrSourceConst sourceVEnv lparams indType.name indType.type
    owner.toVConstVal
  constructors : RestoredConstructorTranslations result loweredEnv lparams safety envTypes
    Hstep.oldInfo.ctors Hstep.restored.headerEnv
      Hstep.restored.constructorEnv indType.ctors owner.ctors
  recursor : SourceRecursorTranslation decl owner safety
    Hstep.restored.recursor envCtors

theorem SourceFamilyTranslations.types
    {sourceTypes : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    {Htrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv targetProdEnv}
    (H : SourceFamilyTranslations decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors) :
    List.Forall₂ (TrInductiveType sourceVEnv envTypes lparams)
      sourceTypes owners := by
  induction H with
  | nil => exact .nil
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest ih =>
    exact .cons ⟨Hheader, Hconstructors.forall₂⟩ ih

/-- Header well-formedness is pointwise data in the source family translations;
no separate premise of the nested installation is needed. -/
theorem SourceFamilyTranslations.typeConstantsWF
    (H : SourceFamilyTranslations decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors)
    (htypes : decl.types = owners) :
    ∀ ci ∈ decl.typeConstants, ci.toVConstant.WF sourceVEnv := by
  intro ci hci
  simp only [VInductDecl.typeConstants] at hci
  rcases List.mem_map.mp hci with ⟨owner, howner, rfl⟩
  have howner' : owner ∈ owners := by
    rw [← htypes]
    exact howner
  rcases Lean4Lean.List.Forall₂.forall_exists_r H.types owner howner' with
    ⟨_source, _hsource, Howner⟩
  exact Howner.header.wf

/-- Constructor well-formedness is likewise fixed by the source family
translations, in the header environment. -/
theorem SourceFamilyTranslations.constructorConstantsWF
    (H : SourceFamilyTranslations decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors)
    (htypes : decl.types = owners) :
    ∀ ci ∈ decl.constructorConstants, ci.toVConstant.WF envTypes := by
  intro ci hci
  simp only [VInductDecl.constructorConstants] at hci
  rcases List.mem_flatMap.mp hci with ⟨owner, howner, hctor⟩
  have howner' : owner ∈ owners := by
    rw [← htypes]
    exact howner
  rcases Lean4Lean.List.Forall₂.forall_exists_r H.types owner howner' with
    ⟨_source, _hsource, Howner⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r Howner.ctors ci hctor with
    ⟨_sourceCtor, _hsourceCtor, Hctor⟩
  exact Hctor.wf

/-- Restored source recursors are typed in the constructor environment, which
already contains every mutual constructor. -/
theorem SourceFamilyTranslations.sourceRecursorsWF
    (H : SourceFamilyTranslations decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors) :
    ∀ ci ∈ recursors, ci.toVConstant.WF envCtors := by
  induction H with
  | nil => simp
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest ih =>
    intro ci hci
    simp only [List.mem_cons] at hci
    rcases hci with rfl | hrest
    · exact Hrecursor.wf
    · exact ih ci hrest

/-- The source declaration translation `TrInductDeclCore`, from the source family
translations. The restoration fold fixes all pointwise source/target
correspondences; only the abstract header and constructor environments and the
declaration metadata are supplied separately. -/
theorem SourceFamilyTranslations.core
    {sourceTypes : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    {Htrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv targetProdEnv}
    (H : SourceFamilyTranslations decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors)
    (htypes : decl.types = owners)
    (huvars : decl.uvars = lparams.length)
    (hnparams : decl.nparams = nparams)
    (hisUnsafe : decl.isUnsafe = isUnsafe)
    (htypesAdded : sourceVEnv.addConstVals decl.typeConstants = some envTypes)
    {envCtors' : VEnv}
    (hctorsAdded : envTypes.addConstVals decl.constructorConstants =
      some envCtors') :
    TrInductDeclCore sourceVEnv lparams nparams sourceTypes isUnsafe decl
      envTypes envCtors' := by
  refine {
    uvars := huvars
    nparams := hnparams
    isUnsafe := hisUnsafe
    typesAdded := htypesAdded
    ctorsAdded := hctorsAdded
    types := ?_ }
  rw [htypes]
  exact H.types

/-- The restored block of a nested declaration: the source declaration's
families, constructors and projection entries, the source recursors followed by
the auxiliary recursors, and their rules in the same order. -/
def restoredBlock (decl : VInductDecl)
    (primaryRecursors auxiliaryRecursors : List VConstVal)
    (primaryRules auxiliaryRules : List VDefEq) : VInductBlock where
  types := decl.typeConstants
  ctors := decl.constructorConstants
  projections := decl.projectionEntries
  recursors := primaryRecursors ++ auxiliaryRecursors
  rules := primaryRules ++ auxiliaryRules

/-- A successful lockstep installation makes every constructor recognized as
belonging to a fresh auxiliary family absent from the source abstract
environment. -/
theorem AddConstants.restoreAuxConstructorsFresh
    (H : AddConstants safety sourceProdEnv sourceVEnv entries
      loweredEnv loweredVEnv)
    (hwf : sourceProdEnv.constants.WF)
    (Howners : ConstructorOwnersPresent sourceProdEnv)
    (Hfamilies : RestoreAuxFamiliesFresh result sourceProdEnv) :
    RestoreAuxConstructorsFresh result loweredEnv sourceVEnv := by
  intro name nested auxFamily hrecognized
  rcases getNestedIfAuxCtor_refines result loweredEnv name nested auxFamily
      hrecognized with ⟨⟨info, hlookup, hfamily, hmap⟩⟩
  rcases H.origin hwf hlookup with hold | hnew
  · rcases Howners name info hold with ⟨owner, howner, -⟩
    have hfresh := Hfamilies info.induct nested hmap
    rw [howner] at hfresh
    contradiction
  · rcases hnew with ⟨entry, hentry, hname, hfound⟩
    have habstractFresh := (VEnv.addConstVals_names_fresh H.abstract).2
      entry.2 (List.mem_map.mpr ⟨entry, hentry, rfl⟩)
    have hentryNames := H.entryNames hentry
    rw [hname, hentryNames]
    exact habstractFresh

end VerifyInductive
end Lean4Lean
