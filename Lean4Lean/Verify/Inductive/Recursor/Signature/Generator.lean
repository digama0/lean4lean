import Lean4Lean.Verify.Inductive.Recursor.Construction
import Lean4Lean.Verify.Inductive.Recursor.Signature.MinorSpine
import Lean4Lean.Verify.Inductive.Recursor.Signature.Parameters
import Lean4Lean.Verify.Inductive.Recursor.Signature.MotiveGroup
import Lean4Lean.Verify.Inductive.Recursor.Signature.Constructors
import Lean4Lean.Verify.Inductive.Context.TypeAnnotations
import Lean4Lean.Verify.Inductive.Recursor.Signature.Assembly
import Lean4Lean.Verify.Inductive.Recursor.Signature.HypothesisArgumentUniverses
import Lean4Lean.Verify.Inductive.Recursor.Signature.FamilyTypesWF

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- A signature constructor matches a minor premise of the executable: the minor's recorded
constructor traversal has the constructor's name, number of fields and recursive positions,
and each induction hypothesis of the minor has as type the unannotated type of the matching
recursive field, with the same target family and number of binders. -/
structure ConstructorMatchesMinor
    (s : InductiveSignature) (S : MinorPremiseType)
    (ctor : InductiveSignature.Constructor s.families.size) where
  traversal : ConstructorFieldTraversal
  traversal_eq : S.traversal = some traversal
  name : ctor.name = S.constructor.name
  fields : ctor.fields.length = traversal.fields.size
  recursivePositions : (InductiveSignature.Instance.recursiveFields (s := s) ctor).map Prod.fst =
    traversal.recursivePositions
  hypotheses : MinorInductionHypothesisTypes S.sourceFullContext S.recursiveFields S.hypotheses
  hypotheses_eq : S.hypothesis_type_origins = some hypotheses
  recursiveCount : (InductiveSignature.Instance.recursiveFields (s := s) ctor).length = S.hypotheses.size
  recursive : ∀ j (hj : j < (InductiveSignature.Instance.recursiveFields (s := s) ctor).length),
    ∃ root sourceType,
      ∃ O : InductionHypothesisType hypotheses.stats hypotheses.recInfos
        root S.recursiveFields[j]! sourceType,
      ∃ D : FVarDeclAt S.sourceFullContext S.hypotheses j,
        BindingContextLE hypotheses.fieldRoot root ∧
        D.type = (sourceType.consumeTypeAnnotationsVerified
          S.sourceFullContext.env.isTypeAnnotationWrapper) ∧
        (InductiveSignature.Instance.recursiveFields (s := s) ctor)[j].2.target.val = O.ownerIdx ∧
        (InductiveSignature.Instance.recursiveFields (s := s) ctor)[j].2.binders.length = O.args.size

/-- A signature and instance that generate the executable's recursors: the signature models
the source declaration and has its parameters, families and constructor order, the instance
is admissible with the recursor's universe levels, names and target level, the executable's
parameter-motive-minor telescope and recursor types translate to the generated ones in the
recursor-checking environment, the generated recursor types and family types are well formed
there, and each minor matches its signature constructor (`ConstructorMatchesMinor`). The
signature's binder syntax is that of the generated declarations, so it need not coincide with
the checked-formation signature. -/
structure RecursorConstruction.GeneratedBy
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) where
  signature : InductiveSignature
  generation : InductiveSignature.Instance signature
  models : signature.Models sourceEnv decl
  params : signature.params = R.parameterScope.toCtx.reverse
  families : signature.families = H.families
  admissible : generation.Admissible R.headerVEnv
  uvars : generation.uvars = (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
  levels : generation.levels = recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible
  target : VLevel.ofLevel (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    H.elimLevel = some generation.targetLevel
  familyCount : signature.families.size = indTypes.size
  familyName : ∀ owner (howner : owner < signature.families.size),
    signature.families[owner].name = indTypes[owner]!.name
  names : ∀ owner, generation.recursorName owner = signature.families[owner].name.str "rec"
  constructorCount : signature.constructors.size = decl.ownedConstructors.length
  constructorOrder : List.Forall₂
    (fun ctor pair => signature.families[ctor.owner].name = pair.1.name ∧
      ctor.name = pair.2.name)
    signature.constructors.toList decl.ownedConstructors
  minorTranslation : TrExprS R.context.venv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
    (H.localContext.lctx.mkForall stats.params <|
      H.localContext.lctx.mkForall (H.recInfos.map (·.motive)) <|
      H.localContext.lctx.mkForall (H.recInfos.flatMap (·.minors)) (.sort .zero))
    (VExpr.wrapForalls (generation.params ++ generation.motives ++ generation.minors) (.sort .zero))
  types : ∀ owner (howner : owner < signature.families.size),
    TrExprS R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      (generation.recursorType ⟨owner, howner⟩)
  generatedIHsWellTyped : generation.GeneratedIHsWellTyped R.context.venv
  familyTypesWF : signature.FamilyTypesWF R.context.venv decl.uvars
  sourceOrigins : ∀ owner (howner : owner < H.recInfos.size)
    localIndex (hlocal : localIndex < H.origins.minorTypes[owner]!.size),
    ∃ index : Fin signature.constructors.size,
      index.val = recursorMinorOffset indTypes owner + localIndex ∧
      signature.constructors[index].owner.val = owner ∧
      signature.fieldTypes signature.constructors[index] = H.declFieldDomains owner howner localIndex hlocal ∧
      signature.constructors[index].indices = H.declConstructorIndices owner howner localIndex hlocal ∧
      Nonempty (ConstructorMatchesMinor signature (H.origins.minorShapes owner howner localIndex hlocal)
        signature.constructors[index])

/-- Each constructor of the construction's signature matches its minor premise. -/
theorem RecursorConstruction.signature_origins
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (HU : H.ArgumentUniverses)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    Nonempty (ConstructorMatchesMinor (H.signature HU)
      (H.origins.minorShapes owner howner localIndex hlocal)
      (H.constructorAt HU owner howner localIndex hlocal)) := by
  have hsourceOwner : owner < indTypes.size := by rwa [← H.sourceFamilyCount]
  obtain ⟨_, _, _, hHas, traversal, htrav, _, hfieldsT, _, _, _, _, _, _, _⟩ :=
    H.minorSources.rows owner howner hsourceOwner localIndex hlocal
  obtain ⟨origins, horig, _, _⟩ :=
    (H.origins.minorShapes owner howner localIndex hlocal).hypothesisTypeOrigins_exists
      stats H.recInfos hHas
  have hspec := H.recursiveShapes_spec HU owner howner localIndex hlocal
  have hrec := H.constructorAt_recursiveFields HU owner howner localIndex hlocal
  refine ⟨{
    traversal := traversal
    traversal_eq := htrav
    name := rfl
    fields := ?_
    recursivePositions := ?_
    hypotheses := origins
    hypotheses_eq := horig
    recursiveCount := ?_
    recursive := ?_ }⟩
  · simp [RecursorConstruction.constructorAt, H.sourceFields_length, hfieldsT]
  · rw [hrec]; exact hspec.1 traversal htrav
  · rw [hrec]; exact hspec.2.1
  · intro j hj
    have hj' : j < (H.recursiveShapes HU owner howner localIndex hlocal).length := by
      rw [hrec] at hj; exact hj
    obtain ⟨root, sourceType, O, D, hLE, hD, htarget, hbinders⟩ := hspec.2.2.2.1 origins horig j hj'
    refine ⟨root, sourceType, O, D, hLE, hD, ?_, ?_⟩
    · rw [← htarget]
      exact congrArg (fun x => x.2.target.val) (List.getElem_of_eq hrec hj)
    · rw [← hbinders]
      exact congrArg (fun x => x.2.binders.length) (List.getElem_of_eq hrec hj)

/-- Given the universe support of the induction-hypothesis arguments, the construction's
signature `H.signature HU` with its generated instance generates the executable's
recursors. -/
noncomputable def RecursorConstruction.generatorOf
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (HU : H.ArgumentUniverses) :
    H.GeneratedBy := by
  have D := H.signatureSpec HU
  have hfamCount : (H.signature HU).families.size = indTypes.size := by
    simp [H.families_size, H.sourceFamilyCount]
  refine {
    signature := H.signature HU
    generation := H.generatedInstance (H.signature HU)
    models := D.models
    params := rfl
    families := rfl
    admissible := H.generatedInstance_admissible D.uvars D.params D.families D.size
      (fun owner howner localIndex hlocal => by
        obtain ⟨hk, _, h2, h3, h4⟩ := D.constructor owner howner localIndex hlocal
        exact ⟨hk, h2, h3, h4⟩)
    uvars := rfl
    levels := rfl
    target := H.generatedInstance_target _
    familyCount := hfamCount
    familyName := ?_
    names := fun _ => rfl
    constructorCount := D.size
    constructorOrder := ?_
    minorTranslation := H.signature_minorTranslation HU
    types := H.signature_types HU
    generatedIHsWellTyped := H.signature_generatedIHsWellTyped HU
    familyTypesWF := H.unannotatedFamilyTypesWF rfl rfl
    sourceOrigins := ?_ }
  · intro owner howner
    have howner' : owner < H.recInfos.size := by
      simpa [H.families_size] using howner
    have hsourceOwner : owner < indTypes.size := by rwa [← H.sourceFamilyCount]
    have hdeclOwner : owner < decl.types.length := by
      rw [← H.cardinality.records]; exact howner'
    have hname := D.family_name ⟨owner, howner⟩ owner howner' rfl
    have hownerTr := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt R.core
      owner (by simpa using hsourceOwner) hdeclOwner
    have hsourceBang : indTypes[owner]! = indTypes[owner] := by
      simp [hsourceOwner]
    rw [hsourceBang]
    refine hname.trans ?_
    simpa using hownerTr.header.name
  · apply List.forall₂_of_getElem (by simp)
    intro k hk hk'
    obtain ⟨owner, howner, localIndex, hlocal, rfl⟩ := H.flatMinorIndex k hk'
    have hk2 : recursorMinorOffset indTypes owner + localIndex <
        (H.signature HU).constructors.size := by
      simpa using hk
    simp only [Array.getElem_toList]
    exact D.constructorNames owner howner localIndex hlocal hk2
  · intro owner howner localIndex hlocal
    obtain ⟨hk, _, hown, hft, hidx⟩ := D.constructor owner howner localIndex hlocal
    refine ⟨⟨recursorMinorOffset indTypes owner + localIndex, hk⟩, rfl, hown, hft, hidx, ?_⟩
    simp only [Fin.getElem_fin]
    rw [H.signature_constructor HU owner howner localIndex hlocal hk]
    exact H.signature_origins HU owner howner localIndex hlocal

/-- The generator of the recursor construction: `generatorOf` at `argumentUniverses`, an
explicit construction rather than a choice, so that its signature is definitionally
`H.signature H.argumentUniverses` and the facts proved about the construction (for instance
`generatedBy_shapeTranslations`) apply to it. -/
noncomputable def RecursorConstruction.generator
    (H : RecursorConstruction R) : H.GeneratedBy :=
  H.generatorOf H.argumentUniverses

theorem RecursorConstruction.generatedBy_signature
    (H : RecursorConstruction R) :
    H.generator.signature = H.signature H.argumentUniverses := rfl

noncomputable def RecursorConstruction.generationSignature
    (H : RecursorConstruction R) : InductiveSignature := H.generator.signature

noncomputable def RecursorConstruction.generationInstance
    (H : RecursorConstruction R) : InductiveSignature.Instance H.generationSignature :=
  H.generator.generation

noncomputable def RecursorConstruction.recursorTarget
    (H : RecursorConstruction R) (owner : Nat) : VConstVal :=
  if h : owner < H.generationSignature.families.size then
    H.generationInstance.recursor ⟨owner, h⟩
  else { name := .anonymous, uvars := 0, type := .sort .zero }

theorem RecursorConstruction.recursorTarget_eq
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat) (howner : owner < indTypes.size) :
    H.recursorTarget owner = {
      name := Lean.mkRecName indTypes[owner]!.name
      uvars := (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      type := (H.recursorTarget owner).type } := by
  have hf : owner < H.generationSignature.families.size := by
    simpa [generationSignature, H.generator.familyCount] using howner
  simp only [recursorTarget, dif_pos hf, InductiveSignature.Instance.recursor]
  have hn := H.generator.names ⟨owner, hf⟩
  have hfName := H.generator.familyName owner hf
  change H.generationInstance.recursorName ⟨owner, hf⟩ = _ at hn
  rw [hn]
  simp only [generationInstance, H.generator.uvars]
  congr 1
  exact congrArg (fun name : Name => name.str "rec") hfName

theorem RecursorConstruction.typeTranslations
    {R : RecursorInput c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R)
    (owner : Nat) (howner : owner < indTypes.size) :
    TrExprS R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      (H.recursorTarget owner).type := by
  have hf : owner < H.generationSignature.families.size := by
    simpa [generationSignature, H.generator.familyCount] using howner
  simp only [recursorTarget, dif_pos hf, InductiveSignature.Instance.recursor]
  exact H.generator.types owner hf

end Lean4Lean.VerifyInductive
