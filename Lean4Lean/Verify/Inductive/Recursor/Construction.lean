import Lean4Lean.Verify.Inductive.Recursor.RecInfoCheck
import Lean4Lean.Verify.Inductive.Install.Metadata
import Lean4Lean.Verify.Inductive.Recursor.Binders.FieldOpening
import Lean4Lean.Verify.Inductive.TypeAnnotations

import Lean4Lean.Verify.Inductive.Constructor.Check
import Lean4Lean.Verify.Inductive.Constructor.CheckedFormation

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
namespace VerifyInductive

/-- A successful `checkRecursiveFields` establishes, for a safe declaration, that the fields
given induction hypotheses by the rule templates are those the positivity check marked. -/
theorem AddInductive.checkRecursiveFields.WF
    {isUnsafe : Bool} {positivity : List (List (List Bool))}
    {recInfos : Array AddInductive.RecInfo} {c : AddInductive.Context} :
    (AddInductive.checkRecursiveFields isUnsafe positivity recInfos c).WF fun _ =>
      isUnsafe = false →
        recInfos.toList.map (fun info => info.ruleTemplates.toList.map (·.recursiveMask)) =
          positivity := by
  intro u h hsafe
  subst hsafe
  unfold AddInductive.checkRecursiveFields at h
  by_cases heq : (recInfos.toList.map fun info =>
      info.ruleTemplates.toList.map (·.recursiveMask)) = positivity
  · exact heq
  · have hne : ((recInfos.toList.map fun info =>
        info.ruleTemplates.toList.map (·.recursiveMask)) == positivity) = false := by
      simpa using heq
    simp [hne] at h

/-- The recursor construction: the executable's elimination level and `mkRecInfos` result,
run on top of a constructor check, with their translations, before the recursor entries are
chosen and installed. The construction's signature and generator (`generator`) are derived
from these fields. -/
structure RecursorConstruction
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv : Environment}
    (R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    where
  sourceSafety : isUnsafe = (c.safety != .safe)
  elimLevel : Level
  elimLevelAdmissible : AddInductive.AdmissibleElimLevel c.lparams elimLevel
  /-- The elimination level is the one `getElimLevel` computes in the constructor
  environment. Freshness of a universe parameter alone does not justify large elimination. -/
  elimLevelChecked : AddInductive.getElimLevel stats indTypes
    { c with env := ctorEnv } = .ok elimLevel
  lparamsNodup : c.lparams.Nodup
  kTarget : Bool
  kTargetChecked : KEligible stats indTypes kTarget
  recInfos : Array AddInductive.RecInfo
  localContext : AddInductive.Context
  localWF : BindingContextWF localContext
  localExtends : BindingContextLE { c with
    env := ctorEnv
    typeCheckerLParams := some <|
      AddInductive.getRecLevelParams elimLevel c.lparams } localContext
  recursorDepth : Nat
  recursorWF : RecursorContextWF localContext
    (AddInductive.getRecLevelParams elimLevel c.lparams)
  recursorEnv : recursorWF.venv = R.context.venv
  /-- The executable type-checks every generated recursor type before any
  recursor is installed.  These translations are the only derivations of the
  closed recursor telescopes available before installation: the minor
  premises mention motives, so their translations cannot be rebuilt from the
  free-variable contexts of the motive pass without strengthening. -/
  recursorTypes : TrRecursorTypes R.context.venv localContext.lparams elimLevel
    localContext stats indTypes recInfos
  parameterSuffix : RecursorParameterContextSuffix recursorWF stats
    recursorDepth
  parameterDecls : parameterSuffix.parameterDecls =
    (R.recursorHeaders.parameterSuffix.toRecursorContext
      elimLevelAdmissible).parameterDecls
  validStats : RecursorValidAppStatsWF recursorWF.venv
    (AddInductive.getRecLevelParams elimLevel c.lparams)
    recursorWF.mlctx.vlctx stats decl recursorDepth
  noIndConsts : VLCtx.NoIndConsts (decl.types.map (·.name))
    recursorWF.mlctx.vlctx
  bindings : RecInfoBindings localContext recInfos
  origins : RecInfoBinderTypes localContext recInfos
  templates : RuleTemplatesMatch stats recInfos origins
  templateTyping : TypedRuleTemplates recursorWF decl
    stats recInfos elimLevel parameterSuffix.parameterDecls origins
  minorSources : MinorsAndIndicesMatchSource stats indTypes origins
  minorTyping : TypedMinors recursorWF origins
    parameterSuffix.parameterDecls
  majorTypes : TrBinderTypes recursorWF origins.majorTypes
  majorShapes : MajorPremiseTypes stats recInfos origins.majorTypes
    localContext.env.isTypeAnnotationWrapper
  motiveTypes : TrBinderTypes recursorWF origins.motiveTypes
  motiveShapes : MotiveTypes localContext recInfos
    origins.motiveTypes elimLevel
  motiveTelescopes : RecInfoMotiveTelescopes recursorWF stats decl
    (R.recursorHeaders.parameterSuffix.toRecursorContext
      elimLevelAdmissible).parameterDecls.toCtx recInfos elimLevel
  indexRows : TrBinderTypesPerFamily recursorWF origins.indexTypes
  params : FVarArrayIn localContext stats.params
  noAlias : RecInfoBindings.NoAlias stats.params recInfos
  outerOrder : RecInfoOuterOrder recursorWF params bindings
  arities : RecInfoArities stats recInfos
  minorCounts : forall i, i < recInfos.size ->
    recInfos[i]!.minors.size = indTypes[i]!.ctors.length
  cardinality : RecursorCounts stats recInfos decl
  /-- For a safe declaration the fields that receive an induction hypothesis are those the
  constructor phase's positivity check classified as recursive (`checkRecursiveFields`). -/
  recursiveFieldsChecked : isUnsafe = false →
    recInfos.toList.map (fun info => info.ruleTemplates.toList.map (·.recursiveMask)) =
      R.classes

end VerifyInductive
end Lean4Lean

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

theorem RecursorConstruction.sourceFamilyCount
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) : H.recInfos.size = indTypes.size := by
  have htypes := Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
  have hrecords := H.cardinality.records
  simp only [Array.length_toList] at htypes
  omega

theorem RecursorConstruction.sourceMinorOffsetBound
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    recursorMinorOffset indTypes owner + localIndex < decl.ownedConstructors.length := by
  have hsourceOwner : owner < indTypes.size := by rw [← H.sourceFamilyCount]; exact howner
  have hsize := (H.origins.minors owner howner).size_eq
  have hcounts := H.minorCounts owner howner
  have hroom := recursorMinorOffset_room indTypes owner hsourceOwner
  have htotal := Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length R.core
  simp only [ownedConstructors, List.length_flatMap, List.length_map] at htotal
  rw [List.length_flatMap] at hroom
  omega

end Lean4Lean.VerifyInductive
