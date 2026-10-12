import Lean4Lean.Verify.Inductive.Nested.Install.DependencyOrder
import Lean4Lean.Verify.Inductive.Nested.Lowering.Expansion.Formation

/-! # The rule-free restored block (`RestoredBlockBase`)

Everything about a restored nested block except its rules. The installation is recorded by its
abstract stages (`BlockStages`); the kernel insertion order is PR #43's `AddInduct.order`
(`KernelData.lean`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The recursor stage of a restored block: its recursors added to the projection stage. -/
structure RecursorsAdded (envP : VEnv) (recursors : List (ConstantInfo × VConstVal))
    (recursorVEnv : VEnv) : Prop where
  abstract : envP.addConstVals (recursors.map Prod.snd) = some recursorVEnv
  name_eq : ∀ entry ∈ recursors, entry.1.name = entry.2.name

theorem RecursorsAdded.le {envP recursorVEnv : VEnv} {recursors : List (ConstantInfo × VConstVal)}
    (H : RecursorsAdded envP recursors recursorVEnv) : envP ≤ recursorVEnv :=
  VEnv.addConstVals_le H.abstract

/-- The abstract stages of a restored block: headers, constructors, the projection stage, the
recursors. -/
structure BlockStages (sourceEnv : VEnv) (types ctors recursors : List (ConstantInfo × VConstVal))
    (projections : List VProjectionEntry) (recursorVEnv : VEnv) where
  venvTypes : VEnv
  venvCtors : VEnv
  abstract_types : sourceEnv.addConstVals (types.map Prod.snd) = some venvTypes
  abstract_ctors : venvTypes.addConstVals (ctors.map Prod.snd) = some venvCtors
  recursorsAdded : RecursorsAdded (venvCtors.addProjections projections) recursors recursorVEnv

theorem BlockStages.abstract_recursors {sourceEnv recursorVEnv : VEnv}
    {types ctors recursors : List (ConstantInfo × VConstVal)}
    {projections : List VProjectionEntry}
    (H : BlockStages sourceEnv types ctors recursors projections recursorVEnv) :
    (H.venvCtors.addProjections projections).addConstVals (recursors.map Prod.snd) =
      some recursorVEnv :=
  H.recursorsAdded.abstract

/-- Rule-independent part of a restored block (see the module documentation). -/
structure RestoredBlockBase
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    (H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv))
    (sourceEnv : VEnv) (decl : VInductDecl) (lparams : List Name)
    (nparams : Nat) (isUnsafe : Bool) (safety : DefinitionSafety) where
  loweredDecl : VInductDecl
  typeEntries : List (ConstantInfo × VConstVal)
  constructorEntries : List (ConstantInfo × VConstVal)
  recursorEntries : List (ConstantInfo × VConstVal)
  recursorVEnv : VEnv
  install : BlockStages sourceEnv typeEntries constructorEntries recursorEntries
    decl.projectionEntries recursorVEnv
  main : VInductiveType
  rest : List VInductiveType
  typesSource : decl.types = main :: rest
  sourceRecursors : List VConstVal
  auxiliaryRecursors : List VConstVal
  sourceTranslations : SourceFamilyTranslations decl lparams safety
    sourceEnv install.venvTypes (install.venvCtors.addProjections decl.projectionEntries)
    H.inductives (main :: rest) sourceRecursors
  /-- The auxiliary recursors, certified without reference to any rule list. -/
  auxiliaryRecursorTrace : AuxiliaryRecursorTranslations safety
    (install.venvCtors.addProjections decl.projectionEntries)
    (install.venvCtors.addProjections decl.projectionEntries)
    H.auxiliaries [] auxiliaryRecursors
  typeValues : typeEntries.map Prod.snd = decl.typeConstants
  constructorValues : constructorEntries.map Prod.snd = decl.constructorConstants
  recursorValues : recursorEntries.map Prod.snd = sourceRecursors ++ auxiliaryRecursors
  formationAssembly : NestedExpansionData sourceEnv decl
  formationExpanded : formationAssembly.expanded = loweredDecl
  checked : SourcePrefixOfLowered decl loweredDecl
  uvars : decl.uvars = lparams.length
  numParams : decl.nparams = nparams
  unsafeEq : decl.isUnsafe = isUnsafe
  sourceNonempty : sourceTypes ≠ []

end VerifyInductive
end Lean4Lean
