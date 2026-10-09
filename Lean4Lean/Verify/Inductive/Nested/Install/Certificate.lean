import Lean4Lean.Verify.Inductive.Nested.Restoration.TrRestoredRecursorVal
import Lean4Lean.Verify.Inductive.Nested.Install.AddInduct
import Lean4Lean.Verify.Inductive.Nested.Install.Permutation
import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceTranslations
import Lean4Lean.Verify.Inductive.Nested.Lowering.Expansion.Formation
import Lean4Lean.Verify.Inductive.Nested.Restoration.Equations.SourceIota
import Lean4Lean.Verify.Inductive.Nested.Restoration.AuxiliaryRecursorsWF
import Lean4Lean.Verify.Inductive.Nested.Install.DependencyOrder
import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceHeaders
import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.Checks
import Lean4Lean.Verify.Inductive.Nested.Lowering.Expansion.Contexts
import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceDeclaration
import Lean4Lean.Verify.Inductive.Install.Ordinary
import Lean4Lean.Verify.Inductive.Nested.Restoration.Tables

/-! The certificate of a restored nested block (section 3.3 of
the design notes): the rule-independent `RestoredBlockBase`, the
`RestoredBlockDerivation` with the restored rules, and the
`RestoredBlockCertificate`, together with the data of a validated nested run
(`NestedRun`, `NestedInstalledRun`).  Typing and abstract installation follow
dependency order (all headers, then all constructors, then all recursors),
while the executable restores family by family; the certificate relates the
two orders by a permutation. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

theorem List.nodup_of_map_nodup
    {l : List α} (f : α → β) (H : (l.map f).Nodup) : l.Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons] at H ⊢
    exact ⟨fun ha => H.1 (List.mem_map_of_mem ha), ih H.2⟩

/-- A fresh extension between fixed endpoints has a unique finite payload up
to order.  Consequently the restored block certificate needs to align just one
restoration fold with dependency order; every other fresh extension for the
same successful run follows automatically. -/
theorem FreshExtension.permOfSameTarget
    (Hleft : FreshExtension source leftEntries target)
    (Hright : FreshExtension source rightEntries target)
    (hsourceWF : source.constants.WF) : leftEntries ~ rightEntries := by
  have leftNodup : leftEntries.Nodup :=
    List.nodup_of_map_nodup (·.name) (Hleft.namesNodup hsourceWF)
  have rightNodup : rightEntries.Nodup :=
    List.nodup_of_map_nodup (·.name) (Hright.namesNodup hsourceWF)
  apply List.Subperm.antisymm
  · apply List.subperm_of_subset leftNodup
    intro ci hci
    have hfind := Hleft.findEntry hsourceWF hci
    rcases Hright.entryOrigin hsourceWF hfind with hsource |
      ⟨entry, hentry, _hname, hfound⟩
    · rw [Hleft.sourceFresh hsourceWF hci] at hsource
      contradiction
    · simpa [hfound] using hentry
  · apply List.subperm_of_subset rightNodup
    intro ci hci
    have hfind := Hright.findEntry hsourceWF hci
    rcases Hleft.entryOrigin hsourceWF hfind with hsource |
      ⟨entry, hentry, _hname, hfound⟩
    · rw [Hright.sourceFresh hsourceWF hci] at hsource
      contradiction
    · simpa [hfound] using hentry

/-- The source restored-iota shape is independent of the block's equation
payload; only the installed recursor list occurs in `NestedIotaRule`. -/
def VInductDecl.NestedIotaRule.rebaseRecursors
    {decl : VInductDecl} {source target : VInductBlock}
    {owner : VInductiveType} {ctor : VConstVal} {rule : VDefEq}
    (H : decl.NestedIotaRule source owner ctor rule)
    (hrecursors : source.recursors = target.recursors) :
    decl.NestedIotaRule target owner ctor rule where
  recursor := H.recursor
  recursor_mem := by rw [← hrecursors]; exact H.recursor_mem
  recursor_shape := H.recursor_shape
  rule_uvars := H.rule_uvars
  domains := H.domains
  lhsBody := H.lhsBody
  rhsBody := H.rhsBody
  typeBody := H.typeBody
  lhs_wrapped := H.lhs_wrapped
  rhs_wrapped := H.rhs_wrapped
  type_wrapped := H.type_wrapped
  recursorLevels := H.recursorLevels
  leadingArgs := H.leadingArgs
  ctorLevels := H.ctorLevels
  ctorArgs := H.ctorArgs
  lhs_pattern := H.lhs_pattern
  recursor_levels := H.recursor_levels
  ctor_levels := H.ctor_levels
  leading_arity := H.leading_arity
  constructor_arity := H.constructor_arity
  parameter_args := H.parameter_args
  domains_arity := H.domains_arity
  recursiveFields := H.recursiveFields
  fieldPositions := H.fieldPositions
  fieldPositions_eq := H.fieldPositions_eq
  fieldPositions_ordered := H.fieldPositions_ordered
  fields_at_positions := H.fields_at_positions
  recursiveArgs := H.recursiveArgs
  recursiveArgs_eq := H.recursiveArgs_eq
  recursive_args := H.recursive_args
  fieldVars := H.fieldVars
  fieldVars_eq := H.fieldVars_eq
  fields_in_scope := H.fields_in_scope
  minorVar := H.minorVar
  minor_in_scope := H.minor_in_scope
  rhsArgs := H.rhsArgs
  rhs_spine := H.rhs_spine
  field_args := H.field_args
  recursive_results := H.recursive_results
  rhs_guarded := by rw [← hrecursors]; exact H.rhs_guarded

theorem NestedIotaBuildCertificate.rebaseRecursors
    {decl : VInductDecl} {source target : VInductBlock}
    {rules : List VDefEq}
    (H : NestedIotaBuildCertificate decl source rules)
    (hrecursors : source.recursors = target.recursors) :
    NestedIotaBuildCertificate decl target rules where
  covered := H.covered
  shapes i hrule hctor := by
    rcases H.shapes i hrule hctor with ⟨Hrule⟩
    exact ⟨VInductDecl.NestedIotaRule.rebaseRecursors Hrule hrecursors⟩

/-- Rule-free block used while the source-family restoration fold determines
the actual source rule list. -/
def restoredShapeBlock (decl : VInductDecl)
    (primaryRecursors auxiliaryRecursors : List VConstVal) : VInductBlock :=
  restoredBlock decl primaryRecursors auxiliaryRecursors [] []

/-- The installed result of nested restoration, relating the returned kernel
environment to the constant stage of the abstract extension and retaining the
complete independent `AddInduct` judgment (including its restored rules). -/
structure NestedInstallResult (sourceEnv : VEnv)
    (decl : VInductDecl) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (safety : DefinitionSafety) (outEnv : Environment) where
  envTypes : VEnv
  envCtors : VEnv
  sourceCore : TrInductDeclCore sourceEnv lparams nparams sourceTypes isUnsafe
    decl envTypes envCtors
  baseVEnv : VEnv
  rules : List VDefEq
  checking : CheckingEnv safety outEnv baseVEnv
  valid : CheckingEnv.ValidCore safety outEnv baseVEnv
  addInduct : VEnv.AddInduct sourceEnv decl
    (baseVEnv.addDefEqRules rules)

/-- The case eliminators `es` registered by the source block restore the case eliminator of the
lowered recursor-checking environment of the lowered run `P`, which registers the restoration-free schema
`(key, ofCompilation P.loweredDecl sL [])`, and the source block registers the schema with the
same key and signature `sL`, restored by the nested compilation restoration of a specialisation
list `auxiliaries` whose restoration tables are those of the run (`RestorationTablesAgree`). -/
def CaseEliminatorsRestored {loweredEnv : Environment}
    (P : LoweredRun loweredEnv) (result : Lean4Lean.ElimNestedInductive.Result)
    (auxRec : NameMap Name) (decl : VInductDecl) (lparams : List Name)
    (es : List (Name × InductiveSignature.CaseSchema)) : Prop :=
  ∃ (key : Name) (sL : InductiveSignature)
    (auxiliaries : List InductiveSignature.ContainerSpecialization),
    P.constructors.toConstructorCheck.eliminators =
      [(key, InductiveSignature.CaseSchema.ofCompilation P.loweredDecl sL [])] ∧
    es = [(key, InductiveSignature.CaseSchema.ofCompilation decl sL auxiliaries)] ∧
    RestorationTablesAgree decl auxiliaries result loweredEnv auxRec lparams

/-- Rule-independent part of the restored block derivation: every field of
`RestoredBlockDerivation` except the two restored rule lists and their three
rule derivations.  The auxiliary recursors are instead certified by the
rule-free `AuxiliaryRecursorTranslations`.  This lets the restored generated
equations be shown well formed in `recursorVEnv` before any rule list is chosen.

The executable's fresh extension supplies only freshness and its
family-interleaved order.  Typing and abstract installation occur in
dependency order, where every mutual header precedes every constructor.
`executableOrder_perm` relates the two orders.

This separation is essential for mutual nested declarations: asking the
abstract environment to follow the executable's per-family order would require a
constructor to typecheck before later sibling headers existed. -/
structure RestoredBlockBase
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    (H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv))
    (sourceEnv : VEnv) (decl : VInductDecl) (lparams : List Name)
    (nparams : Nat) (isUnsafe : Bool) (safety : DefinitionSafety) where
  lowered : LoweredRun loweredEnv
  typeEntries : List (ConstantInfo × VConstVal)
  constructorEntries : List (ConstantInfo × VConstVal)
  recursorEntries : List (ConstantInfo × VConstVal)
  installedEnv : Environment
  recursorVEnv : VEnv
  install : BlockInstallation safety sourceProdEnv sourceEnv typeEntries
    constructorEntries recursorEntries decl.projectionEntries installedEnv
      recursorVEnv
  executableOrder_perm : ∀ actualEntries,
    FreshExtension sourceProdEnv actualEntries outEnv →
    actualEntries ~
      (typeEntries ++ constructorEntries ++ recursorEntries).map Prod.fst
  main : VInductiveType
  rest : List VInductiveType
  typesSource : decl.types = main :: rest
  sourceRecursors : List VConstVal
  auxiliaryRecursors : List VConstVal
  sourceTranslations : SourceFamilyTranslations decl lparams safety
    sourceEnv install.venvTypes ((install.venvCtors.addEliminators install.eliminators).addProjections decl.projectionEntries) H.inductives
      (main :: rest)
      sourceRecursors
  /-- The auxiliary recursors, certified without reference to any rule list. -/
  auxiliaryRecursorTrace : AuxiliaryRecursorTranslations safety
    ((install.venvCtors.addEliminators install.eliminators).addProjections decl.projectionEntries)
    ((install.venvCtors.addEliminators install.eliminators).addProjections decl.projectionEntries)
    H.auxiliaries [] auxiliaryRecursors
  typeValues : typeEntries.map Prod.snd = decl.typeConstants
  constructorValues : constructorEntries.map Prod.snd =
    decl.constructorConstants
  recursorValues : recursorEntries.map Prod.snd =
    sourceRecursors ++ auxiliaryRecursors
  formationAssembly : NestedExpansionData sourceEnv decl
  formationExpanded : formationAssembly.expanded = lowered.loweredDecl
  checked : SourcePrefixOfLowered decl lowered.loweredDecl
  uvars : decl.uvars = lparams.length
  numParams : decl.nparams = nparams
  unsafeEq : decl.isUnsafe = isUnsafe
  sourceNonempty : sourceTypes ≠ []
  /-- The declaration's case eliminators, registered by the block installation before the
  projections, are certified. -/
  eliminatorsWF : VInductBlock.EliminatorsWF sourceEnv decl (decl.caseBlock install.eliminators)
  /-- The certificate of the case eliminators replays over larger safety models of the same
  kernel environment. -/
  eliminatorsCertified : decl.CaseEliminators sourceEnv
    (fun n => sourceProdEnv.constants.find? n = none) install.eliminators
  /-- The case eliminators restore the case eliminator of the lowered recursor-checking environment. -/
  eliminatorsRestored : CaseEliminatorsRestored lowered result auxRec decl lparams
    install.eliminators

/-- The derivation of a restored block: the rule-independent
`RestoredBlockBase` together with the restored rule lists and their source and
auxiliary rule derivations. -/
structure RestoredBlockDerivation
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    (H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv))
    (sourceEnv : VEnv) (decl : VInductDecl) (lparams : List Name)
    (nparams : Nat) (isUnsafe : Bool) (safety : DefinitionSafety)
    extends RestoredBlockBase H sourceEnv decl lparams nparams isUnsafe safety where
  sourceRules : List VDefEq
  auxiliaryRules : List VDefEq
  sourceIota : SourceIotaRulesAll decl
    (restoredShapeBlock decl sourceRecursors auxiliaryRecursors)
      recursorVEnv lowered sourceTranslations
      (main :: rest) sourceRules
  auxiliaryRuleBatches : AuxiliaryRecursorRuleBatches safety ((install.venvCtors.addEliminators install.eliminators).addProjections decl.projectionEntries) H.auxiliaries
      [] [] auxiliaryRecursors auxiliaryRules
  auxiliaryWF : RestoredAuxiliaryRecursorsWF safety ((install.venvCtors.addEliminators install.eliminators).addProjections decl.projectionEntries)
      ((install.venvCtors.addEliminators install.eliminators).addProjections decl.projectionEntries)
      recursorVEnv auxiliaryRuleBatches [] [] auxiliaryRecursors auxiliaryRules

/-- A restored block derivation coerces to its rule-independent base. -/
instance
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety} :
    CoeOut (RestoredBlockDerivation H sourceEnv decl lparams nparams isUnsafe safety)
      (RestoredBlockBase H sourceEnv decl lparams nparams isUnsafe safety) :=
  ⟨RestoredBlockDerivation.toRestoredBlockBase⟩

theorem RestoredBlockDerivation.constructorArityPrefix
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (C : RestoredBlockDerivation H sourceEnv decl lparams nparams
      isUnsafe safety) :
    decl.ConstructorArityPrefix C.lowered.loweredDecl := by
  have h := C.formationAssembly.constructorArityPrefix
  rw [C.formationExpanded] at h
  exact h

/-- The remaining layout facts once the source-family translations and the
source iota rules have been constructed from the run.  Keeping this separate
prevents the executable side from replacing either aggregate with an
unrelated one. -/
structure NestedFinalAssemblyRemainder
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    (P : LoweredRun loweredEnv)
    (H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv))
    (sourceEnv : VEnv) (decl : VInductDecl) (lparams : List Name)
    (nparams : Nat) (isUnsafe : Bool) (safety : DefinitionSafety)
    (main : VInductiveType) (rest : List VInductiveType)
    (primaryRecursors auxiliaryRecursors : List VConstVal)
    (primaryRules auxiliaryRules : List VDefEq)
    (typeEntries constructorEntries recursorEntries :
      List (ConstantInfo × VConstVal))
    (canonicalProdEnv : Environment) (finalBaseVEnv : VEnv)
    (canonical : BlockInstallation safety sourceProdEnv sourceEnv typeEntries
      constructorEntries recursorEntries decl.projectionEntries canonicalProdEnv
        finalBaseVEnv) where
  kernelOrder : ∃ actualEntries,
    FreshExtension sourceProdEnv actualEntries outEnv ∧
      actualEntries ~
        (typeEntries ++ constructorEntries ++ recursorEntries).map Prod.fst
  sourceMapWF : sourceProdEnv.constants.WF
  auxiliaryTyping : AuxiliaryRecursorRuleBatches safety ((canonical.venvCtors.addEliminators canonical.eliminators).addProjections decl.projectionEntries) H.auxiliaries
      [] [] auxiliaryRecursors auxiliaryRules
  recursorValues : recursorEntries.map Prod.snd =
    primaryRecursors ++ auxiliaryRecursors
  auxiliaryWF : RestoredAuxiliaryRecursorsWF safety ((canonical.venvCtors.addEliminators canonical.eliminators).addProjections decl.projectionEntries)
      ((canonical.venvCtors.addEliminators canonical.eliminators).addProjections decl.projectionEntries)
      finalBaseVEnv auxiliaryTyping [] [] auxiliaryRecursors auxiliaryRules

/-- Assemble the full certificate once its two run-indexed aggregates (source
family translations and source iota rules) have been built. -/
noncomputable def NestedFinalAssemblyRemainder.certificate
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {P : LoweredRun loweredEnv}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {main : VInductiveType} {rest : List VInductiveType}
    {primaryRecursors auxiliaryRecursors : List VConstVal}
    {primaryRules auxiliaryRules : List VDefEq}
    {typeEntries constructorEntries recursorEntries :
      List (ConstantInfo × VConstVal)}
    {canonicalProdEnv : Environment} {finalBaseVEnv : VEnv}
    {canonical : BlockInstallation safety sourceProdEnv sourceEnv typeEntries
      constructorEntries recursorEntries decl.projectionEntries canonicalProdEnv
        finalBaseVEnv}
    (R : NestedFinalAssemblyRemainder (sourceTypes := sourceTypes) P H
      sourceEnv decl lparams nparams
      isUnsafe safety main rest primaryRecursors auxiliaryRecursors
      primaryRules auxiliaryRules typeEntries constructorEntries
      recursorEntries canonicalProdEnv finalBaseVEnv canonical)
    (Hsource : SourceFamilyTranslations decl lparams safety
      sourceEnv canonical.venvTypes ((canonical.venvCtors.addEliminators canonical.eliminators).addProjections decl.projectionEntries) H.inductives
      (main :: rest) primaryRecursors)
    (Hprimary : SourceIotaRulesAll decl
      (restoredShapeBlock decl primaryRecursors auxiliaryRecursors)
        finalBaseVEnv P Hsource
      (main :: rest) primaryRules)
    (HauxiliaryRecursors : AuxiliaryRecursorTranslations safety
      ((canonical.venvCtors.addEliminators canonical.eliminators).addProjections decl.projectionEntries)
      ((canonical.venvCtors.addEliminators canonical.eliminators).addProjections decl.projectionEntries)
      H.auxiliaries [] auxiliaryRecursors)
    (htypeValues : typeEntries.map Prod.snd = decl.typeConstants)
    (hconstructorValues : constructorEntries.map Prod.snd =
      decl.constructorConstants)
    (Hformation : NestedExpansionData sourceEnv decl)
    (hformationExpanded : Hformation.expanded = P.loweredDecl)
    (Hmaterialized : SourcePrefixOfLowered decl P.loweredDecl)
    (huvars : decl.uvars = lparams.length)
    (hnumParams : decl.nparams = nparams)
    (hunsafeEq : decl.isUnsafe = isUnsafe)
    (htypesSource : decl.types = main :: rest)
    (hsourceNonempty : sourceTypes ≠ [])
    (Helim : VInductBlock.EliminatorsWF sourceEnv decl (decl.caseBlock canonical.eliminators))
    (Hreplay : decl.CaseEliminators sourceEnv
      (fun n => sourceProdEnv.constants.find? n = none) canonical.eliminators)
    (Hrestored : CaseEliminatorsRestored P result auxRec decl lparams canonical.eliminators) :
    RestoredBlockDerivation (sourceTypes := sourceTypes) H sourceEnv
      decl lparams nparams isUnsafe safety where
  lowered := P
  typeEntries := typeEntries
  constructorEntries := constructorEntries
  recursorEntries := recursorEntries
  installedEnv := canonicalProdEnv
  recursorVEnv := finalBaseVEnv
  install := canonical
  executableOrder_perm := by
    intro actualEntries Hactual
    rcases R.kernelOrder with
      ⟨witnessEntries, Hwitness, hwitnessOrder⟩
    exact (Hactual.permOfSameTarget Hwitness R.sourceMapWF).trans
      hwitnessOrder
  main := main
  rest := rest
  typesSource := htypesSource
  sourceRecursors := primaryRecursors
  auxiliaryRecursors := auxiliaryRecursors
  sourceRules := primaryRules
  auxiliaryRules := auxiliaryRules
  sourceTranslations := Hsource
  auxiliaryRecursorTrace := HauxiliaryRecursors
  sourceIota := Hprimary
  auxiliaryRuleBatches := R.auxiliaryTyping
  typeValues := htypeValues
  constructorValues := hconstructorValues
  recursorValues := R.recursorValues
  formationAssembly := Hformation
  formationExpanded := hformationExpanded
  checked := Hmaterialized
  uvars := huvars
  numParams := hnumParams
  unsafeEq := hunsafeEq
  sourceNonempty := hsourceNonempty
  auxiliaryWF := R.auxiliaryWF
  eliminatorsWF := Helim
  eliminatorsCertified := Hreplay
  eliminatorsRestored := Hrestored

/-- Fold source equations while retaining membership of both the concrete
source family and its exact restored source recursor in the two aggregate
lists.  These are the two positional facts needed to connect a pointwise
restoration step back to its generated kernel entry and installed block. -/
theorem SourceFamilyTranslations.sourceIotaTraceOfMemberships
    {decl : VInductDecl} {lparams : List Name}
    {safety : DefinitionSafety} {sourceVEnv envTypes envCtors : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} (P : LoweredRun loweredEnv)
    {auxRec : NameMap Name} {allIndNames : List Name}
    {sourceTypes : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    {Htrace : FoldSteps
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv targetProdEnv}
    {owners : List VInductiveType} {recursors : List VConstVal}
    {block : VInductBlock}
    (Hsource : SourceFamilyTranslations decl lparams safety
      sourceVEnv envTypes envCtors Htrace owners recursors)
    (targetVEnv : VEnv)
    (Hfamilies : ∀ indType stepSource stepTarget owner
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        indType stepSource stepTarget), indType ∈ sourceTypes →
      (_Hheader : TrSourceConst sourceVEnv lparams indType.name indType.type
        owner.toVConstVal) →
      (_Hconstructors : RestoredConstructorTranslations result loweredEnv lparams safety envTypes
        Hstep.oldInfo.ctors Hstep.restored.headerEnv
          Hstep.restored.constructorEnv indType.ctors owner.ctors) →
      (_Hrecursor : SourceRecursorTranslation decl owner safety
        Hstep.restored.recursor envCtors) →
      _Hrecursor.recursor ∈ recursors →
      Nonempty (SourceIotaFamily decl block targetVEnv owner
        P Hstep)) :
    ∃ rules, SourceIotaRulesAll decl block targetVEnv P Hsource
      owners rules := by
  induction Hsource with
  | nil sourceProdEnv => exact ⟨[], .nil sourceProdEnv⟩
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest ih =>
    rcases Hfamilies _ _ _ _ Hstep (by simp) Hheader Hconstructors Hrecursor
        (by simp) with ⟨Hhead⟩
    rcases ih (fun indType stepSource stepTarget owner Hstep hmem Hheader
        Hconstructors Hrecursor hrecursor =>
      Hfamilies indType stepSource stepTarget owner Hstep (by simp [hmem])
        Hheader Hconstructors Hrecursor (by simp [hrecursor])) with
      ⟨tailRules, Hrules⟩
    exact ⟨Hhead.rules ++ tailRules,
      .cons Hstep Htail Hheader Hconstructors Hrecursor Hrest Hhead.trace
        Hrules⟩

theorem RestoredBlockDerivation.typesAdded
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    (C : RestoredBlockDerivation H sourceEnv decl lparams nparams
      isUnsafe safety) :
    sourceEnv.addConstVals decl.typeConstants = some C.install.venvTypes := by
  rw [← C.typeValues]
  exact C.install.abstract_types

theorem RestoredBlockDerivation.constructorsAdded
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    (C : RestoredBlockDerivation H sourceEnv decl lparams nparams
      isUnsafe safety) :
    C.install.venvTypes.addConstVals decl.constructorConstants =
      some C.install.venvCtors := by
  rw [← C.constructorValues]
  exact C.install.abstract_ctors

theorem RestoredBlockDerivation.sourceIotaBuild
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    (C : RestoredBlockDerivation H sourceEnv decl lparams nparams
      isUnsafe safety) :
    NestedIotaBuildCertificate decl
      (restoredBlock decl C.sourceRecursors C.auxiliaryRecursors
        C.sourceRules C.auxiliaryRules) C.sourceRules :=
  (C.sourceIota.build C.typesSource).rebaseRecursors (by
    simp [restoredShapeBlock, restoredBlock])

/-- The restored block certificate: a restored block derivation with the
translation of its compilation (`trCompilation`) and the recursor alignment
(`recursorsAligned`), both about the same selected rules and restored
constants.  Only the full validated execution constructs it. -/
structure RestoredBlockCertificate
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    (H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv))
    (sourceEnv : VEnv) (decl : VInductDecl) (lparams : List Name)
    (nparams : Nat) (isUnsafe : Bool) (safety : DefinitionSafety)
    extends RestoredBlockDerivation H sourceEnv decl lparams nparams isUnsafe safety where
  trCompilation : InductiveSignature.TrRestoredCompilation sourceEnv decl
    (restoredBlock decl sourceRecursors auxiliaryRecursors
      sourceRules auxiliaryRules) recursorVEnv recursorEntries
  recursorsAligned : NewRecursorsAligned .unsafe sourceProdEnv.constants sourceEnv
    outEnv.constants (recursorVEnv.addDefEqRules (sourceRules ++ auxiliaryRules))

/-- Assemble the independent nested judgment and the alignment of the concrete
restored environment from the same certificate. -/
noncomputable def RestoredBlockCertificate.extension
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (C : RestoredBlockCertificate H sourceEnv decl lparams nparams
      isUnsafe safety)
    (Hvalid : CheckingEnv.Valid safety sourceProdEnv sourceEnv) :
    NestedInstallResult sourceEnv decl lparams nparams sourceTypes
      isUnsafe safety outEnv := by
  let Hsource : TrInductDeclCore sourceEnv lparams nparams sourceTypes
      isUnsafe decl C.install.venvTypes C.install.venvCtors :=
    C.sourceTranslations.core C.typesSource C.uvars C.numParams C.unsafeEq
      C.typesAdded C.constructorsAdded
  let HactualExists : Nonempty { entries : List ConstantInfo //
      FreshExtension sourceProdEnv entries outEnv } := by
    rcases H.freshExtension Hvalid.tr.map_wf with ⟨entries, Hentries⟩
    exact ⟨⟨entries, Hentries⟩⟩
  let actual := Classical.choice HactualExists
  let HrestoredValid : CheckingEnv.ValidCore safety outEnv C.recursorVEnv :=
    C.install.validCoreOfFreshPermutation actual.property
      (C.executableOrder_perm actual.val actual.property) Hvalid.toValidCore
  refine {
    envTypes := C.install.venvTypes
    envCtors := C.install.venvCtors
    sourceCore := Hsource
    baseVEnv := C.recursorVEnv
    rules := C.sourceRules ++ C.auxiliaryRules
    checking := HrestoredValid.tr
    valid := HrestoredValid
    addInduct := ?_ }
  exact addInductOfRestoredInstallation
    C.install.venvTypes C.install.venvCtors
    C.sourceRecursors C.auxiliaryRecursors
    C.sourceRules C.auxiliaryRules C.install.eliminators
    (C.trCompilation.congr_eliminators C.install.eliminators).compiles
    C.formationAssembly.formation Hsource C.sourceNonempty
    (by
      rw [← C.recursorValues]
      exact C.install.abstract_recursors)
    (C.sourceTranslations.typeConstantsWF C.typesSource)
    (C.sourceTranslations.constructorConstantsWF C.typesSource)
    (by
      intro ci hci
      rcases List.mem_append.mp hci with hprimary | hauxiliary
      · exact C.sourceTranslations.sourceRecursorsWF ci hprimary
      · exact C.auxiliaryWF.recursorsWF (by simp) ci hauxiliary)
    (by
      intro df hdf
      rcases List.mem_append.mp hdf with hprimary | hauxiliary
      · exact C.sourceIota.rulesWF df hprimary
      · exact C.auxiliaryWF.rulesWF (by simp) df hauxiliary)
    C.eliminatorsWF

/-- All proof-relevant data produced by a successful nested execution before
the restored block certificate is assembled. -/
structure NestedRun
    (res : Lean4Lean.ElimNestedInductive.Result)
    (sourceProdEnv : Environment) (sourceTypes : List InductiveType)
    (sourceEnv : VEnv) (decl : VInductDecl) (lparams : List Name)
    (nparams : Nat) (isUnsafe : Bool) (safety : DefinitionSafety)
    (outEnv : Environment) where
  loweredEnv : Environment
  lowered : LoweredRun loweredEnv
  context : AddInductive.Context
  contextWF : ContextWF context
  context_env : context.env = sourceProdEnv
  context_lparams : context.lparams = lparams
  context_safety : context.safety = safety
  context_allowPrimitive : context.allowPrimitive = false
  context_venv : contextWF.venv = sourceEnv
  lowered_c : lowered.c = context
  lowered_nparams : lowered.nparams = nparams
  lowered_isUnsafe : lowered.isUnsafe =
    (context.safety != .safe)
  lowered_isUnsafe_source : lowered.isUnsafe = isUnsafe
  lowered_initialEnv : lowered.initialEnv = sourceEnv
  lowered_indTypes : lowered.indTypes = res.types.toArray
  stats : AddInductive.InductiveStats
  depth : Nat
  commonParams : List VExpr
  commonLevel : VLevel
  sourceHeaderTyping :
    checkInductiveTypes.loopType.CheckedHeaders
      contextWF.venv context.lparams nparams commonParams
        commonLevel res.types.toArray.toList
  validationFuel : FuelConfig
  context_fuel : context.fuel = validationFuel
  lowering : NestedLoweringOutputClosed sourceProdEnv
    validationFuel.inductiveFuel nparams sourceTypes
    { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res
  restoration : NestedRestorationFolds res loweredEnv sourceProdEnv
    (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
    (sourceTypes.map (·.name)) sourceTypes
    (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 ((), outEnv)
  primitiveSafe : ∃ entries,
    FreshNonprimitiveExtension false sourceProdEnv entries outEnv
  validationEnv : Environment
  validationEnvironment :
    ValidationEnvironment res loweredEnv sourceProdEnv
      (sourceTypes.map (·.name)) false sourceTypes validationEnv
  recursorTypeValidation :
    Lean4Lean.validateRestoredRecursorTypes.run validationEnv loweredEnv safety validationFuel res
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) sourceTypes
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 = .ok ()
  recursorRuleValidation :
    Lean4Lean.validateRestoredRecursorRules.run
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1))
      loweredEnv safety validationFuel res
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) sourceTypes
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 = .ok ()
  auxiliaryHeaderEnv : Environment
  headerValidationEnvironment :
    ValidationHeaderEnvironment loweredEnv sourceProdEnv
      (sourceTypes.map (·.name)) sourceTypes auxiliaryHeaderEnv
  parameterValidation :
    Lean4Lean.validateSourceConstructorTypes.run auxiliaryHeaderEnv
      lparams safety validationFuel sourceTypes = .ok ()
  auxiliaryVEnv : VEnv
  auxiliaryMLCtx : TypeChecker.MLCtx
  auxiliaryMLCtx_lctx : auxiliaryMLCtx.lctx = res.lctx
  auxiliaryMLCtxWF : auxiliaryMLCtx.WF auxiliaryVEnv lparams
  validatedAuxiliaries : NestedOccurrencesTyped auxiliaryVEnv lparams
    auxiliaryMLCtx.vlctx res
  auxiliarySelection : CDeclArray res.lctx res.params
  auxiliaryTranslations : ClosedNestedOccurrenceTypings auxiliaryVEnv
    lparams res auxiliarySelection
  sourceCore : NestedSourceDeclaration sourceEnv lparams nparams
    sourceTypes isUnsafe lowered.loweredDecl safety validationEnv
      auxiliaryHeaderEnv
  sourceCoreDecl_eq : sourceCore.sourceDecl = decl
  auxiliaryVEnv_eq_sourceCore : auxiliaryVEnv = sourceCore.envTypes

/-- Nested result retaining the lowered run, the restoration folds and the
restored block certificate that produced the public installed environment
model.  Declaration dispatch needs these to derive closure, safety tags, and
constructor coherence for this exact run. -/
structure NestedInstalledRun
    (res : Lean4Lean.ElimNestedInductive.Result)
    (sourceProdEnv : Environment) (sourceTypes : List InductiveType)
    (sourceEnv : VEnv) (decl : VInductDecl) (lparams : List Name)
    (nparams : Nat) (isUnsafe : Bool) (safety : DefinitionSafety)
    (outEnv : Environment) where
  loweredEnv : Environment
  lowered : LoweredRun loweredEnv
  context : AddInductive.Context
  contextWF : ContextWF context
  context_env : context.env = sourceProdEnv
  context_lparams : context.lparams = lparams
  context_safety : context.safety = safety
  lowered_c : lowered.c = context
  lowered_nparams : lowered.nparams = nparams
  lowered_isUnsafe : lowered.isUnsafe =
    (context.safety != .safe)
  lowered_initialEnv : lowered.initialEnv = sourceEnv
  lowered_indTypes : lowered.indTypes = res.types.toArray
  validationFuel : FuelConfig
  lowering : NestedLoweringOutputClosed sourceProdEnv
    validationFuel.inductiveFuel nparams sourceTypes
    { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res
  restoration : NestedRestorationFolds res loweredEnv sourceProdEnv
    (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
    (sourceTypes.map (·.name)) sourceTypes
    (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 ((), outEnv)
  primitiveSafe : ∃ entries,
    FreshNonprimitiveExtension false sourceProdEnv entries outEnv
  validationEnv : Environment
  validationEnvironment :
    ValidationEnvironment res loweredEnv sourceProdEnv
      (sourceTypes.map (·.name)) context.allowPrimitive sourceTypes
      validationEnv
  recursorTypeValidation :
    Lean4Lean.validateRestoredRecursorTypes.run validationEnv loweredEnv safety validationFuel res
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) sourceTypes
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 = .ok ()
  recursorRuleValidation :
    Lean4Lean.validateRestoredRecursorRules.run
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1))
      loweredEnv safety validationFuel res
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) sourceTypes
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 = .ok ()
  auxiliaryHeaderEnv : Environment
  headerValidationEnvironment :
    ValidationHeaderEnvironment loweredEnv sourceProdEnv
      (sourceTypes.map (·.name)) sourceTypes auxiliaryHeaderEnv
  parameterValidation :
    Lean4Lean.validateSourceConstructorTypes.run auxiliaryHeaderEnv
      lparams safety validationFuel sourceTypes = .ok ()
  auxiliaryVEnv : VEnv
  auxiliaryMLCtx : TypeChecker.MLCtx
  auxiliaryMLCtx_lctx : auxiliaryMLCtx.lctx = res.lctx
  auxiliaryMLCtxWF : auxiliaryMLCtx.WF auxiliaryVEnv lparams
  validatedAuxiliaries : NestedOccurrencesTyped auxiliaryVEnv lparams
    auxiliaryMLCtx.vlctx res
  auxiliarySelection : CDeclArray res.lctx res.params
  auxiliaryTranslations : ClosedNestedOccurrenceTypings auxiliaryVEnv
    lparams res auxiliarySelection
  sourceCore : NestedSourceDeclaration sourceEnv lparams nparams
    sourceTypes isUnsafe lowered.loweredDecl safety validationEnv
      auxiliaryHeaderEnv
  sourceCoreDecl_eq : sourceCore.sourceDecl = decl
  assembly : RestoredBlockCertificate restoration sourceEnv decl lparams
    nparams isUnsafe safety
  lowered_eq : assembly.lowered = lowered
  installedResult : NestedInstallResult sourceEnv decl lparams nparams
    sourceTypes isUnsafe safety outEnv

/-- The checker context used by the executable's post-lowering pipeline. -/
def nestedAddInductiveContext (env : Environment) (lparams : List Name)
    (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig) :
    AddInductive.Context :=
  { env := env, lparams := lparams,
    safety := if isUnsafe then .unsafe else .safe,
    allowPrimitive := allowPrimitive, fuel := fuel }

/-- Fully executable validated nested run.  The lowered ordinary run is
discharged by `AddInductive.run.sourceAlignedWF`; its existential checking
context and complete recursor check are retained because restoration needs
the latter. -/
theorem Environment.addInductiveAfterLowering.nestedValidatedRawSourceWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe allowPrimitive : Bool)
    (fuel : FuelConfig) (res : Lean4Lean.ElimNestedInductive.Result)
    (Hc : ContextWF
      (nestedAddInductiveContext env lparams isUnsafe allowPrimitive fuel))
    (Hclosed : MutualInductivesClosed env)
    (HenvGF : TypeChecker.EnvGhostFree (fun _ => True) env)
    (Howners : ConstructorOwnersPresent env)
    (Hpresent : ListedConstructorsPresent env)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < res.types.toArray.size)
    (HnotPartial :
      (nestedAddInductiveContext env lparams isUnsafe allowPrimitive
        fuel).safety ≠ .partial)
    (Hinputs : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {depth : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hc' : ContextWF c') →
      c'.allowPrimitive = allowPrimitive →
      c'.fuel = fuel →
      (Hsemantic :
        checkInductiveTypes.loopType.CheckedHeaders
          Hc'.venv c'.lparams nparams commonParams commonLevel
            res.types.toArray.toList) →
      PrimitiveNamesFresh c' stats nparams depth
        res.aux2nested.size res.types.toArray
        ((nestedAddInductiveContext env lparams isUnsafe allowPrimitive
          fuel).safety != .safe) Hc')
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hallowFalse : allowPrimitive = false)
    (Hlower : NestedLoweringOutputClosed env fuel.inductiveFuel nparams sourceTypes
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res)
    (hnested : res.aux2nested.size ≠ 0) :
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe allowPrimitive fuel res).WF fun outEnv =>
        ∃ c' : AddInductive.Context, ∃ Hc' : ContextWF c',
          c'.env = env ∧
          c'.safety =
            (nestedAddInductiveContext env lparams isUnsafe allowPrimitive
              fuel).safety ∧
          c'.lparams = lparams ∧
          c'.allowPrimitive = allowPrimitive ∧
          c'.fuel = fuel ∧
          Hc'.venv = Hc.venv ∧
          ∃ sourceDecl, Nonempty (NestedRun res env sourceTypes
            Hc'.venv sourceDecl lparams nparams isUnsafe
              (if isUnsafe then .unsafe else .safe) outEnv) := by
  let c := nestedAddInductiveContext env lparams isUnsafe allowPrimitive fuel
  have Hrun := AddInductive.run.sourceAlignedWF
    (types := res.types) nparams res.aux2nested.size Hc (by
      simpa [c, nestedAddInductiveContext] using Hclosed) (by
      simpa [c, nestedAddInductiveContext] using HenvGF) (by
      simpa [c, nestedAddInductiveContext] using Hpresent) hctx hnonempty
      HnotPartial
      (fun Hc' hallowPrimitive hfuel Hsemantic =>
        Hinputs Hc' hallowPrimitive hfuel Hsemantic)
  unfold Environment.addInductiveAfterLowering
  exact Hrun.bind fun loweredEnv Hinstalled => by
    simp only [hnested, ↓reduceIte]
    rcases Hinstalled with
      ⟨c', stats, depth, commonParams, commonLevel, Hc', henv, hsafety,
        hlparams, hallowPrimitive, hfuel, hvenv, Hsemantic, Hphases⟩
    have henv' : c'.env = env := by
      simpa [c, nestedAddInductiveContext] using henv
    have hsafety' : c'.safety = c.safety := hsafety
    have hlparams' : c'.lparams = lparams := by
      simpa [c, nestedAddInductiveContext] using hlparams
    have hallowPrimitive' : c'.allowPrimitive = allowPrimitive := by
      simpa [c, nestedAddInductiveContext] using hallowPrimitive
    have hfuel' : c'.fuel = fuel := by
      simpa [c, nestedAddInductiveContext] using hfuel
    have hvenv' : Hc'.venv = Hc.venv := hvenv
    rcases Hphases with
      ⟨loweredDecl, headerEnv, ctorEnv, Hheaders, R, ⟨Hprod⟩⟩
    let P : LoweredRun loweredEnv := {
      c := c'
      stats := stats
      loweredDecl := loweredDecl
      nparams := nparams
      depth := depth
      isUnsafe := c.safety != .safe
      initialEnv := Hc'.venv
      indTypes := res.types.toArray
      headerEnv := headerEnv
      ctorEnv := ctorEnv
      headers := Hheaders
      constructors := R
      recursors := Hprod }
    have Hlower' : NestedLoweringOutputClosed c'.env fuel.inductiveFuel
        nparams sourceTypes
        { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res := by
      rw [henv']
      exact Hlower
    have HlowerInitial : NestedLoweringOutputClosed c'.env fuel.inductiveFuel
        nparams sourceTypes
        { ({ lvls := lparams.map .param, newTypes := #[] } :
            Lean4Lean.ElimNestedInductive.State) with
          newTypes := sourceTypes.toArray } res := by
      simpa using Hlower'
    rcases HlowerInitial.sourceHeaderPrefix R.core rfl with
      ⟨sourceTypesVEnv, HsourceTypesAdded, HsourceHeaders⟩
    have hsourceTypesWF : sourceTypesVEnv.WF := by
      apply VEnv.WF.addConstVals Hc'.checking.tr.wf _ HsourceTypesAdded
      intro ci hci
      simp only [List.mem_map] at hci
      rcases hci with ⟨target, htarget, rfl⟩
      rcases Lean4Lean.List.Forall₂.forall_exists_r HsourceHeaders target
          htarget with
        ⟨_source, _hsource, Htarget⟩
      exact Htarget.wf
    have Hfirst : ∀ first rest, sourceTypes = first :: rest →
        ∃ target, TrExprS sourceTypesVEnv c'.lparams [] first.type target := by
      intro first rest htypes
      have hsource : 0 < sourceTypes.length := by simp [htypes]
      have htarget : 0 <
          (loweredDecl.types.take sourceTypes.length).length := by
        rw [← Lean4Lean.List.Forall₂.length_eq HsourceHeaders]
        exact hsource
      have Hhead := Lean4Lean.List.forall₂_getElem
        HsourceHeaders 0 hsource htarget
      have hfirst : sourceTypes[0] = first := by simp [htypes]
      rw [hfirst] at Hhead
      exact ⟨_, Hhead.type.mono
        (VEnv.addConstVals_le HsourceTypesAdded)⟩
    rcases HlowerInitial with
      ⟨finalLoweringState, HlowerRun, HauxFVars, HparamsNodup⟩
    have HlowerInitial' : NestedLoweringOutputClosed c'.env
        fuel.inductiveFuel nparams sourceTypes
        { ({ lvls := lparams.map .param, newTypes := #[] } :
            Lean4Lean.ElimNestedInductive.State) with
          newTypes := sourceTypes.toArray } res :=
      ⟨finalLoweringState, HlowerRun, HauxFVars, HparamsNodup⟩
    rcases HlowerRun.resultParameterMLCtx hsourceTypesWF Hfirst rfl with
      ⟨auxiliaryMLCtx, hauxiliaryLctx, hauxiliaryWF,
        hauxiliaryFresh⟩
    have hvisible : c'.safety ≤
        (if c.safety != .safe then DefinitionSafety.unsafe else .safe) := by
      rw [hsafety']
      simp [c, nestedAddInductiveContext]
    have HheaderValid : ∀ auxiliaryHeaderEnv,
        Nonempty (ValidationHeaderEnvironment loweredEnv c'.env
          (sourceTypes.map (·.name)) sourceTypes auxiliaryHeaderEnv) →
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          auxiliaryHeaderEnv sourceTypesVEnv := by
      intro auxiliaryHeaderEnv HheaderValidation
      rcases HheaderValidation with ⟨HheaderValidation⟩
      rcases HheaderValidation.validOfLowering HlowerInitial' Hc' Hprod rfl
          hvisible with
        ⟨headerVEnv, HheaderAdded, HheaderValid⟩
      have hheaderVEnv : headerVEnv = sourceTypesVEnv :=
        Option.some.inj (HheaderAdded.symm.trans HsourceTypesAdded)
      subst headerVEnv
      simpa [c, nestedAddInductiveContext, hsafety'] using HheaderValid
    let Validated := fun restoredEnv =>
      ∃ sourceDecl, Nonempty (NestedRun res env sourceTypes
        Hc'.venv sourceDecl lparams nparams isUnsafe
          (if isUnsafe then .unsafe else .safe) restoredEnv)
    have Hrestore' := Environment.restoreNestedAfterInstall.ofLoweringClosedWF
      (initialState := { lvls := lparams.map .param, newTypes := #[] })
      Hc' Hprod HlowerInitial' Hc'.checking.tr.map_wf lparams
      (if isUnsafe then .unsafe else .safe) allowPrimitive fuel
      sourceTypesVEnv HheaderValid auxiliaryMLCtx
      (by simpa only [hlparams'] using hauxiliaryWF)
      hauxiliaryLctx hauxiliaryFresh
      (hfuel' ▸ Hc'.cacheSound.mono (VEnv.addConstVals_le HsourceTypesAdded))
    have Hrestore :
        (Environment.restoreNestedAfterInstall env loweredEnv lparams
          sourceTypes (if isUnsafe then .unsafe else .safe) allowPrimitive
          fuel res).WF fun outEnv =>
            ValidatedRestoration res env loweredEnv
              (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
              (sourceTypes.map (·.name)) sourceTypes
              lparams (if isUnsafe then .unsafe else .safe) allowPrimitive fuel
              (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1
              Validated
              outEnv := by
      have HrestoreEnv := Hrestore'
      rw [henv'] at HrestoreEnv
      refine HrestoreEnv.mono ?_
      intro restoredEnv Hrestored
      rcases Hrestored.restoration with ⟨Htrace⟩
      rcases Hrestored.recursorTypeValidation with
        ⟨validationEnv, ⟨Hvalidation⟩, HrecursorTypes⟩
      have HrecursorRules := Hrestored.recursorRuleValidation
      rcases Hrestored.auxiliaryHeaderValidation with
        ⟨auxiliaryHeaderEnv, ⟨HheaderValidation⟩, Hparameters,
          HauxiliaryRun⟩
      rcases Hrestored.validated with
        ⟨Hvalidated, selection, Htranslations⟩
      have Howners' : ConstructorOwnersPresent c'.env := by
        simpa only [henv'] using Howners
      have Htrace' : NestedRestorationFolds res loweredEnv c'.env
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
          (sourceTypes.map (·.name)) sourceTypes
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1
          ((), restoredEnv) := by
        simpa only [henv'] using Htrace
      have Hvalidation' : ValidationEnvironment res
          loweredEnv c'.env (sourceTypes.map (·.name)) false sourceTypes
          validationEnv := by
        simpa only [henv', hallowFalse] using Hvalidation
      have HheaderValidation' : ValidationHeaderEnvironment loweredEnv
          c'.env (sourceTypes.map (·.name)) sourceTypes
          auxiliaryHeaderEnv := by
        simpa only [henv'] using HheaderValidation
      have Hparameters' :
          Lean4Lean.validateSourceConstructorTypes.run
            auxiliaryHeaderEnv c'.lparams c'.safety fuel sourceTypes =
              .ok () := by
        simpa only [hlparams', hsafety', c, nestedAddInductiveContext] using
          Hparameters
      have hproducerUnsafe : (c.safety != .safe) = isUnsafe := by
        simp [c, nestedAddInductiveContext]
        cases isUnsafe <;> decide
      have Hnative := HlowerInitial'.sourceCore Hc' Hprod Hsources
        Howners' rfl Htrace' Hvalidation' HheaderValidation' Hparameters'
        (hfuel' ▸ Hc'.cacheSound) hvisible
      have Hnative' : Nonempty (NestedSourceDeclaration Hc'.venv lparams
          nparams sourceTypes isUnsafe loweredDecl
          (if isUnsafe then .unsafe else .safe) validationEnv
            auxiliaryHeaderEnv) := by
        rw [hproducerUnsafe] at Hnative
        simpa only [hlparams', hsafety', c, nestedAddInductiveContext] using
          Hnative
      rcases Hnative' with ⟨N⟩
      exact {
        restoration := ⟨Htrace⟩
        primitiveSafe := Hrestored.primitiveSafe
        constructorParameterValidation := ⟨validationEnv, ⟨Hvalidation⟩⟩
        recursorTypeValidation :=
          ⟨validationEnv, ⟨Hvalidation⟩, HrecursorTypes⟩
        recursorRuleValidation := HrecursorRules
        auxiliaryHeaderValidation :=
          ⟨auxiliaryHeaderEnv, ⟨HheaderValidation⟩, Hparameters,
            HauxiliaryRun⟩
        validated := ⟨N.sourceDecl, ⟨{
            loweredEnv := loweredEnv
            lowered := P
            context := c'
            contextWF := Hc'
            context_env := henv'
            context_lparams := hlparams'
            context_safety := by
              simpa [c, nestedAddInductiveContext] using hsafety'
            context_allowPrimitive := by
              exact hallowPrimitive'.trans hallowFalse
            context_venv := rfl
            lowered_c := rfl
            lowered_nparams := rfl
            lowered_isUnsafe := by
              change (c.safety != .safe) = (c'.safety != .safe)
              rw [hsafety']
            lowered_isUnsafe_source := hproducerUnsafe
            lowered_initialEnv := rfl
            lowered_indTypes := rfl
            stats := stats
            depth := depth
            commonParams := commonParams
            commonLevel := commonLevel
            sourceHeaderTyping := Hsemantic
            lowering := Hlower
            context_fuel := hfuel'
            restoration := Htrace
            primitiveSafe := by
              simpa only [hallowFalse] using Hrestored.primitiveSafe
            validationEnv := validationEnv
            validationFuel := fuel
            validationEnvironment := by
              simpa only [hallowPrimitive', hallowFalse] using Hvalidation
            recursorTypeValidation := HrecursorTypes
            recursorRuleValidation := HrecursorRules
            auxiliaryHeaderEnv := auxiliaryHeaderEnv
            headerValidationEnvironment := HheaderValidation
            parameterValidation := Hparameters
            auxiliaryVEnv := sourceTypesVEnv
            auxiliaryMLCtx := auxiliaryMLCtx
            auxiliaryMLCtx_lctx := hauxiliaryLctx
            auxiliaryMLCtxWF := by
              simpa only [hlparams'] using hauxiliaryWF
            validatedAuxiliaries := by
              simpa only [hlparams'] using Hvalidated
            auxiliarySelection := selection
            auxiliaryTranslations := by
              simpa only [hlparams'] using Htranslations
            sourceCore := N
            sourceCoreDecl_eq := rfl
            auxiliaryVEnv_eq_sourceCore :=
              Option.some.inj (HsourceTypesAdded.symm.trans N.sourceAdded)
          }⟩⟩ }
    exact Hrestore.mono fun restoredEnv Hrestored => by
      exact ⟨c', Hc', henv',
        by simpa [c, nestedAddInductiveContext] using hsafety',
        hlparams',
        hallowPrimitive', hfuel', hvenv',
        Hrestored.validated⟩


end VerifyInductive
end Lean4Lean
