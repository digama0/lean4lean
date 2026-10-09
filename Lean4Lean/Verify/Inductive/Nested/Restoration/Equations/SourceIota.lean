import Lean4Lean.Verify.Inductive.Nested.Restoration.Translations
import Lean4Lean.Theory.Inductive
import Lean4Lean.Verify.Inductive.Nested.Restoration.ExprReplace
import Lean4Lean.Verify.Inductive.Nested.Restoration.Steps
import Lean4Lean.Verify.Inductive.Nested.Lowering.Run
import Lean4Lean.Verify.Inductive.Nested.Restoration.Equations.SourceIotaFamilies
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.Inductive.Constructor.Positivity
import Lean4Lean.Verify.Inductive.Rules.Alignment




namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The recursor that a source restoration step looks up in the lowered kernel
environment is the generated recursor entry at the corresponding source-family
position, so the ordinary equation proof and the restoration steps are indexed
by one shared rule list. -/
theorem RecursorCheck.restoredSourceInfo_eq_generated
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    (H : RecursorCheck R.toConstructorCheck outEnv)
    (owner : Nat) (hentry : owner < H.entries.length)
    (Hstep : RestoredRecursorStep result outEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (holdRecName : oldRecName = Lean.mkRecName indTypes[owner]!.name) :
    Hstep.oldInfo = (H.generated.entry owner hentry).info := by
  let E := H.generated.entry owner hentry
  have hlookup := H.findRecursorOfMem (List.getElem_mem hentry)
  have hlookupE : outEnv.find? (Lean.mkRecName indTypes[owner]!.name) =
      some (.recInfo E.info) := by
    change outEnv.find? H.entries[owner].1.name =
      some H.entries[owner].1 at hlookup
    rw [E.source_eq] at hlookup
    change outEnv.find? E.info.name = some (.recInfo E.info) at hlookup
    rwa [E.name] at hlookup
  have hstepLookup : outEnv.find? (Lean.mkRecName indTypes[owner]!.name) =
      some (.recInfo Hstep.oldInfo) := by
    simpa [holdRecName] using Hstep.lookup
  exact ConstantInfo.recInfo.inj
    (Option.some.inj (hstepLookup.symm.trans hlookupE))

/-- A complete list of restored source nested iota rules gives the
append-form certificate `NestedIotaBuildCertificate`. -/
theorem NestedIotaListCertificate.toBuild
    {decl : VInductDecl} {block : VInductBlock} {rules : List VDefEq}
    (H : NestedIotaListCertificate decl block rules) :
    NestedIotaBuildCertificate decl block rules where
  covered := Nat.le_of_eq H.length
  shapes i hrule hctor := H.rules i hctor hrule

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The restored source equations, flattened and ordered: pointwise nested iota
rules along a list of owner/constructor pairs, which fixes both order and
cardinality. -/
abbrev RestoredSourceIotaListTrace
    (decl : VInductDecl) (block : VInductBlock)
    (owned : List (VInductiveType × VConstVal))
    (rules : List VDefEq) : Prop :=
  List.Forall₂ (fun ownerCtor rule =>
    Nonempty (decl.NestedIotaRule block ownerCtor.1 ownerCtor.2 rule))
    owned rules

/-- The restored source equations along `ownedConstructors` give the ordered
`NestedIotaListCertificate` of nested compilation. -/
theorem NestedIotaListCertificate.ofForall₂
    {decl : VInductDecl} {block : VInductBlock} {rules : List VDefEq}
    (H : RestoredSourceIotaListTrace decl block
      decl.ownedConstructors rules) :
    NestedIotaListCertificate decl block rules where
  length :=
    (Lean4Lean.List.Forall₂.length_eq H).symm
  rules i hctor hrule :=
    Lean4Lean.List.forall₂_getElem H i hctor hrule

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The owned constructors of a list of owners, in order: the order in which
restored source equations are listed one family at a time. -/
def ownedConstructorsFor (owners : List VInductiveType) :
    List (VInductiveType × VConstVal) :=
  owners.flatMap fun owner => owner.ctors.map (owner, ·)

theorem ownedConstructorsFor_eq
    (decl : VInductDecl) :
    ownedConstructorsFor decl.types = decl.ownedConstructors :=
  rfl

/-- The restored source equations, family by family. Each family's batch is
indexed by the constructors of the corresponding source owner, and the
result list is the concatenation in mutual-family order. -/
inductive SourceIotaRulesByFamily
    (decl : VInductDecl) (block : VInductBlock) :
    List VInductiveType → List VDefEq → Prop
  | nil : SourceIotaRulesByFamily decl block [] []
  | cons {owner owners head tail}
      (Hhead : List.Forall₂ (fun ownerCtor rule =>
        Nonempty (decl.NestedIotaRule block ownerCtor.1 ownerCtor.2 rule))
        (owner.ctors.map (owner, ·)) head)
      (Htail : SourceIotaRulesByFamily decl block owners tail) :
      SourceIotaRulesByFamily decl block (owner :: owners)
        (head ++ tail)

/-- Family-local batches flatten to the ordered list
`RestoredSourceIotaListTrace` along `ownedConstructorsFor`. -/
theorem SourceIotaRulesByFamily.forall₂
    (H : SourceIotaRulesByFamily decl block owners rules) :
    RestoredSourceIotaListTrace decl block
      (ownedConstructorsFor owners) rules := by
  induction H with
  | nil => exact .nil
  | @cons owner owners head tail Hhead Htail ih =>
    simpa [ownedConstructorsFor] using
      _root_.List.Forall₂.append' Hhead ih

/-- When the owners are the declaration's families, the family-local batches
give the complete ordered source iota certificate
`NestedIotaListCertificate`. -/
theorem SourceIotaRulesByFamily.certificate
    (Hrules : SourceIotaRulesByFamily decl block owners rules)
    (htypes : decl.types = owners)
    :
    NestedIotaListCertificate decl block rules := by
  apply NestedIotaListCertificate.ofForall₂
  rw [← ownedConstructorsFor_eq decl, htypes]
  exact Hrules.forall₂

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- The abstract rules of one source recursor along the executable
rule-restoration list `RulesRestoration`: one well-formed nested iota rule per
restored rule and constructor, so the abstract rule list has one entry per
executable rule. -/
inductive SourceIotaRules
    (decl : VInductDecl) (block : VInductBlock)
    (owner : VInductiveType)
    (result : Lean4Lean.ElimNestedInductive.Result)
    (prodEnv : Environment) (P : LoweredRun prodEnv)
    (targetVEnv : VEnv) (auxRec : NameMap Name)
    (oldRecName newRecName : Name) :
    ∀ {oldRules newRules},
      RulesRestoration result prodEnv auxRec oldRecName newRecName
        oldRules newRules →
      List VConstVal → List VDefEq → Prop
  | nil : SourceIotaRules decl block owner result prodEnv
      P targetVEnv auxRec oldRecName newRecName (.nil) [] []
  | cons
      (Hrule : RuleRestoration result prodEnv auxRec oldRecName newRecName
        oldRule newRule)
      (Hrules : RulesRestoration result prodEnv auxRec oldRecName newRecName
        oldRules newRules)
      (abstractRule : VDefEq)
      (Hshape : decl.NestedIotaRule block owner ctor abstractRule)
      (Hwf : abstractRule.WF targetVEnv)
      (Hrest : SourceIotaRules decl block owner result prodEnv
        P targetVEnv auxRec oldRecName newRecName Hrules ctors rules) :
      SourceIotaRules decl block owner result prodEnv P
        targetVEnv auxRec oldRecName newRecName (.cons Hrule Hrules) (ctor :: ctors)
        (abstractRule :: rules)

theorem SourceIotaRules.forall₂
    (H : SourceIotaRules decl block owner result prodEnv
      P targetVEnv auxRec oldRecName newRecName Hrules ctors rules) :
    List.Forall₂ (fun ctor rule =>
      Nonempty (decl.NestedIotaRule block owner ctor rule)) ctors rules := by
  induction H with
  | nil => exact .nil
  | cons Hrule Hrules abstractRule Hshape Hwf Hrest ih =>
    exact .cons ⟨Hshape⟩ ih

theorem SourceIotaRules.rulesWF
    (H : SourceIotaRules decl block owner result prodEnv
      P targetVEnv auxRec oldRecName newRecName Hrules ctors rules) :
    ∀ rule ∈ rules, rule.WF targetVEnv := by
  intro rule hrule
  induction H with
  | nil => simp at hrule
  | cons Hrule Hrules abstractRule Hshape Hwf Hrest ih =>
    rcases List.mem_cons.mp hrule with rfl | hrule
    · exact Hwf
    · exact ih hrule

/-- The abstract rule batch of one restored source recursor, with its
`SourceIotaRules` along the executable rule restoration. -/
structure SourceIotaFamily
    (decl : VInductDecl) (block : VInductBlock) (targetVEnv : VEnv)
    (owner : VInductiveType)
    (P : LoweredRun loweredEnv)
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      indType sourceProdEnv targetProdEnv) where
  rules : List VDefEq
  trace : SourceIotaRules decl block owner result loweredEnv
    P targetVEnv auxRec (Lean.mkRecName indType.name)
      Hstep.restored.recursor.restored.newRecName
      Hstep.restored.recursor.restored.restoration.rules owner.ctors rules

/-- The source iota rules of every family, indexed simultaneously by the
source-family translations and the restoration steps, so family order,
constructor order and rule counts follow from the run. -/
inductive SourceIotaRulesAll
    (decl : VInductDecl) (block : VInductBlock) (targetVEnv : VEnv)
    {lparams : List Name} {safety : DefinitionSafety}
    {sourceVEnv envTypes envCtors : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} (P : LoweredRun loweredEnv)
    {auxRec : NameMap Name}
    {allIndNames : List Name} :
    ∀ {sourceTypes : List InductiveType}
        {sourceProdEnv targetProdEnv : Environment}
        {Htrace : FoldSteps
          (RestoredInductiveStep result loweredEnv auxRec allIndNames)
          sourceTypes sourceProdEnv targetProdEnv}
        {owners : List VInductiveType} {recursors : List VConstVal},
      SourceFamilyTranslations decl lparams safety sourceVEnv
        envTypes envCtors Htrace owners recursors →
      List VInductiveType → List VDefEq → Prop
  | nil {lparams safety sourceVEnv envTypes envCtors result loweredEnv auxRec
      allIndNames} (sourceProdEnv : Environment) :
      SourceIotaRulesAll decl block targetVEnv
        P
        (SourceFamilyTranslations.nil
          (decl := decl) (lparams := lparams) (safety := safety)
          (sourceVEnv := sourceVEnv) (envTypes := envTypes)
          (envCtors := envCtors) (result := result) (loweredEnv := loweredEnv)
          (auxRec := auxRec) (allIndNames := allIndNames) sourceProdEnv) [] []
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
        sourceVEnv envTypes envCtors Htail owners recursors)
      (Hhead : SourceIotaRules decl block owner result loweredEnv
        P targetVEnv auxRec (Lean.mkRecName indType.name)
        Hstep.restored.recursor.restored.newRecName
        Hstep.restored.recursor.restored.restoration.rules owner.ctors
        headRules)
      (Hrules : SourceIotaRulesAll decl block targetVEnv P Hrest
        owners tailRules) :
      SourceIotaRulesAll decl block targetVEnv P
        (.cons Hstep Htail Hheader Hconstructors Hrecursor Hrest)
        (owner :: owners) (headRules ++ tailRules)

theorem SourceIotaRulesAll.familyTrace
    (H : SourceIotaRulesAll decl block targetVEnv P Hsource owners
      rules) :
    SourceIotaRulesByFamily decl block owners rules :=
  match H with
  | .nil _ => .nil
  | .cons _ _ _ _ _ _ Hhead Hrules =>
    .cons (by simpa using Hhead.forall₂) Hrules.familyTrace

/-- The source iota rules of every family give the complete source iota
certificate `NestedIotaListCertificate` of nested compilation. -/
theorem SourceIotaRulesAll.certificate
    (H : SourceIotaRulesAll decl block targetVEnv P Hsource owners
      rules)
    (htypes : decl.types = owners) :
    NestedIotaListCertificate decl block rules :=
  H.familyTrace.certificate htypes

theorem SourceIotaRulesAll.build
    (H : SourceIotaRulesAll decl block targetVEnv P Hsource owners
      rules)
    (htypes : decl.types = owners) :
    NestedIotaBuildCertificate decl block rules :=
  (H.certificate htypes).toBuild

theorem SourceIotaRulesAll.length
    (H : SourceIotaRulesAll decl block targetVEnv P Hsource owners
      rules)
    (htypes : decl.types = owners) :
    rules.length = decl.ownedConstructors.length :=
  (H.certificate htypes).length

theorem SourceIotaRulesAll.rulesWF
    (H : SourceIotaRulesAll decl block targetVEnv P Hsource owners
      rules) :
    ∀ rule ∈ rules, rule.WF targetVEnv := by
  intro rule hrule
  induction H with
  | nil => simp at hrule
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest Hhead Hrules ih =>
    rcases List.mem_append.mp hrule with hrule | hrule
    · exact Hhead.rulesWF rule hrule
    · exact ih hrule

end VerifyInductive
end Lean4Lean
