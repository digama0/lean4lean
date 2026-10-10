import Lean4Lean.Verify.Inductive.Recursor.Check
import Lean4Lean.Verify.Inductive.Rules.RulesWF
import Lean4Lean.Verify.Inductive.Rules.Coverage

/-! # The rule phase

The rules of the installed recursors are the generator's equations: each kernel rule's reduct
translates to the generated equation's reduct (`TrRecursorRule`), the generated equations are
well formed in the recursor-stage environment (as `VDefEq`s, for the compiled block), and each
model rule is typed as a schematic ι rule (`VEnv.PatTyped`, the `rules_wf` clause of
`VInductDecl.WF`; PORT_PLAN section 2.3 restates the source branch's `generatorEquationWF` in the
open equation context as the generic instance). `RuleTranslations` is the frozen interface;
`RecursorCheck.generatedRuleTranslation` is the boundary theorem.

Wave 2 scaffold: owned by the `Rules/**` agent (source branch: `Rules/{Alignment,EquationList,
EquationTranslation,EquationWF,FromTemplates,Lhs,LhsTranslation,MinorContext,MinorPremise,
Motive,RecursiveApplication,RecursiveBody,RecursiveCall,RecursiveCallScope,RecursiveResults,
Rhs,RuleSyntax,RuleTranslations,Translation}.lean`). The rule phase consumes the recursor
phase's internals (rule templates, minor contexts), so its port lands after the recursor
agent's. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The rule translations of a recursor check: coverage of every kernel rule by the generated
equation of its constructor, well-formedness of the generated equations in the recursor stage,
and the typing of every model rule as a registered ι rule. -/
structure RuleTranslations
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}  -- WAVE 2 install COMPAT
    (H : RecursorCheck R outEnv) : Prop where
  /-- Each kernel recursor's rules are, in order, the generated equations of the constructors
  it owns. -/
  trRules : List.Forall₂ (fun (owner : Fin H.signature.families.size) rval =>
      List.Forall₂ (InductiveSignature.TrRecursorRule H.generation H.outVEnv rval.levelParams)
        (H.signature.ownedConstructors owner) rval.rules)
    (List.finRange H.signature.families.size) H.rvals
  /-- The generated equations are well formed in the recursor stage (the `rules` clause of
  `VInductBlock.WF` for the compiled block). -/
  equationsWF : ∀ df ∈ H.generation.equations, df.WF H.outVEnv
  /-- `VInductDecl.WF.rules_wf`: every model rule is typed as a schematic ι rule in the
  recursor stage. -/
  rules_wf : ∀ r ∈ H.recs, ∀ ru ∈ r.rules, ∀ hc : ru.rhs.Closed,
    H.outVEnv.PatTyped
      (SimplePattern.iota r.name r.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
      (SimplePattern.iotaRHS r.name ru.ctor
        r.numParams r.numMotives r.numMinors r.numIndices ru.ctorParams ru.nfields ru.rhs hc,
        .true)

/-- `InductiveSignature.Models` reads only the source fields of the declaration. -/
theorem _root_.Lean4Lean.InductiveSignature.Models.withRecs {s : InductiveSignature} {env : VEnv}
    {decl : VInductDecl} (H : s.Models env decl) (recs : List VRecursor) :
    s.Models env (decl.withRecs recs) where
  uvars := H.uvars
  nparams := H.nparams
  safety := H.safety
  families := H.families
  constructors := H.constructors
  classifiedFields := H.classifiedFields
  constructorArity := H.constructorArity

/-- `InductiveSignature.Compiles` reads only the source fields of the declaration. -/
theorem _root_.Lean4Lean.InductiveSignature.Compiles.withRecs {env : VEnv} {decl : VInductDecl}
    {block : VInductBlock} (H : InductiveSignature.Compiles env decl block)
    (recs : List VRecursor) : InductiveSignature.Compiles env (decl.withRecs recs) block :=
  let ⟨s, g, envTypes, hm, rest⟩ := H.generated
  ⟨s, g, envTypes, hm.withRecs recs, rest⟩

section
variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv outEnv : Environment}
  {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}  -- WAVE 2 install COMPAT

/-- Every model rule fires on a constructor with the signature's parameter count. -/
theorem RecursorCheck.ruleCtorParams (H : RecursorCheck R outEnv) : H.RuleCtorParams :=
  fun r hr ru hru => (H.rules_ctorParams r hr ru hru).trans H.models.nparams.symm

end

namespace RuleTranslations

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats} {decl : VInductDecl}
  {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv} {indTypes : Array InductiveType}
  {ctorEnv outEnv : Environment}
  {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}  -- WAVE 2 install COMPAT
  {H : RecursorCheck R outEnv}

/-- The compiled block of the recursor check: the declaration's constants, the generated
recursors and equations, the declaration's projection entries. -/
def block (_T : RuleTranslations H) : VInductBlock where
  types := decl.typeConstants
  ctors := decl.constructorConstants
  recursors := H.generation.recursors
  rules := H.generation.equations
  projections := decl.projectionEntries

/-- The block compiles the declaration (`InductiveSignature.Compiles`). -/
theorem compiles (T : RuleTranslations H) :
    InductiveSignature.Compiles sourceEnv decl T.block :=
  ⟨H.signature, H.generation, R.headerVEnv, H.models, R.core.typesAdded, H.admissible,
    ⟨R.ctorVEnv, R.core.ctorsAdded, H.ihsWellTyped, H.familyTypesWF⟩,
    H.recursorNames, rfl, rfl⟩

/-- The block is well formed in the source environment (`VInductBlock.WF`). -/
theorem blockWF (T : RuleTranslations H) : T.block.WF sourceEnv :=
  ⟨R.headerVEnv, R.ctorVEnv, H.outVEnv, R.core.typesAdded, R.core.ctorsAdded,
    by
      have h := H.recsAdded
      rw [VInductDecl.addRecs_eq_addConstVals, VInductDecl.withRecs_recs, H.recursors_eq] at h
      exact h,
    R.typesWF, R.ctorsWF,
    by rw [show T.block.recursors = H.recs.map (·.toVConstVal) from H.recursors_eq.symm]
       intro ci hci; obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hci; exact H.recsWF r hr,
    T.equationsWF⟩

/-- The declaration compiles to the block (`VInductDecl.CompilesTo`, the ordinary case of
`CompiledInductive`). -/
theorem compilesTo (T : RuleTranslations H) (hnonempty : indTypes.toList ≠ []) :
    H.decl'.CompilesTo sourceEnv T.block := by
  have hnames : ((T.block.types ++ T.block.ctors ++ T.block.recursors).map (·.name)).Nodup := by
    have hR := H.addTypesCtorsProjsRecs
    rw [VInductDecl.addTypesCtorsProjsRecs_eq] at hR
    obtain ⟨envF, hF, -⟩ := Option.map_eq_some_iff.1 hR
    have hnd := VEnv.addConst_foldlM_nodup (nm := Prod.fst) (ci := Prod.snd) hF
    have hrecs : T.block.recursors = H.recs.map (·.toVConstVal) := H.recursors_eq.symm
    rw [hrecs]
    simpa [block, VInductDecl.consts, VInductDecl.typeConstants,
      VInductDecl.constructorConstants, List.map_append, List.map_map, Function.comp_def,
      List.map_flatMap] using hnd
  exact CompiledInductive.ordinary
    (VInductDecl.SourceWF.withRecs (TrInductDeclCore.sourceWF_ofNonempty R.core
      (TrInductDeclCore.nonempty R.core hnonempty)) H.recs)
    (R.formation.withRecs H.recs).formationWF (T.compiles.withRecs H.recs) T.blockWF rfl rfl rfl
    hnames

/-- The model recursors and rules are read off the block (`VInductDecl.RecsOf`): the recursors
by `recursors_eq`, the rules through `TrRecursorRule` and `TrRecursor` agreeing on the reducts
(`VRecRule.OfEquation.ofTr`). -/
theorem recsOf (T : RuleTranslations H) : H.decl'.RecsOf T.block :=
  ⟨H.recursors_eq, (H.rules_ofEquation T.trRules H.ruleCtorParams).1,
    (H.rules_ofEquation T.trRules H.ruleCtorParams).2⟩

/-- `VInductDecl.RecsCompiled` of the installed declaration. -/
theorem recsCompiled (T : RuleTranslations H) (hnonempty : indTypes.toList ≠ []) :
    H.decl'.RecsCompiled sourceEnv :=
  ⟨T.block, T.compilesTo hnonempty, T.recsOf⟩

/-- The recursor half of `VInductDecl.WF`. -/
theorem recursorsWF (T : RuleTranslations H) (hnonempty : indTypes.toList ≠ []) :
    RecursorsWF sourceEnv H.decl' where
  recsCompiled := T.recsCompiled hnonempty
  recs_wf envP hP := by
    have : envP = R.envP := by
      have h := R.addTypesCtorsProjs (decl := decl)
      rw [show H.decl'.addTypesCtorsProjs sourceEnv = decl.addTypesCtorsProjs sourceEnv from rfl,
        h] at hP
      exact (Option.some.inj hP).symm
    subst this; exact H.recsWF
  rec_shape := H.rec_shape
  rules_nodup := H.rules_nodup
  rules_ctor envC hC r hr ru hru := by
    have : envC = R.ctorVEnv := by
      have h := R.addTypesCtors (decl := decl)
      rw [show H.decl'.addTypesCtors sourceEnv = decl.addTypesCtors sourceEnv from rfl, h] at hC
      exact (Option.some.inj hC).symm
    subst this; exact H.rules_ctor r hr ru hru
  rule_shape := H.rule_shape
  rules_wf envR hR := by
    have : envR = H.outVEnv := by
      rw [H.addTypesCtorsProjsRecs] at hR; exact (Option.some.inj hR).symm
    subst this; exact T.rules_wf

end RuleTranslations

section
variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv outEnv : Environment}
  {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}  -- WAVE 2 install COMPAT

/-- Coverage of the installed entries, read on the kernel recursors they carry. -/
theorem rulesCovered_of_entries {s : InductiveSignature} {g : InductiveSignature.Instance s}
    {venv : VEnv} {entries : List (ConstantInfo × VConstVal)} {rvals : List RecursorVal}
    (hcov : List.Forall₂ (fun (owner : Fin s.families.size) (e : ConstantInfo × VConstVal) =>
      ∃ rval, e.1 = .recInfo rval ∧
        List.Forall₂ (InductiveSignature.TrRecursorRule g venv rval.levelParams)
          (s.ownedConstructors owner) rval.rules)
      (List.finRange s.families.size) entries)
    (hr : entries.map Prod.fst = rvals.map .recInfo) :
    List.Forall₂ (fun (owner : Fin s.families.size) rval =>
      List.Forall₂ (InductiveSignature.TrRecursorRule g venv rval.levelParams)
        (s.ownedConstructors owner) rval.rules)
      (List.finRange s.families.size) rvals := by
  have hlen : entries.length = rvals.length := by
    simpa using congrArg List.length hr
  apply List.forall₂_of_getElem
    ((List.Forall₂.length_eq hcov).trans hlen)
  intro j hj hj'
  have hjE : j < entries.length := hlen ▸ hj'
  obtain ⟨rval, he, H⟩ := List.forall₂_getElem hcov j hj hjE
  have := congrArg (·[j]?) hr
  simp only [List.getElem?_map, List.getElem?_eq_getElem hjE, List.getElem?_eq_getElem hj',
    Option.map_some, Option.some.injEq, he] at this
  cases this
  exact H

/-- Transport of the rule clauses along the identification of the installation's generator
with the interface's (`installation_signature`, `installation_generation`). -/
theorem ruleClauses_transport {s s' : InductiveSignature} (hs : s = s')
    {g : InductiveSignature.Instance s} {g' : InductiveSignature.Instance s'} (hg : HEq g g')
    {venv : VEnv} {rvals : List RecursorVal}
    (hcov : List.Forall₂ (fun (owner : Fin s.families.size) rval =>
      List.Forall₂ (InductiveSignature.TrRecursorRule g venv rval.levelParams)
        (s.ownedConstructors owner) rval.rules)
      (List.finRange s.families.size) rvals)
    (hwf : ∀ df ∈ g.equations, df.WF venv) :
    List.Forall₂ (fun (owner : Fin s'.families.size) rval =>
      List.Forall₂ (InductiveSignature.TrRecursorRule g' venv rval.levelParams)
        (s'.ownedConstructors owner) rval.rules)
      (List.finRange s'.families.size) rvals ∧
    ∀ df ∈ g'.equations, df.WF venv := by
  subst hs; cases hg; exact ⟨hcov, hwf⟩

/-- The rule coverage and the equations' well-formedness of a recursor check, read off its
installation (`RecursorInstallation.rulesCovered`, `equationsWF'`, `Rules/Coverage.lean`). -/
theorem RecursorCheck.ruleClauses (H : RecursorCheck R outEnv) :
    H.RulesCovered ∧ H.EquationsWF := by
  have hcov := rulesCovered_of_entries H.installation.rulesCovered H.installation_rvals
  have hwf := H.installation.equationsWF'
  rw [H.installation_outVEnv] at hcov hwf
  exact ruleClauses_transport H.installation_signature H.installation_generation hcov hwf

/-- Rule coverage: each kernel rule's constructor, field count and reduct are the generated
equation's. -/
theorem RecursorCheck.rulesCovered (H : RecursorCheck R outEnv) : H.RulesCovered :=
  H.ruleClauses.1

/-- The generated equations are well formed in the recursor stage. -/
theorem RecursorCheck.equationsWF (H : RecursorCheck R outEnv) : H.EquationsWF :=
  H.ruleClauses.2

end

/-- The boundary theorem of the rule phase: the recursor check determines its rule
translations. No rule, telescope, or equation is chosen by the caller. The `rules_wf` clause is
the `PatTyped` restatement of the generated equations' `VDefEq.WF` (`RecursorCheck.rules_wf_of`,
PORT_PLAN section 2.3). -/
theorem RecursorCheck.generatedRuleTranslation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}  -- WAVE 2 install COMPAT
    (H : RecursorCheck R outEnv) : RuleTranslations H where
  trRules := H.rulesCovered
  equationsWF := H.equationsWF
  rules_wf := H.rules_wf_of H.rulesCovered H.equationsWF H.ruleCtorParams

end VerifyInductive
end Lean4Lean
