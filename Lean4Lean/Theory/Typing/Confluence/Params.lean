import Lean4Lean.Theory.Typing.Confluence.Patterns
import Lean4Lean.Theory.Typing.FullChurchRosser
import Lean4Lean.Theory.Typing.Confluence.GeneratedIotaCoverage
import Lean4Lean.Theory.Typing.Confluence.QuotEquationCoverage
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.Typing.DefinitionPatterns
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.Typing.Confluence.RegistryOfWF
import Lean4Lean.Theory.Typing.Confluence.QuotPatterns
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Confluence.HeadRegistryData
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Typing.Confluence.GeneratedIotaPatterns
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.Typing.Confluence.DefinitionHistory
import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.Inductive.CaseReductionData
import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.CaseReduction
import Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLift
import Lean4Lean.Theory.Typing.RecursorRuleRegistration
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Typing.FullReduction
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Std.Basic
import Lean4Lean.Theory.Typing.Confluence.RecursorDeclarationProvenance
import Lean4Lean.Theory.Typing.Confluence.RecursorRegistration
import Lean4Lean.Theory.Typing.ConstructorRigidity
import Lean4Lean.Theory.Typing.StoredRuleHeads

/-! The `Params` instance of a well-formed environment, built from its
head registry. The structure-major and generated iota soundness facts are passed
in by the caller; they are proved in separate files. -/

namespace Lean4Lean.VEnv
open InductiveSignature HeadRegistry

/-- Assemble `Params` from the head registry and the remaining facts. -/
@[instance_reducible] noncomputable def Params.ofRegistry {E : VEnv} {registry : Registry} {declarations : List VDecl}
    (henv : E.WF) (contract : registry.EnvironmentContract E declarations) (U : Nat)
    (sound : ∀ {Γ : List VExpr} {p : Pattern} {r : p.RHS × p.Check} {e A m1 m2},
      OnCtx Γ (E.IsType U) → GeneratedIotaPattern E registry.recursors p r →
      p.Matches e m1 m2 → E.HasType U Γ e A → E.IsDefEqU U Γ e (r.1.apply m1 m2))
    (structMajor : ∀ {rc mr cc kc} {r : (Pattern.app ((Pattern.const rc).varN mr)
        ((Pattern.const cc).varN kc)).RHS × (Pattern.app ((Pattern.const rc).varN mr)
        ((Pattern.const cc).varN kc)).Check} {Γ family info lsc fs ls ps},
      ConcretePattern registry E (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r →
      OnCtx Γ (E.IsType U) → E.projections family info →
      E.HasType U Γ (VExpr.mkApps (.const cc lsc) fs) (VExpr.mkApps (.const family ls) ps) →
      fs.length = kc → cc = info.ctorName ∧ kc = info.nparams + info.numFields)
    (iotaParams : ∀ {rc mr cc kc} {r : (Pattern.app ((Pattern.const rc).varN mr)
        ((Pattern.const cc).varN kc)).RHS × (Pattern.app ((Pattern.const rc).varN mr)
        ((Pattern.const cc).varN kc)).Check} {family info lsc lsc' ps ps' fields g g'},
      ConcretePattern registry E (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r →
      E.projections family info → cc = info.ctorName →
      ((Pattern.const cc).varN kc).Matches (VExpr.mkApps (.const cc lsc) (ps ++ fields)) lsc g →
      ((Pattern.const cc).varN kc).Matches (VExpr.mkApps (.const cc lsc') (ps' ++ fields)) lsc' g' →
      ps.length = info.nparams → ps'.length = info.nparams →
      (∀ (m1 : List VLevel) (g1 : ((Pattern.const rc).varN mr).Path → VExpr),
        Pattern.RHS.apply (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
            m1 (Sum.elim g1 g) r.1 =
          Pattern.RHS.apply (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
            m1 (Sum.elim g1 g') r.1) ∧
      (∀ (m1 : List VLevel) (g1 : ((Pattern.const rc).varN mr).Path → VExpr)
        (df : VExpr → VExpr → Prop),
        Pattern.Check.OK (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
            df m1 (Sum.elim g1 g) r.2 →
          Pattern.Check.OK (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
            df m1 (Sum.elim g1 g') r.2))
    (schemaStruct : ∀ {Γ rule actual family info ls ps},
      CaseRedex E U Γ rule actual → OnCtx Γ (E.IsType U) →
      E.projections family info →
      E.HasType U Γ (VExpr.mkApps (.const actual.ctorName actual.ctorLevels) actual.ctorArguments)
        (VExpr.mkApps (.const family ls) ps) →
      actual.ctorName = info.ctorName ∧
        actual.ctorArguments.length = info.nparams + info.numFields ∧
        rule.numFields ≤ info.numFields) : Params where
  env := E
  henv := henv
  univs := U
  recursorData := registry.recursors
  recursorData_registered h := let ⟨a, b, _⟩ := contract.recursors _ _ h; ⟨a, b⟩
  Pat := ConcretePattern registry E
  pat_storedRule h := ConcretePattern.origin henv contract h
  pat_recursor h := ConcretePattern.recursor henv contract h
  pat_simple h := ConcretePattern.simple henv contract h
  pat_uniq h h' hs hi := ConcretePattern.uniq henv contract h h' hs hi
  pat_wf hΓ h hm ht hc := by
    rcases h with h | ⟨_, h⟩ | h
    · exact DefinitionPattern.sound henv hΓ (fun _ _ h => (contract.definitions _ _ h).1) h hm ht
    · exact QuotPattern.sound henv hΓ h hm ht hc
    · exact sound hΓ h hm ht
  pat_app_l h hs := ConcretePattern.app_l henv contract h hs
  pat_app_l_uniq h h' hs hs' hb := ConcretePattern.app_l_uniq henv contract h h' hs hs' hb
  pat_app_uniq h h' hs hs' hl hr := ConcretePattern.app_uniq henv contract h h' hs hs' hl hr
  pat_const_not_unfolding h := ConcretePattern.const_not_unfolding henv contract h
  recursorData_quot hq := ConcretePattern.recursor_quot henv contract hq
  pat_ctor_rigid h := ConcretePattern.ctor_rigid henv contract h
  projection_ctor_rigid hl := henv.projectionCtorRigid hl
  pat_struct_major h hΓ hl hs hlen := structMajor h hΓ hl hs hlen
  pat_iota_params h hl hcc hm hm' hps hps' := iotaParams h hl hcc hm hm' hps hps'
  schema_struct_major hm hΓ hl hs := schemaStruct hm hΓ hl hs

section
variable [Params]
open Params

private theorem PatternReductionTrace.of_definition
    (hpat : ∀ {p r}, DefinitionPattern registry p r → Pat p r)
    (H : PatternReductionTrace env univs (DefinitionPattern registry) Γ left right) :
    PatternReductionTrace env univs Pat Γ left right := by
  induction H with
  | refl => exact .refl
  | trans _ _ ih ih' => exact .trans ih ih'
  | pattern hp hm hc => exact .pattern (hpat hp) hm hc
  | schema h => exact .schema h
  | beta => exact .beta
  | app _ _ ih ih' => exact .app ih ih'
  | lam _ ih => exact .lam ih

/-- Coverage of every installed equation from the head registry, given
coverage of the recursor equations at the specializations that the generated
iota guard rejects. -/
theorem equation_covered_of_registry {registry : Registry} {declarations : List VDecl}
    (contract : registry.EnvironmentContract env declarations)
    (hdef : ∀ {p r}, DefinitionPattern registry.definitions p r → Pat p r)
    (hquot : registry.quotient = true → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hnat : ∀ {p r}, GeneratedIotaPattern env recursorData p r → Pat p r)
    (hdata : recursorData = registry.recursors)
    (hzero : ∀ {Γ : List VExpr} {data : RecursorData}
      {index : Fin data.schema.signature.constructors.size} {equation : VDefEq}
      {levels : List VLevel}, OnCtx Γ (env.IsType univs) →
      registry.recursors data.name = some data → RecursorRegistered env data →
      data.schema.signature.constructors[index].owner = data.owner →
      data.equation index = some equation →
      (∀ level ∈ levels, level.WF univs) → levels.length = equation.uvars →
      data.largeTarget = true →
      (data.schema.sourceLevel data.owner data.levels).inst levels ≈ .zero →
      ∃ left right, FullReduction Γ (equation.lhs.instL levels) left ∧
        FullReduction Γ (equation.rhs.instL levels) right ∧ NormalEq Γ left right)
    (hΓ : OnCtx Γ (env.IsType univs)) (hdf : env.defeqs equation)
    (hw : ∀ level ∈ levels, level.WF univs) (hl : levels.length = equation.uvars) :
    ∃ left right, FullReduction Γ (equation.lhs.instL levels) left ∧
      FullReduction Γ (equation.rhs.instL levels) right ∧ NormalEq Γ left right := by
  rcases contract.equations equation hdf with
    ⟨value, lookup, registered, rfl⟩ | ⟨registered, enabled, _, _, rfl⟩ |
    ⟨data, lookup, _, registered, index, owner, generated⟩
  · have htrace := (DefinitionPattern.equation_trace (U := univs) (Γ := Γ) lookup
      ((contract.definitions _ _ lookup).1.closed henv) hl).of_definition hdef
    exact ⟨_, _, htrace.parRedS.full, .rfl,
      .refl (IsDefEq.extra (Γ := Γ) hdf hw hl).hasType.2⟩
  · exact registered.equation_covered hΓ (hquot enabled) hw hl
  · by_cases hguard : data.largeTarget = true ∧
        (data.schema.sourceLevel data.owner data.levels).inst levels ≈ .zero
    · exact hzero hΓ lookup registered owner generated hw hl hguard.1 hguard.2
    · refine registered.equation_join hnat (by rw [hdata]; exact lookup) owner generated hw hl ?_
      exact fun h1 h2 => hguard ⟨h1, h2⟩

end

end Lean4Lean.VEnv
