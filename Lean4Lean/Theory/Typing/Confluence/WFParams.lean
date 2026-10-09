import Lean4Lean.Theory.Typing.Confluence.Params
import Lean4Lean.Theory.Typing.Confluence.GeneratedIotaSoundness
import Lean4Lean.Theory.Typing.Confluence.StructureMajor
import Lean4Lean.Theory.Typing.EliminatorCoherenceOfWF
import Lean4Lean.Theory.Typing.Confluence.SingletonCoverage
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.Typing.FullChurchRosser
import Lean4Lean.Theory.Typing.FullReduction
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.Typing.Confluence.RegistryOfWF
import Lean4Lean.Theory.Typing.Confluence.HeadRegistryData
import Lean4Lean.Theory.Typing.Confluence.GeneratedIotaPatterns
import Lean4Lean.Theory.Typing.Confluence.RecursorDeclarationProvenance
import Lean4Lean.Theory.Typing.RecursorRuleRegistration
import Lean4Lean.Theory.Typing.Confluence.Patterns
import Lean4Lean.Theory.CanonicalEq
import Lean4Lean.Theory.Typing.Confluence.QuotPatterns
import Lean4Lean.Theory.Typing.DefinitionPatterns
import Lean4Lean.Theory.Inductive.CaseReductionData
import Lean4Lean.Theory.Typing.CaseReduction

/-! The `Params` instance of a well-formed environment, its equation
coverage, and the confluence theorem `VEnv.WF.church_rosser` for every
well-formed environment with canonical `Eq`. Every field is a theorem. -/

namespace Lean4Lean.VEnv
open InductiveSignature HeadRegistry

/-- The chosen declaration history and head registry of a well-formed
environment. -/
noncomputable def WF.registry {env : VEnv} (henv : env.WF) : Registry :=
  Classical.choose (Classical.choose_spec henv.headRegistry)

theorem WF.registry_contract {env : VEnv} (henv : env.WF) :
    henv.registry.EnvironmentContract env (Classical.choose henv.headRegistry) :=
  Classical.choose_spec (Classical.choose_spec henv.headRegistry)

/-- The confluence parameters of a well-formed environment at universe
bound `U`. -/
@[instance_reducible] noncomputable def WF.params {env : VEnv} (henv : env.WF)
    (U : Nat) : Params :=
  Params.ofRegistry henv henv.registry_contract U
    (fun hΓ h hm ht => GeneratedIotaPattern.sound henv hΓ
      (fun _ _ h => let ⟨a, b, _⟩ := henv.registry_contract.recursors _ _ h; ⟨a, b⟩) h hm ht)
    (fun h hΓ hl hs hlen => ConcretePattern.struct_major henv h hΓ hl hs hlen)
    (fun h hl hcc hm hm' hps hps' =>
      ConcretePattern.iota_params henv henv.registry_contract h hl hcc hm hm' hps hps')
    (fun hm hΓ hl hs => CaseRedex.struct_major henv henv.eliminatorsCoherent hm hΓ hl hs)

end Lean4Lean.VEnv

namespace Lean4Lean.VEnv
open InductiveSignature HeadRegistry

/-- Zero-source large-elimination coverage for the concrete instance: every
singleton recursor equation, at a universe specialization where the generated iota
guard fails, is joinable. -/
def WF.SingletonCoverage {env : VEnv} (henv : env.WF) (U : Nat) :
    Prop :=
  letI := henv.params U
  ∀ {Γ : List VExpr} {data : RecursorData}
    {index : Fin data.schema.signature.constructors.size} {equation : VDefEq}
    {levels : List VLevel}, OnCtx Γ (env.IsType U) →
    henv.registry.recursors data.name = some data → RecursorRegistered env data →
    data.schema.signature.constructors[index].owner = data.owner →
    data.equation index = some equation →
    (∀ level ∈ levels, level.WF U) → levels.length = equation.uvars →
    data.largeTarget = true →
    (data.schema.sourceLevel data.owner data.levels).inst levels ≈ .zero →
    ∃ left right, FullReduction Γ (equation.lhs.instL levels) left ∧
      FullReduction Γ (equation.rhs.instL levels) right ∧ NormalEq Γ left right

theorem WF.equationCoverage {env : VEnv} (henv : env.WF)
    (hzero : henv.SingletonCoverage U) :
    @FullEquationCoverage (henv.params U) := by
  letI := henv.params U
  refine ⟨fun hΓ hdf hw hl => equation_covered_of_registry henv.registry_contract
    (fun h => .inl h) (fun h => .inr (.inl ⟨h, .intro (henv.registry_contract.quotientRegistered h)⟩))
    (fun h => .inr (.inr h)) rfl (fun hΓ' hl' hr' ho' hg' hw' hlen' h1 h2 =>
      hzero hΓ' hl' hr' ho' hg' hw' hlen' h1 h2) hΓ hdf hw hl⟩

/-- Confluence of definitional equality in a well-formed environment with
coherent eliminator registrations, given zero-source singleton coverage. -/
theorem WF.church_rosser_of_singletonCoverage {env : VEnv} (henv : env.WF)
    (hzero : henv.SingletonCoverage U)
    (hΓ : OnCtx Γ (env.IsType U)) (H : env.IsDefEq U Γ e₁ e₂ A) :
    letI := henv.params U
    ∃ e₁' e₂', FullReduction Γ e₁ e₁' ∧ FullReduction Γ e₂ e₂' ∧ NormalEq Γ e₁' e₂' := by
  letI := henv.params U
  haveI := henv.equationCoverage hzero
  obtain ⟨-, -, h⟩ := IsDefEq.full_church_rosser (Γ := Γ) hΓ H
  exact h

/-- Zero-source large-elimination coverage holds in every well-formed
environment with canonical `Eq`: the installed equation of a singleton recursor
at a universe specialization with source `Prop` is joined by the singleton
prefix unfolding (`RecursorRegistered.zero_join`). -/
theorem WF.singletonCoverage {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq) (U : Nat) :
    henv.SingletonCoverage U := by
  letI := henv.params U
  intro Γ data index equation levels hΓ hlookup hreg howner hgen hw hl hlarge hzero
  exact RecursorRegistered.zero_join heq hΓ hlookup hreg howner hgen hw hl hlarge hzero

/-- **Church-Rosser for definitional equality.** In a well-formed environment
with canonical `Eq`, two definitionally equal terms reduce, in the full
presentation, to normally equal terms: terms equal up to universe levels,
proof irrelevance and eta.

Canonical `Eq` types the singleton prefix unfolding at a universe
specialization whose source is `Prop`: the proof fields of the reconstructed
constructor are extracted by the recursor itself into `Prop`, with the earlier
data fields cast along `Eq`. Without `Eq` this extraction is not available: in
the well-formed `Eq`-free environment of the design notes, section
5.1, the equation of a singleton whose proof field `h : P v` follows a data
field `v` is not joinable at a `Prop` source (argued, not checked in Lean).

Coherence of case eliminators with projection metadata is part of
well-formedness (`VInductDecl.ProjectionsCoherent`, a premise of
`VEnv.WF'.inductEliminators`, and `VEnv.WF.eliminatorsCoherent`). Without it,
the example in `EliminatorCoherence.lean` (projections of
`structure S : Type where a ::` and the case schema of
`inductive S : Type | b : S` over an axiom `S.b : S`) would make the case
applications at `S.a` and `S.b` definitionally equal without a common reduct. -/
theorem WF.church_rosser {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (H : env.IsDefEq U Γ e₁ e₂ A) :
    letI := henv.params U
    ∃ e₁' e₂', FullReduction Γ e₁ e₁' ∧ FullReduction Γ e₂ e₂' ∧ NormalEq Γ e₁' e₂' :=
  henv.church_rosser_of_singletonCoverage (henv.singletonCoverage heq U) hΓ H

end Lean4Lean.VEnv
