import Lean4Lean.Theory.Typing.ConstructorRigidity
import Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLift
import Batteries.Tactic.OpenPrivate
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Inductive.RecursorEquationCoverage
import Lean4Lean.Theory.Inductive.CaseRuleConstructors
import Lean4Lean.Theory.Typing.RecursorRuleRegistration
import Lean4Lean.Theory.Typing.PatternCaptures
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.Typing.DefinitionRegistryInstallation
import Lean4Lean.Theory.Typing.RecursorRegistryInstallation
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Inductive.CaseRegistration
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.Inductive.CaseReductionData
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.Typing.ProjectionConstructorFamily
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.Typing.QuotLiftTelescope
import Lean4Lean.Theory.Typing.RecursorMajorFamily
import Lean4Lean.Theory.Typing.DefinitionPatterns
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.CaseReduction

/-! Structure majors of registered case eliminators.

A case schema is registered (`VEnv.WF'.inductEliminators`) over a base
environment that is only required to agree with the current one on its
equations and to contain the certified declaration's constants. Without a
further premise, nothing would tie the certified declaration to the projection
metadata already registered for the same family names, and the confluence of
the full reduction would fail: `EliminatorsCoherent` below is needed.

Counterexample. Start from the empty environment and register, by
`inductProjections` over the axioms `S : Type` and `S.a : S`, the structure
`structure S : Type where a ::` (one constructor `S.a`, no parameters, no
fields). Add the axiom `S.b : S`, and register by `inductEliminators`, over
the empty base, the case schema of `inductive S : Type | b : S`. Every premise
other than `VInductDecl.ProjectionsCoherent` holds: the schema is certified
over the empty base, the environment contains the constants `S` and `S.b` at
that declaration's values, no equation was
added, the schema needs no projection names, and its key is fresh. In a
context with a motive `m : S → Type` and a minor `x : m S.b`, the case
application `elim S (m, x) S.b` computes to `x`, while structure eta gives
`S.b ≡ S.a`, so the same application is definitionally equal to
`elim S (m, x) S.a`, which has no rule and no reduct other than eta
re-expansions; `x` and it are not normally equal, and proof irrelevance does
not apply at `Type`. Hence `IsDefEq.full_church_rosser` would be false for this
environment, and the case-schema structure-major fact needs
`VEnv.EliminatorsCoherent`.

The specification excludes the example: `inductEliminators` requires
`VInductDecl.ProjectionsCoherent` (`Theory/Typing/Env.lean`), and
`VEnv.WF.eliminatorsCoherent` (`EliminatorCoherenceOfWF.lean`) derives
`VEnv.EliminatorsCoherent` from `VEnv.WF` (section 2.4 of the design notes). The
verified pipeline never registers a schema for foreign projection metadata:
`RegistrationCertificate.register_after_constructors` proves the premise from freshness. -/

namespace Lean4Lean.InductiveSignature.CaseSchema
open VExpr
open private reduction_head_app reduction_head_mkApps restoration_vars view_constructor_external
  from Lean4Lean.Theory.Inductive.CaseReductionLemmas

end Lean4Lean.InductiveSignature.CaseSchema

namespace Lean4Lean.VEnv
open InductiveSignature CaseSchema VExpr
set_option linter.unusedSectionVars false

variable {env : VEnv}

/-- Every registered case eliminator is certified by a source declaration
whose constants are present and which owns the projection metadata of its
source families. It follows from well-formedness (`VEnv.WF.eliminatorsCoherent`). Nested
containers need no premise: they are certified installations, whose projection metadata is
coherent in every well-formed environment. -/
def EliminatorsCoherent (env : VEnv) : Prop :=
  ∀ key schema, env.eliminators key schema → ∃ base source block,
    base ≤ env ∧ schema.Certified base source block ∧
    (∀ value ∈ block.types ++ block.ctors, env.constants value.name = some value.toVConstant) ∧
    ∀ type ∈ source.types, ∀ info, env.projections type.name info →
      (⟨type.name, info⟩ : VProjectionEntry) ∈ source.projectionEntries

end Lean4Lean.VEnv
