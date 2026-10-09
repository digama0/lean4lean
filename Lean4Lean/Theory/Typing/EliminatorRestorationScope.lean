import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.Inductive.CaseReductionData
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.Typing.RecursorRuleRegistration
import Lean4Lean.Theory.Typing.PatternCaptures
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.Typing.DefinitionRegistryInstallation
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Typing.RecursorRegistryInstallation
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.EtaOpening
import Lean4Lean.Theory.Inductive.CaseReductionLemmas
import Lean4Lean.Theory.Inductive.RestorationNaturality
import Lean4Lean.Theory.Inductive.CaseProjections
import Lean4Lean.Theory.Inductive.CaseRegistration

/-! The restoration table of every registered case schema is scoped
(`WF.eliminator_restoration_scoped`): it is the table checked by the certified compilation
of the declaration that registered it. The scope of the generated equations is derived from
the declaration history, not assumed. -/

namespace Lean4Lean.VEnv
open InductiveSignature

/-- The restoration table is the one checked by the certified source compilation. -/
theorem WF.eliminator_restoration_scoped {env : VEnv} {schema : CaseSchema}
    (formed : env.WF)
    (lookup : env.eliminators block schema) : schema.restoration.Scoped := by
  obtain ⟨base, source, generated, _, _, certified, _, _⟩ :=
    formed.eliminator_installed lookup
  obtain ⟨expanded, auxiliaries, compilation, _, restoration, _, _⟩ := certified
  rw [restoration]
  exact compilation.restorationScoped

end Lean4Lean.VEnv

namespace Lean4Lean.CanonicalDataHead
open InductiveSignature VEnv

end Lean4Lean.CanonicalDataHead
