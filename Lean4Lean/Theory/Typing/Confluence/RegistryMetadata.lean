import Lean4Lean.Theory.Typing.Confluence.RecursorDeclarationProvenance
import Lean4Lean.Theory.Typing.Confluence.CaseRhsTyping
import Lean4Lean.Theory.Typing.Confluence.RecursorRegistration
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.Typing.DefinitionPatterns
import Lean4Lean.Theory.Typing.Confluence.HeadRegistryData
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.Typing.Confluence.DefinitionHistory
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Typing.RecursorRuleRegistration
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Inductive.CaseReductionData
import Lean4Lean.Theory.Inductive.Restoration
import Lean4Lean.Theory.Typing.Confluence.HeadRegistryScope
import Lean4Lean.Theory.Typing.EliminatorRestorationScope
import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.Inductive.CaseRegistration
import Lean4Lean.Theory.Typing.ProjectionConstructorFamily

namespace Lean4Lean.VEnv
open InductiveSignature
/-- Only ordered equation registration is needed for right-side scope. -/
theorem RecursorRegistered.equation_rhs_closed (ordered : env.Ordered)
    (registered : RecursorRegistered env data)
    (generated : data.equation index = some equation) : equation.rhs.Closed :=
  VExpr.WF.closedN ordered
    ⟨_, (ordered.defEqWF (registered.equation_present generated)).2⟩ trivial
end Lean4Lean.VEnv
namespace Lean4Lean.HeadRegistry
open InductiveSignature VEnv
/-- The scope required by every possible selection follows from the actual
recursor registration and finite original case headers. -/
theorem Registry.scoped_of_headers {env : VEnv} {registry : Registry}
    (formed : env.WF)
    (definitions : ∀ name value, registry.definitions name = some value → value.value.Closed)
    (recursors : ∀ name data, registry.recursors name = some data →
      RecursorRegistered env data)
    (cases : ∀ block owner entry, registry.cases block owner = some entry →
      env.eliminators block entry.schema ∧
      ∃ header, entry.schema.genericType entry.owner = some header ∧ header.Closed) :
    registry.Scoped := by
  refine ⟨definitions, ?_, ?_, ?_⟩
  · intro name data lookup equation generated
    exact (recursors name data lookup).singletonEquation_rhs_closed formed generated
  · intro name data lookup index equation generated
    exact (recursors name data lookup).equation_rhs_closed formed.ordered generated
  · intro block owner entry lookup rule generated
    obtain ⟨registered, header, selectedHeader, closed⟩ := cases _ _ _ lookup
    exact generated.rhs_closed selectedHeader
      (formed.eliminator_restoration_scoped registered) closed
/-- All tables used by the machine are concrete syntax. Definition bodies
come from the declaration list; the other tables retain their actual lookups. -/
def Registry.ofDataHistory (declarations : List VDecl)
    (recursors : Name → Option RecursorData)
    (cases : Name → Nat → Option CaseEntry)
    (projections : Name → Option VProjectionInfo)
    (structureConstructors : Name → Option VProjectionEntry) (quotient : Bool) : Registry :=
  { definitions := definitionRegistry declarations
    recursors := recursors
    cases := cases
    projections := projections
    structureConstructors := structureConstructors
    quotient := quotient }
/-- The complete machine's scope is produced from the original history and
case headers, including every constructor equation. -/
theorem Registry.ofDataHistory_scoped
    {env : VEnv} {declarations : List VDecl} {recursors : Name → Option RecursorData}
    {cases : Name → Nat → Option CaseEntry} {projections : Name → Option VProjectionInfo}
    {structureConstructors : Name → Option VProjectionEntry} {quotient : Bool}
    (history : RecursorRegistryHistory env declarations recursors)
    (caseHeaders : ∀ block owner entry, cases block owner = some entry →
      env.eliminators block entry.schema ∧
      ∃ header, entry.schema.genericType entry.owner = some header ∧ header.Closed) :
    (Registry.ofDataHistory declarations recursors cases projections structureConstructors quotient).Scoped := by
  have formed : env.WF := ⟨declarations, history.history⟩
  apply Registry.scoped_of_headers formed
  · intro name value lookup
    exact (history.history.definitionRegistry_registered lookup).1.closed formed
  · intro name data lookup
    exact (history.registered lookup).1
  · exact caseHeaders
end Lean4Lean.HeadRegistry

namespace Lean4Lean.VEnv
open VExpr
variable {env : VEnv} {leftName rightName : Name} {leftInfo rightInfo : VProjectionInfo}
set_option Elab.async false
end Lean4Lean.VEnv
namespace Lean4Lean.HeadRegistry
open VEnv InductiveSignature
variable {env : VEnv}
set_option Elab.async false
noncomputable def environmentProjections (env : VEnv) (name : Name) : Option VProjectionInfo := by
  classical
  exact if present : ∃ info, env.projections name info then some (Classical.choose present) else none
noncomputable def environmentStructures (env : VEnv) (name : Name) : Option VProjectionEntry := by
  classical
  exact if present : ∃ entry : VProjectionEntry,
      env.projections entry.typeName entry.info ∧ entry.info.ctorName = name then
    some (Classical.choose present) else none
noncomputable def environmentCases (env : VEnv) (block : Name) (owner : Nat) : Option CaseEntry := by
  classical
  exact if present : ∃ entry : CaseEntry, env.eliminators block entry.schema ∧ entry.owner.val = owner ∧
      ∃ header, entry.schema.genericType entry.owner = some header ∧ header.Closed then
    some (Classical.choose present) else none
theorem environmentProjections_sound
    (lookup : environmentProjections env name = some info) : env.projections name info := by
  classical
  unfold environmentProjections at lookup
  split at lookup
  · rename_i present
    cases lookup; exact Classical.choose_spec present
  · cases lookup
theorem environmentProjections_complete (ordered : env.Ordered)
    (present : env.projections name info) : environmentProjections env name = some info := by
  classical
  unfold environmentProjections
  rw [dif_pos ⟨info, present⟩]
  exact congrArg some (ordered.projections_unique (Classical.choose_spec _) present)
theorem environmentStructures_sound
    (lookup : environmentStructures env name = some entry) :
    env.projections entry.typeName entry.info ∧ entry.info.ctorName = name := by
  classical
  unfold environmentStructures at lookup
  split at lookup
  · rename_i present
    cases lookup; exact Classical.choose_spec present
  · cases lookup
theorem environmentStructures_complete (ordered : env.Ordered)
    (present : env.projections name info) :
    environmentStructures env info.ctorName = some ⟨name, info⟩ := by
  classical
  unfold environmentStructures
  rw [dif_pos ⟨⟨name, info⟩, present, rfl⟩]
  apply congrArg some
  have selected := Classical.choose_spec (show ∃ entry : VProjectionEntry,
    env.projections entry.typeName entry.info ∧ entry.info.ctorName = info.ctorName from
      ⟨⟨name, info⟩, present, rfl⟩)
  obtain ⟨nameEq, infoEq⟩ := ordered.projectionConstructor_family selected.1 present selected.2
  generalize choiceEq : Classical.choose _ = chosen at nameEq infoEq ⊢
  cases chosen with
  | mk chosenName chosenInfo =>
    cases nameEq
    cases infoEq
    rfl
theorem environmentCases_sound
    (lookup : environmentCases env block owner = some entry) :
    env.eliminators block entry.schema ∧ entry.owner.val = owner ∧
      ∃ header, entry.schema.genericType entry.owner = some header ∧ header.Closed := by
  classical
  unfold environmentCases at lookup
  split at lookup
  · rename_i present
    cases lookup; exact Classical.choose_spec present
  · cases lookup
theorem environmentCases_complete (formed : env.WF)
    {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    (present : env.eliminators block schema)
    (header : schema.genericType owner = some type) (closed : type.Closed) :
    environmentCases env block owner.val = some ⟨schema, owner⟩ := by
  classical
  unfold environmentCases
  have entryExists : ∃ entry : CaseEntry, env.eliminators block entry.schema ∧
      entry.owner.val = owner.val ∧ ∃ header,
      entry.schema.genericType entry.owner = some header ∧ header.Closed :=
    ⟨⟨schema, owner⟩, present, rfl, type, header, closed⟩
  rw [dif_pos entryExists]
  apply congrArg some
  generalize selectedEq : Classical.choose entryExists = selected
  have selectedData : env.eliminators block selected.schema ∧ selected.owner.val = owner.val ∧
      ∃ header, selected.schema.genericType selected.owner = some header ∧ header.Closed := by
    rw [← selectedEq]
    exact Classical.choose_spec entryExists
  cases selected with
  | mk selectedSchema selectedOwner =>
    obtain ⟨registered, indexEq, _⟩ := selectedData
    cases formed.eliminators_unique registered present
    cases Fin.ext indexEq
    rfl
end Lean4Lean.HeadRegistry
