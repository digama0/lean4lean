import Lean4Lean.Theory.Typing.Confluence.RecursorRegistration
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.Inductive.Restoration
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.Inductive.CaseReductionData

/-! One concrete registry shared by legacy and ordinary-data head dispatch.
Only syntax and closure evidence occur in this low-level module. -/
namespace Lean4Lean.HeadRegistry
open InductiveSignature
structure CaseEntry where
  schema : CaseSchema
  owner : Fin schema.signature.families.size

structure Registry where
  definitions : Name → Option VDefVal
  recursors : Name → Option RecursorData
  cases : Name → Nat → Option HeadRegistry.CaseEntry := fun _ _ => none
  projections : Name → Option VProjectionInfo := fun _ => none
  structureConstructors : Name → Option VProjectionEntry := fun _ => none
  quotient : Bool := false

/-- Each closure field is produced from the corresponding registered original
header/equation. It does not certify a reduction's semantic guards. -/
structure Registry.Scoped (registry : Registry) : Prop where
  definition : ∀ name value, registry.definitions name = some value → value.value.Closed
  singletonEquation : ∀ name data, registry.recursors name = some data →
    ∀ equation, data.singletonEquation = some equation → equation.rhs.Closed
  recursorEquation : ∀ name data, registry.recursors name = some data →
    ∀ index equation,
      data.schema.restoration.equation (data.recursorInstance.equation index) = some equation →
      equation.rhs.Closed
  caseEquation : ∀ block owner entry, registry.cases block owner = some entry →
    ∀ rule, entry.schema.Generates block entry.owner rule → rule.equation.rhs.Closed

/-- A declaration head whose name cannot also select a computational rule.
Unlike one stopped argument spine, these concrete registry facts survive
substitution of proof inhabitants into its arguments. -/
structure HeadInert (registry : Registry) (name : Name) : Prop where
  definition : registry.definitions name = none
  recursor : registry.recursors name = none
  quotient : registry.quotient = false ∨ name ≠ ``Quot.lift
end Lean4Lean.HeadRegistry
