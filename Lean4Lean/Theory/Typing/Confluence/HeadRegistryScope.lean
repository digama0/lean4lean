import Lean4Lean.Theory.Typing.Confluence.DefinitionHistory
import Lean4Lean.Theory.Typing.Confluence.RecursorRegistration
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.Inductive.SignatureData
import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.Typing.RecursorRegistration
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.Inductive.Restoration
import Lean4Lean.Theory.Typing.Env

/-! The scope requirements of the head registry follow from actual
registration in a well-formed environment. Ordinary definitions are extracted
from its declaration history. The recursor table supplies registration evidence
for its entries; no body-closure or semantic guard assumption is required.
-/

namespace Lean4Lean.VEnv
open InductiveSignature

/-- A selected singleton equation is one of the actually registered recursor
equations, so environment formation supplies the scope of its right side. -/
theorem RecursorRegistered.singletonEquation_rhs_closed
    {env : VEnv} {data : RecursorData} {equation : VDefEq}
    (henv : env.WF) (H : RecursorRegistered env data)
    (hequation : data.singletonEquation = some equation) : equation.rhs.Closed := by
  unfold RecursorData.singletonEquation at hequation
  dsimp only at hequation
  split at hequation <;> try contradiction
  exact (H.equation_closed henv hequation).2.1

end Lean4Lean.VEnv

namespace Lean4Lean.HeadRegistry
open InductiveSignature VEnv

end Lean4Lean.HeadRegistry
