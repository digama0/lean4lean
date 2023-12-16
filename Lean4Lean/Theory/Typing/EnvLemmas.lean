import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.QuotLemmas
import Lean4Lean.Theory.Typing.InductiveLemmas

namespace Lean4Lean

theorem VEnv.WF.ordered (H : WF ds env) : Ordered env := by
  induction H with
  | empty => exact .empty
  | decl h _ ih =>
    cases h with
    | block h => exact .const ih (by rintro _ ⟨⟩) h
    | «axiom» h1 h2 => exact .const ih (by rintro _ ⟨⟩; exact h1) h2
    | @«def» env env' ci h1 h2 =>
      refine .defeq (.const ih (by rintro _ ⟨⟩; exact h1.isType ih ⟨⟩) h2) ⟨?_, ?_⟩
      · simp [VDefVal.toDefEq]
        rw [← (h1.levelWF ⟨⟩).2.2.instL_id]
        exact .const (addConst_self h2) VLevel.id_WF (by simp)
      · exact h1.mono (addConst_le h2)
    | «opaque» h1 h2 => exact .const ih (by rintro _ ⟨⟩; exact h1.isType ih ⟨⟩) h2
    | «example» _ => exact ih
    | quot h1 h2 => exact addQuot_WF ih h1 h2
    | induct h1 h2 => exact addInduct_WF ih h1 h2
