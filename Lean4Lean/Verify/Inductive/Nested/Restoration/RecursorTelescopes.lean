import Lean4Lean.Verify.Inductive.Nested.Lowering.Restore.ExprReplace
import Lean4Lean.Verify.Inductive.Recursor.Signature.RecursorTypeTelescope

/-! The binder-by-binder decomposition of a generated recursor type (`RecursorTypeTelescope`),
used to transport restored recursor types, and the restoration telescopes of generated recursor
entries. Ported from the source branch's `Nested/Restoration/ExprReplace.lean` (its typed
part; the syntactic part is `Nested/Lowering/Restore/ExprReplace.lean`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Executable iota right-hand sides always expose at least the common-parameter
lambda prefix opened by `restoreNested`. -/
theorem RecursorRuleSyntax.rhsRestoreTelescope
    (H : RecursorRuleSyntax indTypes stats motives minors lvls
      ctor minorIdx rule)
    (hparams : nparams = stats.params.size) :
    RestoreTelescope rule.rhs nparams := by
  apply H.rhsLambdaTelescope.restorePrefix
  rw [hparams]
  have hp : stats.params.size = H.params_bound.fvars.length := by
    simpa using congrArg Array.size H.params_bound.expressions
  unfold RecursorRuleSyntax.binders
  simp only [List.length_append]
  omega

/-- The executable recursor type exposes the same parameter prefix that was
bound while generating its telescope. -/
theorem GeneratedRecursorEntry.typeRestoreTelescope
    (H : GeneratedRecursorEntry safety env lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (Hparams : CDeclArray c.lctx stats.params)
    (hparams : nparams = stats.params.size) :
    RestoreTelescope H.info.type nparams := by
  rw [H.type, hparams]
  rcases (Hparams.forallTelescope _).inferImplicit 1000 false with
    ⟨residual, Htelescope⟩
  exact Htelescope.restorePrefix (Nat.le_refl _)

theorem GeneratedRecursorEntry.rulesRestoreTelescope
    (H : GeneratedRecursorEntry safety env lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (hparams : nparams = stats.params.size) :
    ∀ rule ∈ H.info.rules, RestoreTelescope rule.rhs nparams := by
  intro rule hrule
  rcases List.mem_iff_getElem.mp hrule with ⟨i, hi, rfl⟩
  have hctor : i < indTypes[ownerIdx]!.ctors.length := by
    rw [← H.rules.length]
    exact hi
  rcases H.rules.entry i hctor hi with ⟨Hrule⟩
  exact Hrule.rhsRestoreTelescope hparams

end VerifyInductive
end Lean4Lean
