import Lean4Lean.Verify.Environment.Basic
import Lean4Lean.Verify.Inductive.Recursor.Entries.TrRecursorVal

/-! A recursor entry with a corrupted parameter count is still accepted by the constant
translation `TrConstVal`, but it is not the translation of a compiled block
(`InductiveSignature.TrCompilation`), whatever the signature. -/

namespace Lean4Lean.Tests.CorruptRecursorMetadata
open Lean hiding Environment

theorem corrupted_parameter_count_rejected
    (safety : DefinitionSafety) (source target : VEnv)
    (decl : VInductDecl) (block : VInductBlock)
    (rec : RecursorVal) (value : VConstVal)
    (h : TrConstVal safety target (.recInfo rec) value) :
    let corrupted := { rec with numParams := decl.nparams + 1 }
    TrConstVal safety target (.recInfo corrupted) value ∧
      ¬ InductiveSignature.TrCompilation source decl block target
        [(.recInfo corrupted, value)] := by
  refine ⟨h, ?_⟩
  intro realized
  have hcount := realized.parameterCount (List.mem_singleton_self _)
  change decl.nparams + 1 = decl.nparams at hcount
  omega

end Lean4Lean.Tests.CorruptRecursorMetadata
