import Lean4Lean.Verify.Environment.Basic
import Lean4Lean.Verify.Inductive.Recursor.Entries.TrRecursorVal

/-! A recursor entry with a corrupted parameter count is still accepted by the constant
translation `TrConstVal`, but it is not the translation of a generated recursor
(`InductiveSignature.TrRecursorEntry`) for any instance of any signature modelling the source
declaration: the parameter count is fixed by the declaration (`InductiveSignature.Models`), so
choosing a different signature witness cannot repair it. -/

namespace Lean4Lean.Tests.CorruptRecursorMetadata
open Lean hiding Environment

theorem corrupted_parameter_count_rejected
    (safety : DefinitionSafety) (source target : VEnv)
    (decl : VInductDecl) (s : InductiveSignature) (hm : s.Models source decl)
    (g : InductiveSignature.Instance s) (owner : Fin s.families.size)
    (rec : RecursorVal) (value : VConstVal)
    (h : TrConstVal safety target (.recInfo rec) value) :
    let corrupted := { rec with numParams := decl.nparams + 1 }
    TrConstVal safety target (.recInfo corrupted) value ∧
      ¬ InductiveSignature.TrRecursorEntry g target owner (.recInfo corrupted, value) := by
  refine ⟨h, ?_⟩
  rintro ⟨concrete, he, -, hrec⟩
  cases he
  have hcount := hrec.numParams.trans hm.nparams
  change decl.nparams + 1 = decl.nparams at hcount
  omega

end Lean4Lean.Tests.CorruptRecursorMetadata
