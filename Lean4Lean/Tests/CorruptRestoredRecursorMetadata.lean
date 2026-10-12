import Lean4Lean.Verify.Inductive.Nested.Restoration.TrRestoredRecursorVal

namespace Lean4Lean.Tests.CorruptRestoredRecursorMetadata

/-- An existential choice of signature, lowering, or restoration cannot
justify a corrupted parameter count in a concrete restored recursor. -/
theorem rejectsCorruptedParameterCount {env venv : VEnv} {source : VInductDecl}
    {block : VInductBlock} (rec : Lean.RecursorVal) (value : VConstVal) :
    ¬ InductiveSignature.TrRestoredCompilation env source block venv
      [(.recInfo { rec with numParams := source.nparams + 1 }, value)] := by
  intro H
  have h := H.parameterCount (rec := { rec with numParams := source.nparams + 1 })
    (value := value) (by simp)
  simp only at h
  omega

/-- Auxiliary major families may come from prior containers, but the stored
`all` list must still be exactly the source family list. -/
theorem rejectsExtraFamilyMetadata {env venv : VEnv} {source : VInductDecl}
    {block : VInductBlock} (rec : Lean.RecursorVal) (value : VConstVal) (extra : Name) :
    ¬ InductiveSignature.TrRestoredCompilation env source block venv
      [(.recInfo { rec with all := source.types.map (·.name) ++ [extra] }, value)] := by
  intro H
  have h := H.all (rec := { rec with all := source.types.map (·.name) ++ [extra] })
    (value := value) (by simp)
  have hlength := congrArg List.length h
  simp only [List.length_append, List.length_singleton] at hlength
  omega

#print axioms rejectsCorruptedParameterCount
#print axioms rejectsExtraFamilyMetadata

end Lean4Lean.Tests.CorruptRestoredRecursorMetadata
