import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Verify.Inductive.Nested.Restoration.AssemblyRecursors
import Lean4Lean.Verify.Inductive.Nested.Restoration.RestoredRecursorShapes
import Lean4Lean.Verify.Inductive.Nested.Restoration.RuleFree

/-! # The stripped checker environment of a nested run

The premises of `NestedRun.strippedValid` (`RuleFree.lean`) that do not depend on the stripped
checker environment itself: no restored recursor is K-like (`NestedRun.restored_k_false`, the
nested block has more than one family), and the rule-free telescopes of the restored
recursors (`NestedRun.restoredRecursorTelescopes`). `NestedRun.strippedChecker` is the
stripped environment's checker environment with everything discharged. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- **No restored recursor of a nested run is K-like**: its lowered recursor is a recursor of a
block with more than one family. -/
theorem NestedRun.restored_k_false
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv L)
    (hnonempty : sourceTypes ≠ []) (hnested : result.aux2nested.size ≠ 0) :
    ∀ rv ∈ E.restoration.rvals, rv.k = false := by
  intro rv hrv
  obtain ⟨owner, s, t, Hs, rfl⟩ := E.rval_step hnonempty hrv
  have M := E.recursorMetadataOfStep owner Hs
  rw [Hs.restored.restoration.k]
  cases hk : Hs.oldInfo.k with
  | false => rfl
  | true =>
    have := (M.k hk).1
    have := E.one_lt_familiesSize hnested
    omega

/-- **The stripped restored environment of a nested run** is a valid checking environment and
a checker environment of the rule-free recursor stage `B.recursorVEnv`. -/
theorem NestedRun.strippedChecker {ves : VEnvs} {res : ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType} {decl : VInductDecl}
    {lparams : List Name} {nparams : Nat} {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams res.types.toArray loweredEnv₀}
    (E : NestedRun res sourceProdEnv sourceTypes (ves.venv (if isUnsafe then .unsafe else .safe))
      decl lparams nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (B : RestoredBlockBase E.restoration (ves.venv (if isUnsafe then .unsafe else .safe)) decl
      lparams nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hB : B.loweredDecl = E.lowered.loweredDecl) (wf : ves.WF sourceProdEnv)
    (Hsources : SourceSyntaxChecked sourceTypes)
    (Hparameters : decl.SourceParameterWF (ves.venv (if isUnsafe then .unsafe else .safe)))
    (hnested : res.aux2nested.size ≠ 0) :
    CheckingEnv.Valid (if isUnsafe then .unsafe else .safe) (stripRecursorRules outEnv
        (restoredRecursorNames (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) B.recursorVEnv ∧
      CheckerEnv (if isUnsafe then .unsafe else .safe) (stripRecursorRules outEnv
          (restoredRecursorNames (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
            sourceTypes (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1))
          B.recursorVEnv := by
  have hk := E.restored_k_false B.sourceNonempty hnested
  have H := E.strippedValid B hB wf Hsources Hparameters hk
    (fun r hr _ => E.restoredRecursorTelescopes wf Hsources B hB hk r hr)
  exact ⟨H.1, H.2 (wf.toVEnvAt _).toCheckerEnv⟩

end VerifyInductive
end Lean4Lean
