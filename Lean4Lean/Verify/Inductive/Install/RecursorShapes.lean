import Lean4Lean.Verify.Inductive.Install.RecursorShapesOf
import Lean4Lean.Verify.Inductive.Rules.RuleTranslations

/-! # The recursor shapes of a recursor check (`recursorShapesOf` on its fields) -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The recursor shapes of the recursors installed by a recursor check. -/
theorem RecursorCheck.recursorShapes
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv outEnv : Environment}
    {R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) (T : RuleTranslations H)
    (hnp : ∀ {n cval}, outEnv.constants.find? n = some (.ctorInfo cval) →
      (∃ src ∈ decl.constructorConstants, src.name = n) → cval.numParams = decl.nparams) :
    ∀ rval ∈ H.rvals, RecursorShapesAt outEnv.constants H.outVEnv rval :=
  recursorShapesOf H.generation H.models H.admissible.levels_length R.core.typesAdded
    R.core.ctorsAdded (TrInductDeclCore.sourceNames_nodup R.core) R.formation.rawShapes
    (VEnv.addProjections_le.trans (VEnv.addRecs_le H.recsAdded))
    (fun r hr => VEnv.addRecs_find H.recsAdded r hr) H.recursors_eq H.trRecs H.metadata
    T.trRules H.rules_ctor hnp

end VerifyInductive
end Lean4Lean
