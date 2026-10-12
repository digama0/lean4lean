import Lean4Lean.Verify.Inductive.Nested.Restoration.Base
import Lean4Lean.Verify.Inductive.Nested.Restoration.Run

/-! # The installed nested run (`NestedInstalledRun`)

A validated nested run (`NestedRun`) together with the rule-free restored block it produced
(`RestoredBlockBase`) over the same lowered run. Nested blocks are installed through
`RestoredBlock` (`Nested/Install/Installed.lean`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A validated nested run with its rule-free restored block. -/
structure NestedInstalledRun
    (res : Lean4Lean.ElimNestedInductive.Result)
    (sourceProdEnv : Environment) (sourceTypes : List InductiveType)
    (sourceEnv : VEnv) (decl : VInductDecl) (lparams : List Name)
    (nparams : Nat) (isUnsafe : Bool) (safety : DefinitionSafety)
    (outEnv : Environment) {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} (L : LoweredRun Hc₀ nparams res.types.toArray loweredEnv₀) extends
    NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams nparams isUnsafe safety
      outEnv L where
  assembly : RestoredBlockBase restoration sourceEnv decl lparams nparams isUnsafe safety
  lowered_eq : assembly.loweredDecl = L.loweredDecl

section

variable {result : Lean4Lean.ElimNestedInductive.Result}
  {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
  {allIndNames : List Name} {sourceTypes : List InductiveType}
  {auxRecNames : List Name} {outEnv : Environment}
  {H : NestedRestorationFolds result loweredEnv sourceProdEnv
    auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
  {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
  {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}

theorem RestoredBlockBase.typesAdded
    (C : RestoredBlockBase H sourceEnv decl lparams nparams isUnsafe safety) :
    sourceEnv.addConstVals decl.typeConstants = some C.install.venvTypes := by
  rw [← C.typeValues]
  exact C.install.abstract_types

theorem RestoredBlockBase.constructorsAdded
    (C : RestoredBlockBase H sourceEnv decl lparams nparams isUnsafe safety) :
    C.install.venvTypes.addConstVals decl.constructorConstants =
      some C.install.venvCtors := by
  rw [← C.constructorValues]
  exact C.install.abstract_ctors

end

end VerifyInductive
end Lean4Lean
