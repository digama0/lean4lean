import Lean4Lean.Verify.Inductive.Nested.Restoration.Steps

/-! Source translations of the restored constructors of one source family: each step of the
executable constructor-restoration fold paired with the translation of the source constructor
it installs, stated in the abstract header environment (section 3.3 of
the design notes). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- One source constructor paired with the executable restoration step that
installs it. The source translation is stated in the abstract header environment
`canonicalEnv`, not in the kernel environment, where restored headers, constructors
and recursors are interleaved. -/
structure RestoredConstructorTranslation
    (lparams : List Name) (safety : DefinitionSafety) (canonicalEnv : VEnv)
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (source : Constructor) where
  constructor : VConstVal
  sourceTranslation : TrSourceConst canonicalEnv lparams source.name
    source.type constructor
  restoredTranslation : TrConstVal safety canonicalEnv
    (.ctorInfo Hstep.restored.newInfo) constructor

/-- Positional source-constructor semantics for the exact constructor
restoration fold of one family. -/
inductive RestoredConstructorTranslations
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment)
    (lparams : List Name) (safety : DefinitionSafety) (canonicalEnv : VEnv) :
    List Name → Environment → Environment →
      List Constructor → List VConstVal → Prop
  | nil (sourceProdEnv : Environment) :
      RestoredConstructorTranslations result loweredEnv lparams safety canonicalEnv
        [] sourceProdEnv sourceProdEnv [] []
  | cons
      (Hstep : RestoredConstructorStep result loweredEnv ctorName
        sourceProdEnv middleProdEnv)
      (Hsemantic : RestoredConstructorTranslation lparams safety
        canonicalEnv Hstep source)
      (Hrest : RestoredConstructorTranslations result loweredEnv lparams safety canonicalEnv
        names middleProdEnv targetProdEnv sources constructors) :
      RestoredConstructorTranslations result loweredEnv lparams safety canonicalEnv
        (ctorName :: names) sourceProdEnv targetProdEnv (source :: sources)
        (Hsemantic.constructor :: constructors)

theorem RestoredConstructorTranslations.forall₂
    (H : RestoredConstructorTranslations result loweredEnv lparams safety canonicalEnv names
      sourceProdEnv targetProdEnv sources constructors) :
    List.Forall₂ (fun source constructor =>
      TrSourceConst canonicalEnv lparams source.name source.type constructor)
      sources constructors := by
  induction H with
  | nil => exact .nil
  | cons Hstep Hsemantic Hrest ih =>
    exact .cons Hsemantic.sourceTranslation ih


end VerifyInductive
end Lean4Lean
