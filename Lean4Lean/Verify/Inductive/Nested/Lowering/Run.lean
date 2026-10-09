import Lean4Lean.Theory.Inductive
import Lean4Lean.Verify.Inductive.Nested.Restoration.ExprReplace
import Lean4Lean.Verify.Inductive.Nested.Restoration.Steps
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.Inductive.Install.BlockCertificate
import Lean4Lean.Verify.Inductive.Recursor.Binders.FieldOpening
import Lean4Lean.Verify.Inductive.Header.Telescope
import Lean4Lean.Verify.Inductive.Rules.RuleSyntax

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # The lowered run

`LoweredRun` is the ordinary pipeline run on the lowered declaration of a nested inductive
declaration (section 3.3 of the design notes). -/

/-- The lowered run: the header environment, constructor check and recursor check of the
ordinary pipeline on the lowered declaration, ending in `outEnv`.  Unlike
`OrdinaryInstallation`, this keeps the intermediate data as fields rather than under
existentials, so later certificates can be indexed by the run. -/
structure LoweredRun (outEnv : Environment) where
  c : AddInductive.Context
  stats : AddInductive.InductiveStats
  loweredDecl : VInductDecl
  nparams : Nat
  depth : Nat
  isUnsafe : Bool
  initialEnv : VEnv
  indTypes : Array InductiveType
  headerEnv : Environment
  ctorEnv : Environment
  headers : HeaderEnvironment c stats loweredDecl nparams isUnsafe depth
    initialEnv indTypes headerEnv
  constructors : OrdinaryConstructorCheck headers ctorEnv
  recursors : RecursorCheck constructors.toConstructorCheck outEnv

end VerifyInductive
end Lean4Lean
