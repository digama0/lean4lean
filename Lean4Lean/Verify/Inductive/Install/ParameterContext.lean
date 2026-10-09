import Lean4Lean.Verify.Inductive.Install.Environments
import Lean4Lean.Verify.Inductive.Constructor.Check
import Lean4Lean.Verify.Inductive.Recursor.Context.ParameterContext

/-! The common parameter context shared by the header and constructor phases.
The telescope remains in context order, with the innermost binder first. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The common parameter context recorded by the header phase of a block
(in context order).  Every generated auxiliary's parameter telescope
is definitionally this context. -/
def HeaderEnvironment.commonParameterContext
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams : Nat} {isUnsafe : Bool} {depth : Nat}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {outEnv : Environment}
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv) : List VExpr :=
  (H.sourceStatsWF.parameterSuffix.toRecursorContext
    (elimLevel := .zero) (by trivial)).parameterDecls.toCtx

theorem HeaderEnvironment.commonParameterContext_eq
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams : Nat} {isUnsafe : Bool} {depth : Nat}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {outEnv : Environment}
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv) :
    H.commonParameterContext = H.statsWF.parameterScope.toCtx := by
  rw [H.parameterScopeEq]
  rfl

/-- The parameter scope of an ordinary constructor check is the header
phase's common parameter context. -/
theorem OrdinaryConstructorCheck.parameterScope_toCtx
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams : Nat} {isUnsafe : Bool} {depth : Nat}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv : Environment}
    {H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv} (R : OrdinaryConstructorCheck H ctorEnv) :
    R.toConstructorCheck.parameterScope.toCtx = H.commonParameterContext :=
  H.commonParameterContext_eq.symm

end VerifyInductive
end Lean4Lean
