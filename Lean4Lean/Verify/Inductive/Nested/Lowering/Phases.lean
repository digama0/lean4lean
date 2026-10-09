import Lean4Lean.Verify.Inductive.Nested.Lowering.Run
import Lean4Lean.Verify.Inductive.Install.ParameterContext

/-! The dependent header, constructor and recursor certificates of a lowered run.
Reindexing changes their source-family array together, so the later phases
retain precisely the header and constructor certificates they checked. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The three ordinary phases at a chosen source-family array. -/
structure LoweredRun.Phases (P : LoweredRun outEnv)
    (indTypes : Array InductiveType) where
  headers : HeaderEnvironment P.c P.stats P.loweredDecl P.nparams P.isUnsafe
    P.depth P.initialEnv indTypes P.headerEnv
  constructors : OrdinaryConstructorCheck headers P.ctorEnv
  recursors : RecursorCheck constructors.toConstructorCheck outEnv

/-- The certificates already stored by the run, with their dependencies named. -/
def LoweredRun.phases (P : LoweredRun outEnv) : P.Phases P.indTypes :=
  ⟨P.headers, P.constructors, P.recursors⟩

/-- Transport all three phases across an equality of source-family arrays. -/
def LoweredRun.phasesAt (P : LoweredRun outEnv)
    {indTypes : Array InductiveType}
    (h : P.indTypes = indTypes) : P.Phases indTypes :=
  Eq.mp (congrArg P.Phases h) P.phases

/-- Reindexing retains the header's common parameter telescope. -/
theorem LoweredRun.phasesAt_commonParameterContext (P : LoweredRun outEnv)
    {indTypes : Array InductiveType}
    (h : P.indTypes = indTypes) :
    (P.phasesAt h).headers.commonParameterContext =
      P.headers.commonParameterContext := by
  cases h
  rfl

/-- The same run with its family array and dependent phases reindexed together. -/
def LoweredRun.reindex (P : LoweredRun outEnv)
    {indTypes : Array InductiveType}
    (h : P.indTypes = indTypes) : LoweredRun outEnv :=
  { P with
    indTypes := indTypes
    headers := (P.phasesAt h).headers
    constructors := (P.phasesAt h).constructors
    recursors := (P.phasesAt h).recursors }

/-- Array reindexing rebuilds the original run, including its dependent certificates. -/
theorem LoweredRun.reindex_eq (P : LoweredRun outEnv)
    {indTypes : Array InductiveType} (h : P.indTypes = indTypes) :
    P.reindex h = P := by
  cases h
  rfl

end VerifyInductive
end Lean4Lean
