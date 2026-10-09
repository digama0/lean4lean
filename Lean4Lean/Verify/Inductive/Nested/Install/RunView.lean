import Lean4Lean.Verify.Inductive.Nested.Install.Certificate
import Lean4Lean.Verify.Inductive.Nested.Lowering.Phases

/-! Derived views of a nested run's ordinary checking phases.
The original `NestedRun` retains its representation. These views transport its
certificates to the result's family array and expose the recorded context
equalities once for the restoration consumers. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The lowered phases indexed by the nested lowering's result families. -/
def NestedRun.phases
    (E : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv) : E.lowered.Phases res.types.toArray :=
  E.lowered.phasesAt E.lowered_indTypes

theorem NestedRun.phases_commonParameterContext
    (E : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv) :
    E.phases.headers.commonParameterContext =
      E.lowered.headers.commonParameterContext :=
  E.lowered.phasesAt_commonParameterContext E.lowered_indTypes

/-- The context certificate already recorded by the nested run, at its lowered context. -/
def NestedRun.loweredContextWF
    (E : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv) : ContextWF E.lowered.c := by
  rw [E.lowered_c]
  exact E.contextWF

theorem NestedRun.lowered_env
    (E : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv) : E.lowered.c.env = sourceProdEnv :=
  (congrArg AddInductive.Context.env E.lowered_c).trans E.context_env

theorem NestedRun.lowered_lparams
    (E : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv) : E.lowered.c.lparams = lparams :=
  (congrArg AddInductive.Context.lparams E.lowered_c).trans E.context_lparams

theorem NestedRun.lowered_safety
    (E : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv) : E.lowered.c.safety = safety :=
  (congrArg AddInductive.Context.safety E.lowered_c).trans E.context_safety

/-- The ordinary initial state used by the recorded nested lowering. -/
def NestedRun.initialState
    (E : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv) : Lean4Lean.ElimNestedInductive.State :=
  { lvls := E.lowered.c.lparams.map .param, newTypes := #[] }

/-- The recorded lowering in the lowered run's context and parameter indices. -/
theorem NestedRun.loweringAtContext
    (E : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv) :
    NestedLoweringOutputClosed E.lowered.c.env E.validationFuel.inductiveFuel
      E.lowered.nparams sourceTypes
      { E.initialState with newTypes := sourceTypes.toArray } res := by
  simpa only [NestedRun.initialState, E.lowered_env, E.lowered_lparams,
    E.lowered_nparams] using E.lowering

end VerifyInductive
end Lean4Lean
