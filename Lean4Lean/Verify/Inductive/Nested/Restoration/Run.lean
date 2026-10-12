import Lean4Lean.Verify.Inductive.Nested.Restoration.LoweredRun
import Lean4Lean.Verify.Inductive.Nested.Restoration.Steps
import Lean4Lean.Verify.Inductive.Nested.Restoration.Nonprimitive
import Lean4Lean.Verify.Inductive.Nested.Lowering.OccurrenceTyping
import Lean4Lean.Verify.Inductive.Nested.Restoration.SideEnvironment.Environment

/-! # The data of a validated nested run (`NestedRun`)

The run object the restoration certificates are indexed by. It is indexed by the lowered run
`L : LoweredRun` (the ordinary pipeline's run on the lowered block), which the restoration
lemmas read as `E.lowered`.

Also here: `NestedSourceDeclaration` and the derived views of a run. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The source declaration with its header and constructor environments,
obtained from the lowering, restoration, and validation runs. -/
structure NestedSourceDeclaration
    (sourceVEnv : VEnv) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (loweredDecl : VInductDecl) (safety : DefinitionSafety)
    (validationEnv auxiliaryHeaderEnv : Environment) where
  sourceDecl : VInductDecl
  envTypes : VEnv
  envCtors : VEnv
  sourceHeaders : List.Forall₂
    (fun source target => TrSourceConst sourceVEnv lparams source.name
      source.type target.toVConstVal)
    sourceTypes (loweredDecl.types.take sourceTypes.length)
  sourceAdded : sourceVEnv.addConstVals
    ((loweredDecl.types.take sourceTypes.length).map
      VInductiveType.toVConstVal) = some envTypes
  sourceTypeValues : sourceDecl.typeConstants =
    (loweredDecl.types.take sourceTypes.length).map
      VInductiveType.toVConstVal
  core : TrInductDeclCore sourceVEnv lparams nparams sourceTypes isUnsafe
    sourceDecl envTypes envCtors
  checked : SourcePrefixOfLowered sourceDecl loweredDecl
  headerValidationValid : CheckingEnv.Valid safety auxiliaryHeaderEnv envTypes
  validationValid : CheckingEnv.ValidCore safety validationEnv envCtors

/-- All proof-relevant data produced by a successful nested execution before
the restored block certificate is assembled. -/
structure NestedRun
    (res : Lean4Lean.ElimNestedInductive.Result)
    (sourceProdEnv : Environment) (sourceTypes : List InductiveType)
    (sourceEnv : VEnv) (decl : VInductDecl) (lparams : List Name)
    (nparams : Nat) (isUnsafe : Bool) (safety : DefinitionSafety)
    (outEnv : Environment) {c₀ : AddInductive.Context} {Hc : ContextWF c₀}
    {loweredEnv : Environment} (L : LoweredRun Hc nparams res.types.toArray loweredEnv) where
  context_env : L.c.env = sourceProdEnv
  context_lparams : L.c.lparams = lparams
  context_safety : L.c.safety = safety
  lowered_isUnsafe_source : L.isUnsafe = isUnsafe
  lowered_initialEnv : L.Hc'.venv = sourceEnv
  validationFuel : FuelConfig
  lowering : NestedLoweringOutputClosed sourceProdEnv
    validationFuel.inductiveFuel nparams sourceTypes
    { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res
  restoration : NestedRestorationFolds res loweredEnv sourceProdEnv
    (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
    (sourceTypes.map (·.name)) sourceTypes
    (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 ((), outEnv)
  primitiveSafe : ∃ entries,
    FreshNonprimitiveExtension false sourceProdEnv entries outEnv
  validationEnv : Environment
  validationEnvironment :
    ValidationEnvironment res loweredEnv sourceProdEnv
      (sourceTypes.map (·.name)) false sourceTypes validationEnv
  recursorTypeValidation :
    Lean4Lean.validateRestoredRecursorTypes.run validationEnv loweredEnv safety validationFuel res
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) sourceTypes
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 = .ok ()
  recursorRuleValidation :
    Lean4Lean.validateRestoredRecursorRules.run
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1))
      loweredEnv safety validationFuel res
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) sourceTypes
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 = .ok ()
  auxiliaryHeaderEnv : Environment
  headerValidationEnvironment :
    ValidationHeaderEnvironment loweredEnv sourceProdEnv
      (sourceTypes.map (·.name)) sourceTypes auxiliaryHeaderEnv
  auxiliaryVEnv : VEnv
  auxiliarySelection : CDeclArray res.lctx res.params
  auxiliaryTranslations : ClosedNestedOccurrenceTypings auxiliaryVEnv
    lparams res auxiliarySelection
  sourceCore : NestedSourceDeclaration sourceEnv lparams nparams
    sourceTypes isUnsafe L.loweredDecl safety validationEnv
      auxiliaryHeaderEnv
  sourceCoreDecl_eq : sourceCore.sourceDecl = decl
  auxiliaryVEnv_eq_sourceCore : auxiliaryVEnv = sourceCore.envTypes
  /-- The lowered family and constructor names are not primitives (the lowered run
  checks them with `allowPrimitive = false`). -/
  loweredNonprimitive : ∀ n ∈ InductiveSignature.familyNames L.loweredDecl.types,
    ¬ Kernel.Environment.primitives.contains n

/-! ### Derived views -/

/-- The lowered run of a nested run. -/
abbrev NestedRun.lowered {c₀ : AddInductive.Context} {Hc : ContextWF c₀}
    {loweredEnv : Environment} {L : LoweredRun Hc nparams res.types.toArray loweredEnv}
    (_ : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv L) : LoweredRun Hc nparams res.types.toArray loweredEnv :=
  L

/-- The environment the lowered run returns. -/
abbrev NestedRun.loweredEnv {c₀ : AddInductive.Context} {Hc : ContextWF c₀}
    {loweredEnv : Environment} {L : LoweredRun Hc nparams res.types.toArray loweredEnv}
    (_ : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv L) : Environment :=
  loweredEnv

/-- The checker context of the lowered run after its header phase. -/
abbrev NestedRun.context
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams res.types.toArray loweredEnv₀}
    (E : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv L) : AddInductive.Context :=
  E.lowered.c

/-- The context certificate of the lowered run after its header phase. -/
abbrev NestedRun.contextWF
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams res.types.toArray loweredEnv₀}
    (E : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv L) : ContextWF E.context :=
  E.lowered.Hc'

theorem NestedRun.lowered_c
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams res.types.toArray loweredEnv₀}
    (E : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv L) : E.lowered.c = E.context := rfl

theorem NestedRun.context_venv
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams res.types.toArray loweredEnv₀}
    (E : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv L) : E.contextWF.venv = sourceEnv :=
  E.lowered_initialEnv

theorem NestedRun.lowered_env
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams res.types.toArray loweredEnv₀}
    (E : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv L) : E.lowered.c.env = sourceProdEnv :=
  E.context_env

theorem NestedRun.lowered_lparams
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams res.types.toArray loweredEnv₀}
    (E : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv L) : E.lowered.c.lparams = lparams :=
  E.context_lparams

theorem NestedRun.lowered_safety
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams res.types.toArray loweredEnv₀}
    (E : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv L) : E.lowered.c.safety = safety :=
  E.context_safety

/-- The context certificate already recorded by the nested run, at its lowered context. -/
def NestedRun.loweredContextWF
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams res.types.toArray loweredEnv₀}
    (E : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv L) : ContextWF E.lowered.c :=
  E.contextWF

/-- The ordinary initial state used by the recorded nested lowering. -/
def NestedRun.initialState
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams res.types.toArray loweredEnv₀}
    (E : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv L) : Lean4Lean.ElimNestedInductive.State :=
  { lvls := E.lowered.c.lparams.map .param, newTypes := #[] }

/-- The recorded lowering in the lowered run's context and parameter indices. -/
theorem NestedRun.loweringAtContext
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams res.types.toArray loweredEnv₀}
    (E : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv L) :
    NestedLoweringOutputClosed E.lowered.c.env E.validationFuel.inductiveFuel
      nparams sourceTypes
      { E.initialState with newTypes := sourceTypes.toArray } res := by
  simpa only [NestedRun.initialState, E.lowered_env, E.lowered_lparams] using E.lowering

end VerifyInductive
end Lean4Lean
