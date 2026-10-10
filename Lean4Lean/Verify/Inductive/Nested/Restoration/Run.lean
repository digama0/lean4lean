import Lean4Lean.Verify.Inductive.Nested.Restoration.LoweredRun
import Lean4Lean.Verify.Inductive.Nested.Restoration.Steps
import Lean4Lean.Verify.Inductive.Nested.Restoration.Nonprimitive
import Lean4Lean.Verify.Inductive.Nested.Restoration.NestedOccurrences
import Lean4Lean.Verify.Inductive.Nested.Restoration.SideEnvironment.Environment

/-! # The data of a validated nested run (`NestedRun`)

The run object the restoration certificates are indexed by: the source branch's `NestedRun`
(`Nested/Install/Certificate.lean`) with its field names kept, so that the restoration lemmas
port verbatim, over the target's lowered run. The lowered run is exposed through
`LoweredView`, the source branch's `LoweredRun` record (its context, statistics, lowered
declaration, the recursor input as `constructors` and the recursor installation as
`recursors`), built from the scaffold's `LoweredRun` by `LoweredRun.view`. The scaffold's
`LoweredRun.recursors : RecursorCheck` is `LoweredView.check`; the source's `RecursorCheck` is
the target's `RecursorInstallation` (`LoweredView.recursors`).

Also here: `NestedSourceDeclaration` (from the source's `Restoration/SourceDeclaration.lean`)
and the derived views of the source's `Install/RunView.lean`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The lowered run, in the source branch's shape (its `LoweredRun`). -/
structure LoweredView (outEnv : Environment) where
  c : AddInductive.Context
  stats : AddInductive.InductiveStats
  loweredDecl : VInductDecl
  nparams : Nat
  depth : Nat
  isUnsafe : Bool
  initialEnv : VEnv
  indTypes : Array InductiveType
  ctorEnv : Environment
  /-- The constructor phase's output (the source's `OrdinaryConstructorCheck`). -/
  constructors : RecursorInput c stats loweredDecl nparams isUnsafe depth initialEnv indTypes
    ctorEnv
  /-- The recursor phase's check (the scaffold's `RecursorCheck`). -/
  check : RecursorCheck constructors outEnv

namespace LoweredView

variable {outEnv : Environment}

/-- The source's `RecursorCheck`: the recursor installation. -/
abbrev recursors (P : LoweredView outEnv) : RecursorInstallation P.constructors outEnv :=
  P.check.installation

abbrev headerEnv (P : LoweredView outEnv) : Environment := P.constructors.headerEnv

abbrev headers (P : LoweredView outEnv) :
    HeaderData P.c P.stats P.loweredDecl P.nparams P.isUnsafe P.depth P.initialEnv
      P.indTypes P.headerEnv :=
  P.constructors.headers

end LoweredView

/-- The scaffold's lowered run in the source branch's shape. -/
def LoweredRun.view {c : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
    {indTypes : Array InductiveType} {loweredEnv : Environment}
    (L : LoweredRun Hc nparams indTypes loweredEnv) : LoweredView loweredEnv where
  c := L.c'
  stats := L.stats
  loweredDecl := L.loweredDecl
  nparams := nparams
  depth := L.phase.depth
  isUnsafe := c.safety != .safe
  initialEnv := L.Hc'.venv
  indTypes := indTypes
  ctorEnv := L.ctorEnv
  constructors := L.input
  check := L.recursors

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
the restored block certificate is assembled (the source branch's `NestedRun`). -/
structure NestedRun
    (res : Lean4Lean.ElimNestedInductive.Result)
    (sourceProdEnv : Environment) (sourceTypes : List InductiveType)
    (sourceEnv : VEnv) (decl : VInductDecl) (lparams : List Name)
    (nparams : Nat) (isUnsafe : Bool) (safety : DefinitionSafety)
    (outEnv : Environment) where
  loweredEnv : Environment
  lowered : LoweredView loweredEnv
  context : AddInductive.Context
  contextWF : ContextWF context
  context_env : context.env = sourceProdEnv
  context_lparams : context.lparams = lparams
  context_safety : context.safety = safety
  context_allowPrimitive : context.allowPrimitive = false
  context_venv : contextWF.venv = sourceEnv
  lowered_c : lowered.c = context
  lowered_nparams : lowered.nparams = nparams
  lowered_isUnsafe : lowered.isUnsafe = (context.safety != .safe)
  lowered_isUnsafe_source : lowered.isUnsafe = isUnsafe
  lowered_initialEnv : lowered.initialEnv = sourceEnv
  lowered_indTypes : lowered.indTypes = res.types.toArray
  stats : AddInductive.InductiveStats
  depth : Nat
  commonParams : List VExpr
  commonLevel : VLevel
  sourceHeaderTyping :
    checkInductiveTypes.loopType.CheckedHeaders
      contextWF.venv context.lparams nparams commonParams
        commonLevel res.types.toArray.toList
  validationFuel : FuelConfig
  context_fuel : context.fuel = validationFuel
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
  parameterValidation :
    Lean4Lean.validateSourceConstructorTypes.run auxiliaryHeaderEnv
      lparams safety validationFuel sourceTypes = .ok ()
  auxiliaryVEnv : VEnv
  auxiliaryMLCtx : TypeChecker.MLCtx
  auxiliaryMLCtx_lctx : auxiliaryMLCtx.lctx = res.lctx
  auxiliaryMLCtxWF : auxiliaryMLCtx.WF auxiliaryVEnv lparams
  validatedAuxiliaries : NestedOccurrencesTyped auxiliaryVEnv lparams
    auxiliaryMLCtx.vlctx res
  auxiliarySelection : CDeclArray res.lctx res.params
  auxiliaryTranslations : ClosedNestedOccurrenceTypings auxiliaryVEnv
    lparams res auxiliarySelection
  sourceCore : NestedSourceDeclaration sourceEnv lparams nparams
    sourceTypes isUnsafe lowered.loweredDecl safety validationEnv
      auxiliaryHeaderEnv
  sourceCoreDecl_eq : sourceCore.sourceDecl = decl
  auxiliaryVEnv_eq_sourceCore : auxiliaryVEnv = sourceCore.envTypes

/-! ### Derived views (the source branch's `Install/RunView.lean`) -/

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

/-- The context certificate already recorded by the nested run, at its lowered context. -/
def NestedRun.loweredContextWF
    (E : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv) : ContextWF E.lowered.c := by
  rw [E.lowered_c]
  exact E.contextWF

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
