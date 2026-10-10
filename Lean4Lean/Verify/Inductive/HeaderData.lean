import Lean4Lean.Verify.Inductive.Header.Installation

/-! # The header environment without the primitive invariant

`HeaderData` is `HeaderEnvironment` with the header context a `LocalContextWF`, the part of
`ContextWF` that does not assert the primitive invariant (`HasPrimitives`): that invariant is
false in the header-only environment of the primitive `Bool`/`Nat` declarations. It is what the
constructor installation (`CtorInstall`) and the recursor phase (`RecursorInput`) read of the
header environment.

WAVE 2 install COMPAT: interface structure (shared). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The part of `ContextWF` that stays meaningful while a primitive declaration is only partly
installed: no `HasPrimitives` (nor the other `CheckingEnv.Valid` and `CheckerEnv` facts), only
the translation invariant `CheckingEnv` and the local context. -/
structure LocalContextWF (c : AddInductive.Context) where
  venv : VEnv
  checking : CheckingEnv c.safety c.env venv
  mlctx : TypeChecker.MLCtx
  mlctx_wf : mlctx.WF venv c.lparams
  typeCheckerLParams_eq : c.typeCheckerLParams = none
  onlyLams : MLCtxOnlyLams mlctx
  lctx_eq : mlctx.lctx = c.lctx
  ngen_prefix : c.ngen.namePrefix = `_ind_fresh
  indFresh : ∀ fv ∈ mlctx.vlctx.fvars, c.ngen.Reserves fv
  kernelFresh : ∀ fv ∈ mlctx.vlctx.fvars,
    ({} : TypeChecker.State).ngen.Reserves fv
  check : CheckBase venv c.lparams mlctx c.lctx c.checkLCtx

def ContextWF.toLocal {c : AddInductive.Context} (H : ContextWF c) : LocalContextWF c where
  venv := H.venv
  checking := H.checking.tr
  mlctx := H.mlctx
  mlctx_wf := H.mlctx_wf
  typeCheckerLParams_eq := H.typeCheckerLParams_eq
  onlyLams := H.onlyLams
  lctx_eq := H.lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := H.indFresh
  kernelFresh := H.kernelFresh
  check := H.check

@[simp] theorem ContextWF.toLocal_venv {c : AddInductive.Context} (H : ContextWF c) :
    H.toLocal.venv = H.venv := rfl
@[simp] theorem ContextWF.toLocal_mlctx {c : AddInductive.Context} (H : ContextWF c) :
    H.toLocal.mlctx = H.mlctx := rfl

theorem LocalContextWF.wf {c : AddInductive.Context} (H : LocalContextWF c) : H.venv.WF :=
  H.checking.wf

theorem LocalContextWF.map_wf {c : AddInductive.Context} (H : LocalContextWF c) :
    c.env.constants.WF :=
  H.checking.map_wf

/-- `HeaderEnvironment` with the header context a `LocalContextWF` (and without the header
context's `HeaderParameterContext`, which needs a `ContextWF`; the source-side one is kept, and
the parameter scope is `statsWF.parameterScope`). -/
structure HeaderData (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (decl : VInductDecl) (nparams : Nat) (isUnsafe : Bool) (depth : Nat) (sourceEnv : VEnv)
    (indTypes : Array InductiveType) (outEnv : Environment) where
  numNested : Nat
  infos : List InductiveVal
  infos_eq : infos = (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
    isUnsafe c.lparams).toList
  map_eq : outEnv.constants = insertConsts c.env.constants (infos.map .inductInfo)
  quotInit_eq : outEnv.quotInit = c.env.quotInit
  fresh : ∀ info ∈ infos, c.env.find? info.name = none
  uvars : decl.uvars = c.lparams.length
  nparams : decl.nparams = nparams
  isUnsafe : decl.isUnsafe = isUnsafe
  sourceContext : ContextWF c
  sourceContextVEnv : sourceContext.venv = sourceEnv
  context : LocalContextWF { c with env := outEnv }
  contextMLCtx : context.mlctx = sourceContext.mlctx
  typesAdded : sourceEnv.addConstVals decl.typeConstants = some context.venv
  headers : HeaderCertificate sourceEnv decl
  trHeaders : List.Forall₂ (fun (info : InductiveVal) (t : VInductiveType) =>
      TrConstVal c.safety sourceEnv (.inductInfo info) t.toVConstVal ∧
      info.ctors = t.ctors.map (·.name))
    infos decl.types
  trSources : List.Forall₂ (fun (source : InductiveType) (t : VInductiveType) =>
      TrSourceConst sourceEnv c.lparams source.name source.type t.toVConstVal ∧
      source.ctors.map (·.name) = t.ctors.map (·.name))
    indTypes.toList decl.types
  sourceParameters : HeaderParameterContext sourceContext stats headers.params depth
  sourcePresent : ListedConstructorsPresent c.env
  sourceStatsWF : checkInductiveTypes.loopInd.HeaderStatsWF sourceContext.venv c.lparams
    sourceContext.mlctx.vlctx stats decl depth
  sourceHeaderParams : sourceStatsWF.headers.params = headers.params
  statsWF : checkInductiveTypes.loopInd.HeaderStatsWF context.venv c.lparams
    context.mlctx.vlctx stats decl depth
  headerParams : statsWF.headers.params = headers.params
  parameterScopeEq : statsWF.parameterScope = sourceStatsWF.parameterScope

def HeaderEnvironment.toData {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams : Nat} {isUnsafe : Bool} {depth : Nat} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {outEnv : Environment}
    (H : HeaderEnvironment c stats decl nparams isUnsafe depth sourceEnv indTypes outEnv) :
    HeaderData c stats decl nparams isUnsafe depth sourceEnv indTypes outEnv where
  numNested := H.numNested
  infos := H.infos
  infos_eq := H.infos_eq
  map_eq := H.map_eq
  quotInit_eq := H.quotInit_eq
  fresh := H.fresh
  uvars := H.uvars
  nparams := H.nparams
  isUnsafe := H.isUnsafe
  sourceContext := H.sourceContext
  sourceContextVEnv := H.sourceContextVEnv
  context := H.context.toLocal
  contextMLCtx := H.contextMLCtx
  typesAdded := H.typesAdded
  headers := H.headers
  trHeaders := H.trHeaders
  trSources := H.trSources
  sourceParameters := H.sourceParameters
  sourcePresent := H.sourcePresent
  sourceStatsWF := H.sourceStatsWF
  sourceHeaderParams := H.sourceHeaderParams
  statsWF := H.statsWF
  headerParams := H.headerParams
  parameterScopeEq := H.parameterScopeEq

end VerifyInductive
end Lean4Lean
