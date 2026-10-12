import Lean4Lean.Verify.Inductive.Header.Declare

/-! # The header environment without the primitive invariant

`HeaderData` is the header environment with the header context a `LocalContextWF`, the part of
`ContextWF` that does not assert the primitive invariant (`HasPrimitives`): that invariant is
false in the header-only environment of the primitive `Bool`/`Nat` declarations. It is what the
constructor installation (`CtorInstall`) and the constructor check (`ConstructorCheck`) read of
the header environment. The ordinary header phase's `HeaderEnvironment` extends it with the
validity of the header context (`Header/Installation.lean`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The frame of a `ContextWF` with only the translation invariant `CheckingEnv` for its
environment, which stays meaningful while a primitive declaration is only partly installed: no
`HasPrimitives` (nor the other `CheckingEnv.Valid` facts, nor the recursor facts of
`ContextSemantics`). `ContextWF` and `LocalContextWF` share their local frame (`ContextFrame`)
and differ only in what they assert of the environment, `CheckingEnv.Valid` with the recursor
facts against `CheckingEnv`; they convert by `ContextWF.toLocal` and
`LocalContextWF.toContextWF`. -/
structure LocalContextWF (c : AddInductive.Context) extends toFrame : ContextFrame c c.lparams
    where
  checking : CheckingEnv c.safety c.env venv
  typeCheckerLParams_eq : c.typeCheckerLParams = none

abbrev ContextWF.toLocal {c : AddInductive.Context} (H : ContextWF c) : LocalContextWF c where
  toFrame := H.toFrame
  checking := H.checking.tr
  typeCheckerLParams_eq := H.typeCheckerLParams_eq

@[simp] theorem ContextWF.toLocal_venv {c : AddInductive.Context} (H : ContextWF c) :
    H.toLocal.venv = H.venv := rfl
@[simp] theorem ContextWF.toLocal_mlctx {c : AddInductive.Context} (H : ContextWF c) :
    H.toLocal.mlctx = H.mlctx := rfl

/-- A `ContextWF` from its local part and the validity facts the local part omits. Its
`toLocal` is the local part, definitionally. -/
abbrev LocalContextWF.toContextWF {c : AddInductive.Context} (L : LocalContextWF c)
    (valid : CheckingEnv.Valid c.safety c.env L.venv)
    (shapes : RecursorShapesCoherent c.safety c.env.constants L.venv)
    (iota : IotaRulesRegistered c.safety c.env L.venv) : ContextWF c where
  toFrame := L.toFrame
  checking := valid
  shapes := shapes
  iota := iota
  typeCheckerLParams_eq := L.typeCheckerLParams_eq

theorem LocalContextWF.wf {c : AddInductive.Context} (H : LocalContextWF c) : H.venv.WF :=
  H.checking.wf

theorem LocalContextWF.map_wf {c : AddInductive.Context} (H : LocalContextWF c) :
    c.env.constants.WF :=
  H.checking.map_wf

/-- Move a local context to a larger environment over the same local context. -/
abbrev LocalContextWF.withEnv {c : AddInductive.Context} (H : LocalContextWF c)
    {env' : Environment} {venv' : VEnv} (hchecking : CheckingEnv c.safety env' venv')
    (hle : H.venv ≤ venv') : LocalContextWF { c with env := env' } where
  toFrame := H.toFrame.withEnv hle
  checking := hchecking
  typeCheckerLParams_eq := H.typeCheckerLParams_eq

/-- The header environment of a declaration, with the header context a `LocalContextWF` (and
without the header context's `HeaderParameterContext`, which needs a `ContextWF`; the
source-side one is kept, and the parameter scope is `statsWF.parameterScope`). -/
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

end VerifyInductive
end Lean4Lean
