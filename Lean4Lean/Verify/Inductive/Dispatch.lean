import Lean4Lean.Verify.Inductive.Install.OrdinaryExtension
import Lean4Lean.Verify.Inductive.Primitive.Extension
import Lean4Lean.Verify.Inductive.Install.Result
import Lean4Lean.Verify.Inductive.Nested.Install.Result

/-! # Dispatch of inductive declarations

The primitive, ordinary and nested paths each produce an `InductiveExtension`; this file
combines them along the executable's own branch selection (section 3.1 of
the design notes): the primitive recognizer first, then the number of auxiliary
families returned by lowering. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- `InductiveExtension` for the ordinary branch after lowering (no auxiliary families). -/
theorem Environment.addInductiveAfterLowering.ordinaryInductiveExtensionWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (fuel : FuelConfig) (res : ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WF env)
    (hmode : ∀ safety, fuel.cacheMode.Sound (ves.venv safety))
    (Hsources : SourceSyntaxChecks sourceTypes)
    (HsourcesB : SourceBVarClosed sourceTypes)
    (Hlower : NestedLoweringOutput env fuel.inductiveFuel nparams sourceTypes
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res)
    (haux : res.aux2nested.size = 0) :
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe false fuel res).WF fun outEnv =>
        Nonempty (InductiveExtension env outEnv ves lparams nparams sourceTypes
          isUnsafe) := by
  exact (Environment.addInductiveAfterLowering.ordinaryExtensionModelWF
    env lparams nparams sourceTypes isUnsafe fuel res ves wf hmode Hsources HsourcesB
    Hlower haux).mono
      fun _ ⟨ves', wf', hle, ⟨Hspec⟩⟩ =>
        ⟨InductiveExtension.ofModel ves' wf' hle Hspec⟩

/-- `InductiveExtension` for `Environment.addInductive` on the canonical primitive
Bool/Nat declarations. -/
theorem Environment.addInductive.primitiveInductiveExtensionWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env)
    (hmode : ∀ safety, fuel.cacheMode.Sound (ves.venv safety))
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe) :
    (Environment.addInductive env lparams nparams types isUnsafe true
      fuel).WF fun outEnv =>
        Nonempty (InductiveExtension env outEnv ves lparams nparams types
          isUnsafe) := by
  have hisUnsafe : isUnsafe = false := Hshape.2.2.1
  subst isUnsafe
  exact
    (Environment.addInductive.primitiveExtensionModelWF
      env lparams nparams types false fuel ves wf hmode Hshape).mono
      fun _ ⟨ves', wf', hle, ⟨Hspec⟩⟩ =>
        ⟨{
          targetModels := ves'
          wf := wf'
          mono := hle
          specification := Hspec }⟩

/-- The checked `addDecl` form of
`Environment.addInductive.primitiveInductiveExtensionWF`. -/
theorem addInductiveDeclaration.primitiveInductiveExtensionWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env)
    (hmode : ∀ safety, fuel.cacheMode.Sound (ves.venv safety))
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun outEnv =>
        Nonempty (InductiveExtension env outEnv ves lparams nparams types
          isUnsafe) := by
  have hisUnsafe : isUnsafe = false := Hshape.2.2.1
  subst isUnsafe
  exact
    (addInductiveDeclaration.primitiveExtensionModelWF
      env lparams nparams types false fuel ves wf hmode Hshape).mono
      fun _ ⟨ves', wf', hle, ⟨Hspec⟩⟩ =>
        ⟨{
          targetModels := ves'
          wf := wf'
          mono := hle
          specification := Hspec }⟩

/-- Dispatch over the actual lowering result.  The source-facing
specification requires the source declaration to have no loose bound
variables (`SourceBVarClosed`): lowering re-closes constructor types over the
opened parameters, which would silently repair such variables, so the checked
block is literally the source only under that hypothesis.  The case without auxiliary
families is the ordinary branch; otherwise the nested branch receives the checked lowering
output selected by execution. -/
theorem Environment.addInductive.inductiveExtensionWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env)
    (hmode : ∀ safety, fuel.cacheMode.Sound (ves.venv safety))
    (HsourcesB : SourceBVarClosed types) :
    (Environment.addInductive env lparams nparams types isUnsafe false
      fuel).WF fun outEnv =>
        Nonempty (InductiveExtension env outEnv ves lparams nparams types
          isUnsafe) := by
  refine Environment.addInductive.checkedLoweringClosedWF env lparams nparams
    types isUnsafe false fuel wf.inductivesClosed
      (VEnvs.WF.environmentTypesClosed wf)
      (fun outEnv => Nonempty (InductiveExtension env outEnv ves lparams
        nparams types isUnsafe)) ?_
  intro res Hsources Hlower
  by_cases haux : res.aux2nested.size = 0
  · exact Environment.addInductiveAfterLowering.ordinaryInductiveExtensionWF
      env lparams nparams types isUnsafe fuel res ves wf hmode Hsources HsourcesB
      Hlower.toResult haux
  · exact
      Environment.addInductiveAfterLowering.nestedInductiveExtensionWF
        env lparams nparams types isUnsafe fuel res ves wf hmode Hsources Hlower haux

/-- Checked `addDecl` for the non-primitive branch, given that the executable's primitive
recognizer returns `false`; the choice between the ordinary and nested branches is made
inside, by `Environment.addInductive.inductiveExtensionWF`. -/
theorem addInductiveDeclaration.inductiveExtensionWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env)
    (hmode : ∀ safety, fuel.cacheMode.Sound (ves.venv safety))
    (HsourcesB : SourceBVarClosed types)
    (hcheck : Primitive.checkInductive env lparams nparams types
      isUnsafe = .ok false) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun outEnv =>
        Nonempty (InductiveExtension env outEnv ves lparams nparams types
          isUnsafe) := by
  have Hrun := Environment.addInductive.inductiveExtensionWF env lparams
    nparams types isUnsafe fuel ves wf hmode HsourcesB
  simpa [Lean4Lean.addDecl, hcheck, bind, Except.bind] using Hrun

end VerifyInductive
end Lean4Lean
