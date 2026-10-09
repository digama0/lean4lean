import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.ParameterScopes
import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceTranslations
import Lean4Lean.Verify.Inductive.Nested.Install.FromRun
import Lean4Lean.Verify.Inductive.Nested.Install.CertificateOfRun

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # The inductive extension of a nested run

This module turns the executable nested run into the public
`InductiveExtension` (section 3.3 of the design notes).  Formation,
recursors, equations, closure, and unsafe restoration tags are consequences
of the run.  The only further premise of `NestedInstalledRun.inductiveExtension`
is coherence of the restored source constructors in the installed abstract
environment (`NestedInstalledConstructorsCoherent`), which
`Environment.addInductiveAfterLowering.nestedInductiveExtensionWF` derives
from the constructor parameter domains.
-/

/-- Constructor coherence at the installed environment produced by a nested
run.  Naming this premise keeps declaration dispatch independent of the
internal safe/unsafe assembly split. -/
def NestedInstalledConstructorsCoherent
    (E : NestedInstalledRun result sourceProdEnv sourceTypes sourceEnv
      decl lparams nparams isUnsafe safety outEnv) : Prop :=
  ConstructorParameterAlignment safety outEnv
    (E.assembly.recursorVEnv.addDefEqRules
      (E.assembly.sourceRules ++ E.assembly.auxiliaryRules))

/-- Uniformly turn a safe or unsafe nested execution into the public
`InductiveExtension`.  The lowering run is reindexed only by the context
equality of the lowered run retained in `E`; no separately chosen lowered run
is used. -/
theorem NestedInstalledRun.inductiveExtension
    (E : NestedInstalledRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) decl lparams nparams
      isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringOutputClosed sourceProdEnv fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[])
    (hconstructors : NestedInstalledConstructorsCoherent E)
    {venvH : VEnv}
    (htypesH : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      decl.typeConstants = some venvH)
    (hctorOrigin : ∀ {name ci}, outEnv.find? name = some (.ctorInfo ci) →
      sourceProdEnv.find? name = some (.ctorInfo ci) ∨
        (ci.isUnsafe = isUnsafe ∧ CtorTelescopeAt venvH ci)) :
    Nonempty (InductiveExtension sourceProdEnv outEnv ves lparams nparams sourceTypes
      isUnsafe) := by
  have Hlower' : NestedLoweringOutputClosed E.context.env fuel
      nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result := by
    simpa only [E.context_env] using Hlower
  have Hmetadata : SourcePrefixOfLowered decl
      E.lowered.loweredDecl := by
    simpa only [E.lowered_eq] using E.assembly.checked
  cases isUnsafe with
  | false =>
      exact E.safeInductiveExtension wf Hlower' Hmetadata
        Hsources hempty hconstructors htypesH hctorOrigin
  | true =>
      exact E.unsafeInductiveExtension wf Hlower' Hmetadata
        Hsources hempty hconstructors htypesH hctorOrigin

/-- Inductive-extension refinement for the nested post-lowering branch.  The
restored block certificate and the constructor parameter domains are
reconstructed internally from the checked lowered run, lowering, validation,
and restoration folds. -/
theorem Environment.addInductiveAfterLowering.nestedInductiveExtensionWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (fuel : FuelConfig) (res : Lean4Lean.ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WF env)
    (hmode : ∀ safety, fuel.cacheMode.Sound (ves.venv safety))
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hlower : NestedLoweringOutputClosed env fuel.inductiveFuel nparams
      sourceTypes
      { lvls := lparams.map .param, newTypes := sourceTypes.toArray } res)
    (hnested : res.aux2nested.size ≠ 0) :
    (Environment.addInductiveAfterLowering env lparams nparams sourceTypes
      isUnsafe false fuel res).WF fun outEnv =>
        Nonempty (InductiveExtension env outEnv ves lparams nparams sourceTypes
          isUnsafe) := by
  let Hc' : ContextWF
      (nestedAddInductiveContext env lparams isUnsafe false fuel) :=
    ContextWF.initial wf (if isUnsafe then .unsafe else .safe) lparams false fuel (hmode _)
  have hctx : Hc'.mlctx.vlctx = [] := rfl
  have Hc'_venv : Hc'.venv =
      ves.venv (if isUnsafe then .unsafe else .safe) := rfl
  have Hinputs : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {depth : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hctx : ContextWF c') →
      c'.allowPrimitive = false →
      c'.fuel = fuel →
      checkInductiveTypes.loopType.CheckedHeaders
        Hctx.venv c'.lparams nparams commonParams commonLevel
          res.types.toArray.toList →
      PrimitiveNamesFresh c' stats nparams depth
        res.aux2nested.size res.types.toArray
        ((nestedAddInductiveContext env lparams isUnsafe false fuel).safety !=
          .safe) Hctx := by
    intro c' stats depth commonParams commonLevel Hctx hallow _hfuel _Hsemantic
    exact PrimitiveNamesFresh.ofNoPrimitive hallow
  have HlowerInitialClosed : NestedLoweringOutputClosed env
      fuel.inductiveFuel nparams sourceTypes
      { ({ lvls := lparams.map .param, newTypes := #[] } :
          Lean4Lean.ElimNestedInductive.State) with
        newTypes := sourceTypes.toArray } res := by
    simpa using Hlower
  have HlowerInitial : NestedLoweringOutput env fuel.inductiveFuel nparams
      sourceTypes
      { ({ lvls := lparams.map .param, newTypes := #[] } :
          Lean4Lean.ElimNestedInductive.State) with
        newTypes := sourceTypes.toArray } res := by
    exact HlowerInitialClosed.toResult
  have hnonempty : 0 < res.types.toArray.size :=
    HlowerInitial.resultTypesSizePos
  have Hrun :=
    Environment.addInductiveAfterLowering.nestedValidatedRawSourceWF
      env lparams nparams sourceTypes isUnsafe false fuel res
      Hc' wf.inductivesClosed wf.envGhostFree wf.constructorOwners
      wf.listedConstructorsPresent hctx
      hnonempty (inductiveSafety_notPartial isUnsafe)
      Hinputs Hsources rfl Hlower hnested
  exact Hrun.mono fun outEnv Hout => by
    rcases Hout with ⟨c', Hctx, henv, hsafety, hlparams, hallow, hfuel,
      hvenv, sourceDecl, ⟨V⟩⟩
    have hsource : Hctx.venv = ves.venv
        (if isUnsafe then .unsafe else .safe) := by
      exact hvenv.trans Hc'_venv
    have V' : NestedRun res env sourceTypes
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
        nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv := by
      simpa only [hsource] using V
    rcases V'.assemblyOfRun wf Hsources hnested with ⟨⟨C, hproduction⟩⟩
    have Hvalid : CheckingEnv.Valid
        (if isUnsafe then .unsafe else .safe) env
          (ves.venv (if isUnsafe then .unsafe else .safe)) :=
      wf.toCheckingValid (if isUnsafe then .unsafe else .safe)
    let E' : NestedInstalledRun res env sourceTypes
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
        nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv := {
      loweredEnv := V'.loweredEnv
      lowered := V'.lowered
      context := V'.context
      contextWF := V'.contextWF
      context_env := V'.context_env
      context_lparams := V'.context_lparams
      context_safety := V'.context_safety
      lowered_c := V'.lowered_c
      lowered_nparams := V'.lowered_nparams
      lowered_isUnsafe := V'.lowered_isUnsafe
      lowered_initialEnv := V'.lowered_initialEnv
      lowered_indTypes := V'.lowered_indTypes
      validationFuel := V'.validationFuel
      lowering := V'.lowering
      restoration := V'.restoration
      primitiveSafe := V'.primitiveSafe
      validationEnv := V'.validationEnv
      validationEnvironment := by
        simpa only [V'.context_allowPrimitive] using
          V'.validationEnvironment
      recursorTypeValidation := V'.recursorTypeValidation
      recursorRuleValidation := V'.recursorRuleValidation
      auxiliaryHeaderEnv := V'.auxiliaryHeaderEnv
      headerValidationEnvironment := V'.headerValidationEnvironment
      parameterValidation := V'.parameterValidation
      auxiliaryVEnv := V'.auxiliaryVEnv
      auxiliaryMLCtx := V'.auxiliaryMLCtx
      auxiliaryMLCtx_lctx := V'.auxiliaryMLCtx_lctx
      auxiliaryMLCtxWF := V'.auxiliaryMLCtxWF
      validatedAuxiliaries := V'.validatedAuxiliaries
      auxiliarySelection := V'.auxiliarySelection
      auxiliaryTranslations := V'.auxiliaryTranslations
      sourceCore := V'.sourceCore
      sourceCoreDecl_eq := V'.sourceCoreDecl_eq
      assembly := C
      lowered_eq := hproduction
      installedResult := C.extension Hvalid }
    have HlowerExact : NestedLoweringOutputClosed E'.context.env
        fuel.inductiveFuel nparams sourceTypes
        { ({ lvls := lparams.map .param, newTypes := #[] } :
            Lean4Lean.ElimNestedInductive.State) with
          newTypes := sourceTypes.toArray } res := by
      simpa only [E'.context_env] using HlowerInitialClosed
    have hconstructors : NestedInstalledConstructorsCoherent E' := by
      have Hparams := E'.constructorParameterDomainsDefEqOfSource
        (E'.restoredFamilyParameterScopes HlowerExact rfl)
      have Howners : ConstructorOwnersPresent E'.context.env := by
        rw [E'.context_env]
        exact wf.constructorOwners
      have Hmetadata : SourcePrefixOfLowered sourceDecl
          E'.lowered.loweredDecl := by
        simpa only [E'.lowered_eq] using E'.assembly.checked
      cases isUnsafe with
      | false =>
          exact E'.safeConstructorTypingOfParameterDomains wf HlowerExact
            Hmetadata Hsources Howners rfl Hparams
      | true =>
          exact E'.unsafeConstructorTypingOfParameterDomains wf HlowerExact
            Hmetadata Hsources Howners rfl Hparams
    have htypesH : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
        sourceDecl.typeConstants = some V'.sourceCore.envTypes := by
      have h := V'.sourceCore.core.typesAdded
      rw [V'.sourceCoreDecl_eq] at h
      exact h
    exact E'.inductiveExtension wf Hsources HlowerInitialClosed rfl
      hconstructors htypesH
      (V'.restoredCtorOrigin Hsources wf.constructorOwners wf.envGhostFree)

end VerifyInductive
end Lean4Lean
