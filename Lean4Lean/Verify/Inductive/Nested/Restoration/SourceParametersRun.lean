import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceParameters
import Lean4Lean.Verify.Inductive.Nested.Restoration.Lookups
import Lean4Lean.Verify.Inductive.Nested.Lowering.Expansion.AuxiliarySources

/-! # Source parameter formation of a nested run

`NestedRun.sourceParameterWF`: the source declaration's parameter formation, from the raw
constructor shapes of the lowered declaration transported along the nested expansion. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

theorem NestedRun.sourceParameterWF {ves : VEnvs} {result : ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes) :
    sourceDecl.SourceParameterWF (ves.venv (if isUnsafe then .unsafe else .safe)) := by
  let P := E.lowered
  have henv : P.c.env = sourceProdEnv := E.lowered_env
  have hlparams : P.c.lparams = lparams := E.lowered_lparams
  have hnparams : nparams = nparams := rfl
  have hinitial : P.Hc'.venv = ves.venv (if isUnsafe then .unsafe else .safe) :=
    E.lowered_initialEnv
  have hisUnsafe : P.isUnsafe = isUnsafe := E.lowered_isUnsafe_source
  have HcP : ContextWF P.c := E.loweredContextWF
  have Hlower := E.loweringAtContext
  rcases Hlower with ⟨finalState, Hrun, Hcache, Hparams⟩
  let R := E.lowered.constructors
  have Hsource : TrInductDeclCore P.Hc'.venv P.c.lparams nparams
      sourceTypes P.isUnsafe sourceDecl E.sourceCore.envTypes E.sourceCore.envCtors := by
    have h := E.sourceCore.core
    rw [E.sourceCoreDecl_eq] at h
    rw [hinitial, hlparams, hisUnsafe]; exact h
  have Htarget : TrInductDeclCore P.Hc'.venv P.c.lparams nparams
      result.types P.isUnsafe P.loweredDecl R.headers.context.venv R.ctorVEnv := by
    have h := R.core
    simpa using h
  have Hmetadata : SourcePrefixOfLowered sourceDecl P.loweredDecl := by
    have h := E.sourceCore.checked
    rw [E.sourceCoreDecl_eq] at h; exact h
  have wfP : ves.WF P.c.env := by rw [henv]; exact wf
  have HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst P.Hc'.venv P.c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (P.loweredDecl.types.take sourceTypes.length) := by
    rw [hinitial, hlparams]; exact E.sourceCore.sourceHeaders
  have HsourceAdded : P.Hc'.venv.addConstVals
      ((P.loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some E.sourceCore.envTypes := by
    rw [hinitial]; exact E.sourceCore.sourceAdded
  have HsourceTypesWF : E.sourceCore.envTypes.WF :=
    TrInductDeclCore.envTypesWF Hsource (by rw [hinitial]; exact (wf.tr (safety := _)).wf)
  have Htranslations : ClosedNestedOccurrenceTypings
      E.sourceCore.envTypes P.c.lparams result E.auxiliarySelection := by
    rw [← E.auxiliaryVEnv_eq_sourceCore, hlparams]
    exact E.auxiliaryTranslations
  have hempty : E.initialState.nestedAux = #[] := rfl
  obtain ⟨N, -⟩ := Hrun.auxiliaryFamilySources (R := R) Hcache Hparams wfP hinitial HcP Hsources
    HsourceHeaders HsourceAdded HsourceTypesWF hempty E.auxiliarySelection Htranslations Htarget
  have Htypes := Hrun.allExpansionsOfSources Hcache Hparams Hsource Htarget Hmetadata Hsources
    (VEnvs.WF.environmentTypesClosed wfP) wfP.inductivesClosed
    (by rw [hinitial]; exact (wf.tr (safety := _)).wf) hempty N E.auxiliarySelection
  have huvars : P.loweredDecl.uvars = sourceDecl.uvars :=
    Htarget.uvars.trans Hsource.uvars.symm
  have hdeclParams : P.loweredDecl.nparams = sourceDecl.nparams :=
    Htarget.nparams.trans Hsource.nparams.symm
  have hloweredNodup : (P.loweredDecl.types.map (·.name)).Nodup := by
    have h := (List.nodup_append.mp (TrInductDeclCore.sourceNames_nodup Htarget)).1
    simpa [VInductDecl.typeConstants, VInductiveType.toVConstVal, Function.comp_def] using h
  have Hraw : ∀ type ∈ sourceDecl.types, ∀ ctor ∈ type.ctors,
      sourceDecl.RawCtorShape type ctor :=
    VInductDecl.rawShapesOfNestedExpansions Htypes
      R.formation.formationWF.sourceParameterWF.rawCtorShape huvars hdeclParams hloweredNodup
  exact E.sourceCoreParameterWF wf Hsources Hraw

end VerifyInductive
end Lean4Lean
