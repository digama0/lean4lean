import Lean4Lean.Verify.Inductive.Nested.Lowering.Expansion.AuxiliarySources
import Lean4Lean.Verify.Inductive.Nested.Lowering.Assembly

/-! # The nested expansion of a lowering run

The ordered nested expansion of the source declaration into the lowered declaration, as nested
formation reads it (`NestedExpansionData`, hence `VInductDecl.NestedFormationWF`), from the
lowering run (`NestedLoweringOutputClosed`), the recursor input of the ordinary pipeline run on
the lowered block (`RecursorInput`, the constructor phase's output) and the restoration side's
facts about the source declaration: its translation (`TrInductDeclCore`), the header prefix of
the lowered declaration, the typing of the cached nested occurrences
(`ClosedNestedOccurrenceTypings`, from `validateNestedAuxiliaries`) and source parameter
formation. The source branch's `NestedRun.assemblyBaseValid` (`Install/FromRun.lean`) assembles
the same from `auxiliaryFamilySources`, `allExpansionsOfSources` and
`NestedExpansionData.ofConstructorPhases`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- **The nested expansion of a lowering run.** -/
theorem RecursorInput.nestedExpansionData
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {ctorEnv : Environment} {fuel : Nat}
    {sourceTypes : List InductiveType} {res : ElimNestedInductive.Result}
    (R : RecursorInput c stats loweredDecl nparams isUnsafe depth sourceVEnv res.types.toArray
      ctorEnv)
    {ves : VEnvs} {safety : DefinitionSafety} (wf : ves.WF c.env)
    (hsourceVEnv : sourceVEnv = ves.venv safety) (Hc : ContextWF c)
    (Hlow : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      (loweringInitialState c.lparams sourceTypes) res)
    (hsources : checkInductiveSources c.env sourceTypes = .ok ())
    {sourceDecl : VInductDecl} {envTypes envCtors : VEnv}
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes isUnsafe sourceDecl
      envTypes envCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst sourceVEnv c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (loweredDecl.types.take sourceTypes.length))
    (HsourceAdded : sourceVEnv.addConstVals
      ((loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some envTypes)
    (HsourceTypesWF : envTypes.WF)
    (selection : CDeclArray res.lctx res.params)
    (Htranslations : ClosedNestedOccurrenceTypings envTypes c.lparams res selection)
    (Hparameters : sourceDecl.SourceParameterWF sourceVEnv) :
    ∃ D : NestedExpansionData sourceVEnv sourceDecl, D.expanded = loweredDecl := by
  have Hchecked := checkInductiveSources_refines c.env sourceTypes _ hsources
  have hne := Hlow.source_nonempty
  have hlen := Hlow.types_length
  obtain ⟨finalState, Hrun, Hcache, Hparams⟩ := Hlow
  obtain ⟨N, -⟩ := Hrun.auxiliaryFamilySources (R := R)
    (initialState := loweringInitialState c.lparams sourceTypes) Hcache Hparams wf hsourceVEnv Hc
    Hchecked HsourceHeaders HsourceAdded HsourceTypesWF (by rfl) selection Htranslations R.core
  have henv : sourceVEnv.WF := by subst hsourceVEnv; exact wf.tr.wf
  have Htypes := Hrun.allExpansionsOfSources
    (initialState := loweringInitialState c.lparams sourceTypes) Hcache Hparams Hsource R.core Hmetadata Hchecked
    (VEnvs.WF.environmentTypesClosed wf) wf.inductivesClosed henv (by rfl) N selection
  have hnonempty : res.types.toArray.toList ≠ [] := by
    intro h
    have h' : res.types = [] := by simpa using h
    rw [h'] at hlen
    exact hne (List.eq_nil_of_length_eq_zero (by simp at hlen; omega))
  exact ⟨NestedExpansionData.ofConstructorPhases R N.generated hnonempty Hparameters
    (R.core.uvars.trans Hsource.uvars.symm) (R.core.nparams.trans Hsource.nparams.symm)
    (R.core.isUnsafe.trans Hsource.isUnsafe.symm) Htypes, rfl⟩

/-- Nested formation of the source declaration, through the lowered declaration. -/
theorem RecursorInput.nestedFormationWF
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {ctorEnv : Environment} {fuel : Nat}
    {sourceTypes : List InductiveType} {res : ElimNestedInductive.Result}
    (R : RecursorInput c stats loweredDecl nparams isUnsafe depth sourceVEnv res.types.toArray
      ctorEnv)
    {ves : VEnvs} {safety : DefinitionSafety} (wf : ves.WF c.env)
    (hsourceVEnv : sourceVEnv = ves.venv safety) (Hc : ContextWF c)
    (Hlow : NestedLoweringOutputClosed c.env fuel nparams sourceTypes
      (loweringInitialState c.lparams sourceTypes) res)
    (hsources : checkInductiveSources c.env sourceTypes = .ok ())
    {sourceDecl : VInductDecl} {envTypes envCtors : VEnv}
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes isUnsafe sourceDecl
      envTypes envCtors)
    (Hmetadata : SourcePrefixOfLowered sourceDecl loweredDecl)
    (HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst sourceVEnv c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (loweredDecl.types.take sourceTypes.length))
    (HsourceAdded : sourceVEnv.addConstVals
      ((loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some envTypes)
    (HsourceTypesWF : envTypes.WF)
    (selection : CDeclArray res.lctx res.params)
    (Htranslations : ClosedNestedOccurrenceTypings envTypes c.lparams res selection)
    (Hparameters : sourceDecl.SourceParameterWF sourceVEnv) :
    sourceDecl.NestedFormationWF sourceVEnv :=
  let ⟨D, _⟩ := R.nestedExpansionData wf hsourceVEnv Hc Hlow hsources Hsource Hmetadata
    HsourceHeaders HsourceAdded HsourceTypesWF selection Htranslations Hparameters
  D.formation

end VerifyInductive
end Lean4Lean
