import Lean4Lean.Verify.Inductive.Nested.Restoration.Certificate
import Lean4Lean.Verify.Inductive.Nested.Equations.RuleAlignment
import Lean4Lean.Theory.Inductive.RestorationInterpretation
import Lean4Lean.Theory.Typing.RestorationShapes
import Lean4Lean.Theory.Inductive.RestorationHead

/-! # The typing of the restored rules (owner: Equations+Install)

The restored ι rules are typed by transport along the restoration interpretation
(`Theory/Inductive/RestorationInterpretation.lean`): the lowered run's rules are typed in its
recursor stage (`RuleTranslations.rules_wf`, `equationsWF`), the restoration substitution from
the lowered recursor stage `L.recursors.outVEnv` into the restored recursor stage `B.envR`
(`Restoration.Substitution`, with `PatClause` for the lowered rules as `RestoredPattern`s)
carries them to their restorations (`Restoration.equation_wf`), and the restored rules are
the restored equations (`RestoredBlock.rules_ofRestoredEquation`). Source branch:
`Nested/Restoration/Equations/{WF,RestoredRules,RestoredRulesBase,GeneratedGuard,RuleRhs,
SourceIota,SourceIotaFamilies,AuxiliaryConstructors,ProjNames,ProjectionRenaming}.lean`,
stated for `VDefEq`; here the `PatTyped` restatement follows the ordinary path
(`Rules/IotaPatTyped.lean`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

namespace RestoredBlock

variable {c : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
  {res : ElimNestedInductive.Result} {loweredEnv : Environment}
  {L : LoweredRun Hc nparams res.types.toArray loweredEnv}
  {sourceTypes : List InductiveType} {isUnsafe : Bool} {outEnv : Environment}

/-- The projection stage of the restored block is well formed. -/
theorem envP_wf (B : RestoredBlock L sourceTypes isUnsafe outEnv) : B.envP.WF := by
  have hsrc := B.compiled.sourceWF
  obtain ⟨_, hnodup, -, hcu, -⟩ := hsrc
  have htypesWF : ∀ type ∈ B.decl.types, type.toVConstant.WF Hc.venv :=
    TrInductDeclCore.typeHeadersWF B.source
  have hctorsWF : ∀ ci ∈ B.decl.constructorConstants, ci.toVConstant.WF B.envTypes := by
    intro ci hci
    simp only [VInductDecl.constructorConstants, List.mem_flatMap] at hci
    obtain ⟨t, ht, hci⟩ := hci
    obtain ⟨_, _, Ht⟩ := List.Forall₂.forall_exists_r B.source.types t ht
    obtain ⟨_, _, Hc⟩ := List.Forall₂.forall_exists_r Ht.ctors ci hci
    exact Hc.wf
  have hT : B.envTypes.WF := VEnv.WF.addConstVals Hc.wf
    (by
      intro ci hci
      simp only [VInductDecl.typeConstants, List.mem_map] at hci
      obtain ⟨t, ht, rfl⟩ := hci
      exact htypesWF t ht)
    B.source.typesAdded
  have hC : B.envCtors.WF := VEnv.WF.addConstVals hT hctorsWF B.source.ctorsAdded
  have := VEnv.WF.inductProjections (block := B.block) Hc.wf hC hnodup htypesWF hcu hctorsWF
    B.compiled.sourceParameters B.compiled.sourceParameters.rawCtorShape B.compiled.types
    B.compiled.ctors B.compiled.projections (B.compiled.types ▸ B.source.typesAdded)
    (B.compiled.ctors ▸ B.source.ctorsAdded)
  rw [B.compiled.projections] at this
  exact this

/-- The restored recursor stage is well formed. -/
theorem envR_wf (B : RestoredBlock L sourceTypes isUnsafe outEnv) : B.envR.WF := by
  have h := B.recsAdded
  rw [VInductDecl.addRecs_eq_addConstVals] at h
  refine VEnv.WF.addConstVals B.envP_wf ?_ h
  intro ci hci
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hci
  exact B.recs_wf r hr

/-- The restored equations are typed in the restored recursor stage: the restoration
substitution from the lowered recursor stage `L.recursors.outVEnv` into `B.envR` transports the
lowered run's `equationsWF` (`Restoration.equation_wf`); `CompilationData.equations` reads the
block's rules as the restored generated equations. -/
theorem restoredEquationsWF (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    ∀ df ∈ B.block.rules, df.WF B.envR := by
  -- WAVE 3 STUB (Equations+Install): the restoration substitution
  -- (`NestedRun.restoredEquationSubstitution`, `restoredEquationsWF_of_substitutionPremises`
  -- of the source branch's `Equations/WF.lean`, over `B.run`, restB's port of `NestedRun`,
  -- not yet a field of `RestoredBlock`).
  have := B; sorry

/-- The restored block is well formed: its equations are typed in the restored recursor
stage. -/
theorem blockWF (B : RestoredBlock L sourceTypes isUnsafe outEnv) : B.block.WF Hc.venv := by
  have htypes : B.block.types = B.decl.typeConstants := B.compiled.types
  have hctors : B.block.ctors = B.decl.constructorConstants := B.compiled.ctors
  have hprojs : B.block.projections = B.decl.projectionEntries := B.compiled.projections
  have hrecs : B.block.recursors = B.decl.recs.map (·.toVConstVal) := B.recsOf.recursors.symm
  refine ⟨B.envTypes, B.envCtors, B.envR, htypes ▸ B.source.typesAdded,
    hctors ▸ B.source.ctorsAdded, ?_, ?_, ?_, ?_, B.restoredEquationsWF⟩
  · have h := B.recsAdded
    rw [VInductDecl.addRecs_eq_addConstVals] at h
    rw [hprojs, hrecs]; exact h
  · intro ci hci
    rw [htypes] at hci
    simp only [VInductDecl.typeConstants, List.mem_map] at hci
    obtain ⟨t, ht, rfl⟩ := hci
    exact TrInductDeclCore.typeHeadersWF B.source t ht
  · intro ci hci
    rw [hctors] at hci
    simp only [VInductDecl.constructorConstants, List.mem_flatMap] at hci
    obtain ⟨t, ht, hci⟩ := hci
    obtain ⟨_, _, Ht⟩ := List.Forall₂.forall_exists_r B.source.types t ht
    obtain ⟨_, _, Hc⟩ := List.Forall₂.forall_exists_r Ht.ctors ci hci
    exact Hc.wf
  · rw [hrecs, hprojs]
    intro ci hci
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hci
    exact B.recs_wf r hr

/-- `VInductDecl.WF.rules_wf` for the restored rules, in the restored recursor stage. -/
theorem rulesWF (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    ∀ r ∈ B.decl.recs, ∀ ru ∈ r.rules, ∀ hc : ru.rhs.Closed,
      B.envR.PatTyped
        (SimplePattern.iota r.name r.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
        (SimplePattern.iotaRHS r.name ru.ctor r.numParams r.numMotives r.numMinors
          r.numIndices ru.ctorParams ru.nfields ru.rhs hc, .true) := by
  intro r hr ru hru hc
  obtain ⟨df, hdf, D, T, idx, cps, lv, hD, hidx, hcps, hl, hrh, ht⟩ := B.ruleEquation hr hru
  obtain ⟨hL, hR⟩ := B.restoredEquationsWF df hdf
  rw [hl, ht] at hL
  rw [hrh, ht] at hR
  exact VEnv.patTyped_iota_of_wrapped B.envR_wf hc hD hidx hcps hL hR

/-- `VInductDecl.WF` of the restored declaration. -/
theorem wf' (B : RestoredBlock L sourceTypes isUnsafe outEnv) (hsource : sourceTypes ≠ []) :
    B.decl.WF Hc.venv :=
  B.wf hsource B.rulesWF

/-- The compiled block with its typing, for `BlockCertificate.compiled`. -/
theorem compiledWF (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    ∃ block, B.decl.CompilesTo Hc.venv block ∧ B.decl.RecsOf block ∧ block.WF Hc.venv :=
  ⟨B.block, B.compilesTo, B.recsOf, B.blockWF⟩

end RestoredBlock
end VerifyInductive
end Lean4Lean
