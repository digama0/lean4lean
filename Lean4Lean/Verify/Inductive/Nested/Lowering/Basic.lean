import Lean4Lean.Verify.Inductive.Lowering

/-! # The lowering verification (owner: Lowering)

The interface of the lowering run is `NestedLoweringOutput` and its boundary theorem
`loweringRun.WF` (`Verify/Inductive/Lowering.lean`, lead-owned; this directory proves it).
The source branch's `Nested/Lowering/**` (`Basic`, `Queue`, `Expression`, `Recognition`,
`Levels`, `AuxiliaryFamilies`, `AuxiliaryConstructors`, `AuxiliaryFamilyPositions`,
`Expansion/**`, `ParameterOpening`, `Phases`, `Run`; about 15k lines) is the material: the
refinement of `ElimNestedInductive.run` (`NestedLowering`, `LowerNextStep`), the cache
(`NestedAuxMapModels`), the auxiliary family specifications and the restoration inverse
(`ConstructorRestorationInverse.restoredType_eqv_source`), the zero-auxiliary identity
(`types_eq_source_of_aux2nested_size_eq_zero`). The semantic content the source kept here
(`AuxiliaryFamilySpecialization`, `SpecializationGenerates`, the typing of the nested
occurrences) belongs to the restoration side now: the restoration owners translate the
syntactic cache facts of `NestedLoweringOutput` (`nested_app`, `aux_cached`) through the
validation pass `validateNestedAuxiliaries` (`Nested/Restoration/Validation/Passes.lean`).

This file collects the consequences of `NestedLoweringOutput` the nested pipeline reads
directly. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

variable {env : Environment} {fuel nparams : Nat} {sourceTypes : List InductiveType}
  {lparams : List Name} {res : ElimNestedInductive.Result}

theorem NestedLoweringOutput.types_ne_nil
    (H : NestedLoweringOutput env fuel nparams sourceTypes lparams res) : res.types ≠ [] := by
  intro hnil
  have hlen := H.types_length
  rw [hnil] at hlen
  exact H.source_nonempty (List.eq_nil_of_length_eq_zero (by simp at hlen; omega))

theorem NestedLoweringOutput.types_size_pos
    (H : NestedLoweringOutput env fuel nparams sourceTypes lparams res) :
    0 < res.types.toArray.size := by
  cases h : res.types with
  | nil => exact (H.types_ne_nil h).elim
  | cons _ _ => simp

theorem NestedLoweringOutput.source_length_le
    (H : NestedLoweringOutput env fuel nparams sourceTypes lparams res) :
    sourceTypes.length ≤ res.types.length := by
  rw [H.types_length]; exact Nat.le_add_right _ _

/-- The auxiliary families, by count. -/
theorem NestedLoweringOutput.auxTypes_length
    (H : NestedLoweringOutput env fuel nparams sourceTypes lparams res) :
    (auxTypes res sourceTypes).length = res.aux2nested.size := by
  simp [auxTypes, H.types_length]

/-- A nested block has an auxiliary family. -/
theorem NestedLoweringOutput.auxTypes_ne_nil
    (H : NestedLoweringOutput env fuel nparams sourceTypes lparams res)
    (hnested : res.aux2nested.size ≠ 0) : auxTypes res sourceTypes ≠ [] := by
  intro h
  have := H.auxTypes_length
  rw [h] at this
  exact hnested (by simpa using this.symm)

/-- The source family names, read off the lowered block. -/
theorem NestedLoweringOutput.source_names
    (H : NestedLoweringOutput env fuel nparams sourceTypes lparams res) :
    (res.types.take sourceTypes.length).map (·.name) = sourceTypes.map (·.name) := by
  rw [← List.forall₂_eq, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1) H.source_headers

end VerifyInductive
end Lean4Lean
