import Lean4Lean.Theory.Inductive.Compilation

/-! Singleton elimination applies to the complete expanded signature. Since
the source declaration contains a family, its singleton branch leaves no
room for auxiliary families. Consequently restoration is the identity in
this branch, even when the surrounding compilation interface permits nesting. -/

namespace Lean4Lean.InductiveSignature

theorem CompilationData.noAuxiliaries_of_singleton
    {env : VEnv} {source expanded : VInductDecl} {s : InductiveSignature}
    {g : Instance s} {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (compilation : CompilationData env source expanded s g auxiliaries block)
    (singleton : s.families.size = 1) : auxiliaries = [] := by
  obtain ⟨envTypes, direct, _, generated, _, correspondence⟩ := compilation.correspondence
  have lengths := Lean4Lean.List.Forall₂.length_eq correspondence
  have directLength := Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp generated)
  have sourceNonempty := compilation.sourceWF.1
  have sourceLength : 0 < source.types.length := List.length_pos_iff.mpr sourceNonempty
  simp only [declaration, List.length_map, List.length_zipIdx, Array.length_toList,
    List.length_append, singleton] at lengths
  exact List.eq_nil_of_length_eq_zero (by omega)

theorem CompilationData.restoration_of_singleton
    {env : VEnv} {source expanded : VInductDecl} {s : InductiveSignature}
    {g : Instance s} {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (compilation : CompilationData env source expanded s g auxiliaries block)
    (singleton : s.families.size = 1) : compilationRestoration source auxiliaries = {} := by
  rw [compilation.noAuxiliaries_of_singleton singleton]
  rfl

/-- The singleton signature has no expanded header beyond the source
prefix. Its checked and installed family environments therefore coincide. -/
theorem CompilationData.typeConstants_of_singleton
    (compilation : CompilationData env source expanded s g auxiliaries block)
    (singleton : s.families.size = 1) : source.typeConstants = expanded.typeConstants := by
  have expandedLength := Lean4Lean.List.Forall₂.length_eq compilation.model.families
  simp only [declaration, List.length_map, List.length_zipIdx, Array.length_toList,
    singleton] at expandedLength
  obtain ⟨_, direct, _, generated, _, correspondence⟩ := compilation.correspondence
  have lengths := Lean4Lean.List.Forall₂.length_eq correspondence
  rw [compilation.noAuxiliaries_of_singleton singleton] at generated
  change some [] = some direct at generated
  cases generated
  simp only [declaration, List.length_map, List.length_zipIdx, Array.length_toList,
    singleton, List.append_nil] at lengths
  rw [compilation.headerPrefix]
  apply List.take_of_length_le
  simpa only [VInductDecl.typeConstants, List.length_map] using
    (show expanded.types.length ≤ source.types.length by omega)

end Lean4Lean.InductiveSignature
