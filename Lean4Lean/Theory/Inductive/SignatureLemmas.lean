import Lean4Lean.Theory.Inductive.Signature
import Lean4Lean.Theory.Inductive.Formation

/-! Family and constructor lookup consequences of a normalized signature model. -/

namespace Lean4Lean.InductiveSignature

def declarationFamily (s : InductiveSignature) (owner : Fin s.families.size) : VInductiveType where
  name := s.families[owner].name
  uvars := s.uvars
  type := VExpr.wrapForalls (s.params ++ s.families[owner].indices)
    (.sort s.families[owner].resultLevel)
  numIndices := s.families[owner].indices.length
  resultLevel := s.families[owner].resultLevel
  ctors := s.constructors.toList.filterMap fun ctor =>
    if ctor.owner.val = owner.val then
      some { name := ctor.name, uvars := s.uvars, type := s.constructorType ctor }
    else none

theorem declarationFamily_mem (s : InductiveSignature) (owner : Fin s.families.size) :
    s.declarationFamily owner ∈ s.declaration.types := by
  have h : owner.val < s.declaration.types.length := by simp [declaration]
  have := List.getElem_mem h
  simpa [declaration, declarationFamily] using this

theorem Models.family {s : InductiveSignature} (H : s.Models env decl)
    (owner : Fin s.families.size) :
    ∃ source ∈ decl.types,
      s.families[owner].name = source.name ∧ s.uvars = source.uvars ∧
      s.families[owner].indices.length = source.numIndices ∧
      s.families[owner].resultLevel ≈ source.resultLevel ∧
      (s.declarationFamily owner).ctors.map VConstVal.name = source.ctors.map VConstVal.name := by
  exact Lean4Lean.List.Forall₂.forall_exists_l H.families _ (s.declarationFamily_mem owner)

def declarationCtor (s : InductiveSignature) (index : Fin s.constructors.size) : VConstVal :=
  { name := s.constructors[index].name, uvars := s.uvars,
    type := s.constructorType s.constructors[index] }

theorem declarationCtor_family (s : InductiveSignature) (index : Fin s.constructors.size) :
    s.declarationCtor index ∈ (s.declarationFamily s.constructors[index].owner).ctors := by
  simp only [declarationFamily, List.mem_filterMap]
  exact ⟨s.constructors[index], List.getElem_mem (l := s.constructors.toList) index.isLt, by simp [declarationCtor]⟩

theorem declarationCtor_mem (s : InductiveSignature) (index : Fin s.constructors.size) :
    s.declarationCtor index ∈ s.declaration.constructorConstants := by
  exact List.mem_flatMap.mpr ⟨_, s.declarationFamily_mem _, s.declarationCtor_family index⟩

theorem Models.constructor {s : InductiveSignature} (H : s.Models env decl)
    (index : Fin s.constructors.size) {envTypes : VEnv}
    (hadd : env.addConstVals decl.typeConstants = some envTypes) :
    ∃ source ∈ decl.constructorConstants,
      s.constructors[index].name = source.name ∧ s.uvars = source.uvars ∧
      envTypes.IsDefEqU decl.uvars [] (s.constructorType s.constructors[index]) source.type := by
  rcases H.constructors with ⟨envTypes', htypes, hctors⟩
  have heq : envTypes' = envTypes := Option.some.inj (htypes.symm.trans hadd)
  subst envTypes'
  exact Lean4Lean.List.Forall₂.forall_exists_l hctors _ (s.declarationCtor_mem index)

theorem Models.constructorInFamily {s : InductiveSignature}
    (H : s.Models env decl) (hnames : decl.sourceNames.Nodup)
    (index : Fin s.constructors.size) {envTypes : VEnv}
    (hadd : env.addConstVals decl.typeConstants = some envTypes)
    {family : VInductiveType} (hfamily : family ∈ decl.types)
    (hnamesEq : (s.declarationFamily s.constructors[index].owner).ctors.map VConstVal.name =
      family.ctors.map VConstVal.name) :
    ∃ source ∈ family.ctors,
      s.constructors[index].name = source.name ∧ s.uvars = source.uvars ∧
      envTypes.IsDefEqU decl.uvars [] (s.constructorType s.constructors[index]) source.type := by
  rcases H.constructor index hadd with ⟨source, hsource, hname, huvars, htype⟩
  have hctorName : s.constructors[index].name ∈ family.ctors.map VConstVal.name := by
    rw [← hnamesEq]
    exact List.mem_map.mpr ⟨s.declarationCtor index, s.declarationCtor_family index, rfl⟩
  rcases List.mem_map.mp hctorName with ⟨source', hsource', hname'⟩
  have hsourceMem : source' ∈ decl.constructorConstants :=
    List.mem_flatMap.mpr ⟨family, hfamily, hsource'⟩
  have hctorNames : (decl.constructorConstants.map VConstVal.name).Nodup :=
    (List.nodup_append.mp hnames).2.1
  have heq : source = source' := List.eq_of_mem_of_nodup_map
    hctorNames hsource hsourceMem (hname.symm.trans hname'.symm)
  subst source'
  exact ⟨source, hsource', hname, huvars, htype⟩

end Lean4Lean.InductiveSignature
