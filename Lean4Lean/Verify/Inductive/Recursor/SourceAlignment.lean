import Lean4Lean.Verify.Inductive.Formation

/-! Same-index alignment of the executable family array and translated declaration.
The family and constructor packages retain both bounds together with their
translation, so recursor proofs do not repeat array/list index transport. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A family position denotes the same source and translated family. -/
structure FamilyIndexAlignment (env envTypes : VEnv) (lparams : List Name)
    (sources : Array InductiveType) (targets : List VInductiveType)
    (familyIdx : Nat) : Prop where
  source_lt : familyIdx < sources.size
  target_lt : familyIdx < targets.length
  translation : TrInductiveType env envTypes lparams
    sources[familyIdx] targets[familyIdx]

/-- A constructor position belongs to the family already selected on both sides. -/
structure ConstructorIndexAlignment
    (family : FamilyIndexAlignment env envTypes lparams sources targets familyIdx)
    (ctorIdx : Nat) : Prop where
  source_lt : ctorIdx < (sources[familyIdx]'family.source_lt).ctors.length
  target_lt : ctorIdx < (targets[familyIdx]'family.target_lt).ctors.length
  translation : TrSourceConst envTypes lparams
    (sources[familyIdx]'family.source_lt).ctors[ctorIdx].name
    (sources[familyIdx]'family.source_lt).ctors[ctorIdx].type
    (targets[familyIdx]'family.target_lt).ctors[ctorIdx]

theorem TrInductDeclCore.familyAlignmentFromSource
    (H : TrInductDeclCore env lparams nparams sources.toList isUnsafe decl
      envTypes envCtors)
    (familyIdx : Nat) (hsource : familyIdx < sources.size) :
    FamilyIndexAlignment env envTypes lparams sources decl.types familyIdx := by
  have htarget : familyIdx < decl.types.length := by
    rw [← TrInductDeclCore.types_length H]
    simpa using hsource
  have Htype := TrInductDeclCore.typeAt H familyIdx (by simpa using hsource) htarget
  rw [Array.getElem_toList] at Htype
  exact ⟨hsource, htarget, Htype⟩

theorem TrInductDeclCore.familyAlignmentFromTarget
    (H : TrInductDeclCore env lparams nparams sources.toList isUnsafe decl
      envTypes envCtors)
    (familyIdx : Nat) (htarget : familyIdx < decl.types.length) :
    FamilyIndexAlignment env envTypes lparams sources decl.types familyIdx := by
  have hsource : familyIdx < sources.size := by
    have hlength : sources.size = decl.types.length := by
      simpa only [Array.length_toList] using TrInductDeclCore.types_length H
    omega
  exact TrInductDeclCore.familyAlignmentFromSource H familyIdx hsource

theorem FamilyIndexAlignment.constructorAt
    (family : FamilyIndexAlignment env envTypes lparams sources targets familyIdx)
    (ctorIdx : Nat) (hsource : ctorIdx < (sources[familyIdx]'family.source_lt).ctors.length) :
    ConstructorIndexAlignment family ctorIdx := by
  have htarget : ctorIdx < (targets[familyIdx]'family.target_lt).ctors.length := by
    rw [← TrInductiveType.ctors_length family.translation]
    exact hsource
  exact ⟨hsource, htarget,
    TrInductiveType.ctorAt family.translation ctorIdx hsource htarget⟩

end VerifyInductive
end Lean4Lean
