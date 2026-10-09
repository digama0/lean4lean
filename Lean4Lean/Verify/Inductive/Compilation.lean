import Lean4Lean.Verify.Inductive.Formation

/-! # Compilation certificates

Per-index accumulators for the source iota rules of a block, and the
certificate of an ordinary compilation (`OrdinaryCompilationCertificate`), from which
`VInductDecl.CompilesTo` of section 2.2 of the design notes follows. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- The complete list of source iota rules of a nested declaration, one per owned
constructor.  Its pointwise judgment `VInductDecl.NestedIotaRule` allows the auxiliary
motives and minors that remain in the restored source recursor's telescope, and fields
whose recursive calls go through auxiliary recursors. -/
structure NestedIotaListCertificate (decl : VInductDecl)
    (block : VInductBlock) (ruleList : List VDefEq) : Prop where
  length : ruleList.length = decl.ownedConstructors.length
  rules : ∀ i (hctor : i < decl.ownedConstructors.length)
      (hrule : i < ruleList.length),
    Nonempty (decl.NestedIotaRule block decl.ownedConstructors[i].1
      decl.ownedConstructors[i].2 ruleList[i])

/-- Append-oriented form of `NestedIotaListCertificate`, used while the source rules are
selected from the generated rules of the lowered block. -/
structure NestedIotaBuildCertificate (decl : VInductDecl)
    (block : VInductBlock) (rules : List VDefEq) : Prop where
  covered : rules.length ≤ decl.ownedConstructors.length
  shapes : ∀ i (hrule : i < rules.length)
      (hctor : i < decl.ownedConstructors.length),
    Nonempty (decl.NestedIotaRule block decl.ownedConstructors[i].1
      decl.ownedConstructors[i].2 rules[i])

theorem NestedIotaBuildCertificate.empty
    (decl : VInductDecl) (block : VInductBlock) :
    NestedIotaBuildCertificate decl block [] where
  covered := Nat.zero_le _
  shapes _ h := by simp at h

/-- Ordinary compilation of an installed block: its layout and name uniqueness,
the generated compilation `InductiveSignature.Compiles` (read by the prelude `Eq`
declaration), and the finite derivation `CompiledInductive`. -/
structure OrdinaryCompilationCertificate (env : VEnv)
    (decl : VInductDecl) (block : VInductBlock) : Prop where
  types : block.types = decl.typeConstants
  ctors : block.ctors = decl.constructorConstants
  projections : block.projections = decl.projectionEntries
  names : List.Nodup
    ((block.types ++ block.ctors ++ block.recursors).map (·.name))
  canonical : InductiveSignature.Compiles env decl block
  finite : CompiledInductive env decl block

theorem OrdinaryCompilationCertificate.compilesTo
    (H : OrdinaryCompilationCertificate env decl block) : decl.CompilesTo env block :=
  H.finite


end VerifyInductive
end Lean4Lean
