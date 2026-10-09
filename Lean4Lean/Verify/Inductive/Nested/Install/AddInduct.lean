import Lean4Lean.Verify.Inductive.Nested.Restoration.Translations
import Lean4Lean.Verify.Inductive.Nested.Restoration.FreshExtensions

/-! The abstract `VEnv.AddInduct` of a restored nested block, assembled in the
stage order of `VInductBlock.install`, and the concrete `AddInduct` obtained
from it and the restoration folds. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive
/-- Assemble the abstract nested extension from its actual dependency stages.
Projection metadata is installed between constructors and recursors, exactly
as in `VInductBlock.install`; no flattened installation without the
projection stage stands in for it. -/
theorem addInductOfRestoredInstallation
    (envTypes envCtors : VEnv)
    (primaryRecursors auxiliaryRecursors : List VConstVal)
    (primaryRules auxiliaryRules : List VDefEq)
    (es : List (Name × InductiveSignature.CaseSchema))
    (Hcanonical : CompiledInductive sourceEnv decl
      { restoredBlock decl primaryRecursors auxiliaryRecursors
        primaryRules auxiliaryRules with eliminators := es })
    (Hformation : decl.NestedFormationWF sourceEnv)
    (Hsource : TrInductDeclCore sourceEnv lparams nparams sourceTypes
      isUnsafe decl envTypes envCtors)
    (hnonempty : sourceTypes ≠ [])
    (HrecursorsAdded :
      ((envCtors.addEliminators es).addProjections decl.projectionEntries).addConstVals
        (primaryRecursors ++ auxiliaryRecursors) = some outVEnv)
    (HtypesWF : ∀ ci ∈ decl.typeConstants,
      ci.toVConstant.WF sourceEnv)
    (HctorsWF : ∀ ci ∈ decl.constructorConstants,
      ci.toVConstant.WF envTypes)
    (HrecursorsWF : ∀ ci ∈ primaryRecursors ++ auxiliaryRecursors,
      ci.toVConstant.WF
        ((envCtors.addEliminators es).addProjections decl.projectionEntries))
    (HrulesWF : ∀ df ∈ primaryRules ++ auxiliaryRules,
      df.WF outVEnv)
    (Helim : VInductBlock.EliminatorsWF sourceEnv decl (decl.caseBlock es)) :
    VEnv.AddInduct sourceEnv decl
      (outVEnv.addDefEqRules (primaryRules ++ auxiliaryRules)) := by
  let block : VInductBlock := { restoredBlock decl primaryRecursors
    auxiliaryRecursors primaryRules auxiliaryRules with eliminators := es }
  have HblockWF : block.WF sourceEnv := by
    refine ⟨envTypes, envCtors, outVEnv, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [block, restoredBlock] using Hsource.typesAdded
    · simpa [block, restoredBlock] using Hsource.ctorsAdded
    · simpa [block, restoredBlock] using HrecursorsAdded
    ·
      simpa [block, restoredBlock] using HtypesWF
    ·
      simpa [block, restoredBlock] using HctorsWF
    ·
      simpa [block, restoredBlock] using HrecursorsWF
    · simpa [block, restoredBlock] using HrulesWF
  have Hinstall : block.install sourceEnv = some
      (outVEnv.addDefEqRules (primaryRules ++ auxiliaryRules)) := by
    simp [VInductBlock.install, block, restoredBlock,
      Hsource.typesAdded, Hsource.ctorsAdded, HrecursorsAdded]
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty
      Hsource
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty Hsource hnonempty)
  exact .intro
    ⟨Lean4Lean.TrInductDecl.sourceWF Htranslated,
      .nested Hformation VEnv.LE.rfl⟩
    Hcanonical HblockWF
    (Helim.congr_block rfl rfl rfl rfl) Hinstall

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Turn an abstract `VEnv.AddInduct` obtained from nested restoration into the
concrete `AddInduct`. Source lookup preservation, alignment of the kernel and
abstract environments, and delta conservativity are consequences of the
restoration folds. The caller supplies the recursor alignment (`NewRecursorsAligned`) for the same
source and target. -/
theorem NestedRestorationFolds.addInductConcrete
    (H : NestedRestorationFolds result loweredEnv sourceProdEnv
      auxRec allIndNames types auxRecNames out)
    (Habstract : VEnv.AddInduct sourceVEnv decl targetVEnv)
    (Hchecking : CheckingEnv safety out.2 targetVEnv)
    (Hprovenance : NewRecursorsAligned safety
      sourceProdEnv.constants sourceVEnv out.2.constants targetVEnv)
    (hsourceWF : sourceProdEnv.constants.WF) :
    AddInduct safety sourceProdEnv.constants sourceVEnv decl
      out.2.constants targetVEnv := by
  rcases H.freshExtensionNondelta hsourceWF with
    ⟨entries, Hfresh, hnondelta⟩
  cases Habstract with
  | intro Hdecl Hcompile Hblock Helim Hinstall =>
      apply AddInduct.intro _ Hdecl Hcompile Hblock Hinstall
      · intro name ci hfind
        exact Hfresh.preservesSourceMapFind hsourceWF hfind
      · intro _HsourceAligned
        exact Hchecking.aligned
      · exact Hfresh.deltaConservative hsourceWF hnondelta
      · exact Hprovenance
      · exact Helim

end VerifyInductive
end Lean4Lean
