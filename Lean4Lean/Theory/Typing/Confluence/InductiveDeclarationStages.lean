import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Confluence.RecursorRegistration
import Lean4Lean.Theory.InductBlock
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Inductive.Formation

/-! The original typing environments of an installed inductive block.

In particular, equation typing is retained before the block's equations are
added. Moving its raw typing to a later environment is harmless; using that
move as a new semantic induction child would lose this stage information.
The intermediate well-formedness proofs below use fresh constant additions
and the actual projection registration, without installing any current rule.
-/

namespace Lean4Lean
open VExpr VEnv

structure VInductBlock.TypingStages (base : VEnv) (block : VInductBlock)
    (installed : VEnv) where
  types : VEnv
  constructors : VEnv
  recursors : VEnv
  addTypes : base.addConstVals block.types = some types
  addConstructors : types.addConstVals block.ctors = some constructors
  addRecursors : ((constructors.addEliminators block.eliminators).addProjections block.projections).addConstVals
    block.recursors = some recursors
  installed_eq : installed = recursors.addDefEqRules block.rules
  typesWF : types.WF
  constructorsWF : constructors.WF
  projectionsWF : ((constructors.addEliminators block.eliminators).addProjections block.projections).WF
  recursorsWF : recursors.WF
  sourceTypes : ∀ ci ∈ block.types, ci.toVConstant.WF base
  sourceConstructors : ∀ ci ∈ block.ctors, ci.toVConstant.WF types
  sourceRecursors : ∀ ci ∈ block.recursors,
    ci.toVConstant.WF ((constructors.addEliminators block.eliminators).addProjections block.projections)
  sourceRules : ∀ df ∈ block.rules, df.WF recursors

namespace VInductBlock.TypingStages

theorem ofInstallation {base installed : VEnv} {source : VInductDecl}
    {block : VInductBlock} (hbase : base.WF)
    (hsource : source.WF base) (hcompile : source.CompilesTo base block)
    (hblock : block.WF base) (helim : VInductBlock.EliminatorsWF base source block)
    (hinstall : block.install base = some installed) :
    Nonempty (TypingStages base block installed) := by
  obtain ⟨types, constructors, recursors, ht, hc, hr, wt, wc, wr, we⟩ := hblock
  have typesWF := hbase.addConstVals wt ht
  have constructorsWF := typesWF.addConstVals wc hc
  have ht' : base.addConstVals source.typeConstants = some types := by
    simpa only [hcompile.types] using ht
  have projectionsWF := VInductBlock.EliminatorsWF.projectionsWF helim hbase hsource hcompile ht hc
  have recursorsWF := projectionsWF.addConstVals wr hr
  have installed_eq : installed = recursors.addDefEqRules block.rules := by
    simpa [VInductBlock.install, ht, hc, hr] using hinstall.symm
  exact ⟨⟨types, constructors, recursors, ht, hc, hr, installed_eq,
    typesWF, constructorsWF, projectionsWF, recursorsWF, wt, wc, wr, we⟩⟩

variable {base installed : VEnv} {block : VInductBlock}

end VInductBlock.TypingStages
end Lean4Lean
