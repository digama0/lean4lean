import Lean4Lean.Theory.Typing.Confluence.InductiveDeclarationStages
import Lean4Lean.Theory.Typing.Confluence.DefinitionHistory
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.InductBlock
import Lean4Lean.Theory.Inductive

/-! Recover the original block and typing stages from an actual declaration
history. The predecessor history is strictly shorter, even when later
eliminator/projection registrations leave the declaration list unchanged.
-/

namespace Lean4Lean.VEnv
open private declaration_le from Lean4Lean.Theory.Typing.Confluence.DefinitionHistory

structure InductiveStage (env : VEnv) (source : VInductDecl) (historyLength : Nat) where
  base : VEnv
  installed : VEnv
  block : VInductBlock
  earlierDeclarations : List VDecl
  earlierHistory : base.WF' earlierDeclarations
  earlier : earlierDeclarations.length < historyLength
  sourceWF : source.WF base
  compilation : source.CompilesTo base block
  typing : VInductBlock.TypingStages base block installed
  installedBelow : installed ≤ env

namespace InductiveStage

def later {env extended : VEnv} {source : VInductDecl} {n m : Nat}
    (stage : InductiveStage env source n) (hle : env ≤ extended) (bound : n ≤ m) :
    InductiveStage extended source m where
  base := stage.base
  installed := stage.installed
  block := stage.block
  earlierDeclarations := stage.earlierDeclarations
  earlierHistory := stage.earlierHistory
  earlier := Nat.lt_of_lt_of_le stage.earlier bound
  sourceWF := stage.sourceWF
  compilation := stage.compilation
  typing := stage.typing
  installedBelow := stage.installedBelow.trans hle

end InductiveStage

end Lean4Lean.VEnv
