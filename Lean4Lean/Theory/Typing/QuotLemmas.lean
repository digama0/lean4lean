import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.Meta

namespace Lean4Lean

open Lean (Name FVarId)
open VExpr

namespace VEnv

theorem addQuot_WF (henv : Ordered env) (hq : QuotReady env) :
    addQuot env = some env' → Ordered env' := by
  refine with_addConst (cis := [(_, _)]) (hcis := ⟨hq, ⟨⟩⟩) henv
    (fun _ => ⟨_, by type_tac⟩) fun henv => ?_
  refine with_addConst henv (fun ⟨quot, _⟩ => ⟨_, by type_tac⟩) fun henv => ?_
  refine with_addConst henv (fun ⟨_, quot, _⟩ => ⟨_, by type_tac⟩) fun henv => ?_
  refine with_addConst henv (fun ⟨_, _, quot, eq, _⟩ => ⟨_, by type_tac⟩) fun henv => ?_
  rintro ⟨_, _, _, _, eq, _⟩ ⟨⟩; exact .defeq henv ⟨by type_tac, by type_tac⟩
