module

public import Std
public import Lean4Lean.Theory.Typing.Lemmas
public import Lean4Lean.Theory.Typing.Env

@[expose] public section

namespace Lean4Lean
namespace VEnv

theorem addInduct_WF (henv : Ordered env) (hdecl : decl.WF env)
    (henv' : addInduct env decl = some env') : Ordered env' :=
  sorry
