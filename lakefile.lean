import Lake
open Lake DSL

package lean4lean

require std from git "https://github.com/leanprover/std4" @ "main"

lean_lib Lean4Lean

@[default_target]
lean_exe lean4lean where
  root := `Main
  supportInterpreter := true
