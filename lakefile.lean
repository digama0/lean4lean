import Lake
open Lake DSL

package lean4lean

-- require std from git "https://github.com/leanprover/std4" @ "main"
require std from git "https://github.com/JamesGallicchio/std4" @ "perm-move"

@[default_target]
lean_lib Lean4Lean

@[default_target]
lean_exe lean4lean where
  root := `Main
  supportInterpreter := true

@[default_target]
lean_lib Lean4Lean.Theory

@[default_target]
lean_lib Lean4Lean.Verify
