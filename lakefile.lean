import Lake
open Lake DSL

package lean4lean

require batteries from git "https://github.com/leanprover-community/batteries" @ "main"

@[default_target]
lean_lib Lean4Lean

@[default_target]
lean_exe lean4lean where
  root := `Main
  supportInterpreter := true

@[default_target]
lean_lib Lean4Lean.Theory where
  globs := #[.andSubmodules `Lean4Lean.Theory]

@[default_target]
lean_lib Lean4Lean.Verify where
  globs := #[.andSubmodules `Lean4Lean.Verify]
