import Lean

macro "variable!" args:(ppSpace colGt bracketedBinder)+ " in"
    cmd:ppDedent(command) : command => do
  let mut incls := #[]
  for a in args do
    match a with
    | `(bracketedBinder| ($as* $[: $_]?))
    | `(bracketedBinder| {$as* $[: $_]?})
    | `(bracketedBinder| ⦃$as* $[: $_]?⦄) =>
      for a in as do
        match a with | `(_) => pure () | _ => incls := incls.push ⟨a.raw⟩
    | `(bracketedBinder| [$a : $_]) =>
      match a with | `(_) => pure () | _ => incls := incls.push ⟨a.raw⟩
    | _ => pure ()
  `(command| variable $args* in include $incls* in $(⟨cmd.raw⟩))
