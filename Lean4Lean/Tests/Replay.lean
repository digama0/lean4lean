import Lean4Lean.Replay

/-!
Replaying a declaration with a string literal must add `Char.ofNat` and `String.ofList` before
any declaration whose string literals need them.

The first declaration with a string literal used to only schedule the two, among its other
dependencies, and mark strings as handled. Replaying from `outer`, its dependency `inner` comes
first and has a string literal of its own, so it was checked with `Char.ofNat` missing:
`unknown constant 'Char.ofNat'`. Which dependency comes first depends only on the names, so
`--import` and `--fresh` rejected valid declarations depending on what they were called.
-/

namespace Lean4Lean.Tests.Replay

open Lean

def inner : String := "inner"
def outer : String := inner ++ "outer"

run_meta do
  let newConstants := (← getEnv).constants.toList.foldl (fun m (n, ci) => m.insert n ci) {}
  discard <| Lean4Lean.Replay.replay { newConstants, checkQuot := false }
    (.empty `Lean4Lean.Tests.Replay) (decl := some ``outer)

end Lean4Lean.Tests.Replay
