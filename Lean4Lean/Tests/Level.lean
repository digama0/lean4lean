import Lean4Lean.Level

open Lean

/-!
# Regressions for the experimental level normalization

Soundness of `normalize'`, `isEquiv'` and `geq'` is proved in `Verify/Level.lean`. What is
*not* proved, and so is what these check, is canonicity of `normalize'` and completeness of
`isEquiv'`/`geq'`.
-/

private def u : Level := .param `u
private def v : Level := .param `v
private def w : Level := .param `w
private def x : Level := .param `x

-- The reconstruction must depend only on the sublevels, not on which `imax` chains appeared
-- in the input. These two have the same sublevels but different scaffolding keys; picking the
-- chain by parent pointers into the key set reified them to different levels. Four parameters
-- and size 10, so exhaustive fuzzing up to size 7 does not reach it.
#guard (Level.max v (.max w (.imax (.imax (.imax u v) w) x))).isEquiv'
       (Level.max v (.max w (.imax (.imax (.imax u w) v) x)))

-- `NormLevel.le` compares sublevels, not nodes: the node `{v} => {const := 2, var := [v+0]}`
-- of `imax 2 v` has its constant dominated at the empty key of `max 2 v` and its variable at
-- `{v}`, and no single entry dominates both. Reachable from the constructor universe check,
-- where it made lean4lean reject an inductive that Lean accepts.
#guard (Level.max (.ofNat 2) v).geq' (.imax (.ofNat 2) v)
#guard (Level.max (u.addOffset 2) v).geq' (.imax (u.addOffset 2) v)

-- Subsumption drains this node, and the key has to be erased rather than left empty, or
-- `BEq` on the normal form sees scaffolding that carries no information.
#guard (Level.imax u (.max u v)).isEquiv' (.max u v)

-- Equivalences the core `isEquiv` misses.
#guard (Level.max v u).isEquiv' (.max (.imax u v) u)
#guard !(Level.max v u).isEquiv (.max (.imax u v) u)

/-! ### Canonical forms -/

local elab "normalize " l:level : command => do
  Elab.Command.runTermElabM fun _ => do
    logInfo m!"{Level.normalize' (← Elab.Term.elabLevel l)}"

universe u v w

/-- info: max 1 u -/
#guard_msgs in normalize max u 1
/-- info: u -/
#guard_msgs in normalize imax 1 u
/-- info: imax 2 u -/
#guard_msgs in normalize imax 2 u

-- Constant absorption (`Tree.plainOffset?`): the sublevel `V({u}, u, 1)` is reified as the
-- plain `u+1` rather than the guarded `imax (u+1) u`, because the node's constant `1` covers
-- what the plain form contributes at `u = 0`; the constant is then redundant and dropped.
-- Without this every offset in the input doubles the size of its normal form.
/-- info: u + 1 -/
#guard_msgs in normalize u+1
/-- info: max u (v + 1) -/
#guard_msgs in normalize max u (v+1)
-- the constant survives when no variable's offset reaches it
/-- info: max 2 (u + 1) -/
#guard_msgs in normalize max 2 (u+1)
-- and the guard survives when the constant (here 0) does not cover the offset, as it must:
-- `u+2` is 2 at `u = 0`, where the level is 0
/-- info: imax (u + 2) u -/
#guard_msgs in normalize imax (u+2) u
/-- info: max v (imax (imax u v) w) -/
#guard_msgs in normalize max w (imax (imax u w) v)
/-- info: max v (imax (imax u v) w) -/
#guard_msgs in normalize max (imax (imax u v) w) (imax (imax u w) v)
/-- info: u -/
#guard_msgs in normalize imax u u
/-- info: u + 1 -/
#guard_msgs in normalize imax u (u+1)
/-- info: max 1 (imax (max (v + 1) (imax (u + 1) u)) v) -/
#guard_msgs in normalize imax u v + 1

/-! ### Bounded exhaustive canonicity and completeness

Every equivalent pair of levels must reify to the *same* level, and `isEquiv'` must accept it.
Levels are bucketed by their values on a grid of valuations, which for levels this small
decides equivalence.
-/

private def evalL (σ : Name → Nat) : Level → Nat
  | .zero => 0
  | .succ l => evalL σ l + 1
  | .max l₁ l₂ => Nat.max (evalL σ l₁) (evalL σ l₂)
  | .imax l₁ l₂ =>
    match evalL σ l₂ with
    | 0 => 0
    | n+1 => Nat.max (evalL σ l₁) (n+1)
  | .param n => σ n
  | .mvar _ => 0

private def levelsUpTo (n : Nat) : Array (Array Level) := Id.run do
  let mut tbl : Array (Array Level) := #[#[]]
  for k in [1:n+1] do
    if k = 1 then
      tbl := tbl.push #[.zero, .param `u, .param `v, .param `w]
    else
      let mut out := tbl[k-1]!.map .succ
      for i in [1:k-1] do
        for a in tbl[i]! do
          for b in tbl[k-1-i]! do
            out := out.push (.max a b)
            out := out.push (.imax a b)
      tbl := tbl.push out
  return tbl

private def valsOver (hi : Nat) : Array (Name → Nat) := Id.run do
  let mut out := #[]
  for i in [0:hi+1] do
    for j in [0:hi+1] do
      for k in [0:hi+1] do
        out := out.push fun n => if n == `u then i else if n == `v then j else k
  return out

/-- Levels of size at most `sz`, grouped by value vector; every group must be a single
`normalize'` image accepted by `isEquiv'`. -/
private def canonical (sz : Nat) : Bool := Id.run do
  let vals := valsOver (sz + 2)
  let mut buckets : Std.HashMap (Array Nat) (Level × Level) := {}
  for ls in levelsUpTo sz do
    for l in ls do
      let key := vals.map (evalL · l)
      let l' := l.normalize'
      match buckets[key]? with
      | none => buckets := buckets.insert key (l, l')
      | some (r, r') => if l' != r' || !l.isEquiv' r then return false
  return true

-- 852 levels in 123 equivalence classes, so 729 equivalent pairs are checked
#guard canonical 5
