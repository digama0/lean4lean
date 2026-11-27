import Lean4Lean.Environment

/-!
Tests for the cache of successful `isDefEq` queries (`State.success`).

The cache is a set of pairs, as in Lean's kernel since leanprover/lean4#14806, and no longer a
union-find. Two properties are tested, on chosen examples first and on generated ones in the last
section.

* **`isDefEq` does not depend on the queries before it.** It is sound but incomplete, hence not
  transitive: there are `A`, `B`, `C` with `A =?= B` and `B =?= C` accepted and `A =?= C` refuted.
  A union-find answers `A =?= C` from the transitive closure of the first two, so the answer
  depends on what was asked before (the last section).

* **A pair that was decided is answered on entry.** The union-find was consulted behind a hash
  test: at the entry of `isDefEqCore'` it answered `false` as soon as the two hashes differed,
  without looking at the classes, so a recorded equality was only seen again after a reduction
  step. Definitional equalities do not preserve hashes, so the same pair was usually decided again
  from scratch. Two things went wrong:

  * On a term that is shared as a DAG the repetition is exponential (`tower` below).
  * Deciding a pair again is not free of side effects. It can run a full `whnfCore` on a
    projection that the first decision had left stuck, and the unfolded result then sits in
    `whnfCoreCache`, where `cheapProj := true` requests find it. A later comparison of that
    projection against a third term loses the lazy "compare the structures first" path and has to
    compare the unfolded bodies. This is what happened on `New.Variety.tiltTheory` of
    lsernau/grh-lean@72fead10, which took 132 minutes of a run that peaked at 332 GB.

The work is measured in calls of `isDefEqCore'`, counted by `countingMethods`, so the tests are
deterministic and do not depend on the speed of the machine.
-/

namespace Lean4Lean.Tests.DefEqCache

open Lean Lean4Lean TypeChecker

private def c (n : Name) : Expr := .const n []

private def check (what : String) (b : Bool) : MetaM Unit :=
  unless b do throwError "DefEqCache test failed: {what}"

private def runM (r : Except Kernel.Exception α) : MetaM α := do
  match r with
  | .ok a => pure a
  | .error e => throwError "kernel operation failed: {← (e.toMessageData {}).toString}"

/-! ### The set of pairs on its own -/

run_meta
  let env := (← getEnv).toKernelEnv
  let record (st : State) (t s : Expr) : MetaM State :=
    return (← runM <| (Inner.cacheSuccess t s { env }).run st).2
  let seen (st : State) (t s : Expr) : Bool := Inner.succeededBefore st.success t s
  let a := c `a; let b := c `b; let d := c `d; let e := c `e; let f := c `f
  check "the test constants have pairwise distinct hashes"
    (a.hash != b.hash && a.hash != d.hash && b.hash != d.hash && b.hash != e.hash &&
     a.hash != e.hash && (Expr.app f a).hash != (Expr.app f b).hash)
  let st : State := {}
  check "nothing is recorded at the start" (!seen st a b && !seen st a a)
  -- record `a ≡ b`, as `isDefEq` does after a successful `isDefEqCore`
  let st ← record st a b
  check "a recorded pair is seen in both orders" (seen st a b && seen st b a)
  check "an unrelated term stays unrelated" (!seen st a d && !seen st d b)
  let st ← record st b a
  check "a pair is stored once, whichever way round it is recorded" (st.success.size == 1)
  -- the set is not closed under anything
  let st ← record st b e
  check "the second pair is seen" (seen st b e && seen st e b)
  check "no transitivity: a ≡ b and b ≡ e do not give a ≡ e" (!seen st a e && !seen st e a)
  check "no reflexivity" (!seen st a a)
  check "no congruence: a ≡ b does not give f a ≡ f b" (!seen st (.app f a) (.app f b))

/-! ### A shared pair is decided once

    axiom z : Nat      axiom z' : Nat      axiom P : Nat → Nat → Nat
    def a := z         def b := z          def c := z'
    A₀ := a, Aₖ₊₁ := P Aₖ Aₖ        B₀ := b, Bₖ₊₁ := P Bₖ Bₖ

`Aₖ₊₁ =?= Bₖ₊₁` poses the subproblem `Aₖ =?= Bₖ` twice, once per argument of `P`. Neither side
reduces (`P` is an axiom), so the only thing that can answer the second occurrence without
descending again is the pair recorded after the first. -/

private def nat : Expr := .const ``Nat []

private def tower (P leaf : Expr) : Nat → Expr
  | 0 => leaf
  | n + 1 => let x := tower P leaf n; mkApp2 P x x

private def prop : Expr := .sort .zero
private def natPair : Expr := mkApp2 (.const ``Prod [.zero, .zero]) nat nat
private def pair (x y : Expr) : Expr := mkApp4 (.const ``Prod.mk [.zero, .zero]) nat nat x y

/-- Depth of the towers inside `L4LEq.V` and `L4LEq.W`. -/
private def bodyDepth : Nat := 16

/-- Stuck on a proof of `Acc R y` that is not a constructor application, and `0` on
`Acc.intro ..`. -/
private noncomputable def stuckOrZero {T : Type} {R : T → T → Prop} {y : T} (h : Acc R y) :
    Nat :=
  Acc.rec (motive := fun _ _ => Nat) (fun _ _ _ => Nat.zero) h

/-- The test environment: the current one plus

    axiom z z' : Nat                     axiom P : Nat → Nat → Nat
    def a := z      def b := z           def c := z'
    axiom Pr : Prop                      axiom h₀ h₁ h₂ : Pr
    def L (_ : Pr) : Nat := z
    @[reducible] def fst (s : Nat × Nat) : Nat := s.1
    def V (h : Pr) : Nat × Nat := (tower (L h), z)     -- depth `bodyDepth`
    def W (h : Pr) : Nat × Nat := (tower c, z)
    axiom R : Nat → Nat → Prop           axiom acc : Acc R z
    def stuck : Nat := stuckOrZero acc
    def unstuck : Nat := stuckOrZero (Acc.intro z fun _ hy => Acc.inv acc hy)

Every declaration goes through `Lean4Lean.addDecl`, so the terms used below are well typed. -/
private def setup (env : Kernel.Environment) : MetaM Kernel.Environment := do
  let ax (n : Name) (type : Expr) : Declaration :=
    .axiomDecl { name := n, levelParams := [], type, isUnsafe := false }
  let df (n : Name) (type value : Expr) (hints : ReducibilityHints) : Declaration :=
    .defnDecl { name := n, levelParams := [], type, value, hints, safety := .safe }
  let P := c `L4LEq.P; let Pr := c `L4LEq.Pr; let R := c `L4LEq.R; let z := c `L4LEq.z
  let acc := c `L4LEq.acc
  let soz (h : Expr) : Expr := mkApp4 (c ``stuckOrZero) nat R z h
  let mut env := env
  for d in [
      ax `L4LEq.z nat, ax `L4LEq.z' nat,
      ax `L4LEq.P (.forallE `x nat (.forallE `y nat nat .default) .default),
      df `L4LEq.a nat z (.regular 1), df `L4LEq.b nat z (.regular 1),
      df `L4LEq.c nat (c `L4LEq.z') (.regular 1),
      ax `L4LEq.Pr prop, ax `L4LEq.h₀ Pr, ax `L4LEq.h₁ Pr, ax `L4LEq.h₂ Pr,
      df `L4LEq.L (.forallE `h Pr nat .default) (.lam `h Pr z .default) (.regular 1),
      df `L4LEq.fst (.forallE `s natPair nat .default)
        (.lam `s natPair (.proj ``Prod 0 (.bvar 0)) .default) .abbrev,
      df `L4LEq.V (.forallE `h Pr natPair .default)
        (.lam `h Pr (pair (tower P (.app (c `L4LEq.L) (.bvar 0)) bodyDepth) z) .default)
        (.regular 2),
      df `L4LEq.W (.forallE `h Pr natPair .default)
        (.lam `h Pr (pair (tower P (c `L4LEq.c) bodyDepth) z) .default)
        (.regular 2),
      ax `L4LEq.R (.forallE `x nat (.forallE `y nat prop .default) .default),
      ax `L4LEq.acc (mkApp3 (.const ``Acc [1]) nat R z),
      df `L4LEq.stuck nat (soz acc) (.regular 1),
      df `L4LEq.unstuck nat
        (soz <| mkApp4 (.const ``Acc.intro [1]) nat R z <|
          .lam `y nat (.lam `hy (mkApp2 R (.bvar 0) z)
            (mkApp6 (.const ``Acc.inv [1]) nat R z (.bvar 1) acc (.bvar 0)) .default) .default)
        (.regular 1)] do
    env ← runM (Lean4Lean.addDecl env d)
  return env

/-- `Methods.withFuel`, except that every call of `isDefEqCore` bumps the index of the name
generator. The terms compared below contain no binder, so nothing else uses that index, and its
final value is the number of `isDefEqCore'` calls: a deterministic measure of the work done, where a
time limit would depend on the machine. -/
private def countingMethods : Nat → Methods
  | 0 =>
    { isDefEqCore := fun _ _ => throw .deepRecursion
      whnfCore := fun _ _ => throw .deepRecursion
      whnf := fun _ => throw .deepRecursion
      inferType := fun _ _ => throw .deepRecursion }
  | n + 1 =>
    { isDefEqCore := fun t s => do
        modify fun st => { st with ngen := { st.ngen with idx := st.ngen.idx + 1 } }
        Inner.isDefEqCore' t s (countingMethods n)
      whnfCore := fun e p => Inner.whnfCore' e p (countingMethods n)
      whnf := fun e => Inner.whnf' e (countingMethods n)
      inferType := fun e i => Inner.inferType' e i (countingMethods n) }

/-- Runs `x` in `env` with a fresh state and the counting methods. -/
private def runCounting (env : Kernel.Environment) (x : RecM α) : MetaM α := do
  let (a, _) ← runM <| (x (countingMethods 100000) { env }).run {}
  return a

/-- The number of `isDefEqCore'` calls made so far in this state. -/
private def calls : RecM Nat := return (← get).ngen.idx

/-- `Inner.isDefEq t s`, with the number of `isDefEqCore'` calls it made. -/
private def counted (t s : Expr) : RecM (Bool × Nat) := do
  let k ← calls
  let r ← Inner.isDefEq t s
  return (r, (← calls) - k)

/-- Decides `t =?= s` in `env` from a fresh state, with the number of `isDefEqCore'` calls. -/
private def countedIsDefEq (env : Kernel.Environment) (t s : Expr) : MetaM (Bool × Nat) :=
  runCounting env (counted t s)

/-- `theorem name : lhs = rhs := Eq.refl lhs` -/
private def eqThm (name : Name) (lhs rhs : Expr) : Declaration :=
  .thmDecl {
    name, levelParams := []
    type := mkApp3 (.const ``Eq [1]) nat lhs rhs
    value := mkApp2 (.const ``Eq.refl [1]) nat lhs }

/-- Whether Lean's own kernel accepts `d` on top of `env`. -/
private def nativeAccepts (env : Kernel.Environment) (d : Declaration) : Bool :=
  (env.addDeclCore 0 0 d (cancelTk? := none)).toBool

run_meta
  let env ← setup (← getEnv).toKernelEnv
  let P := c `L4LEq.P
  let A := tower P (c `L4LEq.a); let B := tower P (c `L4LEq.b); let C := tower P (c `L4LEq.c)
  -- Linear, not exponential. The count is `3 n + 1`: per level one call for `P =?= P` and two
  -- for the arguments, the second of which is answered on entry. Without that, the count is
  -- `3 · 2ⁿ - 2` (196 606 for `n = 16`).
  for n in [1, 4, 16] do
    let (r, calls) ← countedIsDefEq env (A n) (B n)
    unless r do throwError "depth {n}: A =?= B was refuted"
    unless calls ≤ 4 * n + 4 do
      throwError "depth {n}: A =?= B took {calls} isDefEqCore' calls, expected at most {4 * n + 4}"
  -- A pair that is *not* equal stays unequal: here the first argument is settled (and recorded)
  -- before the second, which differs only in its innermost leaf, is refuted.
  for n in [0, 1, 4, 16] do
    let rhs := mkApp2 P (B n) (C n)
    let (r, calls) ← countedIsDefEq env (A (n + 1)) rhs
    if r then throwError "depth {n}: P A A =?= P B C was accepted"
    unless calls ≤ 16 * n + 32 do
      throwError "depth {n}: refuting P A A =?= P B C took {calls} isDefEqCore' calls"
    -- and nothing recorded on the way makes the mirrored question succeed
    let (r, _) ← countedIsDefEq env rhs (A (n + 1))
    if r then throwError "depth {n}: P B C =?= P A A was accepted"
  -- The same through `addDecl`, at a depth that only a linear check can reach.
  let n := 400
  let good := eqThm `L4LEq.good (A n) (B n)
  let bad := eqThm `L4LEq.bad (A n) (mkApp2 P (B (n - 1)) (C (n - 1)))
  _ ← runM <| Lean4Lean.addDecl env good
  if (Lean4Lean.addDecl env bad).toBool then
    throwError "a theorem identifying two different axioms was accepted"
  -- Lean's own kernel agrees on both.
  unless nativeAccepts env good do throwError "the native kernel rejected the valid theorem"
  if nativeAccepts env bad then throwError "the native kernel accepted the invalid theorem"

/-! ### A decided pair is answered on entry, and deciding it again has no side effects

With `X h := fst (V h)`, the question `X h₁ =?= X h₀` is settled lazily: unfold `fst`, leave both
projections `(V h).1` stuck, compare `V h₁ =?= V h₀` by arguments, which are two proofs of `Pr`.
Three calls, and `V` is never unfolded.

Asking it again must not cost more than the first time, and must not disturb anything. With the
union-find behind the hash test it did both. If in the meantime `(V h₀).1` has been fully reduced,
which is what `whnf` does with `X h₀` whenever type inference needs its normal form, the cache
gives the second attempt that normal form on one side, so it fully reduces `(V h₁).1` as well to
compare the bodies, and leaves *that* in the cache. From then on `X h₁ =?= X h₂` is no longer three
calls either: `(V h₁).1` comes back from the cache unfolded, `(V h₂).1` has to follow, and the two
bodies (towers of depth `bodyDepth` here) are compared instead of the two proofs. The second and
the third question then took 327 679 calls each. -/

run_meta
  let env ← setup (← getEnv).toKernelEnv
  let V (h : Name) : Expr := .app (c `L4LEq.V) (c h)
  let X (h : Name) : Expr := .app (c `L4LEq.fst) (V h)
  let stuck (h : Name) : Expr := .proj ``Prod 0 (V h)
  let (first, hasNF₀, again, hasNF₁, third) ← runCounting env do
    let first ← counted (X `L4LEq.h₁) (X `L4LEq.h₀)
    _ ← Inner.whnf (X `L4LEq.h₀)
    let hasNF₀ := (← get).whnfCoreCache.contains (stuck `L4LEq.h₀)
    let again ← counted (X `L4LEq.h₁) (X `L4LEq.h₀)
    let hasNF₁ := (← get).whnfCoreCache.contains (stuck `L4LEq.h₁)
    let third ← counted (X `L4LEq.h₁) (X `L4LEq.h₂)
    return (first, hasNF₀, again, hasNF₁, third)
  unless first.1 do throwError "X h₁ =?= X h₀ was refuted"
  unless first.2 ≤ 4 do throwError "X h₁ =?= X h₀ took {first.2} isDefEqCore' calls, expected 3"
  -- the scenario needs the normal form of `(V h₀).1` to be in the cache at this point
  unless hasNF₀ do throwError "precondition: `whnf (X h₀)` did not cache the reduct of `(V h₀).1`"
  unless again.1 do throwError "X h₁ =?= X h₀ was refuted the second time"
  unless again.2 == 1 do
    throwError "the already decided X h₁ =?= X h₀ took {again.2} isDefEqCore' calls, expected 1"
  if hasNF₁ then
    throwError "deciding X h₁ =?= X h₀ again left the unfolded `(V h₁).1` in the whnfCore cache"
  unless third.1 do throwError "X h₁ =?= X h₂ was refuted"
  unless third.2 ≤ 4 do
    throwError "X h₁ =?= X h₂ took {third.2} isDefEqCore' calls, expected 3: the lazy path was lost"
  -- The same shape with a different body is still refuted, also after the equalities above.
  let Y : Expr := .app (c `L4LEq.fst) (.app (c `L4LEq.W) (c `L4LEq.h₂))
  let (ok, bad₁, bad₂) ← runCounting env do
    let ok ← counted (X `L4LEq.h₁) (X `L4LEq.h₀)
    let bad₁ ← counted (X `L4LEq.h₁) Y
    let bad₂ ← counted Y (X `L4LEq.h₀)
    return (ok, bad₁, bad₂)
  unless ok.1 do throwError "X h₁ =?= X h₀ was refuted"
  if bad₁.1 || bad₂.1 then throwError "fst (V h) =?= fst (W h) was accepted"
  -- refuting has to look into the bodies, which takes a number of calls linear in their depth
  unless bad₁.2 ≤ 8 * bodyDepth && bad₂.2 ≤ 8 * bodyDepth do
    throwError "refuting fst (V h) =?= fst (W h) took {bad₁.2} and {bad₂.2} isDefEqCore' calls"

/-! ### The answer does not depend on the queries before it

The standard example of the missing transitivity: with `acc : Acc R z` an axiom (or a variable),

    A := stuckOrZero acc                                             -- `Acc.rec` is stuck
    B := stuckOrZero (Acc.intro z fun _ hy => Acc.inv acc hy)        -- reduces to `0`

`A =?= B` holds by proof irrelevance and `B =?= 0` by reduction, but `A =?= 0` is refuted: nothing
suggests replacing `acc` by another proof.

A union-find that has seen the first two has `A` and `0` in one class. Behind the hash test that
showed in an odd way: `A =?= 0` itself was still refuted, since the entry check stopped at the two
hashes, but `(fun n => n) A =?= 0` was accepted, because the check after the beta step looked at
the classes. So the answer depended on the earlier queries and on whether a reduction step, or a
hash collision, came first; `bugs/rec-missing-ih` in the Lean Kernel Arena is a proof of `False`
built on that in the C++ kernel. With a set of pairs every one of these is refuted, whatever came
before, which is also what Lean's kernel answers. -/

run_meta
  let env ← setup (← getEnv).toKernelEnv
  let A := c `L4LEq.stuck; let B := c `L4LEq.unstuck; let zero := Expr.const ``Nat.zero []
  let wrapped := Expr.app (.lam `n nat (.bvar 0) .default) A
  -- each question on its own
  for (what, t, s, expected) in [("A =?= B", A, B, true), ("B =?= 0", B, zero, true),
      ("A =?= 0", A, zero, false), ("0 =?= A", zero, A, false),
      ("(fun n => n) A =?= 0", wrapped, zero, false)] do
    let (r, _) ← countedIsDefEq env t s
    unless r == expected do
      throwError "{what} on its own: expected {expected}"
  -- the last three again, in one state, after the first two have succeeded
  let (ab, b0, a0, a0', w0, w0') ← runCounting env do
    let ab ← Inner.isDefEq A B
    let b0 ← Inner.isDefEq B zero
    return (ab, b0, ← Inner.isDefEq A zero, ← Inner.isDefEq zero A,
      ← Inner.isDefEq wrapped zero, ← Inner.isDefEq zero wrapped)
  unless ab && b0 do throwError "A =?= B or B =?= 0 was refuted"
  if a0 || a0' then throwError "A =?= 0 was accepted after A =?= B and B =?= 0"
  if w0 || w0' then
    throwError "(fun n => n) A =?= 0 was accepted after A =?= B and B =?= 0, \
      although it is refuted on its own"

/-! The same through `addDecl`, with `acc` a variable: a theorem that first proves `A = B` and
`B = 0` by `rfl` and then needs `A = 0` (or `(fun n => n) A = 0`) by `rfl`. -/

open Meta in
run_meta
  let env := (← getEnv).toKernelEnv
  -- `fun T R x acc => (prefix) @id (lhs = 0) (Eq.refl lhs)`, as a proof of `∀ T R x acc, lhs = 0`
  let mkThm (halves wrap : Bool) : MetaM Declaration :=
    withLocalDeclD `T (.sort 1) fun T => do
    withLocalDeclD `R (← mkArrow T (← mkArrow T prop)) fun R => do
    withLocalDeclD `x T fun x => do
    withLocalDeclD `acc (← mkAppM ``Acc #[R, x]) fun acc => do
      let a ← mkAppM ``stuckOrZero #[acc]
      let inv ← withLocalDeclD `y T fun y => do
        withLocalDeclD `hy (mkApp2 R y x) fun hy => do
          mkLambdaFVars #[y, hy] (← mkAppM ``Acc.inv #[acc, hy])
      let b ← mkAppM ``stuckOrZero #[← mkAppM ``Acc.intro #[x, inv]]
      let zero := Expr.const ``Nat.zero []
      let lhs := if wrap then .app (.lam `n nat (.bvar 0) .default) a else a
      let goal ← mkEq lhs zero
      let mut value := mkApp2 (.const ``id [.zero]) goal (← mkEqRefl lhs)
      if halves then
        value := .letE `h₁ (← mkEq a b) (← mkEqRefl a) (.letE `h₂ (← mkEq b zero) (← mkEqRefl b)
          value true) true
      let xs := #[T, R, x, acc]
      return .thmDecl { name := `L4LEq.trans, levelParams := [],
                        type := ← mkForallFVars xs goal, value := ← mkLambdaFVars xs value }
  for halves in [false, true] do
    for wrap in [false, true] do
      let d ← mkThm halves wrap
      let what := (if wrap then "(fun n => n) A = 0" else "A = 0") ++
        (if halves then " after A = B and B = 0" else " on its own")
      if (Lean4Lean.addDecl env d).toBool then throwError "{what} was accepted"
      if nativeAccepts env d then throwError "{what} was accepted by the native kernel"
  -- the two halves themselves are fine: the same term with a goal that holds is accepted
  let okThm : MetaM Declaration :=
    withLocalDeclD `T (.sort 1) fun T => do
    withLocalDeclD `R (← mkArrow T (← mkArrow T prop)) fun R => do
    withLocalDeclD `x T fun x => do
    withLocalDeclD `acc (← mkAppM ``Acc #[R, x]) fun acc => do
      let a ← mkAppM ``stuckOrZero #[acc]
      let inv ← withLocalDeclD `y T fun y => do
        withLocalDeclD `hy (mkApp2 R y x) fun hy => do
          mkLambdaFVars #[y, hy] (← mkAppM ``Acc.inv #[acc, hy])
      let b ← mkAppM ``stuckOrZero #[← mkAppM ``Acc.intro #[x, inv]]
      let zero := Expr.const ``Nat.zero []
      let goal ← mkEq b zero
      let value := Expr.letE `h₁ (← mkEq a b) (← mkEqRefl a) (← mkEqRefl b) true
      let xs := #[T, R, x, acc]
      return .thmDecl { name := `L4LEq.halves, levelParams := [],
                        type := ← mkForallFVars xs goal, value := ← mkLambdaFVars xs value }
  let d ← okThm
  unless (Lean4Lean.addDecl env d).toBool do throwError "A = B followed by B = 0 was rejected"
  unless nativeAccepts env d do throwError "the native kernel rejected A = B followed by B = 0"

/-! ### Random questions: the answers of Lean's kernel, whatever was asked before

The sections above test chosen examples. This one generates its questions. `T` is a small language
of closed terms of type `Nat` over the constants of `setup`: applications of the axiom `P`,
beta-redexes, projections of pairs written both as `fst (x, y)` and as `(x, y).1`, the lazily
compared `fst (V h)` and `fst (W h)`, and leaves from three families of constants. Within a family
the leaves are equal in the theory, but the type checker does not find every such equality:
`stuck`, `unstuck` and `0` are the `Acc` example of the previous section.

`mutate` turns a term into a related one, mostly by replacing leaves with others of their family
and by adding or removing redexes, occasionally by breaking the term. A chain of three related
terms `t₀`, `t₁`, `t₂` (`genChain`) then gives two questions that are often accepted, `t₀ =?= t₁`
and `t₁ =?= t₂`, and a third, `t₀ =?= t₂`, that follows from them by transitivity, which is where
a cache that closes its entries under transitivity answers differently from one that does not.

Three properties, with fixed seeds, so the test is deterministic:

1. every single question gets the verdict of Lean's kernel;
2. a declaration that first proves the accepted questions of a chain and then needs the third gets
   the verdict of Lean's kernel, and the verdict that the third question gets on its own;
3. `isDefEq` gives a question the same answer in a fresh state, in a state that has answered the
   questions before it, and in a state that has answered all of them. -/

/-- Closed terms of type `Nat` over the constants of `setup`. -/
private inductive T where
  /-- `a`, `b`, `z`, `L h₀`, `L h₁` (all `z`); `c`, `z'` (both `z'`); `stuck`, `unstuck`, `0`. -/
  | leaf (i : Nat)
  /-- `P x y` -/
  | p (x y : T)
  /-- `(fun n => n) x` -/
  | beta (x : T)
  /-- `fst (x, y)` -/
  | fstPair (x y : T)
  /-- `(x, y).1` -/
  | projPair (x y : T)
  /-- `fst (V hᵢ)`, or `fst (W hᵢ)` if `w` -/
  | fstV (w : Bool) (i : Nat)
  deriving Inhabited, BEq

private def T.toString : T → String
  | .leaf i => #["a", "b", "z", "L h₀", "L h₁", "c", "z'", "stuck", "unstuck", "0"][i]!
  | .p x y => s!"P ({x.toString}) ({y.toString})"
  | .beta x => s!"(fun n => n) ({x.toString})"
  | .fstPair x y => s!"fst ({x.toString}, {y.toString})"
  | .projPair x y => s!"({x.toString}, {y.toString}).1"
  | .fstV w i => s!"fst ({if w then "W" else "V"} h{i})"

private instance : ToString T := ⟨T.toString⟩

private def T.toExpr : T → Expr
  | .leaf 0 => c `L4LEq.a | .leaf 1 => c `L4LEq.b | .leaf 2 => c `L4LEq.z
  | .leaf 3 => .app (c `L4LEq.L) (c `L4LEq.h₀) | .leaf 4 => .app (c `L4LEq.L) (c `L4LEq.h₁)
  | .leaf 5 => c `L4LEq.c | .leaf 6 => c `L4LEq.z'
  | .leaf 7 => c `L4LEq.stuck | .leaf 8 => c `L4LEq.unstuck
  | .leaf _ => .const ``Nat.zero []
  | .p x y => mkApp2 (c `L4LEq.P) x.toExpr y.toExpr
  | .beta x => .app (.lam `n nat (.bvar 0) .default) x.toExpr
  | .fstPair x y => .app (c `L4LEq.fst) (pair x.toExpr y.toExpr)
  | .projPair x y => .proj ``Prod 0 (pair x.toExpr y.toExpr)
  | .fstV w i =>
    .app (c `L4LEq.fst) <| .app (c (if w then `L4LEq.W else `L4LEq.V)) <|
      c #[`L4LEq.h₀, `L4LEq.h₁, `L4LEq.h₂][i % 3]!

private abbrev Rand := StateM StdGen

/-- A number below `n`. -/
private def rnd (n : Nat) : Rand Nat := modifyGet fun g => randNat g 0 (n - 1)

/-- Half of the leaves come from the family of `stuck`. -/
private def genLeaf : Rand T := do
  if (← rnd 2) == 0 then return .leaf (7 + (← rnd 3)) else return .leaf (← rnd 10)

private def genT : Nat → Rand T
  | 0 => genLeaf
  | d + 1 => do
    match ← rnd 10 with
    | 0 | 1 | 2 => genLeaf
    | 3 | 4 => return .p (← genT d) (← genT d)
    | 5 => return .beta (← genT d)
    | 6 => return .fstPair (← genT d) (← genT d)
    | 7 => return .projPair (← genT d) (← genT d)
    | _ => return .fstV ((← rnd 5) == 0) (← rnd 3)

/-- Sometimes puts a redex around `t`. -/
private def wrapSome (t : T) : Rand T := do
  match ← rnd 8 with
  | 0 => return .beta t
  | 1 => return .fstPair t (.leaf 5)
  | _ => return t

/-- A term related to the given one: usually equal to it in the theory, sometimes not. -/
private def mutate : T → Rand T
  | .leaf i => do
    let (start, size) := if i ≤ 4 then (0, 5) else if i ≤ 6 then (5, 2) else (7, 3)
    match ← rnd 10 with
    | 0 | 1 => wrapSome (.leaf i)
    | 8 | 9 => wrapSome (.leaf (← rnd 10))
    | _ => wrapSome (.leaf (start + (← rnd size)))
  | .p x y => do wrapSome (.p (← mutate x) (← mutate y))
  | .beta x => do if (← rnd 3) == 0 then mutate x else return .beta (← mutate x)
  | .fstPair x y => do if (← rnd 3) == 0 then mutate x else return .fstPair (← mutate x) y
  | .projPair x y => do if (← rnd 3) == 0 then mutate x else return .projPair (← mutate x) y
  | .fstV w _ => do return .fstV (if (← rnd 8) == 0 then !w else w) (← rnd 3)

private def T.mapLeaf (f : Nat → Nat) : T → T
  | .leaf i => .leaf (f i)
  | .p x y => .p (x.mapLeaf f) (y.mapLeaf f)
  | .beta x => .beta (x.mapLeaf f)
  | .fstPair x y => .fstPair (x.mapLeaf f) (y.mapLeaf f)
  | .projPair x y => .projPair (x.mapLeaf f) (y.mapLeaf f)
  | t => t

/-- Three related terms. Half of the time `t₀`, `mutate t₀`, `mutate (mutate t₀)`. The other half
walks the family of `stuck` in step: one term with `stuck` at every leaf of that family, then
`unstuck`, then `0`, so that both links hold by one step each and their composition is the
equality the type checker cannot find. -/
private def genChain : Rand (T × T × T) := do
  let t ← genT 3
  if (← rnd 2) == 0 then
    let walk (j : Nat) : T := t.mapLeaf fun i => if i ≥ 7 then j else i
    return (← wrapSome (walk 7), ← wrapSome (walk 8), ← wrapSome (walk 9))
  else
    let t₁ ← mutate t
    return (t, t₁, ← mutate t₁)

private def mkEqNat (t s : T) : Expr := mkApp3 (.const ``Eq [1]) nat t.toExpr s.toExpr
private def mkRefl (t : T) : Expr := mkApp2 (.const ``Eq.refl [1]) nat t.toExpr

/-- `theorem _ : t = s := let h : t₁ = s₁ := rfl; …; @id (t = s) rfl`, with one `let` for each
premise. -/
private def chainThm (premises : List (T × T)) (t s : T) : Declaration :=
  let goal := mkEqNat t s
  let body := mkApp2 (.const ``id [.zero]) goal (mkRefl t)
  .thmDecl {
    name := `L4LEq.chain, levelParams := [], type := goal
    value := premises.foldr (fun (t, s) v => .letE `h (mkEqNat t s) (mkRefl t) v true) body }

run_meta
  let env ← setup (← getEnv).toKernelEnv
  let l4l (d : Declaration) : Bool := (Lean4Lean.addDecl env d).toBool
  -- 1. single questions
  let mut g := mkStdGen 2026
  let mut yes := 0
  let mut no := 0
  for _ in [0:600] do
    let ((t₀, t₁, t₂), g') := genChain.run g
    g := g'
    for (t, s) in [(t₀, t₁), (t₁, t₂), (t₀, t₂), (t₂, t₀)] do
      let d := chainThm [] t s
      let verdict := l4l d
      unless verdict == nativeAccepts env d do
        throwError "{t} =?= {s}: lean4lean says {verdict}, Lean's kernel says {!verdict}"
      if verdict then yes := yes + 1 else no := no + 1
  -- with this seed: 1 717 accepted, 683 rejected
  unless yes ≥ 300 && no ≥ 300 do
    throwError "the random questions are lopsided: {yes} accepted, {no} rejected"
  -- 2. chains inside one declaration
  let mut gaps := 0
  for _ in [0:1500] do
    let ((t₀, t₁, t₂), g') := genChain.run g
    let (shape, g') := (rnd 4).run g'
    g := g'
    -- the premises are the links of the chain that are accepted on their own
    let premises := [(t₀, t₁), (t₁, t₂)].filter fun (t, s) => nativeAccepts env (chainThm [] t s)
    let (t, s) := match shape with
      | 0 => (t₀, t₂) | 1 => (t₂, t₀) | 2 => (T.beta t₀, t₂) | _ => (t₀, T.beta t₂)
    let alone := l4l (chainThm [] t s)
    let after := l4l (chainThm premises t s)
    let what := s!"{t} =?= {s} after {premises}"
    unless after == nativeAccepts env (chainThm premises t s) do
      throwError "{what}: lean4lean says {after}, Lean's kernel says {!after}"
    unless after == alone do
      throwError "{what}: {after}, but {alone} without the premises"
    if premises.length == 2 && !alone then gaps := gaps + 1
  -- the case the test is about has to occur: both links accepted, their composition refuted
  -- (388 of the 1 500 with this seed)
  unless gaps ≥ 50 do
    throwError "only {gaps} chains had two accepted links and a refuted composition"

run_meta
  let env ← setup (← getEnv).toKernelEnv
  -- 3. `isDefEq` in a fresh state, after the questions before it, and after all of them
  let mut g := mkStdGen 14806
  for round in [0:60] do
    let mut qs : Array (T × T) := #[]
    for _ in [0:8] do
      let ((t₀, t₁, t₂), g') := genChain.run g
      g := g'
      qs := qs ++ #[(t₀, t₁), (t₁, t₂), (t₀, t₂), (t₂, t₀), (.beta t₀, t₂), (t₀, .beta t₂)]
    let fresh ← qs.mapM fun (t, s) => return (← countedIsDefEq env t.toExpr s.toExpr).1
    let (forward, backward) ← runCounting env do
      let forward ← qs.mapM fun (t, s) => Inner.isDefEq t.toExpr s.toExpr
      let backward ← qs.reverse.mapM fun (t, s) => Inner.isDefEq t.toExpr s.toExpr
      return (forward, backward.reverse)
    for i in [0:qs.size] do
      let (t, s) := qs[i]!
      unless forward[i]! == fresh[i]! do
        throwError "round {round}: {t} =?= {s} is {fresh[i]!} in a fresh state and \
          {forward[i]!} after the {i} questions before it"
      unless backward[i]! == fresh[i]! do
        throwError "round {round}: {t} =?= {s} is {fresh[i]!} in a fresh state and \
          {backward[i]!} once every question of the round has been answered"

end Lean4Lean.Tests.DefEqCache
