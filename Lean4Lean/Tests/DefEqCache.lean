import Lean4Lean.Environment

/-!
Tests for the cache of successful `isDefEq` queries (`State.success`), a set of pairs as in Lean's
kernel since leanprover/lean4#14806.

* The set on its own: a pair is seen in both orders and stored once, and the set is not closed
  under transitivity, reflexivity or congruence.
* A decided pair is answered at the entry of `isDefEqCore'`. The union-find was consulted behind a
  hash test there, so a recorded equality was usually not seen and the pair was decided again from
  scratch, which is exponential on a term shared as a DAG (`tower`).
* An exact repeat of a decided pair reduces nothing again (a miniature of
  `New.Variety.tiltTheory`, lsernau/grh-lean@72fead10).
* `isDefEq` is sound but incomplete, hence not transitive. The cache does not answer from the
  transitive closure of earlier successes (the `Acc` example), which is what Lean's kernel does.

Work is measured in calls of `isDefEqCore'`, so nothing depends on the speed of the machine.
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
  check "the key is the whole term, universe levels included" (!seen st (.const `a [.zero]) b)
  let st ← record st b a
  check "a pair is stored once, whichever way round it is recorded" (st.success.size == 1)
  -- the set is not closed under anything
  let st ← record st b e
  check "the second pair is seen" (seen st b e && seen st e b)
  check "no transitivity: a ≡ b and b ≡ e do not give a ≡ e" (!seen st a e && !seen st e a)
  check "no reflexivity" (!seen st a a)
  check "no congruence: a ≡ b does not give f a ≡ f b" (!seen st (.app f a) (.app f b))
  -- Two different terms with the same hash are not ordered by it, so `succeededBefore` has to
  -- look for both orientations. The first two literals that collide serve as the example.
  let mut byHash : Std.HashMap UInt64 Nat := {}
  let mut tie : Option (Nat × Nat) := none
  for i in [0:1000000] do
    let h := (Expr.lit (.natVal i)).hash
    if let some j := byHash[h]? then
      tie := some (j, i)
      break
    byHash := byHash.insert h i
  let some (i, j) := tie | throwError "no two literals below 1000000 have the same hash"
  let m := Expr.lit (.natVal i); let n := Expr.lit (.natVal j)
  check "nothing is known about the colliding pair yet" (!seen st m n && !seen st n m)
  let st ← record st n m
  check "a pair with equal hashes is seen in both orders" (seen st m n && seen st n m)
  check "and only that pair" (!seen st m a && !seen st a n)

/-! ### The test environment and the call counter -/

private def nat : Expr := .const ``Nat []
private def prop : Expr := .sort .zero
private def natPair : Expr := mkApp2 (.const ``Prod [.zero, .zero]) nat nat
private def pair (x y : Expr) : Expr := mkApp4 (.const ``Prod.mk [.zero, .zero]) nat nat x y

/-- `tower P leaf 0 = leaf` and `tower P leaf (n + 1) = P t t` with `t := tower P leaf n`: a term
of `n + 1` distinct subterms and `2ⁿ` leaves. -/
private def tower (P leaf : Expr) : Nat → Expr
  | 0 => leaf
  | n + 1 => let x := tower P leaf n; mkApp2 P x x

/-- Depth of the towers inside `L4LEq.V` and `L4LEq.W`. -/
private def bodyDepth : Nat := 16

/-- Stuck on a proof of `Acc R y` that is not a constructor application, and `0` on
`Acc.intro ..`. -/
private noncomputable def stuckOrZero {T : Type} {R : T → T → Prop} {y : T} (h : Acc R y) :
    Nat :=
  Acc.rec (motive := fun _ _ => Nat) (fun _ _ _ => Nat.zero) h

/-- The current environment plus

    axiom z z' : Nat                     axiom P : Nat → Nat → Nat
    def a := z      def b := z           def c := z'
    axiom Pr : Prop                      axiom h₀ h₁ h₂ : Pr
    def L (_ : Pr) : Nat := z
    @[reducible] def fst (s : Nat × Nat) : Nat := s.1
    def V (h : Pr) : Nat × Nat := (tower P (L h) bodyDepth, z)
    def W (h : Pr) : Nat × Nat := (tower P c bodyDepth, z)
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
generator. No comparison below instantiates a binder, so nothing else uses that index, and its
final value is the number of `isDefEqCore'` calls. -/
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

/-- Runs `x` in `env` with a fresh state and the counting methods. An error of the type checker,
a resource limit included, fails the test: it is never read as "not equal". -/
private def runCounting (env : Kernel.Environment) (x : RecM α) : MetaM α := do
  let (a, _) ← runM <| (x (countingMethods 100000) { env }).run {}
  return a

/-- `Inner.isDefEq t s`, with the number of `isDefEqCore'` calls it made. -/
private def counted (t s : Expr) : RecM (Bool × Nat) := do
  let k := (← get).ngen.idx
  let r ← Inner.isDefEq t s
  return (r, (← get).ngen.idx - k)

/-- `theorem name : t = s := let h : t₁ = s₁ := rfl; …; @id (t = s) rfl`, with one `let` for each
premise. -/
private def eqThm (name : Name) (premises : List (Expr × Expr)) (t s : Expr) : Declaration :=
  let eq (t s : Expr) : Expr := mkApp3 (.const ``Eq [1]) nat t s
  let refl (t : Expr) : Expr := mkApp2 (.const ``Eq.refl [1]) nat t
  .thmDecl {
    name, levelParams := [], type := eq t s
    value := premises.foldr (fun (t, s) v => .letE `h (eq t s) (refl t) v true)
      (mkApp2 (.const ``id [.zero]) (eq t s) (refl t)) }

/-- The verdict of Lean's own kernel on `d`. -/
private def native (env : Kernel.Environment) (d : Declaration) :
    Except Kernel.Exception Kernel.Environment :=
  env.addDeclCore 0 0 d (cancelTk? := none)

/-- Rejected because a type does not match, and not because a resource limit was reached. -/
private def mismatch : Except Kernel.Exception α → Bool
  | .error (.appTypeMismatch ..) | .error (.declTypeMismatch ..) => true
  | _ => false

/-! ### A shared pair is decided once

With `Aₙ := tower P a n`, `Bₙ := tower P b n` and `Cₙ := tower P c n`, the question
`Aₖ₊₁ =?= Bₖ₊₁` poses `Aₖ =?= Bₖ` twice, once per argument of `P`. Neither side reduces (`P` is an
axiom), so only the pair recorded after the first occurrence can answer the second. -/

run_meta
  let env ← setup (← getEnv).toKernelEnv
  let P := c `L4LEq.P
  let A := tower P (c `L4LEq.a); let B := tower P (c `L4LEq.b); let C := tower P (c `L4LEq.c)
  -- `3 n + 1` calls: per level one for `P =?= P` and two for the arguments, the second of which
  -- is answered on entry. Without that it is `3 · 2ⁿ - 2` (196 606 for `n = 16`).
  for n in [1, 4, 16] do
    let (r, calls) ← runCounting env (counted (A n) (B n))
    unless r do throwError "depth {n}: A =?= B was refuted"
    unless calls ≤ 4 * n + 4 do
      throwError "depth {n}: A =?= B took {calls} isDefEqCore' calls, expected at most {4 * n + 4}"
  -- A pair that is not equal stays unequal: the first argument is settled, and recorded, before
  -- the second, which differs in its innermost leaf, is refuted. The mirrored question is asked
  -- in the same state, so nothing recorded on the way may make it succeed.
  for n in [0, 1, 4, 16] do
    let lhs := A (n + 1); let rhs := mkApp2 P (B n) (C n)
    let (r, r') ← runCounting env do return (← counted lhs rhs, ← counted rhs lhs)
    if r.1 then throwError "depth {n}: P A A =?= P B C was accepted"
    if r'.1 then throwError "depth {n}: P B C =?= P A A was accepted after P A A =?= P B C"
    unless r.2 ≤ 16 * n + 32 do
      throwError "depth {n}: refuting P A A =?= P B C took {r.2} isDefEqCore' calls"
  -- The same through `addDecl`, at a depth that only a linear check can reach, with the verdicts
  -- of Lean's kernel.
  let n := 400
  let good := eqThm `L4LEq.good [] (A n) (B n)
  let bad := eqThm `L4LEq.bad [] (A n) (mkApp2 P (B (n - 1)) (C (n - 1)))
  _ ← runM <| Lean4Lean.addDecl env good
  _ ← runM <| native env good
  unless mismatch (Lean4Lean.addDecl env bad) do
    throwError "a theorem identifying two different axioms was not rejected as a type mismatch"
  unless mismatch (native env bad) do
    throwError "Lean's kernel did not reject the invalid theorem as a type mismatch"

/-! ### An exact repeat of a decided pair reduces nothing again

With `X h := fst (V h)`, the question `X h₁ =?= X h₀` is settled lazily: unfold `fst`, leave both
projections `(V h).1` stuck, and compare `V h₁ =?= V h₀` by arguments, which are two proofs of
`Pr`. Three calls, and `V` is never unfolded.

Behind the hash test the union-find did not see this pair when it came back, and deciding it again
was not the same computation. If `(V h₀).1` has been fully reduced in the meantime (`whnf (X h₀)`
does that), the cache hands the second attempt that normal form, so it fully reduces `(V h₁).1` as
well, compares the two bodies (327 679 calls for towers of depth 16), and leaves the unfolded
`(V h₁).1` in `whnfCoreCache`. From then on `X h₁ =?= X h₂` is not three calls either, because
`cheapProj := true` requests are answered from that cache.

With the set of pairs the repeated question is one call. That is all this section tests: the
`whnfCore` cache itself is unchanged, so a pair that is new to the set, such as `X h₁ =?= X h₀`
after `X h₁ =?= X h₂` and `X h₂ =?= X h₀`, is still decided from scratch and can still leave an
unfolded projection behind. -/

run_meta
  let env ← setup (← getEnv).toKernelEnv
  let V (h : Name) : Expr := .app (c `L4LEq.V) (c h)
  let X (h : Name) : Expr := .app (c `L4LEq.fst) (V h)
  let proj (h : Name) : Expr := .proj ``Prod 0 (V h)
  let (first, hasNF₀, again, hasNF₁, third) ← runCounting env do
    let first ← counted (X `L4LEq.h₁) (X `L4LEq.h₀)
    _ ← Inner.whnf (X `L4LEq.h₀)
    let hasNF₀ := (← get).whnfCoreCache.contains (proj `L4LEq.h₀)
    let again ← counted (X `L4LEq.h₁) (X `L4LEq.h₀)
    let hasNF₁ := (← get).whnfCoreCache.contains (proj `L4LEq.h₁)
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
  -- The same shape with a different body is still refuted, also after the equality above, and
  -- refuting it looks into the bodies, which is linear in their depth.
  let Y : Expr := .app (c `L4LEq.fst) (.app (c `L4LEq.W) (c `L4LEq.h₂))
  let (ok, bad₁, bad₂) ← runCounting env do
    return (← counted (X `L4LEq.h₁) (X `L4LEq.h₀), ← counted (X `L4LEq.h₁) Y,
      ← counted Y (X `L4LEq.h₀))
  unless ok.1 do throwError "X h₁ =?= X h₀ was refuted"
  if bad₁.1 || bad₂.1 then throwError "fst (V h) =?= fst (W h) was accepted"
  unless bad₁.2 ≤ 8 * bodyDepth && bad₂.2 ≤ 8 * bodyDepth do
    throwError "refuting fst (V h) =?= fst (W h) took {bad₁.2} and {bad₂.2} isDefEqCore' calls"

/-! ### No answer from the transitive closure

The standard example of the missing transitivity: with `acc : Acc R z` an axiom,

    A := stuckOrZero acc                                             -- `Acc.rec` is stuck
    B := stuckOrZero (Acc.intro z fun _ hy => Acc.inv acc hy)        -- reduces to `0`

`A =?= B` holds by proof irrelevance and `B =?= 0` by reduction, but `A =?= 0` is refuted: nothing
suggests replacing `acc` by another proof.

A union-find that has seen the first two has `A` and `0` in one class. Behind the hash test that
showed in an odd way: `A =?= 0` itself was still refuted, since the entry check stopped at the two
hashes, but `(fun n => n) A =?= 0` was accepted, because the check after the beta step looked at
the classes. With a set of pairs both are refuted after the two premises as well, as in Lean's
kernel. (This is one source of dependence on earlier queries, not the only one: the `whnfCore`
cache is another, here and in Lean's kernel.) -/

run_meta
  let env ← setup (← getEnv).toKernelEnv
  let A := c `L4LEq.stuck; let B := c `L4LEq.unstuck; let zero := Expr.const ``Nat.zero []
  let wrapped := Expr.app (.lam `n nat (.bvar 0) .default) A
  -- each question on its own
  for (what, t, s, expected) in [("A =?= B", A, B, true), ("B =?= 0", B, zero, true),
      ("A =?= 0", A, zero, false), ("0 =?= A", zero, A, false),
      ("(fun n => n) A =?= 0", wrapped, zero, false)] do
    let (r, _) ← runCounting env (counted t s)
    unless r == expected do throwError "{what} on its own: expected {expected}"
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
  -- The same through `addDecl`: one theorem that first proves the premises by `rfl` and then
  -- needs the goal by `rfl`. Each is rejected, as a type mismatch, by lean4lean and Lean's kernel.
  for (goal, lhs) in [("A = 0", A), ("(fun n => n) A = 0", wrapped)] do
    for (after, premises) in [("on its own", []), ("after A = B and B = 0", [(A, B), (B, zero)])] do
      let d := eqThm `L4LEq.trans premises lhs zero
      unless mismatch (Lean4Lean.addDecl env d) do
        throwError "{goal} {after} was not rejected as a type mismatch"
      unless mismatch (native env d) do
        throwError "{goal} {after} was not rejected as a type mismatch by Lean's kernel"
  -- the premises themselves are fine: the same shape with a goal that holds is accepted
  let d := eqThm `L4LEq.halves [(A, B)] B zero
  _ ← runM <| Lean4Lean.addDecl env d
  _ ← runM <| native env d

end Lean4Lean.Tests.DefEqCache
