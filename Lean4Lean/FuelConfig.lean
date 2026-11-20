import Lean.Data.Json.FromToJson

namespace Lean4Lean

/--
Bounds for the various fixed-fuel loops inside the kernel.

Every field is a positive `Nat`; on exhaustion the corresponding loop throws
`.deterministicTimeout` (whnf-family) or `.deepRecursion` (structural /
mutual-recursion loops).

Defaults are set so mathlib passes. Since lean4#13956 the native kernel bounds
its mutually recursive type-checker entry points using `maxRecDepth`.
Lean4lean instead keeps separate, explicit fuel for those calls and for loops
that need structural termination witnesses; these counters also provide a
deterministic defensive check against runaway reductions.
-/
structure FuelConfig where
  /-- `whnf'` unfold-loop, non-eager path (`TypeChecker.lean` whnf'). -/
  whnf        : Nat := 100000
  /-- `whnf'` unfold-loop, `eagerReduce` path. -/
  whnfEager   : Nat := 1000000
  /-- `lazyDeltaReduction.loop`. -/
  lazyDelta   : Nat := 1000
  /-- `etaExpand.loop.loop2`. -/
  etaExpand   : Nat := 1000
  /-- Starting fuel for `Methods.withFuel` (bounds mutual whnf/isDefEq depth). -/
  recDepth    : Nat := 50000
  /-- Shared fuel for the structural loops in `Inductive/Add.lean`. -/
  inductiveFuel : Nat := 1000
  /-- Upper bound, in bytes, on the `Nat` numerals the type checker accepts as literals or
  computes in `reduceNat`; the native kernel's `LEAN_NAT_MAX_SIZE` (lean4#14849), with the
  same 128 MB default. Unlike the other fields this bounds memory rather than steps. -/
  natMaxSize  : Nat := 128 * 1024 * 1024
  deriving Repr, Inhabited, Lean.FromJson, Lean.ToJson
