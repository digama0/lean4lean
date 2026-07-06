import Lean.Data.Json.FromToJson

namespace Lean4Lean

/--
Bounds for the various fixed-fuel loops inside the kernel.

Every field is a positive `Nat`; on exhaustion the corresponding loop throws
`.deterministicTimeout` (whnf-family) or `.deepRecursion` (structural /
mutual-recursion loops).

Defaults are set so mathlib passes.  The C++ Lean kernel has no analog for any
of these bounds (its whnf/lazy-delta loops are `while (true)` and its
mutual-recursion depth is bounded only by the native stack); the counters exist
in lean4lean purely as termination witnesses for the Lean-level proofs and as a
defensive check against runaway reductions.
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
  recDepth    : Nat := 10000
  /-- Shared fuel for the structural loops in `Inductive/Add.lean`. -/
  inductiveFuel : Nat := 1000
  deriving Repr, Inhabited, Lean.FromJson, Lean.ToJson
