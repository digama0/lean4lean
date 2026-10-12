import Lean4Lean.TypeChecker

/-!
Projection reduction (`reduceProjCore`) compared with the kernel's `reduce_proj`: on well-typed
projections of constructor applications, `whnf` of lean4lean and of the kernel agree. The
constructor's inductive is checked against the projected structure, and the selected argument is
read off the constructor spine, as in `type_checker::reduce_proj_core`.
-/

namespace Lean4Lean.Tests.ProjectionReduction

open Lean Lean4Lean TypeChecker

structure Pair3 (alpha : Type u) (beta : Type v) where
  first : alpha
  second : beta
  flag : Bool

private def runL (env : Kernel.Environment) (e : Expr) : MetaM Expr := do
  match TypeChecker.M.run env .safe {} [] {} (TypeChecker.whnf e) with
  | .ok r => pure r
  | .error ex => throwError "lean4lean whnf failed: {← (ex.toMessageData {}).toString}"

private def runK (env : Environment) (e : Expr) : MetaM Expr := do
  match Kernel.whnf env {} e with
  | .ok r => pure r
  | .error ex => throwError "kernel whnf failed: {← (ex.toMessageData {}).toString}"

private def compare (label : String) (e expected : Expr) : MetaM Unit := do
  let l ← runL (← getEnv).toKernelEnv e
  let k ← runK (← getEnv) e
  unless l == k do throwError "{label}: lean4lean {l} but kernel {k}"
  unless l == expected do throwError "{label}: reduced to {l}, expected {expected}"

run_meta do
  let u := Level.zero
  let natT := mkConst ``Nat
  let boolT := mkConst ``Bool
  let mk := mkAppN (mkConst ``Pair3.mk [u, u])
    #[natT, boolT, mkRawNatLit 3, mkConst ``true, mkConst ``false]
  -- each field of a saturated constructor application
  compare "field 0" (.proj ``Pair3 0 mk) (mkRawNatLit 3)
  compare "field 1" (.proj ``Pair3 1 mk) (mkConst ``true)
  compare "field 2" (.proj ``Pair3 2 mk) (mkConst ``false)
  -- the structure argument is reduced to a constructor application first
  let wrapped := mkApp (.lam `x natT mk .default) (mkRawNatLit 7)
  compare "beta major" (.proj ``Pair3 0 wrapped) (mkRawNatLit 3)
  -- a function-valued field, projected and applied
  let fnT := mkForall `n .default natT natT
  let succ := mkConst ``Nat.succ
  let mkFn := mkAppN (mkConst ``Pair3.mk [u, u])
    #[fnT, boolT, succ, mkConst ``true, mkConst ``true]
  compare "function field" (mkApp (.proj ``Pair3 0 mkFn) (mkRawNatLit 1)) (mkRawNatLit 2)
  -- structure-typed projections of a primitive literal (`String.mk`)
  let lit : Expr := .lit (.strVal "ab")
  let k ← runK (← getEnv) (.proj ``String 0 lit)
  let l ← runL (← getEnv).toKernelEnv (.proj ``String 0 lit)
  unless l == k do throwError "string literal: lean4lean {l} but kernel {k}"

end Lean4Lean.Tests.ProjectionReduction
