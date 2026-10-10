import Lean4Lean.TypeChecker

/-!
Unit-like definitional equality (`isDefEqUnitLike`) and K-like recursor reduction
(`toCtorWhenK`) compared with the kernel's `is_def_eq_unit_like` and `to_cnstr_when_K`, on
free variables of unit-like and K-like types. As in the kernel, neither checks the arity of the
type's spine: a well-typed type supplies exactly the inductive's parameters (and indices).
-/

namespace Lean4Lean.Tests.UnitLikeK

open Lean Meta Lean4Lean TypeChecker

structure Unitish (alpha : Type) : Type where

private def defeqL (t s : Expr) : MetaM Bool := do
  match TypeChecker.M.run (← getEnv).toKernelEnv .safe (← getLCtx) [] {}
      (TypeChecker.isDefEq t s) with
  | .ok r => pure r
  | .error ex => throwError "lean4lean isDefEq failed: {← (ex.toMessageData {}).toString}"

private def defeqK (t s : Expr) : MetaM Bool := do
  match Kernel.isDefEq (← getEnv) (← getLCtx) t s with
  | .ok r => pure r
  | .error ex => throwError "kernel isDefEq failed: {← (ex.toMessageData {}).toString}"

private def whnfL (e : Expr) : MetaM Expr := do
  match TypeChecker.M.run (← getEnv).toKernelEnv .safe (← getLCtx) [] {}
      (TypeChecker.whnf e) with
  | .ok r => pure r
  | .error ex => throwError "lean4lean whnf failed: {← (ex.toMessageData {}).toString}"

private def whnfK (e : Expr) : MetaM Expr := do
  match Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok r => pure r
  | .error ex => throwError "kernel whnf failed: {← (ex.toMessageData {}).toString}"

private def compareDefEq (label : String) (t s : Expr) (expected : Bool) : MetaM Unit := do
  let l ← defeqL t s
  let k ← defeqK t s
  unless l == k do throwError "{label}: lean4lean {l} but kernel {k}"
  unless l == expected do throwError "{label}: got {l}, expected {expected}"

private def compareWhnf (label : String) (e : Expr) (expected : Option Expr) : MetaM Unit := do
  let l ← whnfL e
  let k ← whnfK e
  unless l == k do throwError "{label}: lean4lean {l} but kernel {k}"
  if let some x := expected then
    unless l == x do throwError "{label}: reduced to {l}, expected {x}"

run_meta do
  let natT := mkConst ``Nat
  -- unit-like: a parametric structure without fields, and `PUnit`
  let ut := mkApp (mkConst ``Unitish) natT
  withLocalDeclD `x ut fun x => withLocalDeclD `y ut fun y => do
    compareDefEq "Unitish" x y true
  let pu := mkConst ``PUnit [Level.one]
  withLocalDeclD `x pu fun x => withLocalDeclD `y pu fun y => do
    compareDefEq "PUnit" x y true
  -- not unit-like: two constructors
  withLocalDeclD `x (mkConst ``Bool) fun x => withLocalDeclD `y (mkConst ``Bool) fun y => do
    compareDefEq "Bool" x y false
  -- K-like reduction of `Eq.rec` on a free proof of `a = a`
  withLocalDeclD `a natT fun a => withLocalDeclD `b natT fun b => do
    let motive := mkLambda `b' .default natT <|
      mkLambda `h .default (mkApp3 (mkConst ``Eq [Level.one]) natT a (.bvar 0)) natT
    let five := mkRawNatLit 5
    withLocalDeclD `h (mkApp3 (mkConst ``Eq [Level.one]) natT a a) fun h => do
      let e := mkAppN (mkConst ``Eq.rec [Level.one, Level.one]) #[natT, a, motive, five, a, h]
      compareWhnf "Eq.rec on a = a" e (some five)
    -- indices that are not definitionally equal: no reduction
    withLocalDeclD `h (mkApp3 (mkConst ``Eq [Level.one]) natT a b) fun h => do
      let e := mkAppN (mkConst ``Eq.rec [Level.one, Level.one]) #[natT, a, motive, five, b, h]
      compareWhnf "Eq.rec on a = b" e none

end Lean4Lean.Tests.UnitLikeK
