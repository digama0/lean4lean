import Lean.Declaration

namespace Lean4Lean
open Lean

/--
Pointer equality is not a safe function, but the kernel uses it anyway for some fast paths.
We cannot use `withPtrEq` because it is not a mere optimization before a true equality test -
the kernel actually has different behavior (will reject some inputs that it would not otherwise)
if identical objects spontaneously get different addresses.

We use this function to try to isolate uses of pointer equality in the kernel,
and type-restrict it to avoid thorny questions about equality of closures or the like.
-/
opaque ptrEqExpr (a b : Expr) : Bool := unsafe ptrAddrUnsafe a == ptrAddrUnsafe b

axiom ptrEqExpr_eq : ptrEqExpr a b → a = b

/-- See `ptrEqExpr`. -/
opaque ptrEqConstantInfo (a b : ConstantInfo) : Bool := unsafe ptrAddrUnsafe a == ptrAddrUnsafe b

axiom ptrEqConstantInfo_eq : ptrEqConstantInfo a b → a = b
