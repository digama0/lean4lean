import Lean4Lean.Verify.TypeChecker.FrameDefEq

/-!
# Frame lemma for the core checker

Every function of the executable core checker preserves the ghost restriction (`FrameDefs.lean`):
a successful run in a local context extended by ghost declarations is the identical run in the
context without them, with ghost-free result and final state. The `Inner` functions are proved to
preserve it for methods that preserve it in `FrameInfer.lean`, `FrameWHNF.lean` and
`FrameDefEq.lean` (on the combinators of `FrameBasic.lean` and the expression lemmas of
`FrameExpr.lean`); here the fuel fixpoint
`Methods.withFuel` preserves it by induction on the fuel (`Methods.withFuel_locality`, the
public locality theorem), and the public `M` entry points follow.
-/

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception
open Kernel

variable {G : FVarId → Prop}

theorem Methods.withFuel_locality (G : FVarId → Prop) :
    ∀ n, (Methods.withFuel n).PreservesGhostRestriction G
  | 0 => {
      isDefEqCore := fun _ _ _ _ => .throw
      whnfCore := fun _ _ _ => .throw
      whnf := fun _ _ => .throw
      inferType := fun _ _ _ => .throw }
  | n + 1 =>
    have ih := Methods.withFuel_locality G n
    { isDefEqCore := fun _ _ ht hs => Inner.isDefEqCore'.framed ht hs ih
      whnfCore := fun _ cheapProj he => Inner.whnfCore'.framed cheapProj he ih
      whnf := fun _ he => Inner.whnf'.framed he ih
      inferType := fun _ inferOnly he => Inner.inferType'.framed inferOnly he ih }

end Lean4Lean.TypeChecker
