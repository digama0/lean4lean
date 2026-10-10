import Lean4Lean.Environment

/-!
Executable acceptance regressions for ordinary and mutually recursive
inductives. Declarations are assembled directly so the tests exercise
`Lean4Lean.addDecl`, rather than Lean's host elaborator/kernel.
-/

namespace Lean4Lean.Tests.RecursiveInductive

open Lean

/-- A nonrecursive declaration through the ordinary (non-primitive,
non-nested) installer. -/
def colorDecl : Declaration :=
  .inductDecl [] 0 [{
    name := `L4LColor
    type := .sort 1
    ctors := [{
      name := `L4LColor.red
      type := .const `L4LColor []
    }, {
      name := `L4LColor.blue
      type := .const `L4LColor []
    }]
  }] false

def natLikeDecl : Declaration :=
  .inductDecl [] 0 [{
    name := `L4LNatLike
    type := .sort 1
    ctors := [{
      name := `L4LNatLike.zero
      type := .const `L4LNatLike []
    }, {
      name := `L4LNatLike.succ
      type := .forallE `n (.const `L4LNatLike [])
        (.const `L4LNatLike []) .default
    }]
  }] false

def evenOddDecl : Declaration :=
  .inductDecl [] 0 [{
    name := `L4LEven
    type := .sort 1
    ctors := [{
      name := `L4LEven.zero
      type := .const `L4LEven []
    }, {
      name := `L4LEven.succ
      type := .forallE `n (.const `L4LOdd [])
        (.const `L4LEven []) .default
    }]
  }, {
    name := `L4LOdd
    type := .sort 1
    ctors := [{
      name := `L4LOdd.succ
      type := .forallE `n (.const `L4LEven [])
        (.const `L4LOdd []) .default
    }]
  }] false

/-- A higher-order recursive field opens a call-local binder while recursor
rules are generated.  The reader-local name generator may reuse that binder's
identifier for the minor installed immediately afterwards, so this declaration
regresses the collision that the recorded rule templates must survive. -/
def higherOrderRecursiveDecl : Declaration :=
  .inductDecl [] 0 [{
    name := `L4LHigherOrderTree
    type := .sort 1
    ctors := [{
      name := `L4LHigherOrderTree.branch
      type := .forallE `children
        (.forallE `i (.const ``Nat [])
          (.const `L4LHigherOrderTree []) .default)
        (.const `L4LHigherOrderTree []) .default
    }, {
      name := `L4LHigherOrderTree.leaf
      type := .const `L4LHigherOrderTree []
    }]
  }] false

/-- The prelude's `Bool` declaration, in the shape recognized by the primitive dispatch. -/
def primitiveBoolDecl : Declaration :=
  .inductDecl [] 0 [{
    name := ``Bool
    type := .sort (.succ .zero)
    ctors := [{
      name := ``Bool.false
      type := .const ``Bool []
    }, {
      name := ``Bool.true
      type := .const ``Bool []
    }]
  }] false

private def expectAccepted (label : String) (env : Kernel.Environment)
    (decl : Declaration) : MetaM Unit := do
  match Lean4Lean.addDecl env decl with
  | .ok _ => pure ()
  | .error e =>
    throwError "{label} was rejected: {← (e.toMessageData {}).toString}"

run_meta do
  let env := (← getEnv).toKernelEnv
  expectAccepted "ordinary nonrecursive inductive" env colorDecl
  expectAccepted "ordinary recursive inductive" env natLikeDecl
  expectAccepted "mutually recursive inductive" env evenOddDecl
  expectAccepted "higher-order recursive inductive" env higherOrderRecursiveDecl
  let primitiveEnv := Lean.Kernel.Environment.empty `L4LPrimitiveRegression
  expectAccepted "primitive Bool inductive" primitiveEnv primitiveBoolDecl

end Lean4Lean.Tests.RecursiveInductive
