import Lean4Lean.Environment

/-!
Regression test for the opaque-value free variable check added for
leanprover/lean4#14498.

`add_opaque` type checked the value but, unlike `add_definition` and `add_theorem`, never
checked it to be free of metavariables and free variables. Since the same type checker --
and so the same inference cache -- is used for the type and then the value, a declaration
whose *type* is inferred by pushing a free variable into the local context leaves that
variable's type in the cache. The value can then refer to the variable by name: inference
answers from the cache instead of the (already popped) local context, and the declaration
is accepted. With a type that beta-reduces to `False` this proves `False`
(leanprover/lean4#14484).

lean4lean shares `TypeChecker.State` across the whole `M.run` in `addOpaque` exactly as
C++ shares the `type_checker`, so it inherited the bug verbatim, down to the name of the
leaked variable: `_kernel_fresh.2` here as in the lean4 test for this issue.

The declarations are built by hand rather than elaborated, so that the environment does
not already contain them and only the kernel path is exercised.
-/

namespace Lean4Lean.Tests.OpaqueFVar

open Lean

/-- `(fun _ : False → False => False) (fun h : False => h)`.

This beta-reduces to `False`, so it is a legitimate type for an opaque constant, but
inferring it pushes `_kernel_fresh.1 : False → False` and `_kernel_fresh.2 : False` through
the local context, leaving them in the inference cache. -/
def cachePrimingType : Expr :=
  let falseE := mkConst ``False
  let falseToFalse := Expr.forallE `h falseE falseE .default
  let identity := Expr.lam `h falseE (.bvar 0) .default
  .app (.lam `_ falseToFalse falseE .default) identity

/-- `opaque Good0 : Nat := 0`, with a closed value. -/
def goodDecl : Declaration :=
  .opaqueDecl {
    name := `Good0
    levelParams := []
    type := mkConst ``Nat
    value := mkRawNatLit 0
    isUnsafe := false }

/-- `opaque Bad0 : False := _kernel_fresh.2`, referring to a variable that only the
inference cache still knows about. -/
def badDecl : Declaration :=
  .opaqueDecl {
    name := `Bad0
    levelParams := []
    type := cachePrimingType
    value := .fvar { name := .num `_kernel_fresh 2 }
    isUnsafe := false }

run_meta do
  let kenv := (← getEnv).toKernelEnv

  -- A closed opaque value must still be accepted.
  match Lean4Lean.addDecl kenv goodDecl with
  | .ok _ => pure ()
  | .error e =>
    throwError "closed opaque was rejected: {← (e.toMessageData {}).toString}"

  -- ... and a value that escapes into the inference cache must be caught. Before the
  -- `checkNoMVarNoFVar` call in `addOpaque` this succeeded, giving `Bad0 : False`.
  match Lean4Lean.addDecl kenv badDecl with
  | .ok _ => throwError "opaque value containing a free variable was accepted"
  | .error _ => pure ()

end Lean4Lean.Tests.OpaqueFVar
