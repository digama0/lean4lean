import Lean4Lean.Environment

/-!
Regression test for the free variable check on declaration *values*.

`check_no_metavar_no_fvar` is called on the value in three places in the C++ kernel:
`add_definition` (safe branch), `add_theorem`, and -- since leanprover/lean4#14498 --
`add_opaque`. lean4lean had none of them.

The first two were removed deliberately, on the grounds that a free variable in the value
cannot survive type checking anyway. That argument is wrong. It holds only while inference
always consults the local context, and inference also answers from its cache: since the
type and then the value are checked by the *same* `TypeChecker.State` -- exactly as C++
shares one `type_checker` -- a declaration whose type is inferred by pushing a free
variable into the local context leaves that variable's type in `inferTypeI`. The value can
then name the variable, inference answers from the cache instead of the (already popped)
local context, and the declaration is accepted. With a type that beta-reduces to `False`
this proves `False` (leanprover/lean4#14484).

Half of that argument is true, and that is what made it plausible: without these checks an
fvar that was never primed into the cache is still rejected, by inference, as `unknown free
variable`. Only the primed one slips through. Once the checks are restored they run before
inference, so both are rejected as `declaration has free variables` and the two cases are
no longer distinguishable from inside the test -- the assertion below pins the rejection
message so that a rejection coming from some *other* path is not silently accepted as
success.

The leaked variable is `_kernel_fresh.2` because `TypeChecker.State.ngen` uses that prefix
and starts at that index; if either changes, these declarations stop exercising the cache
path and only pin that some free variable is rejected, which was never in doubt.

The declarations are built by hand rather than elaborated, so that the environment does
not already contain them and only the kernel path is exercised.
-/

namespace Lean4Lean.Tests.DeclFVar

open Lean

/-- `(fun _ : False → False => False) (fun h : False => h)`.

This beta-reduces to `False`, so it is a legitimate type, but inferring it pushes
`_kernel_fresh.1 : False → False` and `_kernel_fresh.2 : False` through the local context,
leaving them in the inference cache. -/
def cachePrimingType : Expr :=
  let falseE := mkConst ``False
  let falseToFalse := Expr.forallE `h falseE falseE .default
  let identity := Expr.lam `h falseE (.bvar 0) .default
  .app (.lam `_ falseToFalse falseE .default) identity

/-- The value that only the inference cache still knows about. -/
def leakedFVar : Expr := .fvar { name := .num `_kernel_fresh 2 }

def thmDecl (name : Name) (value : Expr) : Declaration :=
  .thmDecl { name, levelParams := [], type := cachePrimingType, value }

def defnDecl (name : Name) (value : Expr) : Declaration :=
  .defnDecl { name, levelParams := [], type := cachePrimingType, value
              hints := .abbrev, safety := .safe }

def opaqueDecl (name : Name) (value : Expr) : Declaration :=
  .opaqueDecl { name, levelParams := [], type := cachePrimingType, value, isUnsafe := false }

/-- Closed counterparts, so that a blanket rejection cannot pass this test. -/
def goodThm : Declaration :=
  .thmDecl { name := `GoodThm, levelParams := [], type := mkConst ``True,
             value := mkConst ``True.intro }
def goodDefn : Declaration :=
  .defnDecl { name := `GoodDefn, levelParams := [], type := mkConst ``Nat,
              value := mkRawNatLit 0, hints := .abbrev, safety := .safe }
def goodOpaque : Declaration :=
  .opaqueDecl { name := `GoodOpaque, levelParams := [], type := mkConst ``Nat,
                value := mkRawNatLit 0, isUnsafe := false }

run_meta do
  let kenv := (← getEnv).toKernelEnv

  let errorOf (decl : Declaration) : MetaM (Option String) := do
    match Lean4Lean.addDecl kenv decl with
    | .ok _ => return none
    | .error e => return some (← (e.toMessageData {}).toString)
  let mentions (pat : String) (s : String) : Bool := (s.splitOn pat).length > 1

  for (kind, mk) in [("theorem", thmDecl), ("safe definition", defnDecl), ("opaque", opaqueDecl)] do
    -- The value that the inference cache leaks must be rejected *by the fvar check*.
    match ← errorOf (mk `Bad leakedFVar) with
    | none => throwError "{kind} value containing a leaked free variable was accepted"
    | some msg =>
      unless mentions "declaration has free variables" msg do
        throwError "{kind} leaked free variable was rejected, but not by the free variable \
          check, so this test no longer pins the cache path: {msg}"

  -- ... and closed values must still go through.
  for (kind, decl) in [("theorem", goodThm), ("safe definition", goodDefn),
                       ("opaque", goodOpaque)] do
    if let some msg ← errorOf decl then
      throwError "closed {kind} was rejected: {msg}"

end Lean4Lean.Tests.DeclFVar
