import Lean4Lean.Verify.Inductive.Primitive.Lowering

/-!
# The checker context of the primitive branch

The `AddInductive.Context` with which the executable runs a recognized `Bool` or `Nat`
declaration.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The exact checker context selected by the executable's primitive branch. -/
def primitiveAddInductiveContext (env : Environment) (lparams : List Name)
    (isUnsafe : Bool) (fuel : FuelConfig) : AddInductive.Context :=
  { env := env, lparams := lparams,
    safety := if isUnsafe then .unsafe else .safe,
    allowPrimitive := true, fuel := fuel }


end VerifyInductive
end Lean4Lean
