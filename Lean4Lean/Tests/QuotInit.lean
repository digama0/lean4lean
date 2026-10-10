import Lean4Lean.Environment
import Lean4Lean.Theory.Meta
import Lean4Lean.Verify.Environment

/-! Quotient initialization.

The executable's `init_quot`, run after adding `Init.Prelude`'s `Eq` to an
empty environment, installs `Quot`, `Quot.mk`, `Quot.lift` and `Quot.ind`
as Lean's kernel does, exactly (binder names and binder annotations
included; in particular the major premise of `Quot.ind` is an explicit
binder, see `divergences.md`), with the closed types `AddQuotAux.T1'` and
siblings that `Environment.addQuot_eq` (`Lean4Lean/Verify/Environment/Quot.lean`)
computes, and these translate to the abstract constants `quotConst`,
`quotMkConst`, `quotLiftConst` and `quotIndConst` installed by `VEnv.addQuot`.
A second `init_quot` is a no-op. -/

namespace Lean4Lean.Tests.QuotInit

open Lean Meta

deriving instance BEq for QuotKind
deriving instance BEq for VLevel
deriving instance BEq for VExpr

def check (cond : Bool) (msg : String) : MetaM Unit :=
  unless cond do throwError msg

run_meta do
  let env ← getEnv
  let some (.inductInfo I) := env.find? ``Eq | throwError "no Eq"
  let some (.ctorInfo C) := env.find? ``Eq.refl | throwError "no Eq.refl"
  let refl : Constructor := { name := ``Eq.refl, type := C.type }
  let eqDecl := Declaration.inductDecl I.levelParams I.numParams
    [{ name := ``Eq, type := I.type, ctors := [refl] }] I.isUnsafe
  let empty ← mkEmptyEnvironment
  let kenv ← match Lean4Lean.addDecl empty.toKernelEnv eqDecl (check := true) with
    | .error e => throwError "Lean4Lean.addDecl rejected Eq: {e.toMessageData {}}"
    | .ok kenv => pure kenv
  check (!kenv.quotInit) "quotient module unexpectedly initialized"
  let kenv ← match Lean4Lean.addDecl kenv .quotDecl (check := true) with
    | .error e => throwError "Lean4Lean.addDecl rejected init_quot: {e.toMessageData {}}"
    | .ok kenv => pure kenv
  check kenv.quotInit "init_quot did not set quotInit"
  let expected : List (Name × Expr × VConstant) := [
    (``Quot, AddQuotAux.T1', quotConst),
    (``Quot.mk, AddQuotAux.T2', quotMkConst),
    (``Quot.lift, AddQuotAux.T3', quotLiftConst),
    (``Quot.ind, AddQuotAux.T4', quotIndConst)]
  for (n, closed, abs) in expected do
    let some (.quotInfo ci) := kenv.find? n | throwError "Lean4Lean did not install {n}"
    let some (.quotInfo ci₀) := env.find? n | throwError "missing {n}"
    -- Exact comparison, binder info included.
    check (ci.levelParams == ci₀.levelParams && ci.type.equal ci₀.type && ci.kind == ci₀.kind)
      s!"{n}: Lean4Lean and Lean's kernel disagree"
    check (ci.type.equal closed) s!"{n}: type is not the closed form of `Environment.addQuot_eq`"
    let t ← Lean4Lean.Meta.ofExpr ci.levelParams {} ci.type
    check (t == abs.type && ci.levelParams.length == abs.uvars)
      s!"{n}: translation is not the abstract constant"
  -- A second `init_quot` is a no-op.
  match Lean4Lean.addDecl kenv .quotDecl (check := true) with
  | .error e => throwError "repeated init_quot rejected: {e.toMessageData {}}"
  | .ok kenv' => check (kenv'.find? ``Quot.lift |>.isSome) "repeated init_quot lost Quot.lift"

end Lean4Lean.Tests.QuotInit
