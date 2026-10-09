import Lean4Lean.Environment
import Lean4Lean.Theory.Meta
import Lean4Lean.Verify.Inductive.Prelude.EqSyntax

/-! Realizability of `VEnv.HasCanonicalEq` for the real `Eq`.

The declaration of `Eq` is rebuilt exactly as `Init.Prelude` submits it (its
level parameters, parameter count, family type and constructor type, read back
from the environment), and added to an empty environment through
`Lean4Lean.addDecl`.  The test checks that

* the submitted declaration has the syntax `PreludeEqShape` describes
  (`nparams = 2`), so `addDecl.preludeEq_hasCanonicalEq` applies to it;
* the executable installs `Eq`, `Eq.refl` and `Eq.rec` exactly as Lean's kernel
  does, and the installed `Eq.rec` satisfies `IsPreludeEqRec` (its type is
  `eqRecTypeExpr`) with the single rule `eqRecRuleRhsExpr`;
* the translations of these expressions (and of the iota rule's left-hand side
  and type) are the terms stored by `VEnv.HasCanonicalEq`. -/

namespace Lean4Lean.Tests.PreludeEq

open Lean Meta

deriving instance BEq for VLevel
deriving instance BEq for VExpr

/-- The names of the leading `∀` binders. -/
def forallNames : Expr → List Name
  | .forallE n _ b _ => n :: forallNames b
  | _ => []

def check (cond : Bool) (msg : String) : MetaM Unit :=
  unless cond do throwError msg

def toV (ls : List Name) (e : Expr) : MetaM VExpr :=
  Lean4Lean.Meta.ofExpr ls {} e

run_meta do
  let env ← getEnv
  let some (.inductInfo I) := env.find? ``Eq | throwError "no Eq"
  let some (.ctorInfo C) := env.find? ``Eq.refl | throwError "no Eq.refl"
  let some (.recInfo R) := env.find? ``Eq.rec | throwError "no Eq.rec"
  -- The declaration as submitted by `Init.Prelude`.
  let refl : Constructor := { name := ``Eq.refl, type := C.type }
  let eqType : InductiveType := { name := ``Eq, type := I.type, ctors := [refl] }
  let types := [eqType]
  let decl := Declaration.inductDecl I.levelParams I.numParams types I.isUnsafe
  -- `PreludeEqShape`.
  let [u] := I.levelParams | throwError "Eq: unexpected level parameters {I.levelParams}"
  check (I.numParams == 2 && I.numIndices == 1 && !I.isUnsafe) "Eq: not 2 params, 1 index"
  let [alpha, lhs, rhs] := forallNames I.type | throwError "Eq: unexpected type"
  check (I.type.equal (VerifyInductive.preludeEqType u alpha lhs rhs))
    "Eq: type is not preludeEqType"
  check (C.levelParams == [u]) "Eq.refl: level parameters differ from Eq's"
  let [reflAlpha, reflValue] := forallNames C.type | throwError "Eq.refl: unexpected type"
  check (C.type.equal (VerifyInductive.preludeEqReflType u reflAlpha reflValue))
    "Eq.refl: type is not preludeEqReflType"
  -- The executable on the real declaration, from an empty environment.
  let empty ← mkEmptyEnvironment
  let kenv ← match Lean4Lean.addDecl empty.toKernelEnv decl (check := true) with
    | .error e => throwError "Lean4Lean.addDecl rejected Eq: {e.toMessageData {}}"
    | .ok kenv => pure kenv
  for n in [``Eq, ``Eq.refl, ``Eq.rec] do
    let some ci := kenv.find? n | throwError "Lean4Lean did not install {n}"
    let some ci₀ := env.find? n | throwError "missing {n}"
    check (ci.levelParams == ci₀.levelParams && ci.type.equal ci₀.type &&
      ci.isUnsafe == ci₀.isUnsafe) s!"{n}: Lean4Lean and Lean's kernel disagree"
  let some (.recInfo r) := kenv.find? ``Eq.rec | throwError "Eq.rec is not a recursor"
  check (r.numParams == R.numParams && r.numIndices == R.numIndices &&
    r.numMotives == R.numMotives && r.numMinors == R.numMinors && r.k == R.k)
    "Eq.rec: metadata differs from Lean's"
  -- `IsPreludeEqRec`.
  let [ru, rv] := r.levelParams | throwError "Eq.rec: unexpected level parameters"
  check (ru != rv && !r.isUnsafe) "Eq.rec: level parameters not distinct, or unsafe"
  let [nAlpha, nLhs, nMotive, nRefl, nRhs, nProof] := forallNames r.type
    | throwError "Eq.rec: unexpected type"
  let .forallE _ _ (.forallE _ _ (.forallE _ motive _ _) _) _ := r.type
    | throwError "Eq.rec: unexpected type"
  let [nMotiveRhs, nMotiveProof] := forallNames motive
    | throwError "Eq.rec: unexpected motive"
  let names : EqRecBinderNames := {
    alpha := nAlpha, lhs := nLhs, motive := nMotive, motiveRhs := nMotiveRhs,
    motiveProof := nMotiveProof, refl := nRefl, rhs := nRhs, proof := nProof }
  check (r.type.equal (eqRecTypeExpr ru rv names)) "Eq.rec: type is not eqRecTypeExpr"
  let [rule] := r.rules | throwError "Eq.rec: not one rule"
  check (rule.ctor == ``Eq.refl && rule.nfields == 0) "Eq.rec: unexpected rule"
  check (rule.rhs.equal (eqRecRuleRhsExpr ru rv names))
    "Eq.rec: rule is not eqRecRuleRhsExpr"
  -- Translations are the stored terms of `HasCanonicalEq`.
  check ((← toV [u] I.type) == canonicalEqType) "Eq: translation differs"
  check ((← toV [u] C.type) == canonicalEqReflType) "Eq.refl: translation differs"
  check ((← toV r.levelParams r.type) == canonicalEqRecType) "Eq.rec: translation differs"
  check ((← toV r.levelParams rule.rhs) == canonicalEqRecRule.rhs)
    "Eq.rec rule rhs: translation differs"
  check ((← toV r.levelParams (eqRecRuleLhsExpr ru rv names)) == canonicalEqRecRule.lhs)
    "Eq.rec rule lhs: translation differs"
  check ((← toV r.levelParams (eqRecRuleTypeExpr ru rv names)) == canonicalEqRecRule.type)
    "Eq.rec rule type: translation differs"
  check (canonicalEqRecRule.uvars == r.levelParams.length) "Eq.rec rule: universe arity"

end Lean4Lean.Tests.PreludeEq
