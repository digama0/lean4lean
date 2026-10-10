import Lean4Lean.Verify.Typing.Syntactic.Typed
import Lean4Lean.Verify.Environment.Basic
import Lean4Lean.Theory.Inductive.CanonicalEqSignature

/-! # Syntax of the prelude's equality

The declaration of `Eq` submitted by `Init.Prelude`, and the type and iota rule
of the recursor `Eq.rec` that the kernel generates for it, stated literally
(generic only in binder and universe-parameter names).  The three types
translate (`TrSyn`, hence every `TrExprS` derivation) to the corresponding
stored terms of `VEnv.HasCanonicalEq`; the iota-rule expressions are checked
against the stored rule by `Lean4Lean/Tests/PreludeEq.lean`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The concrete family type submitted by the prelude's declaration of
`Eq`. Binder names are kept by `Expr`, although abstract
translation erases them. -/
def preludeEqType (u alphaName lhsName rhsName : Name) : Expr :=
  .forallE alphaName (.sort (.param u))
    (.forallE lhsName (.bvar 0)
      (.forallE rhsName (.bvar 1) (.sort .zero) .default) .default)
    .implicit

/-- The concrete constructor type submitted for `Eq.refl`. -/
def preludeEqReflType (u alphaName valueName : Name) : Expr :=
  .forallE alphaName (.sort (.param u))
    (.forallE valueName (.bvar 0)
      (.app (.app (.app (.const ``Eq [.param u]) (.bvar 1)) (.bvar 0))
        (.bvar 0)) .default)
    .implicit

end VerifyInductive

open VerifyInductive

/-! ### Kernel expressions -/

/-- Binder names of the kernel's `Eq.rec` type and iota rule. They are
erased by translation. -/
structure EqRecBinderNames where
  alpha : Name
  lhs : Name
  motive : Name
  motiveRhs : Name
  motiveProof : Name
  refl : Name
  rhs : Name
  proof : Name

/-- The motive domain of the kernel's `Eq.rec.{u, v}` (`u` is the motive
universe, `v` the sort of `α`), under `α` and `a`. -/
def eqRecMotiveExprU (u v : Name) (n : EqRecBinderNames) : Expr :=
  .forallE n.motiveRhs (.bvar 1)
    (.forallE n.motiveProof
      (.app (.app (.app (.const ``Eq [.param v]) (.bvar 2)) (.bvar 1)) (.bvar 0))
      (.sort (.param u)) .default) .default

/-- The minor premise domain of the kernel's `Eq.rec`, under `α`, `a` and
the motive. -/
def eqRecMinorExpr (v : Name) : Expr :=
  .app (.app (.bvar 0) (.bvar 1))
    (.app (.app (.const ``Eq.refl [.param v]) (.bvar 2)) (.bvar 1))

/-- The type of `Eq.rec.{u, v}` as produced by the kernel for the `Init.Prelude`
declaration of `Eq`:
`∀ {α : Sort v} {a : α} {motive : ∀ b, @Eq α a b → Sort u},
  motive a (Eq.refl a) → ∀ {b : α} (t : @Eq α a b), motive b t`. -/
def eqRecTypeExpr (u v : Name) (n : EqRecBinderNames) : Expr :=
  .forallE n.alpha (.sort (.param v))
    (.forallE n.lhs (.bvar 0)
      (.forallE n.motive (eqRecMotiveExprU u v n)
        (.forallE n.refl (eqRecMinorExpr v)
          (.forallE n.rhs (.bvar 3)
            (.forallE n.proof
              (.app (.app (.app (.const ``Eq [.param v]) (.bvar 4)) (.bvar 3)) (.bvar 0))
              (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) .default)
            .implicit) .default) .implicit) .implicit) .implicit

/-- The right-hand side of the single recursor rule of `Eq.rec`, as stored by
the kernel: `fun α a motive refl => refl`. -/
def eqRecRuleRhsExpr (u v : Name) (n : EqRecBinderNames) : Expr :=
  .lam n.alpha (.sort (.param v))
    (.lam n.lhs (.bvar 0)
      (.lam n.motive (eqRecMotiveExprU u v n)
        (.lam n.refl (eqRecMinorExpr v) (.bvar 0) .default) .default) .default) .implicit

/-- The left-hand side of the iota rule of `Eq.rec`, which the kernel does not
store: `fun α a motive refl => @Eq.rec α a motive refl a (@Eq.refl α a)`. -/
def eqRecRuleLhsExpr (u v : Name) (n : EqRecBinderNames) : Expr :=
  .lam n.alpha (.sort (.param v))
    (.lam n.lhs (.bvar 0)
      (.lam n.motive (eqRecMotiveExprU u v n)
        (.lam n.refl (eqRecMinorExpr v)
          (.app (.app (.app (.app (.app (.app (.const ``Eq.rec [.param u, .param v])
            (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.bvar 2))
            (.app (.app (.const ``Eq.refl [.param v]) (.bvar 3)) (.bvar 2))) .default)
        .default) .default) .implicit

/-- The type of the iota rule of `Eq.rec`:
`∀ α a motive refl, motive a (@Eq.refl α a)`. -/
def eqRecRuleTypeExpr (u v : Name) (n : EqRecBinderNames) : Expr :=
  .forallE n.alpha (.sort (.param v))
    (.forallE n.lhs (.bvar 0)
      (.forallE n.motive (eqRecMotiveExprU u v n)
        (.forallE n.refl (eqRecMinorExpr v)
          (.app (.app (.bvar 1) (.bvar 2))
            (.app (.app (.const ``Eq.refl [.param v]) (.bvar 3)) (.bvar 2))) .default)
        .default) .default) .implicit

/-! ### Translation targets -/

section
variable {u v : Name}

private theorem ofLevel_two_left : VLevel.ofLevel [u, v] (.param u) = some (.param 0) := by
  simp [VLevel.ofLevel]

private theorem ofLevel_two_right (huv : u ≠ v) :
    VLevel.ofLevel [u, v] (.param v) = some (.param 1) := by
  have h : (u == v) = false := by simpa using huv
  simp [VLevel.ofLevel, List.idxOf_cons, h]

private theorem ofLevel_one : VLevel.ofLevel [u] (.param u) = some (.param 0) := by
  simp [VLevel.ofLevel]

private theorem mapM_one :
    [Level.param u].mapM (VLevel.ofLevel [u]) = some [.param 0] := by
  simp [List.mapM_cons, ofLevel_one]

private theorem mapM_two_right (huv : u ≠ v) :
    [Level.param v].mapM (VLevel.ofLevel [u, v]) = some [.param 1] := by
  simp [List.mapM_cons, ofLevel_two_right huv]

private theorem mapM_two (huv : u ≠ v) :
    [Level.param u, .param v].mapM (VLevel.ofLevel [u, v]) =
      some [.param 0, .param 1] := by
  simp [List.mapM_cons, ofLevel_two_left, ofLevel_two_right huv]

end

/-- Build a `TrSyn` derivation whose target is given. -/
syntax "canonical_eq_tr_syn" : tactic
macro_rules | `(tactic| canonical_eq_tr_syn) => `(tactic|
  repeat' (first
    | apply TrSyn.forallE
    | apply TrSyn.lam
    | apply TrSyn.app
    | (apply TrSyn.bvar; rfl)
    | (apply TrSyn.sort; first
        | exact ofLevel_two_left | exact ofLevel_two_right ‹_› | exact ofLevel_one
        | rfl)
    | (apply TrSyn.const; first
        | exact mapM_one | exact mapM_two_right ‹_› | exact mapM_two ‹_›)))

theorem preludeEqType_syn (u alphaName lhsName rhsName : Name) :
    TrSyn [u] [] (preludeEqType u alphaName lhsName rhsName)
      canonicalEqType := by
  unfold preludeEqType canonicalEqType
  canonical_eq_tr_syn

theorem preludeEqReflType_syn (u alphaName valueName : Name) :
    TrSyn [u] [] (preludeEqReflType u alphaName valueName)
      canonicalEqReflType := by
  unfold preludeEqReflType canonicalEqReflType
  canonical_eq_tr_syn

theorem eqRecTypeExpr_syn {u v : Name} (huv : u ≠ v) (n : EqRecBinderNames) :
    TrSyn [u, v] [] (eqRecTypeExpr u v n) canonicalEqRecType := by
  unfold eqRecTypeExpr eqRecMotiveExprU eqRecMinorExpr canonicalEqRecType
    canonicalEqRecMotive canonicalEqRecMinor
  canonical_eq_tr_syn

/-! ### Every translation is the stored term -/

section
variable {env : VEnv} {e : VExpr}

theorem TrExprS.eq_canonicalEqType {u a b c : Name}
    (H : TrExprS env [u] [] (preludeEqType u a b c) e) : e = canonicalEqType :=
  H.toTrSyn.unique (preludeEqType_syn u a b c)

theorem TrExprS.eq_canonicalEqReflType {u a b : Name}
    (H : TrExprS env [u] [] (preludeEqReflType u a b) e) : e = canonicalEqReflType :=
  H.toTrSyn.unique (preludeEqReflType_syn u a b)

theorem TrExprS.eq_canonicalEqRecType {u v : Name} (huv : u ≠ v) {n : EqRecBinderNames}
    (H : TrExprS env [u, v] [] (eqRecTypeExpr u v n) e) : e = canonicalEqRecType :=
  H.toTrSyn.unique (eqRecTypeExpr_syn huv n)

end

/-! ### Kernel constants with the prelude's types -/

/-- A safe kernel constant with the type `Init.Prelude` gives `Eq`. -/
def IsPreludeEq (ci : ConstantInfo) : Prop :=
  ci.safety = .safe ∧ ∃ u a b c, ci.levelParams = [u] ∧ ci.type = preludeEqType u a b c

/-- A safe kernel constant with the type `Init.Prelude` gives `Eq.refl`. -/
def IsPreludeEqRefl (ci : ConstantInfo) : Prop :=
  ci.safety = .safe ∧ ∃ u a b, ci.levelParams = [u] ∧ ci.type = preludeEqReflType u a b

/-- A safe kernel constant with the type the kernel generates for `Eq.rec`. -/
def IsPreludeEqRec (ci : ConstantInfo) : Prop :=
  ci.safety = .safe ∧
    ∃ u v n, u ≠ v ∧ ci.levelParams = [u, v] ∧ ci.type = eqRecTypeExpr u v n

end Lean4Lean
