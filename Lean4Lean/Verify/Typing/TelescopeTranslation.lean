import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Environment

/-!
# Telescope certificates

The projection walk of `inferProj` keeps the body of a constructor telescope past a field binder
that the body does not use, without substituting anything. Its verification therefore needs, at
such a binder, the translation of the body *without* the binder. The syntax of that translation is
free: a source that does not mention a binder translates without it, to the lowered result
(`TrSyn.lower`). What is not free is its typing in the smaller context (section 5.3 of
the design notes).

`TelWF env Us n Δ e e'` is that typing content for the first `n` binders of the leading `forallE`
spine of `e`, whose syntactic translation is `e'`: the result is well typed, the source's residual
obligations (`TrResidual`) hold, and, at a positive depth, `e` is *syntactically* a `forallE`
whose body is certified under the binder (*keep*) and, if the body does not mention the binder,
also without it (*delete*). `TelTrN` pairs it with the syntactic translation; it is exactly
`TrTyped` along every kept and deleted residual telescope.

The certificate speaks only about binders already present in `e`: substituting a term for a
variable creates no obligation for spines exposed inside the substituted term, so it is closed
under substitution, weakening and level instantiation (`Verify/Typing/TelescopeTranslationLemmas.lean`).
A constructor of `n` parameters and `m` fields carries it at depth `n + m`, which is what the walk
consumes.
-/

namespace Lean4Lean
open Lean

variable (env : VEnv) (Us : List Name) in
/-- The typing content of a depth-bounded telescope certificate: the typing of the translated
telescope and of every residual telescope obtained by deleting unused binders, each in its own
context, with the residual obligations of the source. The syntactic content (that the deleted
telescopes translate, to the lowered terms) is not part of it: it is `TrSyn.lower`. -/
inductive TelWF : Nat → VLCtx → Expr → VExpr → Prop
  | zero {Δ : VLCtx} {e : Expr} {e' : VExpr} :
    VExpr.WF env Us.length Δ.toCtx e' → TrResidual env Us Δ e → TelWF 0 Δ e e'
  | succ {k : Nat} {Δ : VLCtx} {n d b bi d' b'} :
    VExpr.WF env Us.length Δ.toCtx (.forallE d' b') →
    TrResidual env Us Δ (.forallE n d b bi) →
    TelWF k ((none, .vlam d') :: Δ) b b' →
    (∀ b₀ b₀', b = Expr.liftLooseBVars' b₀ 0 1 → b' = VExpr.lift b₀' → TelWF k Δ b₀ b₀') →
    TelWF (k + 1) Δ (.forallE n d b bi) (.forallE d' b')

/-- Depth-bounded telescope certificate: the syntactic translation of the telescope together with
the typing-only certificate `TelWF`. -/
structure TelTrN (env : VEnv) (Us : List Name) (n : Nat) (Δ : VLCtx) (e : Expr) (e' : VExpr) :
    Prop where
  syn : TrSyn Us Δ e e'
  tel : TelWF env Us n Δ e e'

end Lean4Lean
