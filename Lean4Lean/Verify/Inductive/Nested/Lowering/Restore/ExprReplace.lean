import Lean4Lean.Verify.Inductive.Nested.Lowering.Refinement
import Lean4Lean.Verify.Inductive.Recursor.Signature.RecursorTypeTelescope

/-! An exact, cache-independent specification of `Expr.replace` (`ExprReplacement`) and the
telescope accepted by nested restoration (`RestoreTelescope`). The typing part of the source
file (`RecursorTypeTelescope`, the generated recursor telescopes) is ported by Restoration-B. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Exact, cache-independent specification of `Expr.replace`. A successful
node callback stops traversal at that node; otherwise the relation records
the recursively restored children and the same update combinators used by
Lean's implementation. -/
inductive ExprReplacement (replaceNode : Expr → Option Expr) : Expr → Expr → Prop
  | occurrence (h : replaceNode input = some output) :
      ExprReplacement replaceNode input output
  | bvar (h : replaceNode (.bvar i) = none) :
      ExprReplacement replaceNode (.bvar i) (.bvar i)
  | fvar {fvarId : FVarId} (h : replaceNode (.fvar fvarId) = none) :
      ExprReplacement replaceNode (.fvar fvarId) (.fvar fvarId)
  | mvar {mvarId : MVarId} (h : replaceNode (.mvar mvarId) = none) :
      ExprReplacement replaceNode (.mvar mvarId) (.mvar mvarId)
  | sort (h : replaceNode (.sort level) = none) :
      ExprReplacement replaceNode (.sort level) (.sort level)
  | const (h : replaceNode (.const name levels) = none) :
      ExprReplacement replaceNode (.const name levels) (.const name levels)
  | lit (h : replaceNode (.lit literal) = none) :
      ExprReplacement replaceNode (.lit literal) (.lit literal)
  | app (h : replaceNode (.app fn arg) = none)
      (hfn : ExprReplacement replaceNode fn fn')
      (harg : ExprReplacement replaceNode arg arg') :
      ExprReplacement replaceNode (.app fn arg)
        (Expr.updateApp! (.app fn arg) fn' arg')
  | lam (h : replaceNode (.lam name dom body bi) = none)
      (hdom : ExprReplacement replaceNode dom dom')
      (hbody : ExprReplacement replaceNode body body') :
      ExprReplacement replaceNode (.lam name dom body bi)
        (Expr.updateLambdaE! (.lam name dom body bi) dom' body')
  | forallE (h : replaceNode (.forallE name dom body bi) = none)
      (hdom : ExprReplacement replaceNode dom dom')
      (hbody : ExprReplacement replaceNode body body') :
      ExprReplacement replaceNode (.forallE name dom body bi)
        (Expr.updateForallE! (.forallE name dom body bi) dom' body')
  | letE (h : replaceNode (.letE name type value body nondep) = none)
      (htype : ExprReplacement replaceNode type type')
      (hvalue : ExprReplacement replaceNode value value')
      (hbody : ExprReplacement replaceNode body body') :
      ExprReplacement replaceNode (.letE name type value body nondep)
        (Expr.updateLetE! (.letE name type value body nondep)
          type' value' body')
  | mdata (h : replaceNode (.mdata data body) = none)
      (hbody : ExprReplacement replaceNode body body') :
      ExprReplacement replaceNode (.mdata data body)
        (Expr.updateMData! (.mdata data body) body')
  | proj (h : replaceNode (.proj typeName index body) = none)
      (hbody : ExprReplacement replaceNode body body') :
      ExprReplacement replaceNode (.proj typeName index body)
        (Expr.updateProj! (.proj typeName index body) body')

/-- Residual-sensitive form of `forallTelescope`: replacement below the
leading binders is retained as an explicit relation between the old and new
residual expressions. -/
theorem ExprReplacement.forallTelescope_residual
    (Hnone : ∀ name dom body bi,
      replaceNode (.forallE name dom body bi) = none)
    (Hreplace : ExprReplacement replaceNode input output)
    (Htelescope : Expr.ForallTelescope input arity residual) :
    ∃ restoredResidual,
      Expr.ForallTelescope output arity restoredResidual ∧
      ExprReplacement replaceNode residual restoredResidual := by
  induction Htelescope generalizing output with
  | nil => exact ⟨output, .nil output, Hreplace⟩
  | @cons body arity residual name dom bi Htail ih =>
    cases Hreplace with
    | occurrence h =>
      rw [Hnone] at h
      contradiction
    | forallE h hdom hbody =>
      rcases ih hbody with ⟨restoredResidual, Hrestored, Hresidual⟩
      refine ⟨restoredResidual, ?_, Hresidual⟩
      simpa [Expr.updateForallE!] using
        (Expr.ForallTelescope.cons (name := name) (dom := _)
          (bi := bi) Hrestored)

/-- Binder-aligned form of expression replacement.  Unlike the existential
`forallTelescope_residual` theorem, this relation retains the replacement
proof for every old/restored domain and for the final residual. -/
inductive ExprReplacement.ForallTelescopeReplacement
    (replaceNode : Expr → Option Expr) :
    Expr → Expr → Nat → Expr → Expr → Prop
  | nil (Hbody : ExprReplacement replaceNode oldBody newBody) :
      ExprReplacement.ForallTelescopeReplacement replaceNode
        oldBody newBody 0 oldBody newBody
  | cons
      (Hnone : replaceNode (.forallE name oldDom oldBody bi) = none)
      (Hdom : ExprReplacement replaceNode oldDom newDom)
      (Hbody : ExprReplacement.ForallTelescopeReplacement replaceNode
        oldBody newBody arity oldResidual newResidual) :
      ExprReplacement.ForallTelescopeReplacement replaceNode
        (.forallE name oldDom oldBody bi)
        (Expr.updateForallE! (.forallE name oldDom oldBody bi)
          newDom newBody)
        (arity + 1) oldResidual newResidual

/-- Decompose a replacement of a known forall telescope into the
binder-aligned `ForallTelescopeReplacement`. -/
theorem ExprReplacement.forallTelescopeReplacement
    (Hnone : ∀ name dom body bi,
      replaceNode (.forallE name dom body bi) = none)
    (Hreplace : ExprReplacement replaceNode input output)
    (Htelescope : Expr.ForallTelescope input arity residual) :
    ∃ restoredResidual,
      ExprReplacement.ForallTelescopeReplacement replaceNode input output
        arity residual restoredResidual := by
  induction Htelescope generalizing output with
  | nil => exact ⟨output, .nil Hreplace⟩
  | @cons body arity residual name dom bi Htail ih =>
    cases Hreplace with
    | occurrence h =>
      rw [Hnone] at h
      contradiction
    | forallE h hdom hbody =>
      rcases ih hbody with ⟨restoredResidual, Hrestored⟩
      exact ⟨restoredResidual, .cons h hdom Hrestored⟩

theorem ExprReplacement.ForallTelescopeReplacement.newTelescope
    (H : ExprReplacement.ForallTelescopeReplacement replaceNode input output
      arity oldResidual newResidual) :
    Expr.ForallTelescope output arity newResidual := by
  induction H with
  | nil => exact .nil _
  | @cons name oldDom oldBody bi newDom newBody arity oldResidual newResidual
      Hnone Hdom Hbody ih =>
    simpa [Expr.updateForallE!] using
      (Expr.ForallTelescope.cons (name := name) (dom := newDom)
        (bi := bi) ih)

theorem ExprReplacement.ForallTelescopeReplacement.residualReplacement
    (H : ExprReplacement.ForallTelescopeReplacement replaceNode input output
      arity oldResidual newResidual) :
    ExprReplacement replaceNode oldResidual newResidual := by
  induction H with
  | nil Hbody => exact Hbody
  | cons _ _ _ ih => exact ih

theorem ExprReplacement.ofReplace
    (replaceNode : Expr → Option Expr) :
    ∀ input, ExprReplacement replaceNode input (input.replace replaceNode) := by
  intro input
  induction input with
  | bvar i =>
    cases h : replaceNode (.bvar i) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.bvar h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)
  | fvar i =>
    cases h : replaceNode (.fvar i) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.fvar h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)
  | mvar i =>
    cases h : replaceNode (.mvar i) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.mvar h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)
  | sort level =>
    cases h : replaceNode (.sort level) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.sort h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)
  | const name levels =>
    cases h : replaceNode (.const name levels) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.const h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)
  | lit literal =>
    cases h : replaceNode (.lit literal) with
    | none => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.lit h)
    | some output => simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)
  | app fn arg hfn harg =>
    cases h : replaceNode (.app fn arg) with
    | none =>
      rw [Expr.replace_eq] at hfn harg
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .app h hfn harg
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)

  | lam name dom body bi hdom hbody =>
    cases h : replaceNode (.lam name dom body bi) with
    | none =>
      rw [Expr.replace_eq] at hdom hbody
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .lam h hdom hbody
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)
  | forallE name dom body bi hdom hbody =>
    cases h : replaceNode (.forallE name dom body bi) with
    | none =>
      rw [Expr.replace_eq] at hdom hbody
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .forallE h hdom hbody
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)
  | letE name type value body nondep htype hvalue hbody =>
    cases h : replaceNode (.letE name type value body nondep) with
    | none =>
      rw [Expr.replace_eq] at htype hvalue hbody
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .letE h htype hvalue hbody
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)
  | mdata data body hbody =>
    cases h : replaceNode (.mdata data body) with
    | none =>
      rw [Expr.replace_eq] at hbody
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .mdata h hbody
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)
  | proj typeName index body hbody =>
    cases h : replaceNode (.proj typeName index body) with
    | none =>
      rw [Expr.replace_eq] at hbody
      simp only [Expr.replace_eq, Expr.replaceNoCache, h]
      exact .proj h hbody
    | some output =>
      simpa [Expr.replace_eq, Expr.replaceNoCache, h] using
        (ExprReplacement.occurrence h)

/-- The relational restoration traversal is functional and computes exactly
`Expr.replace`. This lets the inverse theorems for restoration use the
`ExprReplacement` derivation recorded by `NestedRestoration`. -/
theorem ExprReplacement.eq_replace
    (H : ExprReplacement replaceNode input output) :
    output = input.replace replaceNode := by
  induction H with
  | occurrence h => simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, h]
  | bvar h | fvar h | mvar h | sort h | const h | lit h =>
    simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, h]
  | app h hfn harg ihFn ihArg =>
    rw [Expr.replace_eq] at ihFn ihArg
    rw [Expr.replace_eq]
    rw [Lean.Expr.replaceNoCache.eq_def, h]
    dsimp only
    rw [← ihFn, ← ihArg]
  | lam h hdom hbody ihDom ihBody =>
    rw [Expr.replace_eq] at ihDom ihBody
    rw [Expr.replace_eq]
    rw [Lean.Expr.replaceNoCache.eq_def, h]
    dsimp only
    rw [← ihDom, ← ihBody]
  | forallE h hdom hbody ihDom ihBody =>
    rw [Expr.replace_eq] at ihDom ihBody
    rw [Expr.replace_eq]
    rw [Lean.Expr.replaceNoCache.eq_def, h]
    dsimp only
    rw [← ihDom, ← ihBody]
  | letE h htype hvalue hbody ihType ihValue ihBody =>
    rw [Expr.replace_eq] at ihType ihValue ihBody
    rw [Expr.replace_eq]
    rw [Lean.Expr.replaceNoCache.eq_def, h]
    dsimp only
    rw [← ihType, ← ihValue, ← ihBody]
  | mdata h hbody ihBody | proj h hbody ihBody =>
    rw [Expr.replace_eq] at ihBody
    rw [Expr.replace_eq]
    rw [Lean.Expr.replaceNoCache.eq_def, h]
    dsimp only
    rw [← ihBody]

/-- The body traversal used by `restoreNested` is related exactly to its
three separately specified node-restoration cases. -/
theorem restoreNested_body
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (As : Array Expr) (auxRec : NameMap Name)
    (body : Expr) :
    ExprReplacement (result.restoreNestedNode env As auxRec) body
      (body.replace (result.restoreNestedNode env As auxRec)) :=
  ExprReplacement.ofReplace _ body

/-- Mixed forall/lambda telescope accepted by nested restoration. The
executable preserves the outer binder kind of the input root, while both
binder forms are accepted during opening. -/
inductive RestoreTelescope : Expr → Nat → Prop
  | done : RestoreTelescope e 0
  | forallE : RestoreTelescope body n →
      RestoreTelescope (.forallE name dom body bi) (n + 1)
  | lam : RestoreTelescope body n →
      RestoreTelescope (.lam name dom body bi) (n + 1)

/-- Any prefix of a generated forall telescope is accepted by nested
restoration. -/
theorem Expr.ForallTelescope.restorePrefix
    (H : Expr.ForallTelescope e arity residual)
    (hn : n ≤ arity) : RestoreTelescope e n := by
  induction n generalizing e arity residual with
  | zero => exact .done
  | succ n ih =>
    cases H with
    | nil => simp at hn
    | cons Hbody =>
      apply RestoreTelescope.forallE
      exact ih Hbody (by omega)

/-- Any prefix of a generated lambda telescope is accepted by nested
restoration. -/
theorem Expr.LambdaTelescope.restorePrefix
    (H : Expr.LambdaTelescope e arity residual)
    (hn : n ≤ arity) : RestoreTelescope e n := by
  induction n generalizing e arity residual with
  | zero => exact .done
  | succ n ih =>
    cases H with
    | nil => simp at hn
    | @cons body arity residual name dom bi Hbody =>
      apply RestoreTelescope.lam
      exact ih Hbody (by omega)

theorem RestoreTelescope.instantiate1'
    (H : RestoreTelescope e n) (arg : Expr) (depth : Nat) :
    RestoreTelescope (e.instantiate1' arg depth) n := by
  induction H generalizing depth with
  | done => exact .done
  | forallE H ih =>
    simp only [Expr.instantiate1']
    exact .forallE (ih (depth + 1))
  | lam H ih =>
    simp only [Expr.instantiate1']
    exact .lam (ih (depth + 1))

theorem RestoreTelescope.instantiate1
    (H : RestoreTelescope e n) (arg : Expr) :
    RestoreTelescope (e.instantiate1 arg) n := by
  rw [Expr.instantiate1_eq]
  exact H.instantiate1' arg 0


end VerifyInductive
end Lean4Lean
