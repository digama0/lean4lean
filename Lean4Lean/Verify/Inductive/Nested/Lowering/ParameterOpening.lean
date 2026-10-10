import Lean4Lean.Verify.Inductive.Recursor.Binders.RecursiveFields
import Lean4Lean.Verify.Inductive.Rules.SameForallPrefix

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-! # Parameter opening of nested lowering

The relation `LoweringParamOpening` describes how nested lowering opens the common parameters
of a forall telescope as fresh local declarations, and its basic properties. -/

/-- Parameter-telescope opening performed by nested lowering. The relation
retains both the growing local context and the array of corresponding free
variables, which the restoration substitution reuses. -/
inductive LoweringParamOpening : LocalContext → Array Expr → Expr → Nat →
    LocalContext → Expr → Array Expr → Prop
  | done : LoweringParamOpening lctx params type 0 lctx type params
  | step {id : FVarId} {name : Name} {dom body : Expr} {bi : BinderInfo} :
      LoweringParamOpening
        (lctx.mkLocalDecl id name dom bi) (params.push (.fvar id))
        (body.instantiate1 (.fvar id)) n outLctx tail outParams →
      LoweringParamOpening lctx params (.forallE name dom body bi) (n + 1)
        outLctx tail outParams

theorem LoweringParamOpening.params_size
    (H : LoweringParamOpening lctx params type n outLctx tail outParams) :
    outParams.size = params.size + n := by
  induction H with
  | done => simp
  | step _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

theorem LoweringParamOpening.params_extension
    (H : LoweringParamOpening lctx params type n outLctx tail outParams) :
    ∃ suffix, outParams.toList = params.toList ++ suffix ∧
      suffix.length = n := by
  induction H with
  | done => exact ⟨[], by simp⟩
  | @step lctx params name dom body bi id n outLctx tail outParams H ih =>
    rcases ih with ⟨suffix, heq, hlength⟩
    refine ⟨(.fvar id) :: suffix, ?_, by simp [hlength]⟩
    simp [heq, List.append_assoc]

/-- Exact local-declaration extension performed by the forall-only nested
parameter opening. Declarations are in binder order. -/
theorem LoweringParamOpening.context_extension
    (H : LoweringParamOpening lctx As e n outLctx tail outAs) :
    ∃ decls : List LocalDecl,
      outLctx.toList = decls.reverse ++ lctx.toList ∧
      outAs.toList = As.toList ++ decls.map (fun d => .fvar d.fvarId) ∧
      decls.length = n := by
  induction H with
  | done => exact ⟨[], by simp⟩
  | step Hnext ih =>
    rename_i n' outLctx' tail' outAs' lctx' As' id name dom body bi
    rcases ih with ⟨decls, hlctx, hparams, hlength⟩
    let decl : LocalDecl :=
      .cdecl lctx'.decls.size id name dom bi .default
    refine ⟨decl :: decls, ?_, ?_, by simp [hlength]⟩
    · simp [hlctx, decl, LocalContext.mkLocalDecl_toList]
    · simp [hparams, decl, List.append_assoc, LocalDecl.fvarId]

end VerifyInductive
end Lean4Lean
