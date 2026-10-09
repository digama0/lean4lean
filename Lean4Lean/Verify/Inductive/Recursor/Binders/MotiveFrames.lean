import Lean4Lean.Verify.Inductive.Recursor.Context.ForallTelescope

/-! Typing of one motive frame of the motive pass of `mkRecInfos`: the major premise
and the motive declared after a family's indices (`RecursorMotiveFrameWF`), and the
generated family/motive telescope attached to it (`RecursorMotiveClosedFrameWF`). -/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment
namespace VerifyInductive

/-- Typing of the two locals (major and motive) declared after one family's
indices have been opened.  The starting context is already interpreted
under the recursor universe list, so the same certificate applies to every
member of a mutual block, including those reached after earlier frames. -/
structure RecursorMotiveFrameWF
    {c : AddInductive.Context} {recLparams : List Name}
    (Rindices : RecursorContextWF c recLparams)
    (stats : AddInductive.InductiveStats) (familyIdx : Nat)
    (indices : Array Expr) (elimLevel : Level) where
  familyTarget : VExpr
  familyTr :
    TrExprS Rindices.venv recLparams Rindices.mlctx.vlctx
      (mkAppN stats.indConsts[familyIdx]! stats.params) familyTarget
  familyIndexTargets : List VExpr
  familyIndicesTr : List.Forall₂
    (TrExprS Rindices.venv recLparams Rindices.mlctx.vlctx)
    indices.toList familyIndexTargets
  majorSourceTarget : VExpr
  majorSourceEq : majorSourceTarget =
    VExpr.mkApps familyTarget familyIndexTargets
  majorTarget : VExpr
  majorSourceDefEq :
    Rindices.venv.IsDefEqU recLparams.length Rindices.mlctx.vlctx.toCtx
      majorSourceTarget majorTarget
  majorTr :
    let majorTy :=
      ((mkAppN (mkAppN stats.indConsts[familyIdx]! stats.params)
        indices).consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper)
    TrExprS Rindices.venv
      recLparams
      Rindices.mlctx.vlctx majorTy majorTarget
  majorType :
    Rindices.venv.IsType
      recLparams.length
      Rindices.mlctx.vlctx.toCtx majorTarget
  indexDomains : List VExpr
  indexDomains_length : indexDomains.length = indices.size
  indexDomains_eq : indexDomains =
    (Rindices.mlctx.vlctx.toCtx.take indices.size).reverse
  resultLevel : VLevel
  resultLevelWF : resultLevel.WF recLparams.length
  resultLevelOf : VLevel.ofLevel recLparams elimLevel = some resultLevel
  motiveTarget : VExpr
  motiveTarget_eq :
    motiveTarget =
      ((VExpr.wrapForalls indexDomains
        (.forallE majorTarget (.sort resultLevel))).liftN
          indices.size 0).liftN 1 0
  /-- The generated motive telescope before it is weakened through
  the freshly opened indices and major.  This closed form makes
  the executable's motive comparable with the generated
  telescope in their common outer context. -/
  motiveClosed :
    let majorTy :=
      ((mkAppN (mkAppN stats.indConsts[familyIdx]! stats.params)
        indices).consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper)
    let cMajor : AddInductive.Context := { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ `t majorTy .default }
    let major := Expr.fvar ⟨c.ngen.curr⟩
    let motiveTy := cMajor.lctx.mkForall indices <|
      cMajor.lctx.mkForall #[major] <| .sort elimLevel
    ∃ hsize : indices.size ≤ Rindices.mlctx.length,
      ∃ closedTarget,
        TrExprS Rindices.venv recLparams
          (Rindices.mlctx.dropN indices.size hsize).vlctx
          (motiveTy.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) closedTarget ∧
        Rindices.venv.IsType recLparams.length
          (Rindices.mlctx.dropN indices.size hsize).vlctx.toCtx closedTarget ∧
        closedTarget = VExpr.wrapForalls indexDomains
          (.forallE majorTarget (.sort resultLevel))
  motiveTr :
    let majorTy :=
      ((mkAppN (mkAppN stats.indConsts[familyIdx]! stats.params)
        indices).consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper)
    let Rmajor := Rindices.withLocalDecl (name := `t) (bi := .default)
      majorTr majorType
    let cMajor : AddInductive.Context := { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ `t majorTy .default }
    let major := Expr.fvar ⟨c.ngen.curr⟩
    let motiveTy := cMajor.lctx.mkForall indices <|
      cMajor.lctx.mkForall #[major] <| .sort elimLevel
    TrExprS Rmajor.venv
      recLparams
      Rmajor.mlctx.vlctx (motiveTy.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) motiveTarget
  motiveType :
    let Rmajor := Rindices.withLocalDecl (name := `t) (bi := .default)
      majorTr majorType
    Rmajor.venv.IsType
      recLparams.length
      Rmajor.mlctx.vlctx.toCtx motiveTarget
  motiveSourceEq :
    let majorTy :=
      ((mkAppN (mkAppN stats.indConsts[familyIdx]! stats.params)
        indices).consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper)
    let cMajor : AddInductive.Context := { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ `t majorTy .default }
    let major := Expr.fvar ⟨c.ngen.curr⟩
    let motiveTy := cMajor.lctx.mkForall indices <|
      cMajor.lctx.mkForall #[major] <| .sort elimLevel
    (motiveTy.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) = motiveTy

/-- The generated family/motive telescope attached to one
executable motive frame.  Its motive type is compared with the
unannotated executable target in a separate step; this structure
records the declarative telescope and types its family endpoint. -/
structure RecursorMotiveClosedFrameWF
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (stats : AddInductive.InductiveStats) (familyIdx : Nat)
    (indices : Array Expr) (elimLevel : Level)
    (Hframe : RecursorMotiveFrameWF R stats familyIdx indices elimLevel) :
    Type where
  familyType : VExpr
  motiveType : VExpr
  familyTyping : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
    Hframe.familyTarget familyType
  telescope : RecursorMotiveTelescope Hframe.resultLevel indices.size
    Hframe.familyTarget familyType motiveType

end VerifyInductive
end Lean4Lean
