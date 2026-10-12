import Lean4Lean.Verify.Inductive.Header.Installation
import Lean4Lean.Verify.Inductive.Constructor.SourceSignature

/-! # The checked tail of a constructor

`CheckedCtorTail`: a constructor type is definitionally a telescope over the common parameters
ending in a constructor tail certified by the executable check (`checkConstructors`), with the
field classification it returned. The constructor check records one per constructor
(`ConstructorCheck.tails`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The checked tail of one constructor `ctor` of `target`: its type is definitionally a
telescope over a parameter list `ps` (definitionally the common parameters `params`) ending in
a constructor tail certified by the executable check, with the field classification `classes`
the positivity check returned. -/
def CheckedCtorTail (env : VEnv) (decl : VInductDecl) (params : List VExpr)
    (target : VInductiveType) (ctor : VConstVal) (classes : List Bool) : Prop :=
  ∃ ps tail, env.IsDefEqCtx decl.uvars [] params.reverse ps.reverse ∧
    env.IsDefEqU decl.uvars [] ctor.type (VExpr.wrapForalls ps tail) ∧
    ConstructorTailCertificate env decl target ps.reverse 0 tail classes

theorem _root_.Lean4Lean.VInductDecl.UniformCtorTail.mono {env env' : VEnv} (henv : env ≤ env')
    (H : VInductDecl.UniformCtorTail env decl target levels ctx depth tail classes) :
    VInductDecl.UniformCtorTail env' decl target levels ctx depth tail classes := by
  induction H with
  | result h1 h2 => exact .result h1 h2
  | field htype' hfield _ ih =>
    obtain ⟨u, hu⟩ := htype'
    refine .field ⟨u, hu.mono henv⟩ ?_ ih
    rcases hfield with h | ⟨n, ⟨_, hn⟩, hs⟩
    · exact .inl h
    · exact .inr ⟨n, ⟨_, hn.mono henv⟩, hs⟩

theorem ConstructorTailCertificate.mono {env env' : VEnv} (henv : env ≤ env')
    (H : ConstructorTailCertificate env decl target ctx depth tail classes) :
    ConstructorTailCertificate env' decl target ctx depth tail classes := by
  obtain ⟨hshape, ⟨_, hty⟩, hraw, huniform⟩ := H
  exact ⟨hshape.mono henv, ⟨_, hty.mono henv⟩, hraw, huniform.mono henv⟩

theorem CheckedCtorTail.mono {env env' : VEnv} (henv : env ≤ env')
    (H : CheckedCtorTail env decl params target ctor classes) :
    CheckedCtorTail env' decl params target ctor classes := by
  obtain ⟨ps, tail, hctx, ⟨_, htype⟩, cert⟩ := H
  exact ⟨ps, tail, hctx.mono henv, ⟨_, htype.mono henv⟩, cert.mono henv⟩

end VerifyInductive
end Lean4Lean
