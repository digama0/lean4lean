import Lean4Lean.Verify.Inductive.Nested.Install.Installed
import Lean4Lean.Verify.Inductive.Install.Result

/-! # From the restored block certificate to the inductive extension

`NestedCertificate` is the nested branch's counterpart of `OrdinaryInstallation`: the
restored declaration's block certificate at the checked safety level together with the
translation of the submitted source syntax. Its installation into the safety-indexed model is
the ordinary path's (`BlockCertificate.extendSafeExact`, `extendUnsafeExact`), and
`NestedCertificate.inductiveExtension` is the public result (shared interface, proved). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The certificate of a nested declaration at its safety level. -/
structure NestedCertificate (safety : DefinitionSafety) (env : Environment) (venv : VEnv)
    (lparams : List Name) (nparams : Nat) (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (outEnv : Environment) where
  decl : VInductDecl
  envTypes : VEnv
  envCtors : VEnv
  outVEnv : VEnv
  source : TrInductDeclCore venv lparams nparams sourceTypes isUnsafe decl envTypes envCtors
  block : BlockCertificate safety env venv decl outEnv outVEnv

namespace NestedCertificate

/-- A restored block with its environment-side facts is a nested certificate. -/
def ofRestoredBlock {c : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
    {res : ElimNestedInductive.Result} {loweredEnv : Environment}
    {L : LoweredRun Hc nparams res.types.toArray loweredEnv}
    {sourceTypes : List InductiveType} {isUnsafe : Bool} {outEnv : Environment}
    (B : RestoredBlock L sourceTypes isUnsafe outEnv) (I : B.Installed)
    (hsource : sourceTypes ≠ []) :
    NestedCertificate c.safety c.env Hc.venv c.lparams nparams sourceTypes isUnsafe outEnv where
  decl := B.decl
  envTypes := B.envTypes
  envCtors := B.envCtors
  outVEnv := B.outVEnv
  source := B.source
  block := B.blockCertificate I hsource

/-- A certified nested declaration extends the safety-indexed model, with the source judgment
of the exact submitted syntax. -/
theorem extendExact {env outEnv : Environment} {ves : VEnvs} {lparams : List Name}
    {nparams : Nat} {sourceTypes : List InductiveType} {isUnsafe : Bool}
    (N : NestedCertificate (if isUnsafe then .unsafe else .safe) env
      (ves.venv (if isUnsafe then .unsafe else .safe)) lparams nparams sourceTypes isUnsafe outEnv)
    (wf : ves.WF env) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      Nonempty (SourceAddInduct (ves.venv (if isUnsafe then .unsafe else .safe)) lparams nparams
        sourceTypes isUnsafe (ves'.venv (if isUnsafe then .unsafe else .safe))) := by
  have hu : N.decl.isUnsafe = isUnsafe := N.source.isUnsafe
  cases isUnsafe with
  | false =>
    obtain ⟨ves', wf', hle, heq⟩ := N.block.extendSafeExact wf hu
    refine ⟨ves', wf', hle, ⟨{
      decl := N.decl
      envTypes := N.envTypes
      envCtors := N.envCtors
      source := N.source
      wf := N.block.wf
      installed := heq ▸ N.block.installed }⟩⟩
  | true =>
    obtain ⟨ves', wf', hle, heq⟩ := N.block.extendUnsafeExact wf hu
    refine ⟨ves', wf', hle, ⟨{
      decl := N.decl
      envTypes := N.envTypes
      envCtors := N.envCtors
      source := N.source
      wf := N.block.wf
      installed := heq ▸ N.block.installed }⟩⟩

/-- The public result of the nested branch. -/
theorem inductiveExtension {env outEnv : Environment} {ves : VEnvs} {lparams : List Name}
    {nparams : Nat} {sourceTypes : List InductiveType} {isUnsafe : Bool}
    (N : NestedCertificate (if isUnsafe then .unsafe else .safe) env
      (ves.venv (if isUnsafe then .unsafe else .safe)) lparams nparams sourceTypes isUnsafe outEnv)
    (wf : ves.WF env) :
    Nonempty (InductiveExtension env outEnv ves lparams nparams sourceTypes isUnsafe) :=
  let ⟨ves', wf', hle, ⟨S⟩⟩ := N.extendExact wf
  ⟨InductiveExtension.ofModel ves' wf' hle S⟩

end NestedCertificate
end VerifyInductive
end Lean4Lean
