import Lean4Lean.Verify.Inductive.Basic

/-! The result shared by every inductive execution path: the source-facing `SourceAddInduct`
and the declaration-level `InductiveExtension`. Shared interface of the wave 2 scaffold
(frozen); consumed by `Dispatch.lean` and `Verify/Environment.lean`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The independent inductive judgment produced by a successful checker run, including the
translation of the exact source syntax. Keeping the source translation beside the installation
prevents an installed-environment model from silently being attributed to a different (for
example, lowered) declaration. The installation is the model's staged `VEnv.addInduct` of a
well-formed declaration (`VEnv.InductInstalled`, `Verify/Environment/Blocks.lean`). -/
structure SourceAddInduct
    (sourceEnv : VEnv) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (installedVEnv : VEnv) where
  decl : VInductDecl
  envTypes : VEnv
  envCtors : VEnv
  source : TrInductDeclCore sourceEnv lparams nparams sourceTypes isUnsafe
    decl envTypes envCtors
  wf : decl.WF sourceEnv
  installed : sourceEnv.addInduct decl = some installedVEnv

/-- Ordinary runs and primitive runs (`Bool`, `Nat`) share the same independent
source judgment; this alias documents the ordinary use site. -/
abbrev OrdinarySourceAddInduct := SourceAddInduct

theorem SourceAddInduct.inductInstalled
    (H : SourceAddInduct sourceEnv lparams nparams sourceTypes isUnsafe installedVEnv)
    -- WAVE 3 COMPAT (lowering): `InductInstalled` records a well-formed compiled block
    (hcompiled : ∃ block, H.decl.CompilesTo sourceEnv block ∧ H.decl.RecsOf block ∧
      block.WF sourceEnv) :
    installedVEnv.InductInstalled H.decl :=
  VEnv.InductInstalled.of_addInduct H.wf H.installed hcompiled

/-- Uniform declaration-facing result for every inductive execution path. It records a
complete model of the exact returned environment, pointwise extension of all source observers,
and the independent specification of the exact submitted source declaration. -/
structure InductiveExtension
    (sourceEnv outEnv : Environment) (sourceModels : VEnvs)
    (lparams : List Name) (nparams : Nat) (sourceTypes : List InductiveType)
    (isUnsafe : Bool) where
  targetModels : VEnvs
  wf : targetModels.WF outEnv
  mono : ∀ safety, sourceModels.venv safety ≤ targetModels.venv safety
  specification : SourceAddInduct
    (sourceModels.venv (if isUnsafe then .unsafe else .safe)) lparams nparams
    sourceTypes isUnsafe
    (targetModels.venv (if isUnsafe then .unsafe else .safe))

/-- Construct the uniform result directly from the environment model and
independent source specification. -/
def InductiveExtension.ofModel
    (targetModels : VEnvs) (wf : targetModels.WF outEnv)
    (mono : ∀ safety, sourceModels.venv safety ≤ targetModels.venv safety)
    (specification : SourceAddInduct
      (sourceModels.venv (if isUnsafe then .unsafe else .safe)) lparams
      nparams sourceTypes isUnsafe
      (targetModels.venv (if isUnsafe then .unsafe else .safe))) :
    InductiveExtension sourceEnv outEnv sourceModels lparams nparams sourceTypes
      isUnsafe where
  targetModels := targetModels
  wf := wf
  mono := mono
  specification := specification

/-- Forget the inductive-specific facts and recover the
environment-preservation postcondition used by `addDecl.WF`. -/
theorem InductiveExtension.modelExtension
    (H : InductiveExtension sourceEnv outEnv sourceModels lparams nparams sourceTypes
      isUnsafe) :
    ∃ targetModels : VEnvs, targetModels.WF outEnv ∧
      ∀ safety, sourceModels.venv safety ≤ targetModels.venv safety :=
  ⟨H.targetModels, H.wf, H.mono⟩

end VerifyInductive
end Lean4Lean
