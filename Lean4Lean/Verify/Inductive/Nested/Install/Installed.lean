import Lean4Lean.Verify.Inductive.Nested.Equations.Rules

/-! # The environment-side facts of a restored block and its block certificate (owner: Install)

`RestoredBlock.Installed` collects what `InstalledBlocks.addInduct` and `BlockCertificate` read
of the output environment beyond the restored block's own data: the checking invariant of the
output over the output model, closure, constructor owners, the origin of every new header
(`InductInfosFromDecl`), the cover of the declaration's families, the majors of the new
recursors and the constructor parameter alignment. `RestoredBlock.installedFacts` produces it (the
stub of this file); `RestoredBlock.blockCertificate` assembles PR #43's `BlockCertificate`
from it, the restored block and the Equations owner's rule typing (proved), after which the
ordinary path's `BlockCertificate.extendSafeExact`/`extendUnsafeExact` install the block.

Source branch: `Nested/Install/{BlockCertificate,FromRun,DependencyOrder,ConstructorCoherence,
Result}.lean` (`RestoredBlockCertificate.inductInfosFromDecl`, `.cover`,
`NestedRestorationFolds.constructorOwnersPresentOfContext`,
`NestedInstalledRun.constructorParameterDomainsDefEqOfSource`, the `CheckingEnv.Valid` of the
restored output through `InstalledBlocks.addCtorStage`-style staging). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

namespace RestoredBlock

variable {c : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
  {res : ElimNestedInductive.Result} {loweredEnv : Environment}
  {L : LoweredRun Hc nparams res.types.toArray loweredEnv}
  {sourceTypes : List InductiveType} {isUnsafe : Bool} {outEnv : Environment}

/-- The environment-side facts of a restored block (see the module documentation). -/
structure Installed (B : RestoredBlock L sourceTypes isUnsafe outEnv) : Prop where
  checking : CheckingEnv.Valid c.safety outEnv B.outVEnv
  closed : MutualInductivesClosed outEnv
  constructorOwners : ConstructorOwnersPresent outEnv
  inductInfosFromDecl : InductInfosFromDecl c.env.constants outEnv.constants B.decl
  cover : ∀ T ∈ B.decl.types,
    ∃ v, outEnv.find? T.name = some (.inductInfo v) ∧ c.env.find? T.name = none
  recMajor : ∀ {n r}, outEnv.find? n = some (.recInfo r) → c.env.find? n = none →
    ∃ info, outEnv.find? r.getMajorInduct = some (.inductInfo info)
  constructorParameterAlignment : ConstructorParameterAlignment c.safety c.env Hc.venv →
    ConstructorParameterAlignment c.safety outEnv B.outVEnv

/-- The kernel-level facts of the restored output: what the restoration folds certify about
the inserted `inductInfo`/`ctorInfo`/`recInfo` metadata (the `all` lists, constructor owners,
the families' alignment with the declaration, the recursors' majors, the constructor
parameter domains) and the primitive names. Source branch: `RestoredBlockCertificate`
(`inductInfosFromDecl`, `NestedRestorationFolds.constructorOwnersPresentOfContext`,
`Install/Result.lean`'s `MutualInductivesClosed` and `hconstructorSemantics` through
`Install/ConstructorCoherence.lean`). -/
structure KernelFacts (B : RestoredBlock L sourceTypes isUnsafe outEnv) : Prop where
  closed : MutualInductivesClosed outEnv
  constructorOwners : ConstructorOwnersPresent outEnv
  inductInfosFromDecl : InductInfosFromDecl c.env.constants outEnv.constants B.decl
  recMajor : ∀ {n r}, outEnv.find? n = some (.recInfo r) → c.env.find? n = none →
    ∃ info, outEnv.find? r.getMajorInduct = some (.inductInfo info)
  constructorParameterAlignment : ConstructorParameterAlignment c.safety c.env Hc.venv →
    ConstructorParameterAlignment c.safety outEnv B.outVEnv
  hasPrimitives : B.outVEnv.HasPrimitives
  safePrimitives : ∀ {n ci}, outEnv.find? n = some ci →
    Kernel.Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []

/-- The kernel-level facts of a restored block. -/
theorem kernelFacts (B : RestoredBlock L sourceTypes isUnsafe outEnv)
    (hsource : sourceTypes ≠ []) : B.KernelFacts := by
  -- WAVE 3 STUB (Equations+Install): read off the restoration folds of `B.run` (restB's port
  -- of `NestedRun`, not yet a field of `RestoredBlock`): `RestoredBlockCertificate.
  -- inductInfosFromDecl`, `NestedRestorationFolds.constructorOwnersPresentOfContext`, the
  -- closure and the recursor majors of the restored `inductInfo`/`recInfo`s, the alignment
  -- through `NestedInstalledRun.constructorParameterDomainsDefEqOfSource`, the primitive
  -- names through the lowered run's constructor stage.
  have := B; have := hsource; sorry

/-- The families of the declaration are new `inductInfo`s of the output. -/
theorem cover (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    ∀ T ∈ B.decl.types,
      ∃ v, outEnv.find? T.name = some (.inductInfo v) ∧ c.env.find? T.name = none := by
  have hwf : c.env.constants.WF := Hc.map_wf
  have houtWF : outEnv.constants.WF := B.addInduct.wf hwf
  intro T hT
  obtain ⟨iv, hiv, htr⟩ := Lean4Lean.List.Forall₂.forall_exists_r B.trTypes T hT
  have hname : iv.1.name = T.name := htr.tr.2
  have hmem : ConstantInfo.inductInfo iv.1 ∈ AddInduct.consts B.ivals B.rvals :=
    AddInduct.mem_consts.2 (.inl ⟨iv, hiv, rfl⟩)
  refine ⟨iv.1, ?_, ?_⟩
  · rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?, ← hname]
    exact B.addInduct.find?_self hwf hmem
  · have h := B.fresh _ hmem
    rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?, ← hname]
    exact h

/-- A new recursor of the output is one of the block's. -/
theorem newRec' (B : RestoredBlock L sourceTypes isUnsafe outEnv)
    {n : Name} {r : RecursorVal} (h1 : outEnv.find? n = some (.recInfo r))
    (h2 : c.env.find? n = none) : r ∈ B.rvals := by
  have hwf : c.env.constants.WF := Hc.map_wf
  have houtWF : outEnv.constants.WF := B.addInduct.wf hwf
  rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at h1
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at h2
  rcases B.addInduct.find? hwf h1 with hold | ⟨hmem, -⟩
  · rw [h2] at hold; cases hold
  · rcases AddInduct.mem_consts.1 hmem with ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨rval, hrval, h⟩
    · cases h
    · cases h
    · cases h; exact hrval

/-- **The installation boundary theorem**: the output of a nested restoration is a valid
checking environment with the environment-side facts of the restored block. The checking
invariant is the base translation extended by the restored declaration (`TrEnv'.induct`, the
declaration's `VInductDecl.WF` being `RestoredBlock.wf'`), its installed blocks the base's
complete ones extended by the new block (`InstalledBlocks.addInduct`, whose `hrecShapes` is
`RestoredBlock.recShapes`, auxiliary recursors included, and `hrecK` is `RestoredBlock.recK`).
WAVE 3 eqinst COMPAT: takes the base translation, its complete installed blocks and its
constructor parameter alignment (the caller has them from `VEnvs.WF`); `ContextWF` records the
checking invariant at the `.headers` stage only, which `InstalledBlocks.addInduct` cannot
extend. -/
theorem installedFacts (B : RestoredBlock L sourceTypes isUnsafe outEnv)
    (hsource : sourceTypes ≠ [])
    (hvisible : c.safety ≤ (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (htr : TrEnv c.safety c.env Hc.venv)
    (hblocks : InstalledBlocks c.safety c.env Hc.venv .complete)
    (hparams : ConstructorParameterAlignment c.safety c.env Hc.venv) :
    B.Installed := by
  have K := B.kernelFacts hsource
  have hwf : c.env.constants.WF := Hc.map_wf
  have wf' := B.wf' hsource
  have htrOut : TrEnv c.safety outEnv B.outVEnv := by
    unfold TrEnv; rw [B.quotInit_eq]; exact .induct wf' B.addInduct htr
  have hpres : ∀ {n ci}, c.env.find? n = some ci → outEnv.find? n = some ci := by
    intro n ci h
    have houtWF : outEnv.constants.WF := B.addInduct.wf hwf
    rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at h
    rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?]
    exact B.addInduct.find?_mono hwf h
  have hvis : c.safety ≤ (if B.decl.isUnsafe then DefinitionSafety.unsafe else .safe) := by
    rw [B.isUnsafe_eq]; exact hvisible
  have hblocks' : InstalledBlocks c.safety outEnv B.outVEnv .complete :=
    InstalledBlocks.addInduct hblocks hwf htrOut.toChecking hpres B.le K.inductInfosFromDecl
      B.cover K.closed K.constructorOwners (fun h1 h2 => K.recMajor h1 h2)
      (fun _ => ⟨wf', B.installed, B.compiledWF⟩) -- WAVE 3 COMPAT (lowering)
      (fun h => absurd hvis h)
      (fun _ => K.constructorParameterAlignment hparams)
      (fun h1 h2 _ => B.recK _ (B.newRec' h1 h2))
      (fun h1 h2 _ => B.recShapes _ (B.newRec' h1 h2))
  exact {
    checking := htrOut.toCheckingValid K.hasPrimitives K.safePrimitives hblocks'
    closed := K.closed
    constructorOwners := K.constructorOwners
    inductInfosFromDecl := K.inductInfosFromDecl
    cover := B.cover
    recMajor := K.recMajor
    constructorParameterAlignment := K.constructorParameterAlignment }

/-- A new constant of the output is one of the block's (`B.addInduct.find?`). -/
theorem newRec (B : RestoredBlock L sourceTypes isUnsafe outEnv) (I : B.Installed)
    {n : Name} {r : RecursorVal} (h1 : outEnv.find? n = some (.recInfo r))
    (h2 : c.env.find? n = none) : r ∈ B.rvals := by
  have hwf : c.env.constants.WF := Hc.map_wf
  have houtWF : outEnv.constants.WF := I.checking.tr.map_wf
  rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at h1
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at h2
  rcases B.addInduct.find? hwf h1 with hold | ⟨hmem, -⟩
  · rw [h2] at hold; cases hold
  · rcases AddInduct.mem_consts.1 hmem with ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨rval, hrval, h⟩
    · cases h
    · cases h
    · cases h; exact hrval

/-- **The block certificate of a restored block.** -/
def blockCertificate (B : RestoredBlock L sourceTypes isUnsafe outEnv) (I : B.Installed)
    (hsource : sourceTypes ≠ []) :
    BlockCertificate c.safety c.env Hc.venv B.decl outEnv B.outVEnv where
  wf := B.wf' hsource
  add := B.addInduct
  quotInit_eq := B.quotInit_eq
  checking := I.checking
  closed := I.closed
  constructorOwners := I.constructorOwners
  inductInfosFromDecl := I.inductInfosFromDecl
  cover := I.cover
  recMajor := I.recMajor
  constructorParameterAlignment := I.constructorParameterAlignment
  recK h1 h2 := B.recK _ (B.newRec I h1 h2)
  compiled := B.compiledWF
  newUnsafe ci hci := by rw [B.isUnsafe_eq]; exact B.newUnsafe ci hci
  recShapes h1 h2 := B.recShapes _ (B.newRec I h1 h2)

end RestoredBlock
end VerifyInductive
end Lean4Lean
