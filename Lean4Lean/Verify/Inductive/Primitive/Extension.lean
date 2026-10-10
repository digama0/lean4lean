import Lean4Lean.Verify.Inductive.Primitive.Run
import Lean4Lean.Verify.Inductive.Install.OrdinaryExtension

/-!
# The primitive inductive extension

The end of the primitive path of section 3.1 of the design notes: a successful run on `Bool` or
`Nat` yields well-formed models of the output that extend the source models, together with the
source judgment (`SourceAddInduct`, `addInductiveDeclaration.primitiveExtensionModelWF`).

Wave 2 scaffold: glue over `OrdinaryInstallation.extendSafeExact`; owned by the
`Install/`+`Primitive/`+`Prelude/` agent. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The primitive execution path retains its independent source judgment and
complete model of the output. -/
theorem PrimitiveRunResult.extendSafeWithSpecification {ves : VEnvs}
    {source : AddInductive.Context} {Hsource : ContextWF source}
    (Hrun : PrimitiveRunResult source Hsource nparams types outEnv)
    (wf : ves.WF source.env) (hsource : Hsource.venv = ves.venv .safe)
    (hsafety : source.safety = .safe) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      Nonempty (SourceAddInduct (ves.venv .safe)
        source.lparams nparams types (source.safety != .safe) (ves'.venv .safe)) := by
  obtain ⟨c', stats, Hc', P, Hshape, Hphases⟩ := Hrun
  have wf' : ves.WF c'.env := by rw [P.env_eq]; exact wf
  have hcSafety : c'.safety = .safe := P.safety_eq.trans hsafety
  have hvenv : Hc'.venv = ves.venv .safe := P.venv_eq.trans hsource
  have hproduction : (source.safety != .safe) = (c'.safety != .safe) := by rw [P.safety_eq]
  obtain ⟨ves', wf', hle, ⟨S⟩⟩ := OrdinaryInstallation.extendSafeExact Hphases wf' hcSafety
    hvenv hproduction Hshape.types_nonempty
  refine ⟨ves', wf', hle, ⟨?_⟩⟩
  rw [← P.lparams_eq]; simpa using S

/-- Complete primitive `AddInductive.run` refinement. -/
theorem AddInductive.run.primitiveExtensionModelWF {ves : VEnvs} {c : AddInductive.Context}
    {types : List InductiveType}
    (nparams numNested : Nat) (Hc : ContextWF c) (wf : ves.WF c.env)
    (hsource : Hc.venv = ves.venv .safe)
    (Hshape : PrimitiveInductiveShape c.lparams nparams types.toArray.toList (c.safety != .safe))
    (hallow : c.allowPrimitive = true) (hsafety : c.safety = .safe)
    (hctx : Hc.mlctx.vlctx = []) :
    (AddInductive.run nparams types numNested c).WF fun outEnv =>
      ∃ ves' : VEnvs, ves'.WF outEnv ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        Nonempty (SourceAddInduct (ves.venv .safe) c.lparams nparams types (c.safety != .safe)
          (ves'.venv .safe)) :=
  (AddInductive.run.primitiveSourceAlignedWF nparams numNested Hc wf.inductivesClosed
    wf.listedConstructorsPresent Hshape hallow hctx (by rw [hsafety]; decide)).mono
    fun _ Hrun => Hrun.extendSafeWithSpecification wf hsource hsafety

/-- Primitive post-lowering refinement. -/
theorem Environment.addInductiveAfterLowering.primitiveExtensionModelWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (res : ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WF env)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe)
    (htypes : res.types = types) (haux : res.aux2nested.size = 0) :
    (Environment.addInductiveAfterLowering env lparams nparams types isUnsafe
      true fuel res).WF fun outEnv =>
        ∃ ves' : VEnvs, ves'.WF outEnv ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          Nonempty (SourceAddInduct (ves.venv .safe) lparams nparams types isUnsafe
            (ves'.venv .safe)) := by
  have hisUnsafe : isUnsafe = false := Hshape.isUnsafe_eq
  subst hisUnsafe
  let c := primitiveAddInductiveContext env lparams false fuel
  let Hc : ContextWF c := ContextWF.initial wf .safe lparams true fuel
  have Hshape' : PrimitiveInductiveShape c.lparams nparams types.toArray.toList
      (c.safety != .safe) := by simpa [c, primitiveAddInductiveContext] using Hshape
  have Hrun := AddInductive.run.primitiveExtensionModelWF (c := c) (ves := ves) (types := types)
    nparams 0 Hc wf rfl Hshape' rfl rfl rfl
  unfold Environment.addInductiveAfterLowering
  rw [haux, htypes]
  simpa [c, primitiveAddInductiveContext] using Hrun

/-- End-to-end primitive refinement. -/
theorem Environment.addInductive.primitiveExtensionModelWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe) :
    (Environment.addInductive env lparams nparams types isUnsafe true fuel).WF
      fun outEnv =>
        ∃ ves' : VEnvs, ves'.WF outEnv ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          Nonempty (SourceAddInduct (ves.venv .safe) lparams nparams types isUnsafe
            (ves'.venv .safe)) := by
  refine Environment.addInductive.WF env lparams nparams types isUnsafe true fuel _
    fun res _ hres => ?_
  obtain ⟨htypes, haux⟩ := loweringRun.primitiveNoop env fuel.inductiveFuel lparams nparams
    types isUnsafe Hshape res hres
  exact Environment.addInductiveAfterLowering.primitiveExtensionModelWF env lparams nparams
    types isUnsafe fuel res ves wf Hshape htypes haux

end VerifyInductive
end Lean4Lean
