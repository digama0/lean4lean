import Lean4Lean.Verify.Inductive.Install.BlockCertificate

/-! The complete ordinary checker (`AddInductive.runWithStats`, `AddInductive.run`) refines a
skeleton-free result (`OrdinaryInstallation`, `OrdinaryRunResult`): the declaration is the one
synthesized by the successful header and constructor traversals, and the same declaration is
carried through the recursor check and the rules.

Wave 2 scaffold: the glue below composes the three boundary theorems of the header,
constructor and recursor phases; owned by the `Install/` agent. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Complete post-analysis result when the declaration is synthesized by the successful header
and constructor traversals rather than fixed before execution. -/
def OrdinaryInstallation
    (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (nparams depth : Nat) (indTypes : Array InductiveType)
    (isUnsafe : Bool) (sourceEnv : VEnv) (outEnv : Environment) : Prop :=
  ∃ decl ctorEnv,
    -- WAVE 2 install COMPAT: indexed by the recursor phase's input
    ∃ R : RecursorInput c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv,
      Nonempty (RecursorCheck R outEnv)

/-- Complete ordinary `runWithStats` refinement: the constructor phase's declaration is carried
through the recursor phase. -/
theorem AddInductive.runWithStats.WF
    {c c' : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
    {indTypes : Array InductiveType} {Hc' : ContextWF c'} {stats : AddInductive.InductiveStats}
    (P : HeaderPhase Hc nparams indTypes c' Hc' stats) (numNested : Nat) (isUnsafe : Bool)
    (hvisible : c'.safety ≤ (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hsourceSafety : isUnsafe = (c'.safety != .safe))
    (hnotPartial : c'.safety ≠ .partial)
    (hnprimTypes : c'.allowPrimitive = true → ∀ info ∈
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested isUnsafe c'.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name)
    (hnprimCtors : c'.allowPrimitive = true →
      ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors,
      ¬ Kernel.Environment.primitives.contains ctor.name)
    (hnprimRecursors : c'.allowPrimitive = true →
      ∀ owner (_howner : owner < indTypes.size),
      ¬ Kernel.Environment.primitives.contains (Lean.mkRecName indTypes[owner]!.name))
    (hlparams : c'.lparams.Nodup)
    (hclosed : MutualInductivesClosed c'.env)
    (hpresent : ListedConstructorsPresent c'.env) :
    (AddInductive.runWithStats stats nparams indTypes numNested isUnsafe c').WF
      (OrdinaryInstallation c' stats nparams P.depth indTypes isUnsafe Hc'.venv) := by
  unfold AddInductive.runWithStats
  refine AddInductive.M.WF_bind
    (AddInductive.constructorPhase.WF P numNested isUnsafe hvisible hnprimTypes hnprimCtors
      hlparams hclosed hpresent) fun out Hout => ?_
  obtain ⟨ctorEnv, positivity⟩ := out
  -- WAVE 2 COMPAT (ctor): `constructorPhase.WF` returns one constructor check with the
  -- returned classification (`∃ R, R.classes = out.2`).
  obtain ⟨decl, -, R, hclasses⟩ := Hout
  exact (R.toRecursorInput.recursorPhasesWF hlparams hsourceSafety hnotPartial hnprimRecursors
    hclasses.symm).mono fun outEnv Hrec => ⟨decl, ctorEnv, R.toRecursorInput, Hrec⟩

/-- Remaining environment-wide contracts at the post-header boundary: with the primitive
exception enabled, none of the names the block installs is a primitive. -/
structure PrimitiveNamesFresh
    (c : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (nparams numNested : Nat) (indTypes : Array InductiveType)
    (isUnsafe : Bool) : Prop where
  freshTypes : c.allowPrimitive = true → ∀ info ∈
    (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
      isUnsafe c.lparams).toList,
    ¬ Kernel.Environment.primitives.contains info.name
  freshConstructors : c.allowPrimitive = true →
    ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors,
    ¬ Kernel.Environment.primitives.contains ctor.name
  freshRecursors : c.allowPrimitive = true →
    ∀ owner (_howner : owner < indTypes.size),
    ¬ Kernel.Environment.primitives.contains
      (Lean.mkRecName indTypes[owner]!.name)

theorem PrimitiveNamesFresh.ofAllowPrimitiveFalse
    (h : c.allowPrimitive = false) :
    PrimitiveNamesFresh c stats nparams numNested indTypes isUnsafe where
  freshTypes h' := by rw [h] at h'; cases h'
  freshConstructors h' := by rw [h] at h'; cases h'
  freshRecursors h' := by rw [h] at h'; cases h'

/-- Source-aligned declaration-facing result of the complete ordinary checker: a header phase
from the source context, and the ordinary installation in the resulting context. -/
def OrdinaryRunResult
    (source : AddInductive.Context) (Hsource : ContextWF source) (nparams : Nat)
    (types : List InductiveType) (outEnv : Environment) : Prop :=
  ∃ c' stats, ∃ Hc' : ContextWF c',
    ∃ P : HeaderPhase Hsource nparams types.toArray c' Hc' stats,
      OrdinaryInstallation c' stats nparams P.depth types.toArray (source.safety != .safe)
        Hc'.venv outEnv

theorem Kernel.Environment.checkDuplicatedUnivParams.WF (lparams : List Name) :
    (Kernel.Environment.checkDuplicatedUnivParams lparams).WF (fun _ => lparams.Nodup) := by
  induction lparams with
  | nil =>
    intro out hout
    cases hout
    trivial
  | cons param lparams ih =>
    by_cases hmem : param ∈ lparams
    · rw [Kernel.Environment.checkDuplicatedUnivParams]
      simp only [hmem, if_pos]
      exact Except.WF.throw
    · simpa [Kernel.Environment.checkDuplicatedUnivParams, hmem] using
        ih.mono fun _ htail => List.nodup_cons.mpr ⟨hmem, htail⟩

/-- The complete executable ordinary checker refines a skeleton-free semantic result. -/
theorem AddInductive.run.sourceAlignedWF
    {c : AddInductive.Context} {types : List InductiveType}
    (nparams numNested : Nat) (Hc : ContextWF c)
    (Hclosed : MutualInductivesClosed c.env)
    (Hpresent : ListedConstructorsPresent c.env)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < types.toArray.size)
    (HnotPartial : c.safety ≠ .partial)
    (Hinputs : ∀ {c' : AddInductive.Context} {stats : AddInductive.InductiveStats},
      (Hc' : ContextWF c') → HeaderPhase Hc nparams types.toArray c' Hc' stats →
      PrimitiveNamesFresh c' stats nparams numNested types.toArray (c.safety != .safe)) :
    (AddInductive.run nparams types numNested c).WF (OrdinaryRunResult c Hc nparams types) := by
  show (Kernel.Environment.checkDuplicatedUnivParams c.lparams >>= fun _ =>
      AddInductive.checkInductiveTypes nparams types.toArray (fun stats =>
        AddInductive.runWithStats stats nparams types.toArray numNested (c.safety != .safe))
        c).WF _
  refine Except.WF.bind (Kernel.Environment.checkDuplicatedUnivParams.WF c.lparams)
    fun _ hnodup => ?_
  refine AddInductive.checkInductiveTypes.WF _ _ Hc hctx hnonempty fun {c' stats} Hc' P => ?_
  have I := Hinputs Hc' P
  have hvisible : c'.safety ≤ (if (c.safety != .safe) then DefinitionSafety.unsafe else .safe) := by
    rw [P.safety_eq]
    cases h : c.safety with
    | «unsafe» => simp
    | safe => simp
    | «partial» => exact (HnotPartial h).elim
  have hsafety : (c.safety != .safe) = (c'.safety != .safe) := by rw [P.safety_eq]
  refine (AddInductive.runWithStats.WF P numNested (c.safety != .safe) hvisible hsafety
    (by rw [P.safety_eq]; exact HnotPartial) I.freshTypes I.freshConstructors I.freshRecursors
    (by rw [P.lparams_eq]; exact hnodup) (by rw [P.env_eq]; exact Hclosed)
    (by rw [P.env_eq]; exact Hpresent)).mono fun outEnv Hrun => ?_
  exact ⟨c', stats, Hc', P, Hrun⟩

end VerifyInductive
end Lean4Lean
