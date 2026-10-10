import Lean4Lean.Verify.Inductive.Install.Ordinary
import Lean4Lean.Verify.Inductive.Nested.Lowering.Basic

/-! # The lowered run

The nested branch of `addInductiveAfterLowering` first runs the ordinary pipeline
(`AddInductive.run`) on the lowered block `res.types`; `LoweredRun` is that run's data, as the
restoration certificates index it: the header phase from the source context, the recursor
input (the constructor phase's output: the lowered declaration `loweredDecl`, its header and
constructor stages) and the recursor check (the generated recursors with their rules, the
generator `signature`/`generation`, the recursor-stage model `outVEnv`). It is
`OrdinaryRunResult` with its existentials opened (`OrdinaryRunResult.toLoweredRun`), and
`AddInductive.run.loweredRun` runs the ordinary pipeline for it (shared interface, proved). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The ordinary pipeline's run on the lowered block, from the source context `c`. -/
structure LoweredRun {c : AddInductive.Context} (Hc : ContextWF c) (nparams : Nat)
    (indTypes : Array InductiveType) (loweredEnv : Environment) where
  c' : AddInductive.Context
  stats : AddInductive.InductiveStats
  Hc' : ContextWF c'
  phase : HeaderPhase Hc nparams indTypes c' Hc' stats
  /-- The lowered declaration: the source families (constructors lowered) and the auxiliary
  families, with its generated recursors added by `recursors.recs` (`RecursorCheck.decl'`). -/
  loweredDecl : VInductDecl
  ctorEnv : Environment
  input : RecursorInput c' stats loweredDecl nparams (c.safety != .safe) phase.depth Hc'.venv
    indTypes ctorEnv
  recursors : RecursorCheck input loweredEnv

namespace LoweredRun

variable {c : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
  {indTypes : Array InductiveType} {loweredEnv : Environment}

/-- The rule translations of the lowered run (the rule phase's boundary theorem). -/
def rules (L : LoweredRun Hc nparams indTypes loweredEnv) : RuleTranslations L.recursors :=
  L.recursors.generatedRuleTranslation

theorem env_eq (L : LoweredRun Hc nparams indTypes loweredEnv) : L.c'.env = c.env :=
  L.phase.env_eq

theorem safety_eq (L : LoweredRun Hc nparams indTypes loweredEnv) : L.c'.safety = c.safety :=
  L.phase.safety_eq

theorem lparams_eq (L : LoweredRun Hc nparams indTypes loweredEnv) : L.c'.lparams = c.lparams :=
  L.phase.lparams_eq

theorem venv_eq (L : LoweredRun Hc nparams indTypes loweredEnv) : L.Hc'.venv = Hc.venv :=
  L.phase.venv_eq

/-- The lowered declaration with its generated recursors, as installed by the lowered run. -/
def decl' (L : LoweredRun Hc nparams indTypes loweredEnv) : VInductDecl :=
  L.recursors.decl'

end LoweredRun

/-- An ordinary run result is a lowered run. -/
theorem OrdinaryRunResult.toLoweredRun {c : AddInductive.Context} {Hc : ContextWF c}
    {nparams : Nat} {types : List InductiveType} {outEnv : Environment}
    (H : OrdinaryRunResult c Hc nparams types outEnv) :
    Nonempty (LoweredRun Hc nparams types.toArray outEnv) := by
  obtain ⟨c', stats, Hc', P, decl, ctorEnv, R, ⟨Hrec⟩⟩ := H
  exact ⟨⟨c', stats, Hc', P, decl, ctorEnv, R, Hrec⟩⟩

/-- The ordinary pipeline on the lowered block of a nested declaration yields a lowered run
(from `AddInductive.run.sourceAlignedWF`; the primitive exception is off). -/
theorem AddInductive.run.loweredRun {c : AddInductive.Context} (Hc : ContextWF c)
    (nparams numNested : Nat) (types : List InductiveType)
    (Hclosed : MutualInductivesClosed c.env) (Hpresent : ListedConstructorsPresent c.env)
    (hctx : Hc.mlctx.vlctx = []) (hnonempty : 0 < types.toArray.size)
    (HnotPartial : c.safety ≠ .partial) (hallow : c.allowPrimitive = false) :
    (AddInductive.run nparams types numNested c).WF fun loweredEnv =>
      Nonempty (LoweredRun Hc nparams types.toArray loweredEnv) :=
  (AddInductive.run.sourceAlignedWF nparams numNested Hc Hclosed Hpresent hctx hnonempty
    HnotPartial fun _ P =>
      PrimitiveNamesFresh.ofAllowPrimitiveFalse (P.allowPrimitive_eq.trans hallow)).mono
    fun _ H => H.toLoweredRun

end VerifyInductive
end Lean4Lean
