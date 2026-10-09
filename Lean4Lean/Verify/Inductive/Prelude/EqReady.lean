import Lean4Lean.Verify.Inductive.Install.Environments
import Lean4Lean.Verify.Environment.Extension

/-! # Canonical `Eq` in the safety-indexed models

The invariants that the prelude's `Eq` declaration establishes (`QuotReadyEnvs`) and that
hold on either side of it (`QuotReadyOrEqAbsent`); `Prelude/Eq.lean` proves them for that
declaration. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Abstract `Eq` with its canonical type is available in every safety-indexed model
(`QuotReady` at every safety level). This is the invariant needed after the prelude's `Eq`
declaration and before quotient initialization. -/
def QuotReadyEnvs (ves : VEnvs) : Prop :=
  ∀ safety, (ves.venv safety).QuotReady

/-- Either `Eq` is absent from the kernel environment (before the prelude's `Eq`
declaration), or every safety-indexed model contains abstract `Eq` with its canonical type
(`QuotReadyEnvs`). This disjunction holds both before and after the `Eq` declaration. -/
def QuotReadyOrEqAbsent (env : Environment) (ves : VEnvs) : Prop :=
  env.constants.find? ``Eq = none ∨ QuotReadyEnvs ves

theorem QuotReadyOrEqAbsent.ofCanonical
    (H : QuotReadyEnvs ves) : QuotReadyOrEqAbsent env ves :=
  Or.inr H

theorem QuotReadyEnvs.mono
    (H : QuotReadyEnvs ves)
    (hle : ∀ safety, ves.venv safety ≤ target.venv safety) :
    QuotReadyEnvs target := by
  intro safety
  exact (hle safety).constants (H safety)

end VerifyInductive
end Lean4Lean
