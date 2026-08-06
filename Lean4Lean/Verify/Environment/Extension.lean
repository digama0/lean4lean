import Lean4Lean.Verify.Environment

/-!
Compatibility entry point for the environment-extension verification.

PR #32 extends and supersedes the split extension layer from PR #28 in the
parent `Lean4Lean.Verify.Environment` module. Re-exporting that module here
keeps the split module path buildable without maintaining two incompatible
copies of the environment model and conservation proofs.
-/
