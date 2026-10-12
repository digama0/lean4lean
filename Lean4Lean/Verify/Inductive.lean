import Lean4Lean.Verify.Inductive.Basic
import Lean4Lean.Verify.Inductive.Context
import Lean4Lean.Verify.Inductive.Formation
import Lean4Lean.Verify.Inductive.Header.Check
import Lean4Lean.Verify.Inductive.Header.Installation
import Lean4Lean.Verify.Inductive.Constructor.CheckedTail
import Lean4Lean.Verify.Inductive.Constructor.Check

/-!
# Verification of inductive declarations

Collects the verification of the executable inductive checker (`Lean4Lean/Verify/Inductive/`):
headers, constructors, recursors and rules, block installation, primitive
families and the dispatch over the executable's branches, and
the nested branch (`Nested/**`: the lowering certificate, the lowered run, the restoration
steps and the restored block certificate, `nestedInductiveExtensionWF`). The pipeline is
described in `Inductive/README.md`; the open proofs are listed in
`scripts/inductive-audit-inventory.json`.
-/
