#!/usr/bin/env python3
"""Audit the dependency closure of the verified theorems, including opaque bodies and types.

The roots are listed below. Every axiom a root reaches must be listed in
scripts/inductive-audit-inventory.json; the strict roots (generator definitions, foundational
lemmas) may use only the standard axioms. Every `sorry` a root reaches must come from a declaration listed there as an
accepted open proof (`openProofs`). A strict root may reach no `sorry` at all, except the open
proofs the inventory accepts for that root by name (`acceptedUnder`). With --require-complete
the inventory must also be exact: every accepted open proof must still be reached by some root,
and every open proof accepted under a strict root must still be reached by that root, so that
closing a proof forces its removal from the lists.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MARKER = "INDUCTIVE_AUDIT "
ROOTS = {
    "Lean4Lean.addQuot.WF",
    "Lean4Lean.VerifyInductive.addInductiveDeclaration.preserves",
    "Lean4Lean.VerifyInductive.Environment.addInductive.inductiveExtensionWF",
    "Lean4Lean.VerifyInductive.Environment.addInductive.primitiveInductiveExtensionWF",
    "Lean4Lean.TypeChecker.whnf.WF",
    "Lean4Lean.TypeChecker.Inner.reduceRecursor.WF",
    "Lean4Lean.VerifyInductive.RecursorConstruction.typeTranslations",
    "Lean4Lean.addDecl.preludeEq_hasCanonicalEq",
}
DEFINITION_ROOTS = {
    "Lean4Lean.VEnv.DefinitionRegistered",
    "Lean4Lean.VEnv.DefinitionPattern",
    "Lean4Lean.InductiveSignature.RecursorData.compilationEntries",
    "Lean.Level.paramsIn",
    "Lean.Expr.levelParamsIn",
    "Lean4Lean.InductiveSignature.Restoration.expr",
    "Lean4Lean.CompiledInductive",
    "Lean4Lean.InductiveSignature.Instance.equation",
    "Lean4Lean.InductiveSignature.Compiles",
    "Lean4Lean.InductiveSignature.TrRecursorVal",
    "Lean4Lean.InductiveSignature.RecursorData.singletonEquation",
    "Lean4Lean.VEnv.RecursorRegistered",
    "Lean4Lean.VEnv.HasCanonicalEq",
}
# Foundational lemmas.
FOUNDATION_ROOTS = {
    "Lean4Lean.VEnv.IsDefEq.strong",
    "Lean4Lean.VEnv.IsDefEqStrong.subst",
    "Lean4Lean.VEnv.IsDefEq.transport_bvar",
    "Lean4Lean.VEnv.ConstructorCaptureReplay.transport",
    "Lean4Lean.VEnv.HasType.etaOpen_wf",
    "Lean4Lean.VEnv.HasType.etaOpen_defeq",
    "Lean4Lean.VEnv.IsDefEq.etaOpen_wrapLams",
}
STRICT_ROOTS = DEFINITION_ROOTS | FOUNDATION_ROOTS
ROOTS |= STRICT_ROOTS
BUILD_TARGETS = [
    "Lean4Lean.Verify.Inductive.Dispatch",
    "Lean4Lean.Verify.Environment",
    "Lean4Lean.Verify.TypeChecker",
    "Lean4Lean.Verify.CanonicalEq",
    "Lean4Lean.Theory.Typing.RecursorRegistryInstallation",
    "Lean4Lean.Theory.Typing.ConstructorCaptureTransport",
]


def run_audit(path):
    proc = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                          text=True, capture_output=True)
    if proc.returncode:
        sys.stderr.write(proc.stdout + proc.stderr)
        raise RuntimeError("Lean dependency audit failed")
    reports = [json.loads(line[len(MARKER):]) for line in proc.stdout.splitlines()
               if line.startswith(MARKER)]
    if not reports:
        raise RuntimeError("Lean dependency audit produced no reports")
    return reports


def check_reports(reports, inventory, strict_roots, require_complete, log=lambda _: None):
    """Check the audit reports against the inventory. Returns the failure messages and the set
    of open proofs reached."""
    standard = set(inventory["standardAxioms"])
    allowed = standard | set(inventory["implementationAxioms"])
    accepted = set(inventory["openProofs"])
    accepted_under = {root: set(names)
                      for root, names in inventory.get("acceptedUnder", {}).items()}
    failures = []
    for root, names in sorted(accepted_under.items()):
        if root not in strict_roots:
            failures.append(f"acceptedUnder lists {root}, which is not a strict root")
        for name in sorted(names - accepted):
            failures.append(f"acceptedUnder[{root}] lists {name}, which is not in openProofs")
    reached = set()
    for report in reports:
        root = report["root"]
        sorries = {d["name"] for d in report["sorrySources"]}
        reached |= sorries
        axioms = {d["name"] for d in report["axioms"]}
        log(f'{root}: {len(sorries)} open proofs, {len(axioms - {"sorryAx"})} axioms besides sorryAx')
        strict = root in strict_roots
        permitted = standard if strict else allowed
        for dependency in report["axioms"]:
            name = dependency["name"]
            if name != "sorryAx" and name not in permitted:
                failures.append("  UNLISTED AXIOM: " + " -> ".join(dependency["path"]))
        for dependency in report["sorrySources"]:
            name = dependency["name"]
            if name not in accepted:
                failures.append("  OPEN PROOF NOT ACCEPTED: " + " -> ".join(dependency["path"]))
            elif strict and name not in accepted_under.get(root, set()):
                failures.append("  OPEN PROOF UNDER A STRICT ROOT, NOT IN acceptedUnder: "
                                + " -> ".join(dependency["path"]))
        if "sorryAx" in axioms and not sorries:
            failures.append(f"  {root}: sorryAx reached without a recorded source")
        if require_complete and strict:
            for name in sorted(accepted_under.get(root, set()) - sorries):
                failures.append(f"acceptedUnder[{root}] lists {name}, which it no longer "
                                "reaches (remove it from the inventory)")
    if require_complete:
        for name in sorted(accepted - reached):
            failures.append("ACCEPTED OPEN PROOF NO LONGER REACHED (remove it from the "
                            "inventory): " + name)
    return failures, reached


def self_test():
    source = (ROOT / "scripts/InductiveAudit.lean").read_text()
    source = "import Lean\n" + "\n".join(
        line for line in source.splitlines() if not line.startswith("import "))
    source = source.split("\n#inductive_audit ", 1)[0]
    source += """
namespace AuditSelfTest
axiom typeDependency : Prop
axiom assumed : typeDependency
theorem throughType : typeDependency := assumed
opaque hidden : True := by sorry
theorem throughOpaque : True := hidden
theorem clean : True := True.intro
end AuditSelfTest
#inductive_audit AuditSelfTest.throughType
#inductive_audit AuditSelfTest.throughOpaque
#inductive_audit AuditSelfTest.clean
"""
    with tempfile.TemporaryDirectory(prefix="inductive-audit-") as directory:
        path = Path(directory) / "AuditSelfTest.lean"
        path.write_text(source)
        reports = {r["root"]: r for r in run_audit(path)}
    opaque = reports["AuditSelfTest.throughOpaque"]
    assert any(d["name"] == "AuditSelfTest.hidden" and
               d["path"] == ["AuditSelfTest.throughOpaque", "AuditSelfTest.hidden"]
               for d in opaque["sorrySources"]), "missed an opaque sorry body"
    typed = reports["AuditSelfTest.throughType"]
    assert {d["name"] for d in typed["axioms"]} == {
        "AuditSelfTest.typeDependency", "AuditSelfTest.assumed"}, "missed a type dependency"
    clean = reports["AuditSelfTest.clean"]
    assert not clean["axioms"] and not clean["sorrySources"], "false positive on a clean proof"
    check_self_test()
    print("Audit self-test passed: opaque bodies, types, paths, clean proofs, and the "
          "per-root acceptance of open proofs under strict roots.")


def check_self_test():
    """The acceptance rules of `check_reports` on synthetic reports."""
    def report(root, sorries):
        return {"root": root,
                "axioms": [{"name": "sorryAx", "path": [root, "sorryAx"]}] if sorries else [],
                "sorrySources": [{"name": n, "path": [root, n]} for n in sorries]}
    inventory = {"standardAxioms": [], "implementationAxioms": [],
                 "openProofs": ["open.a", "open.b"],
                 "acceptedUnder": {"strict.r": ["open.a"]}}
    strict = {"strict.r", "strict.clean"}

    def failures(reports, require_complete=True, inv=inventory):
        return check_reports(reports, inv, strict, require_complete)[0]
    base = [report("loose.r", ["open.a", "open.b"]), report("strict.r", ["open.a"]),
            report("strict.clean", [])]
    assert not failures(base), "rejected an inventory that matches"
    assert failures([report("loose.r", ["open.a", "open.c"])] + base[1:]), \
        "accepted an unlisted open proof"
    assert failures([base[0], report("strict.r", ["open.a", "open.b"]), base[2]]), \
        "accepted, under a strict root, an open proof not listed for that root"
    assert failures(base[:2] + [report("strict.clean", ["open.a"])]), \
        "accepted an open proof under a strict root with no acceptedUnder entry"
    assert failures([base[0], report("strict.r", []), base[2]]), \
        "--require-complete accepted a stale acceptedUnder entry"
    assert not failures([base[0], report("strict.r", []), base[2]], require_complete=False), \
        "a stale acceptedUnder entry failed without --require-complete"
    assert failures([report("loose.r", ["open.a"])] + base[1:]), \
        "--require-complete accepted a stale openProofs entry"
    assert failures(base, inv=dict(inventory, acceptedUnder={"loose.r": ["open.a"]})), \
        "accepted an acceptedUnder entry for a root that is not strict"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-complete", action="store_true",
                        help="also reject accepted open proofs (globally or under a strict root) that are no longer reached")
    parser.add_argument("--no-build", action="store_true", help="use already-built dependencies")
    parser.add_argument("--json", type=Path, help="write full dependency paths to this file")
    parser.add_argument("--self-test", action="store_true", help="test the auditor and exit")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return 0
    if not args.no_build:
        subprocess.run(["lake", "build", *BUILD_TARGETS], cwd=ROOT, check=True)
    reports = run_audit(ROOT / "scripts/InductiveAudit.lean")
    if len(reports) != len(ROOTS) or {r["root"] for r in reports} != ROOTS:
        raise RuntimeError("audit roots changed or a theorem report is missing")
    if args.json:
        args.json.write_text(json.dumps(reports, indent=2) + "\n")
    inventory = json.loads((ROOT / "scripts/inductive-audit-inventory.json").read_text())
    failures, reached = check_reports(reports, inventory, STRICT_ROOTS, args.require_complete,
                                      log=print)
    for line in failures:
        print(line)
    if failures:
        print("Inductive dependency audit FAILED.", file=sys.stderr)
        return 1
    if reached:
        print(f"Inventory matches; {len(reached)} accepted open proofs remain: "
              + ", ".join(sorted(reached)))
    else:
        print("No sorry dependencies; all remaining axioms are listed.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (RuntimeError, subprocess.CalledProcessError, AssertionError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
