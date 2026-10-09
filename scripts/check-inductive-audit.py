#!/usr/bin/env python3
"""Audit the dependency closure of the verified theorems, including opaque bodies and types.

The roots are listed below (section 1.4 of the design notes). The default check
rejects axioms not listed in scripts/inductive-audit-inventory.json and sorry sources not
listed there as open proofs; --require-complete rejects every sorry dependency. The strict
roots (generator definitions and foundational lemmas) may use only the standard axioms.
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
    "Lean4Lean.addDecl.WF",
    "Lean4Lean.addDecl.WF_of_canonicalEq",
    "Lean4Lean.addDecl.WFHasCanonicalEq",
    "Lean4Lean.addDecl.WF_of_canonicalEq_mode",
    "Lean4Lean.addDecl.WF_mode",
    "Lean4Lean.addQuot.WF",
    "Lean4Lean.Replay.replayFresh.WF",
    "Lean4Lean.Replay.replayFresh.WF_target",
    "Lean4Lean.Replay.replayPure.WF_fromImports",
    "Lean4Lean.Replay.replayPure.WF_fromImports_mode",
    "Lean4Lean.Replay.Replayed.foldlM",
    "Lean4Lean.VEnv.QuotRegistered.propInhabitant_app",
    "Lean4Lean.VEnv.QuotPrefixUnfold.defeq",
    "Lean4Lean.VerifyInductive.addInductiveDeclaration.inductiveExtensionWF",
    "Lean4Lean.VerifyInductive.addInductiveDeclaration.primitiveInductiveExtensionWF",
    "Lean4Lean.VerifyInductive.Environment.addInductiveAfterLowering.nestedInductiveExtensionWF",
    "Lean4Lean.TypeChecker.whnf.WF",
    "Lean4Lean.TypeChecker.Inner.reduceRecursor.WF",
    "Lean4Lean.VEnv.NormalEq.parRed",
    "Lean4Lean.VerifyInductive.RecursorConstruction.typeTranslations",
    "Lean4Lean.VEnv.PrefixUnfold.defeq",
    "Lean4Lean.VEnv.IsDefEq.full_church_rosser",
}
DEFINITION_ROOTS = {
    "Lean4Lean.QuotPrefixUnfolding.propInhabitant",
    "Lean4Lean.QuotPrefixUnfolding.generate",
    "Lean4Lean.VEnv.QuotRegistered",
    "Lean4Lean.VEnv.QuotPrefixUnfold",
    "Lean4Lean.VEnv.DefinitionRegistered",
    "Lean4Lean.VEnv.DefinitionPattern",
    "Lean4Lean.VEnv.installDefinitions",
    "Lean4Lean.InductiveSignature.RecursorData.compilationEntries",
    "Lean4Lean.InductiveSignature.RecursorData.installEntries",

    "Lean.Level.paramsIn",
    "Lean.Expr.levelParamsIn",
    "Lean4Lean.InductiveSignature.TrRestoredCompilation",
    "Lean4Lean.InductiveSignature.Restoration.expr",
    "Lean4Lean.CompiledInductive",
    "Lean4Lean.InductiveSignature.Instance.equation",
    "Lean4Lean.InductiveSignature.Compiles",
    "Lean4Lean.InductiveSignature.TrRecursorVal",
    "Lean4Lean.InductiveSignature.TrCompilation",
    "Lean4Lean.InductiveSignature.CaseSchema.ofCompilation",
    "Lean4Lean.InductiveSignature.CaseSchema.Certified",
    "Lean4Lean.InductiveSignature.CaseSchema.genericEquations",
    "Lean4Lean.InductiveSignature.CaseSchema.genericProjectionPrefix",
    "Lean4Lean.InductiveSignature.CaseSchema.Generates",
    "Lean4Lean.VEnv.CaseRedex",
    "Lean4Lean.VEnv.HeadParallelReduction",
    "Lean4Lean.InductiveSignature.CaseSchema.singletonReconstruction",
    "Lean4Lean.InductiveSignature.CaseSchema.singletonReconstructAt",
    "Lean4Lean.InductiveSignature.RecursorData.singletonEquation",
    "Lean4Lean.VEnv.RecursorRegistered",
    "Lean4Lean.VEnv.PatternReductionTrace",
    "Lean4Lean.VEnv.PrefixUnfold",
    "Lean4Lean.VEnv.FullStep",
    "Lean4Lean.VEnv.FullReduction",
    "Lean4Lean.VEnv.FullEquationCoverage",
    "Lean4Lean.InductiveSignature.CaseSchema.structureEta",
    "Lean4Lean.InductiveSignature.RecursorData.prefixUnfolding",
    "Lean4Lean.VEnv.WF.params",
}
# Foundational lemmas whose proofs may use only the standard axioms and no open proof.
FOUNDATION_ROOTS = {
    "Lean4Lean.VEnv.IsDefEq.strong",
    "Lean4Lean.VEnv.IsDefEqStrong.subst",
    "Lean4Lean.VEnv.IsDefEq.transport_bvar",
    "Lean4Lean.VEnv.ConstructorCaptureReplay.transport",
    "Lean4Lean.VEnv.HasType.etaOpen_wf",
    "Lean4Lean.VEnv.HasType.etaOpen_defeq",
    "Lean4Lean.VEnv.IsDefEq.etaOpen_wrapLams",
    # The confluence theorem for every well-formed environment with canonical `Eq`
    # (section 4.2 of the design notes) and its two coverage lemmas.
    "Lean4Lean.VEnv.WF.church_rosser",
    "Lean4Lean.VEnv.WF.equationCoverage",
    "Lean4Lean.VEnv.WF.singletonCoverage",
}
STRICT_ROOTS = DEFINITION_ROOTS | FOUNDATION_ROOTS
ROOTS |= STRICT_ROOTS


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


def self_test():
    source = (ROOT / "scripts/InductiveAudit.lean").read_text()
    source = "import Lean\n" + "\n".join(
        line for line in source.splitlines() if not line.startswith("import "))
    source = source.split("\n#inductive_audit Lean4Lean.", 1)[0]
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
    print("Audit self-test passed: opaque bodies, types, paths, and clean proofs.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-complete", action="store_true")
    parser.add_argument("--no-build", action="store_true", help="use already-built dependencies")
    parser.add_argument("--json", type=Path, help="write full dependency paths to this file")
    parser.add_argument("--self-test", action="store_true", help="test the auditor and exit")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return 0
    if not args.no_build:
        subprocess.run(["lake", "build", "Lean4Lean.Verify.Inductive.Dispatch",
                        "Lean4Lean.Verify.TypeChecker",
                        "Lean4Lean.Verify.Inductive.Recursor.Entries.TrRecursorVal",
                        "Lean4Lean.Verify.Inductive.Nested.Restoration.TrRestoredRecursorVal",
                        "Lean4Lean.Theory.Inductive.CaseRegistration",
                        "Lean4Lean.Theory.Inductive.CaseProjections",
                        "Lean4Lean.Theory.Typing.CaseReduction",
                        "Lean4Lean.Theory.Typing.PrefixUnfolding.Rule",
                        "Lean4Lean.Theory.Typing.FullChurchRosser",
                        "Lean4Lean.Theory.Typing.Confluence.WFParams",
                        "Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLift",
                        "Lean4Lean.Theory.Typing.QuotPropInhabitant",
                        "Lean4Lean.Theory.Typing.DefinitionRegistryInstallation",
                        "Lean4Lean.Theory.Typing.RecursorRegistryInstallation",

                        "Lean4Lean.Theory.Typing.ChurchRosser",
                        "Lean4Lean.Verify.Replay"], cwd=ROOT, check=True)
    reports = run_audit(ROOT / "scripts/InductiveAudit.lean")
    if len(reports) != len(ROOTS) or {r["root"] for r in reports} != ROOTS:
        raise RuntimeError("audit roots changed or a theorem report is missing")
    if args.json:
        args.json.write_text(json.dumps(reports, indent=2) + "\n")
    inventory = json.loads((ROOT / "scripts/inductive-audit-inventory.json").read_text())
    allowed = set(inventory["standardAxioms"]) | set(inventory["implementationAxioms"])
    known_sorries = set(inventory["openProofs"])
    failed = False
    for report in reports:
        sorries = {d["name"] for d in report["sorrySources"]}
        axioms = {d["name"] for d in report["axioms"]}
        print(f'{report["root"]}: {len(sorries)} open proofs, {len(axioms - {"sorryAx"})} other axioms')
        permitted = (set(inventory["standardAxioms"])
                     if report["root"] in STRICT_ROOTS else allowed)
        for dependency in report["axioms"]:
            name = dependency["name"]
            if name != "sorryAx" and name not in permitted:
                failed = True
                print("  UNLISTED AXIOM: " + " -> ".join(dependency["path"]))
        for dependency in report["sorrySources"]:
            name = dependency["name"]
            if (name not in known_sorries or args.require_complete
                    or report["root"] in STRICT_ROOTS):
                failed = True
                print("  OPEN PROOF: " + " -> ".join(dependency["path"]))
        if args.require_complete and "sorryAx" in axioms:
            failed = True
    if failed:
        print("Inductive dependency audit FAILED.", file=sys.stderr)
        return 1
    count = len({d["name"] for r in reports for d in r["sorrySources"]})
    print(f"Migration inventory matches; {count} distinct proof obligations remain."
          if count else "No sorry dependencies; all remaining axioms are listed.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (RuntimeError, subprocess.CalledProcessError, AssertionError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
