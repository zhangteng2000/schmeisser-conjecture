"""Pure validation tests: no Lean, external command, or ZIP is created."""
import copy
import json
from pathlib import Path
import sys
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
import package_verified_source as package


def example_report(mode="sequential"):
    order = ["Schmeisser.Main", "Schmeisser"]
    tails = [("pinned-lean-version", ["env", "lean", "--version"])]
    if mode == "sequential":
        tails += [(name, ["build", name]) for name in order]
    else:
        tails += [("preflight-rehash-entry-points", ["--rehash", "--no-build", "build", *order]),
                  ("preflight-rehash-default", ["--rehash", "--no-build", "build"])]
    tails += [("final-rehash-entry-points", ["--rehash", "build", *order]),
              ("final-rehash-build", ["--rehash", "build"]),
              ("final-axiom-gate", ["env", "lean", "reports/AxiomGate.lean"])]
    return {"verification_mode": mode,
            "commands": [{"label": label, "argv": ["lake", *tail], "returncode": 0,
                           "started_utc": "fixture", "finished_utc": "fixture"}
                          for label, tail in tails]}, order


class PackageValidationTests(unittest.TestCase):
    def test_public_entrypoint_must_import_main(self):
        for sources in ({}, {"Schmeisser": {"imports": ["Schmeisser.Basic"]}}):
            with self.subTest(sources=sources), self.assertRaises(package.PackageError):
                package.require_public_main(SimpleNamespace(sources=sources))
        package.require_public_main(SimpleNamespace(
            sources={"Schmeisser": {"imports": ["Schmeisser.Basic", "Schmeisser.Main"]}}))

    def test_unverified_reports_rejected_before_project_read(self):
        for status in ("running", "failed", "plan_only_not_verified", None):
            payload = json.dumps({"status": status}).encode()
            with patch.object(Path, "read_bytes", return_value=payload), \
                 patch.object(package.verifier, "make_plan", side_effect=AssertionError("Project read too early")), \
                 self.assertRaises(package.PackageError):
                package.prepare(Path("."), Path("report.json"), False)

    def test_complete_command_shape(self):
        report, order = example_report()
        self.assertIn("final-axiom-gate", package.validate_commands(report, order, order))

    def test_aggregate_requires_both_real_preflight_commands_and_final_checks(self):
        report, order = example_report("aggregate-only")
        self.assertIn("preflight-rehash-default", package.validate_commands(report, order, order))
        for label in ("preflight-rehash-entry-points", "preflight-rehash-default"):
            for alteration in ("missing", "failed", "no_rehash", "no_no_build"):
                altered = copy.deepcopy(report)
                command = next(row for row in altered["commands"] if row["label"] == label)
                if alteration == "missing":
                    altered["commands"].remove(command)
                elif alteration == "failed":
                    command["returncode"] = 3
                else:
                    command["argv"].remove("--rehash" if alteration == "no_rehash" else "--no-build")
                with self.subTest(label=label, alteration=alteration), self.assertRaises(package.PackageError):
                    package.validate_commands(altered, order, order)

    def test_verification_modes_cannot_be_missing_unknown_or_relabelled(self):
        sequential, order = example_report()
        aggregate, _ = example_report("aggregate-only")
        for report, mode in ((sequential, None), (sequential, "unknown"),
                             (sequential, "aggregate-only"), (aggregate, "sequential")):
            altered = copy.deepcopy(report)
            altered["verification_mode"] = mode
            with self.subTest(mode=mode), self.assertRaises(package.PackageError):
                package.validate_commands(altered, order, order)

    def test_failed_or_unfinished_command_rejected(self):
        report, order = example_report()
        for bad in (1, None, False):
            altered = copy.deepcopy(report)
            altered["commands"][1]["returncode"] = bad
            with self.assertRaises(package.PackageError):
                package.validate_commands(altered, order, order)

    def test_missing_or_fake_gate_rejected(self):
        report, order = example_report()
        altered = copy.deepcopy(report)
        altered["commands"] = altered["commands"][:-1]
        with self.assertRaises(package.PackageError):
            package.validate_commands(altered, order, order)
        altered = copy.deepcopy(report)
        altered["commands"][-1]["argv"] = ["lake", "env", "lean", "unrelated.lean"]
        with self.assertRaises(package.PackageError):
            package.validate_commands(altered, order, order)

    def test_unsafe_package_paths_rejected(self):
        for path in ("../paper.tex", "reference/paper.pdf", ".lake/cache/file",
                     "scratch/check.lean", "Schmeisser/Experiments/Test.lean",
                     "C:/Users/file", "Schmeisser\\Main.lean", "Schmeisser/Main.olean"):
            with self.subTest(path=path), self.assertRaises(package.PackageError):
                package.checked_name(path)
        self.assertEqual(package.checked_name("Schmeisser/Main.lean"), "Schmeisser/Main.lean")

    def test_source_name_must_match_module(self):
        with self.assertRaises(package.PackageError):
            package.source_name("Schmeisser.Main", {"file": "Schmeisser/Other.lean"})
        with self.assertRaises(package.PackageError):
            package.source_name("Schmeisser.Experiments.Test", {"file": "Schmeisser/Experiments/Test.lean"})


if __name__ == "__main__":
    unittest.main(verbosity=2)
