"""Read-only Python preflight tests.  No Lean, Git, or network command is run."""
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import Mock, patch
from types import SimpleNamespace

sys.dont_write_bytecode = True
import verify_project as verifier

ROOT = Path(__file__).absolute().parent.parent


class PreflightTests(unittest.TestCase):
    def test_public_entrypoint_must_import_main_before_actual_verification(self):
        for sources in ({}, {"Schmeisser": {"imports": ["Schmeisser.Basic"]}}):
            with self.subTest(sources=sources), self.assertRaises(verifier.VerificationError):
                verifier.require_public_main(SimpleNamespace(sources=sources))
        verifier.require_public_main(SimpleNamespace(
            sources={"Schmeisser": {"imports": ["Schmeisser.Main"]}}))

    def test_lexer_preserves_offsets_and_ignores_comments_strings(self):
        source = ('/- sorry /- native_decide -/ axiom -/\n'
                  'def title := "admit \\"quoted\\""\n'
                  'def raw := r##"sorry \\" quote"##\n'
                  '-- set_option debug.skipKernelTC true\n'
                  'theorem actual : True := by sorry\n')
        # The ordinary-string fixture uses a single escaped quote in Lean.
        source = source.replace('\\\\"', '\\"')
        clean = verifier.mask_lean_text(source)
        self.assertEqual(len(clean), len(source))
        self.assertEqual(clean.count("\n"), source.count("\n"))
        hits = verifier.scan_forbidden(clean, "fixture.lean")
        self.assertEqual([(h["token"], h["line"]) for h in hits], [("sorry", 5)])

    def test_forbidden_proof_constructs(self):
        source = "axiom x : True\nby native_decide\nby decide +native\nset_option debug.skipKernelTC true\n"
        hits = verifier.scan_forbidden(verifier.mask_lean_text(source), "fixture.lean")
        self.assertEqual(len(hits), 4)
        self.assertEqual(verifier.scan_forbidden("by decide +kernel\n", "safe.lean"), [])
        with self.assertRaises(verifier.VerificationError):
            verifier.reject_kernel_overrides({"leanOptions": {"debug.skipKernelTC": True}})
        with self.assertRaises(verifier.VerificationError):
            verifier.reject_kernel_overrides({"lean_lib": [{"moreLeanArgs": ["--trust=1"]}]})

    def test_import_parser(self):
        self.assertEqual(verifier.imports_of("public meta import A.B C.D\nimport all E.F\n"),
                         ["A.B", "C.D", "E.F"])
        with self.assertRaises(verifier.VerificationError):
            verifier.mask_lean_text("/- unterminated")

    def test_real_project_topological_order(self):
        plan = verifier.make_plan(ROOT, "Schmeisser.Main", None)
        positions = {module: i for i, module in enumerate(plan.order)}
        self.assertIn("Schmeisser.Main", positions)
        self.assertIn("Schmeisser", positions)
        self.assertFalse(plan.forbidden)
        self.assertFalse(any(".Experiments." in name for name in positions))
        for module, info in plan.sources.items():
            for dependency in info["imports"]:
                if dependency in positions:
                    self.assertLess(positions[dependency], positions[module])
        with self.assertRaises(verifier.VerificationError):
            verifier.make_plan(ROOT, "Schmeisser.DoesNotExistForPreflightTest", None)

    def test_process_local_git_exceptions(self):
        plan = verifier.make_plan(ROOT, "Schmeisser.Main", None)
        inherited = {"GIT_CONFIG_COUNT": "2", "GIT_CONFIG_KEY_0": "safe.directory",
                     "GIT_CONFIG_VALUE_0": "*", "GIT_CONFIG_KEY_1": "core.autocrlf",
                     "GIT_CONFIG_VALUE_1": "false"}
        with patch.dict(os.environ, inherited, clear=True):
            env = verifier.environment(plan)
            self.assertEqual(dict(os.environ), inherited)
        pairs = [(env[f"GIT_CONFIG_KEY_{i}"], env[f"GIT_CONFIG_VALUE_{i}"])
                 for i in range(int(env["GIT_CONFIG_COUNT"]))]
        self.assertIn(("core.autocrlf", "false"), pairs)
        safe = [value for key, value in pairs if key == "safe.directory"]
        self.assertTrue(safe)
        self.assertNotIn("*", safe)
        self.assertTrue(all(Path(value).is_absolute() for value in safe))
        self.assertEqual(env["LEAN_NUM_THREADS"], "1")
        self.assertEqual(env["ELAN_TOOLCHAIN"], plan.toolchain)

    def test_plan_mode_runs_no_commands_and_creates_no_logs(self):
        output = io.StringIO()
        absent_logs = ROOT / "reports/plan-only-must-not-create-this-directory"
        self.assertFalse(absent_logs.exists())
        with patch.object(sys, "argv", ["verify_project.py", "--project", str(ROOT),
                                        "--plan-only", "--logs", str(absent_logs)]), \
             patch.object(subprocess, "Popen", side_effect=AssertionError("Subprocess in plan mode")), \
             patch.object(verifier, "available_memory", side_effect=AssertionError("Memory wait in plan mode")), \
             contextlib.redirect_stdout(output):
            self.assertEqual(verifier.main(), 0)
        summary = json.loads(output.getvalue())
        self.assertEqual(summary["status"], "plan_only_not_verified")
        self.assertEqual(summary["memory_reserve_gib"], 6.0)
        self.assertEqual(summary["commit_reserve_gib"], 12.0)
        self.assertEqual(summary["memory_timeout"], 0.0)
        self.assertEqual(summary["commit_check_supported"], os.name == "nt")
        self.assertEqual(summary["commit_memory_query"],
                         "GlobalMemoryStatusEx.ullAvailPageFile" if os.name == "nt" else None)
        self.assertFalse(absent_logs.exists())


class AggregateVerificationTests(unittest.TestCase):
    def make_runner(self, fail_label=None):
        runner = verifier.Runner.__new__(verifier.Runner)
        runner.plan = SimpleNamespace(
            root=ROOT, pins={}, packages_dir=ROOT / ".lake/packages",
            toolchain="leanprover/lean4:v4.34.1",
            targets=["Schmeisser.Main", "Schmeisser"],
            order=["Schmeisser.Main", "Schmeisser"],
            sources={"Schmeisser": {"imports": ["Schmeisser.Main"]}})
        runner.args = SimpleNamespace(aggregate_only=True, fetch_cache=False)
        runner.lake, runner.logdir = "fixture-lake", Path("fixture-no-logs-written")
        runner.report = {"commands": []}
        runner.save = Mock()

        def command(label, argv, memory_gate=True):
            runner.report["commands"].append({"label": label, "argv": argv,
                                               "returncode": 3 if label == fail_label else 0})
            if label == fail_label:
                raise verifier.VerificationError("fixture stale-target rejection")
            return "Lean (version 4.34.1, fixture)" if label == "pinned-lean-version" else ""

        runner.command = command
        return runner

    def test_aggregate_uses_no_per_module_commands_and_keeps_final_gate(self):
        runner = self.make_runner()
        with patch.object(verifier.shutil, "which", return_value="fixture-git"), \
             patch.object(verifier, "check_unchanged") as unchanged, \
             contextlib.redirect_stdout(io.StringIO()):
            runner.verify()
        labels = [row["label"] for row in runner.report["commands"]]
        self.assertEqual(labels, ["pinned-lean-version", "preflight-rehash-entry-points",
                                  "preflight-rehash-default", "final-rehash-entry-points",
                                  "final-rehash-build", "final-axiom-gate"])
        self.assertEqual(runner.report["status"], "verified")
        unchanged.assert_called_with(runner.plan, all_sources=True)

    def test_each_failed_preflight_stops_before_any_unrestricted_build(self):
        for label in ("preflight-rehash-entry-points", "preflight-rehash-default"):
            runner = self.make_runner(label)
            with self.subTest(label=label), \
                 patch.object(verifier.shutil, "which", return_value="fixture-git"), \
                 patch.object(verifier, "check_unchanged"), \
                 self.assertRaises(verifier.VerificationError):
                runner.verify()
            labels = [row["label"] for row in runner.report["commands"]]
            self.assertEqual(labels[-1], label)
            self.assertFalse(any(name.startswith("final-") for name in labels))
            self.assertNotEqual(runner.report.get("status"), "verified")

    def test_aggregate_cannot_fetch_or_build_cache_before_preflight(self):
        with patch.object(sys, "argv", ["verify_project.py", "--aggregate-only", "--fetch-cache"]), \
             contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as error:
            verifier.arguments()
        self.assertEqual(error.exception.code, 2)


class MemoryGateTests(unittest.TestCase):
    def test_windows_query_returns_physical_and_commit_with_explicit_prototypes(self):
        import ctypes
        from ctypes import wintypes

        def populate(pointer):
            status = pointer._obj
            self.assertEqual(status.dwLength, ctypes.sizeof(status))
            status.ullAvailPhys = 9 * verifier.GIB
            status.ullAvailPageFile = int(0.732 * verifier.GIB)
            return 1

        query = Mock(side_effect=populate)
        with patch.object(verifier.os, "name", "nt"), \
             patch.object(ctypes, "WinDLL", return_value=Mock(GlobalMemoryStatusEx=query),
                          create=True) as library:
            self.assertEqual(verifier.available_memory(),
                             (9 * verifier.GIB, int(0.732 * verifier.GIB)))
        library.assert_called_once_with("kernel32", use_last_error=True)
        self.assertEqual(len(query.argtypes), 1)
        self.assertTrue(issubclass(query.argtypes[0]._type_, ctypes.Structure))
        self.assertIs(query.restype, wintypes.BOOL)

    def test_windows_query_failure_blocks_launch(self):
        import ctypes

        query = Mock(return_value=0)
        with patch.object(verifier.os, "name", "nt"), \
             patch.object(ctypes, "WinDLL", return_value=Mock(GlobalMemoryStatusEx=query), create=True), \
             patch.object(ctypes, "get_last_error", return_value=1455, create=True), \
             self.assertRaisesRegex(verifier.VerificationError, "no process was launched.*1455"):
            verifier.wait_for_memory(6, 12, 1)

    def test_waits_until_both_thresholds_are_met(self):
        cases = ((6, (9 * verifier.GIB, int(0.732 * verifier.GIB))),
                 (0, (9 * verifier.GIB, int(0.732 * verifier.GIB))),
                 (6, (5 * verifier.GIB, 20 * verifier.GIB)))
        for physical_threshold, low in cases:
            with self.subTest(physical_threshold=physical_threshold, low=low):
                output = io.StringIO()
                with patch.object(verifier, "available_memory",
                                  side_effect=[low, (9 * verifier.GIB, 20 * verifier.GIB)]) as query, \
                     patch.object(verifier.time, "monotonic", side_effect=[0, 0]), \
                     patch.object(verifier.time, "sleep") as sleep, \
                     contextlib.redirect_stdout(output):
                    verifier.wait_for_memory(physical_threshold, 12, 10)
                self.assertEqual(query.call_count, 2)
                sleep.assert_called_once_with(5)
                message = output.getvalue()
                self.assertIn("Waiting for memory: physical", message)
                self.assertIn(f"{low[0]/verifier.GIB:.2f} GiB available / {physical_threshold:g} GiB required",
                              message)
                self.assertIn(f"commit {low[1]/verifier.GIB:.2f} GiB available / 12 GiB required", message)

    def test_sufficient_physical_but_low_commit_times_out(self):
        output = io.StringIO()
        with patch.object(verifier, "available_memory",
                          return_value=(9 * verifier.GIB, int(0.732 * verifier.GIB))) as query, \
             patch.object(verifier.time, "monotonic", side_effect=[0, 0, 5]), \
             patch.object(verifier.time, "sleep") as sleep, \
             contextlib.redirect_stdout(output), \
             self.assertRaises(verifier.VerificationError) as error:
            verifier.wait_for_memory(6, 12, 5)
        self.assertEqual(query.call_count, 2)
        sleep.assert_called_once_with(5)
        self.assertIn("Timed out waiting for memory", str(error.exception))
        for message in (output.getvalue(), str(error.exception)):
            self.assertIn("physical 9.00 GiB available / 6 GiB required", message)
            self.assertIn("commit 0.73 GiB available / 12 GiB required", message)

    def test_enough_physical_and_commit_returns_without_waiting(self):
        with patch.object(verifier, "available_memory",
                          return_value=(6 * verifier.GIB, 12 * verifier.GIB)) as query, \
             patch.object(verifier.time, "sleep") as sleep:
            verifier.wait_for_memory(6, 12, 1)
        query.assert_called_once_with()
        sleep.assert_not_called()

    def test_both_zero_thresholds_disable_queries(self):
        with patch.object(verifier, "available_memory") as query:
            verifier.wait_for_memory(0, 0, 1)
        query.assert_not_called()

    def test_linux_checks_physical_only_and_reports_no_commit_check(self):
        info = Mock()
        info.is_file.return_value = True
        info.read_text.return_value = "MemAvailable: 6291456 kB\n"
        args = verifier.argparse.Namespace(memory_reserve_gib=6, commit_reserve_gib=12, memory_timeout=0)
        with patch.object(verifier.os, "name", "posix"), \
             patch.object(verifier.sys, "platform", "linux"), \
             patch.object(verifier, "Path", return_value=info) as path:
            available = verifier.available_memory()
            metadata = verifier.memory_gate_metadata(args)
        path.assert_called_once_with("/proc/meminfo")
        self.assertEqual(available, (6 * verifier.GIB, None))
        self.assertEqual(metadata["physical_memory_query"], "/proc/meminfo:MemAvailable")
        self.assertIsNone(metadata["commit_memory_query"])
        self.assertFalse(metadata["commit_check_supported"])
        output = io.StringIO()
        with patch.object(verifier, "available_memory", return_value=available), \
             patch.object(verifier.time, "sleep") as sleep, \
             contextlib.redirect_stdout(output):
            verifier.wait_for_memory(6, 12, 1)
        sleep.assert_not_called()
        self.assertIn("Commit-memory gate unavailable", output.getvalue())
        self.assertIn("only physical memory is checked", output.getvalue())
        self.assertIn("commit unavailable / 12 GiB required", output.getvalue())

    def test_thresholds_and_timeout_must_be_finite_and_nonnegative(self):
        for flag in ("--memory-reserve-gib", "--commit-reserve-gib", "--memory-timeout"):
            for value in ("-1", "nan", "inf", "-inf"):
                with self.subTest(flag=flag, value=value), \
                     patch.object(sys, "argv", ["verify_project.py", f"{flag}={value}"]), \
                     contextlib.redirect_stderr(io.StringIO()) as errors, \
                     self.assertRaises(SystemExit) as error:
                    verifier.arguments()
                self.assertEqual(error.exception.code, 2)
                self.assertIn(f"{flag} must be finite and nonnegative", errors.getvalue())
        with patch.object(sys, "argv", ["verify_project.py", "--memory-reserve-gib=0",
                                       "--commit-reserve-gib=0", "--memory-timeout=0"]):
            args = verifier.arguments()
        self.assertEqual((args.memory_reserve_gib, args.commit_reserve_gib, args.memory_timeout), (0, 0, 0))


if __name__ == "__main__":
    unittest.main(verbosity=2)
