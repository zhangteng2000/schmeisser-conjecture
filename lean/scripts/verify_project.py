#!/usr/bin/env python3
"""Portable verification of the pinned Schmeisser Lean project.

Python 3.11+ and the project's Elan/Lake toolchain are required.  --plan-only
does not run any subprocess, access the network, or create a report directory.
Only Lake writes build artifacts; this script never edits .trace/.hash files.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import tomllib
import uuid

sys.dont_write_bytecode = True

GIB = 1024 ** 3
MODULE = re.compile(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*\Z")
IMPORT = re.compile(r"(?m)^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+([^\n]+)")
FORBIDDEN = (
    ("unproved declaration or tactic", re.compile(r"\b(?:sorry|admit|axiom|sorryAx|mkSorry|mkSyntheticSorry)\b")),
    ("native proof evaluation", re.compile(r"\b(?:native_decide|ofReduceBool|ofReduceNat|trustCompiler)\b")),
    ("native decide option", re.compile(r"\+\s*native\b|\bnative\s*:=\s*true\b")),
    ("kernel bypass", re.compile(r"\bdebug\s*\.\s*skipKernelTC\b|\btrustLevel\b|\bunsafeCast\b")),
    ("unsafe declaration", re.compile(r"\bunsafe\b")),
)


class VerificationError(RuntimeError):
    pass


def utc() -> str:
    return datetime.now(timezone.utc).isoformat()


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def mask_lean_text(text: str) -> str:
    """Blank nested comments and strings while retaining offsets and newlines.

This is a source preflight, not a substitute for Lean's parser or axiom gate.
Both ordinary strings and Lean raw strings r#*"..."#* are recognized.
"""
    out = list(text)
    n, i = len(text), 0

    def blank(start: int, end: int) -> None:
        for j in range(start, end):
            if text[j] not in "\r\n":
                out[j] = " "

    while i < n:
        if text.startswith("--", i):
            end = text.find("\n", i)
            end = n if end < 0 else end
            blank(i, end)
            i = end
        elif text.startswith("/-", i):
            start, depth = i, 1
            i += 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise VerificationError("Unterminated Lean block comment")
            blank(start, i)
        else:
            raw = re.match(r'r(#+)"', text[i:]) if text[i] == "r" else None
            if raw:
                start = i
                marker = '"' + raw.group(1)
                end = text.find(marker, i + len(raw.group(0)))
                if end < 0:
                    raise VerificationError("Unterminated Lean raw string")
                i = end + len(marker)
                blank(start, i)
            elif text[i] == '"':
                start = i
                i += 1
                while i < n:
                    if text[i] == "\\":
                        i += 2
                    elif text[i] == '"':
                        i += 1
                        break
                    else:
                        i += 1
                else:
                    raise VerificationError("Unterminated Lean string")
                blank(start, min(i, n))
            else:
                i += 1
    return "".join(out)


def imports_of(clean: str) -> list[str]:
    imports = []
    for match in IMPORT.finditer(clean):
        words = match.group(1).split()
        if words and words[0] == "all":
            words = words[1:]
        for word in words:
            if not MODULE.fullmatch(word):
                raise VerificationError(f"Unsupported import syntax: {word!r}")
            imports.append(word)
    return imports


def scan_forbidden(clean: str, path: str) -> list[dict]:
    found = []
    for reason, pattern in FORBIDDEN:
        for match in pattern.finditer(clean):
            found.append({"file": path, "line": clean.count("\n", 0, match.start()) + 1,
                          "reason": reason, "token": match.group(0)})
    return found


def reject_kernel_overrides(config: dict) -> None:
    def walk(value, key=""):
        if isinstance(value, dict):
            for child_key, child in value.items():
                if "skipKernelTC" in child_key or "trustLevel" in child_key:
                    raise VerificationError("Kernel/trust overrides are not allowed in lakefile.toml")
                walk(child, child_key)
        elif isinstance(value, list):
            if key == "moreLeanArgs":
                for arg in value:
                    if isinstance(arg, str) and ("skipKernelTC" in arg or "--trust" in arg
                                                 or re.match(r"-t(?:\d|$)", arg)):
                        raise VerificationError("Kernel/trust command-line overrides are not allowed")
            for child in value:
                walk(child, key)
    walk(config)


@dataclass
class Plan:
    root: Path
    targets: list[str]
    order: list[str]
    sources: dict[str, dict]
    external_imports: list[str]
    manifest: dict
    packages_dir: Path
    pins: dict[str, str]
    control_hashes: dict[str, str]
    forbidden: list[dict]
    gate: Path
    toolchain: str


def make_plan(root: Path, main: str, library_roots: list[str] | None) -> Plan:
    config_path = root / "lakefile.toml"
    manifest_path = root / "lake-manifest.json"
    gate = root / "reports/AxiomGate.lean"
    for required in (config_path, manifest_path, root / "lean-toolchain", gate):
        if not required.is_file():
            raise VerificationError(f"Required project file is missing: {required}")
    config = tomllib.loads(config_path.read_text(encoding="utf-8-sig"))
    reject_kernel_overrides(config)
    manifest = json.loads(manifest_path.read_text(encoding="utf-8-sig"))
    toolchain = (root / "lean-toolchain").read_text(encoding="utf-8-sig").strip()
    if not re.fullmatch(r"leanprover/lean4:v\d+\.\d+\.\d+", toolchain):
        raise VerificationError("lean-toolchain must pin a release, not an unversioned channel")
    libs = config.get("lean_lib", [])
    if not libs:
        raise VerificationError("No lean_lib is configured in lakefile.toml")
    if any(lib.get("srcDir", ".") != "." for lib in libs) or config.get("srcDir", ".") != ".":
        raise VerificationError("This verifier expects the project's current srcDir='.' layout")
    roots = library_roots or [r for lib in libs for r in lib.get("roots", [lib["name"]])]
    targets = list(dict.fromkeys([main, *roots]))
    if any(not MODULE.fullmatch(name) for name in targets):
        raise VerificationError("Invalid entry-point module name")
    local_prefixes = {lib["name"].split(".")[0] for lib in libs} | {main.split(".")[0]}
    packages_rel = Path(manifest.get("packagesDir", ".lake/packages"))
    if packages_rel.is_absolute() or ".." in packages_rel.parts:
        raise VerificationError("packagesDir must be a path inside this project")
    packages_dir = root / packages_rel
    pins = {}
    for package in manifest.get("packages", []):
        name, rev = package.get("name", ""), package.get("rev", "")
        if (not re.fullmatch(r"[A-Za-z0-9_-]+", name) or package.get("type") != "git"
                or not re.fullmatch(r"[0-9a-fA-F]{40}", rev)):
            raise VerificationError(f"Dependency {name!r} is not pinned to a full Git commit")
        pins[name] = rev.lower()
    mathlib_req = next((x for x in config.get("require", []) if x.get("name") == "mathlib"), None)
    if not mathlib_req or mathlib_req.get("rev", "").lower() != pins.get("mathlib"):
        raise VerificationError("mathlib's lakefile and manifest revisions must agree exactly")

    sources, order, state, external, violations = {}, [], {}, set(), []

    def visit(name: str) -> None:
        if state.get(name) == 2:
            return
        if state.get(name) == 1:
            raise VerificationError(f"Local import cycle reaches {name}")
        path = root.joinpath(*name.split(".")).with_suffix(".lean")
        if not path.is_file():
            if name.split(".")[0] in local_prefixes or name in targets:
                raise VerificationError(f"Missing local import {name}: {path}")
            external.add(name)
            return
        if not path.resolve().is_relative_to(root.resolve()):
            raise VerificationError(f"Local module resolves outside the project: {path}")
        state[name] = 1
        relative = path.relative_to(root).as_posix()
        clean = mask_lean_text(path.read_text(encoding="utf-8-sig"))
        dependencies = imports_of(clean)
        sources[name] = {"file": relative, "imports": dependencies, "sha256": digest(path)}
        violations.extend(scan_forbidden(clean, relative))
        for dep in dependencies:
            visit(dep)
        state[name] = 2
        order.append(name)

    for target in targets:
        visit(target)
    gate_clean = mask_lean_text(gate.read_text(encoding="utf-8-sig"))
    violations.extend(scan_forbidden(gate_clean, "reports/AxiomGate.lean"))
    for dep in imports_of(gate_clean):
        visit(dep)
    # The gate is not a proof source in the main closure, but it must actually
    # assert the three public results, not merely print their axiom lists.
    for theorem in ("Schmeisser.main", "Schmeisser.sharpness", "Schmeisser.universal_bound_iff"):
        if not re.search(r"(?m)^\s*assert_standard_axioms\s+" + re.escape(theorem) + r"\s*$", gate_clean):
            raise VerificationError(f"AxiomGate.lean lacks its mandatory assertion for {theorem}")
    controls = {p.relative_to(root).as_posix(): digest(p) for p in
                (config_path, manifest_path, root / "lean-toolchain", gate)}
    return Plan(root, targets, order, sources, sorted(external), manifest, packages_dir,
                pins, controls, violations, gate, toolchain)


def environment(plan: Plan) -> dict[str, str]:
    env = os.environ.copy()
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LAKE_OVERRIDE_LEAN",
                "LEAN_BELIEVER_TRUST_LEVEL"):
        env.pop(key, None)
    env["ELAN_TOOLCHAIN"] = plan.toolchain
    count = int(env.get("GIT_CONFIG_COUNT", "0"))
    entries = []
    for i in range(count):
        key, value = env.pop(f"GIT_CONFIG_KEY_{i}", ""), env.pop(f"GIT_CONFIG_VALUE_{i}", "")
        if key and key.lower() != "safe.directory":
            entries.append((key, value))
    paths = [plan.root, *(plan.packages_dir / name for name in plan.pins)]
    exact = sorted({str(p.absolute()).replace("\\", "/") for p in paths} |
                   {str(p.resolve()).replace("\\", "/") for p in paths})
    entries.extend(("safe.directory", path) for path in exact)
    if os.name == "nt":
        entries.append(("core.longpaths", "true"))
    env["GIT_CONFIG_COUNT"] = str(len(entries))
    for i, (key, value) in enumerate(entries):
        env[f"GIT_CONFIG_KEY_{i}"] = key
        env[f"GIT_CONFIG_VALUE_{i}"] = value
    env["LEAN_NUM_THREADS"] = "1"
    # Cache downloads are explicit through --fetch-cache, not implicit builds.
    env["LAKE_NO_CACHE"] = "true"
    return env


def available_memory() -> tuple[int | None, int | None]:
    """Return available physical memory and Windows commit headroom in bytes.

Linux exposes the existing MemAvailable check only; None means that a check
is unavailable, not that zero bytes remain.
"""
    if os.name == "nt":
        import ctypes
        from ctypes import wintypes

        class MemoryStatus(ctypes.Structure):
            _fields_ = [("dwLength", wintypes.DWORD), ("dwMemoryLoad", wintypes.DWORD)] + [
                (name, ctypes.c_ulonglong) for name in ("ullTotalPhys", "ullAvailPhys",
                "ullTotalPageFile", "ullAvailPageFile", "ullTotalVirtual", "ullAvailVirtual",
                "ullAvailExtendedVirtual")]

        status = MemoryStatus()
        status.dwLength = ctypes.sizeof(status)
        kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
        query = kernel32.GlobalMemoryStatusEx
        query.argtypes = [ctypes.POINTER(MemoryStatus)]
        query.restype = wintypes.BOOL
        if not query(ctypes.byref(status)):
            raise VerificationError("Windows physical/commit-memory query failed; no process was launched "
                                    f"(error {ctypes.get_last_error()})")
        return status.ullAvailPhys, status.ullAvailPageFile
    if sys.platform.startswith("linux"):
        info = Path("/proc/meminfo")
        if info.is_file():
            match = re.search(r"(?m)^MemAvailable:\s+(\d+)\s+kB", info.read_text())
            if match:
                return int(match.group(1)) * 1024, None
    return None, None


def memory_gate_metadata(args: argparse.Namespace) -> dict:
    windows = os.name == "nt"
    physical_query = ("GlobalMemoryStatusEx.ullAvailPhys" if windows else
                      "/proc/meminfo:MemAvailable" if sys.platform.startswith("linux") else None)
    return {"memory_reserve_gib": args.memory_reserve_gib,
            "commit_reserve_gib": args.commit_reserve_gib,
            "memory_timeout": args.memory_timeout,
            "physical_memory_query": physical_query,
            "commit_memory_query": "GlobalMemoryStatusEx.ullAvailPageFile" if windows else None,
            "commit_check_supported": windows}


def wait_for_memory(reserve: float, commit_reserve: float, timeout: float) -> None:
    if reserve == 0 and commit_reserve == 0:
        return
    start, announced, commit_notice = time.monotonic(), False, False
    while True:
        free, commit = available_memory()
        physical_status = "unavailable" if free is None else f"{free/GIB:.2f} GiB available"
        commit_status = "unavailable" if commit is None else f"{commit/GIB:.2f} GiB available"
        details = (f"physical {physical_status} / {reserve:g} GiB required; "
                   f"commit {commit_status} / {commit_reserve:g} GiB required")
        if free is None and commit is None:
            print(f"Memory gate unavailable on this platform; no physical or commit check: {details}.",
                  flush=True)
            return
        if commit is None and not commit_notice:
            print(f"Commit-memory gate unavailable on this platform; only physical memory is checked: {details}.",
                  flush=True)
            commit_notice = True
        if (free is None or free >= reserve * GIB) and (commit is None or commit >= commit_reserve * GIB):
            return
        elapsed = time.monotonic() - start
        if timeout and elapsed >= timeout:
            raise VerificationError(f"Timed out waiting for memory: {details}")
        if not announced or int(elapsed) % 60 < 5:
            print(f"Waiting for memory: {details}.", flush=True)
            announced = True
        time.sleep(5)


def check_unchanged(plan: Plan, all_sources: bool = False) -> None:
    expected = dict(plan.control_hashes)
    if all_sources:
        expected.update((v["file"], v["sha256"]) for v in plan.sources.values())
    changed = [name for name, sha in expected.items()
               if not (plan.root / name).is_file() or digest(plan.root / name) != sha]
    if changed:
        raise VerificationError("Sources changed during verification: " + ", ".join(changed[:12]))


def require_public_main(plan: Plan) -> None:
    if "Schmeisser.Main" not in plan.sources.get("Schmeisser", {}).get("imports", []):
        raise VerificationError("The public Schmeisser.lean entry point must import Schmeisser.Main "
                                "before final verification")


class Runner:
    def __init__(self, plan: Plan, args: argparse.Namespace, lake: str, logdir: Path):
        self.plan, self.args, self.lake, self.logdir = plan, args, lake, logdir
        self.report = {"status": "running", "started_utc": utc(), "project": str(plan.root),
                       "verification_mode": "aggregate-only" if args.aggregate_only else "sequential",
                       "toolchain": plan.toolchain, "dependency_pins": plan.pins,
                       "targets": plan.targets, "topological_order": plan.order,
                       "sources": plan.sources, "controls": plan.control_hashes,
                       "source_scan": {"violations": plan.forbidden},
                       **memory_gate_metadata(args), "commands": []}
        self.save()

    def save(self) -> None:
        temp = self.logdir / "report.json.tmp"
        temp.write_text(json.dumps(self.report, ensure_ascii=False, indent=2), encoding="utf-8")
        temp.replace(self.logdir / "report.json")

    def command(self, label: str, argv: list[str], memory_gate: bool = True) -> str:
        check_unchanged(self.plan, all_sources=self.args.aggregate_only)
        if memory_gate:
            wait_for_memory(self.args.memory_reserve_gib, self.args.commit_reserve_gib,
                            self.args.memory_timeout)
        index = len(self.report["commands"])
        filename = f"{index:05d}-" + re.sub(r"[^A-Za-z0-9_.-]", "_", label) + ".log"
        log = self.logdir / filename
        row = {"label": label, "argv": argv, "started_utc": utc(), "log": filename}
        self.report["commands"].append(row)
        self.save()
        print(f"[{index+1}] {label}", flush=True)
        start, interrupted = time.monotonic(), False
        with log.open("w", encoding="utf-8") as output:
            proc = subprocess.Popen(argv, cwd=self.plan.root, env=environment(self.plan),
                                    stdout=output, stderr=subprocess.STDOUT)
            # Always wait for the supervised process.  In particular, do not
            # abandon a background Lake invocation when Python is interrupted.
            while True:
                try:
                    code = proc.wait()
                    break
                except KeyboardInterrupt:
                    interrupted = True
                    print("Interrupted; waiting for the active command to exit before stopping.", flush=True)
        row.update(returncode=code, seconds=time.monotonic()-start, finished_utc=utc())
        self.save()
        if self.args.aggregate_only:
            check_unchanged(self.plan, all_sources=True)
        if interrupted:
            raise KeyboardInterrupt
        if code != 0:
            raise VerificationError(f"{label} failed with return code {code}; see {log}")
        return log.read_text(encoding="utf-8", errors="replace").strip()

    def verify(self) -> None:
        require_public_main(self.plan)
        if self.args.fetch_cache:
            self.command("fetch-pinned-mathlib-cache", [self.lake, "exe", "cache", "get"])
            check_unchanged(self.plan)
        git = shutil.which("git")
        if not git:
            raise VerificationError("Git is required to verify the pinned dependency checkouts")
        for name, revision in self.plan.pins.items():
            package = self.plan.packages_dir / name
            if not package.is_dir():
                raise VerificationError(f"Missing dependency {name}; use --fetch-cache or prepare the pinned dependencies")
            head = self.command("pin-" + name, [git, "-C", str(package), "rev-parse", "HEAD"], False)
            if head.lower() != revision:
                raise VerificationError(f"Dependency {name} is at {head}, expected {revision}")
            self.command("clean-" + name, [git, "-C", str(package), "diff", "--quiet", "HEAD", "--"], False)
        version = self.command("pinned-lean-version", [self.lake, "env", "lean", "--version"])
        release = self.plan.toolchain.split(":v", 1)[1]
        if not re.search(r"\bversion\s+" + re.escape(release) + r"(?:\s|,|\))", version):
            raise VerificationError(f"Lake is not using the pinned Lean {release}: {version}")
        if self.args.aggregate_only:
            # This mode is only for an already built, otherwise idle checkout.
            # Lake itself rehashes and rejects stale/missing targets before
            # any unrestricted aggregate build is allowed to run.
            check_unchanged(self.plan, all_sources=True)
            self.command("preflight-rehash-entry-points",
                         [self.lake, "--rehash", "--no-build", "build", *self.plan.targets])
            self.command("preflight-rehash-default",
                         [self.lake, "--rehash", "--no-build", "build"])
        else:
            for module in self.plan.order:
                info = self.plan.sources[module]
                if digest(self.plan.root / info["file"]) != info["sha256"]:
                    raise VerificationError(f"Source changed before its build: {module}")
                self.command(module, [self.lake, "build", module])
        check_unchanged(self.plan, all_sources=True)
        # Rehash both explicit roots, then perform the unqualified default
        # build and the mandatory rejecting axiom gate in both modes.
        self.command("final-rehash-entry-points", [self.lake, "--rehash", "build", *self.plan.targets])
        self.command("final-rehash-build", [self.lake, "--rehash", "build"])
        self.command("final-axiom-gate", [self.lake, "env", "lean", "reports/AxiomGate.lean"])
        check_unchanged(self.plan, all_sources=True)
        if not self.report["commands"] or any(c.get("returncode") != 0 for c in self.report["commands"]):
            raise VerificationError("Some required commands have not successfully completed")
        self.report.update(status="verified", finished_utc=utc())
        self.save()
        print(f"VERIFIED: {self.logdir / 'report.json'}", flush=True)


def arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path(__file__).absolute().parent.parent)
    parser.add_argument("--main", default="Schmeisser.Main")
    parser.add_argument("--library-root", action="append", help="Library root module; repeat if needed")
    parser.add_argument("--lake", default="lake", help="Lake executable or Elan proxy")
    parser.add_argument("--plan-only", action="store_true", help="Read-only preflight; do not run Lean, Git, or network commands")
    parser.add_argument("--show-order", action="store_true", help="Print the full local module order in plan mode")
    parser.add_argument("--fetch-cache", action="store_true", help="Explicitly fetch the cache for the pinned mathlib dependency")
    parser.add_argument("--aggregate-only", action="store_true",
                        help="For an already built idle checkout: require rehashed no-build preflights, "
                             "then run the full builds and axiom gate without per-module builds")
    parser.add_argument("--memory-reserve-gib", type=float, default=6.0,
                        help="Available physical-memory launch threshold in GiB (default: 6)")
    parser.add_argument("--commit-reserve-gib", type=float, default=12.0,
                        help="Windows available commit-headroom launch threshold in GiB (default: 12)")
    parser.add_argument("--memory-timeout", type=float, default=0.0, help="Seconds to wait for memory; zero waits without a deadline")
    parser.add_argument("--logs", type=Path, help="Parent directory for a fresh isolated verification run")
    args = parser.parse_args()
    if args.aggregate_only and args.fetch_cache:
        parser.error("--aggregate-only requires an already built checkout; prepare caches separately")
    for name in ("memory_reserve_gib", "commit_reserve_gib", "memory_timeout"):
        value = getattr(args, name)
        if not math.isfinite(value) or value < 0:
            parser.error(f"--{name.replace('_', '-')} must be finite and nonnegative")
    return args


def main() -> int:
    args = arguments()
    runner = None
    try:
        # absolute() preserves an explicitly supplied Windows junction path;
        # resolve() is used separately for exact process-local Git exceptions.
        root = args.project.expanduser().absolute()
        plan = make_plan(root, args.main, args.library_root)
        lake = shutil.which(args.lake)
        summary = {"status": "plan_only_not_verified" if args.plan_only else "preflight",
                   "verification_mode": "aggregate-only" if args.aggregate_only else "sequential",
                   "project": str(root), "resolved_project": str(root.resolve()),
                   "toolchain": plan.toolchain, "mathlib_revision": plan.pins["mathlib"],
                   "lake_executable": lake, "targets": plan.targets,
                   "local_module_count": len(plan.order), "external_imports": plan.external_imports,
                   "source_violations": plan.forbidden, **memory_gate_metadata(args),
                   "fetch_cache_requested": args.fetch_cache,
                   "public_root_imports_main": "Schmeisser.Main" in
                       plan.sources.get("Schmeisser", {}).get("imports", []),
                   "aggregate_preflights": ([["lake", "--rehash", "--no-build", "build", *plan.targets],
                                              ["lake", "--rehash", "--no-build", "build"]]
                                             if args.aggregate_only else []),
                   "final_commands": [["lake", "--rehash", "build", *plan.targets],
                                      ["lake", "--rehash", "build"],
                                      ["lake", "env", "lean", "reports/AxiomGate.lean"]]}
        if args.show_order:
            summary["topological_order"] = plan.order
        print(json.dumps(summary, ensure_ascii=False, indent=2), flush=True)
        if plan.forbidden:
            raise VerificationError("Forbidden constructs found in the project import closure")
        if args.plan_only:
            return 0
        if not lake:
            raise VerificationError("Lake was not found; install the pinned Elan toolchain or pass --lake")
        if os.name == "nt" and len(str(root)) > 100:
            print("Windows: a shorter checkout or existing junction path is recommended.", flush=True)
        parent = args.logs.expanduser().absolute() if args.logs else root / "reports/verification-runs"
        run_name = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + f"-{os.getpid()}-{uuid.uuid4().hex[:8]}"
        logdir = parent / run_name
        logdir.mkdir(parents=True, exist_ok=False)
        runner = Runner(plan, args, lake, logdir)
        runner.verify()
        return 0
    except (VerificationError, OSError, ValueError, KeyboardInterrupt) as error:
        status = "interrupted" if isinstance(error, KeyboardInterrupt) else "failed"
        if runner:
            runner.report.update(status=status, error=str(error), finished_utc=utc())
            runner.save()
        print(f"NOT VERIFIED: {error or status}", file=sys.stderr, flush=True)
        return 130 if status == "interrupted" else 1


if __name__ == "__main__":
    raise SystemExit(main())
