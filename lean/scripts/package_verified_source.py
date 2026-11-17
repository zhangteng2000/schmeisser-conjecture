#!/usr/bin/env python3
"""Package only the exact source closure of a successfully verified project.

This command never runs Lean or publishes anything.  A report produced by
verify_project.py is required.  --plan-only validates inputs without creating
a ZIP.  Report records are provenance, not a cryptographic attestation of an
external execution; the packaged verifier can reproduce the checks.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import sys
import zipfile

sys.dont_write_bytecode = True
import verify_project as verifier

FIXED_FILES = (
    "Schmeisser.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain", ".gitignore",
    "reports/AxiomGate.lean", "scripts/verify_project.py", "scripts/verify_project.README.md",
    "scripts/package_verified_source.py", "scripts/test_verify_project.py",
    "scripts/test_package_verified_source.py",
    "README.md", "PROGRESS.md", "reports/theorem-map.tsv",
)
EXCLUDED_PARTS = {"reference", ".lake", "scratch", "experiments", "__pycache__", ".git"}
LOG_LIMIT = 8 * 1024 * 1024


class PackageError(RuntimeError):
    pass


def sha256(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def checked_name(name: str) -> str:
    if not isinstance(name, str) or "\\" in name:
        raise PackageError(f"Invalid archive path: {name!r}")
    path = PurePosixPath(name)
    if (path.is_absolute() or not path.parts or ".." in path.parts or ":" in name
            or path.as_posix() != name or any(part.lower() in EXCLUDED_PARTS for part in path.parts)):
        raise PackageError(f"Excluded or noncanonical archive path: {name!r}")
    if path.suffix.lower() in {".tex", ".pdf", ".doc", ".docx", ".olean", ".ilean", ".trace", ".hash"}:
        raise PackageError(f"Manuscripts or build artifacts are excluded: {name!r}")
    return name


def source_name(module: str, record: dict) -> str:
    if not verifier.MODULE.fullmatch(module):
        raise PackageError(f"Invalid module name in report: {module!r}")
    expected = module.replace(".", "/") + ".lean"
    name = checked_name(record.get("file", ""))
    if name != expected or not (name == "Schmeisser.lean" or name.startswith("Schmeisser/")):
        raise PackageError(f"Report source is not a project module: {module!r}, {name!r}")
    return name


def validate_commands(report: dict, order: list[str], targets: list[str]) -> dict[str, dict]:
    commands = report.get("commands")
    if not isinstance(commands, list) or not commands:
        raise PackageError("Verification report has no completed command records")
    indexed = {}
    for command in commands:
        if not isinstance(command, dict) or type(command.get("returncode")) is not int or command["returncode"] != 0:
            raise PackageError("Every recorded command must actually have returncode 0")
        label, argv = command.get("label"), command.get("argv")
        if (not isinstance(label, str) or label in indexed or not isinstance(argv, list)
                or not argv or any(not isinstance(arg, str) for arg in argv)
                or not command.get("started_utc") or not command.get("finished_utc")):
            raise PackageError("Malformed, duplicate, or unfinished command record")
        indexed[label] = command
    module_names = set(order)
    actual_order = [command["label"] for command in commands if command["label"] in module_names]
    mode = report.get("verification_mode")
    if mode not in ("sequential", "aggregate-only"):
        raise PackageError("Report must explicitly identify its supported verification mode")
    if mode == "sequential" and actual_order != order:
        raise PackageError("Report does not contain the complete topological module build sequence")
    if mode == "aggregate-only" and actual_order:
        raise PackageError("Aggregate-only reports must not claim per-module build records")
    for module in actual_order:
        if indexed[module]["argv"][1:] != ["build", module]:
            raise PackageError(f"Module {module} was not checked by its required lake build command")
    expected = {
        "pinned-lean-version": ["env", "lean", "--version"],
        "final-rehash-entry-points": ["--rehash", "build", *targets],
        "final-rehash-build": ["--rehash", "build"],
        "final-axiom-gate": ["env", "lean", "reports/AxiomGate.lean"],
    }
    preflights = ["preflight-rehash-entry-points", "preflight-rehash-default"]
    if mode == "aggregate-only":
        expected.update({
            preflights[0]: ["--rehash", "--no-build", "build", *targets],
            preflights[1]: ["--rehash", "--no-build", "build"],
        })
        if [command["label"] for command in commands[-5:-3]] != preflights:
            raise PackageError("Both successful aggregate preflights must immediately precede the final checks")
    elif any(label in indexed for label in preflights):
        raise PackageError("Sequential reports must not contain aggregate-only preflight records")
    for label, tail in expected.items():
        if label not in indexed or indexed[label]["argv"][1:] != tail:
            raise PackageError(f"Missing required successful command: {label}")
    if [command["label"] for command in commands[-3:]] != [
            "final-rehash-entry-points", "final-rehash-build", "final-axiom-gate"]:
        raise PackageError("The rehash builds and axiom gate must finish the verification sequence")
    lake = indexed["pinned-lean-version"]["argv"][0]
    for label in [*actual_order, *expected]:
        if indexed[label]["argv"][0] != lake:
            raise PackageError("The Lake executable changed within the verification report")
    return indexed


def read_inside(root: Path, name: str) -> bytes:
    name = checked_name(name)
    path = root / name
    if not path.is_file() or not path.resolve().is_relative_to(root.resolve()):
        raise PackageError(f"Required package file is absent or resolves outside the project: {name}")
    return path.read_bytes()


def require_public_main(plan: verifier.Plan) -> None:
    if "Schmeisser.Main" not in plan.sources.get("Schmeisser", {}).get("imports", []):
        raise PackageError("The public Schmeisser.lean entry point must import Schmeisser.Main "
                           "before final verification and source packaging")


def prepare(root: Path, report_path: Path, include_logs: bool) -> tuple[dict[str, bytes], dict]:
    report_bytes = report_path.read_bytes()
    report = json.loads(report_bytes)
    if report.get("status") != "verified" or not report.get("finished_utc"):
        raise PackageError("Only a completed status=verified report can authorize a source package")
    plan = verifier.make_plan(root, "Schmeisser.Main", None)
    if plan.forbidden:
        raise PackageError("Current proof sources fail the forbidden-construct preflight")
    require_public_main(plan)
    if (report.get("targets") != plan.targets or report.get("topological_order") != plan.order
            or report.get("toolchain") != plan.toolchain or report.get("dependency_pins") != plan.pins):
        raise PackageError("The current project graph or pinned versions differ from the verified report")
    sources = report.get("sources")
    if not isinstance(sources, dict) or set(sources) != set(plan.sources):
        raise PackageError("Report source closure is incomplete or contains additional modules")
    if report.get("controls") != plan.control_hashes:
        raise PackageError("Control-file SHA256 hashes differ from the verified report")
    commands = validate_commands(report, plan.order, plan.targets)
    contents = {}
    for module in plan.order:
        record = sources[module]
        name = source_name(module, record)
        data = read_inside(root, name)
        if sha256(data) != record.get("sha256") or record.get("sha256") != plan.sources[module]["sha256"]:
            raise PackageError(f"Source hash differs from verified report: {name}")
        if record.get("imports") != plan.sources[module]["imports"]:
            raise PackageError(f"Reported import list differs from the current source: {name}")
        contents[name] = data
    for name in FIXED_FILES:
        data = read_inside(root, name)
        if name in report["controls"] and sha256(data) != report["controls"][name]:
            raise PackageError(f"Control file changed while preparing package: {name}")
        if name in contents and contents[name] != data:
            raise PackageError(f"Source changed while preparing package: {name}")
        contents[name] = data
    contents["verification/report.json"] = report_bytes
    if include_logs:
        for label in ("final-rehash-build", "final-axiom-gate"):
            log_name = commands[label].get("log", "")
            if not log_name or Path(log_name).name != log_name or "/" in log_name or "\\" in log_name:
                raise PackageError(f"Unsafe log path for {label}")
            path = report_path.parent / log_name
            if not path.is_file() or path.resolve().parent != report_path.parent.resolve():
                raise PackageError(f"Missing or externally linked final log: {label}")
            if path.stat().st_size > LOG_LIMIT:
                raise PackageError(f"Final log {label} exceeds 8 MiB; omit --include-final-logs")
            contents[f"verification/{label}.log"] = path.read_bytes()
    if report_path.read_bytes() != report_bytes:
        raise PackageError("Verification report changed during package preparation")
    verifier.check_unchanged(plan, all_sources=True)
    metadata = {
        "format": "schmeisser-verified-source-v1",
        "verified_at_utc": report["finished_utc"],
        "verification_mode": report["verification_mode"],
        "verification_report_sha256": sha256(report_bytes),
        "toolchain": plan.toolchain, "dependency_pins": plan.pins,
        "source_module_count": len(plan.order),
        "provenance": "Proof-source and control hashes match the supplied completed verification report. Additional documentation and tooling are the current source snapshot.",
        "excluded": ["manuscripts", "reference/", "*.tex", ".lake/", "scratch/", "Experiments/", "production event logs"],
        "files": {name: {"sha256": sha256(data), "bytes": len(data)} for name, data in sorted(contents.items())},
    }
    contents["PACKAGE_MANIFEST.json"] = (json.dumps(metadata, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    contents["SHA256SUMS"] = ("\n".join(f"{sha256(data)}  {name}" for name, data in sorted(contents.items())) + "\n").encode("utf-8")
    return contents, metadata


def write_archive(output: Path, contents: dict[str, bytes]) -> None:
    if output.suffix.lower() != ".zip":
        raise PackageError("The output path must end in .zip")
    if not output.parent.is_dir():
        raise PackageError("The output directory must already exist")
    created = False
    try:
        # Exclusive creation prevents replacing an earlier release archive.
        with output.open("xb") as stream:
            created = True
            with zipfile.ZipFile(stream, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
                for name, data in sorted(contents.items()):
                    checked_name(name)
                    entry = zipfile.ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
                    entry.compress_type = zipfile.ZIP_DEFLATED
                    entry.external_attr = 0o100644 << 16
                    archive.writestr(entry, data, compresslevel=9)
        with zipfile.ZipFile(output) as archive:
            if sorted(archive.namelist()) != sorted(contents):
                raise PackageError("Archive member list differs from the explicit allowlist")
            for name, data in contents.items():
                if sha256(archive.read(name)) != sha256(data):
                    raise PackageError(f"Archive verification failed for {name}")
    except BaseException:
        if created:
            output.unlink(missing_ok=True)
        raise


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path(__file__).absolute().parent.parent)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--output", type=Path, help="New ZIP filename; an existing file is never replaced")
    parser.add_argument("--plan-only", action="store_true", help="Validate provenance and print allowlist; do not create an archive")
    parser.add_argument("--include-final-logs", action="store_true", help="Include only the final rehash/gate logs, each at most 8 MiB")
    args = parser.parse_args()
    if not args.plan_only and args.output is None:
        parser.error("--output is required unless --plan-only is used")
    try:
        root = args.project.expanduser().absolute()
        report_path = args.report.expanduser().absolute()
        contents, metadata = prepare(root, report_path, args.include_final_logs)
        result = {"status": "package_plan_not_created", "verified_report": str(report_path),
                  "source_module_count": metadata["source_module_count"],
                  "file_count": len(contents), "total_uncompressed_bytes": sum(map(len, contents.values())),
                  "allowlist": sorted(contents)}
        if not args.plan_only:
            output = args.output.expanduser().absolute()
            write_archive(output, contents)
            result.update(status="package_created", output=str(output),
                          archive_sha256=sha256(output.read_bytes()), archive_bytes=output.stat().st_size)
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0
    except (PackageError, verifier.VerificationError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"NO PACKAGE: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
