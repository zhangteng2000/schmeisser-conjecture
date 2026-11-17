The portable verification entry point requires Python 3.11+, Git, and Elan/Lake.
It uses the versions pinned in `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`. Run it after other certificate builders have stopped.
On Windows, use a short checkout or an existing short junction path; the script
does not create junctions or move the checkout.

```text
python scripts/verify_project.py --plan-only
python scripts/verify_project.py --fetch-cache
```

`--plan-only` reads the import graph, checks the entry points and version pins,
and scans the main import closure for forbidden proof constructs after removing
comments and strings. It runs no Lean, Git, or network commands and writes no
verification result. Use `--show-order` to inspect the complete build order.
The plan includes the physical and commit thresholds, timeout, query sources,
and whether this platform supports the commit check. It does not query memory
or wait for headroom.

`--fetch-cache` explicitly permits fetching the pinned mathlib cache. Omit it
when the pinned dependencies and cache are already available. `--project PATH`
selects a checkout independently of the current directory; `--lake PATH`
selects the Lake executable. Dependency commits and tracked-source cleanliness
are checked, and the actual Lean version must match the pinned release.
No drive letter is embedded in the script.

By default, verification runs one project module at a time in dependency order,
including `Schmeisser.Main` and the library root. This is the mode for a fresh
source checkout. Actual verification requires the public `Schmeisser.lean`
entry point to import `Schmeisser.Main`; plan mode reports whether it does.

For a checkout whose entire import closure has already been built, use:

```text
python scripts/verify_project.py --aggregate-only
```

This mode first runs `lake --rehash --no-build build Schmeisser.Main Schmeisser`
and `lake --rehash --no-build build`. Both must return zero before the three
final commands are permitted. A missing or stale target stops verification;
the driver does not fall back to an unrestricted rebuild. Prepare or repair
such a checkout using the default sequential mode. `--aggregate-only` cannot
be combined with `--fetch-cache`. Keep other builders and source editors
stopped throughout the run. The source/control hashes are checked before and
after every command in this mode. Its report explicitly says `aggregate-only`
and contains no invented per-module build records.

The two modes perform the same dependency-pin, tracked-source-cleanliness,
Lean-version, full source-scan, final-build, and axiom checks. The aggregate
mode avoids repeated Lake startup for modules that are already up to date.
Lake 4.34.1 has no `--jobs` option; `LEAN_NUM_THREADS=1` is not asserted to be a
limit on simultaneous compiler subprocesses. The two no-build checks prevent
starting an aggregate rebuild of an unfinished checkout. They do not replace
the final build or the axiom gate.

Both modes set `LEAN_NUM_THREADS=1`
and waits for at least 6 GiB of available physical memory before each Lake
command. On Windows, it also requires at least 12 GiB of available commit
headroom. The independent `GlobalMemoryStatusEx` call reads `ullAvailPhys` and
`ullAvailPageFile`; both thresholds must be satisfied before launching Lake.
Free physical memory alone does not ensure that enough commit remains.
`--memory-reserve-gib` and `--commit-reserve-gib` change the respective launch
thresholds. They accept finite, nonnegative GiB values; zero disables only that
threshold. `--memory-timeout` sets a finite, nonnegative wait deadline in seconds;
its default of zero waits without a deadline. Waiting and timeout messages show
both available values and their thresholds.

Linux uses `/proc/meminfo`'s `MemAvailable` for the physical-memory gate only.
It explicitly reports that no commit check is available; the Windows commit
threshold is not enforced on Linux. Unsupported platforms report that neither
memory check is available. These are launch-headroom checks, not per-process
memory limits. Lake remains responsible for building external
dependency artifacts; fetching the pinned cache avoids a cold mathlib rebuild.

The final three commands in both modes are `lake --rehash build Schmeisser.Main Schmeisser`,
`lake --rehash build`, and `lake env lean reports/AxiomGate.lean`.
A successful result is written only if
every command returns zero and the source/control-file hashes remain unchanged.
The axiom gate is mandatory. No build trace or hash file is synthesized.

Each actual run creates a separate directory under
`reports/verification-runs/` with command logs and `report.json`. Its status is
`verified` only after the final axiom gate succeeds. Failed or interrupted runs
remain explicitly marked as such. `--logs PATH` changes the parent directory.
The existing production event logs are untouched. Git ownership exceptions are
limited to this process and the exact project/dependency paths; global Git
configuration is not changed.

For final delivery, first let every production certificate builder finish.
Before starting verification, make the public `Schmeisser.lean` entry point
import `Schmeisser.Main` and freeze the Lean sources and control files. The
verification report binds every local Lean source in the import closure plus
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, and
`reports/AxiomGate.lean` by SHA256. Changing any of them after verification
requires a new successful verification run before packaging.

`README.md`, `PROGRESS.md`, `reports/theorem-map.tsv`, and the Python tools are
not bound by the verification report. Finish tooling changes before the final
run so that the packaged verifier matches the one used. Update completion claims in those
documents only after the real verification command succeeds, and before
creating the source ZIP. The packager records their exact bytes as an additional
source snapshot in `PACKAGE_MANIFEST.json` and `SHA256SUMS`; it does not claim
that documentation was checked by Lean. Do not edit a verification report to
change its status.

After a successful run, use its actual `report.json` path:

```text
python scripts/package_verified_source.py --report REPORT_PATH --plan-only
python scripts/package_verified_source.py --report REPORT_PATH --include-final-logs --output NEW_ARCHIVE.zip
```

Packaging accepts either explicitly identified verification mode, checking
its actual command sequence. Aggregate reports must include both successful
no-build preflights followed by all three final commands; sequential reports
must include every module in dependency order followed by those final commands.
Packaging rejects incomplete verification, changed proof sources or controls,
and a public entry point that does not import `Schmeisser.Main`. It includes
the full local import closure, the pinned build files, the verifier and packager
with their Python tests, and the final documentation snapshot. It excludes
dependencies, build artifacts, manuscripts, local Windows helpers, and
production logs. The output ZIP must be new and its parent directory must
already exist. Packaging verifies every written archive member and prints the
archive SHA256. None of these instructions assert that final verification has
already succeeded.
