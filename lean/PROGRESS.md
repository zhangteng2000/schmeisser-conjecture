# Schmeisser formalization — verified

The all-degree theorem and optimality of the constant one in every fixed degree at least two have kernel-checked Lean proofs. The complete local import closure, rehashed builds, explicit theorem checks, and final axiom gate passed verification with the pinned toolchain.

## Fixed source and target

- Manuscript: attachment `ee247912-e198-4e55-b935-b17321383593/已粘贴的文本.txt`.
- Computational source commit: `9e958aec9d41c387d19a2485fa771895f09eda60` in the local `schmeisser-conjecture` repository.
- Lean: `v4.34.1`.
- mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612` (`v4.34.1`).
- Main target: for every complex polynomial of degree at least two whose zeros lie in the closed unit disk, every point of the real convex hull of its zeros is within distance one of a zero of its derivative.
- Sharpness target: in every degree at least two, no smaller uniform constant works; the witness is `X^n - 1` at `1`.

## Acceptance conditions

1. No `sorry`, `admit`, unproved auxiliary hypotheses, or additional axioms.
2. Final transitive axiom dependencies are a subset of `propext`, `Classical.choice`, and `Quot.sound`.
3. Computational certificates are justified by a proved checker and kernel-checked acceptance, including degree and interval coverage.
4. The final theorem type matches the mathematical target without hidden restrictions.
5. Rehashed builds of both entry points and the default target, followed by the rejecting axiom gate, succeed with unchanged source and control-file hashes.

## Components and build history

- The pinned environment is installed. All 8,908 official cache archives were successfully re-extracted through a short Windows path after incomplete long-path extraction was detected.
- `Schmeisser.Sharpness`: complete sharpness in every degree at least two; compiled and audited.
- `Schmeisser.Quadratic`: the full convex-hull conclusion in degree two, including repeated zeros; compiled and audited.
- `Schmeisser.Geometry`: diameter-ball covering for arbitrary real inner-product spaces, weighted reciprocal-moment covering, and two boundary/moment auxiliaries; 15 theorems compiled and audited.
- `Schmeisser.Basic`: Gauss-Lucas consequences, existence of critical points, and the origin case; compiled and audited.
- `Schmeisser.ScalarReduction`: the enlarged second moment and all comparison-point parameters, including the strict unit-disk bound; compiled and audited.
- `RootMoments`, `Reflection`, `NormalizedProduct`, and `ReflectedIntegral`: root enumeration with multiplicities, reciprocal identities, the boundary-root case, reflected polynomial comparison, and the normalized integral identity; compiled and audited.
- `NecessaryIntegrals`: failure of the actual polynomial moment criterion implies the two necessary integral inequalities, with the actual centred critical-point family; compiled and audited. No maximum over auxiliary families is needed.
- `IntegralComparison`, `ScalarIntegrals`, `AffineMoments`, and `CentredProduct`: endpoint comparison, first polar threshold, affine second moments, and centred-product interpolation; compiled and audited.
- `Hyperbolic` and `PolarLowerBound`: a direct differential proof of the hyperbolic majorant, and the strict product lower bound implied by the polar integral; compiled.
- `BetaIntegrals`, `ErrorBounds`, and `ErrorIntegrals`: the beta integral, actual-family pointwise error bounds, front integral, and both tail integral estimates; compiled.
- `NumericalBounds`: exact exponential estimates, logarithmic lower bounds for the degree parameter, and exponential-decay monotonicity; compiled.
- `QuadraticIntegrals`: true quadratic-integral recurrence, normalized recurrence, three initial bounds, vertex splitting, and the sharp `11/10` moment bound; all 49 statements compiled and audited.
- `Cubic`, `Rotation`, and `Assembly`: the cubic criterion and the complete polynomial/convex-hull assembly are proved. The assembly takes the explicitly stated scalar-exclusion proposition as a parameter, which `Main` instantiates with `scalar_exclusion`.
- `LargeDegreeExclusion`: the complete scalar exclusion for every critical-point count `m ≥ 6000` has compiled and passed its transitive axiom audit. This completes the infinite-degree scalar argument.
- `QuarticEndpoint`: the complete scalar exclusion near `u = 1` for critical-point count three has compiled and passed its axiom audit. Its polar test uses an elementary square-root inequality instead of Taylor's theorem.
- `PolarCertification`, `PolarThresholds`, and `FiniteReduction`: the strengthened polar test, exact polar integral, block thresholds, default comparison parameter, and final normalized-inequality bridge are compiled.
- `FiniteMomentBound`: the sharp moment lower bound for every integer in a degree block is compiled. `Certificates/BlockRecurrenceBridge` connects all three initial bounds (including the 16-panel trapezoid bound) and arbitrary recurrence depth to the actual normalized integral.
- `Certificates/BlockMomentBridge`, `BlockPolarBridge`, and `BlockScalarBridge` connect the checked expression language to the sharp moment estimate, the polar parameter test, and the actual scalar exclusion. These and the recurrence bridge have passed transitive axiom audits with only the three permitted axioms.
- `QuarticAnalytic` now proves the entire critical-point-count-three case by exact finite beta estimates and an explicit sum-of-squares identity. Its standard Lake build and transitive axiom audit passed. This removes all 6,464 count-three certificate intervals.
- `QuinticFiniteError`, `Certificates/Count4PolynomialBounds`, and `QuinticAnalytic` prove the entire critical-point-count-four case using exact finite beta estimates and two positive Bernstein representations. Their standard Lake builds and all 13 audited dependencies passed. This removes another 5,983 certificate intervals.
- `SexticFiniteError`, `Certificates/Count5PolynomialBounds`, and `SexticAnalytic` prove the entire critical-point-count-five case. Their standard Lake builds and all 15 audited dependencies passed. The proof uses an exact polynomial inequality, not subdivision certificates.
- `SepticFiniteError`, `Certificates/Count6PolynomialBounds`, and `SepticAnalytic` prove the entire critical-point-count-six case. Their standard Lake builds and 13-statement axiom audit passed. Its short rational coefficient table is kernel checked, and its two exact Bernstein identities replace subdivision certificates.
- The finite certificate collection now needs only critical-point counts 7 through 5999. The active `convex64` data contain 257 degree blocks, 7,653 terminal intervals, and 319 compilation chunks. All exported data passed exact integer replay matching the selected expression evaluator, including every saved selection mask. The fixed-point precision is 64 bits. All 257 blocks and their degree coverage have kernel-checked acceptance proofs; external replay is not treated as a proof.
- The revised `convex64` block `M129_131Verified` has passed its complete standard Lake build: Data, all 27 parameter intervals, coefficient bounds, and block assembly are accepted by the kernel. The measured full block run took 160.86 seconds, with a 3.379 GiB peak Lean working set. See `reports/kernel_build/M129_131_monitored.json`. These measurements apply only to this individual block.
- `FiniteDegreeReduction` combines the analytic counts three through six with a collection of verified blocks covering seven through 5999. Its standard Lake build passed. `FiniteDegreeExclusion` applies this result to the kernel-checked concrete collection.
- The convex-panel bound reduces the weighted panel count from 159,264 in the preceding data to 27,368 in the active collection. This is a preparation statistic, not a claim about elapsed kernel time.
- `ConvexPanelBounds` proves a sharper integral bound using convexity of the two factors and their opposite monotonicity. `Certificates/ConvexPanelBridge` proves that either certified panel bound may be selected independently on every panel. The selected bound uses exact rational panel endpoints and requires no assumption about the selection mask.
- `Certificates/BlockVerification` is complete: `VerifiedBlock.scalar_exclusion` deduces the actual scalar exclusion from a verified degree block. All five error branches, including the selected convex-panel bound, and all three rule types are covered, with no remaining analytic hypothesis. The integrated 73-module dependency graph passed standard Lake builds. The selected bridge, error bound, numerical interface, block exclusion, and coverage theorem passed the rejecting axiom gate in `reports/ConvexIntegrationAxioms.lean`; see `reports/convex-integration-axioms.log`.
- `Certificates/VerifiedCoverage` supplies the general coverage argument through `checkCoverageFrom_sound`. The concrete collection covers critical-point counts 7 through 5999; counts 3 through 6 are handled analytically.
- All 70 foundational modules required by `BlockVerification` and `VerifiedCoverage` have passed a dependency-ordered standard Lake build. The real Lake traces and logs are preserved in `reports/foundation-build/`; no trace files were fabricated.
- All statements audited so far depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- Interval arithmetic, expression-evaluation soundness, subdivision-tree coverage, and the original 261 consecutive degree ranges have kernel-checked proofs. The complete count-123 certificate has kernel-checked coverage and acceptance; `Certificates.Count123.scalar_exclusion` proves the actual scalar exclusion directly from the original assumptions and has passed its axiom audit. The final proof uses the revised 257-block collection. Count123 and the original 261-range layout are development history and are not dependencies of `Main`.

The authoritative manuscript copy has SHA256 `09c24f630cc5259ee2f2111029ffade4e34b45b05dfbcebb7a5fb7716d7a4084`.

## Windows build entry point

`D:/codex_data/schmeisser_lean` is a junction pointing to this project, not a separate checkout.
Use `scripts/lake.ps1` from this short path. The script sets exact repository ownership exceptions only in the current process; it does not modify global Git settings.
These local Windows helpers and historical production logs are not part of the
portable source archive. For an extracted archive, use the included
`scripts/verify_project.py` as described in `README.md`.

For an already built checkout: `./scripts/lake.ps1 build Schmeisser`.
For Lean flags such as `-o`, use an argument array: `./scripts/lake.ps1 -LakeArgs @('env','lean','-o','output.olean','Input.lean')`.

## Final verification

The complete production batch checked all 956 generated targets and exited
zero with unchanged source hashes. `Generated.AllVerified`,
`FiniteDegreeExclusion`, and `Main` have compiled, and the public
`Schmeisser.lean` entry point imports `Schmeisser.Main`.

Formal verification completed on 2026-11-17 at 05:13:51 UTC. The report is
`reports/verification-runs/20261117T051139Z-15692-80cbcc7c/report.json`.
Its status is `verified` and its mode is `aggregate-only`. All 24 commands
returned zero, including dependency-pin and tracked-source checks, two
rehashed no-build preflights, two final rehashed builds, and the rejecting
axiom gate. The report binds all 1,055 local Lean sources in the final import
closure and the control files by SHA256. Fresh-clone reproduction was not
performed as part of this verification; the portable procedure is documented
in `README.md`.

The final axiom dependencies are a subset of `propext`, `Classical.choice`,
and `Quot.sound`. The gate passed for `Schmeisser.main`,
`Schmeisser.sharpness`, `Schmeisser.universal_bound_iff`, and the audited
scalar-exclusion theorems. The manuscript's Schoenberg inequality itself is
not formalized; its role is replaced by the proved Cauchy and Newton estimates.

The portable verifier launches one Lake command at a time. Its default
launch thresholds are 6 GiB of available physical memory and, on Windows,
12 GiB of available commit headroom. These are launch thresholds, not
per-process memory limits or a minimum installed-RAM specification. Earlier
failed and interrupted attempts are preserved in local logs and do not
constitute acceptance. Historical production logs and local Windows helpers
are excluded from the portable source archive.

The original manuscript and original code repository are preserved without edits. Local reference copies must not be uploaded.
