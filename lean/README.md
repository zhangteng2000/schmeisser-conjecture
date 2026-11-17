# Formalization of Schmeisser's conjecture

This project contains kernel-checked Lean proofs of Schmeisser's convex-hull
theorem for every degree at least two and of the optimality of the constant
one in each fixed degree. The complete local import closure, rehashed builds,
and final axiom gate passed verification with the pinned toolchain.

The statements concern `Polynomial ℂ`, its derivative, and the convex hull over `ℝ`. The formalization uses Lean 4 and mathlib at the versions pinned in `lean-toolchain` and `lakefile.toml`.

See `PROGRESS.md` for the current status and completion criteria. No successful external numerical computation is treated as a Lean proof.

## Proof structure

The polynomial argument reduces failure of the reciprocal-moment criterion to
two integral inequalities for the actual centred family of critical points.
The scalar exclusion is proved analytically for critical-point counts three,
four, five, six, and all counts at least 6000. The remaining finite range uses
kernel-checked interval certificates. Quadratic and cubic polynomials, multiple
zeros, and the geometric boundary cases are handled separately. The witness
`X^n - 1` proves sharpness in
every degree `n ≥ 2`.

| Polynomial degree | Proof modules |
| --- | --- |
| `2` | `Quadratic` |
| `3` | `Cubic` |
| `4`, `5`, `6`, `7` | `QuarticAnalytic`, `QuinticAnalytic`, `SexticAnalytic`, `SepticAnalytic` |
| `8` through `6000` | `FiniteDegreeReduction` and the generated certificates |
| At least `6001` | `LargeDegreeExclusion` |

`RootMoments` enumerates critical points with multiplicity. `NecessaryIntegrals`
uses this actual family in the integral estimates. `Assembly` combines the
scalar result with diameter-disk covering, rotations, repeated-root cases,
and boundary cases. `Schmeisser.Main` contains the unconditional theorem, and
the public `Schmeisser` entry point imports it.

Some intermediate arguments use replacement proofs: Cauchy estimates and
Newton identities supply the coefficient bounds, the hyperbolic estimate has
a direct differential proof, and the quartic endpoint uses an elementary
square-root inequality. The manuscript's Schoenberg inequality itself is not
formalized; its role is replaced by the Cauchy and Newton estimates. The
correspondence with the manuscript is listed in `reports/theorem-map.tsv`.

The finite verifier uses integer endpoints at scale `2^64`. Its arithmetic,
expression semantics, interval coverage, degree coverage, and analytic bounds
are proved in Lean. Generated acceptance statements use `decide +kernel`.
Python scripts generate and diagnose candidate data; their output is never
accepted as a mathematical premise. A proved convexity bound reduces the
quadrature workload: each panel uses one of two valid bounds, selected by an
untrusted mask that cannot affect the soundness theorem.

## Build and audit

The portable verification entry point is `scripts/verify_project.py`, included
in source archives. It requires Python 3.11+, Git, and Elan/Lake. Do not start it
while certificate builders are running. Its read-only preflight and a rebuild
from a newly extracted source archive are:

```text
python scripts/verify_project.py --plan-only
python scripts/verify_project.py --fetch-cache
```

`--fetch-cache` explicitly allows downloading the pinned dependencies and
mathlib cache. Omit it when these are already available. The driver builds
modules sequentially, rehashes both entry points and the default `lake build`
target, and runs the axiom gate. It applies Windows repository ownership
exceptions only to its own processes. See `scripts/verify_project.README.md`
for the memory thresholds, reports, and packaging order.

Once the complete project has been built and other builders have stopped,
`python scripts/verify_project.py --aggregate-only` avoids repeating each
individual module invocation. It first requires two rehashed Lake no-build
checks, then runs the same full builds and rejecting axiom gate. Missing or
stale artifacts fail this mode before the aggregate builds are attempted.
The report identifies which mode was actually used.

Source archives produced by `scripts/package_verified_source.py` contain the
complete local Lean import closure, version
pins, axiom gate, verification and packaging scripts, and their Python tests.
Dependencies, caches, generated build artifacts, manuscript files, local
Windows wrappers, and production event logs are excluded. The generated Lean
certificate sources are included; regenerating candidate data is not required
to rebuild them.

The final axiom gate checks the unconditional main theorem and degree-by-degree
optimality. It rejects every transitive axiom other than `propext`,
`Classical.choice`, and `Quot.sound`, and also checks the explicit theorem types.
Final verification completed on 2026-11-17 at 05:13:51 UTC in `aggregate-only`
mode. Both rehashed no-build preflights, both final rehashed builds, and the
rejecting axiom gate returned zero. Fresh-clone reproduction was not performed
as part of this verification; the procedure above is provided for rebuilding
the source archive. Source archives include the final report as
`verification/report.json`.

The local `reference/` directory contains the frozen manuscript and is excluded
from Git. It is not needed to check the Lean proofs.
