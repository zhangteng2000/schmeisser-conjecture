# Schmeisser's conjecture: Lean proof and verification code

This repository contains a complete Lean formalization of Schmeisser's
convex-hull theorem and its optimal constant, together with the original
computational supplement. The manuscript and its LaTeX sources are not included.

Paper: Teng Zhang, [*A proof of Schmeisser's conjecture*](https://arxiv.org/abs/2611.19084)
(arXiv:2611.19084).

## Lean formalization

The project in [`lean/`](lean/) proves that, for every complex polynomial of
degree at least two whose zeros lie in the closed unit disk, each point in
the convex hull of the zeros is within distance one of a critical point.
The constant one is optimal in every fixed degree at least two.

- [`Schmeisser.main`](lean/Schmeisser/Main.lean): the all-degree theorem.
- [`Schmeisser.universal_bound_iff`](lean/Schmeisser/Main.lean): the optimal
  universal constant in each degree.
- [`Schmeisser.sharpness`](lean/Schmeisser/Sharpness.lean): the witness `X^n - 1`.
- [`lean/README.md`](lean/README.md): proof structure and build instructions.
- [`verification/report.json`](lean/verification/report.json) and
  [`the final axiom audit`](lean/verification/final-axiom-gate.log): verification
  results for the supplied sources.

The proof uses Lean 4.34.1 and pinned mathlib dependencies. It contains no
`sorry`, `admit`, or additional axioms; the final transitive axiom dependencies
are `propext`, `Classical.choice`, and `Quot.sound`. The finite certificates
are checked by the Lean kernel.

To rebuild and audit the formalization, install Python 3.11+, Git, and
Elan/Lake, then run from the repository root:

```sh
cd lean
python scripts/verify_project.py --fetch-cache
```

The following sections describe the original Python supplement and its
independent finite-certificate replay.

## Verify the supplied certificates

Use Python 3.10 or later. Verification requires only the Python standard
library and does not require network access or additional packages.
Run the following command from the repository root:

```sh
python verify_all.py --workers 4
```

To retain a fresh verification report:

```sh
python verify_all.py --workers 4 --report replay.json
```

Do not use Python's `-O` or `-OO` options: the launcher rejects optimization
mode because the verification uses assertions. Fresh certificate replay
receipts are written to a temporary directory, leaving the supplied inputs
unchanged. The optional `replay.json` is a local output and is ignored by Git.

The verifier checks file hashes, the degree-range coverage, every terminal
interval, and 33 exact rational comparisons. The interval arithmetic uses
outward-rounded integers with scale `2^192`.

## Coverage

The certificates cover all critical-point counts `3 <= n-1 <= 5999`,
corresponding to polynomial degrees `4 <= n <= 6000`.

| Critical-point count `n-1` | Degree-range blocks | Tree nodes | Terminal intervals |
| --- | ---: | ---: | ---: |
| 3-19 | 17 | 27,319 | 13,668 |
| 20-128 | 109 | 4,977 | 2,543 |
| 129-5999 | 135 | 7,657 | 3,896 |
| **Total** | **261** | **39,953** | **20,107** |

The source code and certificate format retain the identifier `N` for `n-1`.
These original identifiers and files are preserved to keep the recorded
source and certificate hashes valid.

The Python program verifies the finite inequalities and their coverage.
The complete formal proof, including the mathematical reduction, endpoint
cases, and large-degree argument, is supplied separately in [`lean/`](lean/).

## Files

- `verify_all.py`: portable verification entry point.
- `SHA256SUMS.txt`: checksums for the distributed code, data, and repository
  documentation.
- `work/verify_mass_scalar_integer_v4.py`: independent certificate verifier.
- `work/mass_integer_arithmetic.py`: integer interval-arithmetic kernel.
- `work/uniform_large_degree_constants.py`: the 33 exact rational checks.
- `work/certify_mass_scalar_v4.py` and `work/mass_arb_helpers.py`: certificate
  generator and its Arb helpers.
- `work/run_mass_scalar_v4_batch.py`: batch generation and independent replay.
- `work/assemble_mass_proof.py`: provenance and coverage audit used to
  assemble the manifest.
- `work/mass_proof_manifest.json`: frozen source hashes and all 261 ranges.
- `work/mass_scalar_v4_certificates/`: compressed subdivision trees and
  the original generation and verification receipts.
- The other JSON files in `work/` record the original completed batch and
  exact-constant checks.

## Optional certificate generation

Replaying the supplied certificates is sufficient to reproduce the finite
verification. Generation additionally requires `python-flint` and uses
Arb arithmetic at 112-bit precision.

To generate one range into a separate local output directory, run:

```sh
python -m pip install python-flint
python work/certify_mass_scalar_v4.py --lo 3 --hi 3 --folder regenerated
```

The output is placed in `work/regenerated/`, which Git ignores. Full batch
regeneration writes to the original certificate directory, so perform it
only in a separate working copy. Regenerated compressed files and timing
receipts need not have the same hashes as the frozen release.

## File integrity

The original verification sources, certificates, and receipts are unchanged.
`SHA256SUMS.txt` covers that supplement and its repository documentation;
[`lean/SHA256SUMS`](lean/SHA256SUMS) covers the verified Lean distribution.
`.gitattributes` disables automatic line-ending conversion so that checking
out the repository on Windows or Unix preserves the bytes used by the
provenance checks.
