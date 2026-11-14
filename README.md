# Schmeisser's conjecture: verification code

This repository contains the computational supplement for Schmeisser's
conjecture: certificate generation, independent integer verification, and
the recorded interval certificates. It contains code and computational data;
the manuscript and its LaTeX sources are not included.

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

The program verifies the finite inequalities and their coverage. The
mathematical reduction, the analytic endpoint cases, and the large-degree
argument belong to the separate manuscript. This repository is not a
proof-assistant formalization of the entire argument.

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

The distributed verification sources, certificates, and original receipts
are copied without modification. `SHA256SUMS.txt` covers this code-only
distribution. `.gitattributes` disables automatic line-ending conversion
so that checking out the repository on Windows or Unix preserves the bytes
used by the provenance checks.
