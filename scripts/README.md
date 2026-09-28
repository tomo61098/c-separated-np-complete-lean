# Submission verification

After `lake build`, run:

```text
lake env lean --run scripts/Audit.lean
lake env lean scripts/SquarePartitionChecks.lean
lake env lean scripts/PolynomialCertificateChecks.lean
```

`Audit.lean` imports Challenge and Solution into separate environments, compares the
main theorem's elaborated type and the Challenge's project definition bodies,
checks the main proof's transitive axioms, and rejects a Solution that imports
Challenge. It is a local preflight, not Comparator or independent kernel replay.

`SquarePartitionChecks.lean` checks the source paired-square results and the
unconditional ordinary-PARTITION reduction. Its positive yes-instance `(2,2)`
exercises a first weight greater than one; its no-instance `(1,2)` rules out
arbitrary balanced output selectors. It also checks positive-square outputs,
the distinction between ordinary and equal-cardinality source partitions,
and the axiom dependencies of correctness, injectivity, and size bounds.

`PolynomialCertificateChecks.lean` checks the executable certificate verifier,
its connection to the original Gaussian predicate, and the certificate-length
and quadratic bit-work theorem dependencies. It includes positive-square
acceptance, count and sum rejections, and a check that longer integer operands
incur more verification work. It also checks the fixed threshold, quarter-integer
arithmetic, coverage of coordinate zero, and rejection of balanced fractional
selectors, and audits the quarter-integrality theorem's axioms.

The GitHub Actions workflow runs the build and this audit, metadata validation
using Palomar's own pinned validator, license detection, and full Comparator
with NanoDa and con-ron replay. The metadata job checks required authorship and
maintainer fields, the supported Lean version, and the module headers and size
limits for tracked Lean files.

On Linux with Lean/Elan, Git, Python 3, and bubblewrap (`bwrap`) installed, run:

```sh
bash scripts/verify-comparator.sh
```

The script runs `lake comparator` from the project's Lean 4.35.0-rc2 toolchain.
That release bundles `leanexport`, `leanchecker`, NanoDa, and con-ron, so the
single `lean-toolchain` pin selects all tools that judge the proof. The script
requires every bundled checker and registers both independent kernels in a
temporary configuration, as Palomar does. The legacy `enable_nanoda` field is
ignored; `external_kernels` must not appear in the submitted `comparator.json`.
Bubblewrap requires Linux; Git Bash on Windows cannot provide the full replay
environment.

The Comparator CI job frees space by removing the unused Android and .NET
SDKs from its disposable GitHub-hosted runner before installing Lean. It also
disables automatic full Mathlib cache downloads and restores. The replay
script downloads only the project's direct Mathlib imports (including public
imports) and their transitive dependencies.

`verify-comparator.sh` follows the bundled-tool workflow from
[PalomarTemplate at 2891de4c48955af824969a263d31b25e7a9a1406](https://github.com/PalomarRegistry/PalomarTemplate/tree/2891de4c48955af824969a263d31b25e7a9a1406/scripts),
under Apache-2.0, with the selective Mathlib caching described above.
The repository's full Apache license text comes from
[PalomarTemplate at 128a6c5ce5f48622e69927ccd639cbff401022e8](https://github.com/PalomarRegistry/PalomarTemplate/tree/128a6c5ce5f48622e69927ccd639cbff401022e8).
CI pins the metadata validator to
[PalomarSubmission at 65f0154ed776cd26c224254aa57b379137f28b0d](https://github.com/PalomarRegistry/PalomarSubmission/tree/65f0154ed776cd26c224254aa57b379137f28b0d).
When updating Lean or Palomar's submission requirements, review this validator
pin as well.

CI installs the validator's dependencies from `scripts/requirements-metadata.txt`
with hash verification enabled. This retains upstream's PyYAML 6.0.3 pin and
hashes and adds the published hash for the CPython 3.12 Linux x86_64 wheel,
which the pinned upstream requirements omit. The added hash was checked
against PyPI's release metadata and the downloaded wheel.

To run the metadata preflight locally, check out that PalomarSubmission
revision outside the tracked project files, then run:

```text
python -m pip install --require-hashes -r scripts/requirements-metadata.txt
python scripts/validate-submission.py --policy-root PATH_TO_PALOMAR_SUBMISSION
python scripts/test-validate-submission.py --policy-root PATH_TO_PALOMAR_SUBMISSION
```

This checks the working tree. Palomar itself verifies only the submitted,
publicly pushed commit; local success is not a registry verification result.
