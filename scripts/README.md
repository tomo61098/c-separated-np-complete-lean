# Submission verification

After `lake build`, run:

```text
lake env lean --run scripts/Audit.lean
lake env lean scripts/SquarePartitionChecks.lean
lake env lean scripts/PolynomialCertificateChecks.lean
```

This imports Challenge and Solution into separate environments, compares the
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
incur more verification work.

The GitHub Actions workflow runs the build and this audit, metadata validation
using Palomar's own pinned validator, license detection, and full Comparator
with NanoDa replay. The metadata job checks required authorship and maintainer
fields along with the other submission metadata.

On Linux with Lean/Elan, Git, Python 3, Cargo, and Go installed, run:

```sh
chmod +x scripts/landrun-wrapper.sh
bash scripts/verify-comparator.sh
```

The script fetches and builds pinned Comparator, lean4export, NanoDa, and
Landrun revisions. It requires the exporter and project Lean toolchains to
match and leaves NanoDa enabled. Its default download directory is the ignored
`.cache/palomar-comparator/`. Landrun requires Linux; Git Bash on Windows cannot
provide the full replay environment.

The pinned Comparator builds with Lean 4.33.0-rc1, while the project and its
exporter use Lean 4.32.0. Both installations are required by these tool pins.
The Comparator CI job frees space by removing the unused Android and .NET
SDKs from its disposable GitHub-hosted runner before installing Lean. It also
disables automatic full Mathlib cache downloads and restores. The replay
script downloads only the project's direct Mathlib imports and their
transitive dependencies, after building the verification tools.

`verify-comparator.sh` and `landrun-wrapper.sh` originated from
[PalomarTemplate at 128a6c5ce5f48622e69927ccd639cbff401022e8](https://github.com/PalomarRegistry/PalomarTemplate/tree/128a6c5ce5f48622e69927ccd639cbff401022e8/scripts),
under Apache-2.0. The replay script now limits Mathlib caching as described
above; the wrapper and verification tool pins are unchanged.
The repository's full Apache license text also comes from
that snapshot. CI pins the metadata validator to
[PalomarSubmission at c605f23466450a52999fcfb3c6d68ed8febc56bf](https://github.com/PalomarRegistry/PalomarSubmission/tree/c605f23466450a52999fcfb3c6d68ed8febc56bf).
When updating Lean or verification tools, review these pins together.

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
```

This checks the working tree. Palomar itself verifies only the submitted,
publicly pushed commit; local success is not a registry verification result.
