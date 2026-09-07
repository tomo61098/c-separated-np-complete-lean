# Submission verification

After `lake build`, run:

```text
lake env lean --run scripts/Audit.lean
```

This imports Challenge and Solution into separate environments, compares the
main theorem's elaborated type and the Challenge's project definition bodies,
checks the main proof's transitive axioms, and rejects a Solution that imports
Challenge. It is a local preflight, not Comparator or independent kernel replay.

The GitHub Actions workflow runs the build and this audit, metadata validation
using Palomar's own pinned validator, license detection, and full Comparator
with NanoDa replay. The metadata job deliberately fails while required author
and maintainer fields are empty.

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

`verify-comparator.sh` and `landrun-wrapper.sh` were copied unchanged from
[PalomarTemplate at 128a6c5ce5f48622e69927ccd639cbff401022e8](https://github.com/PalomarRegistry/PalomarTemplate/tree/128a6c5ce5f48622e69927ccd639cbff401022e8/scripts),
under Apache-2.0. The repository's full Apache license text also comes from
that snapshot. CI pins the metadata validator to
[PalomarSubmission at c605f23466450a52999fcfb3c6d68ed8febc56bf](https://github.com/PalomarRegistry/PalomarSubmission/tree/c605f23466450a52999fcfb3c6d68ed8febc56bf).
When updating Lean or verification tools, review these pins together.

To run the metadata preflight locally, check out that PalomarSubmission
revision outside the tracked project files, install its `requirements.txt`,
and run:

```text
python scripts/validate-submission.py --policy-root PATH_TO_PALOMAR_SUBMISSION
```

This checks the working tree. Palomar itself verifies only the submitted,
publicly pushed commit; local success is not a registry verification result.
