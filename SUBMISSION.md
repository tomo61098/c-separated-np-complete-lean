# Palomar submission

The sole compared result is
`CSeparatedNPComplete.partition_gadget_schedule_partition_iff`.
It is a pointwise equivalence with a selector-dependent threshold; the entry
does not claim a complete NP-hardness reduction. See [README.md](README.md)
and the independent [Challenge.lean](Challenge.lean) for the mathematical scope.

Local checks on 2026-09-07 passed: the full Lean build, equality of the
independent theorem types and 42 definition bodies, the standard-three-axiom
audit, and Solution's independence from Challenge. The pinned Palomar metadata
validator reports only the missing human authors and responsible maintainers.
Full Comparator/NanoDa replay and submission have not yet occurred.

Before selecting the final snapshot:

1. Fill `project.authors` and `project.responsible_maintainers` in
   [formalization.yaml](formalization.yaml) with confirmed human names. Update
   the pending-authorship notes in that file and the README. Credit the
   unpublished manuscript and original Rocq proofs when their authorship is
   confirmed; do not copy the PDF's template author block.
2. Run `lake build` and `lake env lean --run scripts/Audit.lean`.
3. Commit and push the changes, then require all three jobs in
   [Submission checks](https://github.com/tomo61098/c-separated-np-complete-lean/actions/workflows/ci.yml)
   to pass at that commit, including Comparator and NanoDa replay.
4. Obtain the full 40-character SHA with `git rev-parse HEAD`. If anything
   changes after the checks, push and verify the new commit.

Use these submission fields:

| Field | Value |
| --- | --- |
| Repository | `tomo61098/c-separated-np-complete-lean` |
| Commit | Full SHA of the final pushed and checked commit |
| Project path | Leave blank (repository root) |
| Comparator path | Leave blank (default `comparator.json`) |
| Metadata path | Leave blank (default `formalization.yaml`) |
| Existing Palomar ID | Leave blank for a first registration |
| Authorization | Select the truthful author/maintainer or approved-submitter relationship |

Humans submit at [the Palomar submission form](https://submit.palomar-registry.org/)
and authenticate with GitHub. Keep the private status-page link: Palomar does
not send email notifications. An agent must use the
[agent protocol](https://submit.palomar-registry.org/llms.txt), which verifies
write access with a temporary tag and a gist, rather than automate the form.

After mechanical verification, read the editorial review. Registration is a
separate decision that permanently publishes the registry record and review;
an agent must show the review and obtain an explicit instruction to register.

The authoritative requirements are the
[submission guide](https://palomar-registry.org/how-to-submit) and
[submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md).
The CI tool versions are pinned for reproducibility; Palomar may have updated
its service checks since those revisions.
