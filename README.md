# Gaussian separation and equal-cardinality partition

This repository translates the accompanying Rocq development to Lean 4.
Its submission target is
`CSeparatedNPComplete.partition_gadget_schedule_partition_iff`, the final
theorem in [sepsolve.v, line 2782](RocqOld/sepsolve.v#L2782). The motivation is to
select a small set of marker genes that separates Gaussian models of cell
types, and to understand the effect of allowing fractional feature weights.

The accompanying unpublished manuscript,
[*On the NP-Hardness of Feature-Weighted Gaussian c-Separation with Relaxed
Selection*](c_separation_NP_completness-4.pdf), supplies the mathematical
context. Its introduction attributes the Gaussian c-separation formulation
to Bartol Borozan, Luka Borozan, Domagoj Ševerdija, Domagoj Matijević, and
Stefan Canzar,
[*Optimal Marker Genes for c-Separated Cell Types*](https://doi.org/10.1007/978-3-031-90252-9_53),
RECOMB 2025, pp. 424–427. This published article supplies background; the
local manuscript and Rocq development supply the translated construction.
The manuscript's template author block is not used as an attribution.
Formalization authors and responsible maintainers await confirmation.

## Main statement and scope

For `d > 1`, let `s` have `2*d` coordinates, each the square of a natural
number, with `c = dot s 1 / 2 ≥ 1`. The target theorem states, for every
selector `a`, the equivalence between:

- `a` lies in `[0,1]^(2*d)`, its coordinates sum to `d`, and the hinge
  objective of `partition_gadget_schedule d s` is at most
  `partition_schedule_threshold d a s`;
- `a` is binary, selects exactly `d` coordinates, and satisfies
  `dot a s = dot s 1 / 2`.

The construction has dimension `2*d` and `2*d + 3` Gaussian classes: a
three-class partition gadget and a schedule of `2*d` classes. Writing
`k = 2*d - 1`, its threshold is
`c*k*(k+1)/2 - (3*d/2 - 1/(1+a₀))`. This threshold depends on the
selector's zeroth coordinate. The formalization concerns this pointwise
equivalence. Polynomial construction size and running time, NP-hardness
or NP membership of a decision problem, and the manuscript's LP and PTAS
results are outside its scope.

Here a Gaussian class is represented by its mean and diagonal covariance
vectors; the theorem does not construct probability measures. Zero input
coordinates are allowed, so individual covariance coordinates may vanish.
Real division uses Lean's total convention `D / 0 = 0`; the proof handles
the gadget's denominators under the stated hypotheses. No novelty claim is
made for the mathematical result.

The proof combines the gadget equality, vanishing interactions with the
schedule, an exact schedule objective formula, and the reciprocal bound
`1/(1+x) ≤ 1-x/2` on `[0,1]`, whose equality case forces binary
coordinates. The `.v` files in `RocqOld/` provide reference proofs and are not compiled
by the Lean project.

## Auxiliary library results

The library also proves `c_separates_zero` and general
`Karamata_inequality`. These are auxiliary results, not separate submission
targets. Karamata holds in every finite dimension for convex functions on
convex domains. Here `majorized u v` means that descending `u` majorizes
descending `v`, so the sum of `f` over `u` is at least its sum over `v`.

The Karamata proof uses mathlib's `ConvexOn.secant_mono`,
`AntitoneOn.exists_antitone_extension`, and `Finset.sum_range_by_parts`.
Equal coordinates are handled by extending secant slopes. No continuity,
differentiability, or strict convexity is assumed. The main gadget theorem
uses the direct reciprocal inequality from the Rocq proof.

## Build

```text
lake build
lake env lean --run scripts/Audit.lean
```

The main theorem is proved in `CSeparatedNPComplete/Partition.lean`, and
`lake build` passes. Its axiom dependencies are exactly `propext`,
`Classical.choice`, and `Quot.sound`. The Comparator package contains one
compared theorem, `partition_gadget_schedule_partition_iff`, with an
independent `Challenge.lean` statement and a proof imported by `Solution.lean`.
The definitions are explicit, so `definition_names` is empty.
Deliberate Challenge `sorry` placeholders are permitted by the
[Palomar submission guide](https://palomar-registry.org/how-to-submit);
solution proofs must be complete and independent of Challenge.

The local audit also passes: the independent main-theorem types and all 42
checked definition bodies match, and Solution does not import Challenge.
Local Lean checks of the auxiliary Karamata and gadget results have passed.
The development uses AI assistance. Independent human mathematical review,
full Comparator verification, and Palomar submission have not occurred.

The repository is licensed under [Apache-2.0](LICENSE). The
[verification scripts](scripts/README.md) and GitHub Actions workflow provide
reproducible submission checks. Follow [SUBMISSION.md](SUBMISSION.md) to
select a verified, pushed commit and submit it at
<https://submit.palomar-registry.org/>. Required human authorship and
maintainer names still await confirmation.
