# Gaussian separation and equal-cardinality partition

The project's main intended complexity statement is that **selecting features
to relatively c-separate Gaussian classes, in the formulation of Borozan
et al., is NP-hard**. Relative separation compares differences between class
means with within-class variation. The motivation is to select a small set
of marker genes that jointly distinguishes cell types, and to understand
the effect of allowing fractional feature weights.

The Gaussian c-separation feature-selection formulation comes from
Bartol Borozan, Luka Borozan, Domagoj Ševerdija, Domagoj Matijević, and Stefan Canzar,
[*Optimal Marker Genes for c-Separated Cell Types*](https://doi.org/10.1007/978-3-031-90252-9_53),
RECOMB 2025, pp. 424–427.

This repository translates the accompanying Rocq development to Lean 4.
The current formalized result is the gadget equivalence
`CSeparatedNPComplete.partition_gadget_schedule_partition_iff`, the final
theorem in [sepsolve.v, line 2782](RocqOld/sepsolve.v#L2782). It is the sole
Palomar submission target. The full NP-hardness reduction is not yet
formalized; the exact proved statement and its scope are described below.
The formalization author and responsible maintainer is Tomislav Prusina.

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
or NP membership of a decision problem, and approximation guarantees are
outside its scope.

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

`Solution.lean` also proves the general `Karamata_inequality` as an
auxiliary theorem; it is not a separate submission target.
Karamata holds in every finite dimension for convex functions on
convex domains. Here `majorized u v` means that descending `u` majorizes
descending `v`, so the sum of `f` over `u` is at least its sum over `v`.

The Karamata proof uses mathlib's `ConvexOn.secant_mono`,
`AntitoneOn.exists_antitone_extension`, and `Finset.sum_range_by_parts`.
Equal coordinates are handled by extending secant slopes. No continuity,
differentiability, or strict convexity is assumed. The main gadget theorem
uses the direct reciprocal inequality from the Rocq proof.

The paired-square results from [RocqOld/Square.v](RocqOld/Square.v) are also
translated, including `square_partition_implies_partition_for_choice` and
`exists_square_partition_implies_exists_partition`. The translation proves
the converse for paired choices and connects the construction to the
existing `perf_square_vec` and `is_ec_partition` predicates. These are
auxiliary results; the sole Comparator target remains the Gaussian gadget
theorem.

**Equal-cardinality partition of positive perfect squares is NP-complete**
by a polynomial-time injective reduction from ordinary positive-integer
PARTITION. The strengthened construction uses
`K = 2 + n + 2*Σaᵢ + Σaᵢ²` and pairs
`(K^(n+i) ± aᵢ*K^(n−i))²` for `i = 1, …, n`.
Every balanced output partition is proved to split each pair.
`partition_iff_square_ec_partition` in `Solution.lean` states the unconditional
equivalence, with no caller-supplied base bounds and no restriction on the
target selector. Lean also proves positive-square outputs, injectivity of
the natural-number encoding, and numerical output-size bounds.

[SQUARE_PARTITION.md](SQUARE_PARTITION.md) gives the construction and the
NP-completeness proof. The polynomial-time and NP-membership arguments are
mathematical prose, using the standard NP-completeness of PARTITION; a
machine-model NP-completeness theorem is not formalized in Lean. The source
problem imposes no cardinality restriction: for example, `(1,1,1,3)` is a
yes-instance of ordinary PARTITION despite having no equal-cardinality
partition. Positive yes- and no-instances and the axiom dependencies are
checked in [scripts/SquarePartitionChecks.lean](scripts/SquarePartitionChecks.lean).

## Build

```text
lake build
lake env lean --run scripts/Audit.lean
lake env lean scripts/SquarePartitionChecks.lean
```

The main theorem is proved directly in `Solution.lean`, and
`lake build` passes. Its axiom dependencies are exactly `propext`,
`Classical.choice`, and `Quot.sound`. The Comparator package contains one
compared theorem, `partition_gadget_schedule_partition_iff`, with an
independent `Challenge.lean` statement and a proof in `Solution.lean`.
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
<https://submit.palomar-registry.org/>.
