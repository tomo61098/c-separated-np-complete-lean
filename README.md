# NP-hardness of Gaussian c-separation

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

This repository develops and proves an original reduction construction in Lean 4.
The main Lean result is the gadget equivalence
`CSeparatedNPComplete.partition_gadget_schedule_partition_iff`. It is the sole
Palomar submission target. The exact proved statement and its scope are described below.
The formalization author and responsible maintainer is Tomislav Prusina.

## Proof idea

First, we prove that **equal-cardinality partition of positive perfect squares
is NP-complete**, by reducing ordinary positive-integer PARTITION to it.
This supplies the discrete problem encoded by the Gaussian construction.
The square restriction has a concrete purpose: the Gaussian means contain
`√sᵢ`, so square weights make those coordinates integral.

The square reduction outputs pairs `(uᵢ+vᵢ)², (uᵢ−vᵢ)²`. Their total is
`2*Σᵢ(uᵢ²+vᵢ²)`, hence `c = Σsᵢ/2` is also an integer. The output
dimension `d` is even, so `m = d/2` is integral. The displayed Gaussian
formulas therefore give integer means and diagonal covariances. The fixed threshold is an integer multiple of `1/4` for all
natural input weights. The Gaussian-data integrality argument concerns
outputs of the square reduction; the main iff allows more general square
inputs and fractional selectors.

Three Gaussians enforce the partition equation: their combined hinge penalty
vanishes exactly when the selected weights sum to half the total. A second
block enforces binary selectors. In the implemented construction, this block
is a **schedule of `d+1` Gaussians**. Its objective contains reciprocal terms,
and the bound `1/(1+x) ≤ 1−x/2` is tight exactly at `x = 0` or `x = 1`.
Attaining the required total bound forces every selector coordinate to be
one of these endpoints.

The two blocks are placed far apart using the explicit mean offsets and
scaling. Every pair with one Gaussian in each block then has zero hinge
penalty under the box and cardinality constraints. Their objectives add,
so feasibility forces both partition balance and binary selection.
Conversely, any equal-cardinality partition attains the stated bound.
This gives the gadget iff, with `d+4` Gaussian classes in total.

The detailed square reduction and complexity argument are in
[SQUARE_PARTITION.md](SQUARE_PARTITION.md). The polynomial certificate proof
for the constructed Gaussian predicate is explained in
[CERTIFICATES.md](CERTIFICATES.md).

## Main statement and scope

For `d ≥ 4`, let `s` have `d` coordinates, each the square of a natural
number, with `c = dot s 1 / 2 ≥ 1`. The target theorem states, for every
selector `a`, the equivalence between:

- `a` lies in `[0,1]^d`, its coordinates sum to `d/2`, and the hinge
  objective of `partition_gadget_schedule d s` is at most
  `partition_schedule_threshold d s`;
- `a` is binary, selects exactly `d/2` coordinates, and satisfies
  `dot a s = dot s 1 / 2`.

The construction has dimension `d` and `d+4` Gaussian classes: a
three-class partition gadget and a schedule of `d+1` classes. Its fixed
threshold is

```math
\frac{s^T\mathbf{1}}{2}\,\frac{d(d+1)}{2}-\frac{3d}{4}.
```

Every coordinate contributes to the schedule's reciprocal sum. Under the
box and cardinality constraints, this sum is at most `3d/4`, with equality
exactly for binary selectors. This upper bound is attained when `d` is even.
For odd `d`, a binary selector cannot have coordinate sum `d/2`, so both
sides of the equivalence are false. Lean proves that the threshold is an integer multiple of
`1/4` for natural input weights in
`partition_schedule_threshold_quarter_integral`.
The library additionally proves a polynomial certificate theorem for this
constructed predicate. General Gaussian NP membership, the full reduction's
encoding bounds, and machine-model complexity theorems remain outside the
formalized scope.

Here a Gaussian class is represented by its mean and diagonal covariance
vectors; the theorem does not construct probability measures. Zero input
coordinates are allowed, so individual covariance coordinates may vanish.
Real division uses Lean's total convention `D / 0 = 0`; the proof handles
the gadget's denominators under the stated hypotheses. The original contribution
is the reduction construction and its proofs; the Gaussian feature-selection
formulation and standard background results are credited above and below.

## Auxiliary library results

`Solution.lean` also proves the general `Karamata_inequality` as an
auxiliary theorem; it is not a separate submission target.
Karamata holds in every finite dimension for convex functions on
convex domains. Here `majorized u v` requires both vectors to already be
sorted in descending order, with every prefix sum of `u` at least that of
`v` and equal total sums. The sum of `f` over `u` is then at least its sum
over `v`.

The Karamata proof uses mathlib's `ConvexOn.secant_mono`,
`AntitoneOn.exists_antitone_extension`, and `Finset.sum_range_by_parts`.
Equal coordinates are handled by extending secant slopes. No continuity,
differentiability, or strict convexity is assumed. The main gadget theorem
uses the direct reciprocal inequality.

The paired-square results are also proved in Lean, including `square_partition_implies_partition_for_choice` and
`exists_square_partition_implies_exists_partition`. The Lean development proves
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
machine-model NP-completeness theorem is not formalized in Lean. The reduction
maps `n` input weights to `2n` positive squares. An equal-sum partition of the
input, whatever the sizes of its two parts, gives an equal-sum partition of
the constructed squares with exactly `n` entries on each side. Conversely,
every equal-cardinality partition of the constructed squares gives a partition
of the input. Thus the construction preserves both yes- and no-instances.
Concrete yes- and no-instances and the axiom dependencies are
checked in [scripts/SquarePartitionChecks.lean](scripts/SquarePartitionChecks.lean).

For the constructed Gaussian family under the main theorem's assumptions,
`PolynomialCertificate.gadget_polynomial_certificate` proves that a feasible
selector exists exactly when an accepted Boolean certificate exists. The
certificate has exactly `d` bits, one per feature coordinate. The executable
verifier checks that the selected and unselected coordinates have equal
counts and equal sums of the natural weights `sᵢ`.

The gadget equivalence proves both directions: every accepted certificate
gives a selector satisfying the fixed Gaussian threshold, and every feasible
selector is binary and supplies an accepted certificate. Verification therefore
uses integer arithmetic; it does not require approximate real-number evaluation
of the Gaussian objective.

Let `L = 2*Σᵢ(Nat.size(sᵢ)+1)` be the length of the delimited binary encoding
of the weight vector `s`, which determines this Gaussian instance. Lean proves
`d ≤ L` and bounds verification work by `128*(L+1)^2` for every certificate
in the explicit binary-arithmetic cost model. This bound measures the integer
verifier's work. See [CERTIFICATES.md](CERTIFICATES.md) for the encoding,
cost model, and scope.

## Build

```text
lake build
lake env lean --run scripts/Audit.lean
lake env lean scripts/SquarePartitionChecks.lean
lake env lean scripts/PolynomialCertificateChecks.lean
```

`Solution.lean` contains Karamata and the square and Gaussian iff results;
their supporting proofs are in the library. The main proof's axiom dependencies are exactly `propext`,
`Classical.choice`, and `Quot.sound`. The Comparator package contains one
compared theorem, `partition_gadget_schedule_partition_iff`, with an
independent `Challenge.lean` statement and a proof in `Solution.lean`.
The definitions are explicit, so `definition_names` is empty.
Deliberate Challenge `sorry` placeholders are permitted by the
[Palomar submission guide](https://palomar-registry.org/how-to-submit);
solution proofs must be complete and independent of Challenge.

Local checks on 2026-09-09 passed: the full build, the square-partition and
certificate checks, and the main-theorem audit. In that audit, the independent main-theorem types and all 42
checked definition bodies match, and Solution does not import Challenge.
Local Lean checks of the auxiliary Karamata and gadget results have passed.
The development uses AI assistance. Independent human mathematical review
and Palomar submission have not been reported; successful full Comparator
verification has not yet been confirmed.

The repository is licensed under [Apache-2.0](LICENSE). The
[verification scripts](scripts/README.md) and GitHub Actions workflow provide
reproducible submission checks. Follow [SUBMISSION.md](SUBMISSION.md) to
select a verified, pushed commit and submit it at
<https://submit.palomar-registry.org/>.
