# Equal-cardinality partition of positive squares is NP-complete

The source problem is ordinary **PARTITION on positive integers**, encoded in
binary. The target asks whether a list of positive perfect squares can be split
into two parts with equal cardinalities and equal sums. Repeated entries are
allowed and retain their indices. The reduction below is polynomial-time and
injective on ordered instances.

Lean proves its unconditional correctness, positive-square outputs,
injectivity, and numerical size bounds. The running-time argument, NP
membership, and use of the known NP-completeness of PARTITION are given here
as mathematical proofs; they are not machine-model complexity theorems in Lean.

## Construction

For input weights `a₁, …, aₙ ≥ 1`, set

\[
S=\sum_{i=1}^n a_i,\qquad Q=\sum_{i=1}^n a_i^2,\qquad
K=2+n+2S+Q.
\]

For each `i = 1, …, n`, output the pair

\[
u_i=K^{n+i},\quad v_i=a_iK^{n-i},\qquad
x_i^+=(u_i+v_i)^2,\quad x_i^-=(u_i-v_i)^2.
\]

The ordered output lists all `xᵢ⁺` followed by all `xᵢ⁻`. There are `2n`
entries. Since `aᵢ < K ≤ K^(2i)`, we have `0 ≤ vᵢ < uᵢ`; consequently
both squares are strictly positive. The index in the exponents starts at
**one**, so there is no artificial restriction `a₁ ≤ 1`.

The computable natural-number output is `SquareReduction.encode a`.
`SquareReduction.values a` is the same vector cast to real numbers for the
existing `is_ec_partition` predicate. `SquareReduction.base a` supplies `K`;
the theorem requires neither `hK` nor `hbound`.

## Correctness

The identity

\[
x_i^+-x_i^-=4u_iv_i=4a_iK^{2n}
\]

proves the forward direction. Given an ordinary partition, put `xᵢ⁺` on the
first side precisely when `aᵢ` is selected, and otherwise put `xᵢ⁻` there.
Put the other square on the second side. Each side has `n` elements, and
their sum difference is `4K^(2n)` times the original sum difference.

For the reverse direction, consider **any** equal-sum split of the output.
Let `pᵢ, qᵢ ∈ {0,1}` indicate whether `xᵢ⁺, xᵢ⁻` are on its first side.
Set `δᵢ = pᵢ + qᵢ − 1` and `ηᵢ = pᵢ − qᵢ`. Expanding the square sums gives

\[
0=\sum_i\delta_iK^{2n+2i}
  +\sum_i\left(2\eta_i a_iK^{2n}
       +\delta_i a_i^2K^{2(n-i)}\right).
\]

Write `C = 2S + Q`. The second sum has absolute value at most `C K^(2n)`
because `|δᵢ|, |ηᵢ| ≤ 1`. Suppose some `δᵢ` is nonzero and choose the
largest such index `j`. Put `T = K^(2n+2j−2) > 0`.

The leading term has absolute value `K²T`. Every smaller marker term has
absolute value at most `T`; their total is bounded by `nT`. The second sum
is bounded by `CT`, since `K^(2n) ≤ T`. Cancellation would imply
`K²T ≤ (n+C)T`, contradicting `K = 2+n+C` and `K² > n+C`.

Therefore every `δᵢ` vanishes: the split selects exactly one square from
every pair. The displayed equality reduces to
`Σᵢ (2pᵢ−1)aᵢ = 0`, which is an ordinary partition of the input. This
argument even derives the target cardinality from equality of sums.

The unconditional equivalence is
`CSeparatedNPComplete.partition_iff_square_ec_partition` in `Solution.lean`.
Its target existential ranges over every selector, not only paired selectors.
The decisive helper is `SquareReduction.forces_pairs`.

## Polynomial time and injectivity

Let `M = maxᵢ aᵢ`. The proved bounds are

\[
K\le 2+n+2nM+nM^2,\qquad
x_i^\pm\le K^{4(n+1)}.
\]

Thus `log₂ K = O(log(n+1)+log(M+1))`, and each output entry has
`O(n(log(n+1)+log(M+1)))` bits. The whole output has polynomial length in
the binary input length. These numerical inequalities are proved in
`SquareReduction.base_bound` and `SquareReduction.encode_bound`.

Compute `S`, `Q`, and `K`, then compute the table `K⁰, …, K^(2n)` by
successive multiplication. Form each pair with multiplication, addition,
subtraction, and squaring. There are `O(n)` arithmetic operations, on
integers of polynomial bit length. The usual binary arithmetic algorithms
therefore compute the reduction in polynomial time. A small output bound
alone would not suffice; this explicit algorithm supplies the time argument.

For injectivity, the output length recovers `n`. Each ordered pair recovers
`uᵢ` and `vᵢ` from its positive square roots: their half-sum is `uᵢ` and
their half-difference is `vᵢ`. For a nonempty instance, `u₁ = K^(n+1)`
uniquely determines the positive base, and then `vᵢ/K^(n−i)` recovers `aᵢ`.
`SquareReduction.encode_injective` proves this for each length. Hence the
reduction is one-to-one on ordered instances. Karp (many-one) reducibility
does not itself require this additional injectivity property.

## NP-completeness

Ordinary positive-integer PARTITION is NP-complete; see Richard M. Karp,
[*Reducibility Among Combinatorial Problems*](https://doi.org/10.1007/978-1-4684-2001-2_9),
in *Complexity of Computer Computations* (1972), pp. 85–103
([author's reprint](https://www.cs.umd.edu/~gasarch/BLOGPAPERS/Karp.pdf)).
The polynomial-time correctness-preserving reduction above proves NP-hardness
of equal-cardinality partition restricted to positive squares.

For NP membership, a certificate supplies one subset bit per entry and the
positive integer square roots of the entries. The verifier squares the roots,
checks the subset cardinality, and adds the selected and unselected entries
to compare their sums. The certificate has polynomial binary length, and
each verification step uses polynomial-time integer arithmetic. Thus the
target problem is in NP and is **NP-complete**.

The auxiliary paired-choice lemmas have additional assumptions.
The strengthened construction above supplies the
arbitrary-selector reverse direction and explicit base that those lemmas
alone did not provide. The source is ordinary PARTITION; its selected weights
need not have equal cardinality.

## Why the Gaussian construction uses squares

The partition gadget uses `√sᵢ` in its mean vectors. Restricting EC partition
to square weights makes these roots integers while retaining an NP-complete
source problem. The paired output also satisfies

\[
\sum_i(x_i^+ + x_i^-) = 2\sum_i(u_i^2+v_i^2),
\]

so `c = Σsᵢ/2` is integral. The output dimension `d` is even, so the
schedule base `m = d/2`, schedule means `m^j`, separation sums
`Σⱼ(m^i−m^j)²`, and scale `γ` are integers too. Inspection of the
formulas in `PartitionDefs.lean` then shows that all constructed Gaussian
means and diagonal covariances are integral. This is the arithmetic reason
for first reducing to square EC partition.

The fixed threshold is

\[
T(s,d)=\frac{\sum_i s_i}{2}\frac{d(d+1)}{2}-\frac{3d}{4}
      =\frac{(\sum_i s_i)d(d+1)-3d}{4}.
\]

For natural input weights the numerator is an integer, so the threshold
is a multiple of `1/4` and has at most two fractional binary digits.
This holds independently of the selector and is proved in Lean by
`partition_schedule_threshold_quarter_integral`. The Gaussian-data
integrality argument above remains prose.

Three Gaussians impose the partition equation. A schedule of `d+1` Gaussians
forces binary selection: its class at index `i+1` uses feature coordinate
`i`, covering every coordinate including zero. The full reciprocal sum is
at most `d - (d/2)/2 = 3d/4`, with equality exactly at binary selectors.
The explicit shifts and scales separate the two blocks enough that every
cross-block pair contributes zero hinge penalty. The resulting `d+4`-class
construction combines the two conditions in the main iff with the fixed
threshold above.
