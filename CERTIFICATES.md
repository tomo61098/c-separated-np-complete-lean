# Polynomial certificates for the Gaussian gadget

`CSeparatedNPComplete.PolynomialCertificate.gadget_polynomial_certificate`
proves the certificate result for the original Gaussian gadget predicate,
with its existing `partition_schedule_threshold`. Its input assumptions are
the same as the main iff: `d > 1`, natural-square weights `s`, and half-total
at least one.

The certificate consists of **exactly `2d` bits**, one per coordinate. The
verifier accepts precisely when the selected and unselected coordinates have
equal counts and equal integer-weight sums. The existing gadget iff proves
that this is equivalent to feasibility of the constructed Gaussian instance.
Thus the checker can use integer addition and comparison throughout.

## Soundness and completeness

The verifier in `PolynomialCertificate.lean` maintains four accumulators:
selected count, unselected count, selected weight sum, and unselected weight
sum. It accepts if the two counts match and the two sums match.

`run_correct` proves that the executable recursion computes these quantities.
`verify_iff_partition` identifies acceptance with `is_ec_partition` for the
real selector obtained by casting the certificate bits to zero and one.

For soundness, an accepted certificate therefore gives an equal-cardinality
partition. The main gadget iff supplies the box constraints, required selector
cardinality, and Gaussian hinge inequality.

For completeness, any feasible selector satisfies `is_ec_partition` by the
same iff. In particular it is binary, so it has an exact finite Boolean
encoding. That encoding is accepted by the verifier. There is no need to
encode an arbitrary real witness or approximate its entries.

## Binary size and verification work

Encode each weight in binary, least significant bit first. Encode each data
bit `b` by the pair `0b`, and terminate each weight with `11`. This gives
an unambiguous binary encoding of the weight vector. Its length is

\[
L = 2\sum_{i=1}^{2d}(\operatorname{size}(s_i)+1).
\]

`encodeInput_length` proves this exact length. `certificate_length` proves
that the certificate has `2d` bits, and `dimension_le_inputBits` proves
`2d ≤ L`.

The checker uses an explicit binary-arithmetic cost model. Each addition or
comparison of operands `x,y` is charged

\[
8(\operatorname{size}(x)+\operatorname{size}(y)+1).
\]

This is a linear bit-work allowance for ripple-carry addition and padded
binary comparison. An unbounded-integer addition is therefore not a
constant-cost step. The `run` recursion accumulates these charges at its
actual intermediate operands, plus a unit charge for each branch. The final
cost also includes the two comparisons, conjunction, and a linear allowance
for reading the input and certificate.

The proof bounds the combined bit length of the four accumulators by
`B = Σᵢ(size(sᵢ)+3)`, with `B ≤ 3L`. It bounds the recursion's work by
`16*(2d)*(B+1)`. Including input reading and the final comparisons gives
the proved bound

\[
\operatorname{verificationWork}(s,b) \le 128(L+1)^2
\]

for **every** certificate, accepting or rejecting. `verificationWork_le`
proves this inequality. The cost theorem concerns these explicit bit-cost
semantics; a Turing-machine compilation and Lean's compiled execution time
are not formalized.

The final theorem packages soundness, completeness, certificate length,
and the quadratic verification bound into one iff. The input size here is
the binary encoding of the gadget's weight vector `s`; its scope is this
constructed family under the main theorem's assumptions. It does not assert
NP membership for arbitrary continuously weighted Gaussian instances.

## Verification

Run after `lake build`:

```text
lake env lean scripts/PolynomialCertificateChecks.lean
```

The checks cover acceptance, unequal-cardinality rejection, unequal-sum
rejection, increased work for longer binary operands, an end-to-end Gaussian
example, and axiom dependencies. The certificate machinery lives in the
library; `Solution.lean` retains Karamata and the two requested iff results.
