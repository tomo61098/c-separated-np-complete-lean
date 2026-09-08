import CSeparatedNPComplete

/-!
# The partition gadget and Gaussian schedule equivalence

Gaussian c-separation, in the feature-selection formulation of Borozan et al.,
motivates selecting marker genes that distinguish cell types while accounting
for within-type variation. The project's intended complexity statement is
NP-hardness of this relative separation problem. The current Lean result is
the gadget equivalence below. Its construction studies continuous feature
weights in the unit cube under a fixed cardinality constraint. Its three-class
gadget enforces the partition balance; the schedule's reciprocal correction is
tight only at binary selectors.

The main theorem proves the exact pointwise equivalence in `RocqOld/sepsolve.v:2782`. The
threshold depends on the selector's coordinate zero. A fixed-threshold complexity
reduction and its encoding bounds are not asserted by this theorem.
The auxiliary results include general Karamata inequality and a strengthened
square construction based on `RocqOld/Square.v`. An explicit base gives an
unconditional equivalence from ordinary PARTITION to equal-cardinality partition
of positive squares, for arbitrary target selectors. The natural-number encoding
is injective and has proved numerical size bounds. Together with the standard
NP-completeness of positive-integer PARTITION, this gives NP-completeness of the
square restriction by the polynomial-time argument in `SQUARE_PARTITION.md`.
That complexity argument is mathematical prose; no machine-model NP-completeness
theorem is asserted in Lean.
The main theorem is stated independently in `Challenge.lean`; this module does
not import Challenge.
-/

namespace CSeparatedNPComplete

/-- Karamata's inequality for every finite dimension, including zero.
This is the predicate-domain formulation of `RocqOld/Karamata.v:Karamata_inequality`. -/
theorem Karamata_inequality
    (n : Nat) (P : Real → Prop) (f : Real → Real) (u v : Vec n)
    (hconv : convexOnPredicate P f)
    (Pu : ∀ i, P (u i)) (Pv : ∀ i, P (v i))
    (hmajorized : majorized u v) :
    vecSum (fun i => f (u i)) ≥ vecSum (fun i => f (v i)) := by
  exact hmajorized.sum_convex_le ((convexOnPredicate_iff_convexOn P f).mp hconv) Pu Pv

/-- Ordinary PARTITION reduces to equal-cardinality partition of positive
perfect squares. The construction chooses its own base, so there are no `hK`
or `hbound` assumptions. The target existential ranges over every selector.

For positive integer inputs, the encoding is a polynomial-time injective
many-one reduction; see `SQUARE_PARTITION.md` for the complexity argument and
`SquareReduction.encode_bound`, `base_bound`, and `encode_injective` for the
formal arithmetic and injectivity results. -/
theorem partition_iff_square_ec_partition (n : ℕ) (a : Fin n → ℕ) :
    SquareReduction.HasPartition a ↔
      ∃ x : Vec (n + n), is_ec_partition x (SquareReduction.values a) :=
  (SquareReduction.exists_ec_partition_iff a).symm

/-- The explicit Gaussian construction satisfies its threshold constraint exactly
for equal-cardinality partition selectors. This is the main submission result,
corresponding to `RocqOld/sepsolve.v:partition_gadget_schedule_partition_iff`.

For `2*d` perfect-square entries with half-total at least one and `d > 1`, the
left side allows every selector in the unit cube with total weight `d`. The
inequality forces binary coordinates and the partition balance. -/
theorem partition_gadget_schedule_partition_iff
    (d : Nat) (a s : Vec (2 * d))
    (hd : 1 < d) (hc : 1 ≤ dot s 1 / 2) (hs : perf_square_vec s) :
    (box_constraints a ∧ dot a 1 = (d : ℝ) ∧
      hinge_form (dot s 1 / 2) a (partition_gadget_schedule d s) ≤
        partition_schedule_threshold d a s) ↔ is_ec_partition a s :=
  partition_gadget_schedule_pointwise_iff d a s hd hc hs

end CSeparatedNPComplete
