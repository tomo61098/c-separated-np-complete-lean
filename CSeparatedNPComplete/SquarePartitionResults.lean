import CSeparatedNPComplete.SquareReduction

namespace CSeparatedNPComplete

/-- A paired-square partition implies a partition of the original weights.
The square partition here chooses exactly one square from each constructed pair. -/
theorem square_partition_implies_partition_for_choice
    (N : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool)
    (hK : 1 ≤ K) (hbound : ∀ i, i < N → a i ≤ K ^ (2 * i))
    (h : SquarePartition.leftSum N N a K b = SquarePartition.rightSum N N a K b) :
    SquarePartition.chooseSum N a b = SquarePartition.chooseSum N a (fun i => !(b i)) :=
  (SquarePartition.for_choice_iff N a K b hK hbound).mp h

/-- Existence of a paired-square partition implies existence of an original-weight partition.
The conclusion balances the original sums; it does not impose original cardinality. -/
theorem exists_square_partition_implies_exists_partition
    (N : ℕ) (a : ℕ → ℕ) (K : ℕ)
    (hK : 1 ≤ K) (hbound : ∀ i, i < N → a i ≤ K ^ (2 * i))
    (h : ∃ b, SquarePartition.leftSum N N a K b = SquarePartition.rightSum N N a K b) :
    ∃ b, SquarePartition.chooseSum N a b = SquarePartition.chooseSum N a (fun i => !(b i)) := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, square_partition_implies_partition_for_choice N a K b hK hbound hb⟩

/-- The paired-choice result also holds in the forward direction. -/
theorem exists_square_partition_iff_exists_partition
    (N : ℕ) (a : ℕ → ℕ) (K : ℕ)
    (hK : 1 ≤ K) (hbound : ∀ i, i < N → a i ≤ K ^ (2 * i)) :
    (∃ b, SquarePartition.leftSum N N a K b = SquarePartition.rightSum N N a K b) ↔
      ∃ b, SquarePartition.chooseSum N a b = SquarePartition.chooseSum N a (fun i => !(b i)) := by
  exact exists_congr fun b => SquarePartition.for_choice_iff N a K b hK hbound

/-- A paired Boolean choice yields an equal-cardinality partition of the square
vector exactly when it balances the original weights. Every coordinate of this
vector is a natural square, by `SquarePartition.values_perfect_square`. -/
theorem square_choice_is_ec_partition_iff
    (N : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool)
    (hK : 1 ≤ K) (hbound : ∀ i, i < N → a i ≤ K ^ (2 * i)) :
    is_ec_partition (SquarePartition.selector N b) (SquarePartition.values N a K) ↔
      SquarePartition.chooseSum N a b = SquarePartition.chooseSum N a (fun i => !(b i)) :=
  (SquarePartition.selector_is_ec_partition_iff N a K b).trans
    (SquarePartition.for_choice_iff N a K b hK hbound)

/-- Every output coordinate of the unconditional reduction is a strictly
positive natural square. -/
theorem square_reduction_positive_squares (n : ℕ) (a : Fin n → ℕ) :
    perf_square_vec (SquareReduction.values a) ∧
      ∀ i, 0 < SquareReduction.values a i :=
  ⟨SquareReduction.values_perfect_square a, SquareReduction.values_positive a⟩

end CSeparatedNPComplete
