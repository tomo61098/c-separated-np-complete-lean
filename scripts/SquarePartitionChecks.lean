import Solution

/-!
Checks for the source construction and the unconditional ordinary-PARTITION
reduction to equal-cardinality partition of positive squares.
Run with `lake env lean scripts/SquarePartitionChecks.lean` after `lake build`.
-/

open CSeparatedNPComplete

private def weights (i : ℕ) : ℕ := if i = 3 then 3 else 1
private def choice (i : ℕ) : Bool := i == 3

-- All source hypotheses hold for the positive input (1, 1, 1, 3).
example : ∀ i, i < 4 → weights i ≤ 2 ^ (2 * i) := by
  intro i hi
  interval_cases i <;> norm_num [weights]

-- Its constructed square vector has a paired equal-cardinality partition.
example : is_ec_partition (SquarePartition.selector 4 choice)
    (SquarePartition.values 4 weights 2) := by
  apply (square_choice_is_ec_partition_iff 4 weights 2 choice (by norm_num) ?_).mpr
  · norm_num [SquarePartition.chooseSum, Fin.sum_univ_succ, weights, choice]
  · intro i hi
    interval_cases i <;> norm_num [weights]

-- But the original input cannot be split into equal-size, equal-sum parts.
example : ¬ ∃ a : Vec 4, is_ec_partition a ![1, 1, 1, 3] := by
  rintro ⟨a, hbin, hcard, hsum⟩
  have hlast := hbin (3 : Fin 4)
  norm_num [dot, Fin.sum_univ_succ] at hcard hsum
  change a 0 + (a 1 + (a 2 + a 3)) = 2 at hcard
  change a 0 + (a 1 + (a 2 + a 3 * 3)) = 3 at hsum
  rcases hlast with h | h <;> nlinarith

-- A first weight greater than one needs no source-style root-bound hypothesis.
example : ∃ x : Vec 4, is_ec_partition x (SquareReduction.values ![2, 2]) := by
  apply (partition_iff_square_ec_partition 2 ![2, 2]).mp
  refine ⟨![1, 0], ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num
  · norm_num [dot, Fin.sum_univ_succ]

-- No arbitrary target selector can turn the no-instance (1, 2) into a yes-instance.
example : ¬ ∃ x : Vec 4, is_ec_partition x (SquareReduction.values ![1, 2]) := by
  intro h
  obtain ⟨p, hp, hs⟩ := (partition_iff_square_ec_partition 2 ![1, 2]).mpr h
  have h0 := hp 0
  have h1 := hp 1
  norm_num [dot, Fin.sum_univ_succ] at hs
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> norm_num [h0, h1] at hs

-- The new construction outputs only positive squares.
example : perf_square_vec (SquareReduction.values ![1, 1, 1, 3]) ∧
    ∀ i, 0 < SquareReduction.values ![1, 1, 1, 3] i :=
  square_reduction_positive_squares 4 ![1, 1, 1, 3]

run_cmd do
  for name in #[
      `CSeparatedNPComplete.square_partition_implies_partition_for_choice,
      `CSeparatedNPComplete.exists_square_partition_implies_exists_partition,
      `CSeparatedNPComplete.exists_square_partition_iff_exists_partition,
      `CSeparatedNPComplete.square_choice_is_ec_partition_iff,
      `CSeparatedNPComplete.SquarePartition.values_perfect_square,
      `CSeparatedNPComplete.partition_iff_square_ec_partition,
      `CSeparatedNPComplete.square_reduction_positive_squares,
      `CSeparatedNPComplete.SquareReduction.encode_bound,
      `CSeparatedNPComplete.SquareReduction.base_bound,
      `CSeparatedNPComplete.SquareReduction.encode_injective] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Forbidden axiom in {name}: {axiomName}"
    Lean.logInfo m!"{name}: {axioms}"
