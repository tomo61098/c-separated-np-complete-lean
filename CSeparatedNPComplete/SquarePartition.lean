import CSeparatedNPComplete.PartitionBasic

/-!
# The paired-square construction

Each input weight produces two natural-number squares. A Boolean choice places
one square from every pair on each side. Under the source's root bound, equality
of these two sums is equivalent to partitioning the original weights.

This proves correctness for paired choices. It does not assert that every
equal-cardinality partition of the squares respects the pairs, or formalize
polynomial-time reductions or NP-completeness.
-/

namespace CSeparatedNPComplete.SquarePartition

/-- The larger square in input coordinate `i`'s pair. -/
def plus (N : ℕ) (a : ℕ → ℕ) (K i : ℕ) : ℕ :=
  (K ^ (N + i) + a i * K ^ (N - i)) ^ 2

/-- The smaller square, using natural subtraction. -/
def minus (N : ℕ) (a : ℕ → ℕ) (K i : ℕ) : ℕ :=
  (K ^ (N + i) - a i * K ^ (N - i)) ^ 2

/-- Sum of the original weights selected by a Boolean choice. -/
def chooseSum (m : ℕ) (a : ℕ → ℕ) (b : ℕ → Bool) : ℕ :=
  ∑ i : Fin m, if b i then a i else 0

/-- One square from each pair: larger when the Boolean choice is true. -/
def leftSum (N m : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool) : ℕ :=
  ∑ i : Fin m, if b i then plus N a K i else minus N a K i

/-- The complementary square from each pair. -/
def rightSum (N m : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool) : ℕ :=
  ∑ i : Fin m, if b i then minus N a K i else plus N a K i

theorem square_gap (u v : ℕ) (h : v ≤ u) :
    (u + v) ^ 2 = (u - v) ^ 2 + 4 * u * v := by
  have hsub := Nat.sub_add_cancel h
  nlinarith

theorem upper_bound_root (N K i ai : ℕ) (hi : i ≤ N)
    (ha : ai ≤ K ^ (2 * i)) : ai * K ^ (N - i) ≤ K ^ (N + i) := by
  calc
    ai * K ^ (N - i) ≤ K ^ (2 * i) * K ^ (N - i) := Nat.mul_le_mul_right _ ha
    _ = K ^ (N + i) := by rw [← pow_add]; congr 1; omega

theorem root_product (N K i ai : ℕ) (hi : i ≤ N) :
    K ^ (N + i) * (ai * K ^ (N - i)) = ai * K ^ (2 * N) := by
  calc
    K ^ (N + i) * (ai * K ^ (N - i)) = ai * (K ^ (N + i) * K ^ (N - i)) := by ring
    _ = ai * K ^ (2 * N) := by rw [← pow_add]; congr 2; omega

theorem gap (N : ℕ) (a : ℕ → ℕ) (K i : ℕ) (hi : i < N)
    (ha : a i ≤ K ^ (2 * i)) :
    plus N a K i = minus N a K i + 4 * K ^ (2 * N) * a i := by
  unfold plus minus
  rw [square_gap _ _ (upper_bound_root N K i (a i) (by omega) ha)]
  have h := root_product N K i (a i) (by omega)
  nlinarith

theorem right_as_left (N m : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool) :
    rightSum N m a K b = leftSum N m a K (fun i => !(b i)) := by
  apply Finset.sum_congr rfl
  intro i _
  cases hb : b i <;> simp [hb]

theorem left_decomp (N m : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool)
    (hm : m ≤ N) (hbound : ∀ i, i < m → a i ≤ K ^ (2 * i)) :
    leftSum N m a K b = (∑ i : Fin m, minus N a K i) +
      4 * K ^ (2 * N) * chooseSum m a b := by
  unfold leftSum chooseSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hg := gap N a K i (by omega) (hbound i i.isLt)
  cases b i <;> simp [hg]

/-- Both directions hold for choices that take one square from every pair. -/
theorem for_choice_iff (N : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool)
    (hK : 1 ≤ K) (hbound : ∀ i, i < N → a i ≤ K ^ (2 * i)) :
    leftSum N N a K b = rightSum N N a K b ↔
      chooseSum N a b = chooseSum N a (fun i => !(b i)) := by
  rw [right_as_left, left_decomp N N a K b le_rfl hbound,
    left_decomp N N a K (fun i => !(b i)) le_rfl hbound]
  have hfactor : 0 < 4 * K ^ (2 * N) := by positivity
  constructor <;> intro h <;> nlinarith

/-- List the larger squares first and then the smaller squares, as a real vector. -/
def values (N : ℕ) (a : ℕ → ℕ) (K : ℕ) : Vec (N + N) :=
  Fin.append (fun i : Fin N => (plus N a K i : ℝ))
    (fun i : Fin N => (minus N a K i : ℝ))

/-- A binary selector that chooses exactly one square from each pair. -/
def selector (N : ℕ) (b : ℕ → Bool) : Vec (N + N) :=
  Fin.append (fun i : Fin N => if b i then 1 else 0)
    (fun i : Fin N => if b i then 0 else 1)

theorem values_perfect_square (N : ℕ) (a : ℕ → ℕ) (K : ℕ) :
    perf_square_vec (values N a K) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine ⟨K ^ (N + j.val) + a j.val * K ^ (N - j.val), ?_⟩
    simp only [values, Fin.append_left]
    simp [plus, pow_two]
  · intro j
    refine ⟨K ^ (N + j.val) - a j.val * K ^ (N - j.val), ?_⟩
    simp only [values, Fin.append_right]
    simp [minus, pow_two]

theorem selector_binary (N : ℕ) (b : ℕ → Bool) : is_binary (selector N b) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [selector, Fin.append_left]
    cases b j <;> simp
  · intro j
    simp only [selector, Fin.append_right]
    cases b j <;> simp

theorem selector_card (N : ℕ) (b : ℕ → Bool) : dot (selector N b) 1 = (N : ℝ) := by
  simp only [dot, Fin.sum_univ_add, selector, Fin.append_left, Fin.append_right,
    Pi.one_apply, mul_one]
  rw [← Finset.sum_add_distrib]
  have h (i : Fin N) : (if b i then (1 : ℝ) else 0) + (if b i then 0 else 1) = 1 := by
    cases b i <;> norm_num
  simp_rw [h]
  simp

theorem selected_sum (N : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool) :
    dot (selector N b) (values N a K) = (leftSum N N a K b : ℝ) := by
  simp only [dot, Fin.sum_univ_add, selector, values, Fin.append_left, Fin.append_right]
  rw [← Finset.sum_add_distrib]
  simp only [leftSum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases b i <;> simp

theorem total_sum (N : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool) :
    dot (values N a K) 1 = (leftSum N N a K b : ℝ) + (rightSum N N a K b : ℝ) := by
  simp only [dot, Fin.sum_univ_add, values, Fin.append_left, Fin.append_right,
    Pi.one_apply, mul_one, leftSum, rightSum, Nat.cast_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases b i <;> simp [add_comm]

/-- The connection to the existing real-vector equal-cardinality predicate. -/
theorem selector_is_ec_partition_iff (N : ℕ) (a : ℕ → ℕ) (K : ℕ) (b : ℕ → Bool) :
    is_ec_partition (selector N b) (values N a K) ↔
      leftSum N N a K b = rightSum N N a K b := by
  have hbin := selector_binary N b
  have hcard := selector_card N b
  rw [is_ec_partition, selected_sum, total_sum N a K b]
  constructor
  · rintro ⟨_, _, h⟩
    exact_mod_cast (show (leftSum N N a K b : ℝ) = (rightSum N N a K b : ℝ) by linarith)
  · intro h
    refine ⟨hbin, ?_, ?_⟩
    · rw [hcard]
      push_cast
      ring
    · rw [h]
      ring

end CSeparatedNPComplete.SquarePartition
