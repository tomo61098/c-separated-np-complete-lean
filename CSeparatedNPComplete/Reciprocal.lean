import CSeparatedNPComplete.PartitionBasic

namespace CSeparatedNPComplete

/-- The chord bound for the reciprocal potential on the unit interval. -/
theorem inv_one_plus_le_line (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    (1 + x)⁻¹ ≤ 1 - x / 2 := by
  rw [inv_le_iff₀ (by linarith : 0 < 1 + x)]
  nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]

/-- The chord is attained exactly at the two binary endpoints. -/
theorem inv_one_plus_line_eq_binary_iff (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    (1 + x)⁻¹ = 1 - x / 2 ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    have he := congrArg (fun z : ℝ => z * (1 + x)) h
    rw [inv_mul_cancel₀ (by linarith : 1 + x ≠ 0)] at he
    have hp : x * (1 - x) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

private theorem sum_line {n : Nat} (a : Vec n) :
    (∑ i, (1 - a i / 2)) = (n : ℝ) - dot a 1 / 2 := by
  simp [Finset.sum_sub_distrib, Finset.sum_div, dot]

theorem full_correction_le_line {n : Nat} (a : Vec n) (ha : box_constraints a) :
    (∑ i, (1 + a i)⁻¹) ≤ (n : ℝ) - dot a 1 / 2 := by
  rw [← sum_line]
  exact Finset.sum_le_sum fun i _ => inv_one_plus_le_line (a i) ⟨ha.1 i, ha.2 i⟩

theorem full_correction_eq_binary_iff {n : Nat} (a : Vec n) (ha : box_constraints a) :
    (∑ i, (1 + a i)⁻¹) = (n : ℝ) - dot a 1 / 2 ↔ is_binary a := by
  rw [← sum_line]
  constructor
  · intro he i
    have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ (1 - a j / 2) - (1 + a j)⁻¹ :=
      fun j _ => sub_nonneg.mpr (inv_one_plus_le_line (a j) ⟨ha.1 j, ha.2 j⟩)
    have hsum : (∑ j, ((1 - a j / 2) - (1 + a j)⁻¹)) = 0 := by
      rw [Finset.sum_sub_distrib, he, sub_self]
    have hi := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum i (Finset.mem_univ i)
    exact (inv_one_plus_line_eq_binary_iff (a i) ⟨ha.1 i, ha.2 i⟩).mp
      (by linarith)
  · intro hb
    apply Finset.sum_congr rfl
    intro i _
    exact (inv_one_plus_line_eq_binary_iff (a i) ⟨ha.1 i, ha.2 i⟩).mpr (hb i)

/-- The threshold restores the schedule's missing coordinate-zero correction. -/
theorem schedule_full_correction_eq_sum {n : Nat} (a : Vec n) (hn : 0 < n) :
    (1 + dot a (canon_e 0))⁻¹ + gaussian_schedule_hinge_correction a (n - 1) =
      ∑ i, (1 + a i)⁻¹ := by
  let f : Nat → ℝ := fun j => (1 + dot a (canon_e j))⁻¹
  have hn' : n - 1 + 1 = n := by omega
  have hsum := Finset.sum_range_succ' f (n - 1)
  rw [hn'] at hsum
  calc
    _ = ∑ j ∈ Finset.range n, f j := by
      rw [hsum]
      simp only [f, gaussian_schedule_hinge_correction]
      ring
    _ = ∑ i : Fin n, (1 + a i)⁻¹ := by
      rw [Finset.sum_range]
      simp only [f, dot_canon_e_eq]

end CSeparatedNPComplete
