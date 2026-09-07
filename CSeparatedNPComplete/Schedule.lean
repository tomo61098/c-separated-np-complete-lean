import CSeparatedNPComplete.PartitionBasic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace CSeparatedNPComplete

theorem gaussian_schedule_separation_sum_le (m : ℝ) (i : ℕ) {k l : ℕ}
    (hkl : k ≤ l) :
    gaussian_schedule_separation_sum m i k ≤ gaussian_schedule_separation_sum m i l := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkl)
    (fun _ _ _ => sq_nonneg _)

theorem gaussian_schedule_separation_sum_ge_1 {m : ℝ} {j : ℕ}
    (hm : 2 ≤ m) (hj : 0 < j) :
    1 ≤ gaussian_schedule_separation_sum m j j := by
  have hm1 : 1 ≤ m := by linarith
  have hp : m ≤ m ^ j := le_self_pow₀ hm1 (by omega)
  calc
    1 ≤ (m ^ j - m ^ 0) ^ 2 := by simp only [pow_zero]; nlinarith
    _ ≤ gaussian_schedule_separation_sum m j j := by
      unfold gaussian_schedule_separation_sum
      exact Finset.single_le_sum (fun r _ => sq_nonneg (m ^ j - m ^ r))
        (Finset.mem_range.mpr hj)

theorem gaussian_schedule_separation_term_scaled_le {m : ℝ} {k i j : ℕ}
    (hm : 2 ≤ m) (hki : k < i) (hij : i < j) :
    (m + 1) * (m ^ i - m ^ k) ^ 2 ≤ (m ^ j - m ^ k) ^ 2 := by
  have hm0 : 0 ≤ m := by linarith
  have hm1 : 1 ≤ m := by linarith
  have hdi : 0 ≤ m ^ i - m ^ k := sub_nonneg.mpr (pow_le_pow_right₀ hm1 hki.le)
  have hpow : m * m ^ i ≤ m ^ j := by
    simpa only [pow_succ, mul_comm] using pow_le_pow_right₀ hm1 (Nat.succ_le_of_lt hij)
  have hpk : 0 ≤ m ^ k := pow_nonneg hm0 _
  have hscale : m * (m ^ i - m ^ k) ≤ m ^ j - m ^ k := by nlinarith
  have hsquare : (m * (m ^ i - m ^ k)) ^ 2 ≤ (m ^ j - m ^ k) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hm0 hdi) hscale 2
  have hcoeff : m + 1 ≤ m ^ 2 := by nlinarith
  calc
    (m + 1) * (m ^ i - m ^ k) ^ 2 ≤ m ^ 2 * (m ^ i - m ^ k) ^ 2 :=
      mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
    _ = (m * (m ^ i - m ^ k)) ^ 2 := by ring
    _ ≤ (m ^ j - m ^ k) ^ 2 := hsquare

theorem gaussian_schedule_separation_sum_scaled_le {m : ℝ} {i j : ℕ}
    (hm : 2 ≤ m) (hij : i < j) :
    (m + 1) * gaussian_schedule_separation_sum m i i ≤
      gaussian_schedule_separation_sum m j j := by
  unfold gaussian_schedule_separation_sum
  rw [Finset.mul_sum]
  exact (Finset.sum_le_sum (fun k hk => gaussian_schedule_separation_term_scaled_le
    hm (Finset.mem_range.mp hk) hij)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij.le)
      (fun _ _ _ => sq_nonneg _))

theorem gaussian_schedule_separation_sum_diagonal_mono {m : ℝ} (hm : 2 ≤ m)
    {i j : ℕ} (hij : i ≤ j) :
    gaussian_schedule_separation_sum m i i ≤ gaussian_schedule_separation_sum m j j := by
  rcases hij.eq_or_lt with rfl | hij
  · rfl
  · have hn := gaussian_schedule_separation_sum_nonneg m i i
    have hs := gaussian_schedule_separation_sum_scaled_le hm hij
    nlinarith

theorem gaussian_schedule_sigma_dot {n : ℕ} (m : ℝ) (a : Vec n) {j : ℕ}
    (hj : j ≠ 0) :
    dot a (gaussian_schedule_sigma m j) =
      gaussian_schedule_separation_sum m j j * (m * dot a (canon_e j) + dot a 1) := by
  simp only [gaussian_schedule_sigma, if_neg hj, dot, mul_add, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.one_apply]
  ring

theorem gaussian_schedule_mu_distance {n : ℕ} (a : Vec n) (m : ℝ) (i j : ℕ) :
    dot a (sqVec (gaussian_schedule_mu m i - gaussian_schedule_mu m j)) =
      (m ^ i - m ^ j) ^ 2 * dot a 1 := by
  simp only [dot, sqVec, gaussian_schedule_mu, Pi.sub_apply, Pi.one_apply,
    mul_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem gaussian_schedule_sigma_dot_positive_all {n : ℕ} {m : ℝ} (a : Vec n)
    (hm : 2 ≤ m) (ha : is_vec_leq 0 a) (hsum : dot a 1 = m) (j : ℕ) :
    0 < dot a (gaussian_schedule_sigma m j) := by
  by_cases hj : j = 0
  · simp only [gaussian_schedule_sigma, if_pos hj, hsum]
    linarith
  · rw [gaussian_schedule_sigma_dot m a hj, hsum]
    have he := dot_canon_e_nonneg a j ha
    have hs := gaussian_schedule_separation_sum_ge_1 hm (Nat.pos_of_ne_zero hj)
    apply mul_pos (by linarith)
    nlinarith

theorem gaussian_schedule_later_covariance {n : ℕ} {m : ℝ} (a : Vec n)
    (hm : 2 ≤ m) (ha : is_vec_leq 0 a) (hsum : dot a 1 = m)
    {i j : ℕ} (hij : i < j) :
    dot a (gaussian_schedule_sigma m i) ≤ dot a (gaussian_schedule_sigma m j) := by
  have hj : j ≠ 0 := by omega
  have hm0 : 0 ≤ m := by linarith
  have hj0 := gaussian_schedule_separation_sum_nonneg m j j
  have hej := dot_canon_e_nonneg a j ha
  rw [gaussian_schedule_sigma_dot m a hj, hsum]
  by_cases hi : i = 0
  · simp only [gaussian_schedule_sigma, if_pos hi, hsum]
    have hs := gaussian_schedule_separation_sum_ge_1 hm (Nat.pos_of_ne_zero hj)
    calc
      m ≤ gaussian_schedule_separation_sum m j j * m := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) hj0
  · rw [gaussian_schedule_sigma_dot m a hi, hsum]
    have hi0 := gaussian_schedule_separation_sum_nonneg m i i
    have hei := dot_canon_e_le_dot_one a i ha
    rw [hsum] at hei
    have hscaled := gaussian_schedule_separation_sum_scaled_le hm hij
    calc
      _ ≤ gaussian_schedule_separation_sum m i i * (m * (m + 1)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hi0
      _ = m * ((m + 1) * gaussian_schedule_separation_sum m i i) := by ring
      _ ≤ m * gaussian_schedule_separation_sum m j j :=
        mul_le_mul_of_nonneg_left hscaled hm0
      _ ≤ gaussian_schedule_separation_sum m j j * (m * dot a (canon_e j) + m) := by
        rw [mul_comm m]
        exact mul_le_mul_of_nonneg_left (by nlinarith) hj0

theorem gaussian_schedule_separation_term_le_sum (m : ℝ) {i j : ℕ} (hij : i < j) :
    (m ^ i - m ^ j) ^ 2 ≤ gaussian_schedule_separation_sum m j j := by
  rw [sub_sq_comm]
  unfold gaussian_schedule_separation_sum
  exact Finset.single_le_sum (fun r _ => sq_nonneg (m ^ j - m ^ r))
    (Finset.mem_range.mpr hij)

theorem gaussian_schedule_pair_hinge_before {n : ℕ} {m c : ℝ} (a : Vec n)
    (hm : 2 ≤ m) (hc : 1 ≤ c) (ha : is_vec_leq 0 a) (hsum : dot a 1 = m)
    {i j : ℕ} (hij : i < j) :
    gaussian_pair_hinge c a (gaussian_schedule_class m i) (gaussian_schedule_class m j) =
      c - (m ^ i - m ^ j) ^ 2 * m / dot a (gaussian_schedule_sigma m j) := by
  have hord := gaussian_schedule_later_covariance a hm ha hsum hij
  have hpos := gaussian_schedule_sigma_dot_positive_all a hm ha hsum j
  have hterm := gaussian_schedule_separation_term_le_sum m hij
  have hej := dot_canon_e_nonneg a j ha
  have hj0 := gaussian_schedule_separation_sum_nonneg m j j
  have hm0 : 0 ≤ m := by linarith
  have hbound : (m ^ i - m ^ j) ^ 2 * m ≤ dot a (gaussian_schedule_sigma m j) := by
    rw [gaussian_schedule_sigma_dot m a (by omega), hsum]
    calc
      _ ≤ gaussian_schedule_separation_sum m j j * m :=
        mul_le_mul_of_nonneg_right hterm hm0
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) hj0
  have hratio : (m ^ i - m ^ j) ^ 2 * m / dot a (gaussian_schedule_sigma m j) ≤ 1 :=
    (div_le_one hpos).mpr hbound
  unfold gaussian_pair_hinge gaussian_pair_stats gaussian_schedule_class
  simp only [gaussian_schedule_mu_distance, hsum, max_eq_right hord]
  exact max_eq_right (by linarith)

theorem gaussian_schedule_snoc {n : ℕ} (m : ℝ) (k : ℕ) :
    gaussian_schedule (n := n) m (k + 1) =
      gaussian_schedule m k ++ [gaussian_schedule_class m k] := by
  simp [gaussian_schedule, List.range_succ]

theorem hinge_to_gaussian_schedule_last {n : ℕ} {m c : ℝ} (a : Vec n)
    (hm : 2 ≤ m) (hc : 1 ≤ c) (ha : is_vec_leq 0 a) (hsum : dot a 1 = m)
    {j : ℕ} (hj : 0 < j) :
    hinge_to c a (gaussian_schedule m j) (gaussian_schedule_class m j) =
      c * (j : ℝ) - (1 + dot a (canon_e j))⁻¹ := by
  have hspos : 0 < gaussian_schedule_separation_sum m j j :=
    lt_of_lt_of_le (by norm_num) (gaussian_schedule_separation_sum_ge_1 hm hj)
  have he := dot_canon_e_nonneg a j ha
  have hmne : m ≠ 0 := by linarith
  have hene : 1 + dot a (canon_e j) ≠ 0 := by linarith
  have hratio : gaussian_schedule_separation_sum m j j * m /
      dot a (gaussian_schedule_sigma m j) = (1 + dot a (canon_e j))⁻¹ := by
    rw [gaussian_schedule_sigma_dot m a (Nat.ne_of_gt hj), hsum]
    have hfactor : m * dot a (canon_e j) + m = m * (1 + dot a (canon_e j)) := by ring
    rw [hfactor]
    field_simp [hspos.ne', hmne, hene]
  have hsquares : (∑ i ∈ Finset.range j, (m ^ i - m ^ j) ^ 2) =
      gaussian_schedule_separation_sum m j j := by
    unfold gaussian_schedule_separation_sum
    apply Finset.sum_congr rfl
    intro i _
    exact sub_sq_comm _ _
  unfold hinge_to gaussian_schedule
  rw [List.map_map, ← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range, Function.comp_apply]
  calc
    _ = ∑ i ∈ Finset.range j,
        (c - (m ^ i - m ^ j) ^ 2 * m / dot a (gaussian_schedule_sigma m j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact gaussian_schedule_pair_hinge_before a hm hc ha hsum (Finset.mem_range.mp hi)
    _ = c * (j : ℝ) - gaussian_schedule_separation_sum m j j * m /
        dot a (gaussian_schedule_sigma m j) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← Finset.sum_div, ← Finset.sum_mul, hsquares]
      ring
    _ = _ := by rw [hratio]

/-- The total hinge loss of the schedule, expressed using its coordinate correction. -/
theorem gaussian_schedule_hinge_form_prefix_m_ge_2 {n : ℕ} (k : ℕ) {m c : ℝ}
    (a : Vec n) (hm : 2 ≤ m) (hc : 1 ≤ c) (ha : is_vec_leq 0 a)
    (hsum : dot a 1 = m) :
    hinge_form c a (gaussian_schedule m (k + 1)) =
      c * (k : ℝ) * ((k : ℝ) + 1) / 2 - gaussian_schedule_hinge_correction a k := by
  induction k with
  | zero => simp [gaussian_schedule, hinge_form, hinge_against,
      gaussian_schedule_hinge_correction]
  | succ k ih =>
    rw [gaussian_schedule_snoc, hinge_form_snoc, ih,
      hinge_to_gaussian_schedule_last a hm hc ha hsum (Nat.succ_pos k)]
    simp only [gaussian_schedule_hinge_correction, Finset.sum_range_succ,
      Nat.cast_succ, Nat.succ_eq_add_one]
    ring

end CSeparatedNPComplete
