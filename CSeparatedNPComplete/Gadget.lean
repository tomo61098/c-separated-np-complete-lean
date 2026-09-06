import CSeparatedNPComplete.PartitionDefs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace CSeparatedNPComplete

theorem second_gadget_sigma1_dot {n : ℕ} (m : ℝ) (a : Vec n) :
    dot a (second_gadget_sigma1 m) =
      second_gadget_gamma n m * second_gadget_gamma n m * dot a 1 := by
  simp only [dot, second_gadget_sigma1, Pi.one_apply, mul_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem second_gadget_sigma2_dot {n : ℕ} (m : ℝ) (a : Vec n) :
    dot a (second_gadget_sigma2 m) =
      second_gadget_gamma n m * second_gadget_gamma n m * m * dot a 1 := by
  simp only [dot, second_gadget_sigma2, Pi.one_apply, mul_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem second_gadget_sigma3_dot {n : ℕ} (m : ℝ) (a s : Vec n) :
    dot a (second_gadget_sigma3 m s) =
      second_gadget_gamma n m * second_gadget_gamma n m * m * dot a s := by
  simp only [dot, second_gadget_sigma3]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem second_gadget_12_distance {n : ℕ} (m c : ℝ) (a s : Vec n) :
    dot a (sqVec (second_gadget_mu1 m c - second_gadget_mu2 m c s)) =
      second_gadget_gamma n m * second_gadget_gamma n m *
        m * m * dot a (sqVec (fun i => Real.sqrt (s i))) := by
  simp only [dot, sqVec, second_gadget_mu1, second_gadget_mu2, Pi.sub_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem second_gadget_13_distance {n : ℕ} (m c : ℝ) (a : Vec n) :
    dot a (sqVec (second_gadget_mu1 m c - second_gadget_mu3 m c)) =
      second_gadget_gamma n m * second_gadget_gamma n m * c * c * dot a 1 := by
  simp only [dot, sqVec, second_gadget_mu1, second_gadget_mu3, Pi.sub_apply,
    Pi.one_apply, mul_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem second_gadget_23_distance {n : ℕ} (m c : ℝ) (a s : Vec n) :
    dot a (sqVec (second_gadget_mu2 m c s - second_gadget_mu3 m c)) =
      second_gadget_gamma n m * second_gadget_gamma n m *
        dot a (sqVec (fun i => c + m * Real.sqrt (s i))) := by
  simp only [dot, sqVec, second_gadget_mu2, second_gadget_mu3, Pi.sub_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem scalar_hinge_zero_iff (c D S : ℝ) (hS : 0 < S) :
    max 0 (c - D / S) = 0 ↔ c * S ≤ D := by
  rw [max_eq_left_iff, sub_nonpos, le_div_iff₀ hS]

private theorem gadget_scalar_iff (G m c x D : ℝ)
    (hG : 0 < G) (hm : 1 ≤ m) (hc : 1 ≤ c)
    (hD1 : G * m * m * x ≤ D) (hD2 : G * c * c * m ≤ D) :
    (max 0 (c - (G * m * m * x) / max (G * m) (G * m * m)) +
        max 0 (c - (G * c * c * m) / max (G * m) (G * m * x))) +
      max 0 (c - D / max (G * m * m) (G * m * x)) = 0 ↔ x = c := by
  have hm0 : 0 < m := by linarith
  have hc0 : 0 < c := by linarith
  have hGm : 0 < G * m := mul_pos hG hm0
  have hGmm : 0 < G * m * m := mul_pos hGm hm0
  have hS12 : 0 < max (G * m) (G * m * m) := lt_of_lt_of_le hGm (le_max_left _ _)
  have hS13 : 0 < max (G * m) (G * m * x) := lt_of_lt_of_le hGm (le_max_left _ _)
  have hS23 : 0 < max (G * m * m) (G * m * x) := lt_of_lt_of_le hGmm (le_max_left _ _)
  constructor
  · intro h
    have h12 : max 0 (c - (G * m * m * x) / max (G * m) (G * m * m)) = 0 := by
      have := le_max_left 0 (c - (G * c * c * m) / max (G * m) (G * m * x))
      have := le_max_left 0 (c - D / max (G * m * m) (G * m * x))
      have := le_max_left 0 (c - (G * m * m * x) / max (G * m) (G * m * m))
      linarith
    have h13 : max 0 (c - (G * c * c * m) / max (G * m) (G * m * x)) = 0 := by
      have := le_max_left 0 (c - (G * c * c * m) / max (G * m) (G * m * x))
      have := le_max_left 0 (c - D / max (G * m * m) (G * m * x))
      linarith
    have hlo : c ≤ x := by
      have hh := (scalar_hinge_zero_iff _ _ _ hS12).mp h12
      have hle := mul_le_mul_of_nonneg_left (le_max_right (G * m) (G * m * m)) hc0.le
      have hh' : (G * m * m) * c ≤ (G * m * m) * x := by nlinarith
      exact (mul_le_mul_iff_right₀ hGmm).mp hh'
    have hup : x ≤ c := by
      have hh := (scalar_hinge_zero_iff _ _ _ hS13).mp h13
      have hle := mul_le_mul_of_nonneg_left (le_max_right (G * m) (G * m * x)) hc0.le
      have hh' : (c * (G * m)) * x ≤ (c * (G * m)) * c := by nlinarith
      exact (mul_le_mul_iff_right₀ (mul_pos hc0 hGm)).mp hh'
    exact le_antisymm hup hlo
  · intro hxc
    subst x
    have h12 : max 0 (c - (G * m * m * c) / max (G * m) (G * m * m)) = 0 := by
      apply (scalar_hinge_zero_iff _ _ _ hS12).mpr
      rw [mul_max_of_nonneg _ _ hc0.le]
      apply max_le
      · have : G * m ≤ G * m * m := le_mul_of_one_le_right hGm.le hm
        nlinarith
      · nlinarith
    have h13 : max 0 (c - (G * c * c * m) / max (G * m) (G * m * c)) = 0 := by
      apply (scalar_hinge_zero_iff _ _ _ hS13).mpr
      rw [mul_max_of_nonneg _ _ hc0.le]
      apply max_le
      · have : c * (G * m) ≤ c * (G * m) * c :=
          le_mul_of_one_le_right (mul_pos hc0 hGm).le hc
        nlinarith
      · nlinarith
    have h23 : max 0 (c - D / max (G * m * m) (G * m * c)) = 0 := by
      apply (scalar_hinge_zero_iff _ _ _ hS23).mpr
      rw [mul_max_of_nonneg _ _ hc0.le]
      apply max_le <;> nlinarith
    rw [h12, h13, h23]
    norm_num

/- The third pair is separated whenever the first two encode the desired
partition equality. The bounds below use only nonnegativity of coordinates. -/
private theorem gadget_distance_lower_bounds {n : ℕ} (m c : ℝ) (a s : Vec n)
    (hm : 0 ≤ m) (hc : 0 ≤ c) (ha : ∀ i, 0 ≤ a i) (hs : ∀ i, 0 ≤ s i) :
    m * m * dot a s ≤ dot a (sqVec (fun i => c + m * Real.sqrt (s i))) ∧
      c * c * dot a 1 ≤ dot a (sqVec (fun i => c + m * Real.sqrt (s i))) := by
  constructor
  · simp only [dot, sqVec]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hroot := Real.mul_self_sqrt (hs i)
    have hprod := mul_nonneg hc (mul_nonneg hm (Real.sqrt_nonneg (s i)))
    have hsq : m * m * s i ≤ (c + m * Real.sqrt (s i)) * (c + m * Real.sqrt (s i)) := by
      calc
        m * m * s i = m * m * (Real.sqrt (s i) * Real.sqrt (s i)) := by rw [hroot]
        _ = (m * Real.sqrt (s i)) * (m * Real.sqrt (s i)) := by ring
        _ ≤ _ := by nlinarith [sq_nonneg c]
    calc
      m * m * (a i * s i) = a i * (m * m * s i) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq (ha i)
  · simp only [dot, sqVec, Pi.one_apply, mul_one]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hprod := mul_nonneg hc (mul_nonneg hm (Real.sqrt_nonneg (s i)))
    have hsq : c * c ≤ (c + m * Real.sqrt (s i)) * (c + m * Real.sqrt (s i)) := by
      nlinarith [sq_nonneg (m * Real.sqrt (s i))]
    calc
      c * c * a i = a i * (c * c) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq (ha i)

/-- The three-Gaussian gadget enforces the partition equality. This version
only assumes nonnegative coordinates; the binary perfect-square case follows
by specialization. -/
theorem second_gadget_hinge_form_iff {n : ℕ} (m c : ℝ) (a s : Vec n)
    (hm : 1 ≤ m) (hc : 1 ≤ c) (ha : ∀ i, 0 ≤ a i) (hs : ∀ i, 0 ≤ s i)
    (hcard : dot a 1 = m) :
    hinge_form c a (second_gadget_instance m c s) = 0 ↔ dot a s = c := by
  have hg : 0 < second_gadget_gamma n m := by
    have hsep : 0 ≤ gaussian_schedule_separation_sum m n n :=
      Finset.sum_nonneg (fun i hi => sq_nonneg (m ^ n - m ^ i))
    unfold second_gadget_gamma
    linarith
  let G := second_gadget_gamma n m * second_gadget_gamma n m
  have hG : 0 < G := mul_pos hg hg
  obtain ⟨hterm1, hterm2⟩ := gadget_distance_lower_bounds m c a s (by linarith)
    (by linarith) ha hs
  have hD1 : G * m * m * dot a s ≤ G * dot a (sqVec (fun i => c + m * Real.sqrt (s i))) := by
    calc
      G * m * m * dot a s = G * (m * m * dot a s) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hterm1 hG.le
  have hD2 : G * c * c * m ≤ G * dot a (sqVec (fun i => c + m * Real.sqrt (s i))) := by
    rw [hcard] at hterm2
    calc
      G * c * c * m = G * (c * c * m) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hterm2 hG.le
  have hsqrt : sqVec (fun i => Real.sqrt (s i)) = s := by
    funext i
    exact Real.mul_self_sqrt (hs i)
  have h := gadget_scalar_iff G m c (dot a s)
    (G * dot a (sqVec (fun i => c + m * Real.sqrt (s i)))) hG hm hc hD1 hD2
  simpa only [second_gadget_instance, hinge_form, hinge_against, gaussian_pair_hinge,
    gaussian_pair_stats, second_gadget_g1, second_gadget_g2, second_gadget_g3,
    second_gadget_sigma1_dot, second_gadget_sigma2_dot, second_gadget_sigma3_dot,
    second_gadget_12_distance, second_gadget_13_distance, second_gadget_23_distance,
    hsqrt, hcard, hinge, add_zero, G] using h

end CSeparatedNPComplete
