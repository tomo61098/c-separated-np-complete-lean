import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

namespace CSeparatedNPComplete

open scoped BigOperators

/-- Abel's summation inequality for a sequence with nonnegative partial sums
and zero total sum. -/
theorem sum_mul_nonneg_of_antitone_of_partial_sum_nonneg
    (n : ℕ) (a c : ℕ → ℝ)
    (hc : ∀ i, i + 1 < n → c (i + 1) ≤ c i)
    (ha : ∀ k, k ≤ n → 0 ≤ ∑ i ∈ Finset.range k, a i)
    (ht : ∑ i ∈ Finset.range n, a i = 0) :
    0 ≤ ∑ i ∈ Finset.range n, c i * a i := by
  have hab := Finset.sum_range_by_parts c a n
  simp only [smul_eq_mul, ht, mul_zero, zero_sub] at hab
  rw [hab]
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro i hi
  have hi' : i < n - 1 := Finset.mem_range.mp hi
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hc i (by omega)))
    (ha (i + 1) (by omega))

private def extendFin {n : ℕ} (a : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : i < n then a ⟨i, h⟩ else 0

private theorem sum_extendFin {n : ℕ} (a : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    (∑ i ∈ Finset.range k, extendFin a i) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i := by
  apply Finset.sum_bij (fun i hi => (⟨i, lt_of_lt_of_le (Finset.mem_range.mp hi) hk⟩ : Fin n))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.mem_range.mp hi
  · intro i hi j hj hij
    exact congrArg Fin.val hij
  · intro i hi
    exact ⟨i.val, Finset.mem_range.mpr (Finset.mem_filter.mp hi).2, rfl⟩
  · intro i hi
    simp [extendFin, lt_of_lt_of_le (Finset.mem_range.mp hi) hk]

/-- Decreasing weights pair nonnegatively with a finite vector whose partial
sums are nonnegative and whose total sum vanishes. -/
theorem sum_mul_nonneg_of_antitone_of_prefix_nonneg {n : ℕ}
    (a c : Fin n → ℝ) (hc : Antitone c)
    (ha : ∀ k : ℕ, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i)
    (ht : ∑ i, a i = 0) :
    0 ≤ ∑ i, c i * a i := by
  have hfilter : Finset.univ.filter (fun i : Fin n => i.val < n) = Finset.univ := by
    ext i
    simp
  have h := sum_mul_nonneg_of_antitone_of_partial_sum_nonneg n (extendFin a) (extendFin c)
    (fun i hi => by
      simp only [extendFin, dif_pos hi, dif_pos (show i < n by omega)]
      exact hc (by simp))
    (fun k hk => by rw [sum_extendFin a k hk]; exact ha k)
    (by rw [sum_extendFin a n le_rfl, hfilter]; exact ht)
  have heq : (∑ i ∈ Finset.range n, extendFin c i * extendFin a i) = ∑ i, c i * a i := by
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [extendFin]
  rwa [heq] at h

end CSeparatedNPComplete
