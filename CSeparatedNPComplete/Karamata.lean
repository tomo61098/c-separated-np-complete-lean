import CSeparatedNPComplete.ConvexPredicate
import CSeparatedNPComplete.ConvexSlopes
import CSeparatedNPComplete.WeightedSum

/-!
# Karamata's inequality

The proof follows the secant-slope and summation-by-parts argument in `Karamata.v`.
Mathlib supplies convex secant monotonicity, extension of an antitone function,
and Abel summation. Extending the slopes across equal coordinate pairs avoids
the source's deletion and reversal of vectors.
-/

namespace CSeparatedNPComplete

/-- Karamata's inequality with mathlib's native convexity hypothesis.
In the source convention, `majorized u v` means that `u` majorizes `v`. -/
theorem majorized.sum_convex_le {n : Nat} {u v : Vec n}
    (hmajorized : majorized u v) {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ s f) (hu_mem : ∀ i, u i ∈ s) (hv_mem : ∀ i, v i ∈ s) :
    vecSum (fun i => f (v i)) ≤ vecSum (fun i => f (u i)) := by
  rcases hmajorized with ⟨hu, hv, hprefix, htotal⟩
  obtain ⟨c, hc, hfactor⟩ := exists_antitone_secant_coefficients hf u v
    (fun _ _ hij => hu _ _ hij) (fun _ _ hij => hv _ _ hij) hu_mem hv_mem
  have hsum := sum_mul_nonneg_of_antitone_of_prefix_nonneg
    (fun i => u i - v i) c hc
    (fun k => by
      rw [Finset.sum_sub_distrib]
      exact sub_nonneg.mpr (hprefix k))
    (by
      rw [Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr htotal)
  simp_rw [← hfactor, Finset.sum_sub_distrib] at hsum
  exact sub_nonneg.mp hsum

end CSeparatedNPComplete
