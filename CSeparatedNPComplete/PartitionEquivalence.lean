import CSeparatedNPComplete.CrossGadget
import CSeparatedNPComplete.Gadget
import CSeparatedNPComplete.Reciprocal

namespace CSeparatedNPComplete

/-- The fixed Gaussian threshold is attained exactly by equal-cardinality
partition selectors. Here `d` is the full feature dimension. -/
theorem partition_gadget_schedule_pointwise_iff
    (d : Nat) (a s : Vec d)
    (hd : 4 ≤ d) (hc : 1 ≤ dot s 1 / 2) (hs : perf_square_vec s) :
    (box_constraints a ∧ dot a 1 = (d : ℝ) / 2 ∧
      hinge_form (dot s 1 / 2) a (partition_gadget_schedule d s) ≤
        partition_schedule_threshold d s) ↔ is_ec_partition a s := by
  have hdreal : (4 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hm : (2 : ℝ) ≤ (d : ℝ) / 2 := by linarith
  have hs_nonneg := perf_square_non_neg hs
  have hn : 0 < d := by omega
  let c := dot s 1 / 2
  let C := c * (d : ℝ) * ((d : ℝ) + 1) / 2
  let G := hinge_form c a (second_gadget_instance ((d : ℝ) / 2) c s)
  let Corr := gaussian_schedule_hinge_correction a d
  have hdecomp (ha : box_constraints a) (hcard : dot a 1 = (d : ℝ) / 2) :
      hinge_form c a (partition_gadget_schedule d s) = G + (C - Corr) := by
    unfold partition_gadget_schedule second_gadget_partition_instance
    rw [second_gadget_schedule_hinge_form_app ((d : ℝ) / 2) c a s hm hc ha
      hs_nonneg hcard (by dsimp [c]; ring) hn]
    rw [gaussian_schedule_hinge_form_prefix_m_ge_2 d a hm hc ha.1 hcard]
  have hfull := schedule_full_correction_eq_sum a
  have hG_nonneg : 0 ≤ G := hinge_form_nonneg c a _
  constructor
  · rintro ⟨ha, hcard, hhinge⟩
    have hbound := full_correction_le_line a ha
    rw [hcard] at hbound
    rw [hdecomp ha hcard] at hhinge
    change G + (C - Corr) ≤ C - 3 * (d : ℝ) / 4 at hhinge
    have hzero : G = 0 := by dsimp [Corr] at hhinge; linarith
    have heq : (∑ i, (1 + a i)⁻¹) = (d : ℝ) - dot a 1 / 2 := by
      rw [hcard]
      dsimp [Corr] at hhinge
      linarith
    refine ⟨(full_correction_eq_binary_iff a ha).mp heq, hcard, ?_⟩
    exact (second_gadget_hinge_form_iff ((d : ℝ) / 2) c a s (by linarith) hc
      ha.1 hs_nonneg hcard).mp hzero
  · rintro ⟨hbin, hcard, hsum⟩
    have ha := is_binary_box_constraints hbin
    have heq := (full_correction_eq_binary_iff a ha).mpr hbin
    rw [hcard] at heq
    have hzero : G = 0 := (second_gadget_hinge_form_iff ((d : ℝ) / 2) c a s
      (by linarith) hc ha.1 hs_nonneg hcard).mpr hsum
    refine ⟨ha, hcard, ?_⟩
    rw [hdecomp ha hcard]
    change G + (C - Corr) ≤ C - 3 * (d : ℝ) / 4
    dsimp [Corr]
    linarith

/-- For natural input weights, the fixed threshold is an integer multiple of `1/4`. -/
theorem partition_schedule_threshold_quarter_integral (d : Nat) (s : Fin d → Nat) :
    ∃ z : ℤ, partition_schedule_threshold d (fun i => (s i : ℝ)) = (z : ℝ) / 4 := by
  refine ⟨(∑ i, (s i : ℤ)) * (d : ℤ) * ((d : ℤ) + 1) - 3 * (d : ℤ), ?_⟩
  simp only [partition_schedule_threshold, dot, Pi.one_apply, mul_one]
  push_cast
  ring

end CSeparatedNPComplete
