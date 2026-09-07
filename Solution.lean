import CSeparatedNPComplete

/-!
# The partition gadget and Gaussian schedule equivalence

The unpublished manuscript `c_separation_NP_completness-4.pdf` motivates Gaussian
separation by selecting marker genes that distinguish cell types while accounting
for within-type variation. The construction below studies continuous feature
weights in the unit cube under a fixed cardinality constraint. Its three-class
gadget enforces the partition balance; the schedule's reciprocal correction is
tight only at binary selectors.

The main theorem proves the exact pointwise equivalence in `RocqOld/sepsolve.v:2782`. The
threshold depends on the selector's coordinate zero. A fixed-threshold complexity
reduction and its encoding bounds are not asserted by this theorem.
The only auxiliary theorem stated here is the general Karamata inequality.
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
        partition_schedule_threshold d a s) ↔ is_ec_partition a s := by
  have hm : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 2 ≤ d by omega)
  have hs_nonneg := perf_square_non_neg hs
  have hn : 0 < 2 * d := by omega
  have hlen : 2 * d - 1 + 1 = 2 * d := by omega
  let c := dot s 1 / 2
  let C := c * ((2 * d - 1 : Nat) : ℝ) * (((2 * d - 1 : Nat) : ℝ) + 1) / 2
  let G := hinge_form c a (second_gadget_instance (d : ℝ) c s)
  let Corr := gaussian_schedule_hinge_correction a (2 * d - 1)
  have hdecomp (ha : box_constraints a) (hcard : dot a 1 = (d : ℝ)) :
      hinge_form c a (partition_gadget_schedule d s) = G + (C - Corr) := by
    unfold partition_gadget_schedule second_gadget_partition_instance
    rw [second_gadget_schedule_hinge_form_app (d : ℝ) c a s hm hc ha hs_nonneg hcard
      (by dsimp [c]; ring)]
    have hschedule := gaussian_schedule_hinge_form_prefix_m_ge_2 (2 * d - 1)
      a hm hc ha.1 hcard
    rw [hlen] at hschedule
    rw [hschedule]
  have hfull := schedule_full_correction_eq_sum a hn
  have hG_nonneg : 0 ≤ G := hinge_form_nonneg c a _
  constructor
  · rintro ⟨ha, hcard, hhinge⟩
    have hbound := full_correction_le_line a ha
    rw [hcard] at hbound
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hbound
    rw [hdecomp ha hcard] at hhinge
    change G + (C - Corr) ≤ C - (3 * (d : ℝ) / 2 - (1 + dot a (canon_e 0))⁻¹)
      at hhinge
    have hzero : G = 0 := by dsimp [Corr] at hhinge; linarith
    have heq : (∑ i, (1 + a i)⁻¹) = ((2 * d : Nat) : ℝ) - dot a 1 / 2 := by
      rw [hcard]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      dsimp [Corr] at hhinge
      linarith
    have hbin := (full_correction_eq_binary_iff a ha).mp heq
    refine ⟨hbin, ?_, ?_⟩
    · rw [hcard]
      push_cast
      ring
    · exact (second_gadget_hinge_form_iff (d : ℝ) c a s (by linarith) hc
        ha.1 hs_nonneg hcard).mp hzero
  · rintro ⟨hbin, hcard_half, hsum⟩
    have ha := is_binary_box_constraints hbin
    have hcard : dot a 1 = (d : ℝ) := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hcard_half
      linarith
    have heq := (full_correction_eq_binary_iff a ha).mpr hbin
    rw [hcard] at heq
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at heq
    have hzero : G = 0 := (second_gadget_hinge_form_iff (d : ℝ) c a s
      (by linarith) hc ha.1 hs_nonneg hcard).mpr hsum
    refine ⟨ha, hcard, ?_⟩
    rw [hdecomp ha hcard]
    change G + (C - Corr) ≤ C - (3 * (d : ℝ) / 2 - (1 + dot a (canon_e 0))⁻¹)
    dsimp [Corr]
    linarith

end CSeparatedNPComplete
