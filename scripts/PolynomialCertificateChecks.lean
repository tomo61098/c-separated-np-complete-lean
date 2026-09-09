import Solution

open CSeparatedNPComplete
open CSeparatedNPComplete.PolynomialCertificate

-- The threshold is fixed, and its quarter-integer bound can be sharp.
example : partition_schedule_threshold 4 ![1, 4, 1, 4] = 47 := by
  norm_num [partition_schedule_threshold, dot, Fin.sum_univ_succ]

example : partition_schedule_threshold 5 (fun _ => 1) = 135 / 4 := by
  norm_num [partition_schedule_threshold, dot]

-- The schedule covers all four coordinates, including coordinate zero.
example : (partition_gadget_schedule 4 ![1, 4, 1, 4]).length = 8 := by
  rfl

example : gaussian_schedule_hinge_correction (![1, 1, 0, 0] : Vec 4) 4 = 3 := by
  rw [schedule_full_correction_eq_sum]
  norm_num [Fin.sum_univ_succ]

example : gaussian_schedule_hinge_correction (![0, 0, 1, 1] : Vec 4) 4 = 3 := by
  rw [schedule_full_correction_eq_sum]
  norm_num [Fin.sum_univ_succ]

-- A balanced fractional selector still fails the fixed Gaussian bound.
example : ¬ hinge_form 2 (fun _ : Fin 4 => 1 / 2)
    (partition_gadget_schedule 4 (fun _ => 1)) ≤
      partition_schedule_threshold 4 (fun _ => 1) := by
  intro h
  have hp := (partition_gadget_schedule_pointwise_iff 4 (fun _ => 1 / 2)
    (fun _ => 1) (by norm_num) (by norm_num [dot])
    (fun _ => ⟨1, by norm_num⟩)).mp
    ⟨⟨by intro i; norm_num, by intro i; norm_num⟩,
      by norm_num [dot], by norm_num [dot] at *; exact h⟩
  have hbinary := hp.1 0
  norm_num at hbinary

-- Equal counts and equal sums, with positive square weights.
example : verify ![1, 4, 1, 4] ![true, true, false, false] = true := by decide

-- Equal sums alone do not suffice: this choice has unequal cardinalities.
example : verify ![1, 1, 1, 3] ![true, true, true, false] = false := by decide

-- Equal cardinalities alone do not suffice either.
example : verify ![1, 4, 1, 4] ![true, false, true, false] = false := by decide

-- The charged work grows with binary operand length, even at fixed dimension.
example : verificationWork ![2 ^ 32, 2 ^ 32] ![true, false] >
    verificationWork ![1, 1] ![true, false] := by decide

-- End-to-end use of the certificate theorem for the original Gaussian predicate.
example : ∃ a : Vec 4, box_constraints a ∧ dot a 1 = 2 ∧
    hinge_form 5 a (partition_gadget_schedule 4 ![1, 4, 1, 4]) ≤
      partition_schedule_threshold 4 ![1, 4, 1, 4] := by
  let w : Fin 4 → ℕ := ![1, 4, 1, 4]
  have hw : (fun i => (w i : ℝ)) = (![1, 4, 1, 4] : Vec 4) := by
    funext i
    fin_cases i <;> norm_num [w]
  have hcval : dot (fun i => (w i : ℝ)) 1 / 2 = 5 := by
    norm_num [w, dot, Fin.sum_univ_succ]
  have hc : 1 ≤ dot (fun i => (w i : ℝ)) 1 / 2 := by rw [hcval]; norm_num
  have hs : perf_square_vec (fun i => (w i : ℝ)) := by
    rw [hw]
    intro i
    fin_cases i
    · exact ⟨1, by norm_num⟩
    · exact ⟨2, by norm_num⟩
    · exact ⟨1, by norm_num⟩
    · exact ⟨2, by norm_num⟩
  have h := (gadget_polynomial_certificate 4 w (by norm_num) hc hs).mpr
    ⟨![true, true, false, false], by decide,
      by rw [certificate_length]; exact dimension_le_inputBits _, verificationWork_le _ _⟩
  rw [hcval] at h
  simpa only [hw, Nat.cast_ofNat, show (4 : ℝ) / 2 = 2 by norm_num] using h

run_cmd do
  for name in #[
      `CSeparatedNPComplete.PolynomialCertificate.gadget_polynomial_certificate,
      `CSeparatedNPComplete.PolynomialCertificate.verify_iff_partition,
      `CSeparatedNPComplete.PolynomialCertificate.verificationWork_le,
      `CSeparatedNPComplete.PolynomialCertificate.encodeInput_length,
      `CSeparatedNPComplete.PolynomialCertificate.certificate_length,
      `CSeparatedNPComplete.partition_schedule_threshold_quarter_integral] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Forbidden axiom in {name}: {axiomName}"
    Lean.logInfo m!"{name}: {axioms}"
