import Solution

open CSeparatedNPComplete
open CSeparatedNPComplete.PolynomialCertificate

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
    hinge_form 5 a (partition_gadget_schedule 2 ![1, 4, 1, 4]) ≤
      partition_schedule_threshold 2 a ![1, 4, 1, 4] := by
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
  have h := (gadget_polynomial_certificate 2 w (by norm_num) hc hs).mpr
    ⟨![true, true, false, false], by decide,
      by rw [certificate_length]; exact dimension_le_inputBits _, verificationWork_le _ _⟩
  rw [hcval] at h
  simpa only [hw, Nat.cast_ofNat] using h

run_cmd do
  for name in #[
      `CSeparatedNPComplete.PolynomialCertificate.gadget_polynomial_certificate,
      `CSeparatedNPComplete.PolynomialCertificate.verify_iff_partition,
      `CSeparatedNPComplete.PolynomialCertificate.verificationWork_le,
      `CSeparatedNPComplete.PolynomialCertificate.encodeInput_length,
      `CSeparatedNPComplete.PolynomialCertificate.certificate_length] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Forbidden axiom in {name}: {axiomName}"
    Lean.logInfo m!"{name}: {axioms}"
