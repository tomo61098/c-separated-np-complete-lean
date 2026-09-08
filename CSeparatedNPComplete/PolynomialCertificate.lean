import CSeparatedNPComplete.PartitionEquivalence
import Mathlib.Data.Nat.Size

/-!
# Polynomial certificates for the constructed Gaussian instances

A certificate is one Boolean per coordinate. The checker adds the counts and
integer weights on its two sides and compares them. The gadget iff proves that
this arithmetic checker accepts exactly the feasible constructed instances.

The cost model charges `8 * (size x + size y + 1)` for binary addition or
comparison, rather than unit cost for unbounded integers. This is a linear
bit-work allowance for ripple-carry addition and padded binary comparison.
The recursive checker accumulates these charges on its actual intermediate
operands. We prove a quadratic bound in the delimited binary input length.
This is a bit-cost proof, not a compilation theorem for a Turing machine.
-/

namespace CSeparatedNPComplete.PolynomialCertificate

def binaryCost (x y : ℕ) : ℕ := 8 * (Nat.size x + Nat.size y + 1)

structure Totals where
  leftCount : ℕ
  rightCount : ℕ
  leftSum : ℕ
  rightSum : ℕ
  work : ℕ
  deriving DecidableEq, Repr

/-- Four binary accumulators, with costs charged at every addition. -/
def run : List (ℕ × Bool) → Totals
  | [] => ⟨0, 0, 0, 0, 0⟩
  | (w, b) :: xs =>
    let r := run xs
    if b then
      ⟨r.leftCount + 1, r.rightCount, r.leftSum + w, r.rightSum,
        r.work + binaryCost r.leftCount 1 + binaryCost r.leftSum w + 1⟩
    else
      ⟨r.leftCount, r.rightCount + 1, r.leftSum, r.rightSum + w,
        r.work + binaryCost r.rightCount 1 + binaryCost r.rightSum w + 1⟩

def bitMass (r : Totals) : ℕ :=
  Nat.size r.leftCount + Nat.size r.rightCount + Nat.size r.leftSum + Nat.size r.rightSum

def budget (xs : List (ℕ × Bool)) : ℕ :=
  (xs.map fun p => Nat.size p.1 + 3).sum

theorem size_add_le (x y : ℕ) : Nat.size (x + y) ≤ Nat.size x + Nat.size y + 1 := by
  apply Nat.size_le.mpr
  have hx := Nat.lt_size_self x
  have hy := Nat.lt_size_self y
  have hxp : 2 ^ Nat.size x ≤ 2 ^ (Nat.size x + Nat.size y) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hyp : 2 ^ Nat.size y ≤ 2 ^ (Nat.size x + Nat.size y) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  rw [pow_succ]
  omega

theorem run_mass_le (xs : List (ℕ × Bool)) : bitMass (run xs) ≤ budget xs := by
  induction xs with
  | nil => simp [run, bitMass, budget]
  | cons p xs ih =>
    obtain ⟨w, b⟩ := p
    have hlc := size_add_le (run xs).leftCount 1
    have hrc := size_add_le (run xs).rightCount 1
    have hls := size_add_le (run xs).leftSum w
    have hrs := size_add_le (run xs).rightSum w
    simp only [Nat.size_one] at hlc hrc
    cases b <;> simp only [run, Bool.false_eq_true, ↓reduceIte, bitMass,
      budget, List.map_cons, List.sum_cons] at * <;> omega

theorem run_work_le (xs : List (ℕ × Bool)) :
    (run xs).work ≤ 16 * xs.length * (budget xs + 1) := by
  induction xs with
  | nil => simp [run]
  | cons p xs ih =>
    obtain ⟨w, b⟩ := p
    have hm := run_mass_le xs
    cases b <;>
      simp only [run, Bool.false_eq_true, ↓reduceIte, binaryCost, Nat.size_one,
        List.length_cons, budget, List.map_cons, List.sum_cons, bitMass] at * <;> nlinarith

def leftCount (xs : List (ℕ × Bool)) : ℕ := (xs.map fun p => if p.2 then 1 else 0).sum
def rightCount (xs : List (ℕ × Bool)) : ℕ := (xs.map fun p => if p.2 then 0 else 1).sum
def leftSum (xs : List (ℕ × Bool)) : ℕ := (xs.map fun p => if p.2 then p.1 else 0).sum
def rightSum (xs : List (ℕ × Bool)) : ℕ := (xs.map fun p => if p.2 then 0 else p.1).sum

theorem run_correct (xs : List (ℕ × Bool)) :
    (run xs).leftCount = leftCount xs ∧ (run xs).rightCount = rightCount xs ∧
    (run xs).leftSum = leftSum xs ∧ (run xs).rightSum = rightSum xs := by
  induction xs with
  | nil => simp [run, leftCount, rightCount, leftSum, rightSum]
  | cons p xs ih =>
    obtain ⟨w, b⟩ := p
    cases b <;> simp [run, leftCount, rightCount, leftSum, rightSum,
      leftCount, rightCount, leftSum, rightSum] at * <;> omega

def tagged {n : ℕ} (s : Fin n → ℕ) (b : Fin n → Bool) : List (ℕ × Bool) :=
  List.ofFn fun i => (s i, b i)

/-- Two-bit symbols: a data bit `b` is `0b`, and `11` ends a weight. -/
def encodeWeight (w : ℕ) : List Bool :=
  (w.bits.flatMap fun b => [false, b]) ++ [true, true]

def encodeInput {n : ℕ} (s : Fin n → ℕ) : List Bool :=
  (List.ofFn s).flatMap encodeWeight

/-- The actual bit length of the delimited binary encoding. -/
def inputBits {n : ℕ} (s : Fin n → ℕ) : ℕ := 2 * ∑ i, (Nat.size (s i) + 1)

def certificate {n : ℕ} (b : Fin n → Bool) : List Bool := List.ofFn b

def verify {n : ℕ} (s : Fin n → ℕ) (b : Fin n → Bool) : Bool :=
  let r := run (tagged s b)
  (r.leftCount == r.rightCount) && (r.leftSum == r.rightSum)

/-- Include the two final binary comparisons and the conjunction. -/
def verificationWork {n : ℕ} (s : Fin n → ℕ) (b : Fin n → Bool) : ℕ :=
  let r := run (tagged s b)
  inputBits s + n + r.work + binaryCost r.leftCount r.rightCount + binaryCost r.leftSum r.rightSum + 1

theorem certificate_length {n : ℕ} (b : Fin n → Bool) : (certificate b).length = n := by
  simp [certificate]

theorem dimension_le_inputBits {n : ℕ} (s : Fin n → ℕ) : n ≤ inputBits s := by
  have h : n ≤ ∑ i, (Nat.size (s i) + 1) := by
    calc
      n = ∑ _i : Fin n, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => by omega
  unfold inputBits
  omega

theorem budget_le_inputBits {n : ℕ} (s : Fin n → ℕ) (b : Fin n → Bool) :
    budget (tagged s b) ≤ 3 * inputBits s := by
  simp only [budget, tagged, List.map_ofFn, List.sum_ofFn, inputBits,
    ← mul_assoc, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  dsimp
  omega

theorem verificationWork_le {n : ℕ} (s : Fin n → ℕ) (b : Fin n → Bool) :
    verificationWork s b ≤ 128 * (inputBits s + 1) ^ 2 := by
  have hr := run_work_le (tagged s b)
  have hm := run_mass_le (tagged s b)
  have hb := budget_le_inputBits s b
  have hn := dimension_le_inputBits s
  have hl : (tagged s b).length = n := by simp [tagged]
  rw [hl] at hr
  unfold verificationWork binaryCost
  dsimp [bitMass] at hm
  have hprod : n * (budget (tagged s b) + 1) ≤ inputBits s * (3 * inputBits s + 1) :=
    Nat.mul_le_mul hn (by omega)
  nlinarith

theorem encodeInput_length {n : ℕ} (s : Fin n → ℕ) :
    (encodeInput s).length = inputBits s := by
  simp [encodeInput, encodeWeight, List.length_flatMap, List.map_ofFn,
    List.sum_ofFn, Nat.size_eq_bits_len, inputBits, Finset.mul_sum, mul_add]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem counts_total (xs : List (ℕ × Bool)) : leftCount xs + rightCount xs = xs.length := by
  induction xs with
  | nil => simp [leftCount, rightCount]
  | cons p xs ih =>
    obtain ⟨w, b⟩ := p
    cases b <;> simp [leftCount, rightCount] at * <;> omega

theorem sums_total (xs : List (ℕ × Bool)) : leftSum xs + rightSum xs = (xs.map Prod.fst).sum := by
  induction xs with
  | nil => simp [leftSum, rightSum]
  | cons p xs ih =>
    obtain ⟨w, b⟩ := p
    cases b <;> simp [leftSum, rightSum] at * <;> omega

def selector {n : ℕ} (b : Fin n → Bool) : Vec n := fun i => if b i then 1 else 0

theorem selector_binary {n : ℕ} (b : Fin n → Bool) : is_binary (selector b) := by
  intro i
  cases h : b i <;> simp [selector, h]

theorem selector_count {n : ℕ} (s : Fin n → ℕ) (b : Fin n → Bool) :
    dot (selector b) 1 = (leftCount (tagged s b) : ℝ) := by
  simp only [dot, selector, Pi.one_apply, mul_one, leftCount, tagged,
    List.map_ofFn, List.sum_ofFn, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases h : b i <;> simp [h]

theorem selector_sum {n : ℕ} (s : Fin n → ℕ) (b : Fin n → Bool) :
    dot (selector b) (fun i => (s i : ℝ)) = (leftSum (tagged s b) : ℝ) := by
  simp only [dot, selector, leftSum, tagged, List.map_ofFn, List.sum_ofFn, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases h : b i <;> simp [h]

theorem verify_iff_partition {n : ℕ} (s : Fin n → ℕ) (b : Fin n → Bool) :
    verify s b = true ↔ is_ec_partition (selector b) (fun i => (s i : ℝ)) := by
  obtain ⟨hlc, hrc, hls, hrs⟩ := run_correct (tagged s b)
  have hc : (leftCount (tagged s b) : ℝ) + (rightCount (tagged s b) : ℝ) = (n : ℝ) := by
    exact_mod_cast (show leftCount (tagged s b) + rightCount (tagged s b) = n by
      simpa [tagged] using counts_total (tagged s b))
  have hs : (leftSum (tagged s b) : ℝ) + (rightSum (tagged s b) : ℝ) =
      dot (fun i => (s i : ℝ)) 1 := by
    rw [← Nat.cast_add, sums_total]
    simp [tagged, dot, List.map_ofFn, List.sum_ofFn, Nat.cast_sum]
  simp only [verify, Bool.and_eq_true, beq_iff_eq, hlc, hrc, hls, hrs,
    is_ec_partition, selector_count s b, selector_sum]
  constructor
  · rintro ⟨hcount, hsum⟩
    have hcount' : (leftCount (tagged s b) : ℝ) = (rightCount (tagged s b) : ℝ) := by exact_mod_cast hcount
    have hsum' : (leftSum (tagged s b) : ℝ) = (rightSum (tagged s b) : ℝ) := by exact_mod_cast hsum
    exact ⟨selector_binary b, by linarith, by linarith⟩
  · rintro ⟨_, hcount, hsum⟩
    constructor
    · exact_mod_cast (show (leftCount (tagged s b) : ℝ) = (rightCount (tagged s b) : ℝ) by linarith)
    · exact_mod_cast (show (leftSum (tagged s b) : ℝ) = (rightSum (tagged s b) : ℝ) by linarith)

theorem binary_has_certificate {n : ℕ} (a : Vec n) (ha : is_binary a) :
    ∃ b : Fin n → Bool, selector b = a := by
  classical
  refine ⟨fun i => decide (a i = 1), ?_⟩
  funext i
  rcases ha i with hi | hi <;> simp [selector, hi]

/-- The original gadget predicate has a certificate of `2*d` bits, verified
within a quadratic binary-arithmetic work bound. The threshold and the main
pointwise iff are unchanged. -/
theorem gadget_polynomial_certificate (d : ℕ) (s : Fin (2 * d) → ℕ)
    (hd : 1 < d) (hc : 1 ≤ dot (fun i => (s i : ℝ)) 1 / 2)
    (hs : perf_square_vec (fun i => (s i : ℝ))) :
    (∃ a : Vec (2 * d), box_constraints a ∧ dot a 1 = (d : ℝ) ∧
      hinge_form (dot (fun i => (s i : ℝ)) 1 / 2) a
        (partition_gadget_schedule d (fun i => (s i : ℝ))) ≤
        partition_schedule_threshold d a (fun i => (s i : ℝ))) ↔
    ∃ b : Fin (2 * d) → Bool, verify s b = true ∧
      (certificate b).length ≤ inputBits s ∧
      verificationWork s b ≤ 128 * (inputBits s + 1) ^ 2 := by
  constructor
  · rintro ⟨a, ha⟩
    have hp := (partition_gadget_schedule_pointwise_iff d a (fun i => (s i : ℝ)) hd hc hs).mp ha
    obtain ⟨b, hb⟩ := binary_has_certificate a hp.1
    refine ⟨b, (verify_iff_partition s b).mpr (by rwa [hb]), ?_, verificationWork_le s b⟩
    rw [certificate_length]
    exact dimension_le_inputBits s
  · rintro ⟨b, hb, _, _⟩
    exact ⟨selector b, (partition_gadget_schedule_pointwise_iff d (selector b)
      (fun i => (s i : ℝ)) hd hc hs).mpr ((verify_iff_partition s b).mp hb)⟩

end CSeparatedNPComplete.PolynomialCertificate
