import CSeparatedNPComplete.SquarePartition

/-!
# Ordinary PARTITION to equal-cardinality partition of positive squares

The input weights are positive natural numbers. Coordinates start at one in the
exponents. The explicit base dominates both the weights and all possible error
terms, so even an arbitrary equal-sum partition must split every pair.
-/

namespace CSeparatedNPComplete.SquareReduction

def base {n : ℕ} (a : Fin n → ℕ) : ℕ :=
  2 + n + 2 * ∑ i, a i + ∑ i, (a i) ^ 2

def upper {n : ℕ} (a : Fin n → ℕ) (i : Fin n) : ℕ :=
  base a ^ (n + i.val + 1)

def lower {n : ℕ} (a : Fin n → ℕ) (i : Fin n) : ℕ :=
  a i * base a ^ (n - (i.val + 1))

def values {n : ℕ} (a : Fin n → ℕ) : Vec (n + n) :=
  Fin.append (fun i => (((upper a i + lower a i) ^ 2 : ℕ) : ℝ))
    (fun i => (((upper a i - lower a i) ^ 2 : ℕ) : ℝ))

/-- Ordinary PARTITION: a binary choice with half the total weight, with no
cardinality restriction on the choice. -/
def HasPartition {n : ℕ} (a : Fin n → ℕ) : Prop :=
  ∃ p : Vec n, is_binary p ∧ dot p (fun i => (a i : ℝ)) = (∑ i, (a i : ℝ)) / 2

theorem base_ge_two {n : ℕ} (a : Fin n → ℕ) : 2 ≤ base a := by
  unfold base
  omega

theorem weight_lt_base {n : ℕ} (a : Fin n → ℕ) (i : Fin n) : a i < base a := by
  have h : a i ≤ ∑ j, a j := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
  unfold base
  omega

theorem lower_lt_upper {n : ℕ} (a : Fin n → ℕ) (i : Fin n) : lower a i < upper a i := by
  have hK := base_ge_two a
  have ha : a i < base a ^ (2 * (i.val + 1)) :=
    lt_of_lt_of_le (weight_lt_base a i)
      (le_self_pow₀ (by omega : 1 ≤ base a) (by omega))
  calc
    lower a i < base a ^ (2 * (i.val + 1)) * base a ^ (n - (i.val + 1)) :=
      Nat.mul_lt_mul_of_pos_right ha (by positivity)
    _ = upper a i := by unfold upper; rw [← pow_add]; congr 1; omega

theorem root_product {n : ℕ} (a : Fin n → ℕ) (i : Fin n) :
    upper a i * lower a i = a i * base a ^ (2 * n) := by
  unfold upper lower
  rw [mul_left_comm, ← pow_add]
  congr 2
  omega

/-- A bounded perturbation cannot cancel a nonzero highest base-power digit. -/
theorem digits_vanish {n : ℕ} (K C : ℝ) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hlarge : (n : ℝ) + C < K ^ 2) (d : Fin n → ℝ)
    (hd : ∀ i, d i = -1 ∨ d i = 0 ∨ d i = 1) (e : ℝ)
    (he : |e| ≤ C * K ^ (2 * n))
    (hzero : (∑ i, d i * K ^ (2 * n + 2 * i.val + 2)) + e = 0) :
    ∀ i, d i = 0 := by
  classical
  by_contra h
  have hn : (Finset.univ.filter fun i => d i ≠ 0).Nonempty := by
    simpa only [Finset.filter_nonempty_iff, Finset.mem_univ, true_and, not_forall] using h
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image _ (fun i : Fin n => i.val) hn
  have hjne : d j ≠ 0 := (Finset.mem_filter.mp hj).2
  let T := K ^ (2 * n + 2 * j.val)
  have hT : 0 < T := by dsimp [T]; positivity
  have hbase : K ^ (2 * n) ≤ T := pow_le_pow_right₀ hK (by omega)
  have hjabs : |d j| = 1 := by rcases hd j with h | h | h <;> simp_all
  have hsmall (i : Fin n) (hi : i ∈ Finset.univ.erase j) :
      |d i * K ^ (2 * n + 2 * i.val + 2)| ≤ T := by
    by_cases hz : d i = 0
    · simp [hz, hT.le]
    have hij : i.val < j.val := by
      have hle := hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩)
      have hne := (Finset.mem_erase.mp hi).1
      have : i.val ≠ j.val := fun hv => hne (Fin.ext hv)
      omega
    have habs : |d i| = 1 := by rcases hd i with h | h | h <;> simp_all
    rw [abs_mul, habs, one_mul, abs_of_nonneg (by positivity)]
    exact pow_le_pow_right₀ hK (by omega)
  have hsum : |∑ i ∈ Finset.univ.erase j, d i * K ^ (2 * n + 2 * i.val + 2)| ≤ (n : ℝ) * T := by
    calc
      _ ≤ ∑ i ∈ Finset.univ.erase j, |d i * K ^ (2 * n + 2 * i.val + 2)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.univ.erase j, T := Finset.sum_le_sum hsmall
      _ ≤ (n : ℝ) * T := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast (show (Finset.univ.erase j).card ≤ n from
          (Finset.card_le_card (Finset.erase_subset j Finset.univ)).trans_eq (Finset.card_fin n))
  have hexpand : K ^ (2 * n + 2 * j.val + 2) = K ^ 2 * T := by
    dsimp [T]
    rw [pow_add, mul_comm]
  have hsplit := Finset.sum_erase_add Finset.univ
    (fun i : Fin n => d i * K ^ (2 * n + 2 * i.val + 2)) (Finset.mem_univ j)
  have hlead : |d j * K ^ (2 * n + 2 * j.val + 2)| ≤ (n : ℝ) * T + C * T := by
    calc
      _ = |(∑ i ∈ Finset.univ.erase j, d i * K ^ (2 * n + 2 * i.val + 2)) + e| := by
        have : d j * K ^ (2 * n + 2 * j.val + 2) =
            -((∑ i ∈ Finset.univ.erase j, d i * K ^ (2 * n + 2 * i.val + 2)) + e) := by linarith
        rw [this, abs_neg]
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hsum (he.trans (mul_le_mul_of_nonneg_left hbase hC)))
  rw [abs_mul, hjabs, one_mul, abs_of_nonneg (by positivity), hexpand] at hlead
  nlinarith

theorem balance_identity {n : ℕ} (a : Fin n → ℕ) (p q : Vec n) :
    dot (Fin.append p q) (values a) - dot (values a) 1 / 2 =
      ∑ i, ((p i + q i - 1) * (base a : ℝ) ^ (2 * n + 2 * i.val + 2) +
        (2 * (p i - q i) * (a i : ℝ) * (base a : ℝ) ^ (2 * n) +
          (p i + q i - 1) * (lower a i : ℝ) ^ 2)) := by
  simp only [dot, values, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    Pi.one_apply, mul_one]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hroot : (upper a i : ℝ) * (lower a i : ℝ) = (a i : ℝ) * (base a : ℝ) ^ (2 * n) := by
    exact_mod_cast root_product a i
  have hu : (upper a i : ℝ) ^ 2 = (base a : ℝ) ^ (2 * n + 2 * i.val + 2) := by
    simp only [upper, Nat.cast_pow, ← pow_mul]
    congr 1
    omega
  rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_add, Nat.cast_sub (lower_lt_upper a i).le]
  calc
    _ = (p i + q i - 1) * (upper a i : ℝ) ^ 2 +
        2 * (p i - q i) * ((upper a i : ℝ) * (lower a i : ℝ)) +
        (p i + q i - 1) * (lower a i : ℝ) ^ 2 := by ring
    _ = _ := by rw [hu, hroot]; ring

theorem lower_square_bound {n : ℕ} (a : Fin n → ℕ) (i : Fin n) :
    (lower a i : ℝ) ^ 2 ≤ (a i : ℝ) ^ 2 * (base a : ℝ) ^ (2 * n) := by
  simp only [lower, Nat.cast_mul, Nat.cast_pow, mul_pow, ← pow_mul]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply pow_le_pow_right₀
  · exact_mod_cast (base_ge_two a).trans' (by decide : 1 ≤ 2)
  · omega

/-- Equal sums force one member of every pair onto each side. The hypothesis
does not assume equal cardinalities or a paired form of the selector. -/
theorem forces_pairs {n : ℕ} (a : Fin n → ℕ) (p q : Vec n)
    (hp : is_binary p) (hq : is_binary q)
    (hbal : dot (Fin.append p q) (values a) = dot (values a) 1 / 2) :
    ∀ i, p i + q i = 1 := by
  let d : Fin n → ℝ := fun i => p i + q i - 1
  let C : ℝ := ∑ i, (2 * (a i : ℝ) + (a i : ℝ) ^ 2)
  let e : ℝ := ∑ i, (2 * (p i - q i) * (a i : ℝ) * (base a : ℝ) ^ (2 * n) +
    d i * (lower a i : ℝ) ^ 2)
  have hK : 1 ≤ (base a : ℝ) := by exact_mod_cast (show 1 ≤ base a by have := base_ge_two a; omega)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbase : (base a : ℝ) = 2 + n + C := by
    simp [base, C, Nat.cast_add, Nat.cast_mul, Nat.cast_sum, Nat.cast_pow,
      Finset.sum_add_distrib, Finset.mul_sum, add_assoc]
  have hlarge : (n : ℝ) + C < (base a : ℝ) ^ 2 := by nlinarith
  have hd (i : Fin n) : d i = -1 ∨ d i = 0 ∨ d i = 1 := by
    rcases hp i with h | h <;> rcases hq i with h' | h' <;> simp [d, h, h']
  have habsd (i : Fin n) : |d i| ≤ 1 := by
    rcases hd i with h | h | h <;> simp [h]
  have habspq (i : Fin n) : |p i - q i| ≤ 1 := by
    rcases hp i with h | h <;> rcases hq i with h' | h' <;> norm_num [h, h']
  have he : |e| ≤ C * (base a : ℝ) ^ (2 * n) := by
    dsimp [e, C]
    rw [Finset.sum_mul]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ |2 * (p i - q i) * (a i : ℝ) * (base a : ℝ) ^ (2 * n)| +
          |d i * (lower a i : ℝ) ^ 2| := abs_add_le _ _
      _ ≤ 2 * (a i : ℝ) * (base a : ℝ) ^ (2 * n) +
          (a i : ℝ) ^ 2 * (base a : ℝ) ^ (2 * n) := by
        simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
          abs_of_nonneg (show 0 ≤ (a i : ℝ) by positivity), abs_of_nonneg (show 0 ≤ (base a : ℝ) ^ (2 * n) by positivity),
          abs_of_nonneg (sq_nonneg (lower a i : ℝ))]
        apply add_le_add
        · calc
            _ ≤ 2 * 1 * (a i : ℝ) * (base a : ℝ) ^ (2 * n) := by gcongr; exact habspq i
            _ = _ := by ring
        · calc
            _ ≤ 1 * (lower a i : ℝ) ^ 2 := mul_le_mul_of_nonneg_right (habsd i) (sq_nonneg _)
            _ ≤ _ := by simpa using lower_square_bound a i
      _ = _ := by ring
  have hz : (∑ i, d i * (base a : ℝ) ^ (2 * n + 2 * i.val + 2)) + e = 0 := by
    have h := balance_identity a p q
    rw [hbal, sub_self] at h
    simpa only [d, e, Finset.sum_add_distrib] using h.symm
  have hv := digits_vanish (base a : ℝ) C hK hC hlarge d hd e he hz
  intro i
  have := hv i
  dsimp [d] at this
  linarith

theorem paired_balance_identity {n : ℕ} (a : Fin n → ℕ) (p : Vec n) :
    dot (Fin.append p (1 - p)) (values a) - dot (values a) 1 / 2 =
      4 * (base a : ℝ) ^ (2 * n) *
        (dot p (fun i => (a i : ℝ)) - (∑ i, (a i : ℝ)) / 2) := by
  rw [balance_identity]
  simp only [dot, mul_sub, Finset.mul_sum, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, Pi.one_apply]
  ring

theorem paired_card {n : ℕ} (p : Vec n) :
    dot (Fin.append p (1 - p)) 1 = ((n + n : ℕ) : ℝ) / 2 := by
  simp only [dot, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    Pi.one_apply, Pi.sub_apply, mul_one]
  rw [← Finset.sum_add_distrib]
  simp

/-- Correctness of the explicit reduction, with no assumptions on a caller's
choice of base and no restriction to paired target witnesses. -/
theorem exists_ec_partition_iff {n : ℕ} (a : Fin n → ℕ) :
    (∃ x : Vec (n + n), is_ec_partition x (values a)) ↔ HasPartition a := by
  have hK := base_ge_two a
  have hfactor : 0 < 4 * (base a : ℝ) ^ (2 * n) := by
    have : 0 < (base a : ℝ) := by exact_mod_cast (show 0 < base a by omega)
    positivity
  constructor
  · rintro ⟨x, hxbin, _, hxbal⟩
    let p : Vec n := fun i => x (Fin.castAdd n i)
    let q : Vec n := fun i => x (Fin.natAdd n i)
    have hx : Fin.append p q = x := Fin.append_castAdd_natAdd
    have hp : is_binary p := fun i => hxbin _
    have hq : is_binary q := fun i => hxbin _
    have hpq := forces_pairs a p q hp hq (by rwa [hx])
    have hqeq : q = 1 - p := by
      funext i
      have := hpq i
      simp only [Pi.sub_apply, Pi.one_apply]
      linarith
    refine ⟨p, hp, ?_⟩
    have hid := paired_balance_identity a p
    rw [← hqeq, hx, hxbal, sub_self] at hid
    nlinarith
  · rintro ⟨p, hp, hbal⟩
    refine ⟨Fin.append p (1 - p), ?_, paired_card p, ?_⟩
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa only [Fin.append_left] using hp j
      · intro j
        simp only [Fin.append_right, Pi.sub_apply, Pi.one_apply]
        rcases hp j with h | h <;> simp [h]
    · have hid := paired_balance_identity a p
      rw [hbal, sub_self, mul_zero] at hid
      linarith

theorem values_perfect_square {n : ℕ} (a : Fin n → ℕ) : perf_square_vec (values a) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine ⟨upper a j + lower a j, ?_⟩
    simp only [values, Fin.append_left, pow_two, Nat.cast_mul]
  · intro j
    refine ⟨upper a j - lower a j, ?_⟩
    simp only [values, Fin.append_right, pow_two, Nat.cast_mul]

theorem values_positive {n : ℕ} (a : Fin n → ℕ) : ∀ i, 0 < values a i := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    have h : 0 < upper a j := lt_of_le_of_lt (Nat.zero_le _) (lower_lt_upper a j)
    simp only [values, Fin.append_left]
    exact_mod_cast (show 0 < (upper a j + lower a j) ^ 2 by positivity)
  · intro j
    have h : 0 < upper a j - lower a j := Nat.sub_pos_of_lt (lower_lt_upper a j)
    simp only [values, Fin.append_right]
    exact_mod_cast (show 0 < (upper a j - lower a j) ^ 2 by positivity)

/-- The actual output is a computable vector of natural numbers. -/
def encode {n : ℕ} (a : Fin n → ℕ) : Fin (n + n) → ℕ :=
  Fin.append (fun i => (upper a i + lower a i) ^ 2)
    (fun i => (upper a i - lower a i) ^ 2)

theorem values_eq_encode {n : ℕ} (a : Fin n → ℕ) :
    values a = fun i => (encode a i : ℝ) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp only [values, encode, Fin.append_left]
  · intro j; simp only [values, encode, Fin.append_right]

/-- A numerical bound giving polynomial binary output length: there are `2*n`
entries, each with at most `4*(n+1)*log₂ K + 1` bits. -/
theorem encode_bound {n : ℕ} (a : Fin n → ℕ) (i : Fin (n + n)) :
    encode a i ≤ base a ^ (4 * (n + 1)) := by
  have hK := base_ge_two a
  have hp (j : Fin n) : (upper a j + lower a j) ^ 2 ≤ base a ^ (4 * (n + 1)) := by
    have hr : upper a j + lower a j ≤ base a ^ (2 * (n + 1)) := by
      calc
        _ ≤ 2 * upper a j := by have := lower_lt_upper a j; omega
        _ ≤ base a * upper a j := Nat.mul_le_mul_right _ hK
        _ = base a ^ (n + j.val + 2) := by simp [upper, pow_succ, mul_comm]
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
    calc
      _ ≤ (base a ^ (2 * (n + 1))) ^ 2 := Nat.pow_le_pow_left hr 2
      _ = _ := by rw [← pow_mul]; congr 1; omega
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [encode, Fin.append_left] using hp j
  · intro j
    simp only [encode, Fin.append_right]
    exact (Nat.pow_le_pow_left (show upper a j - lower a j ≤ upper a j + lower a j by omega) 2).trans (hp j)

/-- The base itself has polynomial magnitude in the input count and maximum
weight. Its binary length is therefore linear in their binary lengths. -/
theorem base_bound {n : ℕ} (a : Fin n → ℕ) (M : ℕ) (ha : ∀ i, a i ≤ M) :
    base a ≤ 2 + n + 2 * n * M + n * M ^ 2 := by
  have hs : ∑ i, a i ≤ n * M := by
    calc
      _ ≤ ∑ _i : Fin n, M := Finset.sum_le_sum fun i _ => ha i
      _ = _ := by simp
  have hq : ∑ i, (a i) ^ 2 ≤ n * M ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin n, M ^ 2 := Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left (ha i) 2
      _ = _ := by simp
  unfold base
  nlinarith

/-- The ordered encoding is one-to-one, in addition to preserving yes/no
answers. Karp (many-one) reducibility itself does not require injectivity. -/
theorem encode_injective (n : ℕ) : Function.Injective (@encode n) := by
  intro a b h
  have hroots (i : Fin n) : upper a i = upper b i ∧ lower a i = lower b i := by
    have hp := congrFun h (Fin.castAdd n i)
    have hm := congrFun h (Fin.natAdd n i)
    simp only [encode, Fin.append_left] at hp
    simp only [encode, Fin.append_right] at hm
    have hp' := (pow_left_inj₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 2 ≠ 0)).mp hp
    have hm' := (pow_left_inj₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 2 ≠ 0)).mp hm
    have ha := lower_lt_upper a i
    have hb := lower_lt_upper b i
    omega
  by_cases hn : 0 < n
  · have hu := (hroots ⟨0, hn⟩).1
    simp only [upper, add_zero] at hu
    have hbase : base a = base b :=
      (pow_left_inj₀ (Nat.zero_le _) (Nat.zero_le _) (by omega : n + 1 ≠ 0)).mp hu
    funext i
    have hl := (hroots i).2
    simp only [lower, hbase] at hl
    have hK := base_ge_two b
    exact (mul_right_cancel₀ (by positivity : base b ^ (n - (i.val + 1)) ≠ 0)) hl
  · funext i
    have := i.isLt
    omega

end CSeparatedNPComplete.SquareReduction
