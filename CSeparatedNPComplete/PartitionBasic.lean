import CSeparatedNPComplete.PartitionDefs
import Mathlib.Tactic

namespace CSeparatedNPComplete

theorem dot_const {n : Nat} (a : Vec n) (r : ℝ) :
    dot a (fun _ => r) = r * dot a 1 := by
  simp only [dot, Pi.one_apply, mul_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dot_mul_right {n : Nat} (a v : Vec n) (r : ℝ) :
    dot a (fun i => r * v i) = r * dot a v := by
  simp only [dot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dot_add_right {n : Nat} (a u v : Vec n) :
    dot a (u + v) = dot a u + dot a v := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem dot_sub_right {n : Nat} (a u v : Vec n) :
    dot a (u - v) = dot a u - dot a v := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

theorem dot_nonneg {n : Nat} {a v : Vec n}
    (ha : is_vec_leq 0 a) (hv : is_vec_leq 0 v) : 0 ≤ dot a v :=
  Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (hv i)

theorem dot_mono_right {n : Nat} {a u v : Vec n}
    (ha : is_vec_leq 0 a) (huv : is_vec_leq u v) : dot a u ≤ dot a v :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (huv i) (ha i)

theorem dot_canon_e_eq {n : Nat} (a : Vec n) (i : Fin n) :
    dot a (canon_e i.val) = a i := by
  simp only [dot, canon_e, mul_ite, mul_one, mul_zero]
  simp_rw [Fin.val_inj]
  simp

theorem dot_canon_e_nonneg {n : Nat} (a : Vec n) (i : Nat)
    (ha : is_vec_leq 0 a) : 0 ≤ dot a (canon_e i) := by
  apply dot_nonneg ha
  intro j
  simp only [canon_e]
  split_ifs <;> norm_num

theorem dot_canon_e_le_dot_one {n : Nat} (a : Vec n) (i : Nat)
    (ha : is_vec_leq 0 a) : dot a (canon_e i) ≤ dot a 1 := by
  apply dot_mono_right ha
  intro j
  simp only [canon_e]
  split_ifs <;> norm_num

theorem is_binary_box_constraints {n : Nat} {a : Vec n}
    (ha : is_binary a) : box_constraints a := by
  constructor <;> intro i <;> rcases ha i with h | h <;> simp [h]

theorem perf_square_non_neg {n : Nat} {s : Vec n}
    (hs : perf_square_vec s) : is_vec_leq 0 s := by
  intro i
  obtain ⟨k, hk⟩ := hs i
  rw [hk]
  positivity

theorem gaussian_schedule_separation_sum_nonneg (m : ℝ) (i k : Nat) :
    0 ≤ gaussian_schedule_separation_sum m i k :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem second_gadget_gamma_pos (n : Nat) {m : ℝ} (hm : 0 < m) :
    0 < second_gadget_gamma n m :=
  add_pos_of_pos_of_nonneg hm (gaussian_schedule_separation_sum_nonneg m n n)

theorem second_gadget_gamma_ge_one (n : Nat) {m : ℝ} (hm : 1 ≤ m) :
    1 ≤ second_gadget_gamma n m :=
  hm.trans (le_add_of_nonneg_right (gaussian_schedule_separation_sum_nonneg m n n))

theorem hinge_eq_zero_iff {c D S : ℝ} (hS : 0 < S) :
    hinge c D S = 0 ↔ c * S ≤ D := by
  simp only [hinge, max_eq_left_iff, sub_nonpos, le_div_iff₀ hS]

theorem hinge_zero_mul_le {c D S : ℝ} (hS : 0 < S)
    (h : hinge c D S = 0) : c * S ≤ D := (hinge_eq_zero_iff hS).mp h

theorem hinge_zero_of_mul_le {c D S : ℝ} (hS : 0 < S)
    (h : c * S ≤ D) : hinge c D S = 0 := (hinge_eq_zero_iff hS).mpr h

theorem gaussian_pair_hinge_nonneg {n : Nat} (c : ℝ) (a : Vec n)
    (g h : Gaussian n) : 0 ≤ gaussian_pair_hinge c a g h := le_max_left _ _

theorem hinge_against_nonneg {n : Nat} (c : ℝ) (a : Vec n) (g : Gaussian n)
    (L : List (Gaussian n)) : 0 ≤ hinge_against c a g L := by
  induction L with
  | nil => exact le_rfl
  | cons h L ih => exact add_nonneg (gaussian_pair_hinge_nonneg c a g h) ih

theorem hinge_form_nonneg {n : Nat} (c : ℝ) (a : Vec n) (L : List (Gaussian n)) :
    0 ≤ hinge_form c a L := by
  induction L with
  | nil => exact le_rfl
  | cons g L ih => exact add_nonneg (hinge_against_nonneg c a g L) ih

theorem hinge_against_eq_zero {n : Nat} (c : ℝ) (a : Vec n) (g : Gaussian n)
    (L : List (Gaussian n))
    (h : ∀ b ∈ L, gaussian_pair_hinge c a g b = 0) : hinge_against c a g L = 0 := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    simp only [hinge_against, h b (by simp), zero_add]
    exact ih fun x hx => h x (by simp [hx])

theorem hinge_against_app {n : Nat} (c : ℝ) (a : Vec n) (g : Gaussian n)
    (L₁ L₂ : List (Gaussian n)) :
    hinge_against c a g (L₁ ++ L₂) = hinge_against c a g L₁ + hinge_against c a g L₂ := by
  induction L₁ with
  | nil => simp [hinge_against]
  | cons h L ih => simp [hinge_against, ih, add_assoc]

theorem hinge_form_app_no_cross {n : Nat} (c : ℝ) (a : Vec n)
    (L₁ L₂ : List (Gaussian n)) (h : ∀ g ∈ L₁, hinge_against c a g L₂ = 0) :
    hinge_form c a (L₁ ++ L₂) = hinge_form c a L₁ + hinge_form c a L₂ := by
  induction L₁ with
  | nil => simp [hinge_form]
  | cons g L ih =>
    simp only [List.cons_append, hinge_form, hinge_against_app, h g (by simp), add_zero]
    rw [ih (fun g hg => h g (by simp [hg]))]
    ring

theorem hinge_form_snoc {n : Nat} (c : ℝ) (a : Vec n)
    (L : List (Gaussian n)) (g : Gaussian n) :
    hinge_form c a (L ++ [g]) = hinge_form c a L + hinge_to c a L g := by
  induction L with
  | nil => simp [hinge_form, hinge_against, hinge_to]
  | cons h L ih =>
    simp only [List.cons_append, hinge_form, hinge_against_app, hinge_against, add_zero]
    rw [ih]
    simp only [hinge_to, List.map_cons, List.sum_cons]
    ring

end CSeparatedNPComplete
