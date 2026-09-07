import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt

/-!
# Gaussian separation and equal-cardinality partition

Selecting a small set of marker genes that jointly distinguishes cell types is
the motivation for this formulation. Gaussian class means and diagonal covariance
vectors describe both differences between cell types and variation within them.
The unpublished manuscript `c_separation_NP_completness-4.pdf` asks what happens
when binary feature selection is relaxed to weights in the unit cube, and cites
Borozan et al., *Optimal Marker Genes for c-Separated Cell Types* (RECOMB 2025),
as the source of the Gaussian c-separation model.

The theorem below is the pointwise gadget equivalence from `RocqOld/sepsolve.v:2782`.
A three-class gadget enforces the partition balance, and a Gaussian schedule
forces the relaxed selector to be binary at the stated bound. The threshold
explicitly depends on the selector; this statement does not assert a
fixed-threshold NP-hardness reduction or polynomial encoding bounds.

All definitions are given independently here. Only mathlib is imported; the
single deliberate proof placeholder belongs to the Challenge, not the Solution.
-/

noncomputable section

namespace CSeparatedNPComplete

abbrev Vec (n : Nat) := Fin n → Real
abbrev Gaussian (n : Nat) := Vec n × Vec n

def dot {n : Nat} (x y : Vec n) : Real := ∑ i, x i * y i

def sqVec {n : Nat} (x : Vec n) : Vec n := fun i => x i * x i

def is_binary {n : Nat} (a : Vec n) : Prop := ∀ i, a i = 0 ∨ a i = 1

def is_vec_leq {n : Nat} (a b : Vec n) : Prop := ∀ i, a i ≤ b i

def perf_square_vec {n : Nat} (s : Vec n) : Prop :=
  ∀ i, ∃ k : Nat, s i = (k : ℝ) * (k : ℝ)

def box_constraints {n : Nat} (a : Vec n) : Prop :=
  is_vec_leq 0 a ∧ is_vec_leq a 1

def is_ec_partition {n : Nat} (a s : Vec n) : Prop :=
  is_binary a ∧ dot a 1 = (n : ℝ) / 2 ∧ dot a s = dot s 1 / 2

def canon_e {n : Nat} (k : Nat) : Vec n := fun i => if i.val = k then 1 else 0

def hinge (c D S : ℝ) : ℝ := max 0 (c - D / S)

def gaussian_pair_stats {n : Nat} (a : Vec n) (p : Gaussian n × Gaussian n) : ℝ × ℝ :=
  (dot a (sqVec (p.1.1 - p.2.1)), max (dot a p.1.2) (dot a p.2.2))

def gaussian_pair_hinge {n : Nat} (c : ℝ) (a : Vec n) (g h : Gaussian n) : ℝ :=
  let (D, S) := gaussian_pair_stats a (g, h)
  hinge c D S

def hinge_against {n : Nat} (c : ℝ) (a : Vec n) (g : Gaussian n) :
    List (Gaussian n) → ℝ
  | [] => 0
  | h :: tail => gaussian_pair_hinge c a g h + hinge_against c a g tail

def hinge_form {n : Nat} (c : ℝ) (a : Vec n) : List (Gaussian n) → ℝ
  | [] => 0
  | g :: tail => hinge_against c a g tail + hinge_form c a tail

def gaussian_schedule_separation_sum (m : ℝ) (i k : Nat) : ℝ :=
  ∑ j ∈ Finset.range k, (m ^ i - m ^ j) ^ 2

def gaussian_schedule_mu {n : Nat} (m : ℝ) (i : Nat) : Vec n := fun _ => m ^ i

def gaussian_schedule_sigma {n : Nat} (m : ℝ) (i : Nat) : Vec n :=
  if i = 0 then 1 else
    fun j => gaussian_schedule_separation_sum m i i * (m * canon_e i j + 1)

def gaussian_schedule_class {n : Nat} (m : ℝ) (i : Nat) : Gaussian n :=
  (gaussian_schedule_mu m i, gaussian_schedule_sigma m i)

def gaussian_schedule {n : Nat} (m : ℝ) (k : Nat) : List (Gaussian n) :=
  (List.range k).map (gaussian_schedule_class m)

def second_gadget_gamma (n : Nat) (m : ℝ) : ℝ :=
  m + gaussian_schedule_separation_sum m n n

def second_gadget_mu1 {n : Nat} (m c : ℝ) : Vec n :=
  fun _ => second_gadget_gamma n m * (3 * c + m ^ n)

def second_gadget_mu2 {n : Nat} (m c : ℝ) (s : Vec n) : Vec n :=
  fun i => second_gadget_gamma n m * (3 * c + m ^ n + m * Real.sqrt (s i))

def second_gadget_mu3 {n : Nat} (m c : ℝ) : Vec n :=
  fun _ => second_gadget_gamma n m * (2 * c + m ^ n)

def second_gadget_sigma1 {n : Nat} (m : ℝ) : Vec n :=
  fun _ => second_gadget_gamma n m * second_gadget_gamma n m

def second_gadget_sigma2 {n : Nat} (m : ℝ) : Vec n :=
  fun _ => second_gadget_gamma n m * second_gadget_gamma n m * m

def second_gadget_sigma3 {n : Nat} (m : ℝ) (s : Vec n) : Vec n :=
  fun i => second_gadget_gamma n m * second_gadget_gamma n m * m * s i

def second_gadget_g1 {n : Nat} (m c : ℝ) : Gaussian n :=
  (second_gadget_mu1 m c, second_gadget_sigma1 m)

def second_gadget_g2 {n : Nat} (m c : ℝ) (s : Vec n) : Gaussian n :=
  (second_gadget_mu2 m c s, second_gadget_sigma2 m)

def second_gadget_g3 {n : Nat} (m c : ℝ) (s : Vec n) : Gaussian n :=
  (second_gadget_mu3 m c, second_gadget_sigma3 m s)

def second_gadget_instance {n : Nat} (m c : ℝ) (s : Vec n) : List (Gaussian n) :=
  [second_gadget_g1 m c, second_gadget_g2 m c s, second_gadget_g3 m c s]

def second_gadget_partition_instance {n : Nat} (m : ℝ) (s : Vec n) :
    List (Gaussian n) := second_gadget_instance m (dot s 1 / 2) s

def partition_gadget_schedule (d : Nat) (s : Vec (2 * d)) : List (Gaussian (2 * d)) :=
  second_gadget_partition_instance (d : ℝ) s ++ gaussian_schedule (d : ℝ) (2 * d)

def partition_schedule_threshold (d : Nat) (a s : Vec (2 * d)) : ℝ :=
  let k := 2 * d - 1
  dot s 1 / 2 * (k : ℝ) * ((k : ℝ) + 1) / 2 -
    (3 * (d : ℝ) / 2 - (1 + dot a (canon_e 0))⁻¹)

/-- The Gaussian bound holds precisely for equal-cardinality partition selectors.
This is the sole theorem submitted for comparison. -/
theorem partition_gadget_schedule_partition_iff
    (d : Nat) (a s : Vec (2 * d))
    (hd : 1 < d) (hc : 1 ≤ dot s 1 / 2) (hs : perf_square_vec s) :
    (box_constraints a ∧ dot a 1 = (d : ℝ) ∧
      hinge_form (dot s 1 / 2) a (partition_gadget_schedule d s) ≤
        partition_schedule_threshold d a s) ↔ is_ec_partition a s := by
  sorry

end CSeparatedNPComplete
