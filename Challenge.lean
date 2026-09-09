import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt

/-!
# Gaussian separation and equal-cardinality partition

Selecting a small set of marker genes that jointly distinguishes cell types is
the motivation for this formulation. Gaussian class means and diagonal covariance
vectors describe both differences between cell types and variation within them.
The Gaussian c-separation feature-selection formulation is due to Borozan et al.,
*Optimal Marker Genes for c-Separated Cell Types* (RECOMB 2025). The project's
intended complexity statement is NP-hardness of relative Gaussian c-separation
by feature selection. The construction below studies weights in the unit cube.

The proof strategy starts from equal-cardinality partition of positive perfect
squares, whose NP-completeness is established by the accompanying reduction
from ordinary PARTITION. Squares make the roots in the Gaussian means integral.
The paired square construction also has even total, making c integral. On its
outputs the Gaussian means and diagonal covariances are integers, and the
fixed threshold is (dot s 1 / 2)*d*(d+1)/2 - 3*d/4, an integer multiple of 1/4.
Here d is the full feature dimension, and the schedule base is d/2.

The theorem below states the pointwise gadget equivalence.
Three Gaussians enforce partition balance; a schedule of d+1 Gaussians forces
the relaxed selector to be binary through equality in the reciprocal bound.
Explicit offsets and scaling place the two blocks far apart, making all
cross-block hinge penalties zero. The two requirements therefore combine
into the stated iff. There are d+4 classes in the implemented construction.
The threshold is fixed for each input. This statement does not assert a
machine-model NP-hardness theorem or polynomial encoding bounds.

All definitions are given independently here. Only mathlib is imported; the
single deliberate proof placeholder belongs to the Challenge, not the Solution.
-/

noncomputable section

namespace CSeparatedNPComplete

/-- A real vector with coordinates indexed from zero to `n - 1`. -/
abbrev Vec (n : Nat) := Fin n → Real
/-- Mean and diagonal covariance vectors; no probability distribution is constructed. -/
abbrev Gaussian (n : Nat) := Vec n × Vec n

/-- The usual finite dot product. -/
def dot {n : Nat} (x y : Vec n) : Real := ∑ i, x i * y i

/-- Coordinatewise squaring. -/
def sqVec {n : Nat} (x : Vec n) : Vec n := fun i => x i * x i

/-- Every feature weight is either zero or one. -/
def is_binary {n : Nat} (a : Vec n) : Prop := ∀ i, a i = 0 ∨ a i = 1

/-- Coordinatewise order on real vectors. -/
def is_vec_leq {n : Nat} (a b : Vec n) : Prop := ∀ i, a i ≤ b i

/-- Each input coordinate is a natural-number square, including zero. -/
def perf_square_vec {n : Nat} (s : Vec n) : Prop :=
  ∀ i, ∃ k : Nat, s i = (k : ℝ) * (k : ℝ)

/-- The relaxed selector belongs to the closed unit cube. -/
def box_constraints {n : Nat} (a : Vec n) : Prop :=
  is_vec_leq 0 a ∧ is_vec_leq a 1

/-- A binary selector chooses half the coordinates and half the total input weight. -/
def is_ec_partition {n : Nat} (a s : Vec n) : Prop :=
  is_binary a ∧ dot a 1 = (n : ℝ) / 2 ∧ dot a s = dot s 1 / 2

/-- Coordinate `k`'s basis vector; zero when `k` is outside the dimension. -/
def canon_e {n : Nat} (k : Nat) : Vec n := fun i => if i.val = k then 1 else 0

/-- Positive part of the separation deficit. Lean's real division has `D / 0 = 0`. -/
def hinge (c D S : ℝ) : ℝ := max 0 (c - D / S)

/-- Weighted squared mean distance and maximum weighted diagonal covariance sum. -/
def gaussian_pair_stats {n : Nat} (a : Vec n) (p : Gaussian n × Gaussian n) : ℝ × ℝ :=
  (dot a (sqVec (p.1.1 - p.2.1)), max (dot a p.1.2) (dot a p.2.2))

/-- Separation deficit for one pair of Gaussian parameter vectors. -/
def gaussian_pair_hinge {n : Nat} (c : ℝ) (a : Vec n) (g h : Gaussian n) : ℝ :=
  let (D, S) := gaussian_pair_stats a (g, h)
  hinge c D S

/-- Sum of deficits between one class and every class in a list. -/
def hinge_against {n : Nat} (c : ℝ) (a : Vec n) (g : Gaussian n) :
    List (Gaussian n) → ℝ
  | [] => 0
  | h :: tail => gaussian_pair_hinge c a g h + hinge_against c a g tail

/-- Sum over all unordered pairs of distinct list positions, each counted once. -/
def hinge_form {n : Nat} (c : ℝ) (a : Vec n) : List (Gaussian n) → ℝ
  | [] => 0
  | g :: tail => hinge_against c a g tail + hinge_form c a tail

/-- Sum of squared scalar mean differences from index `i` to indices below `k`. -/
def gaussian_schedule_separation_sum (m : ℝ) (i k : Nat) : ℝ :=
  ∑ j ∈ Finset.range k, (m ^ i - m ^ j) ^ 2

/-- Schedule mean: the constant vector with value `m^i`. -/
def gaussian_schedule_mu {n : Nat} (m : ℝ) (i : Nat) : Vec n := fun _ => m ^ i

/-- Unit covariance at index zero; thereafter scaled with a bump at coordinate `i`. -/
def gaussian_schedule_sigma {n : Nat} (m : ℝ) (i : Nat) : Vec n :=
  if i = 0 then 1 else
    fun j => gaussian_schedule_separation_sum m i i * (m * canon_e (i - 1) j + 1)

/-- Mean and diagonal covariance of schedule class `i`. -/
def gaussian_schedule_class {n : Nat} (m : ℝ) (i : Nat) : Gaussian n :=
  (gaussian_schedule_mu m i, gaussian_schedule_sigma m i)

/-- The first `k` schedule classes, in increasing index order. -/
def gaussian_schedule {n : Nat} (m : ℝ) (k : Nat) : List (Gaussian n) :=
  (List.range k).map (gaussian_schedule_class m)

/-- Common scale of the three-class gadget relative to the schedule. -/
def second_gadget_gamma (n : Nat) (m : ℝ) : ℝ :=
  m + gaussian_schedule_separation_sum m n n

/-- First gadget mean: the common shifted baseline. -/
def second_gadget_mu1 {n : Nat} (m c : ℝ) : Vec n :=
  fun _ => second_gadget_gamma n m * (3 * c + m ^ n)

/-- Second gadget mean: baseline plus scaled square roots of the input. -/
def second_gadget_mu2 {n : Nat} (m c : ℝ) (s : Vec n) : Vec n :=
  fun i => second_gadget_gamma n m * (3 * c + m ^ n + m * Real.sqrt (s i))

/-- Third gadget mean: baseline lowered by `gamma * c`. -/
def second_gadget_mu3 {n : Nat} (m c : ℝ) : Vec n :=
  fun _ => second_gadget_gamma n m * (2 * c + m ^ n)

/-- First gadget covariance: the constant `gamma^2` vector. -/
def second_gadget_sigma1 {n : Nat} (m : ℝ) : Vec n :=
  fun _ => second_gadget_gamma n m * second_gadget_gamma n m

/-- Second gadget covariance: the constant `gamma^2 * m` vector. -/
def second_gadget_sigma2 {n : Nat} (m : ℝ) : Vec n :=
  fun _ => second_gadget_gamma n m * second_gadget_gamma n m * m

/-- Third gadget covariance: `gamma^2 * m` times the input vector. -/
def second_gadget_sigma3 {n : Nat} (m : ℝ) (s : Vec n) : Vec n :=
  fun i => second_gadget_gamma n m * second_gadget_gamma n m * m * s i

/-- First gadget class. -/
def second_gadget_g1 {n : Nat} (m c : ℝ) : Gaussian n :=
  (second_gadget_mu1 m c, second_gadget_sigma1 m)

/-- Second gadget class, encoding input weights through its mean. -/
def second_gadget_g2 {n : Nat} (m c : ℝ) (s : Vec n) : Gaussian n :=
  (second_gadget_mu2 m c s, second_gadget_sigma2 m)

/-- Third gadget class, encoding input weights through its covariance. -/
def second_gadget_g3 {n : Nat} (m c : ℝ) (s : Vec n) : Gaussian n :=
  (second_gadget_mu3 m c, second_gadget_sigma3 m s)

/-- The ordered three-class partition balance gadget. -/
def second_gadget_instance {n : Nat} (m c : ℝ) (s : Vec n) : List (Gaussian n) :=
  [second_gadget_g1 m c, second_gadget_g2 m c s, second_gadget_g3 m c s]

/-- Specialize the balance gadget to separation parameter half the input total. -/
def second_gadget_partition_instance {n : Nat} (m : ℝ) (s : Vec n) :
    List (Gaussian n) := second_gadget_instance m (dot s 1 / 2) s

/-- Three gadget classes followed by `d+1` schedule classes, in dimension `d`. -/
def partition_gadget_schedule (d : Nat) (s : Vec d) : List (Gaussian d) :=
  second_gadget_partition_instance ((d : ℝ) / 2) s ++
    gaussian_schedule ((d : ℝ) / 2) (d + 1)

/-- Fixed threshold, where `d` is the full feature dimension. -/
def partition_schedule_threshold (d : Nat) (s : Vec d) : ℝ :=
  dot s 1 / 2 * (d : ℝ) * ((d : ℝ) + 1) / 2 - 3 * (d : ℝ) / 4

/-- The Gaussian bound holds precisely for equal-cardinality partition selectors.
This is the sole theorem submitted for comparison. -/
theorem partition_gadget_schedule_partition_iff
    (d : Nat) (a s : Vec d)
    (hd : 4 ≤ d) (hc : 1 ≤ dot s 1 / 2) (hs : perf_square_vec s) :
    (box_constraints a ∧ dot a 1 = (d : ℝ) / 2 ∧
      hinge_form (dot s 1 / 2) a (partition_gadget_schedule d s) ≤
        partition_schedule_threshold d s) ↔ is_ec_partition a s := by
  sorry

end CSeparatedNPComplete
