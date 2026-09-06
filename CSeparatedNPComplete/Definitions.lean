import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
Definitions shared by the solution proofs. `Challenge.lean` states these independently
so that its statement can be audited using only mathlib imports.
-/

namespace CSeparatedNPComplete

abbrev Vec (n : Nat) := Fin n → Real
abbrev Gaussian (n : Nat) := Vec n × Vec n

def dot {n : Nat} (x y : Vec n) : Real := ∑ i, x i * y i

def sqVec {n : Nat} (x : Vec n) : Vec n := fun i => x i * x i

def isCASeparated {n : Nat} (c : Real) (a : Vec n) (g : Gaussian n)
    (l : List (Gaussian n)) : Prop :=
  match g with
  | (mu, sigma) =>
      match l with
      | [] => True
      | (mu2, sigma2) :: tail =>
          c * dot a sigma ≤ dot a (sqVec (fun i => mu i - mu2 i)) ∧
          c * dot a sigma2 ≤ dot a (sqVec (fun i => mu i - mu2 i)) ∧
          isCASeparated c a g tail

def cSeparates {n : Nat} (c : Real) (a : Vec n) (l : List (Gaussian n)) : Prop :=
  match l with
  | [] => True
  | g :: tail => isCASeparated c a g tail ∧ cSeparates c a tail

def vecSum {n : Nat} (v : Vec n) : Real := ∑ i, v i

def prefixSum {n : Nat} (k : Nat) (v : Vec n) : Real :=
  ∑ i ∈ Finset.univ.filter (fun i => i.1 < k), v i

def sortedDesc {n : Nat} (v : Vec n) : Prop :=
  ∀ i j, i ≤ j → v j ≤ v i

/-- `u` majorizes `v`: descending entries, larger prefix sums, and equal totals. -/
def majorized {n : Nat} (u v : Vec n) : Prop :=
  sortedDesc u ∧
  sortedDesc v ∧
  (∀ k, prefixSum k v ≤ prefixSum k u) ∧
  vecSum u = vecSum v

/-- Convexity of the domain and the function, in the source's one-weight notation. -/
def convexOnPredicate (P : Real → Prop) (f : Real → Real) : Prop :=
  ∀ x y, P x → P y → ∀ t, 0 ≤ t → t ≤ 1 →
    P (t * x + (1 - t) * y) ∧
    f (t * x + (1 - t) * y) ≤ t * f x + (1 - t) * f y

end CSeparatedNPComplete
