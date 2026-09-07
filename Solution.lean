import CSeparatedNPComplete

/-!
The main proof `partition_gadget_schedule_partition_iff` is imported from
`CSeparatedNPComplete.Partition`; it is stated independently in `Challenge.lean`.
The declarations below retain the earlier auxiliary results.
The solution does not import the Challenge module or its statement placeholders.
-/

namespace CSeparatedNPComplete

theorem c_separates_zero (n : Nat) (c : Real) (l : List (Gaussian n)) :
    cSeparates c (fun _ => 0) l := by
  have is_ca_separated_zero : ∀ (g : Gaussian n) (tail : List (Gaussian n)),
      isCASeparated c (fun _ => 0) g tail := by
    intro g tail
    induction tail with
    | nil =>
        simp [isCASeparated]
    | cons h tail ih =>
        simp only [isCASeparated]
        repeat' constructor
        · simp [dot]
        · simp [dot]
        · exact ih
  induction l with
  | nil =>
      simp [cSeparates]
  | cons g tail ih =>
      simp only [cSeparates]
      constructor
      · exact is_ca_separated_zero g tail
      · exact ih

/-- Karamata's inequality for every finite dimension, including zero.
This is the predicate-domain formulation of `RocqOld/Karamata.v:Karamata_inequality`. -/
theorem Karamata_inequality
    (n : Nat) (P : Real → Prop) (f : Real → Real) (u v : Vec n)
    (hconv : convexOnPredicate P f)
    (Pu : ∀ i, P (u i)) (Pv : ∀ i, P (v i))
    (hmajorized : majorized u v) :
    vecSum (fun i => f (u i)) ≥ vecSum (fun i => f (v i)) := by
  exact hmajorized.sum_convex_le ((convexOnPredicate_iff_convexOn P f).mp hconv) Pu Pv

/-- The original zero-dimensional milestone is a special case of the general theorem. -/
theorem Karamata_inequality_zero
    (P : Real → Prop) (f : Real → Real) (u v : Vec 0)
        (hconv : convexOnPredicate P f)
        (Pu : ∀ i : Fin 0, P (u i))
        (Pv : ∀ i : Fin 0, P (v i))
        (hmajorized : majorized u v) :
        vecSum (fun i : Fin 0 => f (u i)) ≥ vecSum (fun i : Fin 0 => f (v i)) := by
    exact Karamata_inequality 0 P f u v hconv Pu Pv hmajorized

end CSeparatedNPComplete
