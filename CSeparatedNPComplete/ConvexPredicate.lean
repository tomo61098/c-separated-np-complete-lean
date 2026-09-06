import CSeparatedNPComplete.Definitions
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Linarith

namespace CSeparatedNPComplete

/-- The source's bundled convexity condition is exactly mathlib's `ConvexOn`. -/
theorem convexOnPredicate_iff_convexOn (P : Real → Prop) (f : Real → Real) :
    convexOnPredicate P f ↔ ConvexOn ℝ {x | P x} f := by
  constructor
  · intro h
    constructor
    · intro x hx y hy a b ha hb hab
      have hb' : b = 1 - a := by linarith
      simpa only [hb', smul_eq_mul, Set.mem_setOf_eq] using
        (h x y hx hy a ha (by linarith)).1
    · intro x hx y hy a b ha hb hab
      have hb' : b = 1 - a := by linarith
      simpa only [hb', smul_eq_mul] using (h x y hx hy a ha (by linarith)).2
  · intro h x y hx hy t ht ht'
    exact ⟨h.1 hx hy ht (sub_nonneg.mpr ht') (by ring),
      h.2 hx hy ht (sub_nonneg.mpr ht') (by ring)⟩

end CSeparatedNPComplete
