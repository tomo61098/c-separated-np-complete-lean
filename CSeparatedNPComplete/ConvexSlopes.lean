import Mathlib.Analysis.Convex.Slope
import Mathlib.Order.Monotone.Extension
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace CSeparatedNPComplete

/-- A divided difference is unchanged when its endpoints are exchanged. -/
private theorem secant_symm (f : ℝ → ℝ) (x y : ℝ) :
    (f y - f x) / (y - x) = (f x - f y) / (x - y) := by
  rw [← neg_div_neg_eq]
  simp

/-- Moving both endpoints of a nondegenerate secant to the right increases its slope. -/
theorem convex_secant_mono {s : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ s f)
    {x₁ x₂ y₁ y₂ : ℝ} (hx₁ : x₁ ∈ s) (hx₂ : x₂ ∈ s)
    (hy₁ : y₁ ∈ s) (hy₂ : y₂ ∈ s)
    (h₁ : x₁ ≠ y₁) (h₂ : x₂ ≠ y₂) (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    (f y₁ - f x₁) / (y₁ - x₁) ≤ (f y₂ - f x₂) / (y₂ - x₂) := by
  by_cases h : x₁ = y₂
  · subst y₂
    rw [secant_symm f x₂ x₁]
    exact hf.secant_mono hx₁ hy₁ hx₂ h₁.symm h₂ (hy.trans hx)
  · calc
      (f y₁ - f x₁) / (y₁ - x₁) ≤ (f y₂ - f x₁) / (y₂ - x₁) :=
        hf.secant_mono hx₁ hy₁ hy₂ h₁.symm (Ne.symm h) hy
      _ = (f x₁ - f y₂) / (x₁ - y₂) := secant_symm f x₁ y₂
      _ ≤ (f x₂ - f y₂) / (x₂ - y₂) :=
        hf.secant_mono hy₂ hx₁ hx₂ h h₂ hx
      _ = (f y₂ - f x₂) / (y₂ - x₂) := secant_symm f y₂ x₂

/-- Secant slopes along two decreasing finite sequences admit a decreasing extension
across indices where the two entries coincide. These coefficients give an exact
factorization of the corresponding differences of convex function values. -/
theorem exists_antitone_secant_coefficients {n : ℕ} {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ s f) (u v : Fin n → ℝ)
    (hu : Antitone u) (hv : Antitone v)
    (hu_mem : ∀ i, u i ∈ s) (hv_mem : ∀ i, v i ∈ s) :
    ∃ c : Fin n → ℝ, Antitone c ∧
      ∀ i, f (u i) - f (v i) = c i * (u i - v i) := by
  let d : Fin n → ℝ := fun i => (f (u i) - f (v i)) / (u i - v i)
  let t : Set (Fin n) := {i | u i ≠ v i}
  have hd : AntitoneOn d t := by
    intro i hi j hj hij
    exact convex_secant_mono hf (hv_mem j) (hv_mem i) (hu_mem j) (hu_mem i)
      hj.symm hi.symm (hv hij) (hu hij)
  have hfinite : (d '' t).Finite := (Set.toFinite t).image d
  obtain ⟨c, hc, heq⟩ := hd.exists_antitone_extension hfinite.bddBelow hfinite.bddAbove
  refine ⟨c, hc, fun i => ?_⟩
  by_cases hi : u i = v i
  · simp [hi]
  · rw [← heq hi]
    exact (div_mul_cancel₀ _ (sub_ne_zero.mpr hi)).symm

end CSeparatedNPComplete
