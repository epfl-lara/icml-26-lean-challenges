import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Real.CompleteField

open Set

theorem exists_affine_between_of_concaveOn_le_convexOn {n : ℕ} 
  (f g : (Fin n → ℝ) → ℝ) 
  (hf : ConvexOn ℝ Set.univ f) 
  (hg : ConcaveOn ℝ Set.univ g) 
  (hfg : ∀ x, g x ≤ f x) :
  ∃ (a : Fin n → ℝ) (b : ℝ), 
    let h : (Fin n → ℝ) → ℝ := fun x => ∑ i, a i * x i + b
    ∀ x, g x ≤ h x ∧ h x ≤ f x := by sorry
