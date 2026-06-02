import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Real.CompleteField

open Set

theorem exists_affine_between_of_concaveOn_le_convexOn {n : ℕ}
    (f g : (Fin n → ℝ) → ℝ)
    (hf : ConvexOn ℝ univ f)
    (hg : ConcaveOn ℝ univ g)
    (hfg : ∀ x, g x ≤ f x) :
    ∃ l : (Fin n → ℝ) →L[ℝ] ℝ, ∃ b : ℝ,
      ∀ x, g x ≤ l x + b ∧ l x + b ≤ f x := by sorry
