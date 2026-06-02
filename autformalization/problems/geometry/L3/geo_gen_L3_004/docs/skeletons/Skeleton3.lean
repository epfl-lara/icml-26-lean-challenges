import Mathlib

open scoped Manifold ContDiff

theorem smoothVectorField_infinite_dimensional (M : Type*) [Manifold ℝ M] [Nonempty M] 
  (h_pos : ∃ p : M, 0 < FiniteDimensional.finrank ℝ (TangentSpace ℝ M p)) :
  ¬FiniteDimensional ℝ (SmoothSections (T M)) := by sorry
