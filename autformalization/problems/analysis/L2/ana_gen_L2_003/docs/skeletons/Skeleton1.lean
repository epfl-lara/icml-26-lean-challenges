import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic

theorem saddle_sections_hasFDerivAt_eq_zero 
  {n m : ℕ} 
  (f : (EuclideanSpace ℝ (Fin n)) × (EuclideanSpace ℝ (Fin m)) → ℝ) 
  (x̃ : EuclideanSpace ℝ (Fin n)) 
  (z̃ : EuclideanSpace ℝ (Fin m))
  (h_saddle : ∀ x z, f (x, z̃) ≤ f (x̃, z̃) ∧ f (x̃, z̃) ≤ f (x, z̃))
  (h_diff_x : DifferentiableAt ℝ (fun x => f (x, z̃)) x̃)
  (h_diff_z : DifferentiableAt ℝ (fun z => f (x̃, z)) z̃) :
  fderiv ℝ f (x̃, z̃) = 0 := by sorry
