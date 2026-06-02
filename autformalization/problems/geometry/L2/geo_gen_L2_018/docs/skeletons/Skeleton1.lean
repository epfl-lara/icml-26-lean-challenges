import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace

open Matrix

theorem affineSubspace_image_of_linear_constraints (m n p : ℕ) 
  (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) 
  (F : Matrix (Fin p) (Fin n) ℝ) (g : Fin p → ℝ) :
  let S := {y : Fin m → ℝ | ∃ x : Fin n → ℝ, F.mulVec x = g ∧ y = A.mulVec x + b}
  ∃ (a : Fin m → ℝ) (V : Submodule ℝ (Fin m → ℝ)), 
    S = {a + v | v ∈ V} := by sorry
