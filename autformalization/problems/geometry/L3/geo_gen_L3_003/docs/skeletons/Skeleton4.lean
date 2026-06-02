import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Convex.Cone.Dual

open Matrix PointedCone

theorem dual_cone_matrix_image_nonneg (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
  let K := {y : Fin m → ℝ | ∃ x : Fin n → ℝ, (∀ i, 0 ≤ x i) ∧ y = A.mulVec x}
  let K_dual := {y : Fin m → ℝ | ∀ z ∈ K, 0 ≤ ∑ i, y i * z i}
  K_dual = {y : Fin m → ℝ | ∀ i, 0 ≤ (A.transpose.mulVec y) i} := by sorry
:= by sorry
