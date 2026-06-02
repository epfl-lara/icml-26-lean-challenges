import Mathlib.Geometry.Euclidean.Projection

open scoped EuclideanGeometry

theorem erdos_mordell_inequality (A B C P : EuclideanSpace ℝ (Fin 2)) 
  (h_inside : -- P is inside triangle ABC
    ∃ (u v w : ℝ), u > 0 ∧ v > 0 ∧ w > 0 ∧ u + v + w = 1 ∧ P = u • A + v • B + w • C) :
  let PL := dist P (projection (affineSpan ℝ {B, C}) P)
  let PM := dist P (projection (affineSpan ℝ {C, A}) P)  
  let PN := dist P (projection (affineSpan ℝ {A, B}) P)
  dist P A + dist P B + dist P C ≥ 2 * (PL + PM + PN) := by sorry
