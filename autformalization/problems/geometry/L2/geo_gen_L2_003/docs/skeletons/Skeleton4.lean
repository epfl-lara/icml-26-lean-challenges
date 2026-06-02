import Mathlib.Geometry.Euclidean.Projection

open Affine
open EuclideanGeometry

theorem erdos_mordell_inequality {V : Type*} {P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] (A B C P : P)
    (h_noncollinear : ¬ Collinear ℝ {A, B, C})
    (h_inside : ∃ b c : ℝ, b > 0 ∧ c > 0 ∧ b + c < 1 ∧
      P = (b • (B -ᵥ A) + c • (C -ᵥ A)) +ᵥ A) :
    dist P A + dist P B + dist P C ≥ 2 *
      (dist P (orthogonalProjection (affineSpan ℝ ({B, C} : Set P)) P) +
       dist P (orthogonalProjection (affineSpan ℝ ({C, A} : Set P)) P) +
       dist P (orthogonalProjection (affineSpan ℝ ({A, B} : Set P)) P)) := by sorry
