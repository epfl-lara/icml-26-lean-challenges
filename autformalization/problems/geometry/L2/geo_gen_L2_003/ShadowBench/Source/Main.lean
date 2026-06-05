import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Analysis.InnerProductSpace.PiL2

open Affine
open EuclideanGeometry
open scoped EuclideanGeometry

/--
Source theorem `thm:erdos_mordell` from `docs/source.tex`, lines 17--23.
Source proof: none is supplied in the source document.
Proof sketch / prover notes: `PL`, `PM`, and `PN` are represented as the distances from `P`
to the orthogonal projections of `P` onto the affine side lines `BC`, `CA`, and `AB`.
Use the classical Erdős--Mordell argument: derive the three vertex/side distance estimates
for these orthogonal projections and sum them to obtain the displayed factor `2`.
-/
theorem erdos_mordell_inequality
    (A B C P : EuclideanSpace ℝ (Fin 2))
    (h_triangle : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (h_inside : ∃ u v w : ℝ,
      0 < u ∧ 0 < v ∧ 0 < w ∧ u + v + w = 1 ∧
        P = u • A + v • B + w • C) :
    let PL :=
      dist P
        (orthogonalProjection
          (affineSpan ℝ ({B, C} : Set (EuclideanSpace ℝ (Fin 2)))) P)
    let PM :=
      dist P
        (orthogonalProjection
          (affineSpan ℝ ({C, A} : Set (EuclideanSpace ℝ (Fin 2)))) P)
    let PN :=
      dist P
        (orthogonalProjection
          (affineSpan ℝ ({A, B} : Set (EuclideanSpace ℝ (Fin 2)))) P)
    dist P A + dist P B + dist P C ≥ 2 * (PL + PM + PN) := by
  sorry
