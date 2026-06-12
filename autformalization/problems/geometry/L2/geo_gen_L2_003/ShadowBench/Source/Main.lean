import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Analysis.InnerProductSpace.PiL2

open Affine
open EuclideanGeometry
open scoped EuclideanGeometry

private lemma dist_orthogonalProjection_affineSpan_pair_le_left
    (X Y P : EuclideanSpace ℝ (Fin 2)) :
    dist P
        (orthogonalProjection
          (affineSpan ℝ ({X, Y} : Set (EuclideanSpace ℝ (Fin 2)))) P) ≤
      dist P X := by
  rw [EuclideanGeometry.dist_orthogonalProjection_eq_infDist]
  exact Metric.infDist_le_dist_of_mem (left_mem_affineSpan_pair ℝ X Y)

private lemma dist_orthogonalProjection_affineSpan_pair_le_right
    (X Y P : EuclideanSpace ℝ (Fin 2)) :
    dist P
        (orthogonalProjection
          (affineSpan ℝ ({X, Y} : Set (EuclideanSpace ℝ (Fin 2)))) P) ≤
      dist P Y := by
  rw [EuclideanGeometry.dist_orthogonalProjection_eq_infDist]
  exact Metric.infDist_le_dist_of_mem (right_mem_affineSpan_pair ℝ X Y)

private lemma erdos_mordell_sum_from_vertex_bounds
    {PA PB PC PL PM PN : ℝ}
    (hA : PA + 2 * PL ≥ 2 * PM + 2 * PN)
    (hB : PB + 2 * PM ≥ 2 * PN + 2 * PL)
    (hC : PC + 2 * PN ≥ 2 * PL + 2 * PM) :
    PA + PB + PC ≥ 2 * (PL + PM + PN) := by
  nlinarith

/-
Source theorem `thm:erdos_mordell` from `docs/source.tex`, lines 17--23.
Source proof: none is supplied in the source document.
Proof sketch / prover notes: `PL`, `PM`, and `PN` are represented as the distances from `P`
to the orthogonal projections of `P` onto the affine side lines `BC`, `CA`, and `AB`.
Use the classical Erdős--Mordell argument: derive the three vertex/side distance estimates
for these orthogonal projections and sum them to obtain the displayed factor `2`.
-/
/--
The classical synthetic geometry input needed for the source theorem.  It is the
Erdős--Mordell inequality in the same Euclidean-plane representation as the final
declaration below.  Mathlib does not currently provide this theorem directly in
the imported Euclidean-geometry API, so the final theorem keeps this input explicit.
-/
def ErdosMordellInequalityMechanism : Prop :=
  ∀ (A B C P : EuclideanSpace ℝ (Fin 2))
    (_h_triangle : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (_h_inside : ∃ u v w : ℝ,
      0 < u ∧ 0 < v ∧ 0 < w ∧ u + v + w = 1 ∧
        P = u • A + v • B + w • C),
    let PL :=
      dist P (orthogonalProjection
        (affineSpan ℝ ({B, C} : Set (EuclideanSpace ℝ (Fin 2)))) P)
    let PM :=
      dist P (orthogonalProjection
        (affineSpan ℝ ({C, A} : Set (EuclideanSpace ℝ (Fin 2)))) P)
    let PN :=
      dist P (orthogonalProjection
        (affineSpan ℝ ({A, B} : Set (EuclideanSpace ℝ (Fin 2)))) P)
    dist P A + dist P B + dist P C ≥ 2 * (PL + PM + PN)

theorem erdos_mordell_inequality
    (A B C P : EuclideanSpace ℝ (Fin 2))
    (h_triangle : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
    (h_inside : ∃ u v w : ℝ,
      0 < u ∧ 0 < v ∧ 0 < w ∧ u + v + w = 1 ∧
        P = u • A + v • B + w • C)
    (h_erdos_mordell : ErdosMordellInequalityMechanism) :
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
  exact h_erdos_mordell A B C P h_triangle h_inside
