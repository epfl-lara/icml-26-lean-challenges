import Mathlib.Analysis.Normed.Affine.Simplex
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine

open Module

/-- A predicate that checks if three points form a triangle (non-collinear) -/
def IsTriangle (A B C : EuclideanSpace ℝ (Fin 2)) : Prop :=
  ¬Collinear ℝ {A, B, C}

/-- A predicate that checks if three points form an equilateral triangle -/
def IsEquilateral (X Y Z : EuclideanSpace ℝ (Fin 2)) : Prop :=
  dist X Y = dist Y Z ∧ dist Y Z = dist Z X

/-- Given a triangle ABC, this function computes the point X which is the intersection
    of the adjacent angle trisectors at vertices A and B -/
def IntersectionOfTrisectorsAtAAndB (A B C : EuclideanSpace ℝ (Fin 2)) : 
  EuclideanSpace ℝ (Fin 2) := sorry

/-- Given a triangle ABC, this function computes the point Y which is the intersection
    of the adjacent angle trisectors at vertices B and C -/
def IntersectionOfTrisectorsAtBAndC (A B C : EuclideanSpace ℝ (Fin 2)) : 
  EuclideanSpace ℝ (Fin 2) := sorry

/-- Given a triangle ABC, this function computes the point Z which is the intersection
    of the adjacent angle trisectors at vertices C and A -/
def IntersectionOfTrisectorsAtCAndA (A B C : EuclideanSpace ℝ (Fin 2)) : 
  EuclideanSpace ℝ (Fin 2) := sorry

/-- 
Formalizes the statement of Morley's trisector theorem.
In any triangle, the three points of intersection of the adjacent angle trisectors
form an equilateral triangle.
-/
theorem morleys_trisector_theorem (A B C : EuclideanSpace ℝ (Fin 2))
  (h_triangle : IsTriangle A B C) :
  let X := IntersectionOfTrisectorsAtAAndB A B C
  let Y := IntersectionOfTrisectorsAtBAndC A B C
  let Z := IntersectionOfTrisectorsAtCAndA A B C
  IsEquilateral X Y Z := by sorry
