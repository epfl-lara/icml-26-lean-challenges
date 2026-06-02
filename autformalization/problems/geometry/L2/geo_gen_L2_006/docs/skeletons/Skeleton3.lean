import Mathlib.Analysis.Normed.Affine.Simplex
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.Geometry.Euclidean.Circumcenter

open Module
open scoped Real RealInnerProductSpace BigOperators

/-- The 2-dimensional Euclidean plane -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Napoleon's Theorem (Inner Version): 
    Given non-collinear points A, B, C in the plane, if equilateral triangles
    are constructed internally on the sides AB, BC, CA, and X, Y, Z are the 
    centroids of these triangles, then triangle XYZ is equilateral. -/
theorem napoleons_theorem_inner (A B C : Plane) 
  (h_noncol : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
  -- Let D be the third vertex of the equilateral triangle constructed
  -- internally on side AB
  ∀ (D : Plane),
  -- Let E be the third vertex of the equilateral triangle constructed
  -- internally on side BC
  ∀ (E : Plane),
  -- Let F be the third vertex of the equilateral triangle constructed
  -- internally on side CA
  ∀ (F : Plane),
  -- Assume ABD is an equilateral triangle constructed internally
  (dist A B = dist B D ∧ dist B D = dist D A) →
  -- Assume BCE is an equilateral triangle constructed internally
  (dist B C = dist C E ∧ dist C E = dist E B) →
  -- Assume CAF is an equilateral triangle constructed internally
  (dist C A = dist A F ∧ dist A F = dist F C) →
  -- Let X, Y, Z be the centroids of triangles ABD, BCE, CAF respectively
  let X := (1/3 : ℝ) • (A + B + D)
  let Y := (1/3 : ℝ) • (B + C + E)
  let Z := (1/3 : ℝ) • (C + A + F)
  -- Then triangle XYZ is equilateral
  dist X Y = dist Y Z ∧ dist Y Z = dist Z X := by sorry

/-- Napoleon's Theorem (Outer Version): 
    Given non-collinear points A, B, C in the plane, if equilateral triangles
    are constructed externally on the sides AB, BC, CA, and X, Y, Z are the 
    centroids of these triangles, then triangle XYZ is equilateral. -/
theorem napoleons_theorem_outer (A B C : Plane) 
  (h_noncol : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
  -- Let D be the third vertex of the equilateral triangle constructed
  -- externally on side AB
  ∀ (D : Plane),
  -- Let E be the third vertex of the equilateral triangle constructed
  -- externally on side BC
  ∀ (E : Plane),
  -- Let F be the third vertex of the equilateral triangle constructed
  -- externally on side CA
  ∀ (F : Plane),
  -- Assume ABD is an equilateral triangle constructed externally
  (dist A B = dist B D ∧ dist B D = dist D A) →
  -- Assume BCE is an equilateral triangle constructed externally
  (dist B C = dist C E ∧ dist C E = dist E B) →
  -- Assume CAF is an equilateral triangle constructed externally
  (dist C A = dist A F ∧ dist A F = dist F C) →
  -- Let X, Y, Z be the centroids of triangles ABD, BCE, CAF respectively
  let X := (1/3 : ℝ) • (A + B + D)
  let Y := (1/3 : ℝ) • (B + C + E)
  let Z := (1/3 : ℝ) • (C + A + F)
  -- Then triangle XYZ is equilateral
  dist X Y = dist Y Z ∧ dist Y Z = dist Z X := by sorry
