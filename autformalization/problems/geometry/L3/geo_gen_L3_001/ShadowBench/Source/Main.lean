import Mathlib.Analysis.Normed.Affine.Simplex
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine

open Module
open scoped EuclideanGeometry

/-- The Euclidean plane used for the source theorem. -/
abbrev PlanePoint := EuclideanSpace ℝ (Fin 2)

/-- A nondegenerate triangle, represented as three non-collinear points. -/
def IsTriangle (A B C : PlanePoint) : Prop :=
  ¬ Collinear ℝ ({A, B, C} : Set PlanePoint)

/-- A point-based equilateral triangle: non-collinear vertices and equal side lengths. -/
def IsEquilateralTriangle (X Y Z : PlanePoint) : Prop :=
  IsTriangle X Y Z ∧ dist X Y = dist Y Z ∧ dist Y Z = dist Z X

/--
`P` lies on the internal trisector at vertex `V` adjacent to the side/ray `VS`
inside the angle `SVT`. The first equation records that the ray `VP` is inside
the angle; the second records that it cuts off one third of the angle from the
side `VS`.
-/
def OnInternalAngleTrisectorAdjacent (P V S T : PlanePoint) : Prop :=
  P ≠ V ∧ ∠ S V P + ∠ P V T = ∠ S V T ∧ 3 * ∠ S V P = ∠ S V T

/--
`P` is the adjacent-trisector intersection associated to side `UV` of triangle
`UVW`: it lies on the trisector at `U` adjacent to `UV` and on the trisector at
`V` adjacent to `VU`.
-/
def IsAdjacentTrisectorIntersection (P U V W : PlanePoint) : Prop :=
  OnInternalAngleTrisectorAdjacent P U V W ∧ OnInternalAngleTrisectorAdjacent P V U W

/--
`X`, `Y`, and `Z` are the three adjacent internal trisector intersections of
triangle `ABC`, with `X` on side `AB`, `Y` on side `BC`, and `Z` on side `CA`.
-/
def IsFirstMorleyTriangle (A B C X Y Z : PlanePoint) : Prop :=
  IsAdjacentTrisectorIntersection X A B C ∧
    IsAdjacentTrisectorIntersection Y B C A ∧
      IsAdjacentTrisectorIntersection Z C A B

/--
Source proof: `docs/source.tex`, theorem `morleys_trisector_theorem`
(label `thm:morley_trisector`), gives only the statement and no proof block.
It says that in any triangle, the three intersections of adjacent internal
angle trisectors form the first Morley triangle, and that this triangle is
equilateral.

Proof sketch / prover notes: `hMorley` expands to the three adjacent internal
trisector intersection hypotheses. A classical Morley proof shows that these
trisectors split the angles of `ABC` into thirds; the small triangles around
`XYZ` then have matching angle data, giving `dist X Y = dist Y Z = dist Z X`
and non-collinearity of `X,Y,Z`. Start by unfolding
`IsFirstMorleyTriangle`, `IsAdjacentTrisectorIntersection`,
`OnInternalAngleTrisectorAdjacent`, and `IsEquilateralTriangle`; likely useful
facts are `EuclideanGeometry.angle` lemmas, triangle angle-sum facts, and
Euclidean distance/angle lemmas.
-/
theorem morleys_trisector_theorem (A B C X Y Z : PlanePoint)
    (hABC : IsTriangle A B C)
    (hMorley : IsFirstMorleyTriangle A B C X Y Z) :
    IsEquilateralTriangle X Y Z := by
  sorry
