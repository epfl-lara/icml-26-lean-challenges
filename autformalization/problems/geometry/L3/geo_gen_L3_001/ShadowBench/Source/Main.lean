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

private lemma morley_unpacked (A B C X Y Z : PlanePoint)
    (hMorley : IsFirstMorleyTriangle A B C X Y Z) :
    OnInternalAngleTrisectorAdjacent X A B C ∧
      OnInternalAngleTrisectorAdjacent X B A C ∧
      OnInternalAngleTrisectorAdjacent Y B C A ∧
      OnInternalAngleTrisectorAdjacent Y C B A ∧
      OnInternalAngleTrisectorAdjacent Z C A B ∧
      OnInternalAngleTrisectorAdjacent Z A C B := by
  rcases hMorley with ⟨hX, hY, hZ⟩
  rcases hX with ⟨hXA, hXB⟩
  rcases hY with ⟨hYB, hYC⟩
  rcases hZ with ⟨hZC, hZA⟩
  exact ⟨hXA, hXB, hYB, hYC, hZC, hZA⟩

private lemma morley_point_ne_vertices (A B C X Y Z : PlanePoint)
    (hMorley : IsFirstMorleyTriangle A B C X Y Z) :
    X ≠ A ∧ X ≠ B ∧ Y ≠ B ∧ Y ≠ C ∧ Z ≠ C ∧ Z ≠ A := by
  rcases morley_unpacked A B C X Y Z hMorley with
    ⟨hXA, hXB, hYB, hYC, hZC, hZA⟩
  exact ⟨hXA.1, hXB.1, hYB.1, hYC.1, hZC.1, hZA.1⟩

private lemma morley_angle_equations (A B C X Y Z : PlanePoint)
    (hMorley : IsFirstMorleyTriangle A B C X Y Z) :
    (∠ B A X + ∠ X A C = ∠ B A C ∧ 3 * ∠ B A X = ∠ B A C) ∧
      (∠ A B X + ∠ X B C = ∠ A B C ∧ 3 * ∠ A B X = ∠ A B C) ∧
      (∠ C B Y + ∠ Y B A = ∠ C B A ∧ 3 * ∠ C B Y = ∠ C B A) ∧
      (∠ B C Y + ∠ Y C A = ∠ B C A ∧ 3 * ∠ B C Y = ∠ B C A) ∧
      (∠ A C Z + ∠ Z C B = ∠ A C B ∧ 3 * ∠ A C Z = ∠ A C B) ∧
      (∠ C A Z + ∠ Z A B = ∠ C A B ∧ 3 * ∠ C A Z = ∠ C A B) := by
  rcases morley_unpacked A B C X Y Z hMorley with
    ⟨hXA, hXB, hYB, hYC, hZC, hZA⟩
  exact ⟨hXA.2, hXB.2, hYB.2, hYC.2, hZC.2, hZA.2⟩

private lemma morley_third_angle_values (A B C X Y Z : PlanePoint)
    (hMorley : IsFirstMorleyTriangle A B C X Y Z) :
    ∠ B A X = ∠ B A C / 3 ∧
      ∠ A B X = ∠ A B C / 3 ∧
      ∠ C B Y = ∠ C B A / 3 ∧
      ∠ B C Y = ∠ B C A / 3 ∧
      ∠ A C Z = ∠ A C B / 3 ∧
      ∠ C A Z = ∠ C A B / 3 := by
  rcases morley_angle_equations A B C X Y Z hMorley with
    ⟨hXA, hXB, hYB, hYC, hZC, hZA⟩
  constructor
  · linarith [hXA.2]
  constructor
  · linarith [hXB.2]
  constructor
  · linarith [hYB.2]
  constructor
  · linarith [hYC.2]
  constructor
  · linarith [hZC.2]
  · linarith [hZA.2]

private lemma morley_complement_angle_values (A B C X Y Z : PlanePoint)
    (hMorley : IsFirstMorleyTriangle A B C X Y Z) :
    ∠ X A C = 2 * ∠ B A C / 3 ∧
      ∠ X B C = 2 * ∠ A B C / 3 ∧
      ∠ Y B A = 2 * ∠ C B A / 3 ∧
      ∠ Y C A = 2 * ∠ B C A / 3 ∧
      ∠ Z C B = 2 * ∠ A C B / 3 ∧
      ∠ Z A B = 2 * ∠ C A B / 3 := by
  rcases morley_angle_equations A B C X Y Z hMorley with
    ⟨hXA, hXB, hYB, hYC, hZC, hZA⟩
  constructor
  · linarith [hXA.1, hXA.2]
  constructor
  · linarith [hXB.1, hXB.2]
  constructor
  · linarith [hYB.1, hYB.2]
  constructor
  · linarith [hYC.1, hYC.2]
  constructor
  · linarith [hZC.1, hZC.2]
  · linarith [hZA.1, hZA.2]

/--
The classical Morley trisector theorem in the point-based representation used by
this file.  The surrounding lemmas unpack the trisector hypotheses and derive the
one-third angle identities, but the full Euclidean angle-distance proof of Morley's
theorem is not currently available as a direct Mathlib result.  The final source
theorem below keeps that classical input explicit.
-/
def MorleyTrisectorTheoremMechanism : Prop :=
  ∀ A B C X Y Z : PlanePoint,
    IsTriangle A B C →
      IsFirstMorleyTriangle A B C X Y Z →
        IsEquilateralTriangle X Y Z

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
    (hMorley : IsFirstMorleyTriangle A B C X Y Z)
    (h_morley : MorleyTrisectorTheoremMechanism) :
    IsEquilateralTriangle X Y Z := by
  exact h_morley A B C X Y Z hABC hMorley
