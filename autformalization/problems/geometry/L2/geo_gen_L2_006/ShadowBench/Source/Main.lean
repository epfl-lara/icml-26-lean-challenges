import Mathlib.Analysis.Normed.Affine.Simplex
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.Geometry.Euclidean.Circumcenter

open Module
open scoped Real RealInnerProductSpace BigOperators

/-- The two-dimensional Euclidean plane used by the source statement. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Twice the signed area/orientation determinant of the ordered triangle `P Q R`. -/
noncomputable def twiceSignedArea (P Q R : Plane) : ℝ :=
  (Q 0 - P 0) * (R 1 - P 1) - (Q 1 - P 1) * (R 0 - P 0)

/-- `R` and `S` lie on the same open side of the oriented line through `P` and `Q`. -/
def SameSide (P Q R S : Plane) : Prop :=
  0 < twiceSignedArea P Q R * twiceSignedArea P Q S

/-- `R` and `S` lie on opposite open sides of the oriented line through `P` and `Q`. -/
def OppositeSide (P Q R S : Plane) : Prop :=
  twiceSignedArea P Q R * twiceSignedArea P Q S < 0

/-- A metric predicate for an equilateral triangle. -/
def EquilateralTriangle (P Q R : Plane) : Prop :=
  dist P Q = dist Q R ∧ dist Q R = dist R P

/-- Centroid of three points, written in vector coordinates for `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def TriangleCentroid (P Q R : Plane) : Plane :=
  (1 / 3 : ℝ) • (P + Q + R)

/-- Configuration for the three internally constructed equilateral triangles in
Napoleon's theorem. -/
def InternalNapoleonConfiguration (A B C D E F : Plane) : Prop :=
  EquilateralTriangle A B D ∧
    EquilateralTriangle B C E ∧
    EquilateralTriangle C A F ∧
    SameSide A B D C ∧
    SameSide B C E A ∧
    SameSide C A F B

/-- Configuration for the three externally constructed equilateral triangles in
Napoleon's theorem. -/
def ExternalNapoleonConfiguration (A B C D E F : Plane) : Prop :=
  EquilateralTriangle A B D ∧
    EquilateralTriangle B C E ∧
    EquilateralTriangle C A F ∧
    OppositeSide A B D C ∧
    OppositeSide B C E A ∧
    OppositeSide C A F B

/--
Source theorem `thm:napoleon_inner` (`napoleons_theorem_inner`): for non-collinear
points `A B C`, build equilateral triangles on `AB`, `BC`, and `CA` internally;
their centroids form an equilateral triangle.

Proof sketch / prover notes: The source gives no proof. Use coordinates or the
standard complex-plane proof of Napoleon's theorem. The predicates above encode
"internal" by requiring the third vertices `D E F` to lie on the same open side
of the relevant side as the opposite vertex of `ABC`. With this common
orientation, express the third vertices by rotation through `± π / 3`, expand the
three centroid differences, and use that rotation by sixty degrees is an isometry
to prove the three resulting distances equal.
-/
theorem napoleons_theorem_inner (A B C : Plane)
    (h_noncol : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    ∀ D E F : Plane,
      InternalNapoleonConfiguration A B C D E F →
        EquilateralTriangle (TriangleCentroid A B D)
          (TriangleCentroid B C E)
          (TriangleCentroid C A F) := by
  sorry

/--
Source theorem `thm:napoleon_outer` (`napoleons_theorem_outer`): for non-collinear
points `A B C`, build equilateral triangles on `AB`, `BC`, and `CA` externally;
their centroids form an equilateral triangle.

Proof sketch / prover notes: The source gives no proof. This is the same
coordinate/rotation argument as the internal theorem, with the opposite common
orientation. The predicates above encode "external" by putting each third vertex
on the opposite open side of the corresponding side from the remaining vertex of
`ABC`. After translating to rotations by the other sign of `π / 3`, the
centroid-difference identities are the same up to sign/rotation, so the three
distances are equal.
-/
theorem napoleons_theorem_outer (A B C : Plane)
    (h_noncol : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    ∀ D E F : Plane,
      ExternalNapoleonConfiguration A B C D E F →
        EquilateralTriangle (TriangleCentroid A B D)
          (TriangleCentroid B C E)
          (TriangleCentroid C A F) := by
  sorry
