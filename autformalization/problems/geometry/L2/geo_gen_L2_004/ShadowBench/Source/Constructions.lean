import ShadowBench.Source.Basic

/-!
Configuration predicates and constructions for the Casey theorem formalization.
-/

namespace EuclideanGeometry

/--
For an inner circle tangent internally to an outer circle, this is the radial contact
point on the outer circle determined by the two centers and radii.
-/
noncomputable def radialContactPoint (outerCenter : Point) (outerRadius : ℝ)
    (innerCenter : Point) (innerRadius : ℝ) : Point :=
  let scale := outerRadius / (outerRadius - innerRadius)
  (outerCenter.1 + scale * (innerCenter.1 - outerCenter.1),
    outerCenter.2 + scale * (innerCenter.2 - outerCenter.2))

/--
The source phrase that the four inner circles are “in that order”, encoded as strict
cyclic order of their radial contact points on the outer circle.
-/
noncomputable def caseyInOrder (outerCenter : Point) (outerRadius : ℝ)
    (c₁ c₂ c₃ c₄ : Point) (r₁ r₂ r₃ r₄ : ℝ) : Prop :=
  strictlyCyclicallyOrdered
    (radialContactPoint outerCenter outerRadius c₁ r₁)
    (radialContactPoint outerCenter outerRadius c₂ r₂)
    (radialContactPoint outerCenter outerRadius c₃ r₃)
    (radialContactPoint outerCenter outerRadius c₄ r₄)

/--
An inner circle lies inside and is tangent to an outer circle: nonnegative inner radius,
strictly smaller than the outer radius, and center distance equal to `outerRadius - innerRadius`.
The zero-radius case covers the source's degenerate point-circle note.
-/
def liesInsideAndTangentTo (innerCenter outerCenter : Point)
    (innerRadius outerRadius : ℝ) : Prop :=
  0 ≤ innerRadius ∧ innerRadius < outerRadius ∧
    sqDist innerCenter outerCenter = (outerRadius - innerRadius) ^ 2

/-- Strict pairwise nonintersection of two circular disks in the center/radius model. -/
def nonintersectingCircles (c₁ c₂ : Point) (r₁ r₂ : ℝ) : Prop :=
  0 ≤ r₁ ∧ 0 ≤ r₂ ∧ (r₁ + r₂) ^ 2 < sqDist c₁ c₂

/-- The six pairwise nonintersection conditions for four circles. -/
def fourCirclesNonintersecting (c₁ c₂ c₃ c₄ : Point) (r₁ r₂ r₃ r₄ : ℝ) : Prop :=
  nonintersectingCircles c₁ c₂ r₁ r₂ ∧
    nonintersectingCircles c₁ c₃ r₁ r₃ ∧
    nonintersectingCircles c₁ c₄ r₁ r₄ ∧
    nonintersectingCircles c₂ c₃ r₂ r₃ ∧
    nonintersectingCircles c₂ c₄ r₂ r₄ ∧
    nonintersectingCircles c₃ c₄ r₃ r₄

end EuclideanGeometry
