import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Real.Sqrt

/-!
ShadowBench problem: `geometry/L2/geo_gen_L2_004` (Casey's theorem).
Source: `docs/source.tex`; Blueprint: `ShadowBench/Source/Blueprint.md`.

All declarations for this problem are consolidated into this single file (Main.lean):
the analytic-plane basics, the configuration constructions, and the two source
theorems. Required declaration names: `EuclideanGeometry.external_tangent_length`,
`EuclideanGeometry.circlePoint`, `EuclideanGeometry.caseys_theorem`.
-/

/-!
Basic analytic-plane definitions for the Casey theorem formalization.
-/

namespace EuclideanGeometry

/-- Analytic points in the real Euclidean plane used for this source formalization. -/
abbrev Point : Type := ℝ × ℝ

/-- Squared Euclidean distance in the analytic plane. -/
def sqDist (p q : Point) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/--
The point set of the circle with the given center and radius, represented in the
analytic plane by the squared-distance equation.
-/
def circlePoint (center : Point) (radius : ℝ) : Set Point :=
  {p | sqDist p center = radius ^ 2}

/--
The length of the exterior common bitangent segment of two circles in the analytic
center/radius model.
-/
noncomputable def external_tangent_length (c₁ c₂ : Point) (r₁ r₂ : ℝ) : ℝ :=
  Real.sqrt (sqDist c₁ c₂ - (r₁ - r₂) ^ 2)

/-- Ordinary analytic distance between two points, used for the degenerate Ptolemy bridge. -/
noncomputable def pointDistance (p q : Point) : ℝ :=
  Real.sqrt (sqDist p q)

/-- Ptolemy's equality for four points in the analytic plane. -/
noncomputable def ptolemyEquality (p₁ p₂ p₃ p₄ : Point) : Prop :=
  let d₁₂ := pointDistance p₁ p₂
  let d₁₃ := pointDistance p₁ p₃
  let d₁₄ := pointDistance p₁ p₄
  let d₂₃ := pointDistance p₂ p₃
  let d₂₄ := pointDistance p₂ p₄
  let d₃₄ := pointDistance p₃ p₄
  d₁₂ * d₃₄ + d₁₄ * d₂₃ = d₁₃ * d₂₄

/-- Signed area/orientation determinant for three analytic points. -/
def orientation (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Strict cyclic order of four points, allowing either orientation. -/
def strictlyCyclicallyOrdered (p₁ p₂ p₃ p₄ : Point) : Prop :=
  (0 < orientation p₁ p₂ p₃ ∧
    0 < orientation p₂ p₃ p₄ ∧
    0 < orientation p₃ p₄ p₁ ∧
    0 < orientation p₄ p₁ p₂) ∨
  (orientation p₁ p₂ p₃ < 0 ∧
    orientation p₂ p₃ p₄ < 0 ∧
    orientation p₃ p₄ p₁ < 0 ∧
    orientation p₄ p₁ p₂ < 0)

end EuclideanGeometry

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

/-!
Source-backed theorem statements for the Casey theorem formalization.
-/

/--
Source theorem `thm:casey` (`caseys_theorem`).
Let `O` be a circle of radius `R`.  Let `O₁, O₂, O₃, O₄` be, in that order, four
nonintersecting circles lying inside `O` and tangent to it.  If `tᵢⱼ` denotes the
length of the exterior common bitangent of `Oᵢ` and `Oⱼ`, then
`t₁₂ * t₃₄ + t₁₄ * t₂₃ = t₁₃ * t₂₄`.

Source proof: no proof is included in `docs/source.tex`.
Proof sketch / prover notes: take the radial contact points of the four inner circles
with the outer circle.  These contact points are cyclically ordered on the outer circle,
so Ptolemy applies to their chord lengths.  For an inner circle with
`aᵢ = R - rᵢ`, the exterior tangent length between `Oᵢ` and `Oⱼ` is the corresponding
chord length multiplied by `sqrt (aᵢ * aⱼ) / R`; the same product factor appears in
every term, yielding Casey's equality.  When all `rᵢ = 0`, the tangent-length formula
reduces to ordinary chord length, giving the Ptolemy theorem noted in the source.
-/
theorem EuclideanGeometry.caseys_theorem
    (O : EuclideanGeometry.Point) (R : ℝ)
    (O₁ O₂ O₃ O₄ : EuclideanGeometry.Point) (r₁ r₂ r₃ r₄ : ℝ)
    (hR : 0 < R)
    (h₁ : EuclideanGeometry.liesInsideAndTangentTo O₁ O r₁ R)
    (h₂ : EuclideanGeometry.liesInsideAndTangentTo O₂ O r₂ R)
    (h₃ : EuclideanGeometry.liesInsideAndTangentTo O₃ O r₃ R)
    (h₄ : EuclideanGeometry.liesInsideAndTangentTo O₄ O r₄ R)
    (hNonintersecting : EuclideanGeometry.fourCirclesNonintersecting O₁ O₂ O₃ O₄ r₁ r₂ r₃ r₄)
    (hOrder : EuclideanGeometry.caseyInOrder O R O₁ O₂ O₃ O₄ r₁ r₂ r₃ r₄) :
    let t₁₂ := EuclideanGeometry.external_tangent_length O₁ O₂ r₁ r₂
    let t₁₃ := EuclideanGeometry.external_tangent_length O₁ O₃ r₁ r₃
    let t₁₄ := EuclideanGeometry.external_tangent_length O₁ O₄ r₁ r₄
    let t₂₃ := EuclideanGeometry.external_tangent_length O₂ O₃ r₂ r₃
    let t₂₄ := EuclideanGeometry.external_tangent_length O₂ O₄ r₂ r₄
    let t₃₄ := EuclideanGeometry.external_tangent_length O₃ O₄ r₃ r₄
    t₁₂ * t₃₄ + t₁₄ * t₂₃ = t₁₃ * t₂₄ := by
  sorry

/--
Source follow-on claim in `thm:casey`: in the degenerate zero-radius case, the
Casey equality is exactly Ptolemy's equality for the four resulting points.

Source proof: no proof is included in `docs/source.tex`.
Proof sketch / prover notes: unfold `external_tangent_length`, `pointDistance`, and
`ptolemyEquality`; with all radii equal to zero, each bitangent length becomes the
ordinary point distance `sqrt (sqDist Pᵢ Pⱼ)`.
-/
theorem EuclideanGeometry.caseys_theorem_degenerate_ptolemy_bridge
    (P₁ P₂ P₃ P₄ : EuclideanGeometry.Point) :
    (let t₁₂ := EuclideanGeometry.external_tangent_length P₁ P₂ 0 0
     let t₁₃ := EuclideanGeometry.external_tangent_length P₁ P₃ 0 0
     let t₁₄ := EuclideanGeometry.external_tangent_length P₁ P₄ 0 0
     let t₂₃ := EuclideanGeometry.external_tangent_length P₂ P₃ 0 0
     let t₂₄ := EuclideanGeometry.external_tangent_length P₂ P₄ 0 0
     let t₃₄ := EuclideanGeometry.external_tangent_length P₃ P₄ 0 0
     t₁₂ * t₃₄ + t₁₄ * t₂₃ = t₁₃ * t₂₄) ↔
      EuclideanGeometry.ptolemyEquality P₁ P₂ P₃ P₄ := by
  sorry
