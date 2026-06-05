import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Real.Sqrt

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
