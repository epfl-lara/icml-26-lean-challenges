import Mathlib

/-!
# ShadowBench geometry/L2/geo_gen_L2_005

This file formalizes the affine-plane version of Monge's theorem described in
`docs/source.tex`.  The nearby blueprint `ShadowBench/Source/Blueprint.md`
records the source-fidelity comparison and proof-handoff notes.
-/

namespace EuclideanGeometry

/-- The real Euclidean affine plane used for the finite-point case in the source. -/
abbrev Point : Type := EuclideanSpace ℝ (Fin 2)

/-- A circle in the real Euclidean plane.  Radius `0` is allowed. -/
structure Circle where
  center : Point
  radius : ℝ
  radius_nonneg : 0 ≤ radius

namespace Circle

/-- The closed disk bounded by a formal circle. -/
def disk (c : Circle) : Set Point :=
  Metric.closedBall c.center c.radius

/-- `c₁` is not completely inside `c₂`, encoded as non-containment of closed disks. -/
def NotCompletelyInside (c₁ c₂ : Circle) : Prop :=
  ¬ c₁.disk ⊆ c₂.disk

end Circle

/-- No one of the three circles is completely inside another one. -/
def CirclesPairwiseNotCompletelyInside (c₁ c₂ c₃ : Circle) : Prop :=
  Circle.NotCompletelyInside c₁ c₂ ∧
    Circle.NotCompletelyInside c₂ c₁ ∧
    Circle.NotCompletelyInside c₁ c₃ ∧
    Circle.NotCompletelyInside c₃ c₁ ∧
    Circle.NotCompletelyInside c₂ c₃ ∧
    Circle.NotCompletelyInside c₃ c₂

/-- The three radii are pairwise distinct, so the external centers are finite affine points. -/
def RadiiPairwiseDistinct (c₁ c₂ c₃ : Circle) : Prop :=
  c₁.radius ≠ c₂.radius ∧ c₁.radius ≠ c₃.radius ∧ c₂.radius ≠ c₃.radius

end EuclideanGeometry

/--
The external homothetic center of two circles in the affine-plane case.

Source note: the text describes this point as the common finite intersection point of the
two external tangent lines.  For distinct radii this is represented by the standard affine
formula `(r₁ • O₂ - r₂ • O₁) / (r₁ - r₂)`, where `Oᵢ` and `rᵢ` are the centers and radii.
The definition is total in Lean; the theorem below supplies the distinct-radius hypotheses
that exclude the point-at-infinity case.
-/
noncomputable def EuclideanGeometry.external_homothetic_center
    (c₁ c₂ : EuclideanGeometry.Circle) : EuclideanGeometry.Point :=
  (c₁.radius - c₂.radius)⁻¹ • (c₁.radius • c₂.center - c₂.radius • c₁.center)

/--
Source theorem `thm:monge` (`monges_circle_theorem`).

Source proof: no proof is supplied in `docs/source.tex`.
Proof sketch: use the algebraic formula for the three external homothetic centers
`X₁₂ = (r₁ O₂ - r₂ O₁)/(r₁-r₂)`, `X₂₃ = (r₂ O₃ - r₃ O₂)/(r₂-r₃)`, and
`X₁₃ = (r₁ O₃ - r₃ O₁)/(r₁-r₃)`.  A coordinate determinant, or equivalently an
affine-span calculation, shows these three points lie on one line.  The non-containment
hypothesis records the source conditions for external tangent lines; the algebraic
collinearity step should only need the pairwise distinct radii.
-/
theorem EuclideanGeometry.monges_circle_theorem (c₁ c₂ c₃ : EuclideanGeometry.Circle)
    (h_not_inside : EuclideanGeometry.CirclesPairwiseNotCompletelyInside c₁ c₂ c₃)
    (h_distinct_radii : EuclideanGeometry.RadiiPairwiseDistinct c₁ c₂ c₃) :
    Collinear ℝ
      ({ EuclideanGeometry.external_homothetic_center c₁ c₂,
         EuclideanGeometry.external_homothetic_center c₂ c₃,
         EuclideanGeometry.external_homothetic_center c₁ c₃ } : Set EuclideanGeometry.Point) := by
  classical
  have _source_side_conditions := h_not_inside
  rcases h_distinct_radii with ⟨h12, h13, h23⟩
  have hd12 : c₁.radius - c₂.radius ≠ 0 := sub_ne_zero.mpr h12
  have hd13 : c₁.radius - c₃.radius ≠ 0 := sub_ne_zero.mpr h13
  have hd23 : c₂.radius - c₃.radius ≠ 0 := sub_ne_zero.mpr h23
  by_cases h2 : c₂.radius = 0
  · have hr1_ne0 : c₁.radius ≠ 0 := by
      intro h1
      exact h12 (by rw [h1, h2])
    have hr3_ne0 : c₃.radius ≠ 0 := by
      intro h3
      exact h23 (by rw [h2, h3])
    have hx12x23 : EuclideanGeometry.external_homothetic_center c₁ c₂ =
        EuclideanGeometry.external_homothetic_center c₂ c₃ := by
      ext i
      simp [EuclideanGeometry.external_homothetic_center, h2, hr1_ne0, hr3_ne0]
    have hx12_mem : EuclideanGeometry.external_homothetic_center c₁ c₂ ∈
        line[ℝ, EuclideanGeometry.external_homothetic_center c₂ c₃,
          EuclideanGeometry.external_homothetic_center c₁ c₃] := by
      simpa [hx12x23] using
        (left_mem_affineSpan_pair (k := ℝ)
          (EuclideanGeometry.external_homothetic_center c₂ c₃)
          (EuclideanGeometry.external_homothetic_center c₁ c₃))
    exact collinear_triple_of_mem_affineSpan_pair hx12_mem
      (left_mem_affineSpan_pair (k := ℝ)
        (EuclideanGeometry.external_homothetic_center c₂ c₃)
        (EuclideanGeometry.external_homothetic_center c₁ c₃))
      (right_mem_affineSpan_pair (k := ℝ)
        (EuclideanGeometry.external_homothetic_center c₂ c₃)
        (EuclideanGeometry.external_homothetic_center c₁ c₃))
  · let t : ℝ := c₁.radius * (c₂.radius - c₃.radius) /
        (c₂.radius * (c₁.radius - c₃.radius))
    have hx13 : EuclideanGeometry.external_homothetic_center c₁ c₃ =
        AffineMap.lineMap
          (EuclideanGeometry.external_homothetic_center c₁ c₂)
          (EuclideanGeometry.external_homothetic_center c₂ c₃) t := by
      ext i
      simp [EuclideanGeometry.external_homothetic_center, AffineMap.lineMap_apply_module, t]
      field_simp [hd12, hd13, hd23, h2]
      ring
    have hx13_mem : EuclideanGeometry.external_homothetic_center c₁ c₃ ∈
        line[ℝ, EuclideanGeometry.external_homothetic_center c₁ c₂,
          EuclideanGeometry.external_homothetic_center c₂ c₃] := by
      rw [hx13]
      exact AffineMap.lineMap_mem_affineSpan_pair t
        (EuclideanGeometry.external_homothetic_center c₁ c₂)
        (EuclideanGeometry.external_homothetic_center c₂ c₃)
    exact collinear_triple_of_mem_affineSpan_pair
      (left_mem_affineSpan_pair (k := ℝ)
        (EuclideanGeometry.external_homothetic_center c₁ c₂)
        (EuclideanGeometry.external_homothetic_center c₂ c₃))
      (right_mem_affineSpan_pair (k := ℝ)
        (EuclideanGeometry.external_homothetic_center c₁ c₂)
        (EuclideanGeometry.external_homothetic_center c₂ c₃))
      hx13_mem
