import ShadowBench.Source.Constructions

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
