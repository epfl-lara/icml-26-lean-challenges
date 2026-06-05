import Mathlib

open Real MeasureTheory ProbabilityTheory

/-- Coordinate model for the Buffon needle experiment used in the source proof.
`needleLength` is the length `ℓ`, and `lineSpacing` is the ruled-line spacing `d`. -/
structure BuffonNeedleExperiment where
  needleLength : ℝ
  lineSpacing : ℝ
  needleLength_pos : 0 < needleLength
  needleLength_le_lineSpacing : needleLength ≤ lineSpacing

/-- Build the coordinate Buffon experiment from the source parameters. -/
def buffonNeedleExperiment (ℓ d : ℝ) (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d) :
    BuffonNeedleExperiment :=
  { needleLength := ℓ
    lineSpacing := d
    needleLength_pos := hℓ
    needleLength_le_lineSpacing := hℓd }

namespace BuffonNeedleExperiment

/-- The source proof's uniform sample rectangle `[0,d] × [0,π]`, where the first
coordinate is midpoint height above the lower ruled line and the second is angle. -/
def sampleSpace (E : BuffonNeedleExperiment) : Set (ℝ × ℝ) :=
  Set.Icc (0 : ℝ) E.lineSpacing ×ˢ Set.Icc (0 : ℝ) Real.pi

/-- The coordinate crossing event from the source proof: for angle `θ`, the
midpoint height `y` is within `ℓ sin θ / 2` of one of the two neighboring lines. -/
def crossingEvent (E : BuffonNeedleExperiment) : Set (ℝ × ℝ) :=
  {p | p.1 ≤ E.needleLength * Real.sin p.2 / 2 ∨
    E.lineSpacing - E.needleLength * Real.sin p.2 / 2 ≤ p.1}

/-- The probability of crossing in the source coordinate model, as normalized
Lebesgue area inside the uniform sample rectangle. -/
noncomputable def crossingProbability (E : BuffonNeedleExperiment) : ℝ :=
  (volume (E.sampleSpace ∩ E.crossingEvent)).toReal / (volume E.sampleSpace).toReal

end BuffonNeedleExperiment

/--
Source proof: Model the experiment by the uniform distribution on `[0,d] × [0,π]`,
where `p.1` is the midpoint height above the lower ruled line and `p.2` is the
angle. For fixed `θ`, crossing occurs exactly when
`y ≤ ℓ * sin θ / 2` or `d - ℓ * sin θ / 2 ≤ y`, so the slice length in `y` is
`ℓ * sin θ` and the conditional probability is `ℓ * sin θ / d`. Averaging over
`θ` gives `(1 / π) ∫ θ in 0..π, ℓ * sin θ / d = 2ℓ / (π d)`.

Prover notes: unfold `BuffonNeedleExperiment.crossingProbability`, `sampleSpace`,
and `crossingEvent`; compute the Lebesgue area by Fubini/product measure; use
nonnegativity of `Real.sin` on `[0, Real.pi]`, `∫ sin = 2`, `Real.pi_pos`, and
field simplification.
-/
theorem BuffonNeedle (ℓ d : ℝ) (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d) :
    BuffonNeedleExperiment.crossingProbability (buffonNeedleExperiment ℓ d hℓ hℓd) =
      2 * ℓ / (Real.pi * d) := by
  sorry
