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

private def buffonNeedleCentral (ℓ d : ℝ) : Set (ℝ × ℝ) :=
  Prod.swap ⁻¹' regionBetween
    (fun θ : ℝ => (ℓ / 2) * Real.sin θ)
    (fun θ : ℝ => d - (ℓ / 2) * Real.sin θ)
    (Set.Icc (0 : ℝ) Real.pi)

private lemma buffonNeedle_strip_bounds (ℓ d : ℝ) (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d) :
    ∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      (ℓ / 2) * Real.sin θ ≤ d - (ℓ / 2) * Real.sin θ := by
  intro θ hθ
  have hsin_le_one : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hmul : ℓ * Real.sin θ ≤ d := by
    exact le_trans (mul_le_of_le_one_right hℓ.le hsin_le_one) hℓd
  nlinarith

private lemma buffonNeedle_integral_width_Icc (ℓ d : ℝ) :
    ∫ θ in Set.Icc (0 : ℝ) Real.pi, (d - ℓ * Real.sin θ) = d * Real.pi - 2 * ℓ := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le Real.pi_pos.le]
  rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_const
      ((Real.continuous_sin.const_mul ℓ).intervalIntegrable 0 Real.pi)]
  rw [intervalIntegral.integral_const]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_sin]
  norm_num [Real.cos_zero, Real.cos_pi]
  ring_nf

private lemma buffonNeedle_centralStrip_prod_volume (ℓ d : ℝ) (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d) :
    (volume.prod volume) (regionBetween
        (fun θ : ℝ => (ℓ / 2) * Real.sin θ)
        (fun θ : ℝ => d - (ℓ / 2) * Real.sin θ)
        (Set.Icc (0 : ℝ) Real.pi)) = ENNReal.ofReal (d * Real.pi - 2 * ℓ) := by
  have hfcont : Continuous fun θ : ℝ => (ℓ / 2) * Real.sin θ :=
    Real.continuous_sin.const_mul (ℓ / 2)
  have hgcont : Continuous fun θ : ℝ => d - (ℓ / 2) * Real.sin θ :=
    continuous_const.sub hfcont
  rw [volume_regionBetween_eq_integral hfcont.integrableOn_Icc hgcont.integrableOn_Icc
      measurableSet_Icc (buffonNeedle_strip_bounds ℓ d hℓ hℓd)]
  congr 1
  rw [← buffonNeedle_integral_width_Icc ℓ d]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro θ hθ
  simp [Pi.sub_apply]
  ring

private lemma buffonNeedleCentral_measurableSet (ℓ d : ℝ) :
    MeasurableSet (buffonNeedleCentral ℓ d) := by
  unfold buffonNeedleCentral
  apply MeasurableSet.preimage
  · apply measurableSet_regionBetween
    · exact (Real.continuous_sin.const_mul (ℓ / 2)).measurable
    · exact (continuous_const.sub (Real.continuous_sin.const_mul (ℓ / 2))).measurable
    · exact measurableSet_Icc
  · exact measurable_swap

private lemma buffonNeedle_central_volume (ℓ d : ℝ) (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d) :
    volume (buffonNeedleCentral ℓ d) = ENNReal.ofReal (d * Real.pi - 2 * ℓ) := by
  unfold buffonNeedleCentral
  rw [MeasureTheory.Measure.volume_eq_prod]
  have hreg : NullMeasurableSet (regionBetween
        (fun θ : ℝ => (ℓ / 2) * Real.sin θ)
        (fun θ : ℝ => d - (ℓ / 2) * Real.sin θ)
        (Set.Icc (0 : ℝ) Real.pi)) (volume.prod volume) := by
    apply MeasurableSet.nullMeasurableSet
    apply measurableSet_regionBetween
    · exact (Real.continuous_sin.const_mul (ℓ / 2)).measurable
    · exact (continuous_const.sub (Real.continuous_sin.const_mul (ℓ / 2))).measurable
    · exact measurableSet_Icc
  rw [(MeasureTheory.Measure.measurePreserving_swap (μ := volume) (ν := volume)).measure_preimage
    hreg]
  exact buffonNeedle_centralStrip_prod_volume ℓ d hℓ hℓd

private lemma buffonNeedle_sample_volume (ℓ d : ℝ) (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d) :
    volume ((buffonNeedleExperiment ℓ d hℓ hℓd).sampleSpace) = ENNReal.ofReal (d * Real.pi) := by
  have hd_nonneg : 0 ≤ d := (lt_of_lt_of_le hℓ hℓd).le
  change volume (Set.Icc (0 : ℝ) d ×ˢ Set.Icc (0 : ℝ) Real.pi) = ENNReal.ofReal (d * Real.pi)
  rw [MeasureTheory.Measure.volume_eq_prod]
  rw [MeasureTheory.Measure.prod_prod]
  rw [Real.volume_Icc, Real.volume_Icc]
  rw [sub_zero, sub_zero]
  rw [← ENNReal.ofReal_mul hd_nonneg]

private lemma buffonNeedleCentral_subset_sample (ℓ d : ℝ) (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d) :
    buffonNeedleCentral ℓ d ⊆ (buffonNeedleExperiment ℓ d hℓ hℓd).sampleSpace := by
  intro p hp
  change (0 ≤ p.2 ∧ p.2 ≤ Real.pi) ∧
      (ℓ / 2) * Real.sin p.2 < p.1 ∧
        p.1 < d - (ℓ / 2) * Real.sin p.2 at hp
  rcases hp with ⟨hθ, hy⟩
  rcases hy with ⟨hy_left, hy_right⟩
  have hsin_nonneg : 0 ≤ Real.sin p.2 := Real.sin_nonneg_of_mem_Icc hθ
  have ha_nonneg : 0 ≤ (ℓ / 2) * Real.sin p.2 := by positivity
  have hy0 : 0 ≤ p.1 := by linarith
  have hyd : p.1 ≤ d := by linarith
  simp [BuffonNeedleExperiment.sampleSpace, buffonNeedleExperiment]
  exact ⟨⟨hy0, hθ.1⟩, ⟨hyd, hθ.2⟩⟩

private lemma buffonNeedle_sample_inter_crossing_eq_diff (ℓ d : ℝ) (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d) :
    (buffonNeedleExperiment ℓ d hℓ hℓd).sampleSpace ∩
        (buffonNeedleExperiment ℓ d hℓ hℓd).crossingEvent =
      (buffonNeedleExperiment ℓ d hℓ hℓd).sampleSpace \ buffonNeedleCentral ℓ d := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hsample, hcross⟩
    refine ⟨hsample, ?_⟩
    intro hcentral
    change (0 ≤ p.2 ∧ p.2 ≤ Real.pi) ∧
        (ℓ / 2) * Real.sin p.2 < p.1 ∧
          p.1 < d - (ℓ / 2) * Real.sin p.2 at hcentral
    rcases hcentral with ⟨hθ, hy⟩
    rcases hy with ⟨hy_left, hy_right⟩
    change p.1 ≤ ℓ * Real.sin p.2 / 2 ∨
        d - ℓ * Real.sin p.2 / 2 ≤ p.1 at hcross
    have ha : ℓ * Real.sin p.2 / 2 = (ℓ / 2) * Real.sin p.2 := by ring
    cases hcross with
    | inl hle =>
        rw [ha] at hle
        linarith
    | inr hle =>
        rw [ha] at hle
        linarith
  · intro hp
    rcases hp with ⟨hsample, hnotcentral⟩
    refine ⟨hsample, ?_⟩
    have hsample' := hsample
    simp only [BuffonNeedleExperiment.sampleSpace, buffonNeedleExperiment, Set.mem_prod,
      Set.mem_Icc] at hsample'
    have hθ : p.2 ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hsample'.2.1, hsample'.2.2⟩
    change p.1 ≤ ℓ * Real.sin p.2 / 2 ∨
        d - ℓ * Real.sin p.2 / 2 ≤ p.1
    have ha : ℓ * Real.sin p.2 / 2 = (ℓ / 2) * Real.sin p.2 := by ring
    rw [ha]
    by_contra hcross
    push Not at hcross
    rcases hcross with ⟨hc1, hc2⟩
    apply hnotcentral
    simp [buffonNeedleCentral, regionBetween]
    have hc2' : p.1 < d - ℓ / 2 * Real.sin p.2 := by linarith
    exact ⟨hθ, ⟨hc1, hc2'⟩⟩

private lemma buffonNeedle_crossing_volume (ℓ d : ℝ) (hℓ : 0 < ℓ) (hℓd : ℓ ≤ d) :
    volume ((buffonNeedleExperiment ℓ d hℓ hℓd).sampleSpace ∩
        (buffonNeedleExperiment ℓ d hℓ hℓd).crossingEvent) = ENNReal.ofReal (2 * ℓ) := by
  rw [buffonNeedle_sample_inter_crossing_eq_diff ℓ d hℓ hℓd]
  rw [MeasureTheory.measure_diff (buffonNeedleCentral_subset_sample ℓ d hℓ hℓd)
      (buffonNeedleCentral_measurableSet ℓ d).nullMeasurableSet]
  · rw [buffonNeedle_sample_volume ℓ d hℓ hℓd, buffonNeedle_central_volume ℓ d hℓ hℓd]
    have hd_nonneg : 0 ≤ d := (lt_of_lt_of_le hℓ hℓd).le
    have hcentral_nonneg : 0 ≤ d * Real.pi - 2 * ℓ := by
      have h1 : 2 * ℓ ≤ 2 * d := by nlinarith
      have h2 : 2 * d ≤ Real.pi * d := by
        exact mul_le_mul_of_nonneg_right Real.two_le_pi hd_nonneg
      nlinarith
    rw [← ENNReal.ofReal_sub (d * Real.pi) hcentral_nonneg]
    congr 1
    ring
  · rw [buffonNeedle_central_volume ℓ d hℓ hℓd]
    exact ENNReal.ofReal_ne_top

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
  rw [BuffonNeedleExperiment.crossingProbability,
    buffonNeedle_crossing_volume ℓ d hℓ hℓd,
    buffonNeedle_sample_volume ℓ d hℓ hℓd]
  rw [ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
  · ring
  · have hd_pos : 0 < d := lt_of_lt_of_le hℓ hℓd
    positivity
  · positivity
