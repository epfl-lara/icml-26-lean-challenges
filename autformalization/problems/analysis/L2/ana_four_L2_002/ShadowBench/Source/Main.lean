import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open Filter MeasureTheory Complex Module Metric Real Bornology
open scoped Topology FourierTransform RealInnerProductSpace Complex

noncomputable section

/--
Source helper for `docs/source.tex`, line-17: the measure-parameterized Fourier
integral displayed in the source. This companion definition records the notation
bridge because the source carries an arbitrary measure `dv`.
-/
def sourceFourierTransform {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure V) (f : V → E) (w : V) : E :=
  ∫ x : V, Complex.exp ((-2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((inner ℝ w x) : ℂ)) • f x ∂μ

/--
Source helper for `docs/source.tex`, line-17: the measure-parameterized inverse
Fourier integral displayed in the source.
-/
def sourceInverseFourierTransform {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure V) (g : V → E) (v : V) : E :=
  ∫ w : V, Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((inner ℝ w v) : ℂ)) • g w ∂μ

/--
Source `docs/source.tex`, line-17 (`ABM_analysis_L2_ana_four_L2_002_item_1`).
The source introduces the Fourier and inverse Fourier transform notation by the
displayed integral formulas on a finite-dimensional real inner product space with
measure `dv` and complex normed target `E`.

Source proof: no proof is supplied; this is a definitional notation item.
Prover notes: unfold `sourceFourierTransform` and `sourceInverseFourierTransform`;
both components are definitional equalities.
-/
lemma ABM_analysis_L2_ana_four_L2_002_item_1
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure V) (f g : V → E) :
    (∀ w : V, sourceFourierTransform μ f w =
      ∫ x : V, Complex.exp ((-2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((inner ℝ w x) : ℂ)) • f x ∂μ) ∧
    (∀ v : V, sourceInverseFourierTransform μ g v =
      ∫ w : V,
        Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((inner ℝ w v) : ℂ)) • g w ∂μ) := by
  constructor <;> intro _ <;> rfl

/--
Source `docs/source.tex`, line-31 (`tendsto_integral_cexp_sq_smul`).
If `f` is integrable, then the integrals of the Gaussian cutoffs
`exp (-c⁻¹ ‖v‖²) • f v` converge, as `c → +∞`, to the integral of `f`.

Source proof: apply dominated convergence. Pointwise the scalar factor tends to
`1`; for eventually positive `c`, the norm of the cutoff integrand is bounded by
`‖f v‖`; measurability follows from continuity of the scalar factor and the
strong measurability contained in `hf`.
Prover notes: use a Bochner-integral dominated-convergence theorem with dominant
`v ↦ ‖f v‖`, prove eventual `Real.exp (-c⁻¹ * ‖v‖ ^ 2) ≤ 1`, and prove scalar
pointwise convergence from `c⁻¹ → 0` along `atTop`.
-/
lemma tendsto_integral_cexp_sq_smul
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure V) (f : V → E) (hf : Integrable f μ) :
    Tendsto (fun c : ℝ => ∫ v : V, Real.exp (-c⁻¹ * ‖v‖ ^ 2) • f v ∂μ)
      atTop (𝓝 (∫ v : V, f v ∂μ)) := by
  have hmeas : ∀ᶠ c in atTop,
      AEStronglyMeasurable (fun v : V => Real.exp (-c⁻¹ * ‖v‖ ^ 2) • f v) μ := by
    refine Eventually.of_forall ?_
    intro c
    have hs : AEStronglyMeasurable (fun v : V => Real.exp (-c⁻¹ * ‖v‖ ^ 2)) μ := by
      exact
        ((by continuity) :
          Continuous (fun v : V => Real.exp (-c⁻¹ * ‖v‖ ^ 2))).aestronglyMeasurable
    exact hs.smul hf.aestronglyMeasurable
  have hbound : ∀ᶠ c in atTop, ∀ᵐ v ∂μ,
      ‖Real.exp (-c⁻¹ * ‖v‖ ^ 2) • f v‖ ≤ (fun v : V => ‖f v‖) v := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with c hc
    filter_upwards with v
    have hcinv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc
    have hpow : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
    have hexp_le_one : Real.exp (-c⁻¹ * ‖v‖ ^ 2) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith)
    calc
      ‖Real.exp (-c⁻¹ * ‖v‖ ^ 2) • f v‖ = Real.exp (-c⁻¹ * ‖v‖ ^ 2) * ‖f v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      _ ≤ 1 * ‖f v‖ := by
        exact mul_le_mul_of_nonneg_right hexp_le_one (norm_nonneg _)
      _ = ‖f v‖ := by rw [one_mul]
  have hlim : ∀ᵐ v ∂μ,
      Tendsto (fun c : ℝ => Real.exp (-c⁻¹ * ‖v‖ ^ 2) • f v) atTop (𝓝 (f v)) := by
    filter_upwards with v
    have harg : Tendsto (fun c : ℝ => -c⁻¹ * ‖v‖ ^ 2) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.neg.mul_const (‖v‖ ^ 2))
    have hscalar : Tendsto (fun c : ℝ => Real.exp (-c⁻¹ * ‖v‖ ^ 2)) atTop (𝓝 1) := by
      simpa [Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp harg
    simpa using hscalar.smul (tendsto_const_nhds : Tendsto (fun _ : ℝ => f v) atTop (𝓝 (f v)))
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (F := fun c v => Real.exp (-c⁻¹ * ‖v‖ ^ 2) • f v) (f := f)
    (fun v : V => ‖f v‖) hmeas hbound hf.norm hlim
