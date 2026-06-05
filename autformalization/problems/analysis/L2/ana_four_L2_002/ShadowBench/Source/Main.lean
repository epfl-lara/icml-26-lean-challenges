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
  sorry

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
  sorry
