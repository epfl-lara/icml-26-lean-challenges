import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open Filter MeasureTheory Complex Module Metric Real Bornology
open scoped Topology FourierTransform RealInnerProductSpace Complex

theorem tendsto_integral_gaussian_smul {V E : Type*} [NormedAddCommGroup V] [NormedAddCommGroup E] 
    [MeasurableSpace V] [MeasureSpace V] [NormedSpace ℝ V] [NormedSpace ℝ E] 
    [CompleteSpace E] [FiniteDimensional ℝ V] [InnerProductSpace ℝ V]
    (f : V → E) (μ : Measure V) (v : V) 
    (hf_int : Integrable f μ) (hf_cont : ContinuousAt f v) :
    Tendsto (fun c : ℝ ↦ (Real.pi * c) ^ ((FiniteDimensional.finrank ℝ V : ℝ) / 2) *
                    ∫ w : V, Real.exp (-Real.pi^2 * c * ‖v - w‖^2) • f w ∂μ)
           atTop (𝓝 (f v)) := by sorry
:= by sorry
