import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open Filter MeasureTheory Complex Module Metric Real Bornology
open scoped Topology FourierTransform RealInnerProductSpace Complex

theorem MeasureTheory.Integrable.fourierInv_fourier_eq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {f : V → ℂ} (hf : Integrable f) (hFf : Integrable (𝓕 f)) {v : V} (hv : ContinuousAt f v) :
    𝓕⁻ (𝓕 f) v = f v := by sorry
