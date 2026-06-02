import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open Filter MeasureTheory Complex Module Metric Real Bornology
open scoped Topology FourierTransform RealInnerProductSpace Complex

/-- Let $f$ be an integrable function on a finite-dimensional real inner product space. 
If its Fourier transform $\mathcal{F} f$ is also integrable, then at every point where $f$ is continuous,
the inverse Fourier transform of $\mathcal{F} f$ equals $f$ itself. -/
theorem MeasureTheory.Integrable.fourierInv_fourier_eq {E : Type*} 
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : E → ℝ) 
  (hf_integrable : MeasureTheory.Integrable f)
  (hF_integrable : MeasureTheory.Integrable (FourierTransform f)) :
  ∀ v : E, ContinuousAt f v → FourierTransform.inv (FourierTransform f) v = f v := by sorry
