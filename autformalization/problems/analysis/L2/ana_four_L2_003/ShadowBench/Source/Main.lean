import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open Filter MeasureTheory Complex Module Metric Real Bornology
open scoped Topology FourierTransform RealInnerProductSpace Complex

/-!
ShadowBench problem `analysis/L2/ana_four_L2_003`.
Source formalization target for `docs/source.tex`.
-/

/--
Source theorem `line-17`, `tendsto_integral_gaussian_smul` from `docs/source.tex`.
Source proof: use the normalized Gaussian
`φ(w) = π^(dim_ℝ V / 2) * exp (-π^2 * ‖w‖^2)`. Its dilates form an
approximate identity: the kernels are nonnegative, have integral one by the Gaussian integral
formula, and concentrate at the origin by exponential decay. Applying the approximate-identity
convergence theorem to an integrable function continuous at `v`, then substituting `c^(1/2)`,
gives the displayed kernel.
Prover notes: the source notation `dμ` is represented here by Lean's default Haar/Lebesgue measure
`volume`. Use `MeasureTheory.tendsto_integral_comp_smul_smul_of_integrable'` with
`GaussianFourier.integral_rexp_neg_mul_sq_norm`, or compare with the nearby complex-valued Mathlib
lemma `Real.tendsto_integral_gaussian_smul'` from `Mathlib.Analysis.Fourier.Inversion`.
-/
theorem tendsto_integral_gaussian_smul
    {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : V → E) (v : V) (hf_int : Integrable f) (hf_cont : ContinuousAt f v) :
    Tendsto (fun c : ℝ =>
      ∫ w : V,
        (((Real.pi * c) ^ ((finrank ℝ V : ℝ) / 2)) *
          Real.exp (-(Real.pi ^ 2) * c * ‖v - w‖ ^ 2)) • f w)
      atTop (𝓝 (f v)) := by
  sorry
