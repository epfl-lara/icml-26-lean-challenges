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
  let φ : V → ℝ := fun w ↦ π ^ (finrank ℝ V / 2 : ℝ) * Real.exp (-π ^ 2 * ‖w‖ ^ 2)
  have A : Tendsto (fun (c : ℝ) ↦ ∫ w : V, (c ^ finrank ℝ V * φ (c • (v - w))) • f w)
      atTop (𝓝 (f v)) := by
    apply tendsto_integral_comp_smul_smul_of_integrable'
    · exact fun x ↦ by positivity
    · rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
      nth_rewrite 2 [← pow_one π]
      rw [← rpow_natCast, ← rpow_natCast, ← rpow_sub pi_pos, ← rpow_mul pi_nonneg,
        ← rpow_add pi_pos]
      ring_nf
      exact rpow_zero _
    · have A : Tendsto (fun (w : V) ↦ π ^ 2 * ‖w‖ ^ 2) (cobounded V) atTop := by
        rw [tendsto_const_mul_atTop_of_pos (by positivity)]
        apply (tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cobounded_atTop
      have B := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (finrank ℝ V / 2) 1
        zero_lt_one |>.comp A |>.const_mul (π ^ (-finrank ℝ V / 2 : ℝ))
      rw [mul_zero] at B
      convert B using 2 with x
      simp only [neg_mul, one_mul, Function.comp_apply, ← mul_assoc, ← rpow_natCast, φ]
      congr 1
      rw [mul_rpow (by positivity) (by positivity), ← rpow_mul pi_nonneg,
        ← rpow_mul (norm_nonneg _), ← mul_assoc, ← rpow_add pi_pos, mul_comm]
      congr <;> ring
    · exact hf_int
    · exact hf_cont
  have B : Tendsto
      (fun (c : ℝ) ↦
        ∫ w : V, ((c ^ (1 / 2 : ℝ)) ^ finrank ℝ V * φ ((c ^ (1 / 2 : ℝ)) • (v - w))) • f w)
      atTop (𝓝 (f v)) :=
    A.comp (tendsto_rpow_atTop (by simp))
  apply B.congr'
  filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
  congr with w
  apply congrArg (fun a : ℝ => a • f w)
  dsimp [φ]
  have hpow :
      (c ^ (1 / 2 : ℝ)) ^ finrank ℝ V * π ^ (finrank ℝ V / 2 : ℝ) =
        (π * c) ^ ((finrank ℝ V : ℝ) / 2) := by
    rw [mul_rpow pi_nonneg hc.le, ← rpow_natCast, ← rpow_mul hc.le]
    ring_nf
  have hexp :
      Real.exp (-π ^ 2 * ‖c ^ (1 / 2 : ℝ) • (v - w)‖ ^ 2) =
        Real.exp (-(π ^ 2) * c * ‖v - w‖ ^ 2) := by
    congr 1
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_mul, neg_inj,
      ← rpow_natCast, ← rpow_mul hc.le, mul_assoc]
    norm_num
  calc
    (c ^ (1 / 2 : ℝ)) ^ finrank ℝ V *
        (π ^ (finrank ℝ V / 2 : ℝ) * Real.exp (-π ^ 2 * ‖c ^ (1 / 2 : ℝ) • (v - w)‖ ^ 2))
        = ((c ^ (1 / 2 : ℝ)) ^ finrank ℝ V * π ^ (finrank ℝ V / 2 : ℝ)) *
          Real.exp (-π ^ 2 * ‖c ^ (1 / 2 : ℝ) • (v - w)‖ ^ 2) := by ring
    _ = (π * c) ^ ((finrank ℝ V : ℝ) / 2) *
          Real.exp (-π ^ 2 * ‖c ^ (1 / 2 : ℝ) • (v - w)‖ ^ 2) := by rw [hpow]
    _ = (π * c) ^ ((finrank ℝ V : ℝ) / 2) *
          Real.exp (-(π ^ 2) * c * ‖v - w‖ ^ 2) := by rw [hexp]
