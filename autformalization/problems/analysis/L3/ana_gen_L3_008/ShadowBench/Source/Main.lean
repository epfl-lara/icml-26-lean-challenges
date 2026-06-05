import Mathlib

open Set MeasureTheory

/--
Source definition bridge for `docs/source.tex`, theorem `line-17`.
The paper defines `g x = ∫ t in x..b, f t / t` only for `0 < x ≤ b`.
For Lean's total-function setting we use the zero-extension outside that source domain;
this does not change interval integrability or the interval integral over `[0,b]` except
at the null endpoint.
-/
noncomputable def intervalTailIntegral (f : ℝ → ℝ) (b : ℝ) : ℝ → ℝ :=
  fun x => if 0 < x ∧ x ≤ b then ∫ t in x..b, f t / t else 0

/--
Source theorem `line-17` (`intervalIntegrable_g_and_integral_g_eq_integral`).
Source proof: first prove the claim for nonnegative `f` by Tonelli/Fubini on the region
`0 ≤ x ≤ t ≤ b`, obtaining
`∫_0^b ∫_x^b f t / t dt dx = ∫_0^b (f t / t) * t dt = ∫_0^b f t dt`.
Since the last integral is finite, `g` is integrable.  Then apply the same argument to
positive and negative parts of a general integrable real function and use linearity.
Prover notes: use interval-integral congruence to ignore the zero-extension and the
endpoint `0`; the explicit hypothesis `0 < b` records the source's positive interval
convention.
-/
theorem intervalIntegrable_g_and_integral_g_eq_integral (b : ℝ) (f : ℝ → ℝ)
    (hb : 0 < b) (hf : IntervalIntegrable f volume 0 b) :
    IntervalIntegrable (intervalTailIntegral f b) volume 0 b ∧
      ∫ x in 0..b, intervalTailIntegral f b x = ∫ t in 0..b, f t := by
  sorry
