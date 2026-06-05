import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set MeasureTheory

/-!
ShadowBench problem `analysis/L2/ana_gen_L2_005`.
Source theorem: `docs/source.tex`, line 17.
Blueprint: `ShadowBench/Source/Blueprint.md`.
-/

/--
Source proof: define `G x = F a + ∫ t in a..x, F' t`, show `F = G` on `[a,b]`, use
absolute continuity of interval-integral primitives together with constants and sums, then apply the
fundamental theorem of calculus on `[a,b]` for the endpoint identity.

Prover notes: this Lean statement represents the source derivative `F'` by `deriv F` and uses
`AbsolutelyContinuousOnInterval F a b` for absolute continuity on the closed interval. Try
the primitive theorem
`IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral` and FTC lemmas from
`IntervalIntegral.FundThmCalculus`. If Mathlib's `IntervalIntegrable` is too weak to derive the
primitive equality asserted in the source proof, return to statement/source review rather than
changing this theorem during proving.
-/
theorem ContinuousOn.absolutelyContinuousOnInterval_and_sub_eq_integral_deriv
    {a b : ℝ} {F : ℝ → ℝ}
    (hcont : ContinuousOn F (Icc a b))
    (hab : a ≤ b)
    (hdiff : DifferentiableOn ℝ F (Ioo a b))
    (hintegr : IntervalIntegrable (deriv F) volume a b) :
    AbsolutelyContinuousOnInterval F a b ∧ F b - F a = ∫ x in a..b, deriv F x := by
  sorry
