import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Real.ConjExponents

open Finset NNReal ENNReal
open scoped BigOperators

/--
Young's inequality for nonnegative real numbers with positive conjugate exponents.

Source proof: Since `p⁻¹ + q⁻¹ = 1`, apply weighted AM-GM to
`a ^ p` and `b ^ q` with weights `p⁻¹` and `q⁻¹`, obtaining
`(a ^ p) ^ (p⁻¹) * (b ^ q) ^ (q⁻¹) ≤ p⁻¹ * a ^ p + q⁻¹ * b ^ q`,
which is equivalent to `a * b ≤ a ^ p / p + b ^ q / q`.

Prover notes: Search `Mathlib.Analysis.MeanInequalities` for
`Real.young_inequality_of_nonneg`. Build `p.HolderConjugate q` from `hp`, `hq`,
and `hpq` using the `HolderTriple` fields; `simpa [one_div] using hpq` converts
the displayed source equation to the inverse-addition field.
-/
theorem young_inequality_of_nonneg
    (a b p q : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 0 < p) (hq : 0 < q)
    (hpq : 1 / p + 1 / q = 1) :
    a * b ≤ a ^ p / p + b ^ q / q := by
  have hpq' : p.HolderConjugate q := by
    exact ⟨by simpa [one_div] using hpq, hp, hq⟩
  exact Real.young_inequality_of_nonneg ha hb hpq'
