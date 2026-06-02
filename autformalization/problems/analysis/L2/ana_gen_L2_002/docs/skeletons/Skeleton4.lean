import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Real.ConjExponents

open Finset NNReal ENNReal
open scoped BigOperators

theorem young_inequality_of_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (h : 1 / p + 1 / q = 1) :
    a * b ≤ a ^ p / p + b ^ q / q := by sorry
