import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Real.ConjExponents

theorem young_inequality_of_nonneg 
  {a b p q : ℝ} 
  (ha : 0 ≤ a) 
  (hb : 0 ≤ b)
  (hp : 0 < p)
  (hq : 0 < q)
  (hpq : 1/p + 1/q = 1) :
  a * b ≤ (a^p)/p + (b^q)/q := by sorry
