import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MeanInequalities

open scoped BigOperators
open Finset Real

/-- The hyperbolic set from `docs/source.tex`, represented as a subset of
finite coordinate functions. The source notation `ℝ_+^n` is encoded by the
coordinatewise predicate `∀ i, 0 ≤ x i`. -/
def hyperbolicSet (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∏ i, x i) ≥ 1}

/--
Source proof: For `x` and `y` in the hyperbolic set and `θ ∈ [0, 1]`, set
`z = θ • x + (1 - θ) • y`. Each coordinate is nonnegative. The product
condition follows coordinatewise from the weighted AM-GM inequality
`xᵢ^θ yᵢ^(1-θ) ≤ θ xᵢ + (1-θ)yᵢ`, then by multiplying over all coordinates and
using `∏ xᵢ ≥ 1` and `∏ yᵢ ≥ 1`.
Prover notes: Unfold `hyperbolicSet` and `Convex`; prove coordinate
nonnegativity and the product lower bound separately. For the product step, use
the weighted AM-GM hint directly or a nonnegative-real form such as
`NNReal.geom_mean_le_arith_mean_weighted`, together with finite-product
monotonicity and `Real.rpow` facts.
-/
theorem hyperbolic_set_convex (n : ℕ) :
    Convex ℝ (hyperbolicSet n) := by
  sorry
