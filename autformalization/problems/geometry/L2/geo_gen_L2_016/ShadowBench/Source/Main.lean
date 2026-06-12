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
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  change ((∀ i, 0 ≤ x i) ∧ 1 ≤ ∏ i, x i) at hx
  change ((∀ i, 0 ≤ y i) ∧ 1 ≤ ∏ i, y i) at hy
  change (∀ i : Fin n, 0 ≤ a * x i + b * y i) ∧
    1 ≤ ∏ i : Fin n, (a * x i + b * y i)
  rcases hx with ⟨hx_nonneg, hx_prod⟩
  rcases hy with ⟨hy_nonneg, hy_prod⟩
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx_nonneg i)) (mul_nonneg hb (hy_nonneg i))
  · have hcoord : ∀ i : Fin n, x i ^ a * y i ^ b ≤ a * x i + b * y i := by
      intro i
      exact Real.geom_mean_le_arith_mean2_weighted ha hb (hx_nonneg i) (hy_nonneg i) hab
    have hleft_nonneg : ∀ i : Fin n, 0 ≤ x i ^ a * y i ^ b := by
      intro i
      exact mul_nonneg (Real.rpow_nonneg (hx_nonneg i) a) (Real.rpow_nonneg (hy_nonneg i) b)
    have hprod_mono :
        (∏ i : Fin n, x i ^ a * y i ^ b) ≤ ∏ i : Fin n, (a * x i + b * y i) := by
      exact Finset.prod_le_prod (fun i _ => hleft_nonneg i) (fun i _ => hcoord i)
    have hxpow : (∏ i : Fin n, x i ^ a) = (∏ i : Fin n, x i) ^ a := by
      simpa using
        (Real.finset_prod_rpow (Finset.univ : Finset (Fin n)) x
          (by intro i _; exact hx_nonneg i) a)
    have hypow : (∏ i : Fin n, y i ^ b) = (∏ i : Fin n, y i) ^ b := by
      simpa using
        (Real.finset_prod_rpow (Finset.univ : Finset (Fin n)) y
          (by intro i _; exact hy_nonneg i) b)
    have hprod_pow :
        (∏ i : Fin n, x i ^ a * y i ^ b) =
          (∏ i : Fin n, x i) ^ a * (∏ i : Fin n, y i) ^ b := by
      rw [Finset.prod_mul_distrib, hxpow, hypow]
    have hgeom_lower : 1 ≤ (∏ i : Fin n, x i ^ a * y i ^ b) := by
      rw [hprod_pow]
      exact one_le_mul_of_one_le_of_one_le
        (Real.one_le_rpow hx_prod ha) (Real.one_le_rpow hy_prod hb)
    exact le_trans hgeom_lower hprod_mono
