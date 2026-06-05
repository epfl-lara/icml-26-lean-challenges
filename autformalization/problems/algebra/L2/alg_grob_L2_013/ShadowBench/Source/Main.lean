import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-!
ShadowBench problem: algebra/L2/alg_grob_L2_013
Source: `docs/source.tex`
Blueprint: `ShadowBench/Source/Blueprint.md`
-/

open scoped MonomialOrder

/--
Source lemma `lm_add_le_of_both_lm_le_mon` (`docs/source.tex`, lines 17-23):
if the leading monomial of each of `f₁` and `f₂` is bounded by the monomial
`x^δ`, then the leading monomial of `f₁ + f₂` is also bounded by `x^δ`.
Here Mathlib represents the leading monomial exponent by `m.degree` and compares
exponents using the monomial-order relation `≼[m]`.

Source proof: choose a polynomial `g = c x^δ` with leading monomial `δ`, which
exists because `R` is nontrivial; then use the corresponding inequality for
`f₁`, `f₂`, and `g`.

Prover notes: the direct Mathlib route is to apply `m.degree_add_le` and close
the upper-bound side goal with `sup_le h₁ h₂`.
-/
theorem lm_add_le_of_both_lm_le_mon {σ : Type*} {R : Type*}
    [CommSemiring R] [Nontrivial R] (m : MonomialOrder σ)
    (f₁ f₂ : MvPolynomial σ R) (δ : σ →₀ ℕ)
    (h₁ : m.degree f₁ ≼[m] δ) (h₂ : m.degree f₂ ≼[m] δ) :
    m.degree (f₁ + f₂) ≼[m] δ := by
  exact le_trans (m.degree_add_le (f := f₁) (g := f₂)) (sup_le h₁ h₂)
