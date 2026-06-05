import Mathlib.RingTheory.MvPolynomial.MonomialOrder

open scoped BigOperators MonomialOrder

/--
Source lemma `lm_sum_le_of_all_lm_le`: for a positive finite family of multivariate
polynomials over a nontrivial commutative semiring and a fixed monomial order, if every
individual leading monomial is bounded by `x^δ`, then the leading monomial of the finite
sum is also bounded by `x^δ`.

Source proof: induction on the number of summands, using the assumed one-summand case
and the previously proven two-summand case.

Prover notes: Mathlib represents the leading monomial exponent for a monomial order `m`
as `m.degree`. The source monomial `x^δ` is represented by the exponent vector `δ`, and
`≤` in the monomial order is `≼[m]`. A direct proof should use
`MonomialOrder.degree_sum_le` for the sum over `Fin n` and bound the resulting finite
supremum by `δ` using the hypothesis.
-/
theorem lm_sum_le_of_all_lm_le {σ R : Type*} [CommSemiring R] [Nontrivial R]
    (m : MonomialOrder σ) (n : ℕ) (hn : 0 < n)
    (f : Fin n → MvPolynomial σ R) (δ : σ →₀ ℕ)
    (h : ∀ i : Fin n, m.degree (f i) ≼[m] δ) :
    m.degree (∑ i : Fin n, f i) ≼[m] δ := by
  sorry
