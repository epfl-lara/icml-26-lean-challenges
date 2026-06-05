import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Henselian

/--
Source lemma `mem_monmul_supp_iff` from `docs/source.tex`.

Source proof: if `x^μ` divides `x^ν`, take the multiplier to be the monomial
`x^(ν - μ)`. Conversely, if `x^ν` occurs in `x^μ * f`, then some monomial
`x^α` of `f` contributes `x^(μ + α) = x^ν`, so `x^μ` divides `x^ν`.

Prover notes: represent `x^η` as `MvPolynomial.monomial η (1 : K)` and
membership of a monomial in a polynomial as membership of its exponent in
`support`. The proof should reduce monomial divisibility to pointwise exponent
order, use `ν - μ` in the forward direction, and extract an exponent from the
support of `f` in the reverse direction.
-/
theorem mem_monmul_supp_iff {K σ : Type*} [Field K]
    (μ ν : σ →₀ ℕ) :
    (MvPolynomial.monomial μ (1 : K) ∣ MvPolynomial.monomial ν (1 : K)) ↔
      ∃ f : MvPolynomial σ K,
        ν ∈ (MvPolynomial.monomial μ (1 : K) * f).support := by
  sorry
