import Mathlib.RingTheory.MvPolynomial.MonomialOrder

open scoped MonomialOrder

/-- Source notation bridge: `leadingMonomial m f` represents the source `LM(f)` as the exponent
vector selected by the fixed monomial order `m`. Mathlib calls this `m.degree f`. -/
noncomputable def leadingMonomial {R : Type*} [CommSemiring R] {σ : Type*}
    (m : MonomialOrder σ) (f : MvPolynomial σ R) : σ →₀ ℕ :=
  m.degree f

/--
Source proof: every monomial of `f₁ + f₂` comes from at least one of `f₁` or `f₂`.
Since the leading monomials of both summands are strictly below `LM(g)`, every monomial in
the sum remains below `LM(g)`, so the leading monomial of the sum is also below `LM(g)`.
Prover notes: unfold `leadingMonomial` to `m.degree`; use `m.degree_add_le`, then bound the
supremum of `m.degree f₁` and `m.degree f₂` by `m.degree g` using the two strict hypotheses.
The nonzero hypotheses are retained to match the source statement.
-/
theorem lm'_add_lt_of_both_lm'_lt {R : Type*} [CommSemiring R] {σ : Type*}
    (m : MonomialOrder σ) (f₁ f₂ g : MvPolynomial σ R)
    (hf₁_nonzero : f₁ ≠ 0) (hf₂_nonzero : f₂ ≠ 0) (hg_nonzero : g ≠ 0)
    (hsum_nonzero : f₁ + f₂ ≠ 0)
    (hf₁_lm_lt : leadingMonomial m f₁ ≺[m] leadingMonomial m g)
    (hf₂_lm_lt : leadingMonomial m f₂ ≺[m] leadingMonomial m g) :
    leadingMonomial m (f₁ + f₂) ≺[m] leadingMonomial m g := by
  sorry
