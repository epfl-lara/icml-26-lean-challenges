import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.MonomialOrder

theorem lm'_add_lt_of_both_lm'_lt {R : Type*} [CommSemiring R] {σ : Type*} 
  (f₁ f₂ g : MvPolynomial σ R) 
  (hf₁_nonzero : f₁ ≠ 0) (hf₂_nonzero : f₂ ≠ 0) (hg_nonzero : g ≠ 0)
  (hsum_nonzero : f₁ + f₂ ≠ 0)
  (h_order : MvPolynomial.leadingMonomial f₁ < MvPolynomial.leadingMonomial g ∧ 
             MvPolynomial.leadingMonomial f₂ < MvPolynomial.leadingMonomial g) :
  MvPolynomial.leadingMonomial (f₁ + f₂) < MvPolynomial.leadingMonomial g := by sorry
