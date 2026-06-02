import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.MonomialOrder

theorem lm'_add_le_of_both_lm'_le (R : Type*) [CommSemiring R] (σ : Type*) [Fintype σ] 
  [LinearOrder (Finsupp σ ℕ)] (f₁ f₂ g : MvPolynomial σ R) 
  (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) (hg : g ≠ 0) (hsum : f₁ + f₂ ≠ 0)
  (h1 : MvPolynomial.leadingMonomial f₁ ≤ MvPolynomial.leadingMonomial g)
  (h2 : MvPolynomial.leadingMonomial f₂ ≤ MvPolynomial.leadingMonomial g) :
  MvPolynomial.leadingMonomial (f₁ + f₂) ≤ MvPolynomial.leadingMonomial g := by sorry
:= by sorry
