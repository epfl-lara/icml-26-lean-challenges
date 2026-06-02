import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.MonomialOrder

theorem lm_add_le_of_both_lm_le_mon {σ : Type*} {R : Type*} 
  [CommSemiring R] [Nontrivial R] 
  [DecidableEq σ]
  [LinearOrder (σ →₀ ℕ)] -- Linear order on monomials
  [CovariantClass (σ →₀ ℕ) (··≤··) (·+·) (·+·)] -- Order respects addition
  (f₁ f₂ : MvPolynomial σ R) 
  (δ : σ →₀ ℕ) 
  (h₁ : MvPolynomial.leadingMonomial f₁ ≤ δ) 
  (h₂ : MvPolynomial.leadingMonomial f₂ ≤ δ) : 
  MvPolynomial.leadingMonomial (f₁ + f₂) ≤ δ := by sorry
