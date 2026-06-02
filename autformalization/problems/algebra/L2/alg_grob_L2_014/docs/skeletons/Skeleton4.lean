import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.MonomialOrder

theorem lm_sum_le_of_all_lm_le (σ : Type*) (R : Type*) [CommSemiring R] [Nontrivial R]
    [MonomialOrder σ] (n : ℕ) (f : Fin n → MvPolynomial σ R) (δ : Finsupp σ ℕ)
    (h : ∀ i : Fin n, MvPolynomial.leadingMonomial (f i) ≤ δ) :
    MvPolynomial.leadingMonomial (∑ i : Fin n, f i) ≤ δ := by sorry
:= by sorry
