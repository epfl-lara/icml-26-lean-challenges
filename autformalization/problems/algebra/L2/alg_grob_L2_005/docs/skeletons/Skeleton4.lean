import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.MonomialOrder

theorem coeff_zero_of_lt_lm {σ : Type*} [Fintype σ] {R : Type*} [CommSemiring R]
  (f g : MvPolynomial σ R) (mo : MvPolynomial.MonomialOrder σ)
  (h_g_ne_zero : g ≠ 0)
  (h_order : mo.lt g.leadingMonomial f.leadingMonomial) :
  f.coeff g.leadingMonomial = 0 := by sorry
:= by sorry
