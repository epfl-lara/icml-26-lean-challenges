import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

theorem span_pow_card_mul_le_span_image_pow (k : Type*) [Field k] (n : ℕ) (s : Finset (MvPolynomial (Fin n) k)) 
  (M : ℕ) : 
  let J := Ideal.span (s : Set (MvPolynomial (Fin n) k))
  J ^ (s.card * M) ≤ Ideal.span {g ^ M | g ∈ s} := by sorry
:= by sorry
