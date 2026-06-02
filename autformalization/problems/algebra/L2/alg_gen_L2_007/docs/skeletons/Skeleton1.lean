import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

theorem isGCD_iff_span_is_least_principal_above_span_pair (k : Type*) [Field k] (n : ℕ) (f g h : MvPolynomial (Fin n) k) :
  (h ∣ f ∧ h ∣ g ∧ ∀ d : MvPolynomial (Fin n) k, d ∣ f → d ∣ g → d ∣ h) ↔
  ((Ideal.span {f, g} ⊆ Ideal.span {h}) ∧ 
   ∀ h' : MvPolynomial (Fin n) k, Ideal.span {f, g} ⊆ Ideal.span {h'} → Ideal.span {h} ⊆ Ideal.span {h'}) := by sorry
