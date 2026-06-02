import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.Span

variable (k : Type*) [Field k] (n : ℕ)

/-- S is the subset of all polynomials in k[x₁,...,xₙ] that have no zeros in kⁿ. -/
def S : Set (MvPolynomial (Fin n) k) := 
  {p | ∀ x : Fin n → k, MvPolynomial.eval x p ≠ 0}

/-- 
Let k be an arbitrary field and let S be the subset of all polynomials in k[x₁,...,xₙ]
that have no zeros in kⁿ. If I is any ideal in k[x₁,...,xₙ] such that
I ∩ S = ∅, then V(I) ≠ ∅.
-/
theorem zeroLocus_nonempty_of_disjoint_noZeros (I : Ideal (MvPolynomial (Fin n) k)) 
  (h : ∀ p ∈ I, p ∉ S) : 
  {x : Fin n → k | ∀ p ∈ I, MvPolynomial.eval x p = 0} ≠ ∅ := by sorry
:= by sorry
