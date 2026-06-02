import Mathlib.RingTheory.Nullstellensatz

theorem zeroLocus_mul {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] 
  (I J : Ideal (MvPolynomial n k)) : 
  {p : n → k | ∀ f ∈ I * J, MvPolynomial.eval p f = 0} = 
  {p : n → k | ∀ f ∈ I, MvPolynomial.eval p f = 0} ∪ 
  {p : n → k | ∀ f ∈ J, MvPolynomial.eval p f = 0} := by sorry
:= by sorry
