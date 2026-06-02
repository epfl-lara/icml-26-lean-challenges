import Mathlib.RingTheory.Nullstellensatz

theorem zariskiClosure_is_smallest_algebraic_set (k : Type*) [Field k] (n : ℕ) (S : Set (Fin n → k)) :
  ∀ W : Set (Fin n → k), 
    (∃ I : Ideal (MvPolynomial (Fin n) k), W = {x | ∀ p ∈ I, MvPolynomial.eval x p = 0}) → 
    S ⊆ W → 
    {x | ∀ p ∈ Ideal.ofSet S, MvPolynomial.eval x p = 0} ⊆ W := by sorry
