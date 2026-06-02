import Mathlib.Algebra.MvPolynomial.Basic

theorem monomial_set_union_distrib (R : Type*) [CommSemiring R] (σ : Type*) [Fintype σ] 
  (F G : Finset (MvPolynomial σ R)) :
  let Mon := fun (S : Finset (MvPolynomial σ R)) => 
    {m : MvPolynomial σ R | ∃ f ∈ S, m ∈ f.support}
  Mon F ∪ Mon G = Mon (F ∪ G) := by sorry
:= by sorry
