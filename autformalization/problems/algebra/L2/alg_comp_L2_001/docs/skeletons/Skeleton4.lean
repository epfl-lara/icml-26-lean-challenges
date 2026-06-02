import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Data.Finsupp.MonomialOrder

open MvPolynomial
open scoped MonomialOrder

theorem minimal_monomial_mem_generators {n : ℕ} 
  (A : Set (Fin n →₀ ℕ)) 
  (I : Ideal (MvPolynomial (Fin n) ℚ)) 
  (hI : I = Ideal.span {m : MvPolynomial (Fin n) ℚ | ∃ α ∈ A, m = MvPolynomial.X α}) 
  (S : Set (Fin n →₀ ℕ)) 
  (hS : S = {α | ∃ f ∈ I, α ∈ f.support}) 
  (lt : (Fin n →₀ ℕ) → (Fin n →₀ ℕ) → Prop)
  (hwell : WellFounded (fun α β => lt α β))
  (horder : IsPartialOrder (Fin n →₀ ℕ) lt)
  (hmult : ∀ α β γ, lt α β → lt (α + γ) (β + γ))
  (hnonempty : S.Nonempty) : 
  ∃ min_elem ∈ S, (∀ β ∈ S, lt min_elem β) ∧ min_elem ∈ A := by sorry
:= by sorry
