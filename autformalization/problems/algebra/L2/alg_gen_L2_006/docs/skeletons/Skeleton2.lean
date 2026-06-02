import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Nullstellensatz

open scoped BigOperators
open MvPolynomial

/-- The zero locus of an ideal is the set of points where all elements of the ideal vanish -/
def zeroLocus {σ : Type*} [Fintype σ] {R : Type*} [CommRing R] (I : Ideal (MvPolynomial σ R)) : 
  Set (σ → R) := {x | ∀ p ∈ I, MvPolynomial.eval x p = 0}

/-- The vanishing ideal of a set of points is the ideal of all polynomials that vanish on that set -/
def vanishingIdeal {σ : Type*} [Fintype σ] {R : Type*} [CommRing R] (S : Set (σ → R)) : 
  Ideal (MvPolynomial σ R) := Ideal.span {p | ∀ x ∈ S, MvPolynomial.eval x p = 0}

theorem zeroLocus_subset_of_ideal_le {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]
    {I₁ I₂ : Ideal (MvPolynomial σ R)} (h : I₁ ≤ I₂) : 
  zeroLocus I₂ ⊆ zeroLocus I₁ := by sorry

theorem vanishingIdeal_le_of_subset {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]
    {S₁ S₂ : Set (σ → R)} (h : S₁ ⊆ S₂) : 
  vanishingIdeal S₂ ≤ vanishingIdeal S₁ := by sorry

theorem zeroLocus_radical_eq_zeroLocus {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]
    (I : Ideal (MvPolynomial σ R)) : 
  zeroLocus (radical I) = zeroLocus I := by sorry
