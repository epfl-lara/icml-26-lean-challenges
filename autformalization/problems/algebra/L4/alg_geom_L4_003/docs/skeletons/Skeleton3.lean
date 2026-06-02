import Mathlib

open Metric EuclideanSpace IntermediateField Module Polynomial
open scoped PiLp Real

/-- A real number is constructible if it can be constructed using compass and straightedge -/
def IsConstructible (α : ℝ) : Prop := by sorry

/-- The normal closure of ℚ(α) over ℚ in ℂ -/
noncomputable def NormalClosure (α : ℝ) : Type* := by sorry

/-- A natural number is a power of 2 if it can be expressed as 2^k for some k -/
def IsPowerOfTwo (n : ℕ) : Prop := ∃ k : ℕ, n = 2^k

/-- A Fermat prime is a prime number of the form 2^(2^a) + 1 for some nonnegative integer a -/
def IsFermatPrime (p : ℕ) : Prop := Nat.Prime p ∧ ∃ a : ℕ, p = 2^(2^a) + 1

/-- An angle 2π/n is constructible if it can be constructed using compass and straightedge -/
def IsAngleConstructible (n : ℕ) : Prop := by sorry

/-- A regular n-gon is constructible if it can be constructed using compass and straightedge -/
def IsRegularNGonConstructible (n : ℕ) : Prop := by sorry

theorem constructible_iff (α : ℝ) : 
  IsConstructible α ↔ IsPowerOfTwo (FiniteDimensional.finrank ℚ (NormalClosure α)) := by sorry

theorem cyclotomic_angle_constructible_iff (n : ℕ) : 
  (IsAngleConstructible n ↔ 
   ∃ (power_of_two : ℕ) (fermat_primes : Finset ℕ), 
     IsPowerOfTwo power_of_two ∧ 
     (∀ p ∈ fermat_primes, IsFermatPrime p) ∧
     n = power_of_two * fermat_primes.prod id) ∧
  (IsAngleConstructible n ↔ IsRegularNGonConstructible n) := by sorry
