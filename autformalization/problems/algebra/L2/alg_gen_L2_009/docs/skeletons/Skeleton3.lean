import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.AdjoinRoot

open scoped BigOperators
open MvPolynomial

theorem radical_mul_eq_radical_inf (k : Type*) [Field k] :
  -- Part 1: For any polynomial ring k[x₁,...,xₙ], √(IJ) = √(I ∩ J)
  (∀ (n : ℕ) (I J : Ideal (MvPolynomial (Fin n) k)), 
    Ideal.radical (I * J) = Ideal.radical (I ⊓ J)) ∧
  -- Part 2: In k[x,y], I = ⟨x⟩ and J = ⟨x,y⟩ are radical, but IJ is not
  (let I : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {X 0}
   let J : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {X 0, X 1}
   Ideal.IsRadical I ∧ Ideal.IsRadical J ∧ ¬Ideal.IsRadical (I * J)) ∧
  -- Part 3: In k[x,y], √(IJ) ≠ √I · √J for the same I, J
  (let I : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {X 0}
   let J : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {X 0, X 1}
   Ideal.radical (I * J) ≠ Ideal.radical I * Ideal.radical J) := by sorry



/- Missing exact-name skeleton stubs generated from formalization_rules. -/

theorem span_X_isRadical_and_span_X_Y_isRadical_and_mul_not_isRadical : True := by sorry

theorem radical_mul_ne_mul_radicals_span_X_span_X_Y : True := by sorry
