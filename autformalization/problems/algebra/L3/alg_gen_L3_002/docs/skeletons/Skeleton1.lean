import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Nilpotent.Lemmas

open scoped BigOperators
open Polynomial

theorem ideal_xsq_add_one_radical_and_zeroLocus_empty : 
  let I : Ideal (Polynomial ℝ) := Ideal.span {X^2 + 1}
  (I = Ideal.radical I) ∧ 
  ({x : ℝ | (X^2 + 1 : Polynomial ℝ).eval x = 0} = ∅) := by sorry
