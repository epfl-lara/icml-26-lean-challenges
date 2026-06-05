import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.AdjoinRoot

open scoped BigOperators
open MvPolynomial

universe u

/-- Lean representation of the source polynomial ring `k[x₁, ..., xₙ]`. -/
abbrev PolynomialRingN (n : ℕ) (k : Type u) [CommSemiring k] : Type u := MvPolynomial (Fin n) k

/-- Lean representation of `k[x,y]`; `x` is `X (0 : Fin 2)` and `y` is `X (1 : Fin 2)`. -/
abbrev PolynomialRingXY (k : Type u) [CommSemiring k] : Type u := PolynomialRingN 2 k

/-- The source ideal `<x>` in the Lean model of `k[x,y]`. -/
noncomputable def spanXIdeal (k : Type*) [CommSemiring k] : Ideal (PolynomialRingXY k) :=
  Ideal.span ({X (0 : Fin 2)} : Set (PolynomialRingXY k))

/-- The source ideal `<x,y>` in the Lean model of `k[x,y]`. -/
noncomputable def spanXYIdeal (k : Type*) [CommSemiring k] : Ideal (PolynomialRingXY k) :=
  Ideal.span ({X (0 : Fin 2), X (1 : Fin 2)} : Set (PolynomialRingXY k))

/--
Source line-17, item (1): for ideals `I,J` in `k[x₁, ..., xₙ]`,
`sqrt(IJ) = sqrt(I ∩ J)`.

Source proof: the source supplies no proof paragraph. Proof sketch: use the Mathlib facts
`Ideal.radical_mul` and `Ideal.radical_inf`; both sides rewrite to
`Ideal.radical I ⊓ Ideal.radical J`. Prover notes: `PolynomialRingN n k` is the
explicit Lean bridge for `k[x₁, ..., xₙ]`.
-/
theorem radical_mul_eq_radical_inf (k : Type*) [Field k] (n : ℕ)
    (I J : Ideal (PolynomialRingN n k)) :
    Ideal.radical (I * J) = Ideal.radical (I ⊓ J) := by
  sorry

/--
Source line-17, item (2): in `k[x,y]`, with `I = <x>` and `J = <x,y>`,
`I` and `J` are radical ideals but `IJ` is not radical.

Source proof: the source supplies no proof paragraph. Proof sketch: identify `<x>`
and `<x,y>` as prime/maximal-style variable ideals, hence radical; show the product
is not radical because `x^2 ∈ <x> * <x,y>` while `x ∉ <x> * <x,y>`. Prover notes:
`spanXIdeal k` and `spanXYIdeal k` are the explicit Lean bridges for the two source
ideals.
-/
theorem span_X_isRadical_and_span_X_Y_isRadical_and_mul_not_isRadical
    (k : Type*) [Field k] :
    Ideal.IsRadical (spanXIdeal k) ∧
      Ideal.IsRadical (spanXYIdeal k) ∧
      ¬ Ideal.IsRadical (spanXIdeal k * spanXYIdeal k) := by
  sorry

/--
Source line-17, item (3): for the same ideals `I = <x>` and `J = <x,y>` in
`k[x,y]`, `sqrt(IJ) ≠ sqrt(I) sqrt(J)`.

Source proof: the source supplies no proof paragraph. Proof sketch: item (2) says
`I` and `J` are radical but `I * J` is not; if `sqrt(IJ) = sqrt(I) * sqrt(J)`, then
`I * J` would equal a radical ideal. Prover notes: alternatively, separate the two
ideals using the witness `X (0 : Fin 2)`, whose square lies in the product but which
itself does not.
-/
theorem radical_mul_ne_mul_radicals_span_X_span_X_Y (k : Type*) [Field k] :
    Ideal.radical (spanXIdeal k * spanXYIdeal k) ≠
      Ideal.radical (spanXIdeal k) * Ideal.radical (spanXYIdeal k) := by
  sorry
