import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Nullstellensatz

open scoped BigOperators
open MvPolynomial

variable {σ : Type*} {k K : Type*} [Field k] [Field K] [Algebra k K]

/--
Source `docs/source.tex`, theorem `line-17`, first claim.

Source proof: if `I₁ ⊆ I₂` and a point vanishes on every polynomial in `I₂`, then it
vanishes on every polynomial in `I₁` by applying the ideal inclusion.
Prover notes: unfold `MvPolynomial.zeroLocus` or use `MvPolynomial.mem_zeroLocus_iff`; the
hypothesis `h` changes membership in `I₁` into membership in `I₂`.
-/
theorem zeroLocus_subset_of_ideal_le
    {I₁ I₂ : Ideal (MvPolynomial σ k)} (h : I₁ ≤ I₂) :
    MvPolynomial.zeroLocus K I₂ ⊆ MvPolynomial.zeroLocus K I₁ := by
  sorry

/--
Source `docs/source.tex`, theorem `line-17`, second claim.

Source proof: if `V₁ ⊆ V₂` and a polynomial vanishes on all points of `V₂`, then it
vanishes on all points of `V₁` by applying the set inclusion.
Prover notes: unfold `MvPolynomial.vanishingIdeal`; for `x ∈ V₁`, use `h x` to regard
`x` as a point of `V₂`.
-/
theorem vanishingIdeal_le_of_subset
    {V₁ V₂ : Set (σ → K)} (h : V₁ ⊆ V₂) :
    MvPolynomial.vanishingIdeal k V₂ ≤ MvPolynomial.vanishingIdeal k V₁ := by
  sorry

/--
Source `docs/source.tex`, theorem `line-17`, final claim.

Source proof: one inclusion follows from `I ⊆ √I` and the inclusion-reversing property.
For the converse, if `x` vanishes on `I` and `p ∈ √I`, choose a positive power of `p`
lying in `I`; evaluating gives a power of `p(x)` equal to zero, hence `p(x)=0` over a
field.
Prover notes: use `zeroLocus_subset_of_ideal_le` for the easy direction; for the other
direction use `Ideal.mem_radical_iff`, evaluation of powers, and a field/no-zero-divisor
power-zero lemma.
-/
theorem zeroLocus_radical_eq_zeroLocus
    (I : Ideal (MvPolynomial σ k)) :
    MvPolynomial.zeroLocus K I.radical = MvPolynomial.zeroLocus K I := by
  sorry
