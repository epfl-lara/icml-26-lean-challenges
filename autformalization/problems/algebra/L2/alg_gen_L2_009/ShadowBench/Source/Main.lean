import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.MvPolynomial.Ideal
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
  rw [Ideal.radical_mul, Ideal.radical_inf]

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
  classical
  have hspanXY_eq : spanXYIdeal k = MvPolynomial.idealOfVars (Fin 2) k := by
    rw [spanXYIdeal, MvPolynomial.idealOfVars]
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact Ideal.subset_span (Set.mem_range_self (0 : Fin 2))
      · exact Ideal.subset_span (Set.mem_range_self (1 : Fin 2))
    · apply Ideal.span_le.mpr
      rintro z ⟨i, rfl⟩
      fin_cases i <;> exact Ideal.subset_span (by simp)
  have hX_le_idealOfVars : spanXIdeal k ≤ MvPolynomial.idealOfVars (Fin 2) k := by
    rw [spanXIdeal, MvPolynomial.idealOfVars]
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact Ideal.subset_span (Set.mem_range_self (0 : Fin 2))
  have hXrad : Ideal.IsRadical (spanXIdeal k) := by
    have hprime : (spanXIdeal k).IsPrime := by
      rw [spanXIdeal]
      exact (Ideal.span_singleton_prime (p := (X (0 : Fin 2) : PolynomialRingXY k))
        (MvPolynomial.X_ne_zero (R := k) (0 : Fin 2))).2
        (MvPolynomial.X_prime (R := k) (i := (0 : Fin 2)))
    exact hprime.isRadical
  have hIdealOfVars_rad : (MvPolynomial.idealOfVars (Fin 2) k).IsRadical := by
    rw [Ideal.isRadical_iff_pow_one_lt 2 (by norm_num)]
    intro p hp
    have hp1 : p ^ 2 ∈ MvPolynomial.idealOfVars (Fin 2) k ^ 1 := by
      simpa using hp
    have hc2 : MvPolynomial.constantCoeff (p ^ 2) = 0 := by
      have hcoeff :=
        (MvPolynomial.mem_pow_idealOfVars_iff' (σ := Fin 2) (R := k) 1 (p ^ 2)).1
          hp1 0 (by simp)
      simpa [MvPolynomial.constantCoeff_eq] using hcoeff
    have hc : MvPolynomial.constantCoeff p = 0 := by
      have hsq : (MvPolynomial.constantCoeff p) ^ 2 = 0 := by
        simpa using hc2
      have hmul : MvPolynomial.constantCoeff p * MvPolynomial.constantCoeff p = 0 := by
        simpa [pow_two] using hsq
      rcases mul_eq_zero.mp hmul with h | h <;> exact h
    have hp_mem1 : p ∈ MvPolynomial.idealOfVars (Fin 2) k ^ 1 := by
      rw [MvPolynomial.mem_pow_idealOfVars_iff']
      intro x hx
      have hx0 : x = 0 := by
        exact (Finsupp.degree_eq_zero_iff x).mp (Nat.lt_one_iff.mp hx)
      subst x
      simpa [MvPolynomial.constantCoeff_eq] using hc
    simpa using hp_mem1
  have hXYrad : Ideal.IsRadical (spanXYIdeal k) := by
    rw [hspanXY_eq]
    exact hIdealOfVars_rad
  have hXsq_mem_prod : (X (0 : Fin 2) : PolynomialRingXY k) ^ 2 ∈
      spanXIdeal k * spanXYIdeal k := by
    have hx_mem_X : (X (0 : Fin 2) : PolynomialRingXY k) ∈ spanXIdeal k := by
      rw [spanXIdeal]
      exact Ideal.subset_span (by simp)
    have hx_mem_XY : (X (0 : Fin 2) : PolynomialRingXY k) ∈ spanXYIdeal k := by
      rw [spanXYIdeal]
      exact Ideal.subset_span (by simp)
    simpa [pow_two] using Ideal.mul_mem_mul hx_mem_X hx_mem_XY
  have hprod_le_pow : spanXIdeal k * spanXYIdeal k ≤
      MvPolynomial.idealOfVars (Fin 2) k ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_le.mpr (by
      intro a ha b hb
      exact Ideal.mul_mem_mul (hX_le_idealOfVars ha) ((le_of_eq hspanXY_eq) hb))
  have hX_not_mem_pow : (X (0 : Fin 2) : PolynomialRingXY k) ∉
      MvPolynomial.idealOfVars (Fin 2) k ^ 2 := by
    intro hmem
    have hdeg : 2 ≤ Finsupp.degree (Finsupp.single (0 : Fin 2) 1) :=
      (MvPolynomial.mem_pow_idealOfVars_iff (σ := Fin 2) (R := k) 2 (X (0 : Fin 2))).1
        hmem (Finsupp.single (0 : Fin 2) 1) (by simp)
    simp at hdeg
  have hnotrad : ¬ Ideal.IsRadical (spanXIdeal k * spanXYIdeal k) := by
    intro hrad
    have hx_mem_prod : (X (0 : Fin 2) : PolynomialRingXY k) ∈
        spanXIdeal k * spanXYIdeal k :=
      hrad ⟨2, hXsq_mem_prod⟩
    exact hX_not_mem_pow (hprod_le_pow hx_mem_prod)
  exact ⟨hXrad, hXYrad, hnotrad⟩

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
  classical
  intro h
  rcases span_X_isRadical_and_span_X_Y_isRadical_and_mul_not_isRadical k with
    ⟨hXrad, hXYrad, hnotrad⟩
  apply hnotrad
  have hRHS_eq :
      Ideal.radical (spanXIdeal k) * Ideal.radical (spanXYIdeal k) =
        spanXIdeal k * spanXYIdeal k := by
    rw [hXrad.radical, hXYrad.radical]
  rw [← hRHS_eq, ← h]
  exact Ideal.radical_isRadical (spanXIdeal k * spanXYIdeal k)
