import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/--
Source theorem `line-17` from `docs/source.tex`.

Source proof: the document gives no proof.  The intended argument is that
principal ideal containment reverses divisibility: `Ideal.span {x} ≤ Ideal.span {y}`
is equivalent to `y ∣ x`.  Therefore containment of `⟨f,g⟩` in `⟨h⟩`
encodes that `h` divides both generators, while minimality among principal ideals
encodes that every common divisor `d` has `⟨h⟩ ≤ ⟨d⟩`, equivalently `d ∣ h`.
Prover notes: use `Ideal.span_singleton_le_span_singleton` and `Ideal.span_le`
to shuttle between divisibility of generators and inclusion of singleton/pair spans.
-/
theorem isGCD_iff_span_is_least_principal_above_span_pair
    (k : Type*) [Field k] (n : ℕ) (f g h : MvPolynomial (Fin n) k) :
    (h ∣ f ∧ h ∣ g ∧
        ∀ d : MvPolynomial (Fin n) k, d ∣ f → d ∣ g → d ∣ h) ↔
      (Ideal.span ({f, g} : Set (MvPolynomial (Fin n) k)) ≤
          Ideal.span ({h} : Set (MvPolynomial (Fin n) k)) ∧
        ∀ h' : MvPolynomial (Fin n) k,
          Ideal.span ({f, g} : Set (MvPolynomial (Fin n) k)) ≤
              Ideal.span ({h'} : Set (MvPolynomial (Fin n) k)) →
            Ideal.span ({h} : Set (MvPolynomial (Fin n) k)) ≤
              Ideal.span ({h'} : Set (MvPolynomial (Fin n) k))) := by
  sorry
