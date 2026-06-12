import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

private lemma span_pair_le_span_singleton_iff_dvd
    {R : Type*} [CommSemiring R] (f g h : R) :
    Ideal.span ({f, g} : Set R) ≤ Ideal.span ({h} : Set R) ↔ h ∣ f ∧ h ∣ g := by
  constructor
  · intro hle
    constructor
    · exact Ideal.span_singleton_le_span_singleton.1 <| by
        rw [Ideal.span_singleton_le_iff_mem]
        exact hle (Ideal.subset_span (by simp))
    · exact Ideal.span_singleton_le_span_singleton.1 <| by
        rw [Ideal.span_singleton_le_iff_mem]
        exact hle (Ideal.subset_span (by simp))
  · intro hfg
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact (Ideal.span_singleton_le_span_singleton.2 hfg.1) (Ideal.subset_span (by simp))
    · exact (Ideal.span_singleton_le_span_singleton.2 hfg.2) (Ideal.subset_span (by simp))

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
  constructor
  · intro hgcd
    rcases hgcd with ⟨hhf, hhg, hcommon⟩
    constructor
    · exact (span_pair_le_span_singleton_iff_dvd f g h).2 ⟨hhf, hhg⟩
    · intro h' hpair
      have hh'f : h' ∣ f := ((span_pair_le_span_singleton_iff_dvd f g h').1 hpair).1
      have hh'g : h' ∣ g := ((span_pair_le_span_singleton_iff_dvd f g h').1 hpair).2
      exact Ideal.span_singleton_le_span_singleton.2 (hcommon h' hh'f hh'g)
  · intro hleast
    have hfg : h ∣ f ∧ h ∣ g :=
      (span_pair_le_span_singleton_iff_dvd f g h).1 hleast.1
    refine ⟨hfg.1, hfg.2, ?_⟩
    intro d hdf hdg
    exact Ideal.span_singleton_le_span_singleton.1
      (hleast.2 d ((span_pair_le_span_singleton_iff_dvd f g d).2 ⟨hdf, hdg⟩))
