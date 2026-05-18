import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.BigOperators

set_option linter.style.longLine false

/-!
# ShadowBench algebra/L2/alg_gen_L2_005

Formalization of `docs/source.tex`, line 16.  The source defines the subset `S`
of polynomials in `k[x_1, ..., x_n]` with no zeros in `k^n`, then asks for
nonemptiness of `V(I)` when an ideal `I` is disjoint from `S`.
-/

universe u

/--
The source subset `S`: polynomials over the field `k` in `n` variables that have
no zero on `k^n`.  The polynomial ring `k[x_1, ..., x_n]` is represented as
`MvPolynomial (Fin n) k`, and points of `k^n` are represented as functions
`Fin n → k`.
-/
def S (k : Type u) [Field k] (n : ℕ) : Set (MvPolynomial (Fin n) k) :=
  {p | ∀ x : Fin n → k, MvPolynomial.eval x p ≠ 0}

private lemma exists_finset_span_eq_mvPolynomial
    (k : Type u) [Field k] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) :
    ∃ G : Finset (MvPolynomial (Fin n) k),
      Ideal.span (G : Set (MvPolynomial (Fin n) k)) = I := by
  classical
  haveI : IsNoetherianRing (MvPolynomial (Fin n) k) := inferInstance
  have hfg : I.FG := Ideal.fg_of_isNoetherianRing I
  obtain ⟨G, hGfin, hGspan⟩ := (Submodule.fg_def (R := MvPolynomial (Fin n) k) (M := MvPolynomial (Fin n) k)).mp hfg
  use hGfin.toFinset
  rw [Set.Finite.coe_toFinset]
  exact hGspan

private lemma exists_monic_pos_degree_no_root_of_not_isAlgClosed
    (k : Type u) [Field k] (hK : ¬ IsAlgClosed k) :
    ∃ P : Polynomial k,
      P.Monic ∧ 0 < P.natDegree ∧ ∀ a : k, Polynomial.eval a P ≠ 0 := by
  have h : ∃ P : Polynomial k, 0 < P.natDegree ∧ ∀ a : k, Polynomial.eval a P ≠ 0 := by
    by_contra h
    push_neg at h
    have : IsAlgClosed k := IsAlgClosed.of_exists_root k (fun p _ hp => h p (Irreducible.natDegree_pos hp))
    contradiction
  rcases h with ⟨P, hPdeg, hPnoroot⟩
  have hPne : P ≠ 0 := by
    by_contra h0
    rw [h0] at hPdeg
    simp at hPdeg
  use P * Polynomial.C ((P.leadingCoeff)⁻¹)
  constructor
  · exact Polynomial.monic_mul_leadingCoeff_inv hPne
  constructor
  · rw [Polynomial.natDegree_mul_C]
    · exact hPdeg
    · exact inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hPne)
  · intro a
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    apply mul_ne_zero
    · exact hPnoroot a
    · exact inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hPne)

private lemma pow_mem_of_mem {R : Type u} [CommSemiring R] {I : Ideal R} {x : R} (hx : x ∈ I) : ∀ n > 0, x ^ n ∈ I := by
  intro n hn
  induction n with
  | zero => linarith
  | succ n ih =>
    cases n with
    | zero =>
      simpa only [zero_add, pow_one] using hx
    | succ n =>
      have h1 : x ^ (n + 1) ∈ I := ih (by linarith)
      rw [pow_succ, mul_comm]
      exact Ideal.mul_mem_left I x h1

private lemma exists_combiner_mem_span_pair_zero_iff
    (k : Type u) [Field k] (n : ℕ)
    (P : Polynomial k) (hPmonic : P.Monic)
    (hPpos : 0 < P.natDegree)
    (hPnoroot : ∀ a : k, Polynomial.eval a P ≠ 0)
    (p q : MvPolynomial (Fin n) k) :
    ∃ r : MvPolynomial (Fin n) k,
      r ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin n) k)) ∧
        ∀ x : Fin n → k,
          MvPolynomial.eval x r = 0 ↔
            MvPolynomial.eval x p = 0 ∧ MvPolynomial.eval x q = 0 := by
  let d := P.natDegree
  let r : MvPolynomial (Fin n) k :=
    ∑ i ∈ Finset.range (d + 1), MvPolynomial.C (P.coeff i) * p ^ i * q ^ (d - i)
  use r
  constructor
  · -- Show r ∈ Ideal.span {p, q}
    have hpq : p ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin n) k)) := by
      apply Ideal.subset_span
      simp
    have hqp : q ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin n) k)) := by
      apply Ideal.subset_span
      simp
    apply Ideal.sum_mem
    intro i hi
    have hi_le : i ≤ d := by
      have : i < d + 1 := Finset.mem_range.mp hi
      omega
    by_cases hi0 : i = 0
    · -- i = 0, term is C (P.coeff 0) * q^d
      rw [hi0]
      simp only [pow_zero, mul_one, tsub_zero]
      have hqd : q ^ d ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin n) k)) := pow_mem_of_mem hqp d (by omega)
      exact Ideal.mul_mem_left _ (MvPolynomial.C (P.coeff 0)) hqd
    · -- i > 0, term has p^i factor
      have : 0 < i := by omega
      have hpi : p ^ i ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin n) k)) := pow_mem_of_mem hpq i (by omega)
      have h1 : MvPolynomial.C (P.coeff i) * p ^ i ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin n) k)) :=
        Ideal.mul_mem_left _ (MvPolynomial.C (P.coeff i)) hpi
      have h2 : q ^ (d - i) * (MvPolynomial.C (P.coeff i) * p ^ i) ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin n) k)) :=
        Ideal.mul_mem_left _ (q ^ (d - i)) h1
      have hterm : MvPolynomial.C (P.coeff i) * p ^ i * q ^ (d - i) = q ^ (d - i) * (MvPolynomial.C (P.coeff i) * p ^ i) := by ring
      rw [hterm]
      exact h2
  · -- Show zero locus equivalence
    intro x
    have heval : MvPolynomial.eval x r =
        ∑ i ∈ Finset.range (d + 1), P.coeff i * (MvPolynomial.eval x p) ^ i * (MvPolynomial.eval x q) ^ (d - i) := by
      simp [r]
    rw [heval]
    constructor
    · -- Forward: if eval r = 0, then both eval p = 0 and eval q = 0
      intro hr0
      by_cases hq : MvPolynomial.eval x q = 0
      · -- If eval q = 0
        have hsplit : ∑ i ∈ Finset.range (d + 1), P.coeff i * (MvPolynomial.eval x p) ^ i * (MvPolynomial.eval x q) ^ (d - i) =
            (∑ i ∈ Finset.range d, P.coeff i * (MvPolynomial.eval x p) ^ i * (MvPolynomial.eval x q) ^ (d - i)) + (MvPolynomial.eval x p) ^ d := by
          rw [Finset.sum_range_succ]
          have hdd : d - d = 0 := by omega
          rw [hdd, pow_zero, mul_one, hPmonic.coeff_natDegree]
          ring
        rw [hsplit] at hr0
        have h0 : ∀ i ∈ Finset.range d, P.coeff i * (MvPolynomial.eval x p) ^ i * (MvPolynomial.eval x q) ^ (d - i) = 0 := by
          intro i hi
          have : d - i ≠ 0 := by
            have : i < d := Finset.mem_range.mp hi
            omega
          have : (MvPolynomial.eval x q) ^ (d - i) = 0 := by
            rw [hq]
            exact zero_pow this
          rw [this]
          ring
        have hsum0 : ∑ i ∈ Finset.range d, P.coeff i * (MvPolynomial.eval x p) ^ i * (MvPolynomial.eval x q) ^ (d - i) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          exact h0 i hi
        have hp0 : (MvPolynomial.eval x p) ^ d = 0 := by
          rw [hsum0, zero_add] at hr0
          exact hr0
        constructor
        · exact eq_zero_of_pow_eq_zero hp0
        · exact hq
      · -- If eval q ≠ 0
        have hr0' : ∑ i ∈ Finset.range (d + 1), P.coeff i * (MvPolynomial.eval x p / MvPolynomial.eval x q) ^ i = 0 := by
          have h1 : MvPolynomial.eval x q ≠ 0 := hq
          have h2 : ∑ i ∈ Finset.range (d + 1), P.coeff i * (MvPolynomial.eval x p) ^ i * (MvPolynomial.eval x q) ^ (d - i) = 0 := hr0
          have h3 : MvPolynomial.eval x q ^ d ≠ 0 := by
            exact pow_ne_zero d h1
          have h4 : MvPolynomial.eval x q ^ d * ∑ i ∈ Finset.range (d + 1), P.coeff i * (MvPolynomial.eval x p / MvPolynomial.eval x q) ^ i =
              ∑ i ∈ Finset.range (d + 1), P.coeff i * (MvPolynomial.eval x p) ^ i * (MvPolynomial.eval x q) ^ (d - i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr
            · rfl
            · intro i hi
              have hi_le : i ≤ d := by
                have : i < d + 1 := Finset.mem_range.mp hi
                omega
              have hterm : MvPolynomial.eval x q ^ d * (P.coeff i * (MvPolynomial.eval x p / MvPolynomial.eval x q) ^ i) =
                  P.coeff i * (MvPolynomial.eval x p) ^ i * (MvPolynomial.eval x q) ^ (d - i) := by
                have hdiv : (MvPolynomial.eval x p / MvPolynomial.eval x q) ^ i = (MvPolynomial.eval x p) ^ i * ((MvPolynomial.eval x q)⁻¹) ^ i := by
                  rw [div_eq_mul_inv, mul_pow]
                rw [hdiv]
                have hpow : (MvPolynomial.eval x q) ^ d = (MvPolynomial.eval x q) ^ i * (MvPolynomial.eval x q) ^ (d - i) := by
                  rw [← pow_add]
                  congr
                  omega
                rw [hpow]
                have hinv : (MvPolynomial.eval x q) ^ i * ((MvPolynomial.eval x q)⁻¹) ^ i = 1 := by
                  rw [← mul_pow]
                  simp [h1]
                have : (MvPolynomial.eval x q) ^ i * (MvPolynomial.eval x q) ^ (d - i) * (P.coeff i * ((MvPolynomial.eval x p) ^ i * ((MvPolynomial.eval x q)⁻¹) ^ i)) =
                    P.coeff i * (MvPolynomial.eval x p) ^ i * ((MvPolynomial.eval x q) ^ i * ((MvPolynomial.eval x q)⁻¹) ^ i) * (MvPolynomial.eval x q) ^ (d - i) := by ring
                rw [this, hinv]
                ring
              exact hterm
          have h5 : MvPolynomial.eval x q ^ d * ∑ i ∈ Finset.range (d + 1), P.coeff i * (MvPolynomial.eval x p / MvPolynomial.eval x q) ^ i = 0 := by
            rw [h4]
            exact h2
          have h6 : ∑ i ∈ Finset.range (d + 1), P.coeff i * (MvPolynomial.eval x p / MvPolynomial.eval x q) ^ i = 0 := by
            have h7 : MvPolynomial.eval x q ^ d ≠ 0 := h3
            have h8 : MvPolynomial.eval x q ^ d * ∑ i ∈ Finset.range (d + 1), P.coeff i * (MvPolynomial.eval x p / MvPolynomial.eval x q) ^ i = 0 := h5
            have : ∑ i ∈ Finset.range (d + 1), P.coeff i * (MvPolynomial.eval x p / MvPolynomial.eval x q) ^ i = 0 := by
              apply (mul_eq_zero.mp h8).resolve_left
              exact h7
            exact this
          exact h6
        have hroot : Polynomial.eval (MvPolynomial.eval x p / MvPolynomial.eval x q) P = 0 := by
          simpa only [Polynomial.eval_eq_sum_range, d] using hr0'
        have hcontr := hPnoroot (MvPolynomial.eval x p / MvPolynomial.eval x q)
        contradiction
    · -- Backward: if both eval p = 0 and eval q = 0, then eval r = 0
      rintro ⟨hp0, hq0⟩
      have h0 : ∀ i ∈ Finset.range (d + 1), P.coeff i * (MvPolynomial.eval x p) ^ i * (MvPolynomial.eval x q) ^ (d - i) = 0 := by
        intro i hi
        by_cases hi0 : i = 0
        · rw [hi0, hp0, hq0]
          have h1 : d - 0 > 0 := by omega
          have h2 : (0 : k) ^ (d - 0) = 0 := by
            rw [zero_pow]
            omega
          rw [h2]
          ring
        · rw [hp0, hq0]
          have h1 : 0 < i := by omega
          have h2 : (0 : k) ^ i = 0 := by
            rw [zero_pow]
            omega
          rw [h2]
          ring
      rw [Finset.sum_eq_zero]
      intro i hi
      exact h0 i hi

private lemma exists_single_poly_mem_span_finset_zero_iff
    (k : Type u) [Field k] (n : ℕ)
    (P : Polynomial k) (hPmonic : P.Monic)
    (hPpos : 0 < P.natDegree)
    (hPnoroot : ∀ a : k, Polynomial.eval a P ≠ 0)
    (G : Finset (MvPolynomial (Fin n) k)) :
    ∃ r : MvPolynomial (Fin n) k,
      r ∈ Ideal.span (G : Set (MvPolynomial (Fin n) k)) ∧
        ∀ x : Fin n → k,
          MvPolynomial.eval x r = 0 ↔
            ∀ g ∈ G, MvPolynomial.eval x g = 0 := by
  classical
  induction G using Finset.induction_on with
  | empty =>
    use 0
    constructor
    · exact Ideal.zero_mem _
    · intro x
      simp
  | @insert p G' hpG' ih =>
    rcases ih with ⟨r', hr'mem, hr'zero⟩
    rcases exists_combiner_mem_span_pair_zero_iff k n P hPmonic hPpos hPnoroot p r' with ⟨r, hrmem, hrzero⟩
    use r
    constructor
    · -- Show r ∈ Ideal.span (insert p G')
      have h1 : r ∈ Ideal.span ({p, r'} : Set (MvPolynomial (Fin n) k)) := hrmem
      have hp_mem : p ∈ Ideal.span ((insert p G' : Finset (MvPolynomial (Fin n) k)) : Set (MvPolynomial (Fin n) k)) := by
        exact Ideal.subset_span (by simp)
      have hr'_mem : r' ∈ Ideal.span ((insert p G' : Finset (MvPolynomial (Fin n) k)) : Set (MvPolynomial (Fin n) k)) := by
        apply Ideal.span_mono ?_ hr'mem
        intro g hg
        simp [hg]
      have h2 : Ideal.span ({p, r'} : Set (MvPolynomial (Fin n) k)) ≤ Ideal.span ((insert p G' : Finset (MvPolynomial (Fin n) k)) : Set (MvPolynomial (Fin n) k)) := by
        apply Ideal.span_le.mpr
        intro x hx
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with (rfl | rfl)
        · exact hp_mem
        · exact hr'_mem
      exact h2 h1
    · -- Show zero locus equivalence
      intro x
      rw [hrzero x]
      constructor
      · -- Forward
        rintro ⟨hp0, hr'0⟩
        intro g hg
        rw [Finset.mem_insert] at hg
        rcases hg with (rfl | hg)
        · exact hp0
        · exact hr'zero x |>.mp hr'0 g hg
      · -- Backward
        intro h
        constructor
        · exact h p (by simp)
        · apply hr'zero x |>.mpr
          intro g hg
          exact h g (by simp [hg])

private lemma exists_mem_I_inter_S_of_empty_zeroLocus_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) k))
    (hZ : (MvPolynomial.zeroLocus k I) = ∅) :
    ∃ p : MvPolynomial (Fin n) k, p ∈ I ∧ p ∈ S k n := by
  have hrad : MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k I) = I.radical := by
    apply MvPolynomial.vanishingIdeal_zeroLocus_eq_radical
  have h1rad : (1 : MvPolynomial (Fin n) k) ∈ I.radical := by
    rw [← hrad, hZ, MvPolynomial.vanishingIdeal_empty]
    trivial
  have h1I : (1 : MvPolynomial (Fin n) k) ∈ I := by
    rcases Ideal.mem_radical_iff.mp h1rad with ⟨m, hm⟩
    simpa using hm
  use 1
  constructor
  · exact h1I
  · intro x
    simp

private lemma exists_mem_I_inter_S_of_empty_zeroLocus
    (k : Type u) [Field k] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) k))
    (hZ : (MvPolynomial.zeroLocus k I) = ∅) :
    ∃ p : MvPolynomial (Fin n) k, p ∈ I ∧ p ∈ S k n := by
  classical
  by_cases hAlg : IsAlgClosed k
  · letI := hAlg
    exact exists_mem_I_inter_S_of_empty_zeroLocus_isAlgClosed k n I hZ
  · -- k is not algebraically closed
    rcases exists_monic_pos_degree_no_root_of_not_isAlgClosed k hAlg with ⟨P, hPmonic, hPpos, hPnoroot⟩
    rcases exists_finset_span_eq_mvPolynomial k n I with ⟨G, hGspan⟩
    rcases exists_single_poly_mem_span_finset_zero_iff k n P hPmonic hPpos hPnoroot G with ⟨r, hrmem, hrzero⟩
    use r
    constructor
    · -- Show r ∈ I
      rw [← hGspan]
      exact hrmem
    · -- Show r ∈ S k n
      intro x
      by_contra hr0
      have hgen : ∀ g ∈ G, MvPolynomial.eval x g = 0 := by
        apply (hrzero x).mp hr0
      have hx : x ∈ MvPolynomial.zeroLocus k I := by
        rw [← hGspan, MvPolynomial.mem_zeroLocus_iff]
        intro p hp
        have hspan_vanish : Ideal.span (G : Set (MvPolynomial (Fin n) k)) ≤
            RingHom.ker (MvPolynomial.eval x) := by
          apply Ideal.span_le.mpr
          intro g hg
          exact hgen g (by simpa using hg)
        exact hspan_vanish hp
      rw [hZ] at hx
      exact hx

/--
Source label `line-16` (`docs/source.tex`, lines 16--18): if `I` is an ideal
in `k[x_1, ..., x_n]` such that `I ∩ S = ∅`, then `V(I) ≠ ∅`.

Source proof: the source gives no separate proof beyond the problem statement.
Proof sketch: extend `I`, using Zorn/localization at the multiplicative set `S`,
to a maximal ideal still disjoint from `S`.  Zariski's lemma makes the residue
field algebraic over `k`; if any residue coordinate were not represented by an
element of `k`, its minimal polynomial would give an element of `S` in the
maximal ideal.  The resulting `k`-valued coordinates are a common zero of `I`.
Prover notes: `MvPolynomial.zeroLocus` is Mathlib's zero-locus definition, and
`MvPolynomial.mem_zeroLocus_iff` unfolds membership.  The definition `S` unfolds
to `∀ x : Fin n → k, MvPolynomial.eval x p ≠ 0`.
-/
theorem zeroLocus_nonempty_of_disjoint_S
    (k : Type u) [Field k] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) k))
    (hI : ((I : Set (MvPolynomial (Fin n) k)) ∩ S k n) = ∅) :
    (MvPolynomial.zeroLocus k I).Nonempty := by
  by_contra h
  have hZ : MvPolynomial.zeroLocus k I = ∅ := by
    exact Set.eq_empty_of_forall_notMem (fun x hx => h ⟨x, hx⟩)
  rcases exists_mem_I_inter_S_of_empty_zeroLocus k n I hZ with ⟨p, hpI, hpS⟩
  have : p ∈ ((I : Set (MvPolynomial (Fin n) k)) ∩ S k n) := ⟨hpI, hpS⟩
  rw [hI] at this
  exact this
