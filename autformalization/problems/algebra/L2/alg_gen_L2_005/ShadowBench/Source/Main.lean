import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.RingTheory.MvPolynomial.Ideal

/--
`S k n` is the source set of all polynomials in `k[x₁, …, xₙ]` with no zeros on
`k^n`, represented in Lean by `MvPolynomial (Fin n) k` and points `Fin n → k`.
-/
def S (k : Type*) [Field k] (n : ℕ) : Set (MvPolynomial (Fin n) k) :=
  {p | ∀ x : Fin n → k, MvPolynomial.aeval x p ≠ 0}

private lemma exists_monic_noRoot_pos_natDegree_of_not_isAlgClosed (k : Type*) [Field k]
    (hk : ¬ IsAlgClosed k) :
    ∃ p : Polynomial k, p.Monic ∧ p.natDegree ≠ 0 ∧ ∀ x : k, Polynomial.eval x p ≠ 0 := by
  classical
  by_contra h
  apply hk
  exact IsAlgClosed.of_exists_root k (by
    intro p hpmonic hpirr
    by_contra hroot
    apply h
    refine ⟨p, hpmonic, ?_, ?_⟩
    · exact ne_of_gt hpirr.natDegree_pos
    · intro x hx
      exact hroot ⟨x, hx⟩)

private lemma homogenize_mem_span_X_of_pos (k : Type*) [Field k]
    (p : Polynomial k) (d : ℕ) (hd : d ≠ 0) :
    p.homogenize d ∈ Ideal.span ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} :
      Set (MvPolynomial (Fin 2) k)) := by
  classical
  have hmem_univ : p.homogenize d ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin 2))) := by
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    have hcoeff_ne : MvPolynomial.coeff m (p.homogenize d) ≠ 0 := by
      simpa [MvPolynomial.mem_support_iff] using hm
    have hsum : m 0 + m 1 = d := by
      by_contra hne
      apply hcoeff_ne
      simp [Polynomial.coeff_homogenize, hne]
    by_cases h0 : m 0 ≠ 0
    · exact ⟨0, trivial, h0⟩
    · refine ⟨1, trivial, ?_⟩
      intro h1
      have hm0 : m 0 = 0 := not_not.mp h0
      have hd0 : d = 0 := by
        simpa [hm0, h1] using hsum.symm
      exact hd hd0
  have hset : MvPolynomial.X '' (Set.univ : Set (Fin 2)) =
      ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} : Set (MvPolynomial (Fin 2) k)) := by
    ext z
    constructor
    · rintro ⟨i, -, rfl⟩
      fin_cases i <;> simp
    · intro hz
      rcases hz with hz | hz
      · refine ⟨0, trivial, ?_⟩
        simp [hz]
      · refine ⟨1, trivial, ?_⟩
        simpa using hz.symm
  simpa [hset] using hmem_univ

private lemma eval_homogenize_second_zero_of_monic (k : Type*) [Field k]
    {p : Polynomial k} (hp : p.Monic) (a : k) :
    MvPolynomial.aeval (![a, 0] : Fin 2 → k) (p.homogenize p.natDegree) = a ^ p.natDegree := by
  classical
  rw [Polynomial.homogenize]
  simp only [MvPolynomial.aeval_eq_eval, map_sum, MvPolynomial.eval_monomial, Fin.isValue]
  rw [Finset.sum_eq_single (p.natDegree, 0)]
  · simp [hp.coeff_natDegree]
  · intro b hb hne
    have hsum : b.1 + b.2 = p.natDegree := by simpa using hb
    have hb2 : b.2 ≠ 0 := by
      intro hb20
      apply hne
      ext
      · simpa [hb20] using hsum
      · exact hb20
    simp [hb2]
  · intro hnot
    exfalso
    apply hnot
    simp

private lemma exists_binary_anisotropic_of_not_isAlgClosed (k : Type*) [Field k]
    (hk : ¬ IsAlgClosed k) :
    ∃ q : MvPolynomial (Fin 2) k,
      q ∈ Ideal.span ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} :
        Set (MvPolynomial (Fin 2) k)) ∧
      ∀ y : Fin 2 → k, MvPolynomial.aeval y q = 0 → y 0 = 0 ∧ y 1 = 0 := by
  classical
  rcases exists_monic_noRoot_pos_natDegree_of_not_isAlgClosed k hk with ⟨p, hpmonic, hd, hroot⟩
  refine ⟨p.homogenize p.natDegree, homogenize_mem_span_X_of_pos k p p.natDegree hd, ?_⟩
  intro y hy
  have hy1 : y 1 = 0 := by
    by_contra hy1ne
    have h_eval := Polynomial.eval_homogenize (p := p) (n := p.natDegree) (le_rfl) y hy1ne
    have hprod : Polynomial.eval (y 0 / y 1) p * y 1 ^ p.natDegree = 0 := by
      rw [← h_eval]
      simpa [MvPolynomial.aeval_eq_eval] using hy
    have hpow : y 1 ^ p.natDegree ≠ 0 := pow_ne_zero _ hy1ne
    have heval0 : Polynomial.eval (y 0 / y 1) p = 0 := by
      exact mul_eq_zero.mp hprod |>.resolve_right hpow
    exact hroot (y 0 / y 1) heval0
  have hy0 : y 0 = 0 := by
    by_contra hy0ne
    have hvec : (![y 0, 0] : Fin 2 → k) = y := by
      funext i
      fin_cases i <;> simp [hy1]
    have hq0 : MvPolynomial.aeval (![y 0, 0] : Fin 2 → k) (p.homogenize p.natDegree) = 0 := by
      simpa [hvec] using hy
    have hpow0 : y 0 ^ p.natDegree = 0 := by
      simpa [eval_homogenize_second_zero_of_monic k hpmonic] using hq0
    exact (pow_ne_zero _ hy0ne) hpow0
  exact ⟨hy0, hy1⟩

private lemma aeval_binary_mem_ideal_of_mem_span_X (k A : Type*) [Field k]
    [CommSemiring A] [Algebra k A] {J : Ideal A} {a b : A}
    (ha : a ∈ J) (hb : b ∈ J)
    {q : MvPolynomial (Fin 2) k}
    (hq : q ∈ Ideal.span ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} :
      Set (MvPolynomial (Fin 2) k))) :
    MvPolynomial.aeval (![a, b] : Fin 2 → A) q ∈ J := by
  classical
  rw [Ideal.mem_span_pair] at hq
  rcases hq with ⟨r, s, hrs⟩
  rw [← hrs]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, map_add,
    map_mul, MvPolynomial.aeval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  exact J.add_mem (J.mul_mem_left _ ha) (J.mul_mem_left _ hb)

private lemma finset_single_equation_for_common_zeros (k : Type*) [Field k] (n : ℕ)
    (q : MvPolynomial (Fin 2) k)
    (hq_span : q ∈ Ideal.span ({MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} :
      Set (MvPolynomial (Fin 2) k)))
    (hq_aniso : ∀ y : Fin 2 → k, MvPolynomial.aeval y q = 0 → y 0 = 0 ∧ y 1 = 0)
    (F : Finset (MvPolynomial (Fin n) k)) :
    ∃ g : MvPolynomial (Fin n) k,
      g ∈ Ideal.span (F : Set (MvPolynomial (Fin n) k)) ∧
      ∀ x : Fin n → k,
        MvPolynomial.aeval x g = 0 ↔
          ∀ p ∈ F, MvPolynomial.aeval x p = 0 := by
  classical
  refine Finset.induction_on F ?base ?step
  · refine ⟨0, ?_, ?_⟩
    · simp
    · intro x
      simp
  · intro a F ha ih
    rcases ih with ⟨g, hgmem, hgeq⟩
    let G : MvPolynomial (Fin n) k :=
      MvPolynomial.aeval (![a, g] : Fin 2 → MvPolynomial (Fin n) k) q
    refine ⟨G, ?mem, ?zero⟩
    · have haJ : a ∈ Ideal.span ((insert a F : Finset (MvPolynomial (Fin n) k)) : Set (MvPolynomial (Fin n) k)) := by
        exact Ideal.subset_span (by simp)
      have hgJ : g ∈ Ideal.span ((insert a F : Finset (MvPolynomial (Fin n) k)) : Set (MvPolynomial (Fin n) k)) := by
        exact Ideal.span_mono (by intro z hz; simp [hz]) hgmem
      exact aeval_binary_mem_ideal_of_mem_span_X (k := k)
        (A := MvPolynomial (Fin n) k) (J := Ideal.span ((insert a F : Finset (MvPolynomial (Fin n) k)) : Set (MvPolynomial (Fin n) k)))
        haJ hgJ hq_span
    · intro x
      have hcomp : MvPolynomial.aeval x G =
          MvPolynomial.aeval (![MvPolynomial.aeval x a, MvPolynomial.aeval x g] : Fin 2 → k) q := by
        dsimp [G]
        have h := congrArg (fun φ : MvPolynomial (Fin 2) k →ₐ[k] k => φ q)
          (MvPolynomial.comp_aeval (![a, g] : Fin 2 → MvPolynomial (Fin n) k) (MvPolynomial.aeval x))
        have hfun : (fun i : Fin 2 => (MvPolynomial.eval x) (![a, g] i)) =
            (![MvPolynomial.eval x a, MvPolynomial.eval x g] : Fin 2 → k) := by
          funext i
          fin_cases i <;> simp
        simpa [hfun, MvPolynomial.aeval_eq_eval] using h
      constructor
      · intro hG p hp
        have hq0 : MvPolynomial.aeval (![MvPolynomial.aeval x a, MvPolynomial.aeval x g] : Fin 2 → k) q = 0 := by
          simpa [hcomp] using hG
        have hz := hq_aniso _ hq0
        rw [Finset.mem_insert] at hp
        rcases hp with rfl | hpF
        · exact hz.1
        · exact (hgeq x).mp hz.2 p hpF
      · intro hall
        have ha0 : MvPolynomial.aeval x a = 0 := hall a (by simp)
        have hg0 : MvPolynomial.aeval x g = 0 := by
          exact (hgeq x).mpr (by
            intro p hp
            exact hall p (by simp [hp]))
        have hbot : MvPolynomial.aeval (![MvPolynomial.aeval x a, MvPolynomial.aeval x g] : Fin 2 → k) q ∈ (⊥ : Ideal k) := by
          exact aeval_binary_mem_ideal_of_mem_span_X (k := k) (A := k) (J := (⊥ : Ideal k))
            (by simp [ha0]) (by simp [hg0]) hq_span
        have hq0 : MvPolynomial.aeval (![MvPolynomial.aeval x a, MvPolynomial.aeval x g] : Fin 2 → k) q = 0 := by
          simpa using hbot
        simpa [hcomp] using hq0

private lemma mvPolynomial_ideal_eq_span_finset (k : Type*) [Field k] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) :
    ∃ F : Finset (MvPolynomial (Fin n) k),
      I = Ideal.span (F : Set (MvPolynomial (Fin n) k)) := by
  classical
  letI : IsNoetherianRing (MvPolynomial (Fin n) k) := MvPolynomial.isNoetherianRing_fin
  rcases (Ideal.fg_of_isNoetherianRing I) with ⟨F, hF⟩
  exact ⟨F, hF.symm⟩

private lemma exists_mem_I_inter_S_of_zeroLocus_empty (k : Type*) [Field k] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) k))
    (hZ : MvPolynomial.zeroLocus k I = ∅) :
    ∃ p : MvPolynomial (Fin n) k, p ∈ I ∧ p ∈ S k n := by
  classical
  by_cases hk : IsAlgClosed k
  · letI : IsAlgClosed k := hk
    refine ⟨1, ?_, ?_⟩
    · have hrad : I.radical = ⊤ := by
        rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k) I, hZ,
          MvPolynomial.vanishingIdeal_empty]
      have htop : I = ⊤ := Ideal.radical_eq_top.mp hrad
      rw [htop]
      simp
    · intro x
      simp
  · rcases exists_binary_anisotropic_of_not_isAlgClosed k hk with ⟨q, hq_span, hq_aniso⟩
    rcases mvPolynomial_ideal_eq_span_finset k n I with ⟨F, hF⟩
    rcases finset_single_equation_for_common_zeros k n q hq_span hq_aniso F with ⟨g, hgmem, hgeq⟩
    refine ⟨g, ?_, ?_⟩
    · rw [hF]
      exact hgmem
    · intro x hxg
      have hall : ∀ p ∈ F, MvPolynomial.aeval x p = 0 := (hgeq x).mp hxg
      have hxzero_span : x ∈ MvPolynomial.zeroLocus k (Ideal.span (F : Set (MvPolynomial (Fin n) k))) := by
        rw [MvPolynomial.zeroLocus_span]
        exact hall
      have hxzero : x ∈ MvPolynomial.zeroLocus k I := by
        simpa [hF] using hxzero_span
      rw [hZ] at hxzero
      cases hxzero

/--
Source theorem (`docs/source.tex`, `line-17`): if an ideal `I` in `k[x₁, …, xₙ]`
is disjoint from the set `S` of polynomials having no zeros on `k^n`, then its
zero locus is nonempty.

Source proof: no proof is supplied in the source document.
Proof sketch: use the contrapositive. If `MvPolynomial.zeroLocus k I = ∅`, then
produce some `p ∈ I` whose evaluations are all nonzero, giving `p ∈ S k n` and
contradicting `(I : Set _) ∩ S k n = ∅`. Unfold `MvPolynomial.mem_zeroLocus_iff`
to translate membership in the zero locus into simultaneous vanishing.
Prover notes: the statement intentionally keeps the source's arbitrary-field
quantifier; if proof search fails, check whether an additional field hypothesis is
missing from the source rather than weakening this theorem silently.
-/
theorem zeroLocus_nonempty_of_disjoint_noZeros (k : Type*) [Field k] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) k))
    (hI : (I : Set (MvPolynomial (Fin n) k)) ∩ S k n = ∅) :
    MvPolynomial.zeroLocus k I ≠ ∅ := by
  classical
  by_contra hZ
  rcases exists_mem_I_inter_S_of_zeroLocus_empty k n I hZ with ⟨p, hpI, hpS⟩
  have hpinter : p ∈ (I : Set (MvPolynomial (Fin n) k)) ∩ S k n := ⟨hpI, hpS⟩
  rw [hI] at hpinter
  cases hpinter
