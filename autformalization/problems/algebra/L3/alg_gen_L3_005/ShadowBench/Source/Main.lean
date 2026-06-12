import Mathlib
import Aesop

open MvPolynomial

noncomputable section

abbrev algGenL3005Ring (k : Type*) [CommSemiring k] := MvPolynomial (Fin 2) k

def algGenL3005_x (k : Type*) [CommSemiring k] : algGenL3005Ring k :=
  MvPolynomial.X (0 : Fin 2)

def algGenL3005_y (k : Type*) [CommSemiring k] : algGenL3005Ring k :=
  MvPolynomial.X (1 : Fin 2)

def algGenL3005_I (k : Type*) [CommSemiring k] : Ideal (algGenL3005Ring k) :=
  Ideal.span ({algGenL3005_x k ^ 2, algGenL3005_x k * algGenL3005_y k, algGenL3005_y k ^ 2} :
    Set (algGenL3005Ring k))

def algGenL3005_J (k : Type*) [CommSemiring k] : Ideal (algGenL3005Ring k) :=
  Ideal.span ({algGenL3005_x k ^ 2, algGenL3005_y k} : Set (algGenL3005Ring k))

def algGenL3005_K (k : Type*) [CommSemiring k] : Ideal (algGenL3005Ring k) :=
  Ideal.span ({algGenL3005_x k, algGenL3005_y k ^ 2} : Set (algGenL3005Ring k))

private lemma algGenL3005_idealOfVars_eq_ker_constantCoeff (k : Type*) [Field k] :
    MvPolynomial.idealOfVars (Fin 2) k =
      RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin 2) k →+* k) := by
  classical
  ext p
  rw [MvPolynomial.idealOfVars, RingHom.mem_ker]
  rw [show (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k)) =
      MvPolynomial.X '' (Set.univ : Set (Fin 2)) by
    ext q
    simp]
  rw [MvPolynomial.mem_ideal_span_X_image]
  constructor
  · intro hp
    rw [MvPolynomial.constantCoeff_eq]
    by_contra hcoeff
    have hzero : (0 : Fin 2 →₀ ℕ) ∈ p.support := by
      simpa [MvPolynomial.mem_support_iff] using hcoeff
    obtain ⟨i, _hi, hne⟩ := hp 0 hzero
    exact hne rfl
  · intro hcoeff m hm
    by_contra hno
    have hm0 : m = 0 := by
      ext i
      by_contra hi
      exact hno ⟨i, trivial, hi⟩
    have hmcoeff : p.coeff m ≠ 0 := by
      simpa [MvPolynomial.mem_support_iff] using hm
    have hcc : MvPolynomial.constantCoeff p ≠ 0 := by
      simpa [MvPolynomial.constantCoeff_eq, hm0] using hmcoeff
    exact hcc hcoeff

private lemma algGenL3005_idealOfVars_isMaximal (k : Type*) [Field k] :
    (MvPolynomial.idealOfVars (Fin 2) k).IsMaximal := by
  rw [algGenL3005_idealOfVars_eq_ker_constantCoeff]
  exact RingHom.ker_isMaximal_of_surjective
    (MvPolynomial.constantCoeff : MvPolynomial (Fin 2) k →+* k) (by
      intro a
      exact ⟨MvPolynomial.C a, by simp⟩)

private lemma algGenL3005_radical_I (k : Type*) [Field k] :
    Ideal.radical (algGenL3005_I k) = MvPolynomial.idealOfVars (Fin 2) k := by
  let m : Ideal (algGenL3005Ring k) := MvPolynomial.idealOfVars (Fin 2) k
  have hx_m : algGenL3005_x k ∈ m := by
    dsimp [m]
    rw [MvPolynomial.idealOfVars]
    exact Ideal.subset_span ⟨(0 : Fin 2), rfl⟩
  have hy_m : algGenL3005_y k ∈ m := by
    dsimp [m]
    rw [MvPolynomial.idealOfVars]
    exact Ideal.subset_span ⟨(1 : Fin 2), rfl⟩
  have hI_le_m : algGenL3005_I k ≤ m := by
    rw [algGenL3005_I, Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · simpa [pow_two] using (Ideal.mul_mem_left m (algGenL3005_x k) hx_m)
    · exact Ideal.mul_mem_left m (algGenL3005_x k) hy_m
    · simpa [pow_two] using (Ideal.mul_mem_left m (algGenL3005_y k) hy_m)
  have hrad_le_m : Ideal.radical (algGenL3005_I k) ≤ m := by
    have hm_prime : m.IsPrime := by
      dsimp [m]
      exact (algGenL3005_idealOfVars_isMaximal k).isPrime
    exact (hm_prime.radical_le_iff).2 hI_le_m
  have hx_rad : algGenL3005_x k ∈ Ideal.radical (algGenL3005_I k) := by
    rw [Ideal.mem_radical_iff]
    refine ⟨2, ?_⟩
    rw [algGenL3005_I]
    simpa [algGenL3005_x] using
      (Ideal.subset_span (by simp : (algGenL3005_x k ^ 2) ∈
        ({algGenL3005_x k ^ 2, algGenL3005_x k * algGenL3005_y k, algGenL3005_y k ^ 2} :
          Set (algGenL3005Ring k))))
  have hy_rad : algGenL3005_y k ∈ Ideal.radical (algGenL3005_I k) := by
    rw [Ideal.mem_radical_iff]
    refine ⟨2, ?_⟩
    rw [algGenL3005_I]
    simpa [algGenL3005_y] using
      (Ideal.subset_span (by simp : (algGenL3005_y k ^ 2) ∈
        ({algGenL3005_x k ^ 2, algGenL3005_x k * algGenL3005_y k, algGenL3005_y k ^ 2} :
          Set (algGenL3005Ring k))))
  have hm_le_rad : m ≤ Ideal.radical (algGenL3005_I k) := by
    dsimp [m]
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro z ⟨i, rfl⟩
    fin_cases i
    · simpa [algGenL3005_x] using hx_rad
    · simpa [algGenL3005_y] using hy_rad
  exact le_antisymm hrad_le_m hm_le_rad

/--
Source proof: Let `m = <x,y>`. The source identifies
`I = <x^2, xy, y^2>` with `m^2`, computes `radical I = m`, and uses
`k[x,y]/m ≃ k` to see that `m` is maximal. Therefore the radical of `I`
is maximal, so Mathlib's primary-ideal criterion should prove `I` is primary.
Prover notes: look for `Ideal.isPrimary_of_isMaximal_radical`; prove the radical
calculation through the square of the variable ideal.
-/
theorem I_isPrimary (k : Type*) [Field k] :
    Ideal.IsPrimary (algGenL3005_I k) := by
  apply Ideal.isPrimary_of_isMaximal_radical
  rw [algGenL3005_radical_I]
  exact algGenL3005_idealOfVars_isMaximal k

/--
Source proof: Put `J = <x^2,y>` and `K = <x,y^2>`. The source proves
`I = J ∩ K` by checking monomials: membership in both `J` and `K` means
`(a ≥ 2 or b ≥ 1)` and `(a ≥ 1 or b ≥ 2)`, hence divisibility by `x^2`,
`xy`, or `y^2`. The strict containments are witnessed by `y ∈ J \ I` and
`x ∈ K \ I`, so the displayed equality is a nontrivial infimum decomposition.
Prover notes: use monomial ideal membership lemmas for the equality, then unfold
`InfIrred` and refute it using the equality with `J` and `K` plus strictness.
-/
theorem I_not_infIrred (k : Type*) [Field k] :
    (algGenL3005_I k = algGenL3005_J k ⊓ algGenL3005_K k) ∧
      ¬ InfIrred (algGenL3005_I k) := by
  classical
  let e10 : Fin 2 →₀ ℕ := Finsupp.single (0 : Fin 2) 1
  let e01 : Fin 2 →₀ ℕ := Finsupp.single (1 : Fin 2) 1
  let e20 : Fin 2 →₀ ℕ := Finsupp.single (0 : Fin 2) 2
  let e02 : Fin 2 →₀ ℕ := Finsupp.single (1 : Fin 2) 2
  let SI : Set (Fin 2 →₀ ℕ) := {e20, e10 + e01, e02}
  let SJ : Set (Fin 2 →₀ ℕ) := {e20, e01}
  let SK : Set (Fin 2 →₀ ℕ) := {e10, e02}
  have hx2 : algGenL3005_x k ^ 2 = MvPolynomial.monomial e20 (1 : k) := by
    simp [algGenL3005_x, MvPolynomial.X_pow_eq_monomial, e20]
  have hxy : algGenL3005_x k * algGenL3005_y k = MvPolynomial.monomial (e10 + e01) (1 : k) := by
    simp [algGenL3005_x, algGenL3005_y, MvPolynomial.X, e10, e01]
  have hy2 : algGenL3005_y k ^ 2 = MvPolynomial.monomial e02 (1 : k) := by
    simp [algGenL3005_y, MvPolynomial.X_pow_eq_monomial, e02]
  have hx : algGenL3005_x k = MvPolynomial.monomial e10 (1 : k) := by
    simp [algGenL3005_x, MvPolynomial.X, e10]
  have hy : algGenL3005_y k = MvPolynomial.monomial e01 (1 : k) := by
    simp [algGenL3005_y, MvPolynomial.X, e01]
  have hI_mono :
      algGenL3005_I k =
        Ideal.span ((fun s => MvPolynomial.monomial s (1 : k)) '' SI) := by
    rw [algGenL3005_I, hx2, hxy, hy2]
    apply congrArg Ideal.span
    ext z
    simp [SI, eq_comm]
  have hJ_mono :
      algGenL3005_J k =
        Ideal.span ((fun s => MvPolynomial.monomial s (1 : k)) '' SJ) := by
    rw [algGenL3005_J, hx2, hy]
    apply congrArg Ideal.span
    ext z
    simp [SJ, eq_comm]
  have hK_mono :
      algGenL3005_K k =
        Ideal.span ((fun s => MvPolynomial.monomial s (1 : k)) '' SK) := by
    rw [algGenL3005_K, hx, hy2]
    apply congrArg Ideal.span
    ext z
    simp [SK, eq_comm]
  have he01_le_e10e01 : e01 ≤ e10 + e01 := by
    intro i
    fin_cases i <;> simp [e10, e01]
  have he01_le_e02 : e01 ≤ e02 := by
    intro i
    fin_cases i <;> simp [e01, e02]
  have he10_le_e20 : e10 ≤ e20 := by
    intro i
    fin_cases i <;> simp [e10, e20]
  have he10_le_e10e01 : e10 ≤ e10 + e01 := by
    intro i
    fin_cases i <;> simp [e10, e01]
  have h_eq : algGenL3005_I k = algGenL3005_J k ⊓ algGenL3005_K k := by
    rw [hI_mono, hJ_mono, hK_mono]
    ext p
    constructor
    · intro hp
      have hp' := (MvPolynomial.mem_ideal_span_monomial_image (x := p) (s := SI)).1 hp
      rw [Ideal.mem_inf]
      constructor
      · rw [MvPolynomial.mem_ideal_span_monomial_image]
        intro xi hxi
        obtain ⟨si, hsi, hle⟩ := hp' xi hxi
        simp only [SI, Set.mem_insert_iff, Set.mem_singleton_iff] at hsi
        rcases hsi with rfl | rfl | rfl
        · exact ⟨e20, by simp [SJ], hle⟩
        · exact ⟨e01, by simp [SJ], le_trans he01_le_e10e01 hle⟩
        · exact ⟨e01, by simp [SJ], le_trans he01_le_e02 hle⟩
      · rw [MvPolynomial.mem_ideal_span_monomial_image]
        intro xi hxi
        obtain ⟨si, hsi, hle⟩ := hp' xi hxi
        simp only [SI, Set.mem_insert_iff, Set.mem_singleton_iff] at hsi
        rcases hsi with rfl | rfl | rfl
        · exact ⟨e10, by simp [SK], le_trans he10_le_e20 hle⟩
        · exact ⟨e10, by simp [SK], le_trans he10_le_e10e01 hle⟩
        · exact ⟨e02, by simp [SK], hle⟩
    · intro hp
      rw [Ideal.mem_inf] at hp
      have hpJ := (MvPolynomial.mem_ideal_span_monomial_image (x := p) (s := SJ)).1 hp.1
      have hpK := (MvPolynomial.mem_ideal_span_monomial_image (x := p) (s := SK)).1 hp.2
      rw [MvPolynomial.mem_ideal_span_monomial_image]
      intro xi hxi
      obtain ⟨sj, hsj, hsjle⟩ := hpJ xi hxi
      obtain ⟨sk, hsk, hskle⟩ := hpK xi hxi
      simp only [SJ, Set.mem_insert_iff, Set.mem_singleton_iff] at hsj
      simp only [SK, Set.mem_insert_iff, Set.mem_singleton_iff] at hsk
      rcases hsj with rfl | rfl
      · exact ⟨e20, by simp [SI], hsjle⟩
      · rcases hsk with rfl | rfl
        · have hsum : e10 + e01 ≤ xi := by
            intro i
            fin_cases i
            · simpa [e10, e01] using hskle (0 : Fin 2)
            · simpa [e10, e01] using hsjle (1 : Fin 2)
          exact ⟨e10 + e01, by simp [SI], hsum⟩
        · exact ⟨e02, by simp [SI], hskle⟩
  have hy_not_mem_I : algGenL3005_y k ∉ algGenL3005_I k := by
    intro hyI
    have hyI' : MvPolynomial.monomial e01 (1 : k) ∈
        Ideal.span ((fun s => MvPolynomial.monomial s (1 : k)) '' SI) := by
      simpa [hy, hI_mono] using hyI
    have hsupport : e01 ∈ (MvPolynomial.monomial e01 (1 : k)).support := by
      simp
    obtain ⟨si, hsi, hsile⟩ :=
      (MvPolynomial.mem_ideal_span_monomial_image
        (x := MvPolynomial.monomial e01 (1 : k)) (s := SI)).1 hyI' e01 hsupport
    simp only [SI, Set.mem_insert_iff, Set.mem_singleton_iff] at hsi
    rcases hsi with rfl | rfl | rfl
    · have hbad := hsile (0 : Fin 2)
      simp [e20, e01] at hbad
    · have hbad := hsile (0 : Fin 2)
      simp [e10, e01] at hbad
    · have hbad := hsile (1 : Fin 2)
      simp [e02, e01] at hbad
  have hx_not_mem_I : algGenL3005_x k ∉ algGenL3005_I k := by
    intro hxI
    have hxI' : MvPolynomial.monomial e10 (1 : k) ∈
        Ideal.span ((fun s => MvPolynomial.monomial s (1 : k)) '' SI) := by
      simpa [hx, hI_mono] using hxI
    have hsupport : e10 ∈ (MvPolynomial.monomial e10 (1 : k)).support := by
      simp
    obtain ⟨si, hsi, hsile⟩ :=
      (MvPolynomial.mem_ideal_span_monomial_image
        (x := MvPolynomial.monomial e10 (1 : k)) (s := SI)).1 hxI' e10 hsupport
    simp only [SI, Set.mem_insert_iff, Set.mem_singleton_iff] at hsi
    rcases hsi with rfl | rfl | rfl
    · have hbad := hsile (0 : Fin 2)
      simp [e20, e10] at hbad
    · have hbad := hsile (1 : Fin 2)
      simp [e10, e01] at hbad
    · have hbad := hsile (1 : Fin 2)
      simp [e02, e10] at hbad
  have hy_mem_J : algGenL3005_y k ∈ algGenL3005_J k := by
    rw [algGenL3005_J]
    exact Ideal.subset_span (by simp)
  have hx_mem_K : algGenL3005_x k ∈ algGenL3005_K k := by
    rw [algGenL3005_K]
    exact Ideal.subset_span (by simp)
  have hI_le_J : algGenL3005_I k ≤ algGenL3005_J k := by
    rw [h_eq]
    exact inf_le_left
  have hI_le_K : algGenL3005_I k ≤ algGenL3005_K k := by
    rw [h_eq]
    exact inf_le_right
  have hI_ne_J : algGenL3005_I k ≠ algGenL3005_J k := by
    intro hIJ
    exact hy_not_mem_I (by simpa [hIJ] using hy_mem_J)
  have hI_ne_K : algGenL3005_I k ≠ algGenL3005_K k := by
    intro hIK
    exact hx_not_mem_I (by simpa [hIK] using hx_mem_K)
  have hI_lt_J : algGenL3005_I k < algGenL3005_J k :=
    lt_of_le_of_ne hI_le_J hI_ne_J
  have hI_lt_K : algGenL3005_I k < algGenL3005_K k :=
    lt_of_le_of_ne hI_le_K hI_ne_K
  refine ⟨h_eq, ?_⟩
  rw [not_infIrred]
  right
  exact ⟨algGenL3005_J k, algGenL3005_K k, h_eq.symm, hI_lt_J, hI_lt_K⟩
