import Mathlib

/--
Source `docs/source.tex`, line 17. `LCM m` denotes the least common multiple of
all positive integers up to the natural number `m`. This draft uses Mathlib's
the finite-set LCM over `Finset.Icc 1 m`, the interval of integers from `1`
through `m`.
-/
def LCM (m : ℕ) : ℕ :=
  (Finset.Icc 1 m).lcm id

/--
Source proof: unfold the definition of `LCM` and reduce positivity to the fact
that the LCM of the positive integers up to `m` is not zero.
Prover notes: unfold `LCM`; prove positivity of the finite LCM over `Finset.Icc 1 m`.
-/
lemma LCM_gt_0 (m : ℕ) : 0 < LCM m := by
  rw [LCM]
  exact Nat.pos_of_ne_zero (by
    rw [Finset.lcm_ne_zero_iff]
    intro a ha
    exact Nat.ne_of_gt ((Finset.mem_Icc.mp ha).1))

/--
Source proof: show the LCM is monotone by comparing the intervals `[1, m]` and
`[1, n]`; equivalently, prove the successor divisibility step and handle
`LCM 0 = LCM 1 = 1` directly.
Prover notes: unfold `LCM` and use monotonicity/inclusion facts for
the finite-set LCM over `Finset.Icc`.
-/
lemma LCM_monotone (m n : ℕ) (h : m ≤ n) : LCM m ≤ LCM n := by
  rw [LCM, LCM]
  exact Nat.le_of_dvd (by
    simpa [LCM] using LCM_gt_0 n) (Finset.lcm_mono (f := id) (by
      intro a ha
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1, le_trans (Finset.mem_Icc.mp ha).2 h⟩))

/--
Source proof: define `β'(m,n) = ∫_0^1 x^(m-1) * (1-x)^(n-m) dx`; compute it as
`1 / (m * binom n m)`, also expand it as an integer linear combination of
fractions `a_i / i` for `1 ≤ i ≤ n`. Clearing denominators with `LCM n`, since
each `i` divides `LCM n`, yields `m * binom n m ∣ LCM n`.
Prover notes: the Lean statement only records the arithmetic divisibility
claim. Existing binomial/LCM divisibility lemmas may avoid formalizing the
analytic beta-integral proof.
-/
lemma LCM_dvd_by (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    m * Nat.choose n m ∣ LCM n := by
  have hm0 : m ≠ 0 := by exact Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hm)
  have hn0 : n ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (Nat.lt_of_lt_of_le Nat.zero_lt_one hm) hmn)
  have hchoose0 : Nat.choose n m ≠ 0 := by
    exact Nat.ne_of_gt (Nat.choose_pos hmn)
  have hprod0 : m * Nat.choose n m ≠ 0 := Nat.mul_ne_zero hm0 hchoose0
  have hfactorization_le_log :
      ∀ p : ℕ, (m * Nat.choose n m).factorization p ≤ Nat.log p n := by
    intro p
    by_cases hp : p.Prime
    · rw [Nat.factorization_mul hm0 hchoose0]
      change m.factorization p + (Nat.choose n m).factorization p ≤ Nat.log p n
      have hdisj :
          Disjoint
            {i ∈ Finset.Ico 1 (Nat.log p n).succ |
              p ^ i ≤ m % p ^ i + (n - m) % p ^ i}
            {i ∈ Finset.Ico 1 (Nat.log p n).succ | p ^ i ∣ m} := by
        simp +contextual [Finset.disjoint_right, Nat.dvd_iff_mod_eq_zero,
          Nat.mod_lt _ (pow_pos hp.pos _)]
      rw [Nat.factorization_choose hp hmn (Nat.lt_add_one _),
        Nat.factorization_eq_card_pow_dvd_of_lt hp (Nat.pos_of_ne_zero hm0)
          (lt_of_le_of_lt hmn (Nat.lt_pow_succ_log_self hp.one_lt n))]
      rw [Nat.add_comm]
      rw [← Finset.card_union_of_disjoint hdisj, Finset.filter_union_right]
      have hle := (Finset.Ico 1 (Nat.log p n).succ).card_filter_le
        (fun i => p ^ i ≤ m % p ^ i + (n - m) % p ^ i ∨ p ^ i ∣ m)
      simpa using hle
    · simp [Nat.factorization_eq_zero_of_not_prime, hp]
  refine (Nat.factorization_le_iff_dvd hprod0 (Nat.ne_of_gt (LCM_gt_0 n))).mp ?_
  intro p
  by_cases hzero : (m * Nat.choose n m).factorization p = 0
  · simp [hzero]
  · have hp : p.Prime := by
      by_contra hnp
      exact hzero (Nat.factorization_eq_zero_of_not_prime (m * Nat.choose n m) hnp)
    let e := (m * Nat.choose n m).factorization p
    have he_log : e ≤ Nat.log p n := hfactorization_le_log p
    have hpow_le : p ^ e ≤ n := Nat.pow_le_of_le_log hn0 he_log
    have hpow_mem : p ^ e ∈ Finset.Icc 1 n := by
      exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (pow_ne_zero e hp.ne_zero), hpow_le⟩
    have hdvdLCM : p ^ e ∣ LCM n := by
      simpa [LCM] using (Finset.dvd_lcm (s := Finset.Icc 1 n) (f := id) hpow_mem)
    have hfac_le :=
      (Nat.factorization_le_iff_dvd (pow_ne_zero e hp.ne_zero)
        (Nat.ne_of_gt (LCM_gt_0 n))).mpr hdvdLCM
    have hpowfac : (p ^ e).factorization p = e := Nat.factorization_pow_self (n := e) hp
    have hfac_le_p : (p ^ e).factorization p ≤ (LCM n).factorization p := hfac_le p
    rw [hpowfac] at hfac_le_p
    exact hfac_le_p

/--
Source proof: check `m = 7, 8` computationally. For odd `m = 2*k + 1`, use
binomial coefficient bounds together with divisibility of suitable products by
`LCM (2*k+1)`. For even `m`, reduce to a nearby odd case using monotonicity of
`LCM`.
Prover notes: likely dependencies are `LCM_dvd_by`, `LCM_monotone`, binomial
coefficient estimates, and coprimality/divisibility facts; finite-set LCM
facts over `Finset.Icc` should preserve the exact target statement.
-/
lemma LCM_range_lower_bdd (m : ℕ) (hm : 7 ≤ m) : 2 ^ m ≤ LCM m := by
  have hodd : ∀ k : ℕ, 4 ≤ k → 2 ^ (2 * k + 2) ≤ LCM (2 * k + 1) := by
    intro k hk
    let c := Nat.choose (2 * k + 1) k
    have hdiv₁ : k * c ∣ LCM (2 * k + 1) := by
      simpa [c] using LCM_dvd_by k (2 * k + 1) (by omega) (by omega)
    have hdiv₂ : (k + 1) * c ∣ LCM (2 * k + 1) := by
      simpa [c, Nat.choose_symm_half k] using
        LCM_dvd_by (k + 1) (2 * k + 1) (by omega) (by omega)
    have hprod_dvd : k * (k + 1) * c ∣ LCM (2 * k + 1) := by
      have hlcm_dvd : Nat.lcm (k * c) ((k + 1) * c) ∣ LCM (2 * k + 1) :=
        Nat.lcm_dvd hdiv₁ hdiv₂
      have hcop : Nat.Coprime k (k + 1) := by
        simp
      have hlcm_eq : Nat.lcm (k * c) ((k + 1) * c) = k * (k + 1) * c := by
        calc
          Nat.lcm (k * c) ((k + 1) * c)
              = Nat.lcm (c * k) (c * (k + 1)) := by
                  rw [mul_comm k c, mul_comm (k + 1) c]
          _ = c * Nat.lcm k (k + 1) := by
                  rw [Nat.lcm_mul_left]
          _ = c * (k * (k + 1)) := by
                  rw [Nat.Coprime.lcm_eq_mul hcop]
          _ = k * (k + 1) * c := by
                  ring
      simpa [hlcm_eq] using hlcm_dvd
    have hc_lower : 4 ^ k ≤ (k + 1) * c := by
      calc
        4 ^ k = ∑ i ∈ Finset.range (k + 1), Nat.choose (2 * k + 1) i := by
            exact (Nat.sum_range_choose_halfway k).symm
        _ ≤ ∑ _i ∈ Finset.range (k + 1), c := by
            apply Finset.sum_le_sum
            intro i hi
            have hmid := Nat.choose_le_middle i (2 * k + 1)
            have hhalf : (2 * k + 1) / 2 = k := by
              omega
            simpa [c, hhalf] using hmid
        _ = (k + 1) * c := by
            simp
    have hpow_le : 2 ^ (2 * k + 2) ≤ k * 4 ^ k := by
      have hpow_eq : 2 ^ (2 * k + 2) = 4 * 4 ^ k := by
        rw [pow_add, pow_mul]
        norm_num
        ring
      simpa [hpow_eq] using Nat.mul_le_mul_right (4 ^ k) hk
    have htarget_le : 2 ^ (2 * k + 2) ≤ k * (k + 1) * c := by
      calc
        2 ^ (2 * k + 2) ≤ k * 4 ^ k := hpow_le
        _ ≤ k * ((k + 1) * c) := Nat.mul_le_mul_left k hc_lower
        _ = k * (k + 1) * c := by ring
    exact htarget_le.trans (Nat.le_of_dvd (LCM_gt_0 (2 * k + 1)) hprod_dvd)
  by_cases hsmall : m < 9
  · interval_cases m
    · have hdiv420 : 420 ∣ LCM 7 := by
        have hdiv₁ : 3 * Nat.choose 7 3 ∣ LCM 7 := by
          exact LCM_dvd_by 3 7 (by norm_num) (by norm_num)
        have hdiv₂ : 4 * Nat.choose 7 4 ∣ LCM 7 := by
          exact LCM_dvd_by 4 7 (by norm_num) (by norm_num)
        have hlcm_dvd : Nat.lcm (3 * Nat.choose 7 3) (4 * Nat.choose 7 4) ∣ LCM 7 :=
          Nat.lcm_dvd hdiv₁ hdiv₂
        norm_num at hlcm_dvd
        exact hlcm_dvd
      have hle : 420 ≤ LCM 7 := Nat.le_of_dvd (LCM_gt_0 7) hdiv420
      omega
    · have hdiv280 : 280 ∣ LCM 8 := by
        have hdiv : 4 * Nat.choose 8 4 ∣ LCM 8 := by
          exact LCM_dvd_by 4 8 (by norm_num) (by norm_num)
        norm_num at hdiv
        exact hdiv
      have hle : 280 ≤ LCM 8 := Nat.le_of_dvd (LCM_gt_0 8) hdiv280
      omega
  · have hm9 : 9 ≤ m := by omega
    obtain ⟨k, hk⟩ | ⟨k, hk⟩ := m.even_or_odd
    · subst m
      have hk5 : 5 ≤ k := by omega
      have hkm1 : 4 ≤ k - 1 := by omega
      have hodd' := hodd (k - 1) hkm1
      have hmono : LCM (2 * (k - 1) + 1) ≤ LCM (k + k) :=
        LCM_monotone _ _ (by omega)
      suffices 2 ^ (k + k) ≤ LCM (k + k) by
        simpa [two_mul] using this
      calc
        2 ^ (k + k) = 2 ^ (2 * (k - 1) + 2) := by
            congr 1
            omega
        _ ≤ LCM (2 * (k - 1) + 1) := hodd'
        _ ≤ LCM (k + k) := hmono
    · subst m
      have hk4 : 4 ≤ k := by omega
      have hodd' := hodd k hk4
      suffices 2 ^ (k + k + 1) ≤ LCM (k + k + 1) by
        simpa [two_mul, add_assoc, add_comm, add_left_comm] using this
      calc
        2 ^ (k + k + 1) ≤ 2 ^ (2 * k + 2) := by
            apply Nat.pow_le_pow_right (by norm_num)
            omega
        _ ≤ LCM (2 * k + 1) := hodd'
        _ = LCM (k + k + 1) := by
            congr 1
            omega
