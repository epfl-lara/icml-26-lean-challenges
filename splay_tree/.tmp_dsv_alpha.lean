import Challenges.Splay_Tree.Def_Ackermann
open KlazarAckermann

-- ============================================================
-- helpers: alpha / Nat.find  plumbing
-- ============================================================

lemma F_omega_exists (n : ℕ) : ∃ m, n ≤ F_omega m := by
  induction n
  · use 0; simp [F_omega, F]
  · rename_i n ih
    use n + 1
    have := @F_inflationary (n + 1) (n + 1) (by omega) (by omega)
    rw [<- F_omega] at this
    linarith

lemma alpha_spec (n : ℕ) : n ≤ F_omega (alpha n) := by
  have h := F_omega_exists n
  have h_eq : alpha n = @Nat.find (P_omega n) (P_omega_decidable n) h := by
    unfold alpha; rfl
  rw [h_eq]; exact Nat.find_spec h

-- ============================================================
-- 1. F_one
-- ============================================================
lemma F_one (n : ℕ) : F 1 n = 2 * n := by rfl

-- ============================================================
-- 2. F_succ_succ
-- ============================================================
lemma F_succ_succ (k n : ℕ) : F (k + 2) n = (F (k + 1) ·)^[n] 1 := by rfl

-- ============================================================
-- 3. F_mono_right
-- ============================================================

lemma iterate_ge_one {k m : ℕ} (hk : 1 ≤ k) : 1 ≤ (F k ·)^[m] 1 := by
  induction m
  · exact le_rfl
  · rename_i m ih
    rw [show (F k ·)^[m+1] 1 = F k ((F k ·)^[m] 1) by rw [Function.iterate_succ_apply']]
    exact F_iterate_ge_one hk ih

lemma iterate_step_ge {k n : ℕ} (hk : 1 ≤ k) :
    (F k ·)^[n] 1 ≤ (F k ·)^[n + 1] 1 := by
  rw [Function.iterate_succ_apply']
  have h_ge : 1 ≤ (F k ·)^[n] 1 := iterate_ge_one hk
  have h_inf : (F k ·)^[n] 1 < F k ((F k ·)^[n] 1) := F_inflationary hk h_ge
  linarith

lemma iterate_le_iterate_of_le {k a b : ℕ} (hk : 1 ≤ k) (hab : a ≤ b) :
    (F k ·)^[a] 1 ≤ (F k ·)^[b] 1 := by
  induction b generalizing a
  · have ha0 : a = 0 := by linarith
    rw [ha0]
  · rename_i b ih
    by_cases h : a ≤ b
    · have h1 := ih h
      have h2 : (F k ·)^[b] 1 ≤ (F k ·)^[b + 1] 1 := iterate_step_ge hk
      linarith
    · have ha1 : a = b + 1 := by linarith
      rw [ha1]

lemma F_mono_right : ∀ k, 1 ≤ k → ∀ {a b : ℕ}, a ≤ b → F k a ≤ F k b := by
  intro k hk a b hab
  cases k
  · contradiction
  · rename_i k
    by_cases hk0 : k = 0
    · subst hk0; simp [F]; omega
    · have k_ge_1 : k ≥ 1 := by omega
      simp [F]
      exact iterate_le_iterate_of_le k_ge_1 hab

-- ============================================================
-- 4. F_mono_left
-- ============================================================

lemma F_k_1_eq_2 {k : ℕ} (hk : 1 ≤ k) : F k 1 = 2 := by
  induction k
  · contradiction
  · rename_i k ih
    by_cases hk0 : k = 0
    · subst hk0; rfl
    · have k_ge_1 : k ≥ 1 := by omega
      have : F (k + 1) 1 = F k 1 := by simp [F]
      rw [this]
      exact ih k_ge_1

lemma F_k_n_le_iterate {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    F k n ≤ (F k ·)^[n] 1 := by
  induction n
  · linarith
  · rename_i n ih
    cases n
    · simp [F_k_1_eq_2 hk]
    · rename_i n
      have h_iter : (F k ·)^[n + 2] 1 = F k ((F k ·)^[n + 1] 1) := by
        rw [Function.iterate_succ_apply']
      have h_n2 : n + 2 ≤ F k (n + 1) := by
        have h_inf : n + 1 < F k (n + 1) := F_inflationary hk (by linarith)
        linarith
      have h_F2 : F k (n + 2) ≤ F k (F k (n + 1)) := F_mono_right k hk (by omega)
      have h_ih : F k (n + 1) ≤ (F k ·)^[n + 1] 1 := ih (by linarith)
      have h_F : F k (F k (n + 1)) ≤ F k ((F k ·)^[n + 1] 1) := F_mono_right k hk h_ih
      rw [h_iter]
      linarith

lemma F_mono_left : ∀ {j k : ℕ}, 1 ≤ j → j ≤ k → ∀ n, 1 ≤ n → F j n ≤ F k n := by
  intro j k hj hjk n hn
  have h_base : F j n ≤ F j n := le_rfl
  have h_step : ∀ (m : ℕ), j ≤ m → F j n ≤ F m n → F j n ≤ F (m + 1) n := by
    intro m hm ih
    have h_kn : F m n ≤ F (m + 1) n := by
      cases m
      · have h_j0 : j = 0 := by omega
        omega
      · rename_i m
        have hk' : 1 ≤ m + 1 := by omega
        simp [F]
        exact F_k_n_le_iterate hk' hn
    linarith
  exact Nat.le_induction h_base h_step k hjk

-- ============================================================
-- 5. F_omega_mono
-- ============================================================
lemma F_omega_zero : F_omega 0 = 0 := by rw [F_omega, F]

lemma alpha_zero_eq : alpha 0 = 0 := by
  have h1 : alpha 0 ≤ 0 := by
    unfold alpha
    apply Nat.find_le
    unfold P_omega
    rw [F_omega_zero]
    simp
  have h2 : 0 ≤ alpha 0 := by simp
  omega

lemma F_omega_mono : ∀ {a b : ℕ}, 1 ≤ a → a ≤ b → F_omega a ≤ F_omega b := by
  intro a b ha hab
  rw [F_omega, F_omega]
  have h3 : F a a ≤ F b a := F_mono_left ha hab a ha
  have h4 : F b a ≤ F b b := F_mono_right b (by omega) hab
  linarith

-- ============================================================
-- 6. alpha_le_iff
-- ============================================================
lemma alpha_le_iff (n m : ℕ) : alpha n ≤ m ↔ n ≤ F_omega m := by
  constructor
  · intro h
    have h_n_le : n ≤ F_omega (alpha n) := alpha_spec n
    have h_Fmono : F_omega (alpha n) ≤ F_omega m := by
      by_cases hn0 : n = 0
      · subst hn0
        rw [alpha_zero_eq] at h
        rw [alpha_zero_eq, F_omega_zero]
        linarith
      · have h1 : 1 ≤ alpha n := by
          have : alpha n ≠ 0 := by
            by_contra h0; rw [h0] at h_n_le; rw [F_omega_zero] at h_n_le; omega
          omega
        apply F_omega_mono h1 h
    linarith
  · intro h
    unfold alpha
    apply Nat.find_le
    unfold P_omega
    exact h

-- ============================================================
-- 7. alpha_mono
-- ============================================================
lemma alpha_mono : ∀ {a b : ℕ}, a ≤ b → alpha a ≤ alpha b := by
  intro a b hab
  by_cases ha0 : a = 0
  · subst ha0; rw [alpha_zero_eq]; simp
  · have h_alpha_a_1 : 1 ≤ alpha a := by
      have : alpha a ≠ 0 := by
        by_contra h0
        have h_a0 : a = 0 := by
          have h_spec : a ≤ F_omega (alpha a) := alpha_spec a
          rw [h0] at h_spec; rw [F_omega_zero] at h_spec; omega
        contradiction
      omega
    apply (alpha_le_iff a (alpha b)).mpr
    have h_b_le : b ≤ F_omega (alpha b) := alpha_spec b
    linarith

-- ============================================================
-- 8. alpha_F_omega_self
-- ============================================================
lemma alpha_F_omega_self (m : ℕ) : alpha (F_omega m) ≤ m := by
  unfold alpha
  apply Nat.find_le
  unfold P_omega
  exact le_rfl

-- ============================================================
-- 9. alpha_pos_of_two_le
-- ============================================================
lemma alpha_pos_of_two_le : 2 ≤ n → 1 ≤ alpha n := by
  intro h
  have : n ≠ 0 := by linarith
  have : alpha n ≠ 0 := by
    by_contra h0
    have h_spec : n ≤ F_omega (alpha n) := alpha_spec n
    rw [h0] at h_spec; rw [F_omega_zero] at h_spec; omega
  omega

-- ============================================================
-- 10. alpha_two_mul_le
-- ============================================================

lemma iterate_F1_eq_pow2 (r : ℕ) : (F 1 ·)^[r] 1 = 2 ^ r := by
  induction r
  · simp
  · rename_i r ih
    rw [show (F 1 ·)^[r+1] 1 = F 1 ((F 1 ·)^[r] 1) by rw [Function.iterate_succ_apply']]
    rw [ih]
    simp [F]
    ring

lemma F_2_eq_pow2 (x : ℕ) : F 2 x = 2 ^ x := by
  rw [show F 2 x = (F 1 ·)^[x] 1 by rfl]
  exact iterate_F1_eq_pow2 x

lemma two_x_le_pow2 {x : ℕ} (hx : 1 ≤ x) : 2 * x ≤ 2 ^ x := by
  have base : 2 * 1 ≤ 2 ^ 1 := by norm_num
  have step : ∀ (k : ℕ), 1 ≤ k → 2 * k ≤ 2 ^ k → 2 * (k + 1) ≤ 2 ^ (k + 1) := by
    intro k hk ih
    have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [this]
    have h1 : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [h1]
    omega
  exact Nat.le_induction base step x hx

lemma F_ge_two_mul {a x : ℕ} (ha : 1 ≤ a) (hx : 1 ≤ x) : 2 * x ≤ F a x := by
  cases a
  · contradiction
  · rename_i a
    cases a
    · simp [F]; omega
    · rename_i a
      have h_F2 : F 2 x ≤ F (a + 2) x := F_mono_left (by omega) (by omega) x hx
      rw [F_2_eq_pow2 x] at h_F2
      have h_pow : 2 * x ≤ 2 ^ x := two_x_le_pow2 hx
      linarith

lemma two_mul_F_omega_le_F_omega_succ {m : ℕ} (hm : 1 ≤ m) :
    2 * F_omega m ≤ F_omega (m + 1) := by
  have h1 : F_omega m = F m m := rfl
  have h2 : F_omega (m + 1) = (F m ·)^[m + 1] 1 := by
    cases m
    · linarith
    · rfl
  rw [h1, h2]
  have h_iter : (F m ·)^[m + 1] 1 = F m ((F m ·)^[m] 1) := by
    rw [Function.iterate_succ_apply']
  rw [h_iter]
  have h_F_le_iter : F m m ≤ (F m ·)^[m] 1 := F_k_n_le_iterate hm hm
  have h_two_iter : 2 * (F m ·)^[m] 1 ≤ F m ((F m ·)^[m] 1) := by
    apply F_ge_two_mul hm
    apply iterate_ge_one hm
  linarith

lemma alpha_two_mul_le (n : ℕ) : 1 ≤ n → alpha (2 * n) ≤ alpha n + 1 := by
  intro hn
  apply (alpha_le_iff (2 * n) (alpha n + 1)).mpr
  have h1 : 1 ≤ alpha n := by
    have : alpha n ≠ 0 := by
      by_contra h0
      have h_spec : n ≤ F_omega (alpha n) := alpha_spec n
      rw [h0] at h_spec; rw [F_omega_zero] at h_spec; omega
    omega
  have h2 : n ≤ F_omega (alpha n) := alpha_spec n
  have h3 : 2 * n ≤ 2 * F_omega (alpha n) := by omega
  have h4 : 2 * F_omega (alpha n) ≤ F_omega (alpha n + 1) :=
    two_mul_F_omega_le_F_omega_succ h1
  linarith

-- ============================================================
-- 11. alpha_sq_le
-- ============================================================

lemma sq_le_pow2 {x : ℕ} (hx : 4 ≤ x) : x * x ≤ 2 ^ x := by
  have base : 4 * 4 ≤ 2 ^ 4 := by norm_num
  have step : ∀ (k : ℕ), 4 ≤ k → k * k ≤ 2 ^ k → (k + 1) * (k + 1) ≤ 2 ^ (k + 1) := by
    intro k hk ih
    have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [this]
    have h1 : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
    rw [h1]
    nlinarith
  exact Nat.le_induction base step x hx

lemma F_ge_four {a x : ℕ} (ha : 2 ≤ a) (hx : 2 ≤ x) : 4 ≤ F a x := by
  have h_F2 : F 2 x ≤ F a x := F_mono_left (by omega) (by omega) x (by omega)
  rw [F_2_eq_pow2 x] at h_F2
  have : 4 ≤ 2 ^ x := by
    have base : 4 ≤ 2 ^ 2 := by norm_num
    have step : ∀ (k : ℕ), 4 ≤ 2 ^ k → 4 ≤ 2 ^ (k + 1) := by
      intro k ih
      rw [pow_succ]
      nlinarith
    exact Nat.le_induction base step x (by omega)
  linarith

lemma sq_F_omega_le_F_omega_succ {m : ℕ} (hm : 1 ≤ m) :
    F_omega m * F_omega m ≤ F_omega (m + 1) := by
  cases m
  · simp [F_omega, F]
  · rename_i m
    cases m
    · simp [F_omega, F]
    · rename_i m
      have h_sq : (F (m + 2) (m + 2)) * (F (m + 2) (m + 2)) ≤ 2 ^ (F (m + 2) (m + 2)) := by
        apply sq_le_pow2
        exact F_ge_four (by omega) (by omega)
      have h_le : (F (m + 2) (m + 2)) * (F (m + 2) (m + 2)) ≤ F (m + 2) (F (m + 2) (m + 2)) := by
        have h_a : (F (m + 2) (m + 2)) * (F (m + 2) (m + 2)) ≤ 2 ^ (F (m + 2) (m + 2)) := h_sq
        have h_b : 2 ^ (F (m + 2) (m + 2)) = F 2 (F (m + 2) (m + 2)) := by rw [F_2_eq_pow2]
        have h_c : F 2 (F (m + 2) (m + 2)) ≤ F (m + 2) (F (m + 2) (m + 2)) := by
          apply F_mono_left (by omega) (by omega)
          apply F_iterate_ge_one (by omega) (by omega)
        rw [h_b] at h_c
        linarith [h_a, h_c]
      have h_iter : F (m + 2) (F (m + 2) (m + 2)) ≤ F (m + 2) ((F (m + 2) ·)^[m + 2] 1) := by
        have h_F : F (m + 2) (m + 2) ≤ (F (m + 2) ·)^[m + 2] 1 :=
          F_k_n_le_iterate (by omega) (by omega)
        apply F_mono_right (m + 2) (by omega) h_F
      have h2 : (F (m + 2) (m + 2)) * (F (m + 2) (m + 2)) ≤ F (m + 2) ((F (m + 2) ·)^[m + 2] 1) := by
        linarith [h_le, h_iter]
      have h_L : F_omega (m + 2) = F (m + 2) (m + 2) := rfl
      have h_R : F_omega (m + 2 + 1) = F (m + 2) ((F (m + 2) ·)^[m + 2] 1) := by
        cases m + 2 with
        | zero => linarith
        | succ m => rfl
      rw [h_L, h_R]
      exact h2

lemma alpha_sq_le (n : ℕ) : 1 ≤ n → alpha (n * n) ≤ alpha n + 1 := by
  intro hn
  apply (alpha_le_iff (n * n) (alpha n + 1)).mpr
  have h1 : 1 ≤ alpha n := by
    have : alpha n ≠ 0 := by
      by_contra h0
      have h_spec : n ≤ F_omega (alpha n) := alpha_spec n
      rw [h0] at h_spec; rw [F_omega_zero] at h_spec; omega
    omega
  have h2 : n ≤ F_omega (alpha n) := alpha_spec n
  have h3 : n * n ≤ F_omega (alpha n) * F_omega (alpha n) := by
    apply Nat.mul_le_mul h2 h2
  have h4 : F_omega (alpha n) * F_omega (alpha n) ≤ F_omega (alpha n + 1) :=
    sq_F_omega_le_F_omega_succ h1
  linarith
