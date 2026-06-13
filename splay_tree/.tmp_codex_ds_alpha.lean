import Challenges.Splay_Tree.Def_Ackermann

/-!
M2 staging for the finite-sequence Davenport--Schinzel formalization.

This file records the directly usable arithmetic facts about the shipped
Klazar Ackermann hierarchy.  In particular, the inverse diagonal `alpha` is a
`Nat.find`, so its specification and minimality are available without adding
any new assumptions.
-/

namespace CodexDS
namespace AckermannFacts

open KlazarAckermann

-- from dsv
lemma F_omega_exists (n : ℕ) : ∃ m, n ≤ F_omega m := by
  induction n with
  | zero =>
      use 0
      simp [F_omega, F]
  | succ n _ih =>
      use n + 1
      have := @F_inflationary (n + 1) (n + 1) (by omega) (by omega)
      rw [← F_omega] at this
      linarith

-- from dsv
lemma F_one (n : ℕ) : F 1 n = 2 * n := by
  rfl

-- from dsv
lemma F_succ_succ (k n : ℕ) : F (k + 2) n = (F (k + 1) ·)^[n] 1 := by
  rfl

-- from dsv
lemma iterate_ge_one {k m : ℕ} (hk : 1 ≤ k) :
    1 ≤ (F k ·)^[m] 1 := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
      rw [show (F k ·)^[m + 1] 1 = F k ((F k ·)^[m] 1) by
        rw [Function.iterate_succ_apply']]
      exact F_iterate_ge_one hk ih

-- from dsv
lemma iterate_step_ge {k n : ℕ} (hk : 1 ≤ k) :
    (F k ·)^[n] 1 ≤ (F k ·)^[n + 1] 1 := by
  rw [Function.iterate_succ_apply']
  have h_ge : 1 ≤ (F k ·)^[n] 1 := iterate_ge_one hk
  have h_inf : (F k ·)^[n] 1 < F k ((F k ·)^[n] 1) :=
    F_inflationary hk h_ge
  linarith

-- from dsv
lemma iterate_le_iterate_of_le {k a b : ℕ} (hk : 1 ≤ k) (hab : a ≤ b) :
    (F k ·)^[a] 1 ≤ (F k ·)^[b] 1 := by
  induction b generalizing a with
  | zero =>
      have ha0 : a = 0 := by linarith
      rw [ha0]
  | succ b ih =>
      by_cases h : a ≤ b
      · have h1 : (F k ·)^[a] 1 ≤ (F k ·)^[b] 1 := ih h
        have h2 : (F k ·)^[b] 1 ≤ (F k ·)^[b + 1] 1 := iterate_step_ge hk
        linarith
      · have ha1 : a = b + 1 := by linarith
        rw [ha1]

-- from dsv
lemma F_mono_right : ∀ k, 1 ≤ k → ∀ {a b : ℕ}, a ≤ b → F k a ≤ F k b := by
  intro k hk a b hab
  cases k with
  | zero => contradiction
  | succ k =>
      by_cases hk0 : k = 0
      · subst hk0
        simp [F]
        omega
      · have k_ge_1 : k ≥ 1 := by omega
        simp [F]
        exact iterate_le_iterate_of_le k_ge_1 hab

-- from dsv
lemma F_k_1_eq_2 {k : ℕ} (hk : 1 ≤ k) : F k 1 = 2 := by
  induction k with
  | zero => contradiction
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst hk0
        rfl
      · have k_ge_1 : k ≥ 1 := by omega
        have : F (k + 1) 1 = F k 1 := by simp [F]
        rw [this]
        exact ih k_ge_1

-- from dsv
lemma F_k_n_le_iterate {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    F k n ≤ (F k ·)^[n] 1 := by
  induction n with
  | zero => linarith
  | succ n ih =>
      cases n with
      | zero =>
          simp [F_k_1_eq_2 hk]
      | succ n =>
          have h_iter : (F k ·)^[n + 2] 1 =
              F k ((F k ·)^[n + 1] 1) := by
            rw [Function.iterate_succ_apply']
          have h_n2 : n + 2 ≤ F k (n + 1) := by
            have h_inf : n + 1 < F k (n + 1) :=
              F_inflationary hk (by linarith)
            linarith
          have h_F2 : F k (n + 2) ≤ F k (F k (n + 1)) :=
            F_mono_right k hk (by omega)
          have h_ih : F k (n + 1) ≤ (F k ·)^[n + 1] 1 :=
            ih (by linarith)
          have h_F : F k (F k (n + 1)) ≤
              F k ((F k ·)^[n + 1] 1) :=
            F_mono_right k hk h_ih
          rw [h_iter]
          linarith

-- from dsv
lemma F_mono_left :
    ∀ {j k : ℕ}, 1 ≤ j → j ≤ k → ∀ n, 1 ≤ n → F j n ≤ F k n := by
  intro j k hj hjk n hn
  have h_base : F j n ≤ F j n := le_rfl
  have h_step :
      ∀ (m : ℕ), j ≤ m → F j n ≤ F m n → F j n ≤ F (m + 1) n := by
    intro m hm ih
    have h_kn : F m n ≤ F (m + 1) n := by
      cases m with
      | zero =>
          have h_j0 : j = 0 := by omega
          omega
      | succ m =>
          have hk' : 1 ≤ m + 1 := by omega
          simp [F]
          exact F_k_n_le_iterate hk' hn
    linarith
  exact Nat.le_induction h_base h_step k hjk

-- from dsv
lemma F_omega_zero : F_omega 0 = 0 := by
  rw [F_omega, F]

-- from dsv
lemma alpha_zero_eq : alpha 0 = 0 := by
  have h1 : alpha 0 ≤ 0 := by
    unfold alpha
    apply Nat.find_le
    unfold P_omega
    simp [F_omega_zero]
  have h2 : 0 ≤ alpha 0 := by simp
  omega

-- from dsv
lemma F_omega_mono : ∀ {a b : ℕ}, 1 ≤ a → a ≤ b → F_omega a ≤ F_omega b := by
  intro a b ha hab
  rw [F_omega, F_omega]
  have h3 : F a a ≤ F b a := F_mono_left ha hab a ha
  have h4 : F b a ≤ F b b := F_mono_right b (by omega) hab
  linarith

theorem alpha_spec (n : ℕ) :
    n ≤ F_omega (alpha n) := by
  change P_omega n (alpha n)
  unfold alpha
  exact @Nat.find_spec (P_omega n) (P_omega_decidable n) _

theorem alpha_min {n m : ℕ} (h : n ≤ F_omega m) :
    alpha n ≤ m := by
  change @Nat.find (P_omega n) (P_omega_decidable n) _ ≤ m
  exact @Nat.find_min' (P_omega n) (P_omega_decidable n) _ m h

theorem alpha_le_iff_exists_le (n m : ℕ) :
    alpha n ≤ m ↔ ∃ r ≤ m, n ≤ F_omega r := by
  change @Nat.find (P_omega n) (P_omega_decidable n) _ ≤ m ↔ ∃ r ≤ m, P_omega n r
  exact @Nat.find_le_iff (P_omega n) (P_omega_decidable n) _ m

theorem alpha_Fomega_le (m : ℕ) :
    alpha (F_omega m) ≤ m :=
  alpha_min (n := F_omega m) (m := m) le_rfl

theorem alpha_le_of_le_Fomega {n m : ℕ} (h : n ≤ F_omega m) :
    alpha n ≤ m :=
  alpha_min h

theorem alpha_zero_eq_zero :
    alpha 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact alpha_min (n := 0) (m := 0) (by simp)

theorem alpha_one_le_one :
    alpha 1 ≤ 1 := by
  apply alpha_min (n := 1) (m := 1)
  unfold F_omega KlazarAckermann.F
  norm_num

theorem one_le_Fomega_self {m : ℕ} (hm : 1 ≤ m) :
    1 ≤ F_omega m := by
  exact KlazarAckermann.F_iterate_ge_one (k := m) (n := m) hm hm

theorem Fomega_inflationary {m : ℕ} (hm : 1 ≤ m) :
    m < F_omega m := by
  exact KlazarAckermann.F_inflationary (k := m) (n := m) hm hm

theorem alpha_succ_le_self_of_Fomega_ge {n m : ℕ}
    (h : n + 1 ≤ F_omega m) :
    alpha (n + 1) ≤ m :=
  alpha_min h

theorem alpha_le_self_add_one (n : ℕ) :
    alpha n ≤ n + 1 := by
  apply alpha_min (n := n) (m := n + 1)
  cases n with
  | zero =>
      simp
  | succ n =>
      have hlt :
          n + 2 < F_omega (n + 2) := by
        exact Fomega_inflationary (m := n + 2) (by omega)
      have hle : n + 1 ≤ F_omega (n + 2) := by omega
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hle

-- from dsv
lemma alpha_le_iff (n m : ℕ) : alpha n ≤ m ↔ n ≤ F_omega m := by
  constructor
  · intro h
    have h_n_le : n ≤ F_omega (alpha n) := by
      have h_spec := Nat.find_spec (@F_omega_exists n)
      have h_eq :
          alpha n =
            @Nat.find (P_omega n) (P_omega_decidable n) (F_omega_exists n) := by
        unfold alpha
        rfl
      rw [h_eq]
      exact h_spec
    have h_Fmono : F_omega (alpha n) ≤ F_omega m := by
      by_cases hn0 : n = 0
      · subst hn0
        rw [alpha_zero_eq] at h
        rw [alpha_zero_eq, F_omega_zero]
        linarith
      · have h1 : 1 ≤ alpha n := by
          have : alpha n ≠ 0 := by
            by_contra h0
            rw [h0] at h_n_le
            rw [F_omega_zero] at h_n_le
            omega
          omega
        apply F_omega_mono h1 h
    linarith
  · intro h
    unfold alpha
    apply Nat.find_le
    unfold P_omega
    exact h

-- from dsv
lemma alpha_mono : ∀ {a b : ℕ}, a ≤ b → alpha a ≤ alpha b := by
  intro a b hab
  by_cases ha0 : a = 0
  · subst ha0
    rw [alpha_zero_eq]
    simp
  · have h_alpha_a_1 : 1 ≤ alpha a := by
      have : alpha a ≠ 0 := by
        by_contra h0
        have h_spec : a ≤ F_omega (alpha a) := by
          have h_spec := Nat.find_spec (F_omega_exists a)
          have h_eq :
              alpha a =
                @Nat.find (P_omega a) (P_omega_decidable a) (F_omega_exists a) := by
            unfold alpha
            rfl
          rw [h_eq]
          exact h_spec
        rw [h0] at h_spec
        rw [F_omega_zero] at h_spec
        omega
      omega
    apply (alpha_le_iff a (alpha b)).mpr
    have h_b_le : b ≤ F_omega (alpha b) := by
      have h_spec := Nat.find_spec (F_omega_exists b)
      have h_eq :
          alpha b =
            @Nat.find (P_omega b) (P_omega_decidable b) (F_omega_exists b) := by
        unfold alpha
        rfl
      rw [h_eq]
      exact h_spec
    linarith

-- from dsv
lemma alpha_F_omega_self (m : ℕ) : alpha (F_omega m) ≤ m := by
  unfold alpha
  apply Nat.find_le
  unfold P_omega
  exact le_rfl

-- from dsv
lemma alpha_pos_of_two_le {n : ℕ} : 2 ≤ n → 1 ≤ alpha n := by
  intro h
  have : n ≠ 0 := by linarith
  have : alpha n ≠ 0 := by
    by_contra h0
    have h_spec : n ≤ F_omega (alpha n) := by
      have h_spec := Nat.find_spec (F_omega_exists n)
      have h_eq :
          alpha n =
            @Nat.find (P_omega n) (P_omega_decidable n) (F_omega_exists n) := by
        unfold alpha
        rfl
      rw [h_eq]
      exact h_spec
    rw [h0] at h_spec
    rw [F_omega_zero] at h_spec
    omega
  omega

/-- The tiny padding inequality used by the conditional M3 shell: any bound
with the target right-hand side can be transported through a larger constant. -/
theorem target_bound_mono_const {C D m len : ℕ}
    (hCD : C ≤ D)
    (h : len ≤ C * (m + 1) * (alpha (m + 1) + 1)) :
    len ≤ D * (m + 1) * (alpha (m + 1) + 1) := by
  exact le_trans h (by
    gcongr)

#print axioms alpha_spec
#print axioms F_mono_right
#print axioms F_mono_left
#print axioms F_omega_mono
#print axioms alpha_le_iff
#print axioms alpha_mono
#print axioms alpha_F_omega_self
#print axioms alpha_pos_of_two_le
#print axioms alpha_Fomega_le
#print axioms alpha_le_self_add_one
#print axioms target_bound_mono_const

end AckermannFacts
end CodexDS
