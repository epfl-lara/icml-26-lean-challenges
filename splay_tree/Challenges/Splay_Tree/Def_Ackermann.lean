/-
Copyright (c) 14.01.2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Klazar's Ackermann Hierarchy

This file defines the specific Ackermann hierarchy used in Klazar's proof for N_5(n).
We cannot use `Mathlib.Computability.Ackermann` because the base cases and recursion
scheme differ (e.g., Klazar uses F_1(n) = 2n, while standard Ackermann is n+2).
-/

namespace KlazarAckermann

/--
The function F_k(n) defined recursively.
Base case: F_1(n) = 2n.
Recursive step: F_k(n) = F_{k-1}^(n) (1) (n applications of F_{k-1}).
-/
def F (k n : ℕ) : ℕ :=
  match k with
  | 0 => 0 -- Arbitrary base for 0, Klazar starts at k=1.
  | 1 => 2 * n
  | k' + 1 => (F k' ·)^[n] 1

-- For k ≥ 1, n ≥ 1, 1 ≤ F k n.
lemma F_iterate_ge_one {k n : ℕ} (hk : k ≥ 1) (hn : n ≥ 1) :
    1 ≤ F k n := by
  induction k generalizing n
  · contradiction
  · rename_i k ih
    by_cases hk0 : k = 0
    · subst hk0
      simp [F]
      linarith
    · have k_ge_1 : k ≥ 1 := by omega
      simp [F]
      have iter_ge_one (m : ℕ) : 1 ≤ (F k ·)^[m] 1 := by
        induction m with
        | zero => simp
        | succ m ihm =>
          rw [Function.iterate_succ_apply']
          apply ih k_ge_1 ihm
      apply iter_ge_one

-- From the above result, we deduce that for k ≥ 1 and n ≥ 1, F_k(n) is inflationary (n < F_k(n)).
lemma F_inflationary {k n : ℕ} (hk : k ≥ 1) (hn : n ≥ 1) :
    n < F k n := by
  induction k generalizing n
  · simp_all only [ge_iff_le, nonpos_iff_eq_zero, one_ne_zero]
  · rename_i k ih
    by_cases hk : k = 0
    · simp_all only [ge_iff_le, nonpos_iff_eq_zero, one_ne_zero, IsEmpty.forall_iff,
      zero_add, le_refl, F]
      linarith
    · have k_pos : k ≥ 1 := by omega
      simp_all [F]
      induction n
      · contradiction
      · rename_i n ih_n
        by_cases h_n : n = 0
        · simp_all only [nonpos_iff_eq_zero, one_ne_zero, Function.iterate_zero, id_eq,
          zero_lt_one, implies_true, zero_add, le_refl, Function.iterate_one]
        · have n_pos : n ≥ 1 := by omega
          have : (n < (F k .)^[n] 1) ∧ ((F k .)^[n] 1 < F k ((F k .)^[n] 1)):= by
            constructor
            · apply ih_n n_pos
            · apply ih
              have := @F_iterate_ge_one (k+1) n (by linarith) n_pos
              simp_all only [forall_const, le_add_iff_nonneg_left, zero_le, ge_iff_le, F]
          rw [Function.iterate_succ_apply']
          linarith

-- The diagonal Ackermann function F_ω(n) = F_n(n).
def F_omega (n : ℕ) : ℕ := F n n

-- Let the boolean property P_ω(n, m) be defined as F_ω(m) ≥ n.
def P_omega (n : ℕ) : ℕ → Prop := fun m => n ≤ F_omega m

-- This property is decidable because F_omega is computable and ≤ is decidable on ℕ.
instance P_omega_decidable (n m : ℕ) : Decidable (P_omega n m) := by
  unfold P_omega
  infer_instance

-- The inverse diagonal function α(n) = α_ω(n) = min { m : F_omega (m) ≥ n }.
def alpha (n : ℕ) : ℕ :=
  @Nat.find (P_omega n) (P_omega_decidable n) (by
    have : ∃ m, n ≤ F_omega m := by
      induction n
      · use 0; simp only [zero_le]
      · rename_i n _
        use n + 1
        have := @F_inflationary (n + 1) (n + 1) (by omega) (by omega)
        rw [<- F_omega] at this
        linarith
    exact this)

end KlazarAckermann
