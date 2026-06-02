import Mathlib

def LCM (m : ℕ) : ℕ := (Finset.Icc 1 m).lcm id

theorem LCM_gt_0 : ∀ m : ℕ, LCM m > 0 := by sorry

theorem LCM_monotone : ∀ m n : ℕ, m ≤ n → LCM m ≤ LCM n := by sorry

theorem LCM_dvd_by : ∀ m n : ℕ, 1 ≤ m → m ≤ n → (m * Nat.choose n m) ∣ LCM n := by sorry

theorem LCM_range_lower_bdd : ∀ m : ℕ, 7 ≤ m → 2^m ≤ LCM m := by sorry
