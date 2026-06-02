/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Collodel, Sorrachai Yingchareonthawornchai
-/

import Challenges.Treap.Challenge_Analysis_1

open MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {n : ℕ}

-- Calculate the expected depth
private lemma harmonic_range_real (m : ℕ) :
    (∑ i ∈ Finset.range m, (((i + 1 : ℕ) : ℝ)⁻¹)) = (harmonic m : ℝ) := by
  simp [harmonic]

private lemma sum_range_left_harmonic (p : ℕ) :
    (∑ x ∈ Finset.range (p + 1), (((p + 1 - x : ℕ) : ℝ)⁻¹)) =
      (harmonic (p + 1) : ℝ) := by
  rw [← harmonic_range_real (p + 1)]
  rw [← Finset.sum_range_reflect (fun j => (((j + 1 : ℕ) : ℝ)⁻¹)) (p + 1)]
  apply Finset.sum_congr rfl
  intro x hx
  have hxlt : x < p + 1 := Finset.mem_range.mp hx
  have h : p - x + 1 = p + 1 - x := by omega
  simp [h]

private lemma sum_range_tail_harmonic_inv (r : ℕ) :
    (∑ i ∈ Finset.range r, (((i + 2 : ℕ) : ℝ)⁻¹)) = (harmonic (r + 1) : ℝ) - 1 := by
  rw [harmonic, Finset.sum_range_succ']
  simp [add_comm, add_left_comm]

private lemma sum_range_inv_max_min_eq (N p : ℕ) (hp : p < N) :
    (∑ x ∈ Finset.range N, (((max x p + 1 - min x p : ℕ) : ℝ)⁻¹)) =
      (harmonic (p + 1) : ℝ) + ((harmonic (N - p) : ℝ) - 1) := by
  have hsplit : N = (p + 1) + (N - (p + 1)) := by omega
  conv_lhs => rw [hsplit]
  rw [Finset.sum_range_add]
  have hleft :
      (∑ x ∈ Finset.range (p + 1),
          (((max x p + 1 - min x p : ℕ) : ℝ)⁻¹)) =
        (harmonic (p + 1) : ℝ) := by
    rw [← sum_range_left_harmonic p]
    apply Finset.sum_congr rfl
    intro x hx
    have hxlt : x < p + 1 := Finset.mem_range.mp hx
    have hxle : x ≤ p := Nat.lt_succ_iff.mp hxlt
    simp [max_eq_right hxle, min_eq_left hxle]
  have hright :
      (∑ x ∈ Finset.range (N - (p + 1)),
          (((max (p + 1 + x) p + 1 - min (p + 1 + x) p : ℕ) : ℝ)⁻¹)) =
        (harmonic (N - p) : ℝ) - 1 := by
    calc
      (∑ x ∈ Finset.range (N - (p + 1)),
          (((max (p + 1 + x) p + 1 - min (p + 1 + x) p : ℕ) : ℝ)⁻¹)) =
          (∑ x ∈ Finset.range (N - (p + 1)), (((x + 2 : ℕ) : ℝ)⁻¹)) := by
            apply Finset.sum_congr rfl
            intro x hx
            have hle : p ≤ p + 1 + x := by omega
            have hden : p + 1 + x + 1 - p = x + 2 := by omega
            simp [max_eq_left hle, min_eq_right hle, hden]
      _ = (harmonic (N - (p + 1) + 1) : ℝ) - 1 := by
            exact sum_range_tail_harmonic_inv (N - (p + 1))
      _ = (harmonic (N - p) : ℝ) - 1 := by
            have hr : N - (p + 1) + 1 = N - p := by omega
            rw [hr]
  rw [hleft, hright]

private lemma harmonic_mono_real {a b : ℕ} (h : a ≤ b) :
    (harmonic a : ℝ) ≤ (harmonic b : ℝ) := by
  induction b, h using Nat.le_induction with
  | base => rfl
  | succ b hle ih =>
      rw [harmonic_succ]
      norm_num
      exact le_trans ih (le_add_of_nonneg_right (by positivity))

private lemma sum_range_inv_max_min_le (N p : ℕ) (hp : p < N) :
    (∑ x ∈ Finset.range N, (((max x p + 1 - min x p : ℕ) : ℝ)⁻¹)) ≤
      1 + 2 * Real.log N := by
  rw [sum_range_inv_max_min_eq N p hp]
  have hp1 : p + 1 ≤ N := Nat.succ_le_iff.mpr hp
  have hNp : N - p ≤ N := Nat.sub_le N p
  have h1 : (harmonic (p + 1) : ℝ) ≤ (harmonic N : ℝ) := harmonic_mono_real hp1
  have h2 : (harmonic (N - p) : ℝ) ≤ (harmonic N : ℝ) := harmonic_mono_real hNp
  have hlog : (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
  nlinarith

private lemma fin_interval_card_min_max (j k : Fin n) :
    (Finset.Icc (min j k) (max j k)).card = max (j : ℕ) (k : ℕ) + 1 - min (j : ℕ) (k : ℕ) := by
  rw [Fin.card_Icc]
  rfl

private lemma fin_sum_ancestor_probs_eq_range (k : Fin n) :
    (∑ j : Fin n, (1 / ((Finset.Icc (min j k) (max j k)).card : ℝ))) =
      ∑ x ∈ Finset.range n, (((max x (k : ℕ) + 1 - min x (k : ℕ) : ℕ) : ℝ)⁻¹) := by
  classical
  calc
    (∑ j : Fin n, (1 / ((Finset.Icc (min j k) (max j k)).card : ℝ))) =
        ∑ j : Fin n, (((max (j : ℕ) (k : ℕ) + 1 - min (j : ℕ) (k : ℕ) : ℕ) : ℝ)⁻¹) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [fin_interval_card_min_max j k]
          simp [one_div]
    _ = ∑ x ∈ Finset.range n, (((max x (k : ℕ) + 1 - min x (k : ℕ) : ℕ) : ℝ)⁻¹) := by
          exact
            Fin.sum_univ_eq_sum_range
              (fun x : ℕ =>
                (((max x (k : ℕ) + 1 - min x (k : ℕ) : ℕ) : ℝ)⁻¹))
              n

theorem expected_depth (k : Fin n) :
    ∫ ω, depth k ω ∂P ≤ 1 + 2 * Real.log n := by
  classical
  calc
    ∫ ω, depth k ω ∂P = ∑ j : Fin n, ∫ ω, isAncestor j k ω ∂P := by
      simpa [depth] using
        (MeasureTheory.integral_finset_sum (s := (Finset.univ : Finset (Fin n)))
          (f := fun j ω => isAncestor j k ω)
          (by
            intro j hj
            exact MeasureTheory.Integrable.of_finite))
    _ = ∑ j : Fin n, (1 / ((Finset.Icc (min j k) (max j k)).card : ℝ)) := by
      simp [prob_is_ancestor]
    _ = ∑ x ∈ Finset.range n, (((max x (k : ℕ) + 1 - min x (k : ℕ) : ℕ) : ℝ)⁻¹) :=
      fin_sum_ancestor_probs_eq_range k
    _ ≤ 1 + 2 * Real.log n := sum_range_inv_max_min_le n (k : ℕ) k.isLt
