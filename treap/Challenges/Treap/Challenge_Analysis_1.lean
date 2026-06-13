/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Collodel, Sorrachai Yingchareonthawornchai
-/

import Challenges.Treap.Def_Analysis

open MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {n : ℕ}

-- Calculate the expected value of being an ancestor
private def intervalGood {n : ℕ} (j k a : Fin n) (ω : Equiv.Perm (Fin n)) : Prop :=
  ∀ i ∈ Finset.Icc (min j k) (max j k), i ≠ a → ω i < ω a

set_option linter.unusedVariables false in
private noncomputable def goodWeight {n : ℕ} (j k a : Fin n)
    (ω : Equiv.Perm (Fin n)) (c : ℝ) : ℝ := by
  classical
  exact if intervalGood j k a ω then c else 0

private lemma ancestor_condition_iff_intervalGood {n : ℕ} (j k : Fin n)
    (ω : Equiv.Perm (Fin n)) :
    (∀ i : Fin n, j ≤ i ∨ k ≤ i → i ≤ j ∨ i ≤ k → ¬ i = j → ω i < ω j) ↔
      intervalGood j k j ω := by
  constructor
  · intro h i hi hne
    have hmem := (Finset.mem_Icc.mp hi)
    have hlo : j ≤ i ∨ k ≤ i := by
      simpa only [inf_le_iff] using hmem.1
    have hhi : i ≤ j ∨ i ≤ k := by
      simpa only [le_sup_iff] using hmem.2
    exact h i hlo hhi hne
  · intro h i hlo hhi hne
    have hi : i ∈ Finset.Icc (min j k) (max j k) := by
      simpa only [Finset.mem_Icc, inf_le_iff, le_sup_iff] using And.intro hlo hhi
    exact h i hi hne

private lemma interval_argmax_existsUnique {n : ℕ} (j k : Fin n)
    (ω : Equiv.Perm (Fin n)) :
    ∃! a : Fin n, a ∈ Finset.Icc (min j k) (max j k) ∧ intervalGood j k a ω := by
  classical
  let s : Finset (Fin n) := Finset.Icc (min j k) (max j k)
  have hj : j ∈ s := by
    dsimp [s]
    simp only [Finset.mem_Icc, inf_le_left, le_sup_left, and_self]
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image s (fun i => ω i) ⟨j, hj⟩
  refine ⟨a, ⟨ha, ?_⟩, ?_⟩
  · intro i hi hne
    have hi' : i ∈ s := hi
    have hle : ω i ≤ ω a := hmax i hi'
    have hne_img : ω i ≠ ω a := by
      intro heq
      exact hne (ω.injective heq)
    exact lt_of_le_of_ne hle hne_img
  · intro b hb
    rcases hb with ⟨hbmem, hbmax⟩
    by_contra hne
    have hbmem' : b ∈ s := hbmem
    have hamem : a ∈ Finset.Icc (min j k) (max j k) := ha
    have hba : ω b < ω a := by
      have hle : ω b ≤ ω a := hmax b hbmem'
      have hne_img : ω b ≠ ω a := by
        intro heq
        exact hne (ω.injective heq)
      exact lt_of_le_of_ne hle hne_img
    have hab : ω a < ω b := hbmax a hamem (by intro h; exact hne h.symm)
    exact (lt_asymm hba hab)

private lemma interval_argmax_weight_sum {n : ℕ} (j k : Fin n)
    (ω : Equiv.Perm (Fin n)) (c : ℝ) :
    (Finset.Icc (min j k) (max j k)).sum
      (fun a => goodWeight j k a ω c) = c := by
  classical
  obtain ⟨a, ⟨ha_mem, ha_max⟩, huniq⟩ := interval_argmax_existsUnique j k ω
  calc
    (Finset.Icc (min j k) (max j k)).sum
      (fun b => goodWeight j k b ω c)
        = goodWeight j k a ω c := by
          refine Finset.sum_eq_single a ?_ ?_
          · intro b hb hba
            have hnot : ¬ intervalGood j k b ω := by
              intro hbmax
              exact hba (huniq b ⟨hb, hbmax⟩)
            simp only [goodWeight, hnot, ↓reduceIte]
          · intro hnotmem
            exact (hnotmem ha_mem).elim
    _ = c := by simp only [goodWeight, ha_max, ↓reduceIte]

private def precomposeSwapEquiv {n : ℕ} (j a : Fin n) :
    Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun ω := (Equiv.swap j a).trans ω
  invFun ω := (Equiv.swap j a).trans ω
  left_inv := by
    intro ω
    ext x
    simp only [Equiv.trans_apply, Equiv.swap_apply_self]
  right_inv := by
    intro ω
    ext x
    simp only [Equiv.trans_apply, Equiv.swap_apply_self]

private lemma swap_mem_interval {n : ℕ} {j k a i : Fin n}
    (ha : a ∈ Finset.Icc (min j k) (max j k))
    (hi : i ∈ Finset.Icc (min j k) (max j k)) :
    Equiv.swap j a i ∈ Finset.Icc (min j k) (max j k) := by
  classical
  by_cases hij : i = j
  · subst i
    simpa only [Equiv.swap_apply_left, Finset.mem_Icc, inf_le_iff, le_sup_iff] using ha
  · by_cases hia : i = a
    · subst i
      have hj : j ∈ Finset.Icc (min j k) (max j k) := by
        simp only [Finset.mem_Icc, inf_le_left, le_sup_left, and_self]
      simp only [Equiv.swap_apply_right, hj]
    · have hswap : Equiv.swap j a i = i := Equiv.swap_apply_of_ne_of_ne hij hia
      simpa only [hswap, Finset.mem_Icc, inf_le_iff, le_sup_iff] using hi

private lemma intervalGood_swap {n : ℕ} (j k a : Fin n)
    (ha : a ∈ Finset.Icc (min j k) (max j k))
    (ω : Equiv.Perm (Fin n)) :
    intervalGood j k a ((Equiv.swap j a).trans ω) ↔ intervalGood j k j ω := by
  classical
  constructor
  · intro h i hi hinej
    have hmem : Equiv.swap j a i ∈ Finset.Icc (min j k) (max j k) :=
      swap_mem_interval (j := j) (k := k) (a := a) ha hi
    have hne : Equiv.swap j a i ≠ a := by
      intro hs
      rw [Equiv.swap_apply_eq_iff] at hs
      exact hinej (by simpa only [Equiv.swap_apply_right] using hs)
    have hlt := h (Equiv.swap j a i) hmem hne
    simpa only [gt_iff_lt, Equiv.trans_apply, Equiv.swap_apply_self, Equiv.swap_apply_right] using hlt
  · intro h i hi hinea
    have hmem : Equiv.swap j a i ∈ Finset.Icc (min j k) (max j k) :=
      swap_mem_interval (j := j) (k := k) (a := a) ha hi
    have hne : Equiv.swap j a i ≠ j := by
      intro hs
      rw [Equiv.swap_apply_eq_iff] at hs
      exact hinea (by simpa only [Equiv.swap_apply_left] using hs)
    have hlt := h (Equiv.swap j a i) hmem hne
    simpa only [Equiv.trans_apply, Equiv.swap_apply_right, gt_iff_lt] using hlt

private lemma intervalGood_weight_sum_eq {n : ℕ} (j k a : Fin n)
    (ha : a ∈ Finset.Icc (min j k) (max j k)) (c : ℝ) :
    (∑ ω : Equiv.Perm (Fin n), goodWeight j k a ω c) =
      (∑ ω : Equiv.Perm (Fin n), goodWeight j k j ω c) := by
  classical
  have hsum :
      (∑ ω : Equiv.Perm (Fin n), goodWeight j k j ω c) =
        (∑ ω : Equiv.Perm (Fin n), goodWeight j k a ω c) := by
    refine Fintype.sum_equiv (precomposeSwapEquiv j a)
      (fun ω : Equiv.Perm (Fin n) => goodWeight j k j ω c)
      (fun ω : Equiv.Perm (Fin n) => goodWeight j k a ω c) ?_
    intro ω
    change goodWeight j k j ω c = goodWeight j k a ((Equiv.swap j a).trans ω) c
    by_cases hgood : intervalGood j k j ω
    · have hg2 : intervalGood j k a ((Equiv.swap j a).trans ω) :=
        (intervalGood_swap j k a ha ω).mpr hgood
      simp only [goodWeight, hgood, ↓reduceIte, hg2]
    · have hg2 : ¬ intervalGood j k a ((Equiv.swap j a).trans ω) := by
        intro hg
        exact hgood ((intervalGood_swap j k a ha ω).mp hg)
      simp only [goodWeight, hgood, ↓reduceIte, hg2]
  exact hsum.symm

theorem prob_is_ancestor (j k : Fin n) :
  ∫ ω, isAncestor j k ω ∂P = 1 / (Finset.Icc (min j k) (max j k)).card := by
  classical
  let s : Finset (Fin n) := Finset.Icc (min j k) (max j k)
  let c : ℝ := ((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹)
  let p : Fin n → ℝ := fun a => ∑ ω : Equiv.Perm (Fin n), goodWeight j k a ω c
  have htotal : s.sum p = 1 := by
    calc
      s.sum p = ∑ ω : Equiv.Perm (Fin n), s.sum (fun a => goodWeight j k a ω c) := by
        dsimp [p]
        rw [Finset.sum_comm]
      _ = ∑ ω : Equiv.Perm (Fin n), c := by
        apply Finset.sum_congr rfl
        intro ω hω
        exact interval_argmax_weight_sum j k ω c
      _ = 1 := by
        dsimp [c]
        have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
          exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin n)) ≠ 0)
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ne_eq, hcard, not_false_eq_true, mul_inv_cancel₀]
  have hjmem : j ∈ s := by
    dsimp [s]
    simp only [Finset.mem_Icc, inf_le_left, le_sup_left, and_self]
  have hcollapse : (s.card : ℝ) * p j = 1 := by
    have hconst : s.sum (fun _ : Fin n => p j) = (s.card : ℝ) * p j := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    calc
      (s.card : ℝ) * p j = s.sum (fun _ : Fin n => p j) := hconst.symm
      _ = s.sum p := by
        apply Finset.sum_congr rfl
        intro a ha
        dsimp [p]
        exact (intervalGood_weight_sum_eq j k a ha c).symm
      _ = 1 := htotal
  have hcard_s : (s.card : ℝ) ≠ 0 := by
    have hpos : 0 < s.card := Finset.card_pos.mpr ⟨j, hjmem⟩
    exact_mod_cast (Nat.ne_of_gt hpos)
  have hpj : p j = 1 / (s.card : ℝ) := by
    rw [← hcollapse]
    field_simp [hcard_s]
  simpa only [P, permPMF, isAncestor, Finset.mem_Icc, inf_le_iff, le_sup_iff, ne_eq, gt_iff_lt, and_imp,
    ancestor_condition_iff_intervalGood, PMF.integral_eq_sum, PMF.ofFintype_apply, perm_prob, one_div, toReal_inv,
    toReal_natCast, smul_eq_mul, mul_ite, mul_one, mul_zero, Fin.card_Icc, Fin.coe_max, Fin.coe_min, goodWeight,
    s, p, c] using hpj
