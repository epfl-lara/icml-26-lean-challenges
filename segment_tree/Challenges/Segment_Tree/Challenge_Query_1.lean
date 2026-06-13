/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carmen Casulli, Fabio Giovanazzi, Sorrachai Yingchareonthawornchai
-/

import Challenges.Segment_Tree.Def_Query

namespace Cslib.Algorithms.Lean.TimeM

set_option autoImplicit false

private theorem array_foldl_extract_empty_of_stop_le_start {α β : Type*} (f : β → α → β)
    (xs : Array α) (init : β) {l r : ℕ} (h : r ≤ l) :
    (xs.extract l r).foldl f init = init := by
  have hx : xs.extract l r = #[] :=
    Array.extract_eq_empty_of_le (le_trans (min_le_left r xs.size) h)
  rw [hx]
  rfl

private theorem array_toList_extract_split {α : Type*} (xs : Array α) {l m r : ℕ}
    (hlm : l ≤ m) (hmr : m ≤ r) :
    (xs.extract l r).toList = (xs.extract l m).toList ++ (xs.extract m r).toList := by
  simp only [Array.toList_extract, List.extract]
  rw [← List.take_append_drop (m - l) (List.take (r - l) (List.drop l xs.toList))]
  congr 1
  · rw [List.take_take]
    have hle : m - l ≤ r - l := Nat.sub_le_sub_right hmr l
    simp only [min_eq_left hle]
  · rw [List.drop_take]
    congr 1
    · omega
    · rw [List.drop_drop]
      congr 1
      omega

private theorem array_foldl_extract_split {α β : Type*} (f : β → α → β) (xs : Array α)
    (init : β) {l m r : ℕ} (hlm : l ≤ m) (hmr : m ≤ r) :
    (xs.extract l r).foldl f init =
      (xs.extract m r).foldl f ((xs.extract l m).foldl f init) := by
  rw [← Array.foldl_toList, array_toList_extract_split xs hlm hmr, List.foldl_append]
  rw [Array.foldl_toList, Array.foldl_toList]

private theorem List.foldl_mul_assoc {α : Type*} [Monoid α] (xs : List α) (a : α) :
    xs.foldl (fun a b => a * b) a = a * xs.foldl (fun a b => a * b) 1 := by
  induction xs generalizing a with
  | nil => exact (mul_one a).symm
  | cons x xs ih =>
      change xs.foldl (fun a b => a * b) (a * x) =
        a * xs.foldl (fun a b => a * b) (1 * x)
      rw [one_mul, ih (a * x), ih x]
      rw [mul_assoc]

private theorem Array.foldl_mul_assoc {α : Type*} [Monoid α] (xs : Array α) (a : α) :
    xs.foldl (fun a b => a * b) a = a * xs.foldl (fun a b => a * b) 1 := by
  rw [← Array.foldl_toList, List.foldl_mul_assoc, Array.foldl_toList]

private theorem fold_inter_split {α : Type*} [Monoid α] (xs : Array α)
    (s L C R p q : ℕ) (hLC : L ≤ C) (hCR : C ≤ R) :
    (xs.extract (s + max L p) (s + min R q)).foldl (fun a b => a * b) 1 =
      (xs.extract (s + max L p) (s + min C q)).foldl (fun a b => a * b) 1 *
        (xs.extract (s + max C p) (s + min R q)).foldl (fun a b => a * b) 1 := by
  by_cases hqC : q ≤ C
  · have hqR : q ≤ R := le_trans hqC hCR
    have hminR : min R q = q := min_eq_right hqR
    have hminC : min C q = q := min_eq_right hqC
    have hright_empty :
        (xs.extract (s + max C p) (s + min R q)).foldl (fun a b => a * b) 1 = 1 := by
      apply array_foldl_extract_empty_of_stop_le_start
      have hCmax : C ≤ max C p := le_max_left C p
      omega
    rw [hright_empty, mul_one, hminR, hminC]
  · by_cases hpC : C ≤ p
    · have hLp : L ≤ p := le_trans hLC hpC
      have hmaxL : max L p = p := max_eq_right hLp
      have hmaxC : max C p = p := max_eq_right hpC
      have hleft_empty :
          (xs.extract (s + max L p) (s + min C q)).foldl (fun a b => a * b) 1 = 1 := by
        apply array_foldl_extract_empty_of_stop_le_start
        have hminCle : min C q ≤ C := min_le_left C q
        omega
      rw [hleft_empty, one_mul, hmaxL, hmaxC]
    · have hpC_lt : p < C := Nat.lt_of_not_ge hpC
      have hCq : C < q := Nat.lt_of_not_ge hqC
      have hmaxL : max L p ≤ C := max_le hLC hpC_lt.le
      have hCminR : C ≤ min R q := le_min hCR hCq.le
      have hsplit := array_foldl_extract_split (fun a b : α => a * b) xs 1
        (l := s + max L p) (m := s + C) (r := s + min R q) (by omega) (by omega)
      rw [hsplit]
      conv_lhs => rw [Array.foldl_mul_assoc]
      have hminC : min C q = C := min_eq_left hCq.le
      have hmaxC : max C p = C := max_eq_left hpC_lt.le
      rw [hminC, hmaxC]

private theorem array_foldl_extract_stop_min {α β : Type*} (f : β → α → β)
    (xs : Array α) (init : β) (m p q : ℕ) (hsize : xs.size = 2 * m) :
    (xs.extract (m + p) (m + min m q)).foldl f init =
      (xs.extract (m + p) (m + q)).foldl f init := by
  by_cases hqm : q ≤ m
  · rw [min_eq_right hqm]
  · have hmq : m ≤ q := Nat.le_of_not_ge hqm
    have hleft : xs.extract (m + p) (m + min m q) = xs.extract (m + p) := by
      rw [min_eq_left hmq, Array.extract_eq_extract_right]
      omega
    have hright : xs.extract (m + p) (m + q) = xs.extract (m + p) := by
      rw [Array.extract_eq_extract_right]
      omega
    rw [hleft, hright]

private theorem log2_two_mul (j : ℕ) (h0j : 0 < j) :
    Nat.log2 (2 * j) = Nat.log2 j + 1 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two,
    show 2 * j = Nat.bit false j by simp only [Nat.bit, cond_false], Nat.log_two_bit (Nat.ne_of_gt h0j)]

private theorem log2_two_mul_add_one (j : ℕ) (h0j : 0 < j) :
    Nat.log2 (2 * j + 1) = Nat.log2 j + 1 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two,
    show 2 * j + 1 = Nat.bit true j by
      simp only [Nat.add_comm, Nat.bit, cond_true],
    Nat.log_two_bit (Nat.ne_of_gt h0j)]

private theorem log2_le_of_lt_two_mul_pow {j H : ℕ} (h0j : 0 < j)
    (hj : j < 2 * 2^H) :
    Nat.log2 j ≤ H := by
  have hjpow : j < 2 ^ (H + 1) := by
    rw [Nat.pow_succ]
    omega
  have hloglt : Nat.log2 j < H + 1 := (Nat.log2_lt (Nat.ne_of_gt h0j)).2 hjpow
  omega

private theorem left_start_eq (H h j : ℕ) (h0j : 0 < j)
    (hh : h + 1 = H - Nat.log2 j) :
    2 ^ (H - Nat.log2 (2 * j)) * (2 * j - 2 ^ Nat.log2 (2 * j)) =
      2 ^ (H - Nat.log2 j) * (j - 2 ^ Nat.log2 j) := by
  let l := Nat.log2 j
  have hpowle : 2 ^ l ≤ j := (Nat.le_log2 (Nat.ne_of_gt h0j)).1 (le_refl l)
  have hlog : Nat.log2 (2 * j) = l + 1 := by simpa only [l] using log2_two_mul j h0j
  have hsubH : H - (l + 1) = h := by omega
  have hsubHparent : H - l = h + 1 := by omega
  rw [hlog, hsubH, hsubHparent]
  rw [Nat.pow_succ]
  have hsub : 2 * j - 2 ^ l * 2 = 2 * (j - 2 ^ l) := by omega
  rw [hsub]
  rw [Nat.pow_succ]
  ring

private theorem left_stop_eq (H h j : ℕ) (h0j : 0 < j)
    (hh : h + 1 = H - Nat.log2 j) :
    2 ^ (H - Nat.log2 (2 * j)) * (2 * j - 2 ^ Nat.log2 (2 * j)) +
        2 ^ (H - Nat.log2 (2 * j)) =
      2 ^ (H - Nat.log2 j) * (j - 2 ^ Nat.log2 j) + 2 ^ h := by
  let l := Nat.log2 j
  have hlog : Nat.log2 (2 * j) = l + 1 := by simpa only [l] using log2_two_mul j h0j
  have hsubH : H - (l + 1) = h := by omega
  rw [left_start_eq H h j h0j hh, hlog, hsubH]

private theorem right_start_eq (H h j : ℕ) (h0j : 0 < j)
    (hh : h + 1 = H - Nat.log2 j) :
    2 ^ (H - Nat.log2 (2 * j + 1)) * (2 * j + 1 - 2 ^ Nat.log2 (2 * j + 1)) =
      2 ^ (H - Nat.log2 j) * (j - 2 ^ Nat.log2 j) + 2 ^ h := by
  let l := Nat.log2 j
  have hpowle : 2 ^ l ≤ j := (Nat.le_log2 (Nat.ne_of_gt h0j)).1 (le_refl l)
  have hlog : Nat.log2 (2 * j + 1) = l + 1 := by
    simpa only [l] using log2_two_mul_add_one j h0j
  have hsubH : H - (l + 1) = h := by omega
  have hsubHparent : H - l = h + 1 := by omega
  rw [hlog, hsubH, hsubHparent]
  rw [Nat.pow_succ]
  have hsub : 2 * j + 1 - 2 ^ l * 2 = 2 * (j - 2 ^ l) + 1 := by omega
  rw [hsub]
  rw [Nat.pow_succ]
  ring

private theorem right_stop_eq (H h j : ℕ) (h0j : 0 < j)
    (hh : h + 1 = H - Nat.log2 j) :
    2 ^ (H - Nat.log2 (2 * j + 1)) * (2 * j + 1 - 2 ^ Nat.log2 (2 * j + 1)) +
        2 ^ (H - Nat.log2 (2 * j + 1)) =
      2 ^ (H - Nat.log2 j) * (j - 2 ^ Nat.log2 j) + 2 ^ (H - Nat.log2 j) := by
  let l := Nat.log2 j
  have hlog : Nat.log2 (2 * j + 1) = l + 1 := by
    simpa only [l] using log2_two_mul_add_one j h0j
  have hsubH : H - (l + 1) = h := by omega
  have hsubHparent : H - l = h + 1 := by omega
  rw [right_start_eq H h j h0j hh, hlog, hsubH, hsubHparent]
  rw [Nat.pow_succ]
  ring

theorem coverage_left_L {α : Type*} [Monoid α] {n j : ℕ} (st : SegmentTree α n)
    (h0j : 0 < j) (hjm : j < st.m) :
    (CoverageIntervalDefs.from_st n (2 * j) st (by omega) (by omega)).L =
      (CoverageIntervalDefs.from_st n j st h0j (by omega)).L := by
  have hlt_log : Nat.log2 j < st.H := by
    rw [st.h_m_pow2H] at hjm
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt h0j) hjm
  have hh : (st.H - (Nat.log2 j + 1)) + 1 = st.H - Nat.log2 j := by omega
  simp only [CoverageIntervalDefs.from_st, CoverageIntervalDefs.from_assumptions]
  exact left_start_eq st.H (st.H - (Nat.log2 j + 1)) j h0j hh

theorem coverage_left_R {α : Type*} [Monoid α] {n j : ℕ} (st : SegmentTree α n)
    (h0j : 0 < j) (hjm : j < st.m) :
    (CoverageIntervalDefs.from_st n (2 * j) st (by omega) (by omega)).R =
      ((CoverageIntervalDefs.from_st n j st h0j (by omega)).L +
        (CoverageIntervalDefs.from_st n j st h0j (by omega)).R) / 2 := by
  have hlt_log : Nat.log2 j < st.H := by
    rw [st.h_m_pow2H] at hjm
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt h0j) hjm
  have hh : (st.H - (Nat.log2 j + 1)) + 1 = st.H - Nat.log2 j := by omega
  simp only [CoverageIntervalDefs.from_st, CoverageIntervalDefs.from_assumptions]
  rw [left_stop_eq st.H (st.H - (Nat.log2 j + 1)) j h0j hh]
  have hparent : st.H - Nat.log2 j = (st.H - (Nat.log2 j + 1)) + 1 := by omega
  rw [hparent, Nat.pow_succ]
  omega

theorem coverage_right_L {α : Type*} [Monoid α] {n j : ℕ} (st : SegmentTree α n)
    (h0j : 0 < j) (hjm : j < st.m) :
    (CoverageIntervalDefs.from_st n (2 * j + 1) st (by omega) (by omega)).L =
      ((CoverageIntervalDefs.from_st n j st h0j (by omega)).L +
        (CoverageIntervalDefs.from_st n j st h0j (by omega)).R) / 2 := by
  have hlt_log : Nat.log2 j < st.H := by
    rw [st.h_m_pow2H] at hjm
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt h0j) hjm
  have hh : (st.H - (Nat.log2 j + 1)) + 1 = st.H - Nat.log2 j := by omega
  simp only [CoverageIntervalDefs.from_st, CoverageIntervalDefs.from_assumptions]
  rw [right_start_eq st.H (st.H - (Nat.log2 j + 1)) j h0j hh]
  have hparent : st.H - Nat.log2 j = (st.H - (Nat.log2 j + 1)) + 1 := by omega
  rw [hparent, Nat.pow_succ]
  omega

theorem coverage_right_R {α : Type*} [Monoid α] {n j : ℕ} (st : SegmentTree α n)
    (h0j : 0 < j) (hjm : j < st.m) :
    (CoverageIntervalDefs.from_st n (2 * j + 1) st (by omega) (by omega)).R =
      (CoverageIntervalDefs.from_st n j st h0j (by omega)).R := by
  have hlt_log : Nat.log2 j < st.H := by
    rw [st.h_m_pow2H] at hjm
    rw [Nat.log2_eq_log_two]
    exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt h0j) hjm
  have hh : (st.H - (Nat.log2 j + 1)) + 1 = st.H - Nat.log2 j := by omega
  simp only [CoverageIntervalDefs.from_st, CoverageIntervalDefs.from_assumptions]
  rw [right_stop_eq st.H (st.H - (Nat.log2 j + 1)) j h0j hh]

private theorem coverage_leaf_width {α : Type*} [Monoid α] {n j : ℕ} (st : SegmentTree α n)
    (h0j : 0 < j) (hmj : st.m ≤ j) (hj2m : j < 2 * st.m) :
    (CoverageIntervalDefs.from_st n j st h0j hj2m).R =
      (CoverageIntervalDefs.from_st n j st h0j hj2m).L + 1 := by
  have hjpow : j < 2 * 2 ^ st.H := by simpa only [st.h_m_pow2H] using hj2m
  have hle_log : Nat.log2 j ≤ st.H := log2_le_of_lt_two_mul_pow h0j hjpow
  have hHle_log : st.H ≤ Nat.log2 j := by
    rw [st.h_m_pow2H] at hmj
    rw [Nat.log2_eq_log_two]
    exact Nat.le_log_of_pow_le Nat.one_lt_two hmj
  have hlogH : Nat.log2 j = st.H := le_antisymm hle_log hHle_log
  simp only [CoverageIntervalDefs.from_st, CoverageIntervalDefs.from_assumptions, hlogH,
    tsub_self, pow_zero, one_mul]

theorem split_node_lt_m {α : Type*} [Monoid α] {n j L R p q : ℕ}
    (st : SegmentTree α n) (h0j : 0 < j) (hj2m : j < 2 * st.m)
    (hcov : L = (CoverageIntervalDefs.from_st n j st h0j hj2m).L ∧
      R = (CoverageIntervalDefs.from_st n j st h0j hj2m).R)
    (hnsub : ¬(p ≤ L ∧ R ≤ q)) (hnotdisjoint : ¬(q ≤ L ∨ R ≤ p)) :
    j < st.m := by
  by_contra hjm_not
  have hmj : st.m ≤ j := Nat.le_of_not_gt hjm_not
  have hwidth := coverage_leaf_width st h0j hmj hj2m
  have hR : R = L + 1 := by
    rw [hcov.1, hcov.2]
    exact hwidth
  have hnqL : ¬ q ≤ L := by
    intro hqL
    exact hnotdisjoint (Or.inl hqL)
  have hnRp : ¬ R ≤ p := by
    intro hRp
    exact hnotdisjoint (Or.inr hRp)
  have hLq : L < q := Nat.lt_of_not_ge hnqL
  have hpR : p < R := Nat.lt_of_not_ge hnRp
  have hpL : p ≤ L := by omega
  have hRq : R ≤ q := by omega
  exact hnsub ⟨hpL, hRq⟩

private theorem query_aux_correct (α : Type) [inst : Monoid α] (n : ℕ)
    (st : SegmentTree α n) (p q : ℕ) :
    ∀ (j L R : ℕ) (h_j0 : j > 0),
      (∀ hj2m : j < 2 * st.m,
        L = (CoverageIntervalDefs.from_st n j st h_j0 hj2m).L ∧
        R = (CoverageIntervalDefs.from_st n j st h_j0 hj2m).R) →
      (¬ j < 2 * st.m → min R q ≤ max L p) →
      (query.query_aux α n st p q j L R h_j0).ret =
        (st.a.toArray.extract (st.m + max L p) (st.m + min R q)).foldl
          (fun a b => a * b) 1 := by
  refine query.query_aux.induct α n st p q (motive := fun j L R h_j0 =>
      (∀ hj2m : j < 2 * st.m,
        L = (CoverageIntervalDefs.from_st n j st h_j0 hj2m).L ∧
        R = (CoverageIntervalDefs.from_st n j st h_j0 hj2m).R) →
      (¬ j < 2 * st.m → min R q ≤ max L p) →
      (query.query_aux α n st p q j L R h_j0).ret =
        (st.a.toArray.extract (st.m + max L p) (st.m + min R q)).foldl
          (fun a b => a * b) 1) ?caseSub ?caseDisjoint ?caseSplit ?caseOutside
  · intro j L R h_j0 hj2m hsub hcov _hempty
    rw [query.query_aux.eq_def (α := α) (n := n) (st := st) (p := p) (q := q)
      (j := j) (L := L) (R := R) (h_j0 := h_j0)]
    simp only [hj2m, ↓reduceDIte, hsub, and_self, bind_pure_comp, ret_map, sup_of_le_left,
      inf_of_le_left, Array.size_extract, Vector.size_toArray]
    rcases hcov hj2m with ⟨hL, hR⟩
    simpa only [hL, hR, Array.size_extract, Vector.size_toArray] using
      SegmentTree.coverage_interval n j st h_j0 hj2m
  · intro j L R h_j0 hj2m hnsub hdisjoint hcov _hempty
    rw [query.query_aux.eq_def (α := α) (n := n) (st := st) (p := p) (q := q)
      (j := j) (L := L) (R := R) (h_j0 := h_j0)]
    simp only [hj2m, ↓reduceDIte, hnsub, hdisjoint, bind_pure_comp, ret_map, Array.size_extract,
      Vector.size_toArray]
    symm
    have hfold :
        (st.a.toArray.extract (st.m + max L p) (st.m + min R q)).foldl
          (fun a b => a * b) 1 = 1 := by
      apply array_foldl_extract_empty_of_stop_le_start
      rcases hdisjoint with hqL | hRp
      · have hLmax : L ≤ max L p := le_max_left L p
        have hminRq : min R q ≤ q := min_le_right R q
        omega
      · have hminRR : min R q ≤ R := min_le_left R q
        have hpmax : p ≤ max L p := le_max_right L p
        omega
    simpa only [Array.size_extract, Vector.size_toArray] using hfold
  · intro j L R h_j0 hj2m hnsub hnotdisjoint C ihLeft ihRight hcov hempty
    have hcovj := hcov hj2m
    have hjm : j < st.m := split_node_lt_m st h_j0 hj2m hcovj hnsub hnotdisjoint
    have hC : C = (L + R) / 2 := rfl
    have hLR : L ≤ R := by
      rcases hcovj with ⟨hL, hR⟩
      rw [hL, hR]
      simp only [CoverageIntervalDefs.from_st, CoverageIntervalDefs.from_assumptions,
        le_add_iff_nonneg_right, zero_le]
    have hLC : L ≤ C := by
      rw [hC]
      omega
    have hCR : C ≤ R := by
      rw [hC]
      omega
    have hleft := ihLeft
      (by
        intro h2j
        rcases hcovj with ⟨hL, hR⟩
        constructor
        · rw [hL]
          exact (coverage_left_L st h_j0 hjm).symm
        · rw [hC, hL, hR]
          exact (coverage_left_R st h_j0 hjm).symm)
      (by
        intro hnot2j
        omega)
    have hright := ihRight
      (by
        intro h2j1
        rcases hcovj with ⟨hL, hR⟩
        constructor
        · rw [hC, hL, hR]
          exact (coverage_right_L st h_j0 hjm).symm
        · rw [hR]
          exact (coverage_right_R st h_j0 hjm).symm)
      (by
        intro hnot2j1
        omega)
    rw [query.query_aux.eq_def (α := α) (n := n) (st := st) (p := p) (q := q)
      (j := j) (L := L) (R := R) (h_j0 := h_j0)]
    simp only [hj2m, ↓reduceDIte, hnsub, hnotdisjoint, bind_pure_comp, ret_bind, ret_map,
      Array.size_extract, Vector.size_toArray]
    rw [hleft, hright]
    simpa only [Array.size_extract, Vector.size_toArray] using
      (fold_inter_split st.a.toArray st.m L C R p q hLC hCR).symm
  · intro j L R h_j0 hnot hcov hempty
    rw [query.query_aux.eq_def (α := α) (n := n) (st := st) (p := p) (q := q)
      (j := j) (L := L) (R := R) (h_j0 := h_j0)]
    simp only [hnot, ↓reduceDIte, bind_pure_comp, ret_map, Array.size_extract, Vector.size_toArray]
    symm
    have hfold :
        (st.a.toArray.extract (st.m + max L p) (st.m + min R q)).foldl
          (fun a b => a * b) 1 = 1 := by
      apply array_foldl_extract_empty_of_stop_le_start
      exact Nat.add_le_add_left (hempty hnot) st.m
    simpa only [Array.size_extract, Vector.size_toArray] using hfold

-- QUERY OPERATION:
-- query function: given an interval [p, q), if we call p1:=max(0, p) and q1:=min(q, st.m)
-- and denote with leaf[] the bottom layer of the tree (= a[m] to a[2m-1]),
-- it returns the result of the computation leaf[p1] * leaf[p1+1] * .... * leaf[q1-2] * leaf[q1-1],
-- or the identity element if q1 ≤ p1

-- the query starts by calling query_aux from the root (j=1) and operates recursively:
-- at each node, if its coverage interval is entirely contained in the query interval, it returns the value stored at that node,
-- otherwise, if the two intervals are disjoint, it returns the identity element,
-- lastly, if the two have a proper intersection, the function will query the children of node j, and aggregate their answers

theorem query_correctness (α : Type) (inst : Monoid α) (n : ℕ) (st : SegmentTree α n) (p q : ℕ) :
    (query α n st p q).ret =
      (st.a.toArray.extract (st.m + p) (st.m + q)).foldl (fun a b => a * b) 1 := by
  have hroot := query_aux_correct α n st p q 1 0 st.m (by omega)
    (by
      intro h12m
      constructor
      · simp only [CoverageIntervalDefs.from_st, CoverageIntervalDefs.from_assumptions,
          Nat.log2_eq_log_two, Nat.log_one_right, pow_zero, tsub_self, tsub_zero, mul_zero,
          zero_add]
      · simp only [st.h_m_pow2H, CoverageIntervalDefs.from_st,
          CoverageIntervalDefs.from_assumptions, Nat.log2_eq_log_two, Nat.log_one_right, pow_zero,
          tsub_self, tsub_zero, mul_zero, zero_add])
    (by
      intro hnot
      have hm0 := st.h_m0
      omega)
  have hroot' :
      (query.query_aux α n st p q 1 0 st.m (by omega)).ret =
        (st.a.toArray.extract (st.m + p) (st.m + min st.m q)).foldl
          (fun a b => a * b) 1 := by
    simpa only [Array.size_extract, Vector.size_toArray, zero_le, sup_of_le_right] using hroot
  rw [array_foldl_extract_stop_min (fun a b : α => a * b) st.a.toArray 1 st.m p q
    (by simp only [Vector.size_toArray])] at hroot'
  simpa only [query, Array.size_extract, Vector.size_toArray] using hroot'

end Cslib.Algorithms.Lean.TimeM
