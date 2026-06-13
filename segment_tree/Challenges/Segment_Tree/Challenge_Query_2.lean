/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carmen Casulli, Fabio Giovanazzi, Sorrachai Yingchareonthawornchai
-/

import Challenges.Segment_Tree.Def_Query

namespace Cslib.Algorithms.Lean.TimeM

set_option autoImplicit false

private def endpointCount (L R p q : ℕ) : ℕ :=
  (if L < p ∧ p < R then 1 else 0) + (if L < q ∧ q < R then 1 else 0)

private theorem endpointCount_le_two (L R p q : ℕ) : endpointCount L R p q ≤ 2 := by
  unfold endpointCount
  split_ifs <;> omega

private theorem endpointCount_split_le (L C R p q : ℕ) (hLC : L ≤ C) (hCR : C ≤ R) :
    endpointCount L C p q + endpointCount C R p q ≤ endpointCount L R p q := by
  unfold endpointCount
  split_ifs <;> omega

private theorem endpointCount_pos_of_partial (L R p q : ℕ)
    (hnsub : ¬(p ≤ L ∧ R ≤ q)) (hnotdisjoint : ¬(q ≤ L ∨ R ≤ p)) :
    1 ≤ endpointCount L R p q := by
  unfold endpointCount
  split_ifs <;> omega

private theorem log2_two_mul (j : ℕ) (h0j : 0 < j) :
    Nat.log2 (2 * j) = Nat.log2 j + 1 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two,
    show 2 * j = Nat.bit false j by simp only [Nat.bit, cond_false], Nat.log_two_bit (Nat.ne_of_gt h0j)]

private theorem log2_two_mul_add_one (j : ℕ) (h0j : 0 < j) :
    Nat.log2 (2 * j + 1) = Nat.log2 j + 1 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two,
    show 2 * j + 1 = Nat.bit true j by simp only [Nat.add_comm, Nat.bit, cond_true],
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
  rw [Nat.pow_succ, Nat.mul_assoc]

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

private theorem coverage_left_L {α : Type*} [Monoid α] {n j : ℕ} (st : SegmentTree α n)
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

private theorem coverage_left_R {α : Type*} [Monoid α] {n j : ℕ} (st : SegmentTree α n)
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

private theorem coverage_right_L {α : Type*} [Monoid α] {n j : ℕ} (st : SegmentTree α n)
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

private theorem coverage_right_R {α : Type*} [Monoid α] {n j : ℕ} (st : SegmentTree α n)
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
  simp only [CoverageIntervalDefs.from_st, CoverageIntervalDefs.from_assumptions, hlogH, tsub_self,
    pow_zero, one_mul]

private theorem split_node_lt_m {α : Type*} [Monoid α] {n j L R p q : ℕ}
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
  have hnpR : ¬ R ≤ p := by
    intro hRp
    exact hnotdisjoint (Or.inr hRp)
  have hLq : L < q := Nat.lt_of_not_ge hnqL
  have hpR : p < R := Nat.lt_of_not_ge hnpR
  have hpL : p ≤ L := by omega
  have hRq : R ≤ q := by omega
  exact hnsub ⟨hpL, hRq⟩

private theorem height_le_log_add_four {α : Type} [Monoid α] {n : ℕ} (st : SegmentTree α n) :
    st.H ≤ Nat.log 2 n + 4 := by
  rcases st.h_m2n with hm1 | hm2n
  · have hH : st.H = 0 := by
      have hlog := Nat.log_pow Nat.one_lt_two st.H
      rw [← st.h_m_pow2H, hm1, Nat.log_one_right] at hlog
      exact hlog.symm
    omega
  · have hn0 : n ≠ 0 := by
      intro hn
      omega
    have hpowle : 2 ^ st.H ≤ n * 2 := by
      rw [← st.h_m_pow2H]
      omega
    have hHlog : st.H ≤ Nat.log 2 (n * 2) :=
      Nat.le_log_of_pow_le Nat.one_lt_two hpowle
    rw [Nat.log_mul_base Nat.one_lt_two hn0] at hHlog
    omega

-- QUERY OPERATION:
-- query function: given an interval [p, q), if we call p1:=max(0, p) and q1:=min(q, st.m)
-- and denote with leaf[] the bottom layer of the tree (= a[m] to a[2m-1]),
-- it returns the result of the computation leaf[p1] * leaf[p1+1] * .... * leaf[q1-2] * leaf[q1-1],
-- or the identity element if q1 ≤ p1

-- the query starts by calling query_aux from the root (j=1) and operates recursively:
-- at each node, if its coverage interval is entirely contained in the query interval,
-- it returns the value stored at that node,
-- otherwise, if the two intervals are disjoint, it returns the identity element,
-- lastly, if the two have a proper intersection, the function will query the children of node j,
-- and aggregate their answers

theorem query_time (α : Type) (inst : Monoid α) (n : ℕ) (st : SegmentTree α n) (p q : ℕ) :
    (query α n st p q).time ≤ 17 + 4 * (Nat.log 2 n) := by
  have haux : ∀ (j L R : ℕ) (h_j0 : j > 0),
      (∀ hj2m : j < 2 * st.m,
        L = (CoverageIntervalDefs.from_st n j st h_j0 hj2m).L ∧
        R = (CoverageIntervalDefs.from_st n j st h_j0 hj2m).R) →
      (query.query_aux α n st p q j L R h_j0).time ≤
        2 * (st.H - Nat.log2 j) * endpointCount L R p q + 1 := by
    refine query.query_aux.induct α n st p q (motive := fun j L R h_j0 =>
        (∀ hj2m : j < 2 * st.m,
          L = (CoverageIntervalDefs.from_st n j st h_j0 hj2m).L ∧
          R = (CoverageIntervalDefs.from_st n j st h_j0 hj2m).R) →
        (query.query_aux α n st p q j L R h_j0).time ≤
          2 * (st.H - Nat.log2 j) * endpointCount L R p q + 1)
        ?caseSub ?caseDisjoint ?caseSplit ?caseOutside
    · intro j L R h_j0 hj2m hsub hcov
      rw [query.query_aux.eq_def (α := α) (n := n) (st := st) (p := p) (q := q)
        (j := j) (L := L) (R := R) (h_j0 := h_j0)]
      simp only [hj2m, ↓reduceDIte, hsub, and_self, bind_pure_comp, time_map, time_tick,
        le_add_iff_nonneg_left, zero_le]
    · intro j L R h_j0 hj2m hnsub hdisjoint hcov
      rw [query.query_aux.eq_def (α := α) (n := n) (st := st) (p := p) (q := q)
        (j := j) (L := L) (R := R) (h_j0 := h_j0)]
      simp only [hj2m, ↓reduceDIte, hnsub, hdisjoint, bind_pure_comp, time_map, time_tick,
        le_add_iff_nonneg_left, zero_le]
    · intro j L R h_j0 hj2m hnsub hnotdisjoint C ihLeft ihRight hcov
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
      have hright := ihRight
        (by
          intro h2j1
          rcases hcovj with ⟨hL, hR⟩
          constructor
          · rw [hC, hL, hR]
            exact (coverage_right_L st h_j0 hjm).symm
          · rw [hR]
            exact (coverage_right_R st h_j0 hjm).symm)
      have hcnt := endpointCount_split_le L C R p q hLC hCR
      have hcntpos := endpointCount_pos_of_partial L R p q hnsub hnotdisjoint
      have hlogj_lt : Nat.log2 j < st.H := by
        have hjpow : j < 2 ^ st.H := by
          simpa only [st.h_m_pow2H] using hjm
        exact (Nat.log2_lt (Nat.ne_of_gt h_j0)).2 hjpow
      have hleftHeight : st.H - Nat.log2 (2 * j) + 1 = st.H - Nat.log2 j := by
        rw [log2_two_mul j h_j0]
        omega
      have hrightHeight : st.H - Nat.log2 (2 * j + 1) + 1 = st.H - Nat.log2 j := by
        rw [log2_two_mul_add_one j h_j0]
        omega
      have hbase : 2 * (st.H - Nat.log2 (2 * j)) ≤ 2 * (st.H - Nat.log2 j) - 2 := by omega
      have hbase' : 2 * (st.H - Nat.log2 (2 * j + 1)) ≤ 2 * (st.H - Nat.log2 j) - 2 := by omega
      have hKpos : 2 ≤ 2 * (st.H - Nat.log2 j) := by omega
      have hprod :
          2 * (st.H - Nat.log2 (2 * j)) * endpointCount L C p q +
              2 * (st.H - Nat.log2 (2 * j + 1)) * endpointCount C R p q + 2 ≤
            2 * (st.H - Nat.log2 j) * endpointCount L R p q := by
        calc
          2 * (st.H - Nat.log2 (2 * j)) * endpointCount L C p q +
                2 * (st.H - Nat.log2 (2 * j + 1)) * endpointCount C R p q + 2
              ≤ (2 * (st.H - Nat.log2 j) - 2) * endpointCount L C p q +
                  (2 * (st.H - Nat.log2 j) - 2) * endpointCount C R p q + 2 :=
                Nat.add_le_add_right
                  (Nat.add_le_add (Nat.mul_le_mul_right _ hbase) (Nat.mul_le_mul_right _ hbase')) 2
          _ = (2 * (st.H - Nat.log2 j) - 2) * (endpointCount L C p q + endpointCount C R p q) + 2 := by
                rw [Nat.mul_add]
          _ ≤ (2 * (st.H - Nat.log2 j) - 2) * endpointCount L R p q + 2 :=
                Nat.add_le_add_right (Nat.mul_le_mul_left _ hcnt) 2
          _ ≤ 2 * (st.H - Nat.log2 j) * endpointCount L R p q := by
                have hexp :
                    2 * (st.H - Nat.log2 j) * endpointCount L R p q =
                      (2 * (st.H - Nat.log2 j) - 2) * endpointCount L R p q +
                        2 * endpointCount L R p q := by
                  rw [← Nat.add_mul]
                  congr 1
                  omega
                rw [hexp]
                have : 2 ≤ 2 * endpointCount L R p q := by omega
                omega
      rw [query.query_aux.eq_def (α := α) (n := n) (st := st) (p := p) (q := q)
        (j := j) (L := L) (R := R) (h_j0 := h_j0)]
      simp only [hj2m, ↓reduceDIte, hnsub, hnotdisjoint, bind_pure_comp, time_bind, time_map,
        time_tick, ge_iff_le]
      rw [← hC]
      omega
    · intro j L R h_j0 hnot hcov
      rw [query.query_aux.eq_def (α := α) (n := n) (st := st) (p := p) (q := q)
        (j := j) (L := L) (R := R) (h_j0 := h_j0)]
      simp only [hnot, ↓reduceDIte, bind_pure_comp, time_map, time_tick, le_add_iff_nonneg_left,
        zero_le]
  have hroot := haux 1 0 st.m (by omega)
    (by
      intro h12m
      constructor
      · simp only [CoverageIntervalDefs.from_st, CoverageIntervalDefs.from_assumptions,
          Nat.log2_eq_log_two, Nat.log_one_right, pow_zero, tsub_self, tsub_zero, mul_zero, zero_add]
      · simp only [st.h_m_pow2H, CoverageIntervalDefs.from_st, CoverageIntervalDefs.from_assumptions,
          Nat.log2_eq_log_two, Nat.log_one_right, pow_zero, tsub_self, tsub_zero, mul_zero,
          zero_add])
  have hroot' : (query α n st p q).time ≤ 2 * st.H * endpointCount 0 st.m p q + 1 := by
    simpa only [query] using hroot
  have hcnt := endpointCount_le_two 0 st.m p q
  have hH := height_le_log_add_four st
  have hmul : 2 * st.H * endpointCount 0 st.m p q ≤ 2 * st.H * 2 :=
    Nat.mul_le_mul_left _ hcnt
  omega

end Cslib.Algorithms.Lean.TimeM
