/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carmen Casulli, Fabio Giovanazzi, Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Challenges.Segment_Tree.Def_SegmentTree

set_option autoImplicit false

-- structure with variables describing the properties of a node with index j in a Segmen Tree of height H,
-- in particular those regarding its "coverage interval" (= the set of leaves that j as lowest common ancestor).
-- [L, R) denotes such interval among the leaves, which means that the respective interval of tree nodes is [st.m+L, st.m+R)
-- C is the middle point of the interval; it is relevant only for internal nodes
-- since every Segment Tree is a complete binary tree, each coverage interval has a power of 2 as width (and its exponent h is the height of the node in the tree)
structure CoverageIntervalDefs (j H : ℕ) where
  h0j : 0 < j
  hj2m : j < 2*2^H
  l : ℕ
  k : ℕ
  h : ℕ
  L : ℕ
  R : ℕ
  C : ℕ
  h_l : l = Nat.log2 j
  h_k : k = j - 2^l
  h_h : h = H - l
  h_L : L = 2^h * k
  h_R : R = L + 2^h
  h_C : C = (L + R) / 2

def CoverageIntervalDefs.from_assumptions (j H : ℕ) (h0j : 0 < j) (hj2m: j < 2*2^H) :
  CoverageIntervalDefs j H := {
    h0j := h0j,
    hj2m := hj2m,
    l := Nat.log2 j,
    k := j - 2^(Nat.log2 j),
    h := H - Nat.log2 j,
    L := 2^(H - Nat.log2 j) * (j - 2^(Nat.log2 j)),
    R := 2^(H - Nat.log2 j) * (j - 2^(Nat.log2 j)) + 2^(H - Nat.log2 j),
    C := (2^(H - Nat.log2 j) * (j - 2^(Nat.log2 j)) + (2^(H - Nat.log2 j) * (j - 2^(Nat.log2 j)) + 2^(H - Nat.log2 j))) / 2
    h_l := rfl,
    h_k := rfl,
    h_h := rfl,
    h_L := rfl,
    h_R := rfl,
    h_C := rfl,
  }

def CoverageIntervalDefs.from_st {α : Type*} [Monoid α] (n j : ℕ) (st : SegmentTree α n) (h0j : 0 < j) (hj2m: j < 2*st.m) :
  CoverageIntervalDefs j st.H := CoverageIntervalDefs.from_assumptions j st.H h0j (by simp [← st.h_m_pow2H, hj2m])

private theorem array_toList_extract_split {α : Type*} (xs : Array α) {l m r : ℕ}
    (hlm : l ≤ m) (hmr : m ≤ r) :
    (xs.extract l r).toList = (xs.extract l m).toList ++ (xs.extract m r).toList := by
  simp [Array.toList_extract, List.extract]
  rw [← List.take_append_drop (m - l) (List.take (r - l) (List.drop l xs.toList))]
  congr 1
  · rw [List.take_take]
    have hle : m - l ≤ r - l := Nat.sub_le_sub_right hmr l
    simp [min_eq_left hle]
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

private theorem array_foldl_extract_singleton {α : Type*} [Monoid α] (xs : Array α)
    {i : ℕ} (hi : i < xs.size) :
    (xs.extract i (i + 1)).foldl (fun a b => a * b) 1 = xs[i]'hi := by
  rw [← Array.foldl_toList, Array.toList_extract]
  unfold List.extract
  rw [show i + 1 - i = 1 by omega]
  rw [List.take_one_drop_eq_of_lt_length]
  · rw [← Array.getElem_toList hi]
    simp only [List.foldl, one_mul]
    rw [List.get_eq_getElem]
  · rw [Array.length_toList]
    exact hi

private theorem vector_get_eq_toArray_getElem {α : Type*} {N : ℕ} (v : Vector α N)
    (i : Fin N) :
    v.get i = v.toArray[i.1]'(by simp [v.size_toArray, i.2]) := by
  rfl

private theorem log2_two_mul (j : ℕ) (h0j : 0 < j) :
    Nat.log2 (2 * j) = Nat.log2 j + 1 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two,
    show 2 * j = Nat.bit false j by simp [Nat.bit], Nat.log_two_bit (Nat.ne_of_gt h0j)]

private theorem log2_two_mul_add_one (j : ℕ) (h0j : 0 < j) :
    Nat.log2 (2 * j + 1) = Nat.log2 j + 1 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two,
    show 2 * j + 1 = Nat.bit true j by simp [Nat.bit, Nat.add_comm],
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
  have hlog : Nat.log2 (2 * j) = l + 1 := by simpa [l] using log2_two_mul j h0j
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
  have hlog : Nat.log2 (2 * j) = l + 1 := by simpa [l] using log2_two_mul j h0j
  have hsubH : H - (l + 1) = h := by omega
  rw [left_start_eq H h j h0j hh, hlog, hsubH]

private theorem right_start_eq (H h j : ℕ) (h0j : 0 < j)
    (hh : h + 1 = H - Nat.log2 j) :
    2 ^ (H - Nat.log2 (2 * j + 1)) * (2 * j + 1 - 2 ^ Nat.log2 (2 * j + 1)) =
      2 ^ (H - Nat.log2 j) * (j - 2 ^ Nat.log2 j) + 2 ^ h := by
  let l := Nat.log2 j
  have hpowle : 2 ^ l ≤ j := (Nat.le_log2 (Nat.ne_of_gt h0j)).1 (le_refl l)
  have hlog : Nat.log2 (2 * j + 1) = l + 1 := by
    simpa [l] using log2_two_mul_add_one j h0j
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
    simpa [l] using log2_two_mul_add_one j h0j
  have hsubH : H - (l + 1) = h := by omega
  have hsubHparent : H - l = h + 1 := by omega
  rw [right_start_eq H h j h0j hh, hlog, hsubH, hsubHparent]
  rw [Nat.pow_succ]
  ring

private theorem SegmentTree.coverage_interval_aux {α : Type*} [Monoid α] {n : ℕ}
    (st : SegmentTree α n) :
    ∀ h j (_h0j : 0 < j) (hj2m : j < 2 * st.m),
      h = st.H - Nat.log2 j →
      st.a.get ⟨j, hj2m⟩ =
        (st.a.toArray.extract
          (st.m + 2 ^ (st.H - Nat.log2 j) * (j - 2 ^ Nat.log2 j))
          (st.m + (2 ^ (st.H - Nat.log2 j) * (j - 2 ^ Nat.log2 j) +
            2 ^ (st.H - Nat.log2 j)))).foldl (fun a b => a * b) 1 := by
  intro h
  induction h with
  | zero =>
      intro j h0j hj2m hh
      have hjpow : j < 2 * 2 ^ st.H := by
        simpa [st.h_m_pow2H] using hj2m
      have hle_log : Nat.log2 j ≤ st.H := log2_le_of_lt_two_mul_pow h0j hjpow
      have hlogH : Nat.log2 j = st.H := by omega
      have hpowle : 2 ^ st.H ≤ j := by
        simpa [hlogH] using (Nat.le_log2 (Nat.ne_of_gt h0j)).1 (le_refl (Nat.log2 j))
      have hstart : st.m + 2 ^ (st.H - Nat.log2 j) * (j - 2 ^ Nat.log2 j) = j := by
        rw [st.h_m_pow2H, hlogH]
        simp only [tsub_self, pow_zero, one_mul]
        omega
      have hstop : st.m + (2 ^ (st.H - Nat.log2 j) * (j - 2 ^ Nat.log2 j) +
          2 ^ (st.H - Nat.log2 j)) = j + 1 := by
        rw [st.h_m_pow2H, hlogH]
        simp only [tsub_self, pow_zero, one_mul]
        omega
      rw [hstart, hstop]
      rw [vector_get_eq_toArray_getElem]
      rw [array_foldl_extract_singleton]
  | succ h ih =>
      intro j h0j hj2m hh
      have hjpow : j < 2 * 2 ^ st.H := by
        simpa [st.h_m_pow2H] using hj2m
      have hle_log : Nat.log2 j ≤ st.H := log2_le_of_lt_two_mul_pow h0j hjpow
      have hlt_log : Nat.log2 j < st.H := by omega
      have hj_lt_pow_succ : j < 2 ^ (Nat.log2 j + 1) :=
        (Nat.log2_lt (Nat.ne_of_gt h0j)).1 (Nat.lt_succ_self (Nat.log2 j))
      have hj_lt_m : j < st.m := by
        rw [st.h_m_pow2H]
        exact lt_of_lt_of_le hj_lt_pow_succ
          (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : Nat.log2 j + 1 ≤ st.H))
      have h2j0 : 0 < 2 * j := by omega
      have h2j2m : 2 * j < 2 * st.m := by omega
      have h2j10 : 0 < 2 * j + 1 := by omega
      have h2j12m : 2 * j + 1 < 2 * st.m := by omega
      have hleftHeight : h = st.H - Nat.log2 (2 * j) := by
        rw [log2_two_mul j h0j]
        omega
      have hrightHeight : h = st.H - Nat.log2 (2 * j + 1) := by
        rw [log2_two_mul_add_one j h0j]
        omega
      have hleft := ih (2 * j) h2j0 h2j2m hleftHeight
      have hright := ih (2 * j + 1) h2j10 h2j12m hrightHeight
      rw [st.h_children j h0j hj_lt_m]
      rw [hleft, hright]
      rw [left_stop_eq st.H h j h0j hh]
      rw [left_start_eq st.H h j h0j hh]
      rw [right_stop_eq st.H h j h0j hh]
      rw [right_start_eq st.H h j h0j hh]
      have hstartmid :
          st.m + 2 ^ (st.H - Nat.log2 j) * (j - 2 ^ Nat.log2 j) ≤
            st.m + (2 ^ (st.H - Nat.log2 j) * (j - 2 ^ Nat.log2 j) + 2 ^ h) := by
        exact Nat.add_le_add_left
          (Nat.le_add_right (2 ^ (st.H - Nat.log2 j) * (j - 2 ^ Nat.log2 j)) (2 ^ h)) st.m
      have hmidstop :
          st.m + (2 ^ (st.H - Nat.log2 j) * (j - 2 ^ Nat.log2 j) + 2 ^ h) ≤
            st.m + (2 ^ (st.H - Nat.log2 j) * (j - 2 ^ Nat.log2 j) +
              2 ^ (st.H - Nat.log2 j)) := by
        have hwidth : 2 ^ h ≤ 2 ^ (st.H - Nat.log2 j) := by
          rw [← hh]
          exact Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.le_succ h)
        exact Nat.add_le_add_left
          (Nat.add_le_add_left hwidth (2 ^ (st.H - Nat.log2 j) * (j - 2 ^ Nat.log2 j))) st.m
      have hsplit := array_foldl_extract_split (fun a b : α => a * b) st.a.toArray 1
        hstartmid hmidstop
      rw [hsplit]
      conv_rhs => rw [Array.foldl_mul_assoc]

-- fundamental theorem of Segment Tree:
-- the value stored in node j with coverage interval [L, R) is:
--  a[m + L] * a[m + L + 1] * .... * a[m + R - 2] * a[m + R - 1],
--  which means that each tree node stores the "query value" for its coverage interval.

theorem SegmentTree.coverage_interval {α : Type*} [Monoid α] (n j : ℕ) (st : SegmentTree α n)
    (h0j : 0 < j) (hj2m: j < 2*st.m) :
  let d := CoverageIntervalDefs.from_st n j st h0j hj2m
  st.a.get ⟨j, hj2m⟩ = (st.a.toArray.extract (st.m+d.L) (st.m+d.R)).foldl (fun a b => a * b) 1
:= by
  simpa [CoverageIntervalDefs.from_st, CoverageIntervalDefs.from_assumptions]
    using SegmentTree.coverage_interval_aux st (st.H - Nat.log2 j) j h0j hj2m rfl
