/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carmen Casulli, Fabio Giovanazzi, Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Challenges.Segment_Tree.Def_SegmentTree

set_option autoImplicit false

-- function build returns a SegmentTree from a vector of elements xs of the monoid α,
-- providing in particular the proof of the segment tree property h_children
-- Preferably, the implementation should be a linear-time construction.
-- We do not force this time constraint in this exercise.
private def buildLeaf (α : Type) [Monoid α] (n : ℕ) (xs : Vector α n) (i : ℕ) : α :=
  if h : i < n then xs.get ⟨i, h⟩ else 1

private def buildNode (α : Type) [Monoid α] (n : ℕ) (xs : Vector α n) : ℕ → ℕ → α
  | 0, i => buildLeaf α n xs i
  | h + 1, i => buildNode α n xs h (2 * i) * buildNode α n xs h (2 * i + 1)

private def buildValue (α : Type) [Monoid α] (n : ℕ) (xs : Vector α n) (H i : ℕ) : α :=
  if i = 0 then 1 else buildNode α n xs (H - Nat.log2 i) (i - 2 ^ Nat.log2 i)

private theorem log2_two_mul (j : ℕ) (h0j : 0 < j) :
    Nat.log2 (2 * j) = Nat.log2 j + 1 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two,
    show 2 * j = Nat.bit false j by simp [Nat.bit], Nat.log_two_bit (Nat.ne_of_gt h0j)]

private theorem log2_two_mul_add_one (j : ℕ) (h0j : 0 < j) :
    Nat.log2 (2 * j + 1) = Nat.log2 j + 1 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two,
    show 2 * j + 1 = Nat.bit true j by simp [Nat.bit, Nat.add_comm],
    Nat.log_two_bit (Nat.ne_of_gt h0j)]

private theorem left_offset_eq (j : ℕ) (h0j : 0 < j) :
    2 * j - 2 ^ (Nat.log2 j + 1) = 2 * (j - 2 ^ Nat.log2 j) := by
  have hpowle : 2 ^ Nat.log2 j ≤ j :=
    (Nat.le_log2 (Nat.ne_of_gt h0j)).1 (le_refl (Nat.log2 j))
  rw [Nat.pow_succ]
  omega

private theorem right_offset_eq (j : ℕ) (h0j : 0 < j) :
    2 * j + 1 - 2 ^ (Nat.log2 j + 1) = 2 * (j - 2 ^ Nat.log2 j) + 1 := by
  have hpowle : 2 ^ Nat.log2 j ≤ j :=
    (Nat.le_log2 (Nat.ne_of_gt h0j)).1 (le_refl (Nat.log2 j))
  rw [Nat.pow_succ]
  omega

def build (α : Type) [inst: Monoid α] (n : ℕ) (xs : Vector α n) : SegmentTree α n :=
  let H := Nat.clog 2 n
  let m := 2 ^ H
  { m := m
    H := H
    a := Vector.ofFn (fun i : Fin (2 * m) => buildValue α n xs H i.1)
    h_m0 := by
      dsimp [m]
      positivity
    h_mn := by
      dsimp [m, H]
      exact Nat.le_pow_clog Nat.one_lt_two n
    h_m2n := by
      dsimp [m, H]
      by_cases hn : n ≤ 1
      · left
        have hclog : Nat.clog 2 n = 0 := Nat.clog_of_right_le_one hn 2
        simp [hclog]
      · right
        have hn1 : 1 < n := by omega
        have hpred : 2 ^ (Nat.clog 2 n).pred < n :=
          Nat.pow_pred_clog_lt_self Nat.one_lt_two hn1
        have hpos : 0 < Nat.clog 2 n := Nat.clog_pos Nat.one_lt_two hn1
        have hsucc : (Nat.clog 2 n).pred + 1 = Nat.clog 2 n :=
          Nat.succ_pred_eq_of_pos hpos
        have hpow : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n).pred := by
          calc
            2 ^ Nat.clog 2 n = 2 ^ ((Nat.clog 2 n).pred + 1) := by rw [hsucc]
            _ = 2 ^ (Nat.clog 2 n).pred * 2 := by rw [Nat.pow_succ]
            _ = 2 * 2 ^ (Nat.clog 2 n).pred := by rw [Nat.mul_comm]
        rw [hpow]
        omega
    h_m_pow2H := by rfl
    h_children := by
      intro j h0j hjm
      have hjH : j < 2 ^ H := by simpa [m] using hjm
      have hloglt : Nat.log2 j < H := by
        rw [Nat.log2_eq_log_two]
        exact Nat.log_lt_of_lt_pow (Nat.ne_of_gt h0j) hjH
      have hparent :
          (Vector.ofFn (fun i : Fin (2 * m) => buildValue α n xs H i.1)).get
              ⟨j, by omega⟩ =
            buildValue α n xs H j := by
        exact Vector.getElem_ofFn (by omega)
      have hleft :
          (Vector.ofFn (fun i : Fin (2 * m) => buildValue α n xs H i.1)).get
              ⟨2 * j, by omega⟩ =
            buildValue α n xs H (2 * j) := by
        exact Vector.getElem_ofFn (by omega)
      have hright :
          (Vector.ofFn (fun i : Fin (2 * m) => buildValue α n xs H i.1)).get
              ⟨2 * j + 1, by omega⟩ =
            buildValue α n xs H (2 * j + 1) := by
        exact Vector.getElem_ofFn (by omega)
      rw [hparent, hleft, hright]
      simp [buildValue, Nat.ne_of_gt h0j, show 2 * j ≠ 0 by omega]
      rw [log2_two_mul j h0j, log2_two_mul_add_one j h0j]
      have hheight : H - Nat.log2 j = H - (Nat.log2 j + 1) + 1 := by omega
      rw [hheight]
      simp [buildNode]
      rw [left_offset_eq j h0j, right_offset_eq j h0j] }
