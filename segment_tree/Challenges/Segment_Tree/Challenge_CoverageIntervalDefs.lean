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

-- fundamental theorem of Segment Tree:
-- the value stored in node j with coverage interval [L, R) is:
--  a[m + L] * a[m + L + 1] * .... * a[m + R - 2] * a[m + R - 1],
--  which means that each tree node stores the "query value" for its coverage interval.

theorem SegmentTree.coverage_interval {α : Type*} [Monoid α] (n j : ℕ) (st : SegmentTree α n)
    (h0j : 0 < j) (hj2m: j < 2*st.m) :
  let d := CoverageIntervalDefs.from_st n j st h0j hj2m
  st.a.get ⟨j, hj2m⟩ = (st.a.toArray.extract (st.m+d.L) (st.m+d.R)).foldl (fun a b => a * b) 1
:= sorry
