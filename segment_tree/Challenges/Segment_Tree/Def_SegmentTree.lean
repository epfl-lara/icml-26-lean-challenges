/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carmen Casulli, Fabio Giovanazzi, Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic

set_option autoImplicit false


structure SegmentTree (α : Type*) [Monoid α] (n : ℕ) where
  m : ℕ
  H : ℕ
  a : Vector α (2*m)
  h_m0 : m > 0
  h_mn : m ≥ n
  h_m2n : m = 1 ∨ m < n * 2 - 1
  h_m_pow2H : m = 2^H
  h_children (j : ℕ) (h0j : 0 < j) (hjm: j < m) :
    (a.get ⟨j, by omega⟩) = (a.get ⟨2*j, by omega⟩) * (a.get ⟨2*j+1, by omega⟩)
