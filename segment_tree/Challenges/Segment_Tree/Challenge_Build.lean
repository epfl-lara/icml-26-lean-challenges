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
def build (α : Type) [inst: Monoid α] (n : ℕ) (xs : Vector α n) : SegmentTree α n := sorry
