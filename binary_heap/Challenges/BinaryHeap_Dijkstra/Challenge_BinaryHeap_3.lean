/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sonja Joost, Josefine Lindmar, Sorrachai Yingchareonthawornchai
-/

import Challenges.BinaryHeap_Dijkstra.Def_BinaryHeap

open BinaryTree

-- insert_correctness:
-- Describes the behavior of `insert`:
-- - Membership: inserting `v'` into `bt` yields a tree where an element `v`
--   is present iff it was already in `bt` or `v = v'` (no elements are lost,
--   and the new element is present).
-- - Heap preservation: if `bt` is a min-heap, then inserting preserves the
--   min-heap property.  The proof follows by structural induction on `insert`
--   and uses `min_heap*` lemmas to maintain the root ordering.
theorem insert_correctness (bt: BinaryTree α) (f: α → ENat):
  (∀ v v', contains bt v ∨ v = v' ↔ contains (insert bt v' f) v)
  ∧ (is_min_heap bt f → is_min_heap (insert bt v f) f) := sorry
