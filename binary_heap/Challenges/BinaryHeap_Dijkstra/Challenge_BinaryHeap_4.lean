/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sonja Joost, Josefine Lindmar, Sorrachai Yingchareonthawornchai
-/

import Challenges.BinaryHeap_Dijkstra.Def_BinaryHeap

open BinaryTree

-- decrease_priority_correctness:
-- States the two main correctness properties of `decrease_priority`:
-- - Membership preservation/behavior: an element `v` is in the original tree
--   exactly when it is in the tree after calling `decrease_priority bt v' f`.
--   In other words, decreasing the priority does not lose or create elements.
-- - Heap preservation: if the original `bt` is a min-heap, then decreasing
--   the priority of a value preserves the min-heap property.
-- The proof combines the containment lemmas and the preservation lemma above.
lemma decrease_priority_correctness [DecidableEq α] (bt: BinaryTree α) (v v': α) (f : α → ENat):
  contains bt v ↔ contains (decrease_priority bt v' f) v ∧
  (is_min_heap bt f → is_min_heap (decrease_priority bt v f) f) := sorry
