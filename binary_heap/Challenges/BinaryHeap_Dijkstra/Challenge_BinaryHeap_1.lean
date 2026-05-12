/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sonja Joost, Josefine Lindmar, Sorrachai Yingchareonthawornchai
-/

import Challenges.BinaryHeap_Dijkstra.Def_BinaryHeap

open BinaryTree

-- heapify_correctness:
-- This theorem bundles two key correctness properties of `heapify`:
-- 1) `heapify` preserves membership: an element is contained in `heapify bt f`
--    iff it was contained in `bt`.
-- 2) If `bt = node l v r` and both children `l` and `r` are min-heaps, then
--    `heapify bt f` is a min-heap. The proof combines containment lemmas and
--    `heapify_establishes_min_heap` which shows that fixing one violating
--    child yields a valid min-heap.
theorem heapify_correctness (bt: BinaryTree α) (f: α → ENat):
  (contains (heapify bt f) v ↔ contains bt v) ∧
  bt = node l v r ∧ is_min_heap l f ∧ is_min_heap r f → is_min_heap (heapify bt f) f := sorry
