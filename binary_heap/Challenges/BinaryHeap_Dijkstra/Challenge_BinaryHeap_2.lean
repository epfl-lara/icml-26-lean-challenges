/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sonja Joost, Josefine Lindmar, Sorrachai Yingchareonthawornchai
-/

import Challenges.BinaryHeap_Dijkstra.Def_BinaryHeap

open BinaryTree

-- extract_min_correctness:
-- correctness for `extract_min`:
-- - The members remain the same except for the extracted minimum.
-- - If the input was a min-heap, extracting returns some value `v'` and a
--   resulting tree that is a min-heap; furthermore the extracted priority
--   equals `heap_min bt f`.
-- The proof composes containment lemmas, `get_last` properties and
-- `heapify` correctness used in `extract_min_correct_node`.
theorem extract_min_correctness (bt l r: BinaryTree α) (v v': α) (f: α → ENat): (
  contains (extract_min bt f).2 v → contains bt v)
  ∧ (bt = node l v r → contains bt v' → v ≠ v' → contains (extract_min bt f).2 v')
  ∧ (bt = node l v r → is_min_heap bt f → ∃ bt' v', extract_min bt f = (some v', bt')
  ∧ is_min_heap bt' f ∧ f v = heap_min bt f) := sorry
