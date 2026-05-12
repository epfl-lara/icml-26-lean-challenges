/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sonja Joost, Josefine Lindmar, Sorrachai Yingchareonthawornchai
-/

import Challenges.BinaryHeap_Dijkstra.Def_BinaryHeapComposite

open BinaryTree BinaryHeap Finset SimpleGraph

set_option autoImplicit true

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
  Prove that the algotithm below terminates.
-/
theorem dijkstra_terminate {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V]
    [inst_2 : Nonempty V] (g : fin_simple_graph V) (dist : V → ℕ∞) (queue : BinaryHeap V)
    (hq hne : ¬queue.isEmpty = true) :
    (relax_neighbors g (queue.extract_min dist hne).1 dist (queue.extract_min dist hne).2).2.sizeOf <
      queue.sizeOf := sorry
