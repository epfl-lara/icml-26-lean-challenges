/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sonja Joost, Josefine Lindmar, Sorrachai Yingchareonthawornchai
-/

import Challenges.BinaryHeap_Dijkstra.Def_DijkstraComposite

open BinaryTree BinaryHeap Finset SimpleGraph

set_option autoImplicit true

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
  Main correctness theorem: for every vertex `v`, Dijkstra computes the true shortest-path length
  from `s` to `v`. That is, `(dijkstra g s v) v = delta g s v` when the graph is connected.
-/
theorem dijkstra_correctness
  [Nonempty V]
  (g : fin_simple_graph V) (s : V)
  (is_connected : SimpleGraph.Connected g.toSimpleGraph) :
  ∀ v : V, (dijkstra g s v) v = delta g s v := sorry
