/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sonja Joost, Josefine Lindmar, Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Challenges.BinaryHeap_Dijkstra.Def_BinaryHeap

open Finset SimpleGraph BinaryTree BinaryHeap

set_option autoImplicit true

variable {V : Type*} [Fintype V] [DecidableEq V]

structure fin_simple_graph (V : Type u) [Fintype V] [DecidableEq V]  extends SimpleGraph V

noncomputable
instance fintype_fin_simple_graph {V : Type u} [Fintype V] [DecidableEq V] (G : fin_simple_graph V) (v : V): Fintype (G.neighborSet v) :=  Fintype.ofFinite ↑(G.neighborSet v)

/-
  two definitions to shorten proof states
-/
noncomputable def delta (g : fin_simple_graph V) (s v : V) : Nat :=
  (SimpleGraph.dist (G := (by exact g.toSimpleGraph)) s v)

/-
  Beginning of the implementation of the algorithm. This is the inner fold.
-/
noncomputable def relax_neighbors (g : fin_simple_graph V) (u : V) (dist : V → ENat) (queue : BinaryHeap V) : (V → ENat) × (BinaryHeap V) :=
  List.foldl
    (fun (acc : (V → ENat) × BinaryHeap V) (v : V) =>
      let (dist, queue) := acc
      let alt := dist u + 1
      if alt < dist v then
        let dist' : V → ENat := fun x => if x = v then alt else dist x
        let queue' := queue.decrease_priority v dist'
        (dist', queue')
      else
        (dist, queue)
    )
    (dist, queue)
    (g.neighborFinset u).val.toList
