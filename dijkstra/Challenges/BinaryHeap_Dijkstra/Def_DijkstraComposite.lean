/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sonja Joost, Josefine Lindmar, Sorrachai Yingchareonthawornchai
-/

import Challenges.BinaryHeap_Dijkstra.Challenge_Dijkstra_2

open BinaryTree BinaryHeap Finset SimpleGraph

set_option autoImplicit true

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
  two definitions to shorten proof states
-/
def min_y_invariant [Nonempty V] (y : V) (p : (V → ENat) × BinaryHeap V)
    (hh : ¬ isEmpty p.2) : Prop :=
  ∀ u1 : V, Prod.fst (p.2.extract_min p.1 hh) = u1 → p.1 y ≤ p.1 u1

/-
  Continued implementation of the algorithm
-/
noncomputable def dijkstra_rec [Nonempty V] (g : fin_simple_graph V) (source : V) (target : V)
    (dist : V → ENat) (queue : BinaryHeap V) : V → ENat :=
  if hq : queue.isEmpty then dist
  else
    have hne : ¬ queue.isEmpty = true := by exact hq
    let extract_result := queue.extract_min dist hne
    let u := extract_result.1
    let queue' := extract_result.2
    let relax_result := relax_neighbors g u dist queue'
    let dist' := relax_result.1
    let queue'' := relax_result.2
    dijkstra_rec g source target dist' queue''
termination_by queue.sizeOf
decreasing_by exact dijkstra_terminate g dist queue hq hne

noncomputable def dijkstra [Nonempty V] (g : fin_simple_graph V) (source : V) (target : V) : V → ENat :=
  let dist : V → ENat := fun v => if v = source then 0 else ⊤
  let queue := Finset.univ.val.toList.foldl (fun acc v => acc.add v dist) BinaryHeap.empty
  dijkstra_rec g source target dist queue
