/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sonja Joost, Josefine Lindmar, Sorrachai Yingchareonthawornchai
-/

import Challenges.BinaryHeap_Dijkstra.Challenge_Dijkstra_1

open BinaryTree

namespace BinaryHeap

def extract_min {α : Type u} [DecidableEq α] (h : BinaryHeap α) (priority : α → ENat)
    (hh : ¬ isEmpty h) : (α × BinaryHeap α) :=
  ((h.tree.extract_min priority).1.get (by grind [extract_min_is_someHeap]),
   { tree := (h.tree.extract_min priority).2 })

end BinaryHeap
