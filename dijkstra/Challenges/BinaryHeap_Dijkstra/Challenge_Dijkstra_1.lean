/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sonja Joost, Josefine Lindmar, Sorrachai Yingchareonthawornchai
-/

import Challenges.BinaryHeap_Dijkstra.Def_BinaryHeap
import Challenges.BinaryHeap_Dijkstra.Def_Dijkstra

open BinaryTree

namespace BinaryHeap

lemma extract_min_is_someHeap {α : Type u} [DecidableEq α] (h : BinaryHeap α) (f : α → ENat)
    (hh : ¬ isEmpty h) : (BinaryTree.extract_min h.tree f).1.isSome := sorry

end BinaryHeap
