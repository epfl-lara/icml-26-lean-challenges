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
    (hh : ¬ isEmpty h) : (BinaryTree.extract_min h.tree f).1.isSome := by
  have get_last_isSome : ∀ t : BinaryTree α, t ≠ BinaryTree.leaf → (BinaryTree.get_last t).1.isSome := by
    intro t ht
    induction t with
    | leaf => contradiction
    | node l v r ihl ihr =>
      cases l with
      | leaf =>
        cases r with
        | leaf => simp [BinaryTree.get_last]
        | node rl rv rr =>
          have hne : BinaryTree.node rl rv rr ≠ BinaryTree.leaf := by intro h; cases h
          simpa [BinaryTree.get_last] using ihr hne
      | node ll lv lr =>
        have hne : BinaryTree.node ll lv lr ≠ BinaryTree.leaf := by intro h; cases h
        simpa [BinaryTree.get_last] using ihl hne
  rcases h with ⟨t⟩
  cases t with
  | leaf =>
    simp [isEmpty] at hh
  | node l v r =>
    unfold BinaryTree.extract_min
    cases hlast : BinaryTree.get_last (BinaryTree.node l v r) with
    | mk lastNode treeWithoutLast =>
      cases lastNode with
      | none =>
        have hsome := get_last_isSome (BinaryTree.node l v r) (by intro h; cases h)
        simp [hlast] at hsome
      | some v' =>
        cases treeWithoutLast <;> simp

end BinaryHeap
