/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Collodel, Sorrachai Yingchareonthawornchai
-/

import Challenges.Treap.Def_Treap

namespace Cslib.Algorithms.Lean.TimeM
namespace TreapLogic
open Tree

variable {Key : Type} [LinearOrder Key]
variable {Prio : Type} [LinearOrder Prio]

/-
  Split correctness
-/

theorem split_correct (tn : TreapNode Key Prio) (k : Key) :
    ((IsBST tn) → (IsBST (TreapNode.split tn k).1 ∧ IsBST (TreapNode.split tn k).2)) ∧
    (IsHeap tn → IsHeap (TreapNode.split tn k).1 ∧ IsHeap (TreapNode.split tn k).2) := sorry

-- Splitting creates a BST on the left
theorem split_IsBST_left (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) :
    IsBST (TreapNode.split tn k).1 := by have := split_correct tn k; simp_all

-- Splitting creates a BST on the right
theorem split_IsBST_right (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) :
    IsBST (TreapNode.split tn k).2 := by have := split_correct tn k; simp_all

-- Splitting creates a Heap on the left
theorem split_IsHeap_left (tn : TreapNode Key Prio) (tn_proof : IsHeap tn) (k : Key) :
    IsHeap (TreapNode.split tn k).1 := by have := split_correct tn k; simp_all

-- Splitting creates a Heap on the right
theorem split_IsHeap_right (tn : TreapNode Key Prio) (tn_proof : IsHeap tn) (k : Key) :
    IsHeap (TreapNode.split tn k).2 := by have := split_correct tn k; simp_all

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
