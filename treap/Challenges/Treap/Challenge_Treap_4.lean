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
  SplitUpper correctness
-/

theorem splitUpper_correct (tn : TreapNode Key Prio) (k : Key) :
    ((IsBST tn) →
      (IsBST (TreapNode.splitUpper tn k).1 ∧ IsBST (TreapNode.splitUpper tn k).2)) ∧
    (IsHeap tn →
      IsHeap (TreapNode.splitUpper tn k).1 ∧ IsHeap (TreapNode.splitUpper tn k).2) := by
  have all_keys_union_splitUpper :
      ∀ (tn : TreapNode Key Prio) (k : Key),
        (TreapNode.splitUpper tn k).1.all_keys ∪
          (TreapNode.splitUpper tn k).2.all_keys = tn.all_keys := by
    intro tn k
    fun_induction TreapNode.splitUpper tn k
    · simp [TreapNode.all_keys]
    case case2 kp l r h split_l new_r hsplit new_l ih1 =>
      subst new_l
      simp only [hsplit, TreapNode.all_keys, Set.union_singleton] at ih1 ⊢
      rw [← ih1]
      ext x
      simp [or_assoc]
    case case3 kp l r h split_l split_r hsplit new_r ih1 =>
      subst new_r
      simp only [hsplit, TreapNode.all_keys, Set.union_singleton] at ih1 ⊢
      rw [← ih1]
      ext x
      simp [or_assoc, or_left_comm]
  have all_prios_union_splitUpper :
      ∀ (tn : TreapNode Key Prio) (k : Key),
        (TreapNode.splitUpper tn k).1.all_prios ∪
          (TreapNode.splitUpper tn k).2.all_prios = tn.all_prios := by
    intro tn k
    fun_induction TreapNode.splitUpper tn k
    · simp [TreapNode.all_prios]
    case case2 kp l r h split_l new_r hsplit new_l ih1 =>
      subst new_l
      simp only [hsplit, TreapNode.all_prios, Set.union_singleton] at ih1 ⊢
      rw [← ih1]
      ext x
      simp [or_assoc]
    case case3 kp l r h split_l split_r hsplit new_r ih1 =>
      subst new_r
      simp only [hsplit, TreapNode.all_prios, Set.union_singleton] at ih1 ⊢
      rw [← ih1]
      ext x
      simp [or_assoc, or_left_comm]
  fun_induction TreapNode.splitUpper tn k
  · constructor
    · intro _
      exact ⟨IsBST.nil, IsBST.nil⟩
    · intro _
      exact ⟨IsHeap.nil, IsHeap.nil⟩
  case case2 kp l r h split_l new_r hsplit new_l ih1 =>
    subst new_l
    constructor
    · intro hbst
      cases hbst with
      | node _ _ _ left_lt_root right_ge_root bst_l bst_r =>
        have bst_pair := ih1.1 bst_r
        have bst_split_l : IsBST split_l := by
          have := bst_pair.1
          simpa [hsplit] using this
        have bst_new_r : IsBST new_r := by
          have := bst_pair.2
          simpa [hsplit] using this
        constructor
        · apply IsBST.node
          · exact left_lt_root
          · intro x hx
            have hx_r : x ∈ TreapNode.all_keys r := by
              rw [← all_keys_union_splitUpper r k]
              left
              simpa [hsplit] using hx
            exact right_ge_root x hx_r
          · exact bst_l
          · exact bst_split_l
        · exact bst_new_r
    · intro hheap
      cases hheap with
      | node _ _ _ left_le_root right_le_root heap_l heap_r =>
        have heap_pair := ih1.2 heap_r
        have heap_split_l : IsHeap split_l := by
          have := heap_pair.1
          simpa [hsplit] using this
        have heap_new_r : IsHeap new_r := by
          have := heap_pair.2
          simpa [hsplit] using this
        constructor
        · apply IsHeap.node
          · exact left_le_root
          · intro p hp
            have hp_r : p ∈ TreapNode.all_prios r := by
              rw [← all_prios_union_splitUpper r k]
              left
              simpa [hsplit] using hp
            exact right_le_root p hp_r
          · exact heap_l
          · exact heap_split_l
        · exact heap_new_r
  case case3 kp l r h split_l split_r hsplit new_r ih1 =>
    subst new_r
    constructor
    · intro hbst
      cases hbst with
      | node _ _ _ left_lt_root right_ge_root bst_l bst_r =>
        have bst_pair := ih1.1 bst_l
        have bst_split_l : IsBST split_l := by
          have := bst_pair.1
          simpa [hsplit] using this
        have bst_split_r : IsBST split_r := by
          have := bst_pair.2
          simpa [hsplit] using this
        constructor
        · exact bst_split_l
        · apply IsBST.node
          · intro x hx
            have hx_l : x ∈ TreapNode.all_keys l := by
              rw [← all_keys_union_splitUpper l k]
              right
              simpa [hsplit] using hx
            exact left_lt_root x hx_l
          · exact right_ge_root
          · exact bst_split_r
          · exact bst_r
    · intro hheap
      cases hheap with
      | node _ _ _ left_le_root right_le_root heap_l heap_r =>
        have heap_pair := ih1.2 heap_l
        have heap_split_l : IsHeap split_l := by
          have := heap_pair.1
          simpa [hsplit] using this
        have heap_split_r : IsHeap split_r := by
          have := heap_pair.2
          simpa [hsplit] using this
        constructor
        · exact heap_split_l
        · apply IsHeap.node
          · intro p hp
            have hp_l : p ∈ TreapNode.all_prios l := by
              rw [← all_prios_union_splitUpper l k]
              right
              simpa [hsplit] using hp
            exact left_le_root p hp_l
          · exact right_le_root
          · exact heap_split_r
          · exact heap_r

-- Splitting creates a BST on the left
theorem splitUpper_IsBST_left (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) :
    IsBST (TreapNode.splitUpper tn k).1 := by have := splitUpper_correct tn k; simp_all

-- Splitting creates a BST on the right
theorem splitUpper_IsBST_right (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) :
    IsBST (TreapNode.splitUpper tn k).2 := by have := splitUpper_correct tn k; simp_all

-- Splitting creates a Heap on the left
theorem splitUpper_IsHeap_left (tn : TreapNode Key Prio) (tn_proof : IsHeap tn) (k : Key) :
    IsHeap (TreapNode.splitUpper tn k).1 := by have := splitUpper_correct tn k; simp_all

-- Splitting creates a Heap on the right
theorem splitUpper_IsHeap_right (tn : TreapNode Key Prio) (tn_proof : IsHeap tn) (k : Key) :
    IsHeap (TreapNode.splitUpper tn k).2 := by have := splitUpper_correct tn k; simp_all

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
