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
  Merge correctness
-/

-- Merging creates another Heap
theorem merge_IsHeap (l r : TreapNode Key Prio)
    (l_proof : IsHeap l) (r_proof : IsHeap r) :
    IsHeap (TreapNode.merge l r) := by
  have all_prios_union_merge :
      ∀ (l r : TreapNode Key Prio),
        l.all_prios ∪ r.all_prios = (TreapNode.merge l r).all_prios := by
    intro l r
    fun_induction TreapNode.merge l r
    · simp [TreapNode.all_prios]
    · simp [TreapNode.all_prios]
    · simp [TreapNode.all_prios]
    case case4 kp_1 l_1 r_1 kp_2 l_2 r_2 h new_l new_r ih1 =>
      subst new_l
      subst new_r
      simp [TreapNode.all_prios] at ih1 ⊢
      rw [← ih1]
      ext x
      simp [or_assoc, or_left_comm]
    case case5 kp_1 l_1 r_1 kp_2 l_2 r_2 h new_l new_r ih1 =>
      subst new_l
      subst new_r
      simp [TreapNode.all_prios] at ih1 ⊢
      rw [← ih1]
      ext x
      simp [or_assoc, or_left_comm]
  have heap_root_bound :
      ∀ (kp : KeyPrioPair Key Prio) (l r : TreapNode Key Prio),
        IsHeap (Tree.node kp l r) →
        ∀ p, p ∈ TreapNode.all_prios (Tree.node kp l r : TreapNode Key Prio) → p ≤ kp.prio := by
    intro kp l r hheap p hp
    cases hheap with
    | node _ _ _ left_le_root right_le_root _ _ =>
        simp [TreapNode.all_prios] at hp
        rcases hp with hp_lr | hp_right
        · rcases hp_lr with hp_root | hp_left
          · simp [hp_root]
          · exact left_le_root p hp_left
        · exact right_le_root p hp_right
  fun_induction TreapNode.merge l r
  · exact IsHeap.nil
  · simpa [TreapNode.merge] using r_proof
  · simpa [TreapNode.merge] using l_proof
  case case4 kp_1 l_1 r_1 kp_2 l_2 r_2 h new_l new_r ih1 =>
    subst new_l
    subst new_r
    cases l_proof with
    | node _ _ _ left_le_root right_le_root heap_l1 heap_r1 =>
      have heap_new_r : IsHeap (TreapNode.merge r_1 (Tree.node kp_2 l_2 r_2)) :=
        ih1 heap_r1 r_proof
      apply IsHeap.node
      · exact left_le_root
      · intro p hp
        have hp' :
            p ∈ TreapNode.all_prios r_1 ∪
              TreapNode.all_prios (Tree.node kp_2 l_2 r_2 : TreapNode Key Prio) := by
          rw [all_prios_union_merge]
          exact hp
        cases hp' with
        | inl hp_r1 => exact right_le_root p hp_r1
        | inr hp_r =>
            exact le_trans (heap_root_bound kp_2 l_2 r_2 r_proof p hp_r) h
      · exact heap_l1
      · exact heap_new_r
  case case5 kp_1 l_1 r_1 kp_2 l_2 r_2 h new_l new_r ih1 =>
    subst new_l
    subst new_r
    cases r_proof with
    | node _ _ _ left_le_root right_le_root heap_l2 heap_r2 =>
      have heap_new_l : IsHeap (TreapNode.merge (Tree.node kp_1 l_1 r_1) l_2) :=
        ih1 l_proof heap_l2
      have hle : kp_1.prio ≤ kp_2.prio := le_of_lt (lt_of_not_ge h)
      apply IsHeap.node
      · intro p hp
        have hp' :
            p ∈ TreapNode.all_prios (Tree.node kp_1 l_1 r_1 : TreapNode Key Prio) ∪
              TreapNode.all_prios l_2 := by
          rw [all_prios_union_merge]
          exact hp
        cases hp' with
        | inl hp_l =>
            exact le_trans (heap_root_bound kp_1 l_1 r_1 l_proof p hp_l) hle
        | inr hp_l2 =>
            exact left_le_root p hp_l2
      · exact right_le_root
      · exact heap_new_l
      · exact heap_r2

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
