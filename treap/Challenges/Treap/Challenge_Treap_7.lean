/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Collodel, Sorrachai Yingchareonthawornchai
-/

import Challenges.Treap.Def_TreapComposite

namespace Cslib.Algorithms.Lean.TimeM
namespace TreapLogic
open Tree

variable {Key : Type} [LinearOrder Key]
variable {Prio : Type} [LinearOrder Prio]

/-
  Insert correctness

  Inserting an element adds it to the set of keys of the treap, regardless of
  whether it was already present or not.

-/
theorem insert_inserts_element (t : Treap Key Prio) (ins_kp : KeyPrioPair Key Prio) :
    (Treap.insert t ins_kp).root.all_keys = (t.root.all_keys \ {ins_kp.key}) ∪ {ins_kp.key} := by
  have all_keys_union_split :
      ∀ (tn : TreapNode Key Prio) (k : Key),
        (TreapNode.split tn k).1.all_keys ∪ (TreapNode.split tn k).2.all_keys =
          tn.all_keys := by
    intro tn k
    fun_induction TreapNode.split tn k
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
  have h_insert :
      (Treap.insert t ins_kp).root.all_keys =
        (((TreapNode.split t.root ins_kp.key).1.all_keys ∪ {ins_kp.key}) ∪
          (TreapNode.splitUpper t.root ins_kp.key).2.all_keys) := by
    simp only [Treap.insert, Treap.merge, Treap.split, Treap.splitUpper,
      Treap.singleton]
    rw [← all_keys_union_merge (TreapNode.split t.root ins_kp.key).1
      (TreapNode.merge (TreapNode.singleton ins_kp)
        (TreapNode.splitUpper t.root ins_kp.key).2)]
    rw [← all_keys_union_merge (TreapNode.singleton ins_kp)
      (TreapNode.splitUpper t.root ins_kp.key).2]
    ext x
    simp [TreapNode.singleton, TreapNode.all_keys, or_assoc]
  rw [h_insert]
  ext x
  constructor
  · intro hx
    simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with (hxL | hxk) | hxR
    · left
      constructor
      · have hxU :
            x ∈ (TreapNode.split t.root ins_kp.key).1.all_keys ∪
              (TreapNode.split t.root ins_kp.key).2.all_keys := Or.inl hxL
        simpa [all_keys_union_split t.root ins_kp.key] using hxU
      · exact ne_of_lt (split_left_lt_k t.root t.is_treap.2 ins_kp.key x hxL)
    · right
      exact hxk
    · left
      constructor
      · have hxU :
            x ∈ (TreapNode.splitUpper t.root ins_kp.key).1.all_keys ∪
              (TreapNode.splitUpper t.root ins_kp.key).2.all_keys := Or.inr hxR
        simpa [all_keys_union_splitUpper t.root ins_kp.key] using hxU
      · exact ne_of_gt (splitUpper_right_gt_k t.root t.is_treap.2 ins_kp.key x hxR)
  · intro hx
    simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with ⟨hx_all, hx_ne⟩ | hxk
    · by_cases hlt : x < ins_kp.key
      · left
        left
        have hxU :
            x ∈ (TreapNode.split t.root ins_kp.key).1.all_keys ∪
              (TreapNode.split t.root ins_kp.key).2.all_keys := by
          simpa [all_keys_union_split t.root ins_kp.key] using hx_all
        rcases hxU with hxL | hxR
        · exact hxL
        · have hge := split_right_ge_k t.root t.is_treap.2 ins_kp.key x hxR
          exact False.elim ((not_lt_of_ge hge) hlt)
      · right
        have hgt : ins_kp.key < x := by
          exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hx_ne)
        have hxU :
            x ∈ (TreapNode.splitUpper t.root ins_kp.key).1.all_keys ∪
              (TreapNode.splitUpper t.root ins_kp.key).2.all_keys := by
          simpa [all_keys_union_splitUpper t.root ins_kp.key] using hx_all
        rcases hxU with hxL | hxR
        · have hle := splitUpper_left_le_k t.root t.is_treap.2 ins_kp.key x hxL
          exact False.elim ((not_lt_of_ge hle) hgt)
        · exact hxR
    · left
      right
      exact hxk

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
