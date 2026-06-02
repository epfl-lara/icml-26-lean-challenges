/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Collodel, Sorrachai Yingchareonthawornchai
-/

import Challenges.Treap.Def_Treap
import Challenges.Treap.Challenge_Treap_1

namespace Cslib.Algorithms.Lean.TimeM
namespace TreapLogic
open Tree

variable {Key : Type} [LinearOrder Key]
variable {Prio : Type} [LinearOrder Prio]

/-
  Merge correctness
-/
-- Merging creates another BST
theorem merge_IsBST (l r : TreapNode Key Prio)
    (l_proof : IsBST l) (r_proof : IsBST r)
    (sorted_l_r : ∀ kl ∈ l.all_keys, ∀ kr ∈ r.all_keys, kl < kr) :
    IsBST (TreapNode.merge l r) := by
  fun_induction TreapNode.merge l r
  · exact IsBST.nil
  · simpa [TreapNode.merge] using r_proof
  · simpa [TreapNode.merge] using l_proof
  case case4 kp_1 l_1 r_1 kp_2 l_2 r_2 h new_l new_r ih1 =>
    subst new_l
    subst new_r
    cases l_proof with
    | node _ _ _ left_lt_root right_ge_root bst_l1 bst_r1 =>
      have sorted_r1_r :
          ∀ kl ∈ TreapNode.all_keys r_1,
            ∀ kr ∈ TreapNode.all_keys (Tree.node kp_2 l_2 r_2 : TreapNode Key Prio),
              kl < kr := by
        intro kl hkl kr hkr
        exact sorted_l_r kl (by simp [TreapNode.all_keys, hkl]) kr hkr
      have bst_new_r : IsBST (TreapNode.merge r_1 (Tree.node kp_2 l_2 r_2)) :=
        ih1 bst_r1 r_proof sorted_r1_r
      apply IsBST.node
      · exact left_lt_root
      · intro k hk
        have hk' :
            k ∈ TreapNode.all_keys r_1 ∪
              TreapNode.all_keys (Tree.node kp_2 l_2 r_2 : TreapNode Key Prio) := by
          rw [all_keys_union_merge]
          exact hk
        cases hk' with
        | inl hk_r1 => exact right_ge_root k hk_r1
        | inr hk_r =>
            exact le_of_lt (sorted_l_r kp_1.key (by simp [TreapNode.all_keys]) k hk_r)
      · exact bst_l1
      · exact bst_new_r
  case case5 kp_1 l_1 r_1 kp_2 l_2 r_2 h new_l new_r ih1 =>
    subst new_l
    subst new_r
    cases r_proof with
    | node _ _ _ left_lt_root right_ge_root bst_l2 bst_r2 =>
      have sorted_l_l2 :
          ∀ kl ∈ TreapNode.all_keys (Tree.node kp_1 l_1 r_1 : TreapNode Key Prio),
            ∀ kr ∈ TreapNode.all_keys l_2, kl < kr := by
        intro kl hkl kr hkr
        exact sorted_l_r kl hkl kr (by simp [TreapNode.all_keys, hkr])
      have bst_new_l : IsBST (TreapNode.merge (Tree.node kp_1 l_1 r_1) l_2) :=
        ih1 l_proof bst_l2 sorted_l_l2
      apply IsBST.node
      · intro k hk
        have hk' :
            k ∈ TreapNode.all_keys (Tree.node kp_1 l_1 r_1 : TreapNode Key Prio) ∪
              TreapNode.all_keys l_2 := by
          rw [all_keys_union_merge]
          exact hk
        cases hk' with
        | inl hk_l => exact sorted_l_r k hk_l kp_2.key (by simp [TreapNode.all_keys])
        | inr hk_l2 => exact left_lt_root k hk_l2
      · exact right_ge_root
      · exact bst_new_l
      · exact bst_r2

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
