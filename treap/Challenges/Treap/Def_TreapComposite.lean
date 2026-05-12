/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Collodel, Sorrachai Yingchareonthawornchai
-/

import Challenges.Treap.Def_Treap
import Challenges.Treap.Challenge_Treap_1
import Challenges.Treap.Challenge_Treap_2
import Challenges.Treap.Challenge_Treap_3
import Challenges.Treap.Challenge_Treap_4
import Challenges.Treap.Challenge_Treap_5
import Challenges.Treap.Challenge_Treap_6

namespace Cslib.Algorithms.Lean.TimeM
namespace TreapLogic
open Tree

set_option linter.style.longLine false

variable {Key : Type} [LinearOrder Key]
variable {Prio : Type} [LinearOrder Prio]

-- Prove the resulting treaps satisfy the treap properties
def Treap.split (t : Treap Key Prio) (k : Key) : Treap Key Prio × Treap Key Prio :=
  let split_res := t.root.split k
  -- Construct treap proofs for l and r
  let l_bst_proof := split_IsBST_left t.root t.is_treap.2 k
  let r_bst_proof := split_IsBST_right t.root t.is_treap.2 k
  let l_heap_proof := split_IsHeap_left t.root t.is_treap.1 k
  let r_heap_proof := split_IsHeap_right t.root t.is_treap.1 k
  have l_treap_proof : IsTreap split_res.1 := by
    subst split_res
    simp_all [IsTreap]
  have r_treap_proof : IsTreap split_res.2 := by
    subst split_res
    simp_all [IsTreap]
  let l_treap := { root := (t.root.split k).1, is_treap := l_treap_proof }
  let r_treap := { root := (t.root.split k).2, is_treap := r_treap_proof }
  (l_treap, r_treap)

-- Repeat the same for splitUpper
def Treap.splitUpper (t : Treap Key Prio) (k : Key) : Treap Key Prio × Treap Key Prio :=
  let split_res := t.root.splitUpper k
  -- Construct treap proofs for l and r
  let l_bst_proof := splitUpper_IsBST_left t.root t.is_treap.2 k
  let r_bst_proof := splitUpper_IsBST_right t.root t.is_treap.2 k
  let l_heap_proof := splitUpper_IsHeap_left t.root t.is_treap.1 k
  let r_heap_proof := splitUpper_IsHeap_right t.root t.is_treap.1 k
  have l_treap_proof : IsTreap split_res.1 := by
    subst split_res
    simp_all [IsTreap]
  have r_treap_proof : IsTreap split_res.2 := by
    subst split_res
    simp_all [IsTreap]
  let l_treap := { root := (t.root.splitUpper k).1, is_treap := l_treap_proof }
  let r_treap := { root := (t.root.splitUpper k).2, is_treap := r_treap_proof }
  (l_treap, r_treap)

-- Prove the merged treap satisfies the treap properties
def Treap.merge (l r : Treap Key Prio)
(sorted_l_r : ∀ kl ∈ l.root.all_keys, ∀ kr ∈ r.root.all_keys, kl < kr) : Treap Key Prio :=
  let root_merged := TreapNode.merge l.root r.root
  let bst_proof := merge_IsBST l.root r.root l.is_treap.2 r.is_treap.2 sorted_l_r
  let heap_proof := merge_IsHeap l.root r.root l.is_treap.1 r.is_treap.1
  have treap_proof : IsTreap root_merged := by
    subst root_merged
    simp_all [IsTreap]
  { root := root_merged, is_treap := treap_proof }

/-
  Composite operations

  We now define more operations on Treaps, and prove their correctness.
  These operations will be:
  - find
  - insert
  - delete

  We'll not prove complexity of these operations, since they are direct compositions of
  previously defined operations whose complexity has already been analyzed.

  We will however prove their behavioral correctness.
-/

-- Returns none if the key is not found, some (key,prio) if it is found
def Treap.find (t : Treap Key Prio) (k : Key) : Option (KeyPrioPair Key Prio) :=
  let split := t.split k
  match split.2.root.leftmost with
  | none => none
  | some kp =>
    if kp.key = k then
      some kp
    else
      none

-- We discard other existing occurrences of the same key
def Treap.insert (t : Treap Key Prio) (kp : KeyPrioPair Key Prio) : Treap Key Prio :=
  let split_l_key := t.split kp.key
  -- Save split proofs
  have l_lt_k := split_left_lt_k t.root t.is_treap.2 kp.key
  have r_ge_k := split_right_ge_k t.root t.is_treap.2 kp.key

  let split_key_r := t.splitUpper kp.key
  -- Save splitUpper proofs
  have l_le_k := splitUpper_left_le_k t.root t.is_treap.2 kp.key
  have r_gt_k := splitUpper_right_gt_k t.root t.is_treap.2 kp.key


  let new_node := Treap.singleton kp

  -- We need new_node < r
  have kp_lt_r : (∀ kl ∈ new_node.root.all_keys, ∀ kr ∈ TreapNode.all_keys split_key_r.2.root, kl < kr) := by
    subst new_node
    subst split_key_r
    subst split_l_key
    simp_all [Treap.singleton, TreapNode.singleton, TreapNode.all_keys]
    exact r_gt_k

  let merged_right := Treap.merge new_node split_key_r.2 kp_lt_r -- First merge right (ensures l < r)

  -- We need l < new_node ∪ r
  have l_lt_kp_r : (∀ kl ∈ TreapNode.all_keys split_l_key.1.root, ∀ kr ∈ merged_right.root.all_keys, kl < kr) := by
    subst merged_right
    subst new_node
    subst split_key_r
    subst split_l_key
    simp_all [Treap.merge, Treap.split, Treap.singleton, TreapNode.singleton, TreapNode.all_keys]
    simp [Treap.singleton, TreapNode.singleton, TreapNode.all_keys] at kp_lt_r
    suffices ∀ kl ∈ (t.root.split kp.key).1.all_keys, kl < kp.key by
      rw [← all_keys_union_merge]
      simp_all only [Set.mem_union]
      intro kl kl_h kr kr_h
      cases kr_h <;> rename_i kr_h
      · simp [TreapNode.all_keys] at kr_h
        rw [kr_h]
        revert kr kl_h kl
        simp
        exact this
      · grind
    simp_all
  Treap.merge split_l_key.1 merged_right l_lt_kp_r

-- Deletes the key only if it exists, otherwise doesn't do anything
def Treap.delete (t : Treap Key Prio) (k : Key) : Treap Key Prio :=
  let split_l_key := t.split k
  -- Save split proofs
  have l_lt_k := split_left_lt_k t.root t.is_treap.2 k
  have r_ge_k := split_right_ge_k t.root t.is_treap.2 k
  let split_key_r := t.splitUpper k
  -- Save splitUpper proofs
  have l_le_k := splitUpper_left_le_k t.root t.is_treap.2 k
  have r_gt_k := splitUpper_right_gt_k t.root t.is_treap.2 k
  -- We need new_node < r
  have l_lt_r : (∀ kl ∈ TreapNode.all_keys split_l_key.1.root, ∀ kr ∈ TreapNode.all_keys split_key_r.2.root, kl < kr) := by
    intro kl hkl kr hkr
    trans k
    · revert kl hkl
      assumption
    · revert kr hkr
      assumption
  Treap.merge split_l_key.1 split_key_r.2 l_lt_r

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
