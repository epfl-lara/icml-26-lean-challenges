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

lemma split_properties (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) :
    (∀ lk, lk ∈ (TreapNode.split tn k).1.all_keys → lk < k) ∧
    (∀ rk, rk ∈ (TreapNode.split tn k).2.all_keys → k ≤ rk) ∧
    (∀ lk, lk ∈ (TreapNode.splitUpper tn k).1.all_keys → lk ≤ k) ∧
    (∀ rk, rk ∈ (TreapNode.splitUpper tn k).2.all_keys → k < rk) := by
  induction tn_proof with
  | nil =>
      simp [TreapNode.split, TreapNode.splitUpper, TreapNode.all_keys]
  | node kp l r hlt hge bst_l bst_r ih_l ih_r =>
      constructor
      · intro lk hlk
        by_cases h : kp.key < k
        · have hlk' :
              (lk = kp.key ∨ lk ∈ l.all_keys) ∨
                lk ∈ (TreapNode.split r k).1.all_keys := by
            simpa [TreapNode.split, h, TreapNode.all_keys] using hlk
          rcases hlk' with (hroot | hl) | hr
          · subst lk
            exact h
          · exact lt_trans (hlt lk hl) h
          · exact ih_r.1 lk hr
        · have hlk' : lk ∈ (TreapNode.split l k).1.all_keys := by
            simpa [TreapNode.split, h] using hlk
          exact ih_l.1 lk hlk'
      constructor
      · intro rk hrk
        by_cases h : kp.key < k
        · have hrk' : rk ∈ (TreapNode.split r k).2.all_keys := by
            simpa [TreapNode.split, h] using hrk
          exact ih_r.2.1 rk hrk'
        · have hrk' :
              (rk = kp.key ∨ rk ∈ (TreapNode.split l k).2.all_keys) ∨
                rk ∈ r.all_keys := by
            simpa [TreapNode.split, h, TreapNode.all_keys] using hrk
          rcases hrk' with (hroot | hl) | hr
          · subst rk
            exact le_of_not_gt h
          · exact ih_l.2.1 rk hl
          · exact le_trans (le_of_not_gt h) (hge rk hr)
      constructor
      · intro lk hlk
        by_cases h : kp.key ≤ k
        · have hlk' :
              (lk = kp.key ∨ lk ∈ l.all_keys) ∨
                lk ∈ (TreapNode.splitUpper r k).1.all_keys := by
            simpa [TreapNode.splitUpper, h, TreapNode.all_keys] using hlk
          rcases hlk' with (hroot | hl) | hr
          · subst lk
            exact h
          · exact le_trans (le_of_lt (hlt lk hl)) h
          · exact ih_r.2.2.1 lk hr
        · have hlk' : lk ∈ (TreapNode.splitUpper l k).1.all_keys := by
            simpa [TreapNode.splitUpper, h] using hlk
          exact ih_l.2.2.1 lk hlk'
      · intro rk hrk
        by_cases h : kp.key ≤ k
        · have hrk' : rk ∈ (TreapNode.splitUpper r k).2.all_keys := by
            simpa [TreapNode.splitUpper, h] using hrk
          exact ih_r.2.2.2 rk hrk'
        · have hrk' :
              (rk = kp.key ∨ rk ∈ (TreapNode.splitUpper l k).2.all_keys) ∨
                rk ∈ r.all_keys := by
            simpa [TreapNode.splitUpper, h, TreapNode.all_keys] using hrk
          have hklt : k < kp.key := lt_of_not_ge h
          rcases hrk' with (hroot | hl) | hr
          · subst rk
            exact hklt
          · exact ih_l.2.2.2 rk hl
          · exact lt_of_lt_of_le hklt (hge rk hr)

-- All keys on the left of a split k are < k
lemma split_left_lt_k (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) :
    ∀ lk, lk ∈ (TreapNode.split tn k).1.all_keys → lk < k :=
  (split_properties tn tn_proof k).1

-- All keys on the right of a split k are ≥ k
lemma split_right_ge_k (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) :
    ∀ rk, rk ∈ (TreapNode.split tn k).2.all_keys → k ≤ rk :=
  (split_properties tn tn_proof k).2.1

-- All keys on the left of a splitUpper k are ≤ k
lemma splitUpper_left_le_k (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) :
    ∀ lk, lk ∈ (TreapNode.splitUpper tn k).1.all_keys → lk ≤ k :=
  (split_properties tn tn_proof k).2.2.1

-- All keys on the right of a splitUpper k are > k
lemma splitUpper_right_gt_k (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) :
    ∀ rk, rk ∈ (TreapNode.splitUpper tn k).2.all_keys → k < rk :=
  (split_properties tn tn_proof k).2.2.2

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
