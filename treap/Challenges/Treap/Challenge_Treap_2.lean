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
    (∀ rk, rk ∈ (TreapNode.splitUpper tn k).2.all_keys → k < rk) := sorry

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
