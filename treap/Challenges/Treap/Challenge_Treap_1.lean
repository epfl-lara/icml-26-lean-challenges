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
  Operations correctness - Ensure every operation which creates a new treap satisfies
  the treap properties
-/

-- Merging two treaps results in all keys being the union of both
theorem all_keys_union_merge (l r : TreapNode Key Prio) :
    l.all_keys ∪ r.all_keys = (TreapNode.merge l r).all_keys := by
  fun_induction TreapNode.merge l r
  · simp [TreapNode.all_keys]
  · simp [TreapNode.all_keys]
  · simp [TreapNode.all_keys]
  case case4 kp_1 l_1 r_1 kp_2 l_2 r_2 h new_l new_r ih1 =>
    subst new_l
    subst new_r
    ext x
    simp only [TreapNode.all_keys, Set.mem_union] at ih1 ⊢
    rw [← ih1]
    simp only [Set.mem_union]
    tauto
  case case5 kp_1 l_1 r_1 kp_2 l_2 r_2 h new_l new_r ih1 =>
    subst new_l
    subst new_r
    ext x
    simp only [TreapNode.all_keys, Set.mem_union] at ih1 ⊢
    rw [← ih1]
    simp only [Set.mem_union]
    tauto

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
