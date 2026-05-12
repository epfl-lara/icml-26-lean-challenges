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
-- Merging creates another BST
theorem merge_IsBST (l r : TreapNode Key Prio)
    (l_proof : IsBST l) (r_proof : IsBST r)
    (sorted_l_r : ∀ kl ∈ l.all_keys, ∀ kr ∈ r.all_keys, kl < kr) :
    IsBST (TreapNode.merge l r) := sorry

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
