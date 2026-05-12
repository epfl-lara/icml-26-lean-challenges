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
  Operations correctness - Ensure every operation which creates a new treap satisfies the treap properties
-/

-- Merging two treaps results in all keys being the union of both
theorem all_keys_union_merge (l r : TreapNode Key Prio) :
    l.all_keys ∪ r.all_keys = (TreapNode.merge l r).all_keys := sorry

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
