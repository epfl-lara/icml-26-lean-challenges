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
    IsHeap (TreapNode.merge l r) := sorry

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
