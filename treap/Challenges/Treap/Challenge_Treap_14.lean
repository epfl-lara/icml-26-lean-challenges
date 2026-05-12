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

-- Prove the mergeT has the same behavior as merge
theorem mergeT_correctness (l r : TreapNode Key Prio) :
    (mergeT l r).ret = TreapNode.merge l r := sorry

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
