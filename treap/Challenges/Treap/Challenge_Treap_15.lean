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

-- Prove the mergeT is bounded by sum of heights
theorem mergeT_time (l r : TreapNode Key Prio) :
    (mergeT l r).time ≤ l.height + r.height := sorry

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
