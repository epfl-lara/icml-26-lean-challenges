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
  Split complexity
-/

-- Prove the splitT has the same behavior as split
theorem splitT_correctness (tn : TreapNode Key Prio) (k : Key) :
    (splitT tn k).ret = TreapNode.split tn k := sorry

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
