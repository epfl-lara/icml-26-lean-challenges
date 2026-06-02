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

-- Prove the splitUpperT has the same behavior as splitUpper
theorem splitUpperT_correctness (tn : TreapNode Key Prio) (k : Key) :
    (splitUpperT tn k).ret = TreapNode.splitUpper tn k := by
  induction tn with
  | nil =>
      simp [splitUpperT, TreapNode.splitUpper]
  | node kp l r ih_l ih_r =>
      by_cases h : kp.key ≤ k
      · simp [splitUpperT, TreapNode.splitUpper, h, ih_r]
      · simp [splitUpperT, TreapNode.splitUpper, h, ih_l]

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
