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

-- Prove the splitUpperT is bounded by 1 + tn.height
theorem splitUpperT_time (tn : TreapNode Key Prio) (k : Key) :
    (splitUpperT tn k).time ≤ 1 + tn.height := by
  induction tn with
  | nil =>
      simp [splitUpperT]
  | node kp l r ih_l ih_r =>
      by_cases h : kp.key ≤ k
      · simp [splitUpperT, h]
        omega
      · simp [splitUpperT, h]
        omega

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
