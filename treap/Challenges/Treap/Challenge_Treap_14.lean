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
    (mergeT l r).ret = TreapNode.merge l r := by
  induction l generalizing r with
  | nil =>
      cases r <;> simp [mergeT, TreapNode.merge]
  | node kp₁ l₁ r₁ ih_l ih_r =>
      cases r with
      | nil => simp [mergeT, TreapNode.merge]
      | node kp₂ l₂ r₂ =>
          by_cases h : kp₁.prio ≥ kp₂.prio
          · simp [mergeT, TreapNode.merge, h, ih_r]
          · simp only [mergeT, ge_iff_le, h, ↓reduceIte, bind_pure_comp, ret_bind, ret_map,
              TreapNode.merge, node.injEq, and_true, true_and]
            induction l₂ with
            | nil =>
                simp [mergeT, TreapNode.merge]
            | node kp₃ l₃ r₃ ih_l₂_l ih_l₂_r =>
                by_cases h₂ : kp₁.prio ≥ kp₃.prio
                · simp [mergeT, TreapNode.merge, h₂, ih_r]
                · simp [mergeT, TreapNode.merge, h₂, ih_l₂_l]

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
