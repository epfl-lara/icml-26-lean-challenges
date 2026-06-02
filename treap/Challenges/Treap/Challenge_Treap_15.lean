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
    (mergeT l r).time ≤ l.height + r.height := by
  induction l generalizing r with
  | nil =>
      cases r <;> simp [mergeT]
  | node kp₁ l₁ r₁ ih_l ih_r =>
      cases r with
      | nil => simp [mergeT]
      | node kp₂ l₂ r₂ =>
          by_cases h : kp₁.prio ≥ kp₂.prio
          · simp [mergeT, h]
            have hr := ih_r (Tree.node kp₂ l₂ r₂)
            simp at hr
            omega
          · have hrec : (mergeT (Tree.node kp₁ l₁ r₁) l₂).time ≤
                (Tree.node kp₁ l₁ r₁ : TreapNode Key Prio).height + l₂.height := by
                induction l₂ with
                | nil =>
                    simp [mergeT]
                | node kp₃ l₃ r₃ ih_l₂_l ih_l₂_r =>
                    by_cases h₂ : kp₁.prio ≥ kp₃.prio
                    · simp [mergeT, h₂]
                      have hr := ih_r (Tree.node kp₃ l₃ r₃)
                      simp at hr
                      omega
                    · simp [mergeT, h₂]
                      simp at ih_l₂_l
                      omega
            simp [mergeT, h]
            simp at hrec
            omega

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
