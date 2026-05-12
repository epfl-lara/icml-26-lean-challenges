/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Collodel, Sorrachai Yingchareonthawornchai
-/

import Challenges.Treap.Challenge_Analysis_1

open MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {n : ℕ}

-- Calculate the expected depth
theorem expected_depth (k : Fin n) :
    ∫ ω, depth k ω ∂P ≤ 1 + 2 * Real.log n := sorry
