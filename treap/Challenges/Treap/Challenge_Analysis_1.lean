/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Collodel, Sorrachai Yingchareonthawornchai
-/

import Challenges.Treap.Def_Analysis

open MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {n : ℕ}

-- Calculate the expected value of being an ancestor
theorem prob_is_ancestor (j k : Fin n) :
  ∫ ω, isAncestor j k ω ∂P = 1 / (Finset.Icc (min j k) (max j k)).card := sorry
