import Mathlib.Analysis.InnerProductSpace.EuclideanDist

open Euclidean

theorem open_disc_not_disjoint_union_rectangles :
    ∀ (c : ℝ × ℝ) (r : ℝ) (hr : 0 < r) (I : Type*) (R : I → Set (ℝ × ℝ)),
      (∀ i, ∃ a b c' d : ℝ, a < b ∧ c' < d ∧ R i = Set.Ioo a b ×ˢ Set.Ioo c' d) →
      (∀ i j, i ≠ j → Disjoint (R i) (R j)) →
      {p : ℝ × ℝ | (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 < r ^ 2} ≠ ⋃ i, R i := by sorry
