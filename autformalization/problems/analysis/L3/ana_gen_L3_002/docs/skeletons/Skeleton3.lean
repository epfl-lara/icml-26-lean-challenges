import Mathlib.Analysis.InnerProductSpace.EuclideanDist

open Set

theorem open_disc_not_disjoint_union_rectangles : 
  ∀ (center : ℝ × ℝ) (radius : ℝ), radius > 0 → 
  ¬ ∃ (rectangles : Set (ℝ × ℝ × ℝ × ℝ)), 
    (∀ (a b c d : ℝ), (a, b, c, d) ∈ rectangles ↔ (a < b ∧ c < d)) ∧
    (⋃ (p : ℝ × ℝ × ℝ × ℝ) (hp : p ∈ rectangles), 
      Set.prod (Set.Ioo p.1 p.2.1) (Set.Ioo p.2.2.1 p.2.2.2)) = 
    {x : ℝ × ℝ | dist x center < radius} ∧
    ∀ (p q : ℝ × ℝ × ℝ × ℝ), p ∈ rectangles → q ∈ rectangles → p ≠ q → 
      Disjoint (Set.prod (Set.Ioo p.1 p.2.1) (Set.Ioo p.2.2.1 p.2.2.2)) 
               (Set.prod (Set.Ioo q.1 q.2.1) (Set.Ioo q.2.2.1 q.2.2.2)) := by sorry
