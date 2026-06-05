import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/--
An axis-aligned open rectangle in `ℝ × ℝ`, represented as a Cartesian product of
open real intervals. This companion definition records the convention used for
the source phrase "open rectangles".
-/
def IsOpenRectangle (R : Set (ℝ × ℝ)) : Prop :=
  ∃ a b c d : ℝ, a < b ∧ c < d ∧ R = Set.Ioo a b ×ˢ Set.Ioo c d

/--
Source theorem `line-17` (`open_disc_not_disjoint_union_rectangles`): an open disc
in `ℝ^2` is not the disjoint union of open rectangles.

Source proof: no proof is supplied in `docs/source.tex`.
Proof sketch: interpret the disc as the genuine Euclidean disc
`{p | (p.1 - c.1)^2 + (p.2 - c.2)^2 < r^2}` in `ℝ × ℝ` and open rectangles as
products of open intervals. A later proof can use connectedness or
path-connectedness of the disc: a pairwise-disjoint cover by nonempty open
rectangles would force at most one rectangle, and a positive-radius round disc is
not a single axis-aligned open rectangle.

Representation note: the disc must be the EUCLIDEAN disc, written out explicitly as
a quadratic inequality. Mathlib's `Metric.ball`/`dist` on `ℝ × ℝ` use the sup
(L∞) metric, so they describe an axis-aligned open SQUARE, which is itself an open
rectangle; using them here would make the theorem false. This matches `Skeleton4`.

Prover notes: `hrectangles` makes every family member a nonempty open rectangle;
`hdisjoint` is the formal disjointness condition; the conclusion denies equality
with the indexed union of the family.
-/
theorem open_disc_not_disjoint_union_rectangles
    (center : ℝ × ℝ) (radius : ℝ) (hradius : 0 < radius)
    (ι : Type*) (rectangles : ι → Set (ℝ × ℝ))
    (hrectangles : ∀ i, IsOpenRectangle (rectangles i))
    (hdisjoint : Pairwise (fun i j => Disjoint (rectangles i) (rectangles j))) :
    {p : ℝ × ℝ | (p.1 - center.1) ^ 2 + (p.2 - center.2) ^ 2 < radius ^ 2} ≠
      ⋃ i, rectangles i := by
  sorry
