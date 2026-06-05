import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Convex.Cone.Basic

open InnerProductSpace
open scoped BigOperators

/--
The set of coefficient pairs `(a,b)` representing hyperplanes that weakly separate
`C` from `D`: every point of `C` lies on the `≤ b` side and every point of `D`
lies on the `≥ b` side.

This records the source's representation of a subset of `ℝ^{n+1}` as
`(Fin n → ℝ) × ℝ`, with `a^T x` represented by a finite dot-product sum.
-/
def separatingHyperplanesSet (n : ℕ) (C D : Set (Fin n → ℝ)) :
    Set ((Fin n → ℝ) × ℝ) :=
  {p | (∀ x ∈ C, (∑ i, p.1 i * x i) ≤ p.2) ∧
      (∀ x ∈ D, p.2 ≤ (∑ i, p.1 i * x i))}

/--
Source theorem `separatingHyperplanes_is_pointed` (`docs/source.tex`, lines 17--37):
for disjoint subsets `C,D ⊆ ℝ^n`, the coefficient pairs `(a,b)` satisfying
`a^T x ≤ b` on `C` and `a^T x ≥ b` on `D` form a convex cone containing the
origin. The source also says this set is `{0}` if there is no separating
hyperplane.

Source proof: multiply the defining inequalities by a nonnegative scalar to get
closure under scalar multiplication; add inequalities for two separating pairs to
get closure under addition; `(0,0)` satisfies both inequalities. Prover notes:
construct the `ConvexCone` from these two closure arguments, use finite-sum
rewrites for dot products, and prove the singleton clause by `Set.ext` from the
assumption that every separating pair is zero plus origin membership.
-/
theorem separatingHyperplanes_is_pointed
    (n : ℕ) (C D : Set (Fin n → ℝ)) (h_disjoint : Disjoint C D) :
    ∃ K : ConvexCone ℝ ((Fin n → ℝ) × ℝ),
        (K : Set ((Fin n → ℝ) × ℝ)) = separatingHyperplanesSet n C D ∧
        ConvexCone.Pointed K := by
  sorry
