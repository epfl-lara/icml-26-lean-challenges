import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Real.Hom

open Set

/--
An explicit affine-function bridge for real-valued functions on `ℝ^n`, represented
in Lean as functions on `Fin n → ℝ`. The source proof obtains a continuous
linear functional from Hahn--Banach and then adds a constant.
-/
def IsAffineRealMap {n : ℕ} (h : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ l : ((Fin n → ℝ) →L[ℝ] ℝ), ∃ b : ℝ, ∀ x, h x = l x + b

/--
Source theorem `line-17` from `docs/source.tex`: a convex finite-valued function
`f : ℝ^n → ℝ` above a concave finite-valued function `g : ℝ^n → ℝ` admits an
affine separator `h` with `g x ≤ h x ≤ f x` for every `x`.

Proof sketch: form the strict upper epigraph `E = {(x,t) | t > f x}` and strict
lower hypograph `H = {(x,t) | t < g x}` in `ℝ^n × ℝ`. They are nonempty,
open, convex, and disjoint. Separate them by the open-open geometric Hahn--Banach
theorem, write the separating functional as `A x + c t`, prove `c > 0`, and set
`h x = (u - A x) / c`. The epsilon argument in the source then gives
`g x ≤ h x ≤ f x`.

Prover notes: the Lean statement represents the affine function as `x ↦ l x + b`,
where `l : (Fin n → ℝ) →L[ℝ] ℝ` and `b : ℝ`, matching the linear-functional-plus-
constant construction from the source proof.
-/
theorem exists_affine_between_of_concaveOn_le_convexOn {n : ℕ}
    (f g : (Fin n → ℝ) → ℝ)
    (hf : ConvexOn ℝ Set.univ f)
    (hg : ConcaveOn ℝ Set.univ g)
    (hfg : ∀ x, g x ≤ f x) :
    ∃ h : (Fin n → ℝ) → ℝ, IsAffineRealMap h ∧
      ∀ x, g x ≤ h x ∧ h x ≤ f x := by
  sorry
