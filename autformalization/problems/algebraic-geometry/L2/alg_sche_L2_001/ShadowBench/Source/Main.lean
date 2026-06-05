import Mathlib.AlgebraicGeometry.FunctionField

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits TopCat
open AlgebraicGeometry

/--
Source inventory entry: `line-17`.
Source locator: `line-17` in `docs/source.tex`.

Source proof: The function field of `Spec R` is the stalk of the structure sheaf at
the generic point. For an integral domain, that generic point is the zero prime,
and the stalk at the zero prime is the localization of `R` at its nonzero
elements, i.e. the field of fractions.

Prover notes: Mathlib's algebraic-geometry API represents “is the field of
fractions” by `IsFractionRing`. After importing
`Mathlib.AlgebraicGeometry.FunctionField`, the namespaced affine-domain instance
`AlgebraicGeometry.functionField_isFractionRing_of_affine R` should provide the
proof after statement/source review.
-/
theorem functionField_isFractionRing_of_affine (R : CommRingCat) [IsDomain R] :
    IsFractionRing R (Spec R).functionField := by
  exact AlgebraicGeometry.functionField_isFractionRing_of_affine R
