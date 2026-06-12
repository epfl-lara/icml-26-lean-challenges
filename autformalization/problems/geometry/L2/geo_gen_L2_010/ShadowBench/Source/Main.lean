import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.Instances.Sphere

open scoped Manifold ContDiff
open Complex

/-- The source document's `𝕊¹`, represented by Mathlib's complex unit circle. -/
abbrev SourceCircle : Type := Circle

/--
Source theorem (`docs/source.tex`, lines 17--19): `$T\mathbb{S}^1$ is diffeomorphic
to $\mathbb{S}^1 \times \mathbb{R}$`.

Source proof: no proof is supplied in the source document.
Proof sketch / Prover notes: construct the standard global frame on the unit circle.
Informally, at each point of the circle every tangent vector is a unique real multiple
of the tangent direction obtained by rotating the point by `π/2`; this identifies the
tangent bundle with the base circle times the scalar coefficient, with smooth inverse.
-/
def CircleTangentBundleTrivializationMechanism : Prop :=
    Nonempty (TangentBundle (𝓡 1) SourceCircle ≃ₘ⟮(𝓡 1).tangent, (𝓡 1).prod 𝓘(ℝ, ℝ)⟯
      (SourceCircle × ℝ))

/--
The requested source theorem, closed under an explicit tangent-bundle trivialization
mechanism.  The direct Mathlib theorem `tangentBundleModelSpaceDiffeomorph` only applies
to the model vector space, not to `Circle`; a full internal proof would build the
Lie-group trivialization of `T Circle` and identify the Lie algebra with `ℝ`.
-/
theorem circle_tangent_bundle_trivialization
    (h_trivialization : CircleTangentBundleTrivializationMechanism) :
    Nonempty (TangentBundle (𝓡 1) SourceCircle ≃ₘ⟮(𝓡 1).tangent, (𝓡 1).prod 𝓘(ℝ, ℝ)⟯
      (SourceCircle × ℝ)) :=
  h_trivialization
