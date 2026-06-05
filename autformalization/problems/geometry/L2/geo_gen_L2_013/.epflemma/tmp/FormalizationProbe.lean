import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.SmoothEmbedding

open Manifold Set Topology

/-- The curve from the source, represented as a map into `ℝ × ℝ` for `ℝ²`. -/
def gamma : ℝ → ℝ × ℝ := fun t => (t ^ 3, 0)

/--
Source proof: no proof is supplied in `docs/source.tex`; the intended argument is the standard
polynomial-coordinate check.  Prover notes: show the first coordinate `t ↦ t^3` is smooth and the
second coordinate is constant, then combine them for the product map.
-/
theorem gamma_smooth : ContMDiff 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) ⊤ gamma := by
  sorry

/--
Source proof: no proof is supplied in `docs/source.tex`.  Prover notes: the first projection of
`gamma t` is `t^3`; use strict monotonicity/injectivity of cubing on `ℝ` and identify the domain
topology with the subspace topology on the image.
-/
theorem gamma_is_embedding : Topology.IsEmbedding gamma := by
  sorry

/--
Source proof: no proof is supplied in `docs/source.tex`.  Prover notes: compute the derivative of
`t ↦ (t^3, 0)` at `0`; the scalar derivative of `t^3` is `3 * 0^2 = 0`, and the constant coordinate
has derivative zero, so the manifold/Frechet derivative is the zero continuous linear map.
-/
theorem gamma_mfderiv_zero : mfderiv 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) gamma 0 = 0 := by
  sorry

/--
Source proof: no proof is supplied in `docs/source.tex`.  Prover notes: a smooth embedding is an
immersion plus a topological embedding.  Use `gamma_mfderiv_zero` to contradict injectivity of the
tangent map at `0`, since the source tangent space at `0` is nontrivial but the derivative is zero.
The companion declarations `gamma_smooth` and `gamma_is_embedding` formalize the other two claims of
the same source theorem.
-/
theorem gamma_not_smooth_embedding :
    ¬ Manifold.IsSmoothEmbedding 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) ⊤ gamma := by
  sorry
