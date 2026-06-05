import Mathlib

open Filter TopologicalSpace
open scoped Topology

/-!
# ShadowBench analysis/L2/ana_gen_L2_004

Formalization draft for `docs/source.tex`.
-/

/--
Source theorem `line-17` (`exists_seq_finite_rank_strongly_convergent_to`) states
that on a separable Hilbert space every bounded operator is the strong limit of
finite-rank bounded operators.

Source proof: choose a countable orthonormal basis, let `T_seq n` agree with `T`
on the first `n` basis vectors and vanish on the remaining basis vectors, so each
`T_seq n` has finite-dimensional range. For convergence, prove convergence first
on finite linear combinations of basis vectors, then approximate an arbitrary
vector and use boundedness plus the triangle inequality.

Prover notes: the source proof's final sentence should be read with the standard
density/approximation argument; it is not literally eventually zero for every
vector unless the vector has finite support in the chosen basis.
-/
theorem exists_seq_finite_rank_strongly_convergent_to
    {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [SeparableSpace H] (T : H →L[𝕜] H) :
    ∃ T_seq : ℕ → (H →L[𝕜] H),
      (∀ n, FiniteDimensional 𝕜 (LinearMap.range (T_seq n).toLinearMap)) ∧
      (∀ x : H, Tendsto (fun n : ℕ => T_seq n x) atTop (𝓝 (T x))) := by
  sorry
