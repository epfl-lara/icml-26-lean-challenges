import Mathlib

open Filter
open scoped Topology

/--
A continuous linear operator has finite rank when the range of its underlying linear map
is finite-dimensional. This is the Lean bridge for the source phrase "bounded operator
of finite rank".
-/
def HasFiniteRankOperator
    {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (T : H →L[𝕜] H) : Prop :=
  FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap)

/--
Strong convergence of a sequence of bounded operators to a bounded operator, encoded as
pointwise convergence on every vector. This avoids the operator-norm topology on
`H →L[𝕜] H`, which would express norm convergence rather than strong convergence.
-/
def StrongOperatorTendsto
    {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (TSeq : ℕ → H →L[𝕜] H) (T : H →L[𝕜] H) : Prop :=
  ∀ x : H, Tendsto (fun n : ℕ => TSeq n x) atTop (𝓝 (T x))

/--
Source `docs/source.tex`, theorem `line-17`
(`exists_seq_finite_rank_strongly_convergent_to`): in a separable Hilbert space, every
bounded operator is the strong limit of a sequence of finite-rank bounded operators.

Source proof: choose a countable orthonormal basis `(g_k)`. Define `T_n` to agree with
`T` on the first `n` basis vectors and to vanish on the remaining basis vectors; equivalently,
`T_n = T` composed with the orthogonal projection onto the span of the first `n` basis
vectors. Each `T_n` has finite-dimensional range. The finite-span projections converge
strongly to the identity, hence `T_n x → T x` for every vector `x`.

Prover notes: use Hilbert-space orthonormal/Hilbert basis machinery for a separable space,
construct finite-span orthogonal projections, prove finite rank from the finite-dimensional
range of the projection, then compose with `T` and use pointwise convergence plus continuity
of `T`.
-/
theorem exists_seq_finite_rank_strongly_convergent_to
    {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (T : H →L[𝕜] H) :
    ∃ TSeq : ℕ → H →L[𝕜] H,
      (∀ n : ℕ, HasFiniteRankOperator (TSeq n)) ∧
        StrongOperatorTendsto TSeq T := by
  sorry
