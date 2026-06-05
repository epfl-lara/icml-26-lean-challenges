# Formalization Blueprint: `analysis/L2/ana_gen_L2_004`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench.lean` imports `ShadowBench.Source`.
- `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`.
- `ShadowBench/Source/Main.lean` contains the source theorem declaration and imports only the direct Lean dependency listed below.

## Import Plan

```lean
import Mathlib
```

## Suggested Search Modules

- `Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM` for pointwise/strong operator topology facts.
- `Mathlib.Algebra.Module.LinearMap.FiniteRange` and `Mathlib.LinearAlgebra.FiniteDimensional.Basic` for finite-rank/range facts.
- `Mathlib.Analysis.InnerProductSpace.PiL2` and `Mathlib.Analysis.InnerProductSpace.Projection` for orthonormal bases and coordinate projections.

## Required Names

- `exists_seq_finite_rank_strongly_convergent_to`

## Candidate Skeletons

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` use the default topology on `H →L[ℝ] H`, which is operator-norm convergence and is stronger than the source's strong convergence.
- `docs/skeletons/Skeleton4.lean` is adopted because it states strong convergence pointwise: `∀ x, Tendsto (fun n => T_seq n x) atTop (𝓝 (T x))`.

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, theorem lines 17-20; proof lines 22-24.
- Source statement: "Consider a separable Hilbert space `\mathcal{H}`. Show that for any bounded operator `T` there is a sequence `{T_n}` of bounded operators of finite rank so that `T_n \to T` strongly as `n \to \infty`."
- Planned Lean declarations: `exists_seq_finite_rank_strongly_convergent_to` in `ShadowBench/Source/Main.lean`.
- Declaration kind: theorem `exists_seq_finite_rank_strongly_convergent_to`.
- Lean statement:

```lean
theorem exists_seq_finite_rank_strongly_convergent_to
    {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [SeparableSpace H] (T : H →L[𝕜] H) :
    ∃ T_seq : ℕ → (H →L[𝕜] H),
      (∀ n, FiniteDimensional 𝕜 (LinearMap.range (T_seq n).toLinearMap)) ∧
      (∀ x : H, Tendsto (fun n : ℕ => T_seq n x) atTop (𝓝 (T x)))
```

- Skeleton candidate used: `docs/skeletons/Skeleton4.lean`.
- Dependencies: `RCLike`, `NormedAddCommGroup`, `InnerProductSpace`, `CompleteSpace`, `SeparableSpace`, `ContinuousLinearMap`, `FiniteDimensional`, `LinearMap.range`, `Filter.Tendsto`, `Filter.atTop`, and `𝓝`.
- Formal statement review: the Lean theorem makes the scalar field explicit, keeps the Hilbert-space and separability hypotheses, quantifies over an arbitrary bounded linear endomorphism `T`, produces a sequence of bounded linear endomorphisms, requires finite-dimensional range for every term, and states pointwise convergence to `T x` for every vector.
- Source qualifiers:
  - Mathematical object class: separable Hilbert space.
  - Quantifier order: Hilbert space first, then arbitrary bounded operator, then existence of a sequence.
  - Parameter domain/codomain: bounded linear endomorphisms `H →L[𝕜] H`.
  - Output codomain: sequence `ℕ → (H →L[𝕜] H)`.
  - Finite-rank side condition: every approximating operator has finite-dimensional range.
  - Convergence condition: strong operator convergence, encoded as pointwise norm convergence.
- Lean coverage: `[InnerProductSpace 𝕜 H] [CompleteSpace H]` covers Hilbert space, `[SeparableSpace H]` covers separability, `H →L[𝕜] H` covers bounded operators, `FiniteDimensional 𝕜 (LinearMap.range (T_seq n).toLinearMap)` covers finite rank, and `∀ x, Tendsto (fun n => T_seq n x) atTop (𝓝 (T x))` covers strong convergence.
- Scope changes: scalar field is made explicit and generalized to `RCLike 𝕜`; strong convergence is represented by its pointwise convergence criterion rather than a separate topology wrapper. The finite-rank and convergence conditions are kept in the Lean statement.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: "Let `(g_k)_{k=1}^{\infty}` be a orthonormal basis of `\mathcal{H}`. Let `T_n g_k = T g_k` for `k \le n` and `T_n g_k = 0` for `k > n`. Then each `T_n` has finite rank (i.e. dimension of range is finite) and `\|T_n g_k - T g_k\| = 0` for `n` sufficiently large. For an arbitrary vector `g`, applying the triangle inequality gives `\|T_n g - T g\| = 0` for `n` sufficiently large."
- Source proof / prover notes: construct `T_seq n` as `T` composed with projection onto the span of the first `n` vectors of a countable orthonormal basis. Finite-dimensionality follows from the finite span. Prove convergence first on finite linear combinations, then approximate an arbitrary vector and use boundedness plus the triangle inequality; the source's final sentence needs this density argument for arbitrary vectors.
