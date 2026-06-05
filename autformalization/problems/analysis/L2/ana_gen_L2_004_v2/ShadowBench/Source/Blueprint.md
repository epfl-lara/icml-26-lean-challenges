# Formalization Blueprint: `analysis/L2/ana_gen_L2_004_v2`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: bridge predicates for finite-rank bounded operators and strong operator convergence, plus the source theorem skeleton.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so plain `lake build` covers the generated target module.

## Import Plan

Direct imports used by `ShadowBench/Source/Main.lean`:

```lean
import Mathlib
```

## Suggested Search Modules

These are proof/search hints, not extra direct imports for the current generated Lean file.

- `Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM`: pointwise convergence topology for continuous linear maps; useful declarations include `PointwiseConvergenceCLM.tendsto_iff_forall_tendsto`.
- `Mathlib.Analysis.LocallyConvex.PointwiseConvergence`: pointwise-convergence tendsto lemmas for continuous linear maps.
- `Mathlib.Algebra.Module.LinearMap.FiniteRange`: finite-range linear-map facts such as `LinearMap.HasFiniteRange`.
- `Mathlib.Analysis.InnerProductSpace.Projection`, `Mathlib.Analysis.InnerProductSpace.PiL2`, and `Mathlib.Analysis.InnerProductSpace.l2Space`: Hilbert bases, finite spans, orthogonal projections, and Fourier/partial-sum convergence tools.

## Required Names

- `exists_seq_finite_rank_strongly_convergent_to`

## Candidate Skeletons

- `docs/skeletons/Skeleton1.lean`, `docs/skeletons/Skeleton2.lean`, and `docs/skeletons/Skeleton3.lean` state convergence in `nhds T` for the default topology on `H →L[ℝ] H`. That expresses operator-norm/bounded convergence, which is stronger than the source statement's strong convergence, so these skeletons were rejected.
- `docs/skeletons/Skeleton4.lean` states pointwise convergence `∀ x, Tendsto (fun n => T_seq n x) atTop (𝓝 (T x))`, which matches strong operator convergence. The final theorem adopts this shape, with explicit bridge predicates for finite rank and strong convergence.

## Bridge Declarations

### `HasFiniteRankOperator`

Lean declaration:

```lean
def HasFiniteRankOperator
    {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (T : H →L[𝕜] H) : Prop :=
  FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap)
```

Purpose: representation bridge for the source phrase "bounded operator of finite rank". A bounded operator is represented by a continuous linear map `H →L[𝕜] H`; finite rank is represented by finite-dimensionality of the range of the underlying linear map.

### `StrongOperatorTendsto`

Lean declaration:

```lean
def StrongOperatorTendsto
    {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (TSeq : ℕ → H →L[𝕜] H) (T : H →L[𝕜] H) : Prop :=
  ∀ x : H, Tendsto (fun n : ℕ => TSeq n x) atTop (𝓝 (T x))
```

Purpose: representation bridge for the source phrase "`T_n → T` strongly". This is pointwise convergence on every vector, not the default operator-norm topology on `H →L[𝕜] H`.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`.
- Source locator: `docs/source.tex`, theorem block `line-17`, theorem lines 17--20; proof lines 20--24.
- Source kind: theorem.
- Source title/name: `exists_seq_finite_rank_strongly_convergent_to`.
- Planned Lean declarations: `exists_seq_finite_rank_strongly_convergent_to`.
- Skeleton candidate used: `docs/skeletons/Skeleton4.lean`, because it encodes strong convergence pointwise. Skeletons 1--3 were rejected because they encode operator-norm convergence.
- Dependencies: `HasFiniteRankOperator`, `StrongOperatorTendsto`, `RCLike`, `NormedAddCommGroup`, `InnerProductSpace`, `CompleteSpace`, `TopologicalSpace.SeparableSpace`, `ContinuousLinearMap`, `FiniteDimensional`, `LinearMap.range`, `Filter.Tendsto`, `Filter.atTop`, and `𝓝`.
- Source statement: "Consider a separable Hilbert space `\mathcal{H}`. Show that for any bounded operator `T` there is a sequence `{T_n}` of bounded operators of finite rank so that `T_n \to T` strongly as `n \to \infty`."
- Lean statement:

```lean
theorem exists_seq_finite_rank_strongly_convergent_to
    {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (T : H →L[𝕜] H) :
    ∃ TSeq : ℕ → H →L[𝕜] H,
      (∀ n : ℕ, HasFiniteRankOperator (TSeq n)) ∧
        StrongOperatorTendsto TSeq T := by
  sorry
```

- Source qualifiers:
  - Mathematical object class: separable Hilbert space, i.e. a complete inner product space with a countable dense subset.
  - Scalar field: not specified explicitly in the source; the usual Hilbert-space convention permits real or complex scalars.
  - Quantifier order: first the Hilbert space structure, then an arbitrary bounded operator `T`, then the approximating sequence.
  - Parameter domain and codomain: `T` and every `T_n` act from the Hilbert space to itself.
  - Output object/codomain: a sequence `(T_n)_{n : ℕ}` of bounded linear operators on the same Hilbert space.
  - Finite-rank image condition: every `T_n` has finite-dimensional range.
  - Side conditions: separability of the Hilbert space; no compactness, self-adjointness, or bounded-rank assumption on `T` is stated.
  - Equality/follow-on conditions in the theorem statement: none beyond finite-dimensional range of each approximant and strong convergence to `T`; the basis-truncation equalities occur only in the source proof.
  - Convergence condition: `T_n → T` strongly as `n → ∞`, i.e. `T_n x → T x` for every vector `x`.
- Lean coverage:
  - Separable Hilbert space is encoded by `[NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]` with `[RCLike 𝕜]`.
  - Bounded operators are encoded by continuous linear maps `H →L[𝕜] H`.
  - The approximating sequence is `TSeq : ℕ → H →L[𝕜] H`.
  - Finite rank is covered by `∀ n, HasFiniteRankOperator (TSeq n)`, where `HasFiniteRankOperator` means `FiniteDimensional 𝕜 (LinearMap.range (TSeq n).toLinearMap)`.
  - Strong convergence is covered by `StrongOperatorTendsto TSeq T`, i.e. `∀ x, Tendsto (fun n => TSeq n x) atTop (𝓝 (T x))`.
- Scope changes:
  - Scalar field is expressed with any `RCLike 𝕜`, covering both real and complex Hilbert spaces under the source's unspecified Hilbert-space scalar convention. This is an intentional scalar-convention generalization, not a weakening.
  - Strong convergence is represented directly as pointwise convergence instead of using a bundled pointwise-convergence topology wrapper. This representation choice keeps the source convergence condition.
- Formal statement review:
  - The norm-topology skeletons would silently strengthen the source claim and are not used.
  - The adopted theorem keeps the source quantifier order and all source side conditions: separability, bounded operator input, finite-rank bounded approximants, and strong convergence.
  - The source theorem's phrase "bounded operator" is represented by `ContinuousLinearMap`, the standard Lean representation for bounded linear maps between normed spaces.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: "Let `(g_k)_{k=1}^{\infty}` be a orthonormal basis of `\mathcal{H}`. Let `T_n g_k = T g_k` for `k \le n` and `T_n g_k = 0` for `k > n`. Then each `T_n` has finite rank (i.e. dimension of range is finite) and `\|T_n g_k - T g_k\| = 0` for `n` sufficiently large. For an arbitrary vector `g`, applying the triangle inequality gives `\|T_n g - T g\| = 0` for `n` sufficiently large."
- Source proof / prover notes: Source proof chooses an orthonormal basis and finite-rank truncations; the prover should formalize these as projections onto spans of finite basis prefixes, prove finite-dimensional range, and show pointwise convergence using convergence of the projections together with continuity of `T`.
  - Use the standard finite-rank projection argument: choose a countable orthonormal/Hilbert basis for the separable Hilbert space, let `P_n` be the orthogonal projection onto the span of the first `n` basis vectors, and set `T_n = T ∘L P_n` (equivalently, the operator agreeing with `T` on the first `n` basis vectors and vanishing on the remaining basis vectors).
  - Each `P_n` has finite-dimensional range, so `T_n` has finite-dimensional range because its range is contained in the image of a finite-dimensional subspace under `T`.
  - Prove `P_n x → x` for every `x` using Hilbert-basis completeness / convergence of Fourier partial sums, then use continuity of `T` to get `T (P_n x) → T x`.
  - The source proof's final sentence claims eventual equality for an arbitrary vector; that is only true for finite-support vectors. The rigorous proof should use approximation/convergence for arbitrary vectors.

## Statement/Source Review Checklist

- [x] Source document inspected with `formalization_document_inspect`.
- [x] Companion instructions and candidate skeletons read.
- [x] Local project and Mathlib search performed before drafting.
- [x] Source inventory entry `line-17` recorded with source qualifiers, Lean coverage, scope changes, source proof text, and prover notes.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
