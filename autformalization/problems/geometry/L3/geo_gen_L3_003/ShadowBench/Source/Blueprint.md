# Formalization Blueprint: `geometry/L3/geo_gen_L3_003`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Draft status: source inventory and Lean statement accepted by formalization PASS and 2026-06-05 audit; ready for later prove workflow.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the concrete finite-dimensional bridge definitions and the source theorem statement `dual_cone_matrix_image_nonneg`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`.

## Import Plan

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Convex.Cone.Dual
```

These are the direct imports in `ShadowBench/Source/Main.lean`, matching `docs/instructions.md`.

## Suggested Search Modules

Non-gating proof-search hints for the later `/prove` phase:

- `Mathlib.Data.Matrix.Mul` for `Matrix.mulVec`, `Matrix.transpose`, and `Matrix.dotProduct_transpose_mulVec`.
- `Mathlib.Analysis.Convex.Cone.InnerDual` for Mathlib's unfolded inner-dual cone conventions if the proof is refactored toward inner-product notation.
- Existing imported big-operator facts for `Finset.sum_nonneg` and finite dot-product sums.

## Required Names

- `dual_cone_matrix_image_nonneg`

## Candidate Skeleton Review

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` give the same set-theoretic finite-dimensional theorem shape. This draft adopts their core representation because it matches the source theorem after unfolding the dual cone definition.
- `docs/skeletons/Skeleton4.lean` has the same candidate statement but includes an extra malformed `:= by sorry`, so only its intended statement shape was considered.
- The final Lean draft factors the skeleton's local `let` bindings into implemented bridge definitions: `pointwiseNonneg`, `nonnegOrthantImage`, and `finiteDualCone`.

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, theorem lines 17--22; proof lines 24--46.
- Source label/title: `dual_cone_matrix_image_nonneg`.
- Planned Lean declarations: `dual_cone_matrix_image_nonneg` in `ShadowBench/Source/Main.lean`.
- Auxiliary Lean declarations:
  - `pointwiseNonneg`: represents vector inequality `x \succeq 0` as pointwise nonnegativity on `Fin n → ℝ`.
  - `nonnegOrthantImage`: represents `K = {A x | x \succeq 0}` as a set of vectors `Fin m → ℝ`.
  - `finiteDualCone`: represents `K^*` by the unfolded finite-dimensional dual-cone predicate `∀ z ∈ K, 0 ≤ ∑ i, z i * y i`.
- Dependencies: `Matrix (Fin m) (Fin n) ℝ`, `Matrix.mulVec`, `Matrix.transpose`, finite sums over `Fin`, pointwise order on real-valued functions.
- Source statement: Let `A ∈ ℝ^{m × n}` and consider the cone `K = {A x | x \succeq 0}`. Then the dual cone of `K` is `K^* = {y ∈ ℝ^m | A^T y \succeq 0}`.
- Lean statement:
  ```lean
  theorem dual_cone_matrix_image_nonneg (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
      finiteDualCone (nonnegOrthantImage A) =
        {y : Fin m → ℝ | pointwiseNonneg (A.transpose.mulVec y)} := by
    sorry
  ```
- Source qualifiers:
  - Object class: real finite matrices and vectors, formalized as `Matrix (Fin m) (Fin n) ℝ`, `Fin n → ℝ`, and `Fin m → ℝ`.
  - Quantifier order: dimensions `m n : ℕ`, then matrix `A`.
  - Parameter domain/codomain: `A` maps vectors `Fin n → ℝ` to vectors `Fin m → ℝ` by `A.mulVec`.
  - Nonnegative orthant condition: `x \succeq 0` and `A^T y \succeq 0` are represented by `pointwiseNonneg`.
  - Cone/image condition: `K` is exactly the image of the nonnegative orthant under `A`, represented by `nonnegOrthantImage A`.
  - Dual equality condition: equality is an equality of sets of vectors `Fin m → ℝ`, with the dual cone unfolded by `finiteDualCone`.
  - Side conditions: no additional rank, closure, pointedness, or positivity assumptions are present in the source; the Lean statement also has none. Zero-dimensional cases are included by the finite-index encoding.
- Lean coverage: exact for the finite-dimensional membership/equality content of the source theorem. The bridge declarations `pointwiseNonneg`, `nonnegOrthantImage`, and `finiteDualCone` explicitly translate `ℝ^k`, the nonnegative orthant, the image `K = {A x | x \succeq 0}`, and `K^*` into typed finite functions, set image membership, and the unfolded nonnegative-dot-product dual-cone predicate.
- Scope changes:
  - Representation bridge: the draft uses finite index types `Fin m`, `Fin n` and the unfolded set predicate `finiteDualCone` rather than constructing a Mathlib `PointedCone` object for `K`; this is intentional because the source equality is a set-membership dual-cone characterization.
  - Dimension convention: the Lean theorem includes zero-dimensional finite index cases (`m = 0` or `n = 0`). The source does not state a positivity side condition on `m,n`, so this is at most a harmless finite-dimensional convention/generalization rather than an added or dropped assumption.
  - No source side condition or follow-on claim is left out.
- Formal statement review: compare the two inclusions encoded by set equality:
  - membership in `finiteDualCone (nonnegOrthantImage A)` means `∀ z = A x` with `x ≥ 0`, the dot product `∑ i, z i * y i` is nonnegative;
  - membership in the right-hand set means every component of `A.transpose.mulVec y` is nonnegative.
  This is the same equivalence asserted by the source proof; there are no additional follow-on claims in the source theorem beyond this set equality.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: By definition, the dual cone `K^*` consists of all vectors `y ∈ ℝ^m` such that `⟨z, y⟩ ≥ 0` for all `z ∈ K`.

  First, let `y ∈ K^*`. Then for any `x ∈ ℝ^n` with `x \succeq 0`, we have `A x ∈ K`, which implies
  `⟨A x, y⟩ = y^T A x = (A^T y)^T x = ⟨x, A^T y⟩ ≥ 0`.
  To show that `A^T y \succeq 0`, test this condition with the standard basis vectors `e_i ∈ ℝ^n` for each `i = 1, …, n`. Since `e_i \succeq 0`, we must have `⟨e_i, A^T y⟩ = (A^T y)_i ≥ 0`. Since this holds for every `i`, it follows that `A^T y \succeq 0`. This proves that `K^* ⊆ {y | A^T y \succeq 0}`.

  Conversely, suppose `y ∈ ℝ^m` satisfies `A^T y \succeq 0`. For any `z ∈ K`, there exists an `x ∈ ℝ^n` such that `x \succeq 0` and `z = A x`. We then compute:
  `⟨z, y⟩ = ⟨A x, y⟩ = ⟨x, A^T y⟩ = ∑ i x_i (A^T y)_i`.
  Since `x_i ≥ 0` and `(A^T y)_i ≥ 0` for all `i`, each term in the sum is non-negative, hence `⟨z, y⟩ ≥ 0`. This shows that `y ∈ K^*`, which proves the reverse inclusion `{y | A^T y \succeq 0} ⊆ K^*`.

  Therefore, we conclude that `K^* = {y ∈ ℝ^m | A^T y \succeq 0}`.
- Prover notes: prove by `ext y`; unfold `finiteDualCone`, `nonnegOrthantImage`, and `pointwiseNonneg`; split the equivalence. For the forward direction, for each `j : Fin n`, apply the dual condition to `A.mulVec (Pi.single j 1)` or an equivalent standard basis vector and simplify the resulting finite sum to `(A.transpose.mulVec y) j`. For the reverse direction, take `z = A.mulVec x` with `pointwiseNonneg x`; rewrite the dot product using the transpose/mulVec dot-product identity (search result: `Matrix.dotProduct_transpose_mulVec`) and use `Finset.sum_nonneg` with `mul_nonneg (hx j) (hy j)`.

## Review Checklist

- [ ] Source document inspection recorded for reviewer.
- [ ] Candidate skeleton comparison checked by reviewer.
- [ ] Blueprint source inventory entry `line-17` checked by reviewer.
- [ ] Lean statement and doc-comment prover notes checked by reviewer.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
