# Formalization Blueprint: `geometry/L2/geo_gen_L2_018`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the finite-dimensional matrix/vector set definition and the source theorem skeleton.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`.

No split into additional generated files is currently justified because the source has one theorem and one small bridge definition.

## Import Plan

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
```

These are the direct imports used by `ShadowBench/Source/Main.lean`: finite-dimensional real vector spaces, matrices, and Mathlib's `AffineSubspace` representation of affine sets. The initial instruction import `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace` was replaced by the valid Mathlib module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic` after Lean verification reported the original module object file missing.

## Suggested Search Modules

Non-gating search hints for the prover; do not treat these as required target imports unless proof search demonstrates a missing dependency.

- `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic`: `AffineSubspace.map` for images under affine maps.
- `Mathlib.LinearAlgebra.Matrix.ToLin`: `Matrix.mulVecLin` and related matrix-as-linear-map lemmas.
- Search results consulted during planning: `AffineSubspace`, `AffineSubspace.map`, `AffineSubspace.mk'`, `Matrix.mulVecLin`, `Matrix.toLin'_apply'`.

## Required Names

- `affineSubspace_image_of_linear_constraints`

## Source Statement Inventory

### line-17

- Kind: theorem
- Source locator: `docs/source.tex:17-19`; proof lines 21-40.
- Source statement: Show that the set `{A x + b | F x = g}` is affine, where `A ∈ ℝ^{m × n}`, `b ∈ ℝ^m`, `F ∈ ℝ^{p × n}`, and `g ∈ ℝ^p`.
- Planned Lean declarations: `linearConstraintImage`, `affineSubspace_image_of_linear_constraints`.
- Skeleton candidate used: skeletons 1--3 were used only for the matrix/vector parameter encoding and set comprehension shape. Their conclusion `∃ a V, S = {a + v | v ∈ V}` was not adopted because the source does not assume the constraint system is feasible; such a point-plus-submodule representation would incorrectly rule out the empty set. Skeleton 4 is malformed and was not adopted.
- Dependencies: Lean definition `linearConstraintImage`; Mathlib `Matrix`/`Matrix.mulVec`; Mathlib `AffineSubspace` as the formal representation of an affine set.
- Formal statement review: the Lean theorem quantifies over arbitrary natural dimensions `m n p`, matrices `A : Matrix (Fin m) (Fin n) ℝ` and `F : Matrix (Fin p) (Fin n) ℝ`, vectors `b : Fin m → ℝ` and `g : Fin p → ℝ`, and states that the exact set of outputs `A.mulVec x + b` satisfying `F.mulVec x = g` is an affine set by exhibiting it as the carrier of an `AffineSubspace`. This matches the source's arbitrary finite-dimensional real matrix/vector data and adds no feasibility side condition.
- Source qualifiers:
  - Mathematical object class: finite-dimensional real matrices and vectors; the output is a subset of `ℝ^m`.
  - Quantifier order: dimensions `m n p`, then arbitrary data `A b F g`.
  - Parameter domain: `A ∈ ℝ^{m×n}`, `b ∈ ℝ^m`, `F ∈ ℝ^{p×n}`, `g ∈ ℝ^p`.
  - Output codomain: affine subset of `ℝ^m`.
  - Equality/image condition: the set is exactly `{A x + b | F x = g}`.
  - Side conditions: none; the constraint set may be empty.
  - Follow-on claims: closure under every real affine combination of two points in the set, as used in the source proof.
- Lean coverage:
  - Finite-dimensional vectors are encoded as functions `Fin k → ℝ`.
  - Matrices are encoded as `Matrix (Fin rows) (Fin cols) ℝ`.
  - Matrix-vector products are encoded by `Matrix.mulVec`.
  - The set `{A x + b | F x = g}` is encoded by `linearConstraintImage A b F g`.
  - The affine-set conclusion is encoded as `∃ S : AffineSubspace ℝ (Fin m → ℝ), (S : Set (Fin m → ℝ)) = linearConstraintImage A b F g`.
- Scope changes: representation bridge only: the source's `ℝ^k` notation is represented by `Fin k → ℝ`, and the informal phrase "is affine" is represented by existence of a Mathlib `AffineSubspace` with the same carrier; no feasibility assumption is added.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof: A set `S` is affine if for every `z₁, z₂ ∈ S` and `θ ∈ ℝ`, the point `θ z₁ + (1 - θ) z₂` is also in `S`. Let `S = {A x + b | F x = g}`. Suppose `z₁, z₂ ∈ S`. Then there exist `x₁, x₂ ∈ ℝ^n` such that `z₁ = A x₁ + b`, `F x₁ = g`, `z₂ = A x₂ + b`, and `F x₂ = g`. For any `θ ∈ ℝ`, set `x̄ = θ x₁ + (1 - θ) x₂`. Then `θ z₁ + (1 - θ) z₂ = A x̄ + b` by linearity of `A` and `θ + (1 - θ) = 1`, and `F x̄ = θ F x₁ + (1 - θ) F x₂ = θ g + (1 - θ) g = g` by linearity of `F`. Hence the affine combination is again in `S`, so `S` is affine.
- Source proof / prover notes: unpack two membership witnesses `x₁` and `x₂`; use witness `θ • x₁ + (1 - θ) • x₂`; linearity of `Matrix.mulVec` should rewrite both `A.mulVec` and `F.mulVec` over addition and scalar multiplication. If proving the `AffineSubspace` existence directly, either build an `AffineSubspace` with carrier `linearConstraintImage A b F g` from the closure property, or identify the constraint set as an affine preimage and map it by the affine map `x ↦ A.mulVec x + b`.

## Statement Review Checklist

- [x] Source document and preflight manifest read.
- [x] Candidate skeletons compared against the source.
- [x] Local/Mathlib search consulted before drafting.
- [x] Blueprint source inventory contains `line-17` with declaration names, dependencies, fidelity notes, and proof notes.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.

## Formalization Rules from Instructions

```text
open Matrix

Formalize in Lean the Theorem (affineSubspace_image_of_linear_constraints) from Text.

The Lean declaration must be named exactly:
- affineSubspace_image_of_linear_constraints
  Matched text: Show that the set {Ax + b | Fx = g} is affine. Here A ∈ ℝ^{m×n}, b ∈ ℝ^m, F ∈ ℝ^{p×n}, and g ∈ ℝ^p.
```
