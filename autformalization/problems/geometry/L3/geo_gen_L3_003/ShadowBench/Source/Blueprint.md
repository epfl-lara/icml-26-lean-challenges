# Formalization Blueprint: `geometry/L3/geo_gen_L3_003`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Convex.Cone.Dual
```

## Required Names

- `dual_cone_matrix_image_nonneg`

## Statement Inventory

For each source theorem, lemma, definition, or named item:

- Planned Lean declaration: _pending_
- Source locator: `docs/source.tex`
- Dependencies: _pending_
- Formal statement review: _pending_
- Source qualifiers: _pending_
- Lean coverage: _pending_
- Scope changes: _pending_
- Statement verification status: _pending_
- Source proof / prover notes: _pending_

## Formalization Rules

```text
open Matrix PointedCone

/-
Formalize in Lean the Theorem (dual_cone_matrix_image_nonneg) from Text.

The theorem must be named `dual_cone_matrix_image_nonneg`.
   Matched text (candidate 0, theorem, label=dual_cone_matrix_image_nonneg): \begin{theorem}[dual_cone_matrix_image_nonneg] Let $A \in \mathbb{R}^{m \times n}$ and
                                                                             consider the cone $K = \{Ax \mid x \succeq 0\}$. Then the dual cone of $K$ is given by \[
                                                                             K^* = \{y \in \mathbb{R}^m \mid A^T y \succeq 0\}. \] \end{theorem}
-/
```
