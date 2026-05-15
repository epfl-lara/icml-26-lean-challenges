# Formalization Blueprint: `geometry/L2/geo_gen_L2_006`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Analysis.Normed.Affine.Simplex
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.Geometry.Euclidean.Circumcenter
```

## Required Names

- `napoleons_theorem_inner`
- `napoleons_theorem_outer`

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
open Module
open scoped Real RealInnerProductSpace BigOperators

/-
Formalize in Lean the following named items from Text.

1. Theorem (napoleons_theorem_inner)
   The theorem must be named `napoleons_theorem_inner`.
   Matched text (candidate 0, theorem, label=Napoleon's Theorem (inner)): \begin{theorem}[Napoleon's Theorem (inner)]\label{thm:napoleon_inner} Let $A,B,C$ be non-
                                                                          collinear points in the plane. On each side of $\triangle ABC$, construct an equilateral
                                                                          triangle \emph{internally} (all three on the same ``inner'' side). Let $X,Y,Z$ be the
                                                                          centroids of the equilateral triangles on $AB,BC,CA$, respectively. Then $\triangle XYZ$ is
                                                                          equilateral. \end{theorem}
2. Theorem (napoleons_theorem_outer)
   The theorem must be named `napoleons_theorem_outer`.
   Matched text (candidate 1, theorem, label=napoleons_theorem_outer): \begin{theorem}[napoleons_theorem_outer]\label{thm:napoleon_outer} Let $A,B,C$ be non-
                                                                       collinear points in the plane. On each side of $\triangle ABC$, construct an equilateral
                                                                       triangle \emph{externally} (all three on the same ``outer'' side). Let $X,Y,Z$ be the
                                                                       centroids of the equilateral triangles on $AB,BC,CA$, respectively. Then $\triangle XYZ$ is
                                                                       equilateral. \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
