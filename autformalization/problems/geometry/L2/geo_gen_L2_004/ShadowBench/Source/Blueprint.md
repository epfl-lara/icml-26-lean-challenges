# Formalization Blueprint: `geometry/L2/geo_gen_L2_004`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`
- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Use skeletons as candidate declaration shapes. Record which candidate, if any, was adopted and why it matches the source.

## Import Plan

```lean
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
```

## Required Names

- `EuclideanGeometry.external_tangent_length`
- `EuclideanGeometry.circlePoint`
- `EuclideanGeometry.caseys_theorem`

## Statement Inventory

For each source theorem, lemma, definition, or named item:

- Planned Lean declaration: _pending_
- Source locator: `docs/source.tex`
- Skeleton candidate used: _pending_
- Dependencies: _pending_
- Formal statement review: _pending_
- Source qualifiers: _pending_
- Lean coverage: _pending_
- Scope changes: _pending_
- Statement verification status: _pending_
- Source proof / prover notes: _pending_

## Formalization Rules

```text
/-
Formalize in Lean the following named items from the theorem in the text.

1. Definition (external_tangent_length)
   The definition must be named `EuclideanGeometry.external_tangent_length`.
   Matched text (candidate 0, definition):
Denote by $t_{ij}$ the length of the exterior common bitangent of the circles $O_i, O_j$.

2. Definition (circlePoint)
   The definition must be named `EuclideanGeometry.circlePoint`.
   Matched text (candidate 0, definition):
Let $O_1, O_2, O_3, O_4$ be (in that order) four non-intersecting circles that lie inside $O$ and tangent to it.

3. Theorem (caseys_theorem)
   The theorem must be named `EuclideanGeometry.caseys_theorem`.
   Matched text (candidate 0, theorem, label=caseys_theorem):
\begin{theorem}[caseys_theorem]\label{thm:casey}
Let $O$ be a circle of radius $R$. Let $O_1, O_2, O_3, O_4$ be (in that order) four non-intersecting circles that lie inside $O$ and tangent to it. Denote by $t_{ij}$ the length of the exterior common bitangent of the circles $O_i, O_j$. Then:
\[
t_{12} \cdot t_{34} + t_{14} \cdot t_{23} = t_{13} \cdot t_{24}.
\]
Note that in the degenerate case, where all four circles reduce to points, this is exactly Ptolemy's theorem.
\end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
