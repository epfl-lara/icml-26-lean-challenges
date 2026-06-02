# Formalization Blueprint: `geometry/L2/geo_gen_L2_005`

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
import Mathlib
```

## Required Names

- `EuclideanGeometry.external_homothetic_center`
- `EuclideanGeometry.monges_circle_theorem`

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

1. Definition (external_homothetic_center)
   The definition must be named `EuclideanGeometry.external_homothetic_center`.
   Matched text (candidate 0, definition):
For any two circles in a plane, an external tangent is a line that is tangent to both circles
but does not pass between them. Each such pair has a unique intersection point in the
extended Euclidean plane.

2. Theorem (monges_circle_theorem)
   The theorem must be named `EuclideanGeometry.monges_circle_theorem`.
   Matched text (candidate 1, theorem, label=monges_circle_theorem):
\begin{theorem}[monges_circle_theorem]\label{thm:monge}
Monge's theorem states that for any three circles in a plane, none of which is completely
inside one of the others, the intersection points of each of the three pairs of external
tangent lines are collinear.

In this formalization, we assume that the three radii are pairwise distinct, so that the
intersection points of the external common tangent lines are finite points in the affine
plane rather than points at infinity. Degenerate circles of radius zero are allowed,
provided the radii remain pairwise distinct.

For any two circles in a plane, an external tangent is a line that is tangent to both circles
but does not pass between them. There are two such external tangent lines for any two circles
satisfying the above non-containment assumptions. Monge's theorem states that the three such
points given by the three pairs of circles lie on a straight line.
\end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
