# ShadowBench Instructions: `geometry/L2/geo_gen_L2_005`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Candidate Skeletons

Dataset: `Lemmy00/ShadowBench-skeletons-prod`

- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Treat these as candidate statement/definition shapes, not authoritative answers. Prefer the source theorem and formalization rules when candidates disagree.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib
```

## Expected Declaration Names

- `EuclideanGeometry.external_homothetic_center`
- `EuclideanGeometry.monges_circle_theorem`

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

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
